use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::error::BridgeError;
use crate::vellvm_sanitize::{
    SliceRole, find_outside_quotes, sanitize_for_vellvm, strip_line_comment_preserving_strings,
};

/// Identified struct/type definition (`%struct.Foo = type { ... }`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeDefRecord {
    pub ident: String,
    pub raw_line: String,
}

/// Module-level `@global`, `@constant`, `@alias`, or `@ifunc` record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GlobalRecord {
    pub name: String,
    pub raw_line: String,
    /// `GlobalOpt`-safe declaration emitted into isolated per-function slices.
    pub slice_decl: String,
}

/// External function prototype (`declare ... @callee(...)`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclRecord {
    pub name: String,
    pub raw_line: String,
    pub sanitized_slice_decl: String,
}

/// Original linkage, visibility, section, comdat, and alignment properties of a defined function,
/// preserved in `ModuleManifest` and restored verbatim during `merge_module`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionManifestEntry {
    pub name: String,
    pub original_linkage_vis: String,
    pub unnamed_addr: Option<String>,
    pub section: Option<String>,
    pub comdat: Option<String>,
    pub align: Option<String>,
    pub prototype_declare: String,
    pub splittable: bool,
    pub non_splittable_reason: Option<String>,
}

/// Complete module skeleton manifest emitted by `split_module` and consumed by `merge_module`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleManifest {
    pub source_filename: Option<String>,
    pub target_datalayout: Option<String>,
    pub target_triple: Option<String>,
    pub module_asm_lines: Vec<String>,
    pub comdats: Vec<String>,
    pub type_defs: Vec<TypeDefRecord>,
    pub globals: Vec<GlobalRecord>,
    pub declarations: Vec<DeclRecord>,
    pub functions: Vec<FunctionManifestEntry>,
    pub attr_groups: BTreeMap<u32, String>,
    pub named_metadata: Vec<String>,
    pub numbered_metadata: BTreeMap<u32, String>,
}

/// Result of splitting a whole LLVM 23.1.5 `.ll` module into isolated per-function slices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitOutput {
    pub manifest: ModuleManifest,
    /// Maps function symbol name (without leading `@`) to self-contained `<fn>.input.ll` text.
    pub slices: BTreeMap<String, String>,
}

const LINKAGE_VIS_KEYWORDS: &[&str] = &[
    "private",
    "internal",
    "available_externally",
    "linkonce",
    "weak",
    "common",
    "appending",
    "extern_weak",
    "linkonce_odr",
    "weak_odr",
    "external",
    "dso_local",
    "dso_preemptable",
    "default",
    "hidden",
    "protected",
    "dllimport",
    "dllexport",
];

const IMPLICIT_DSO_LOCAL_KEYWORDS: &[&str] = &["private", "internal", "hidden", "protected"];

/// Splits a whole LLVM 23.1.5 `.ll` module into a `ModuleManifest` plus one isolated,
/// `GlobalOpt`- and `GlobalDCE`-sound `<fn>.input.ll` slice per splittable function.
pub fn split_module(module_ir: &str) -> Result<SplitOutput, BridgeError> {
    let parsed = parse_raw_module(module_ir)?;

    let type_map: BTreeMap<&str, &TypeDefRecord> = parsed
        .manifest
        .type_defs
        .iter()
        .map(|t| (t.ident.as_str(), t))
        .collect();
    let global_map: BTreeMap<&str, &GlobalRecord> = parsed
        .manifest
        .globals
        .iter()
        .map(|g| (g.name.as_str(), g))
        .collect();

    // Build combined symbol -> sanitized `declare` lookup (external declares + sibling defines).
    let mut callee_decl_map: BTreeMap<String, String> = BTreeMap::new();
    for d in &parsed.manifest.declarations {
        callee_decl_map.insert(d.name.clone(), d.sanitized_slice_decl.clone());
    }
    for f in &parsed.manifest.functions {
        callee_decl_map.insert(f.name.clone(), f.prototype_declare.clone());
    }

    let mut slices = BTreeMap::new();
    for raw_fn in &parsed.raw_functions {
        let Some(meta) = parsed
            .manifest
            .functions
            .iter()
            .find(|m| m.name == raw_fn.name)
        else {
            continue;
        };
        if !meta.splittable {
            continue;
        }

        let slice_text = build_single_function_slice(
            &parsed.manifest,
            raw_fn,
            &type_map,
            &global_map,
            &callee_decl_map,
        );
        slices.insert(raw_fn.name.clone(), slice_text);
    }

    Ok(SplitOutput {
        manifest: parsed.manifest,
        slices,
    })
}

/// Splits and additionally runs Vellvm surface sanitization (`SliceRole::Source`) on every slice.
pub fn split_module_for_vellvm(module_ir: &str) -> Result<SplitOutput, BridgeError> {
    let mut out = split_module(module_ir)?;
    for slice in out.slices.values_mut() {
        *slice = sanitize_for_vellvm(slice, SliceRole::Source)?;
    }
    Ok(out)
}

/// Recombines verified per-function slices (`<fn>.opt_fast.ll` or `<fn>.opt_safe.ll`) with the
/// original `ModuleManifest`, restoring linkages/globals/comdats and globally re-indexing `#N`
/// attribute groups and `!N` metadata nodes without collisions.
pub fn merge_module(
    manifest: &ModuleManifest,
    verified_slices: &BTreeMap<String, String>,
) -> Result<String, BridgeError> {
    let mut attr_interner = AttrInterner::default();
    let mut meta_pool = MetadataArena::from_manifest(&manifest.numbered_metadata);

    let manifest_attr_remap = attr_interner.register_table(&manifest.attr_groups);
    let identity_meta_remap: BTreeMap<u32, u32> = manifest
        .numbered_metadata
        .keys()
        .map(|&id| (id, id))
        .collect();

    let mut merged_types: Vec<TypeDefRecord> = manifest.type_defs.clone();
    let mut seen_types: BTreeSet<String> = merged_types.iter().map(|t| t.ident.clone()).collect();

    let defined_fn_names: BTreeSet<&str> =
        manifest.functions.iter().map(|f| f.name.as_str()).collect();
    let mut seen_decls: BTreeSet<String> = manifest
        .declarations
        .iter()
        .map(|d| d.name.clone())
        .collect();
    let mut extra_synthesized_decls: Vec<String> = Vec::new();
    let mut rendered_functions: Vec<String> = Vec::with_capacity(manifest.functions.len());

    for fn_meta in &manifest.functions {
        let slice_ir = verified_slices.get(&fn_meta.name).ok_or_else(|| {
            BridgeError::MissingVerifiedSlice {
                function_name: fn_meta.name.clone(),
            }
        })?;
        let slice_parsed = parse_raw_module(slice_ir)?;
        let slice_attr_remap = attr_interner.register_table(&slice_parsed.manifest.attr_groups);
        let slice_meta_remap =
            meta_pool.absorb_slice_metadata(&slice_parsed.manifest.numbered_metadata);

        // Collect any new `%struct.* = type ...` synthesized by `opt -O2`.
        for td in &slice_parsed.manifest.type_defs {
            if seen_types.insert(td.ident.clone()) {
                merged_types.push(td.clone());
            }
        }

        // Collect new external/intrinsic `declare`s synthesized by `opt -O2` (e.g., `@llvm.memcpy.*`).
        for decl in &slice_parsed.manifest.declarations {
            if !defined_fn_names.contains(decl.name.as_str())
                && seen_decls.insert(decl.name.clone())
            {
                let remapped_decl =
                    remap_attrs_and_metadata(&decl.raw_line, &slice_attr_remap, &slice_meta_remap);
                extra_synthesized_decls.push(remapped_decl);
            }
        }

        let target_raw_fn = slice_parsed
            .raw_functions
            .iter()
            .find(|rf| rf.name == fn_meta.name)
            .or_else(|| slice_parsed.raw_functions.first())
            .ok_or_else(|| BridgeError::MalformedModule {
                detail: format!(
                    "verified slice for `@{}` contains no `define` body",
                    fn_meta.name
                ),
            })?;

        let restored_fn = restore_and_remap_function(
            fn_meta,
            target_raw_fn,
            &slice_attr_remap,
            &slice_meta_remap,
        )?;
        rendered_functions.push(restored_fn);
    }

    // Assemble final LLVM 23.1.5 module in canonical section order.
    let mut out = Vec::new();
    if let Some(sf) = &manifest.source_filename {
        out.push(sf.clone());
    }
    if let Some(dl) = &manifest.target_datalayout {
        out.push(dl.clone());
    }
    if let Some(tt) = &manifest.target_triple {
        out.push(tt.clone());
    }
    for asm in &manifest.module_asm_lines {
        out.push(asm.clone());
    }
    if !out.is_empty() {
        out.push(String::new());
    }

    if !merged_types.is_empty() {
        for td in &merged_types {
            out.push(td.raw_line.clone());
        }
        out.push(String::new());
    }

    if !manifest.comdats.is_empty() {
        for cd in &manifest.comdats {
            out.push(cd.clone());
        }
        out.push(String::new());
    }

    if !manifest.globals.is_empty() {
        for g in &manifest.globals {
            out.push(remap_attrs_and_metadata(
                &g.raw_line,
                &manifest_attr_remap,
                &identity_meta_remap,
            ));
        }
        out.push(String::new());
    }

    if !manifest.declarations.is_empty() || !extra_synthesized_decls.is_empty() {
        for d in &manifest.declarations {
            out.push(remap_attrs_and_metadata(
                &d.raw_line,
                &manifest_attr_remap,
                &identity_meta_remap,
            ));
        }
        for synth in &extra_synthesized_decls {
            out.push(synth.clone());
        }
        out.push(String::new());
    }

    for fn_block in &rendered_functions {
        out.push(fn_block.clone());
        out.push(String::new());
    }

    let attr_lines = attr_interner.emit_lines();
    if !attr_lines.is_empty() {
        out.extend(attr_lines);
        out.push(String::new());
    }

    if !manifest.named_metadata.is_empty() || !meta_pool.nodes.is_empty() {
        for nm in &manifest.named_metadata {
            out.push(nm.clone());
        }
        for (&id, rhs) in &meta_pool.nodes {
            out.push(format!("!{id} = {rhs}"));
        }
    }

    let mut joined = out.join("\n");
    if !joined.ends_with('\n') {
        joined.push('\n');
    }
    Ok(joined)
}

#[derive(Debug, Clone)]
struct RawFunctionDef {
    name: String,
    widened_header: String,
    raw_lines: Vec<String>,
}

struct ParsedModule {
    manifest: ModuleManifest,
    raw_functions: Vec<RawFunctionDef>,
}

fn parse_raw_module(ir: &str) -> Result<ParsedModule, BridgeError> {
    let mut manifest = ModuleManifest {
        source_filename: None,
        target_datalayout: None,
        target_triple: None,
        module_asm_lines: Vec::new(),
        comdats: Vec::new(),
        type_defs: Vec::new(),
        globals: Vec::new(),
        declarations: Vec::new(),
        functions: Vec::new(),
        attr_groups: BTreeMap::new(),
        named_metadata: Vec::new(),
        numbered_metadata: BTreeMap::new(),
    };
    let mut raw_functions = Vec::new();

    let lines: Vec<&str> = ir.lines().collect();
    let mut idx = 0_usize;
    while let Some(&raw_line) = lines.get(idx) {
        let code = strip_line_comment_preserving_strings(raw_line).trim();
        if code.is_empty() || code.starts_with("uselistorder") {
            idx += 1;
            continue;
        }

        if code.starts_with("source_filename") {
            manifest.source_filename = Some(code.to_owned());
            idx += 1;
            continue;
        }
        if code.starts_with("target datalayout") {
            manifest.target_datalayout = Some(code.to_owned());
            idx += 1;
            continue;
        }
        if code.starts_with("target triple") {
            manifest.target_triple = Some(code.to_owned());
            idx += 1;
            continue;
        }
        if code.starts_with("module asm") {
            manifest.module_asm_lines.push(code.to_owned());
            idx += 1;
            continue;
        }
        if code.starts_with('$') && code.contains("= comdat") {
            manifest.comdats.push(code.to_owned());
            idx += 1;
            continue;
        }
        if code.starts_with('%')
            && let Some((lhs, rhs)) = code.split_once('=')
            && rhs.trim_start().starts_with("type ")
        {
            manifest.type_defs.push(TypeDefRecord {
                ident: lhs.trim().to_owned(),
                raw_line: code.to_owned(),
            });
            idx += 1;
            continue;
        }
        if code.starts_with('@') && code.contains('=') {
            let rec = parse_global_record(code)?;
            manifest.globals.push(rec);
            idx += 1;
            continue;
        }
        if code.starts_with("declare ") {
            let decl = parse_declaration_record(code)?;
            manifest.declarations.push(decl);
            idx += 1;
            continue;
        }
        if code.starts_with("define ") {
            let start_idx = idx;
            let mut fn_lines = Vec::new();
            let mut brace_depth = 0_i32;
            let mut saw_open = false;
            while let Some(&fl) = lines.get(idx) {
                let fl_code = strip_line_comment_preserving_strings(fl);
                for b in count_braces_outside_quotes(fl_code) {
                    if b == b'{' {
                        brace_depth += 1;
                        saw_open = true;
                    } else if b == b'}' {
                        brace_depth -= 1;
                    }
                }
                fn_lines.push(fl.to_owned());
                idx += 1;
                if saw_open && brace_depth <= 0 {
                    break;
                }
            }
            if !saw_open || brace_depth != 0 {
                return Err(BridgeError::MalformedModule {
                    detail: format!(
                        "unbalanced braces in `define` starting at line {}",
                        start_idx + 1
                    ),
                });
            }
            let (meta, raw_fn) = parse_function_definition(&fn_lines)?;
            manifest.functions.push(meta);
            raw_functions.push(raw_fn);
            continue;
        }
        if let Some(rest) = code.strip_prefix("attributes #")
            && let Some((id_str, rhs)) = rest.split_once('=')
            && let Ok(id) = id_str.trim().parse::<u32>()
        {
            let body = extract_braced_body(rhs.trim());
            manifest.attr_groups.insert(id, body);
            idx += 1;
            continue;
        }
        if let Some(rest) = code.strip_prefix('!')
            && let Some((lhs, rhs)) = rest.split_once('=')
        {
            let lhs_trim = lhs.trim();
            if let Ok(id) = lhs_trim.parse::<u32>() {
                manifest.numbered_metadata.insert(id, rhs.trim().to_owned());
            } else {
                manifest.named_metadata.push(code.to_owned());
            }
            idx += 1;
            continue;
        }

        idx += 1;
    }

    Ok(ParsedModule {
        manifest,
        raw_functions,
    })
}

fn parse_global_record(code: &str) -> Result<GlobalRecord, BridgeError> {
    let (lhs, rhs_raw) = code
        .split_once('=')
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("invalid global definition `{code}`"),
        })?;
    let sym = lhs
        .trim()
        .strip_prefix('@')
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("global `{lhs}` missing `@`"),
        })?
        .to_owned();
    let rhs = rhs_raw.trim();

    let slice_decl = build_sound_global_slice_decl(&sym, rhs)?;
    Ok(GlobalRecord {
        name: sym,
        raw_line: code.to_owned(),
        slice_decl,
    })
}

/// Rewrites a module-level `@global` / `@constant` / `@alias` / `@ifunc` into a sound declaration
/// for isolated per-function optimization (`GlobalOpt` protection).
fn build_sound_global_slice_decl(sym: &str, rhs: &str) -> Result<String, BridgeError> {
    // Extract optional alignment `, align <N>` from top-level comma annotations.
    let align_suffix = extract_top_level_align(rhs);
    let addrspace_piece = extract_addrspace_clause(rhs);
    let unnamed_piece = if contains_bare_keyword(rhs, "local_unnamed_addr") {
        " local_unnamed_addr"
    } else if contains_bare_keyword(rhs, "unnamed_addr") {
        " unnamed_addr"
    } else {
        ""
    };

    // Alias / ifunc: degrade to external declaration (`ExtractGV.cpp:108-145`).
    for kw in ["alias ", "ifunc "] {
        if let Some(pos) = find_keyword_outside_quotes(rhs, kw) {
            let after_kw = rhs.get(pos + kw.len()..).unwrap_or("").trim_start();
            let (ty, _) =
                parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                    detail: format!("unable to parse `{kw}` type for `@{sym}`"),
                })?;
            let ty_without_comma = ty.trim_end_matches(',').trim();
            return Ok(format!("@{sym} = external global {ty_without_comma}"));
        }
    }

    if let Some(pos) = find_keyword_outside_quotes(rhs, "global ") {
        let after_kw = rhs.get(pos + "global ".len()..).unwrap_or("").trim_start();
        let (ty, _) =
            parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                detail: format!("unable to parse `global` type for `@{sym}`"),
            })?;
        // Mutable globals MUST become `external global <Ty>` without initializer so `opt -O2`
        // (`GlobalOpt`) never assumes zero writers in the isolated slice.
        return Ok(format!(
            "@{sym} = external{addrspace_piece} global {ty}{align_suffix}"
        ));
    }

    if let Some(pos) = find_keyword_outside_quotes(rhs, "constant ") {
        let prefix_mods = rhs.get(..pos).unwrap_or("");
        let after_kw = rhs
            .get(pos + "constant ".len()..)
            .unwrap_or("")
            .trim_start();
        let (ty, after_ty) =
            parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                detail: format!("unable to parse `constant` type for `@{sym}`"),
            })?;

        let is_external_only = contains_bare_keyword(prefix_mods, "external")
            || contains_bare_keyword(prefix_mods, "extern_weak");
        let is_interposable = contains_bare_keyword(prefix_mods, "weak")
            || contains_bare_keyword(prefix_mods, "linkonce")
            || contains_bare_keyword(prefix_mods, "common")
            || contains_bare_keyword(prefix_mods, "appending");

        let init_str = split_at_top_level_comma(after_ty.trim()).0.trim();
        let has_unsupported_const_expr =
            init_str.contains("inrange(") || init_str.contains("blockaddress(");

        if is_external_only || is_interposable || init_str.is_empty() || has_unsupported_const_expr
        {
            return Ok(format!(
                "@{sym} = external{unnamed_piece}{addrspace_piece} constant {ty}{align_suffix}"
            ));
        }

        // Definitive read-only constant: emit as `available_externally constant <Ty> <Init>`.
        return Ok(format!(
            "@{sym} = available_externally{unnamed_piece}{addrspace_piece} constant {ty} {init_str}{align_suffix}"
        ));
    }

    Err(BridgeError::MalformedModule {
        detail: format!("unrecognized global/constant kind on `@{sym} = {rhs}`"),
    })
}

fn parse_declaration_record(code: &str) -> Result<DeclRecord, BridgeError> {
    let rest = code
        .strip_prefix("declare ")
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("invalid declaration `{code}`"),
        })?
        .trim_start();

    // Strip any leading `!dbg !N` metadata attachments on `declare`.
    let mut clean_rest = rest;
    while let Some(after_bang) = clean_rest.strip_prefix('!') {
        let after_key = after_bang.trim_start_matches(|c: char| !c.is_ascii_whitespace());
        let after_ws = after_key.trim_start();
        if let Some(after_val) = after_ws.strip_prefix('!') {
            clean_rest = after_val
                .trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_')
                .trim_start();
        } else {
            break;
        }
    }

    let (name, prefix_mods_and_ret, params_inside, post_params) =
        split_function_signature_parts(clean_rest)?;
    let (_, cconv_and_ret) = split_leading_linkage_vis(&prefix_mods_and_ret);
    let nameless_params = strip_param_names(&params_inside);
    let attr_grp = extract_first_attr_group(&post_params);
    let grp_suffix = attr_grp.map_or_else(String::new, |g| format!(" #{g}"));

    let sanitized_slice_decl =
        format!("declare {cconv_and_ret} @{name}({nameless_params}){grp_suffix}");
    Ok(DeclRecord {
        name,
        raw_line: code.to_owned(),
        sanitized_slice_decl,
    })
}

fn parse_function_definition(
    fn_lines: &[String],
) -> Result<(FunctionManifestEntry, RawFunctionDef), BridgeError> {
    let header_line = fn_lines
        .first()
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: "empty function definition".to_owned(),
        })?;
    let header_code = strip_line_comment_preserving_strings(header_line).trim();
    let after_define = header_code
        .strip_prefix("define ")
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("function header does not start with `define `: `{header_code}`"),
        })?
        .trim_start();
    let without_open_brace = after_define
        .strip_suffix('{')
        .unwrap_or(after_define)
        .trim_end();

    let (name, prefix_mods_and_ret, params_inside, post_params) =
        split_function_signature_parts(without_open_brace)?;
    let (original_linkage_vis, cconv_and_ret) = split_leading_linkage_vis(&prefix_mods_and_ret);

    let unnamed_addr = if contains_bare_keyword(&post_params, "local_unnamed_addr") {
        Some("local_unnamed_addr".to_owned())
    } else if contains_bare_keyword(&post_params, "unnamed_addr") {
        Some("unnamed_addr".to_owned())
    } else {
        None
    };
    let section = extract_section_clause(&post_params);
    let comdat = extract_comdat_clause(&post_params);
    let align = extract_func_align_clause(&post_params);
    let attr_grp = extract_first_attr_group(&post_params);
    let personality = extract_personality_clause(&post_params);

    let nameless_params = strip_param_names(&params_inside);
    let grp_suffix = attr_grp.map_or_else(String::new, |g| format!(" #{g}"));
    let prototype_declare =
        format!("declare {cconv_and_ret} @{name}({nameless_params}){grp_suffix}");

    // Widen linkage to external (`dso_local` if non-interposable) in `<fn>.input.ll` so `opt -O2`
    // (`GlobalDCE` / `DeadArgElim`) cannot delete `@f` or rewrite its calling convention/signature.
    let mut slice_post = Vec::new();
    if let Some(ua) = &unnamed_addr {
        slice_post.push(ua.clone());
    }
    if let Some(g) = attr_grp {
        slice_post.push(format!("#{g}"));
    }
    if let Some(pers) = personality {
        slice_post.push(pers);
    }
    let slice_post_str = if slice_post.is_empty() {
        String::new()
    } else {
        format!(" {}", slice_post.join(" "))
    };
    let widened_header =
        format!("define dso_local {cconv_and_ret} @{name}({params_inside}){slice_post_str} {{");

    // Check for cross-function `blockaddress(@other_fn, %bb)` which forbids isolating `@other_fn` as `declare`.
    let full_body = fn_lines.join("\n");
    let non_splittable_reason = check_cross_function_blockaddress(&full_body, &name);

    let meta = FunctionManifestEntry {
        name: name.clone(),
        original_linkage_vis,
        unnamed_addr,
        section,
        comdat,
        align,
        prototype_declare,
        splittable: non_splittable_reason.is_none(),
        non_splittable_reason,
    };
    let raw_fn = RawFunctionDef {
        name,
        widened_header,
        raw_lines: fn_lines.to_vec(),
    };
    Ok((meta, raw_fn))
}

fn check_cross_function_blockaddress(fn_body: &str, self_name: &str) -> Option<String> {
    let mut rest = fn_body;
    while let Some(pos) = find_outside_quotes(rest, "blockaddress(") {
        let after = rest.get(pos + "blockaddress(".len()..).unwrap_or("");
        if let Some(at_pos) = after.find('@') {
            let after_at = after.get(at_pos + 1..).unwrap_or("");
            let target_fn: String = after_at
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$'))
                .collect();
            if !target_fn.is_empty() && target_fn != self_name {
                return Some(format!(
                    "references cross-function `blockaddress(@{target_fn}, ...)`"
                ));
            }
        }
        rest = after;
    }
    None
}

fn build_single_function_slice(
    manifest: &ModuleManifest,
    raw_fn: &RawFunctionDef,
    type_map: &BTreeMap<&str, &TypeDefRecord>,
    global_map: &BTreeMap<&str, &GlobalRecord>,
    callee_decl_map: &BTreeMap<String, String>,
) -> String {
    let mut fn_lines = raw_fn.raw_lines.clone();
    if let Some(first) = fn_lines.first_mut() {
        *first = raw_fn.widened_header.clone();
    }
    let fn_text = fn_lines.join("\n");

    // 1. Collect transitively referenced `@symbols` (`globals` + `declarations` / sibling `define`s).
    let mut kept_globals: BTreeSet<String> = BTreeSet::new();
    let mut kept_callees: BTreeSet<String> = BTreeSet::new();
    let mut symbol_worklist: Vec<String> = collect_prefixed_idents(&fn_text, b'@');

    while let Some(sym) = symbol_worklist.pop() {
        if sym == raw_fn.name {
            continue;
        }
        if let Some(g) = global_map.get(sym.as_str()) {
            if kept_globals.insert(sym) {
                symbol_worklist.extend(collect_prefixed_idents(&g.slice_decl, b'@'));
            }
        } else if callee_decl_map.contains_key(&sym) {
            kept_callees.insert(sym);
        }
    }

    // 2. Collect transitive closure of `%struct.* = type ...` across function, kept globals & kept callees
    //    (prevents Vellvm's `TypToDtyp.v:187-192` silent `DTYPE_Void` size-0 bug!).
    let mut type_seeds = collect_prefixed_idents(&fn_text, b'%');
    for g_name in &kept_globals {
        if let Some(g) = global_map.get(g_name.as_str()) {
            type_seeds.extend(collect_prefixed_idents(&g.slice_decl, b'%'));
        }
    }
    for c_name in &kept_callees {
        if let Some(decl) = callee_decl_map.get(c_name) {
            type_seeds.extend(collect_prefixed_idents(decl, b'%'));
        }
    }

    let mut kept_type_idents: BTreeSet<String> = BTreeSet::new();
    while let Some(cand) = type_seeds.pop() {
        let full_ident = format!("%{cand}");
        if let Some(td) = type_map.get(full_ident.as_str())
            && kept_type_idents.insert(full_ident)
        {
            type_seeds.extend(collect_prefixed_idents(&td.raw_line, b'%'));
        }
    }
    // LLVM `LLParser::parseUnnamedType` requires `%0 .. %k` without gaps if any numbered type `%k` is kept.
    let max_numbered_type = kept_type_idents
        .iter()
        .filter_map(|id| id.strip_prefix('%')?.parse::<u32>().ok())
        .max();
    if let Some(max_k) = max_numbered_type {
        for k in 0..=max_k {
            let num_id = format!("%{k}");
            if type_map.contains_key(num_id.as_str()) {
                kept_type_idents.insert(num_id);
            }
        }
    }

    // 3. Collect referenced `#N` attribute groups & transitive `!N` metadata nodes.
    let mut kept_attr_ids: BTreeSet<u32> = collect_numeric_refs(&fn_text, b'#');
    for c_name in &kept_callees {
        if let Some(decl) = callee_decl_map.get(c_name) {
            kept_attr_ids.extend(collect_numeric_refs(decl, b'#'));
        }
    }

    let mut kept_meta_ids: BTreeSet<u32> = BTreeSet::new();
    let mut meta_worklist: Vec<u32> = collect_numeric_refs(&fn_text, b'!').into_iter().collect();
    while let Some(mid) = meta_worklist.pop() {
        if let Some(rhs) = manifest.numbered_metadata.get(&mid)
            && kept_meta_ids.insert(mid)
        {
            meta_worklist.extend(collect_numeric_refs(rhs, b'!'));
        }
    }

    // 4. Emit `<fn>.input.ll` in canonical order.
    let mut out = Vec::new();
    if let Some(sf) = &manifest.source_filename {
        out.push(sf.clone());
    }
    if let Some(dl) = &manifest.target_datalayout {
        out.push(dl.clone());
    }
    if let Some(tt) = &manifest.target_triple {
        out.push(tt.clone());
    }
    if !out.is_empty() {
        out.push(String::new());
    }

    if !kept_type_idents.is_empty() {
        for td in &manifest.type_defs {
            if kept_type_idents.contains(&td.ident) {
                out.push(td.raw_line.clone());
            }
        }
        out.push(String::new());
    }

    if !kept_globals.is_empty() {
        for g in &manifest.globals {
            if kept_globals.contains(&g.name) {
                out.push(g.slice_decl.clone());
            }
        }
        out.push(String::new());
    }

    if !kept_callees.is_empty() {
        for c_name in &kept_callees {
            if let Some(decl) = callee_decl_map.get(c_name) {
                out.push(decl.clone());
            }
        }
        out.push(String::new());
    }

    out.push(fn_text);
    out.push(String::new());

    if !kept_attr_ids.is_empty() {
        for id in &kept_attr_ids {
            if let Some(body) = manifest.attr_groups.get(id) {
                out.push(format!("attributes #{id} = {{ {body} }}"));
            }
        }
        out.push(String::new());
    }

    if !kept_meta_ids.is_empty() {
        for id in &kept_meta_ids {
            if let Some(rhs) = manifest.numbered_metadata.get(id) {
                out.push(format!("!{id} = {rhs}"));
            }
        }
    }

    let mut text = out.join("\n");
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

fn restore_and_remap_function(
    fn_meta: &FunctionManifestEntry,
    verified_fn: &RawFunctionDef,
    attr_remap: &BTreeMap<u32, u32>,
    meta_remap: &BTreeMap<u32, u32>,
) -> Result<String, BridgeError> {
    let header_line =
        verified_fn
            .raw_lines
            .first()
            .ok_or_else(|| BridgeError::MalformedModule {
                detail: format!("empty verified function `@{}`", fn_meta.name),
            })?;
    let header_code = strip_line_comment_preserving_strings(header_line).trim();
    let after_define = header_code
        .strip_prefix("define ")
        .unwrap_or(header_code)
        .trim_start();
    let without_brace = after_define
        .strip_suffix('{')
        .unwrap_or(after_define)
        .trim_end();

    let (_parsed_name, prefix_mods_and_ret, params_inside, post_params) =
        split_function_signature_parts(without_brace)?;
    let (_, opt_cconv_and_ret) = split_leading_linkage_vis(&prefix_mods_and_ret);

    // Restore original linkage/visibility from Manifest (handling LLVM Verifier implicit dso_local rule).
    let restored_link_vis = normalize_restored_linkage_vis(&fn_meta.original_linkage_vis);
    let link_prefix = if restored_link_vis.is_empty() {
        String::new()
    } else {
        format!("{restored_link_vis} ")
    };

    // Combine Manifest structural properties (`unnamed_addr`, `section`, `comdat`, `align`)
    // with any inferred attribute group `#N` / `personality` / `!metadata` on the verified function.
    let mut post_parts: Vec<String> = Vec::new();
    if let Some(ua) = &fn_meta.unnamed_addr {
        post_parts.push(ua.clone());
    } else if contains_bare_keyword(&post_params, "local_unnamed_addr") {
        post_parts.push("local_unnamed_addr".to_owned());
    } else if contains_bare_keyword(&post_params, "unnamed_addr") {
        post_parts.push("unnamed_addr".to_owned());
    }

    if let Some(sec) = &fn_meta.section {
        post_parts.push(sec.clone());
    }
    if let Some(cd) = &fn_meta.comdat {
        post_parts.push(cd.clone());
    }
    if let Some(al) = &fn_meta.align {
        post_parts.push(al.clone());
    }
    if let Some(grp) = extract_first_attr_group(&post_params) {
        post_parts.push(format!("#{grp}"));
    }
    if let Some(pers) = extract_personality_clause(&post_params) {
        post_parts.push(pers);
    }
    for meta_attach in extract_metadata_attachments(&post_params) {
        post_parts.push(meta_attach);
    }

    let post_str = if post_parts.is_empty() {
        String::new()
    } else {
        format!(" {}", post_parts.join(" "))
    };

    let rebuilt_header = format!(
        "define {link_prefix}{opt_cconv_and_ret} @{}({params_inside}){post_str} {{",
        fn_meta.name
    );

    let mut remapped_lines = Vec::with_capacity(verified_fn.raw_lines.len());
    remapped_lines.push(remap_attrs_and_metadata(
        &rebuilt_header,
        attr_remap,
        meta_remap,
    ));
    for body_line in verified_fn.raw_lines.iter().skip(1) {
        remapped_lines.push(remap_attrs_and_metadata(body_line, attr_remap, meta_remap));
    }
    Ok(remapped_lines.join("\n"))
}

fn normalize_restored_linkage_vis(orig: &str) -> String {
    let toks: Vec<&str> = orig.split_whitespace().collect();
    let has_implicit_dso = toks.iter().any(|t| IMPLICIT_DSO_LOCAL_KEYWORDS.contains(t));
    let filtered: Vec<&str> = toks
        .into_iter()
        .filter(|&t| !(has_implicit_dso && t == "dso_local"))
        .collect();
    filtered.join(" ")
}

#[derive(Default)]
struct AttrInterner {
    body_to_id: BTreeMap<String, u32>,
    ordered_bodies: Vec<String>,
}

impl AttrInterner {
    fn register_table(&mut self, table: &BTreeMap<u32, String>) -> BTreeMap<u32, u32> {
        let mut remap = BTreeMap::new();
        for (&old_id, raw_body) in table {
            let canon = raw_body.split_whitespace().collect::<Vec<_>>().join(" ");
            let new_id = if let Some(&existing) = self.body_to_id.get(&canon) {
                existing
            } else {
                let next_id = u32::try_from(self.ordered_bodies.len()).unwrap_or(0);
                self.ordered_bodies.push(canon.clone());
                self.body_to_id.insert(canon, next_id);
                next_id
            };
            remap.insert(old_id, new_id);
        }
        remap
    }

    fn emit_lines(&self) -> Vec<String> {
        self.ordered_bodies
            .iter()
            .enumerate()
            .map(|(idx, body)| format!("attributes #{idx} = {{ {body} }}"))
            .collect()
    }
}

struct MetadataArena {
    nodes: BTreeMap<u32, String>,
    next_id: u32,
}

impl MetadataArena {
    fn from_manifest(manifest_nodes: &BTreeMap<u32, String>) -> Self {
        let next_id = manifest_nodes.keys().copied().max().map_or(0, |m| m + 1);
        Self {
            nodes: manifest_nodes.clone(),
            next_id,
        }
    }

    fn absorb_slice_metadata(&mut self, slice_nodes: &BTreeMap<u32, String>) -> BTreeMap<u32, u32> {
        let mut remap = BTreeMap::new();
        for &old_id in slice_nodes.keys() {
            let fresh = self.next_id;
            self.next_id += 1;
            remap.insert(old_id, fresh);
        }
        let empty_attr = BTreeMap::new();
        for (&old_id, rhs) in slice_nodes {
            if let Some(&new_id) = remap.get(&old_id) {
                let rewritten = remap_attrs_and_metadata(rhs, &empty_attr, &remap);
                self.nodes.insert(new_id, rewritten);
            }
        }
        remap
    }
}

fn remap_attrs_and_metadata(
    line: &str,
    attr_remap: &BTreeMap<u32, u32>,
    meta_remap: &BTreeMap<u32, u32>,
) -> String {
    if attr_remap.is_empty() && meta_remap.is_empty() {
        return line.to_owned();
    }
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut out = String::with_capacity(len);
    let mut i = 0_usize;

    while i < len {
        let Some(&b) = bytes.get(i) else {
            break;
        };
        if b == b'"' {
            let start = i;
            i += 1;
            while let Some(&ch) = bytes.get(i) {
                if ch == b'\\' {
                    i = (i + 2).min(len);
                    continue;
                }
                i += 1;
                if ch == b'"' {
                    break;
                }
            }
            if let Some(seg) = line.get(start..i) {
                out.push_str(seg);
            }
            continue;
        }
        if b == b';' {
            if let Some(comment) = line.get(i..) {
                out.push_str(comment);
            }
            break;
        }

        if (b == b'#' || b == b'!') && bytes.get(i + 1).is_some_and(u8::is_ascii_digit) {
            let sigil = char::from(b);
            let num_start = i + 1;
            let mut num_end = num_start;
            while bytes.get(num_end).is_some_and(u8::is_ascii_digit) {
                num_end += 1;
            }
            let digits = line.get(num_start..num_end).unwrap_or("");
            if let Ok(old_id) = digits.parse::<u32>() {
                let mapped = if b == b'#' {
                    attr_remap.get(&old_id).copied()
                } else {
                    meta_remap.get(&old_id).copied()
                };
                if let Some(new_id) = mapped {
                    out.push(sigil);
                    out.push_str(&new_id.to_string());
                    i = num_end;
                    continue;
                }
            }
        }

        if let Some(ch) = line.get(i..).and_then(|s| s.chars().next()) {
            out.push(ch);
            i += ch.len_utf8();
        } else {
            break;
        }
    }
    out
}

fn split_function_signature_parts(
    sig: &str,
) -> Result<(String, String, String, String), BridgeError> {
    let at_pos = find_function_name_at(sig).ok_or_else(|| BridgeError::MalformedModule {
        detail: format!("missing `@name(` in function signature `{sig}`"),
    })?;
    let prefix = sig.get(..at_pos).unwrap_or("").trim().to_owned();
    let after_at = sig.get(at_pos + 1..).unwrap_or("");
    let open_paren =
        find_outside_quotes(after_at, "(").ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("missing parameter `(` in `{sig}`"),
        })?;
    let fn_name = after_at.get(..open_paren).unwrap_or("").trim().to_owned();
    let from_open = after_at.get(open_paren..).unwrap_or("");
    let close_paren =
        find_matching_delim(from_open, b'(', b')').ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("unbalanced parameter `(...)` in `{sig}`"),
        })?;
    let params_inside = from_open.get(1..close_paren).unwrap_or("").to_owned();
    let post_params = from_open
        .get(close_paren + 1..)
        .unwrap_or("")
        .trim()
        .to_owned();
    Ok((fn_name, prefix, params_inside, post_params))
}

fn find_function_name_at(sig: &str) -> Option<usize> {
    let bytes = sig.as_bytes();
    let mut i = 0_usize;
    let mut paren_depth = 0_i32;
    let mut in_quotes = false;
    while let Some(&b) = bytes.get(i) {
        if in_quotes {
            if b == b'\\' {
                i = (i + 2).min(bytes.len());
                continue;
            }
            if b == b'"' {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        match b {
            b'"' => in_quotes = true,
            b'(' => paren_depth += 1,
            b')' => paren_depth -= 1,
            b'@' if paren_depth == 0 => return Some(i),
            _ => {}
        }
        i += 1;
    }
    None
}

fn split_leading_linkage_vis(prefix: &str) -> (String, String) {
    let mut kept = Vec::new();
    let mut rest = prefix.trim_start();
    loop {
        let next_ws = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let tok = rest.get(..next_ws).unwrap_or("");
        if LINKAGE_VIS_KEYWORDS.contains(&tok) && next_ws < rest.len() {
            kept.push(tok);
            rest = rest.get(next_ws..).unwrap_or("").trim_start();
        } else {
            break;
        }
    }
    (kept.join(" "), rest.to_owned())
}

fn strip_param_names(params: &str) -> String {
    if params.trim().is_empty() {
        return String::new();
    }
    let parts = split_top_level_commas(params);
    let mut cleaned = Vec::with_capacity(parts.len());
    for part in parts {
        let p = part.trim();
        if p == "..." || p.is_empty() {
            cleaned.push(p.to_owned());
            continue;
        }
        // If the final token starts with `%` (e.g. `ptr nocapture %p` or `i32 %0`), drop that `%name`.
        if let Some(last_ws) = p.rfind(char::is_whitespace) {
            let last_tok = p.get(last_ws..).unwrap_or("").trim();
            if last_tok.starts_with('%') {
                cleaned.push(p.get(..last_ws).unwrap_or(p).trim_end().to_owned());
                continue;
            }
        }
        cleaned.push(p.to_owned());
    }
    cleaned.join(", ")
}

fn split_top_level_commas(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let mut parts = Vec::new();
    let mut start = 0_usize;
    let mut depth = 0_i32;
    let mut in_quotes = false;
    let mut i = 0_usize;

    while let Some(&b) = bytes.get(i) {
        if in_quotes {
            if b == b'\\' {
                i = (i + 2).min(bytes.len());
                continue;
            }
            if b == b'"' {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        match b {
            b'"' => in_quotes = true,
            b'(' | b'[' | b'{' | b'<' => depth += 1,
            b')' | b']' | b'}' | b'>' => depth = (depth - 1).max(0),
            b',' if depth == 0 => {
                if let Some(seg) = s.get(start..i) {
                    parts.push(seg);
                }
                start = i + 1;
            }
            _ => {}
        }
        i += 1;
    }
    if let Some(tail) = s.get(start..) {
        parts.push(tail);
    }
    parts
}

fn split_at_top_level_comma(s: &str) -> (&str, &str) {
    let parts = split_top_level_commas(s);
    let first = parts.first().copied().unwrap_or(s);
    let rest = s.get(first.len()..).unwrap_or("");
    (first, rest)
}

fn parse_balanced_llvm_type(s: &str) -> Option<(&str, &str)> {
    let trimmed = s.trim_start();
    let first = *trimmed.as_bytes().first()?;

    if let Some((open, close)) = match first {
        b'[' => Some((b'[', b']')),
        b'{' => Some((b'{', b'}')),
        b'<' => Some((b'<', b'>')),
        _ => None,
    } {
        let end = find_matching_delim(trimmed, open, close)?;
        let ty = trimmed.get(..=end)?;
        let rest = trimmed.get(end + 1..).unwrap_or("");
        return Some((ty, rest));
    }

    // Scalar, `ptr [addrspace(N)]`, or `%struct.Foo` / `%"quoted"`.
    let mut end = 0_usize;
    let bytes = trimmed.as_bytes();
    if first == b'%' && bytes.get(1) == Some(&b'"') {
        end = 2;
        while let Some(&b) = bytes.get(end) {
            if b == b'\\' {
                end = (end + 2).min(bytes.len());
                continue;
            }
            end += 1;
            if b == b'"' {
                break;
            }
        }
    } else {
        while let Some(&b) = bytes.get(end) {
            if b.is_ascii_whitespace() || matches!(b, b',' | b'(' | b')') {
                break;
            }
            end += 1;
        }
    }
    if end == 0 {
        return None;
    }
    let base_ty = trimmed.get(..end)?;
    let after_base = trimmed.get(end..).unwrap_or("");
    // Check `ptr addrspace(N)`.
    if base_ty == "ptr"
        && let Some(after_as) = after_base.trim_start().strip_prefix("addrspace(")
        && let Some(close) = after_as.find(')')
    {
        let ws_len = after_base
            .len()
            .saturating_sub(after_base.trim_start().len());
        let total_len = end + ws_len + "addrspace(".len() + close + 1;
        return Some((
            trimmed.get(..total_len)?,
            trimmed.get(total_len..).unwrap_or(""),
        ));
    }
    Some((base_ty, after_base))
}

fn find_matching_delim(s: &str, open: u8, close: u8) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut depth = 0_i32;
    let mut in_quotes = false;
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if in_quotes {
            if b == b'\\' {
                i = (i + 2).min(bytes.len());
                continue;
            }
            if b == b'"' {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        if b == b'"' {
            in_quotes = true;
        } else if b == open {
            depth += 1;
        } else if b == close {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn count_braces_outside_quotes(line: &str) -> Vec<u8> {
    let bytes = line.as_bytes();
    let mut out = Vec::new();
    let mut in_quotes = false;
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if in_quotes {
            if b == b'\\' {
                i = (i + 2).min(bytes.len());
                continue;
            }
            if b == b'"' {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        match b {
            b'"' => in_quotes = true,
            b'{' | b'}' => out.push(b),
            _ => {}
        }
        i += 1;
    }
    out
}

fn collect_prefixed_idents(text: &str, sigil: u8) -> Vec<String> {
    let mut found = Vec::new();
    for raw_line in text.lines() {
        let line = strip_line_comment_preserving_strings(raw_line);
        let bytes = line.as_bytes();
        let len = bytes.len();
        let mut i = 0_usize;
        let mut in_quotes = false;
        while let Some(&b) = bytes.get(i) {
            if in_quotes {
                if b == b'\\' {
                    i = (i + 2).min(len);
                    continue;
                }
                if b == b'"' {
                    in_quotes = false;
                }
                i += 1;
                continue;
            }
            if b == b'"' {
                in_quotes = true;
                i += 1;
                continue;
            }
            if b == sigil {
                let start = i + 1;
                let mut end = start;
                if bytes.get(end) == Some(&b'"') {
                    end += 1;
                    while let Some(&ch) = bytes.get(end) {
                        if ch == b'\\' {
                            end = (end + 2).min(len);
                            continue;
                        }
                        end += 1;
                        if ch == b'"' {
                            break;
                        }
                    }
                } else {
                    while let Some(&ch) = bytes.get(end) {
                        if ch.is_ascii_alphanumeric() || matches!(ch, b'_' | b'.' | b'$' | b'-') {
                            end += 1;
                        } else {
                            break;
                        }
                    }
                }
                if end > start
                    && let Some(ident) = line.get(start..end)
                {
                    found.push(ident.to_owned());
                }
                i = end;
                continue;
            }
            i += 1;
        }
    }
    found
}

fn collect_numeric_refs(text: &str, sigil: u8) -> BTreeSet<u32> {
    let mut ids = BTreeSet::new();
    for tok in collect_prefixed_idents(text, sigil) {
        if let Ok(n) = tok.parse::<u32>() {
            ids.insert(n);
        }
    }
    ids
}

fn extract_braced_body(rhs: &str) -> String {
    let Some((_, after_open)) = rhs.split_once('{') else {
        return rhs.to_owned();
    };
    let Some((inside, _)) = after_open.rsplit_once('}') else {
        return after_open.trim().to_owned();
    };
    inside.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn extract_top_level_align(rhs: &str) -> String {
    for part in split_top_level_commas(rhs).into_iter().skip(1) {
        let p = part.trim();
        if let Some(after) = p.strip_prefix("align ") {
            let digits: String = after.chars().take_while(char::is_ascii_digit).collect();
            if !digits.is_empty() {
                return format!(", align {digits}");
            }
        }
    }
    String::new()
}

fn extract_addrspace_clause(rhs: &str) -> String {
    if let Some(pos) = find_outside_quotes(rhs, "addrspace(") {
        let after = rhs.get(pos..).unwrap_or("");
        if let Some(close) = after.find(')')
            && let Some(clause) = after.get(..=close)
        {
            return format!(" {clause}");
        }
    }
    String::new()
}

fn find_keyword_outside_quotes(haystack: &str, kw: &str) -> Option<usize> {
    let bytes = haystack.as_bytes();
    let mut offset = 0_usize;
    while let Some(sub) = haystack.get(offset..) {
        let rel = find_outside_quotes(sub, kw)?;
        let abs = offset + rel;
        let prev_ok = abs == 0 || bytes.get(abs - 1).is_some_and(|b| b.is_ascii_whitespace());
        if prev_ok {
            return Some(abs);
        }
        offset = abs + 1;
    }
    None
}

fn contains_bare_keyword(haystack: &str, kw: &str) -> bool {
    let scrubbed = crate::vellvm_sanitize::mask_quoted_strings(haystack);
    scrubbed
        .split(|c: char| c.is_ascii_whitespace() || c == ',')
        .any(|t| t == kw)
}

fn extract_first_attr_group(post: &str) -> Option<u32> {
    collect_numeric_refs(post, b'#').into_iter().next()
}

fn extract_section_clause(post: &str) -> Option<String> {
    let pos = find_outside_quotes(post, "section \"")?;
    let after_quote = post.get(pos + "section \"".len()..)?;
    let end_quote = find_outside_quotes_unescaped_quote(after_quote)?;
    let val = after_quote.get(..end_quote)?;
    Some(format!("section \"{val}\""))
}

fn find_outside_quotes_unescaped_quote(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if b == b'\\' {
            i = (i + 2).min(bytes.len());
            continue;
        }
        if b == b'"' {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn extract_comdat_clause(post: &str) -> Option<String> {
    if let Some(pos) = find_outside_quotes(post, "comdat(") {
        let from_cd = post.get(pos..)?;
        let close = find_matching_delim(from_cd.get("comdat".len()..)?, b'(', b')')?;
        return from_cd
            .get(.."comdat".len() + close + 1)
            .map(ToOwned::to_owned);
    }
    if contains_bare_keyword(post, "comdat") {
        return Some("comdat".to_owned());
    }
    None
}

fn extract_func_align_clause(post: &str) -> Option<String> {
    let pos = find_keyword_outside_quotes(post, "align ")?;
    let after = post.get(pos + "align ".len()..)?;
    let digits: String = after.chars().take_while(char::is_ascii_digit).collect();
    if digits.is_empty() {
        None
    } else {
        Some(format!("align {digits}"))
    }
}

fn extract_personality_clause(post: &str) -> Option<String> {
    let pos = find_keyword_outside_quotes(post, "personality ")?;
    let after = post.get(pos + "personality ".len()..)?.trim_start();
    let (ty, rest) = parse_balanced_llvm_type(after)?;
    let rest_trim = rest.trim_start();
    let end_tok = rest_trim
        .find(char::is_whitespace)
        .unwrap_or(rest_trim.len());
    let fn_tok = rest_trim.get(..end_tok)?;
    if fn_tok.is_empty() {
        None
    } else {
        Some(format!("personality {ty} {fn_tok}"))
    }
}

fn extract_metadata_attachments(post: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = post;
    while let Some(pos) = find_outside_quotes(cur, "!") {
        let from_bang = cur.get(pos..).unwrap_or("");
        let mut iter = from_bang.split_whitespace();
        let Some(k) = iter.next() else {
            break;
        };
        let Some(v) = iter.next() else {
            break;
        };
        if k.starts_with('!') && v.starts_with('!') {
            out.push(format!("{k} {v}"));
            let advance = k.len() + 1 + v.len();
            cur = from_bang.get(advance..).unwrap_or("");
        } else {
            cur = from_bang.get(1..).unwrap_or("");
        }
    }
    out
}
