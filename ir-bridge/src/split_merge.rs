use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::error::BridgeError;
use crate::vellvm_sanitize::{
    SliceRole, canonical_llvm_ident_key, find_outside_quotes, mask_quoted_strings,
    sanitize_for_vellvm, strip_declare_metadata, strip_line_comment_preserving_strings,
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
    /// True for `@llvm.global_ctors`, `@llvm.global_dtors`, `@llvm.used`, `@llvm.compiler.used` (`F-24`).
    #[serde(default)]
    pub elide_in_slice: bool,
    /// True when `@sym = ... alias ...` uses a GEP/bitcast constant expression (`F-33`).
    #[serde(default)]
    pub is_const_expr_alias: bool,
}

/// External function prototype (`declare ... @callee(...)`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclRecord {
    pub name: String,
    pub raw_line: String,
    pub sanitized_slice_decl: String,
}

/// Original signature, linkage, visibility, section, comdat, alignment, and attribute properties of
/// a defined function, preserved in `ModuleManifest` and restored during `merge_module` (`F-19`, `F-24`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionManifestEntry {
    pub name: String,
    pub original_linkage_vis: String,
    #[serde(default)]
    pub original_cconv_and_ret: String,
    #[serde(default)]
    pub original_param_types_and_attrs: Vec<String>,
    pub unnamed_addr: Option<String>,
    #[serde(default)]
    pub addrspace: Option<String>,
    #[serde(default)]
    pub original_fn_attrs_and_groups: Vec<String>,
    pub section: Option<String>,
    #[serde(default)]
    pub partition: Option<String>,
    pub comdat: Option<String>,
    pub align: Option<String>,
    #[serde(default)]
    pub gc: Option<String>,
    #[serde(default)]
    pub prefix: Option<String>,
    #[serde(default)]
    pub prologue: Option<String>,
    #[serde(default)]
    pub original_attr_group: Option<u32>,
    #[serde(default)]
    pub original_personality: Option<String>,
    #[serde(default)]
    pub original_header_metadata: Vec<String>,
    pub prototype_declare: String,
    pub splittable: bool,
    pub non_splittable_reason: Option<String>,
    #[serde(default)]
    pub raw_unmodified_lines: Vec<String>,
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

const UNWINDING_INSTRUCTIONS: &[&str] = &[
    "invoke",
    "landingpad",
    "resume",
    "catchswitch",
    "catchpad",
    "cleanuppad",
    "catchret",
    "cleanupret",
    "callbr",
];

/// Unverified `-O2` optimization/alias metadata attachments stripped from merged Fast-Path bodies (`F-19`).
const UNVERIFIED_OPT_METADATA_KINDS: &[&str] = &[
    "!tbaa.struct",
    "!tbaa",
    "!alias.scope",
    "!noalias",
    "!llvm.access.group",
    "!invariant.load",
    "!invariant.group",
];

/// Deterministically validates an LLVM `target datalayout` specification against Vellvm 3.0's
/// little-endian 64-bit pointer (`IP64Bit` / `LP64`) memory model (`F-22`).
///
/// Requires explicit little-endian `e` (rejecting big-endian `E`) and 64-bit address-space-0
/// pointers (either LLVM's default 64-bit `p0` or explicit `p:64:64...` / `p0:64:64...`), while
/// permitting non-zero address spaces such as `p270:32:32`.
pub fn validate_target_datalayout(datalayout_line_or_spec: &str) -> Result<(), BridgeError> {
    let trimmed = datalayout_line_or_spec.trim();
    let spec = if let Some(after_kw) = trimmed.strip_prefix("target datalayout") {
        let Some((_, rhs)) = after_kw.split_once('=') else {
            return Err(BridgeError::UnsupportedDataLayout {
                datalayout: trimmed.to_owned(),
                reason: "malformed `target datalayout` directive (missing `=`)".to_owned(),
            });
        };
        let rhs_trim = rhs.trim();
        let Some(unquoted) = rhs_trim.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
            return Err(BridgeError::UnsupportedDataLayout {
                datalayout: rhs_trim.to_owned(),
                reason: "malformed `target datalayout` directive (expected quoted layout string)"
                    .to_owned(),
            });
        };
        unquoted
    } else {
        trimmed
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .unwrap_or(trimmed)
    };

    let segments: Vec<&str> = spec.split('-').filter(|s| !s.is_empty()).collect();
    if segments.contains(&"E") {
        return Err(BridgeError::UnsupportedDataLayout {
            datalayout: spec.to_owned(),
            reason:
                "big-endian `E` layout is unsupported; Vellvm IP64Bit requires little-endian `e` (F-22)"
                    .to_owned(),
        });
    }
    if !segments.contains(&"e") {
        return Err(BridgeError::UnsupportedDataLayout {
            datalayout: spec.to_owned(),
            reason: "missing little-endian `e` specification in target datalayout (F-22)"
                .to_owned(),
        });
    }

    for seg in segments {
        if let Some(after_p) = seg.strip_prefix('p') {
            let fields: Vec<&str> = after_p.split(':').collect();
            let addrspace = fields.first().copied().unwrap_or("");
            if addrspace.is_empty() || addrspace == "0" {
                let ptr_size = fields.get(1).copied().unwrap_or("");
                if ptr_size != "64" {
                    return Err(BridgeError::UnsupportedDataLayout {
                        datalayout: spec.to_owned(),
                        reason: format!(
                            "address space 0 pointer size in `{seg}` must be 64 bits for Vellvm IP64Bit (F-22)"
                        ),
                    });
                }
                if let Some(&abi_align) = fields.get(2)
                    && abi_align != "64"
                {
                    return Err(BridgeError::UnsupportedDataLayout {
                        datalayout: spec.to_owned(),
                        reason: format!(
                            "address space 0 pointer ABI alignment in `{seg}` must be 64 bits (F-22)"
                        ),
                    });
                }
                if let Some(&idx_width) = fields.get(4)
                    && idx_width != "64"
                {
                    return Err(BridgeError::UnsupportedDataLayout {
                        datalayout: spec.to_owned(),
                        reason: format!(
                            "address space 0 pointer index width in `{seg}` must be 64 bits (F-22)"
                        ),
                    });
                }
            }
        }
    }

    Ok(())
}

/// Splits a whole LLVM 23.1.5 `.ll` module into a `ModuleManifest` plus one isolated,
/// `GlobalOpt`- and `GlobalDCE`-sound `<fn>.input.ll` slice per splittable function.
pub fn split_module(module_ir: &str) -> Result<SplitOutput, BridgeError> {
    let parsed = parse_raw_module(module_ir)?;

    let type_map: BTreeMap<String, &TypeDefRecord> = parsed
        .manifest
        .type_defs
        .iter()
        .map(|t| {
            let key = canonical_llvm_ident_key(t.ident.strip_prefix('%').unwrap_or(&t.ident));
            (key, t)
        })
        .collect();
    let global_map: BTreeMap<String, &GlobalRecord> = parsed
        .manifest
        .globals
        .iter()
        .map(|g| (canonical_llvm_ident_key(&g.name), g))
        .collect();

    // Build combined canonical symbol -> sanitized `declare` lookup (external declares + sibling defines).
    let mut callee_decl_map: BTreeMap<String, String> = BTreeMap::new();
    for d in &parsed.manifest.declarations {
        callee_decl_map.insert(
            canonical_llvm_ident_key(&d.name),
            d.sanitized_slice_decl.clone(),
        );
    }
    for f in &parsed.manifest.functions {
        callee_decl_map.insert(
            canonical_llvm_ident_key(&f.name),
            f.prototype_declare.clone(),
        );
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
/// original `ModuleManifest`, restoring original `input.ll` function headers/attributes (`F-19`),
/// stripping unverified `-O2` alias metadata (`F-19`), supporting non-splittable/whole-module
/// pass-through (`F-24`), and globally re-indexing `#N` and `!N` without collisions.
pub fn merge_module(
    manifest: &ModuleManifest,
    verified_slices: &BTreeMap<String, String>,
) -> Result<String, BridgeError> {
    if let Some(dl) = &manifest.target_datalayout {
        validate_target_datalayout(dl)?;
    }

    let mut attr_interner = AttrInterner::default();
    let mut meta_pool = MetadataArena::from_manifest(&manifest.numbered_metadata);

    let manifest_attr_remap = attr_interner.register_table(&manifest.attr_groups);
    let identity_meta_remap: BTreeMap<u32, u32> = manifest
        .numbered_metadata
        .keys()
        .map(|&id| (id, id))
        .collect();

    let whole_module_parsed = if let Some(whole_ir) = verified_slices.get("__module__") {
        Some(parse_raw_module(whole_ir)?)
    } else {
        None
    };

    let mut merged_types: Vec<TypeDefRecord> = manifest.type_defs.clone();
    let mut seen_types: BTreeSet<String> = merged_types
        .iter()
        .map(|t| canonical_llvm_ident_key(&t.ident))
        .collect();

    let defined_fn_names: BTreeSet<String> = manifest
        .functions
        .iter()
        .map(|f| canonical_llvm_ident_key(&f.name))
        .collect();
    let mut seen_decls: BTreeSet<String> = manifest
        .declarations
        .iter()
        .map(|d| canonical_llvm_ident_key(&d.name))
        .collect();
    let mut extra_synthesized_decls: Vec<String> = Vec::new();
    let mut rendered_functions: Vec<String> = Vec::with_capacity(manifest.functions.len());

    for fn_meta in &manifest.functions {
        let parsed_storage: Option<ParsedModule> =
            if let Some(slice_ir) = verified_slices.get(&fn_meta.name) {
                Some(parse_raw_module(slice_ir)?)
            } else {
                None
            };

        let active_parsed = parsed_storage.as_ref().or(whole_module_parsed.as_ref());

        let Some(slice_parsed) = active_parsed else {
            if !fn_meta.splittable && !fn_meta.raw_unmodified_lines.is_empty() {
                rendered_functions.push(restore_unmodified_manifest_function(
                    fn_meta,
                    &manifest_attr_remap,
                    &identity_meta_remap,
                ));
                continue;
            }
            return Err(BridgeError::MissingVerifiedSlice {
                function_name: fn_meta.name.clone(),
            });
        };

        let target_raw_fn = slice_parsed
            .raw_functions
            .iter()
            .find(|rf| {
                rf.name == fn_meta.name
                    || canonical_llvm_ident_key(&rf.name) == canonical_llvm_ident_key(&fn_meta.name)
            })
            .or_else(|| {
                if slice_parsed.raw_functions.len() == 1 {
                    slice_parsed.raw_functions.first()
                } else {
                    None
                }
            })
            .ok_or_else(|| BridgeError::MalformedModule {
                detail: format!(
                    "verified slice for `@{}` contains no matching `define` body",
                    fn_meta.name
                ),
            })?;

        // Collect any new `%struct.* = type ...` synthesized by `opt -O2`.
        for td in &slice_parsed.manifest.type_defs {
            if seen_types.insert(canonical_llvm_ident_key(&td.ident)) {
                merged_types.push(td.clone());
            }
        }

        // Strip unverified `-O2` optimization/alias metadata from body lines first (`F-19`)
        // so orphaned `!tbaa` / `!alias.scope` / `!noalias` nodes are never absorbed.
        let stripped_body_lines: Vec<String> = target_raw_fn
            .raw_lines
            .iter()
            .skip(1)
            .map(|l| strip_unverified_opt_metadata(l))
            .collect();

        let mut pending_new_decls: Vec<&DeclRecord> = Vec::new();
        for decl in &slice_parsed.manifest.declarations {
            let decl_key = canonical_llvm_ident_key(&decl.name);
            if !defined_fn_names.contains(&decl_key) && seen_decls.insert(decl_key) {
                pending_new_decls.push(decl);
            }
        }

        // Register ONLY `#N` attribute groups and transitive `!N` metadata nodes actually
        // referenced by synthesized declarations or the stripped body (`F-19`).
        let mut used_slice_attrs = BTreeSet::new();
        let mut meta_worklist: Vec<u32> = Vec::new();
        for decl in &pending_new_decls {
            used_slice_attrs.extend(collect_numeric_refs(&decl.raw_line, b'#'));
            meta_worklist.extend(collect_numeric_refs(&decl.raw_line, b'!'));
        }
        for bl in &stripped_body_lines {
            used_slice_attrs.extend(collect_numeric_refs(bl, b'#'));
            meta_worklist.extend(collect_numeric_refs(bl, b'!'));
        }

        let filtered_slice_attrs: BTreeMap<u32, String> = slice_parsed
            .manifest
            .attr_groups
            .iter()
            .filter(|(id, _)| used_slice_attrs.contains(id))
            .map(|(&id, body)| (id, body.clone()))
            .collect();
        let slice_attr_remap = attr_interner.register_table(&filtered_slice_attrs);

        let mut used_slice_metas = BTreeSet::new();
        while let Some(mid) = meta_worklist.pop() {
            if let Some(rhs) = slice_parsed.manifest.numbered_metadata.get(&mid)
                && used_slice_metas.insert(mid)
            {
                meta_worklist.extend(collect_numeric_refs(rhs, b'!'));
            }
        }
        let filtered_slice_metas: BTreeMap<u32, String> = slice_parsed
            .manifest
            .numbered_metadata
            .iter()
            .filter(|(id, _)| used_slice_metas.contains(id))
            .map(|(&id, rhs)| (id, rhs.clone()))
            .collect();
        let slice_meta_remap = meta_pool.absorb_slice_metadata(&filtered_slice_metas);

        for decl in pending_new_decls {
            let remapped_decl =
                remap_attrs_and_metadata(&decl.raw_line, &slice_attr_remap, &slice_meta_remap);
            extra_synthesized_decls.push(remapped_decl);
        }

        let remap_tables = RemapTables {
            manifest_attr: &manifest_attr_remap,
            identity_meta: &identity_meta_remap,
            slice_attr: &slice_attr_remap,
            slice_meta: &slice_meta_remap,
        };
        let restored_fn = restore_and_remap_function(
            fn_meta,
            target_raw_fn,
            &stripped_body_lines,
            &remap_tables,
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
            validate_target_datalayout(code)?;
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
            && let Some(eq_idx) = find_outside_quotes(code, "=")
            && let (Some(lhs), Some(rhs)) = (code.get(..eq_idx), code.get(eq_idx + 1..))
            && rhs.trim_start().starts_with("type")
        {
            let after_type = rhs.trim_start().strip_prefix("type").unwrap_or("");
            if after_type.is_empty()
                || after_type.starts_with(char::is_whitespace)
                || after_type.starts_with('{')
                || after_type.starts_with('<')
                || after_type.starts_with('[')
            {
                manifest.type_defs.push(TypeDefRecord {
                    ident: lhs.trim().to_owned(),
                    raw_line: code.to_owned(),
                });
                idx += 1;
                continue;
            }
        }
        if code.starts_with('@') && find_outside_quotes(code, "=").is_some() {
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

    // Filter out `!dbg` or dangling metadata IDs not defined in `manifest.numbered_metadata`
    // from `original_header_metadata`, and propagate cross-function `blockaddress` (`F-24`)
    // and constant-expression `alias` (`F-33`) non-splittable constraints across the module.
    finalize_manifest_constraints(&mut manifest, &raw_functions);

    Ok(ParsedModule {
        manifest,
        raw_functions,
    })
}

fn finalize_manifest_constraints(manifest: &mut ModuleManifest, raw_functions: &[RawFunctionDef]) {
    for fn_meta in &mut manifest.functions {
        fn_meta.original_header_metadata.retain(|attach| {
            if attach.starts_with("!dbg ") {
                return false;
            }
            collect_numeric_refs(attach, b'!')
                .iter()
                .all(|id| manifest.numbered_metadata.contains_key(id))
        });
    }

    // 1. Cross-function or global `blockaddress(@target_fn, %bb)` (`F-24` & `F-52`):
    //    mark `@target_fn` non-splittable too so its basic-block labels cannot be deleted in isolation!
    let mut blockaddr_targets: BTreeMap<String, String> = BTreeMap::new();
    for g in &manifest.globals {
        for target_fn in collect_blockaddress_targets(&g.raw_line) {
            blockaddr_targets
                .entry(canonical_llvm_ident_key(&target_fn))
                .or_insert_with(|| {
                    format!("target of global `blockaddress` in `@{}` (F-24)", g.name)
                });
        }
    }
    for rf in raw_functions {
        let rf_key = canonical_llvm_ident_key(&rf.name);
        let body = rf.raw_lines.join("\n");
        for target_fn in collect_blockaddress_targets(&body) {
            let target_key = canonical_llvm_ident_key(&target_fn);
            if target_key != rf_key {
                blockaddr_targets.entry(target_key).or_insert_with(|| {
                    format!(
                        "target of cross-function `blockaddress` from `@{}` (F-24)",
                        rf.name
                    )
                });
            }
        }
    }

    // 2. Constant-expression global `alias` (`F-33` & `F-52`): mark referencing functions non-splittable
    //    so `opt -O2` BasicAA never treats a degraded `external global` alias as disjoint from its base!
    let const_expr_aliases: BTreeSet<String> = manifest
        .globals
        .iter()
        .filter(|g| g.is_const_expr_alias)
        .map(|g| canonical_llvm_ident_key(&g.name))
        .collect();

    for (fn_meta, rf) in manifest.functions.iter_mut().zip(raw_functions.iter()) {
        let fn_key = canonical_llvm_ident_key(&fn_meta.name);
        if fn_meta.splittable
            && let Some(reason) = blockaddr_targets.get(&fn_key)
        {
            fn_meta.splittable = false;
            fn_meta.non_splittable_reason = Some(reason.clone());
        }
        if fn_meta.splittable && !const_expr_aliases.is_empty() {
            let fn_text = rf.raw_lines.join("\n");
            for sym in collect_prefixed_idents(&fn_text, b'@') {
                let sym_key = canonical_llvm_ident_key(&sym);
                if const_expr_aliases.contains(&sym_key) {
                    fn_meta.splittable = false;
                    fn_meta.non_splittable_reason = Some(format!(
                        "references constant-expression global `alias @{sym}` (F-33)"
                    ));
                    break;
                }
            }
        }
    }
}

pub(crate) fn is_elided_module_intrinsic_global(sym: &str) -> bool {
    let canonical = canonical_llvm_ident_key(sym);
    matches!(
        canonical.as_str(),
        "llvm.global_ctors" | "llvm.global_dtors" | "llvm.used" | "llvm.compiler.used"
    )
}

pub(crate) fn is_const_expr_alias_line(code: &str) -> bool {
    let Some(eq_idx) = find_outside_quotes(code, "=") else {
        return false;
    };
    let Some(rhs_raw) = code.get(eq_idx + 1..) else {
        return false;
    };
    let rhs = rhs_raw.trim();
    let Some(pos) = find_keyword_outside_quotes(rhs, "alias ") else {
        return false;
    };
    let after_kw = rhs.get(pos + "alias ".len()..).unwrap_or("").trim_start();
    let Some((_, after_ty)) = parse_balanced_llvm_type(after_kw) else {
        return true;
    };
    let aliasee = after_ty
        .trim_start()
        .strip_prefix(',')
        .unwrap_or(after_ty)
        .trim();
    let aliasee_first = split_at_top_level_comma(aliasee).0.trim();
    aliasee_first.contains('(')
        || contains_bare_keyword(aliasee_first, "getelementptr")
        || contains_bare_keyword(aliasee_first, "bitcast")
        || contains_bare_keyword(aliasee_first, "addrspacecast")
        || contains_bare_keyword(aliasee_first, "inttoptr")
}

fn parse_global_record(code: &str) -> Result<GlobalRecord, BridgeError> {
    let eq_idx = find_outside_quotes(code, "=").ok_or_else(|| BridgeError::MalformedModule {
        detail: format!("invalid global definition `{code}`"),
    })?;
    let lhs = code.get(..eq_idx).unwrap_or("");
    let rhs_raw = code.get(eq_idx + 1..).unwrap_or("");
    let sym = lhs
        .trim()
        .strip_prefix('@')
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("global `{lhs}` missing `@`"),
        })?
        .to_owned();
    let rhs = rhs_raw.trim();

    if is_elided_module_intrinsic_global(&sym) {
        return Ok(GlobalRecord {
            name: sym,
            raw_line: code.to_owned(),
            slice_decl: String::new(),
            elide_in_slice: true,
            is_const_expr_alias: false,
        });
    }

    let is_const_expr_alias = is_const_expr_alias_line(code);
    let slice_decl = build_sound_global_slice_decl(&sym, rhs)?;
    Ok(GlobalRecord {
        name: sym,
        raw_line: code.to_owned(),
        slice_decl,
        elide_in_slice: false,
        is_const_expr_alias,
    })
}

/// Rewrites a module-level `@global` / `@constant` / `@alias` / `@ifunc` into a sound declaration
/// for isolated per-function optimization (`GlobalOpt` protection, `F-24` `thread_local`, `F-33` `extern_weak`).
fn build_sound_global_slice_decl(sym: &str, rhs: &str) -> Result<String, BridgeError> {
    let align_suffix = extract_top_level_align(rhs);
    let tls_piece = extract_thread_local_clause(rhs);
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
            let prefix_mods = rhs.get(..pos).unwrap_or("");
            let ext_kw = if contains_bare_keyword(prefix_mods, "extern_weak") {
                "extern_weak"
            } else {
                "external"
            };
            let after_kw = rhs.get(pos + kw.len()..).unwrap_or("").trim_start();
            let (ty, _) =
                parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                    detail: format!("unable to parse `{kw}` type for `@{sym}`"),
                })?;
            let ty_without_comma = ty.trim_end_matches(',').trim();
            return Ok(format!(
                "@{sym} = {ext_kw}{tls_piece}{addrspace_piece} global {ty_without_comma}"
            ));
        }
    }

    if let Some(pos) = find_keyword_outside_quotes(rhs, "global ") {
        let prefix_mods = rhs.get(..pos).unwrap_or("");
        let ext_kw = if contains_bare_keyword(prefix_mods, "extern_weak") {
            "extern_weak"
        } else {
            "external"
        };
        let after_kw = rhs.get(pos + "global ".len()..).unwrap_or("").trim_start();
        let (ty, _) =
            parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                detail: format!("unable to parse `global` type for `@{sym}`"),
            })?;
        // Mutable globals MUST become `external`/`extern_weak` without initializer so `opt -O2`
        // (`GlobalOpt`) never assumes zero writers in the isolated slice.
        return Ok(format!(
            "@{sym} = {ext_kw}{tls_piece}{addrspace_piece} global {ty}{align_suffix}"
        ));
    }

    if let Some(pos) = find_keyword_outside_quotes(rhs, "constant ") {
        let prefix_mods = rhs.get(..pos).unwrap_or("");
        let is_extern_weak = contains_bare_keyword(prefix_mods, "extern_weak");
        let ext_kw = if is_extern_weak {
            "extern_weak"
        } else {
            "external"
        };
        let after_kw = rhs
            .get(pos + "constant ".len()..)
            .unwrap_or("")
            .trim_start();
        let (ty, after_ty) =
            parse_balanced_llvm_type(after_kw).ok_or_else(|| BridgeError::MalformedModule {
                detail: format!("unable to parse `constant` type for `@{sym}`"),
            })?;

        let is_external_only = contains_bare_keyword(prefix_mods, "external") || is_extern_weak;
        let is_interposable = contains_bare_keyword(prefix_mods, "weak")
            || contains_bare_keyword(prefix_mods, "linkonce")
            || contains_bare_keyword(prefix_mods, "common")
            || contains_bare_keyword(prefix_mods, "appending");

        let init_str = split_at_top_level_comma(after_ty.trim()).0.trim();
        let has_unsupported_const_expr =
            init_str.contains("inrange(") || init_str.contains("blockaddress(");

        if is_external_only
            || is_interposable
            || !tls_piece.is_empty()
            || init_str.is_empty()
            || has_unsupported_const_expr
        {
            return Ok(format!(
                "@{sym} = {ext_kw}{tls_piece}{unnamed_piece}{addrspace_piece} constant {ty}{align_suffix}"
            ));
        }

        // Definitive read-only non-TLS constant: emit as `available_externally constant <Ty> <Init>`.
        return Ok(format!(
            "@{sym} = available_externally{unnamed_piece}{addrspace_piece} constant {ty} {init_str}{align_suffix}"
        ));
    }

    Err(BridgeError::MalformedModule {
        detail: format!("unrecognized global/constant kind on `@{sym} = {rhs}`"),
    })
}

fn parse_declaration_record(code: &str) -> Result<DeclRecord, BridgeError> {
    let metadata_free = strip_declare_metadata(code);
    let clean_rest = metadata_free
        .trim_start()
        .strip_prefix("declare ")
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: format!("invalid declaration `{code}`"),
        })?
        .trim_start();

    let (name, prefix_mods_and_ret, params_inside, post_params) =
        split_function_signature_parts(clean_rest)?;
    let (leading_link_vis, cconv_and_ret) = split_leading_linkage_vis(&prefix_mods_and_ret);
    let link_piece = if leading_link_vis
        .split_whitespace()
        .any(|w| w == "extern_weak")
    {
        "extern_weak "
    } else {
        ""
    };
    let nameless_params = strip_param_names(&params_inside);
    let post = parse_post_param_header(&post_params);
    let decl_post = format_declare_post_params(&post);

    let sanitized_slice_decl =
        format!("declare {link_piece}{cconv_and_ret} @{name}({nameless_params}){decl_post}");
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
    let post = parse_post_param_header(&post_params);

    let original_param_types_and_attrs = parse_param_types_and_attrs(&params_inside);
    let nameless_params = original_param_types_and_attrs.join(", ");
    let decl_post = format_declare_post_params(&post);
    let prototype_declare =
        format!("declare {cconv_and_ret} @{name}({nameless_params}){decl_post}");

    // Widen linkage to external (`dso_local`) in `<fn>.input.ll` while preserving ALL original
    // inline function attributes (`noinline`, `optnone`, `strictfp`, `naked`, `noreturn`, etc.)
    // and ALL `#N` attribute-group refs (`F-54`).
    let mut slice_post = Vec::new();
    if let Some(ua) = &post.unnamed_addr {
        slice_post.push(ua.clone());
    }
    if let Some(as_clause) = &post.addrspace {
        slice_post.push(as_clause.clone());
    }
    slice_post.extend(post.fn_attrs_and_groups.iter().cloned());
    if let Some(al) = &post.align {
        slice_post.push(al.clone());
    }
    if let Some(gc) = &post.gc {
        slice_post.push(gc.clone());
    }
    if let Some(pref) = &post.prefix {
        slice_post.push(pref.clone());
    }
    if let Some(prol) = &post.prologue {
        slice_post.push(prol.clone());
    }
    if let Some(pers) = &post.personality {
        slice_post.push(pers.clone());
    }
    let slice_post_str = if slice_post.is_empty() {
        String::new()
    } else {
        format!(" {}", slice_post.join(" "))
    };
    let widened_header =
        format!("define dso_local {cconv_and_ret} @{name}({params_inside}){slice_post_str} {{");

    let full_body = fn_lines.join("\n");
    let non_splittable_reason = check_unwinding_in_function(fn_lines, post.personality.is_some())
        .or_else(|| check_cross_function_blockaddress(&full_body, &name));

    let first_attr_grp = post
        .fn_attrs_and_groups
        .iter()
        .find_map(|tok| tok.strip_prefix('#')?.parse::<u32>().ok());

    let meta = FunctionManifestEntry {
        name: name.clone(),
        original_linkage_vis,
        original_cconv_and_ret: cconv_and_ret,
        original_param_types_and_attrs,
        unnamed_addr: post.unnamed_addr,
        addrspace: post.addrspace,
        original_fn_attrs_and_groups: post.fn_attrs_and_groups,
        section: post.section,
        partition: post.partition,
        comdat: post.comdat,
        align: post.align,
        gc: post.gc,
        prefix: post.prefix,
        prologue: post.prologue,
        original_attr_group: first_attr_grp,
        original_personality: post.personality,
        original_header_metadata: post.metadata,
        prototype_declare,
        splittable: non_splittable_reason.is_none(),
        non_splittable_reason,
        raw_unmodified_lines: fn_lines.to_vec(),
    };
    let raw_fn = RawFunctionDef {
        name,
        widened_header,
        raw_lines: fn_lines.to_vec(),
    };
    Ok((meta, raw_fn))
}

fn check_unwinding_in_function(fn_lines: &[String], has_personality: bool) -> Option<String> {
    if has_personality {
        return Some("function carries `personality` unwinding handler (F-34)".to_owned());
    }
    for body_line in fn_lines.iter().skip(1) {
        let code = strip_line_comment_preserving_strings(body_line).trim();
        let scrubbed = mask_quoted_strings(code);
        for tok in scrubbed.split(|c: char| c.is_ascii_whitespace() || matches!(c, ',' | '(' | ')'))
        {
            if UNWINDING_INSTRUCTIONS.contains(&tok) {
                return Some(format!(
                    "contains unwinding/exception instruction `{tok}` (F-34)"
                ));
            }
        }
    }
    None
}

fn collect_blockaddress_targets(text: &str) -> Vec<String> {
    let mut targets = Vec::new();
    for raw_line in text.lines() {
        let line = strip_line_comment_preserving_strings(raw_line);
        let mut rest = line;
        while let Some(pos) = find_outside_quotes(rest, "blockaddress(") {
            let after = rest.get(pos + "blockaddress(".len()..).unwrap_or("");
            if let Some(at_pos) = find_outside_quotes(after, "@") {
                let after_at = after.get(at_pos + 1..).unwrap_or("");
                let target_fn = if after_at.starts_with('"') {
                    let mut end = 1_usize;
                    let a_bytes = after_at.as_bytes();
                    while let Some(&ch) = a_bytes.get(end) {
                        end += 1;
                        if ch == b'"' {
                            break;
                        }
                    }
                    after_at.get(..end).unwrap_or("").to_owned()
                } else {
                    after_at
                        .chars()
                        .take_while(|c| {
                            c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$' | '-')
                        })
                        .collect()
                };
                if !target_fn.is_empty() {
                    targets.push(target_fn);
                }
            }
            rest = after;
        }
    }
    targets
}

fn check_cross_function_blockaddress(fn_body: &str, self_name: &str) -> Option<String> {
    let self_key = canonical_llvm_ident_key(self_name);
    for target_fn in collect_blockaddress_targets(fn_body) {
        if canonical_llvm_ident_key(&target_fn) != self_key {
            return Some(format!(
                "references cross-function `blockaddress(@{target_fn}, ...)` (F-24)"
            ));
        }
    }
    None
}

fn build_single_function_slice(
    manifest: &ModuleManifest,
    raw_fn: &RawFunctionDef,
    type_map: &BTreeMap<String, &TypeDefRecord>,
    global_map: &BTreeMap<String, &GlobalRecord>,
    callee_decl_map: &BTreeMap<String, String>,
) -> String {
    let mut fn_lines = raw_fn.raw_lines.clone();
    if let Some(first) = fn_lines.first_mut() {
        *first = raw_fn.widened_header.clone();
    }
    let fn_text = fn_lines.join("\n");
    let self_key = canonical_llvm_ident_key(&raw_fn.name);

    // 1. Collect transitively referenced `@symbols` (`globals` + `declarations` / sibling `define`s),
    //    skipping elided module arrays (`@llvm.global_ctors`, `@llvm.used`, etc., `F-24`).
    let mut kept_globals: BTreeSet<String> = BTreeSet::new();
    let mut kept_callees: BTreeSet<String> = BTreeSet::new();
    let mut symbol_worklist: Vec<String> = collect_prefixed_idents(&fn_text, b'@');

    while let Some(sym) = symbol_worklist.pop() {
        let sym_key = canonical_llvm_ident_key(&sym);
        if sym_key == self_key {
            continue;
        }
        if let Some(g) = global_map.get(&sym_key) {
            if g.elide_in_slice || g.slice_decl.is_empty() {
                continue;
            }
            if kept_globals.insert(sym_key) {
                symbol_worklist.extend(collect_prefixed_idents(&g.slice_decl, b'@'));
            }
        } else if callee_decl_map.contains_key(&sym_key) {
            kept_callees.insert(sym_key);
        }
    }

    // 2. Collect transitive closure of `%struct.* = type ...` across function, kept globals & kept callees
    //    (prevents Vellvm's `TypToDtyp.v:187-192` silent `DTYPE_Void` size-0 bug!).
    let mut type_seeds = collect_prefixed_idents(&fn_text, b'%');
    for g_key in &kept_globals {
        if let Some(g) = global_map.get(g_key) {
            type_seeds.extend(collect_prefixed_idents(&g.slice_decl, b'%'));
        }
    }
    for c_key in &kept_callees {
        if let Some(decl) = callee_decl_map.get(c_key) {
            type_seeds.extend(collect_prefixed_idents(decl, b'%'));
        }
    }

    let mut kept_type_keys: BTreeSet<String> = BTreeSet::new();
    while let Some(cand) = type_seeds.pop() {
        let cand_key = canonical_llvm_ident_key(&cand);
        if let Some(td) = type_map.get(&cand_key)
            && kept_type_keys.insert(cand_key)
        {
            type_seeds.extend(collect_prefixed_idents(&td.raw_line, b'%'));
        }
    }
    // LLVM `LLParser::parseUnnamedType` requires `%0 .. %k` without gaps if any numbered type `%k` is kept.
    let max_numbered_type = kept_type_keys
        .iter()
        .filter_map(|id| id.parse::<u32>().ok())
        .max();
    if let Some(max_k) = max_numbered_type {
        for k in 0..=max_k {
            let num_key = k.to_string();
            if type_map.contains_key(&num_key) {
                kept_type_keys.insert(num_key);
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

    if !kept_type_keys.is_empty() {
        for td in &manifest.type_defs {
            let td_key = canonical_llvm_ident_key(td.ident.strip_prefix('%').unwrap_or(&td.ident));
            if kept_type_keys.contains(&td_key) {
                out.push(td.raw_line.clone());
            }
        }
        out.push(String::new());
    }

    if !kept_globals.is_empty() {
        for g in &manifest.globals {
            if !g.elide_in_slice && kept_globals.contains(&canonical_llvm_ident_key(&g.name)) {
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

fn restore_unmodified_manifest_function(
    fn_meta: &FunctionManifestEntry,
    manifest_attr_remap: &BTreeMap<u32, u32>,
    identity_meta_remap: &BTreeMap<u32, u32>,
) -> String {
    fn_meta
        .raw_unmodified_lines
        .iter()
        .map(|l| remap_attrs_and_metadata(l, manifest_attr_remap, identity_meta_remap))
        .collect::<Vec<_>>()
        .join("\n")
}

struct RemapTables<'a> {
    manifest_attr: &'a BTreeMap<u32, u32>,
    identity_meta: &'a BTreeMap<u32, u32>,
    slice_attr: &'a BTreeMap<u32, u32>,
    slice_meta: &'a BTreeMap<u32, u32>,
}

fn restore_and_remap_function(
    fn_meta: &FunctionManifestEntry,
    verified_fn: &RawFunctionDef,
    stripped_body_lines: &[String],
    tables: &RemapTables<'_>,
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

    let (_parsed_name, opt_prefix_mods_and_ret, opt_params_inside, _opt_post_params) =
        split_function_signature_parts(without_brace)?;

    let restored_link_vis = normalize_restored_linkage_vis(&fn_meta.original_linkage_vis);
    let link_prefix = if restored_link_vis.is_empty() {
        String::new()
    } else {
        format!("{restored_link_vis} ")
    };

    // F-19: Restore original `input.ll` calling convention + return attributes/type, NEVER copying
    // `-O2`-inferred return attributes (`noundef`, `nonnull`, `noalias`, `range(...)`) from `opt_fast.ll`!
    let orig_cconv_and_ret = if !fn_meta.original_cconv_and_ret.is_empty() {
        fn_meta.original_cconv_and_ret.clone()
    } else {
        extract_cconv_and_ret_from_declare(&fn_meta.prototype_declare)
            .unwrap_or_else(|| split_leading_linkage_vis(&opt_prefix_mods_and_ret).1)
    };

    // F-19: Pair original `input.ll` parameter types + parameter attributes with the SSA `%name`s
    // of `verified_fn`, stripping any `-O2`-inferred parameter attributes (`nocapture`, `readonly`,
    // `noalias`, `nonnull`, `noundef`, `dereferenceable(...)`, etc.)!
    let restored_params = restore_original_param_attrs_with_ssa_names(
        &fn_meta.name,
        &fn_meta.original_param_types_and_attrs,
        &opt_params_inside,
    )?;

    // F-19 & F-54: Restore ALL original `input.ll` post-parameter header clauses, inline function
    // attributes, and `#N` group refs in canonical LLVM `AsmWriter::printFunction` order
    // (never splicing `-O2`-inferred `willreturn`, `mustprogress`, `memory(...)`, `local_unnamed_addr`).
    let mut post_parts: Vec<String> = Vec::new();
    if let Some(ua) = &fn_meta.unnamed_addr {
        post_parts.push(ua.clone());
    }
    if let Some(as_clause) = &fn_meta.addrspace {
        post_parts.push(as_clause.clone());
    }
    if let Some(sec) = &fn_meta.section {
        post_parts.push(sec.clone());
    }
    if let Some(part) = &fn_meta.partition {
        post_parts.push(part.clone());
    }
    if let Some(cd) = &fn_meta.comdat {
        post_parts.push(cd.clone());
    }
    if let Some(al) = &fn_meta.align {
        post_parts.push(al.clone());
    }
    if let Some(gc) = &fn_meta.gc {
        post_parts.push(gc.clone());
    }
    if let Some(pref) = &fn_meta.prefix {
        post_parts.push(pref.clone());
    }
    if let Some(prol) = &fn_meta.prologue {
        post_parts.push(prol.clone());
    }
    if !fn_meta.original_fn_attrs_and_groups.is_empty() {
        for item in &fn_meta.original_fn_attrs_and_groups {
            if let Some(orig_grp) = item.strip_prefix('#').and_then(|d| d.parse::<u32>().ok()) {
                let mapped_grp = tables
                    .manifest_attr
                    .get(&orig_grp)
                    .copied()
                    .unwrap_or(orig_grp);
                post_parts.push(format!("#{mapped_grp}"));
            } else {
                post_parts.push(item.clone());
            }
        }
    } else if let Some(orig_grp) = fn_meta.original_attr_group {
        let mapped_grp = tables
            .manifest_attr
            .get(&orig_grp)
            .copied()
            .unwrap_or(orig_grp);
        post_parts.push(format!("#{mapped_grp}"));
    }
    if let Some(pers) = &fn_meta.original_personality {
        post_parts.push(pers.clone());
    }
    for meta_attach in &fn_meta.original_header_metadata {
        post_parts.push(remap_attrs_and_metadata(
            meta_attach,
            tables.manifest_attr,
            tables.identity_meta,
        ));
    }

    let post_str = if post_parts.is_empty() {
        String::new()
    } else {
        format!(" {}", post_parts.join(" "))
    };

    let rebuilt_header = format!(
        "define {link_prefix}{orig_cconv_and_ret} @{}({restored_params}){post_str} {{",
        fn_meta.name
    );

    let mut remapped_lines = Vec::with_capacity(stripped_body_lines.len() + 1);
    remapped_lines.push(rebuilt_header);
    for body_line in stripped_body_lines {
        remapped_lines.push(remap_attrs_and_metadata(
            body_line,
            tables.slice_attr,
            tables.slice_meta,
        ));
    }
    Ok(remapped_lines.join("\n"))
}

fn extract_cconv_and_ret_from_declare(decl: &str) -> Option<String> {
    let rest = decl.trim().strip_prefix("declare ")?.trim_start();
    let (_, prefix, _, _) = split_function_signature_parts(rest).ok()?;
    Some(split_leading_linkage_vis(&prefix).1)
}

fn restore_original_param_attrs_with_ssa_names(
    fn_name: &str,
    orig_types_and_attrs: &[String],
    opt_params_inside: &str,
) -> Result<String, BridgeError> {
    let opt_parts: Vec<&str> = if opt_params_inside.trim().is_empty() {
        Vec::new()
    } else {
        split_top_level_commas(opt_params_inside)
    };

    if orig_types_and_attrs.is_empty() && opt_parts.is_empty() {
        return Ok(String::new());
    }
    if orig_types_and_attrs.is_empty() {
        // Legacy manifest deserialization fallback when `original_param_types_and_attrs` was omitted.
        return Ok(opt_params_inside.to_owned());
    }
    if orig_types_and_attrs.len() != opt_parts.len() {
        return Err(BridgeError::MalformedModule {
            detail: format!(
                "parameter count mismatch when merging `@{fn_name}`: manifest has {}, slice has {}",
                orig_types_and_attrs.len(),
                opt_parts.len()
            ),
        });
    }

    let mut rebuilt = Vec::with_capacity(orig_types_and_attrs.len());
    for (orig_ty_attrs, opt_raw) in orig_types_and_attrs.iter().zip(opt_parts.iter()) {
        let (_, opt_ssa_name) = split_single_param_type_attrs_and_name(opt_raw);
        match opt_ssa_name {
            Some(ssa) => rebuilt.push(format!("{orig_ty_attrs} {ssa}")),
            None => rebuilt.push(orig_ty_attrs.clone()),
        }
    }
    Ok(rebuilt.join(", "))
}

fn parse_param_types_and_attrs(params: &str) -> Vec<String> {
    if params.trim().is_empty() {
        return Vec::new();
    }
    split_top_level_commas(params)
        .into_iter()
        .map(|part| split_single_param_type_attrs_and_name(part).0)
        .collect()
}

fn split_single_param_type_attrs_and_name(param: &str) -> (String, Option<String>) {
    let p = param.trim();
    if p.is_empty() || p == "..." {
        return (p.to_owned(), None);
    }
    let Some((ty, after_ty)) = parse_balanced_llvm_type(p) else {
        return (p.to_owned(), None);
    };
    let after_trim = after_ty.trim();
    if after_trim.is_empty() {
        return (ty.to_owned(), None);
    }

    // In LLVM IR parameter syntax `<ty> [param_attrs]* [%ssa_name]`, every attribute taking a
    // `%type` wraps it in parentheses (`byval(%T)`, `sret(%T)`), so a trailing `%ident` or
    // `%"quoted"` token outside parentheses after `<ty>` is unambiguously the SSA parameter name.
    let (mid_attrs, last_tok) = split_last_top_level_token(after_trim);

    let is_ssa_name =
        if last_tok.starts_with("%\"") && last_tok.ends_with('"') && last_tok.len() >= 3 {
            true
        } else {
            last_tok.starts_with('%') && !last_tok.contains('(') && !last_tok.contains(')')
        };
    if is_ssa_name {
        let ty_and_attrs = if mid_attrs.is_empty() {
            ty.to_owned()
        } else {
            format!("{ty} {mid_attrs}")
        };
        (ty_and_attrs, Some(last_tok.to_owned()))
    } else {
        (format!("{ty} {after_trim}"), None)
    }
}

fn split_last_top_level_token(s: &str) -> (&str, &str) {
    let bytes = s.as_bytes();
    let mut in_quotes = false;
    let mut paren_depth = 0_i32;
    let mut last_ws_end: Option<(usize, usize)> = None;
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if in_quotes {
            if b == b'"' {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        match b {
            b'"' => {
                in_quotes = true;
                i += 1;
            }
            b'(' => {
                paren_depth += 1;
                i += 1;
            }
            b')' => {
                paren_depth = (paren_depth - 1).max(0);
                i += 1;
            }
            _ if b.is_ascii_whitespace() && paren_depth == 0 => {
                let ws_start = i;
                while bytes.get(i).is_some_and(u8::is_ascii_whitespace) {
                    i += 1;
                }
                if i < bytes.len() {
                    last_ws_end = Some((ws_start, i));
                }
            }
            _ => {
                i += 1;
            }
        }
    }
    match last_ws_end {
        Some((ws_start, tok_start)) => (
            s.get(..ws_start).unwrap_or("").trim_end(),
            s.get(tok_start..).unwrap_or("").trim(),
        ),
        None => ("", s),
    }
}

/// Strips unverified `-O2` optimization/alias metadata attachments (`, !tbaa !N`, `, !alias.scope !N`,
/// `, !noalias !N`, `, !invariant.load !{}`, etc.) from instruction lines outside quotes & comments (`F-19`).
fn strip_unverified_opt_metadata(line: &str) -> String {
    let code_part = strip_line_comment_preserving_strings(line);
    let comment_suffix = line.get(code_part.len()..).unwrap_or("");

    let mut current = code_part.to_owned();
    loop {
        let mut changed = false;
        for kind in UNVERIFIED_OPT_METADATA_KINDS {
            let pattern = format!(", {kind}");
            let mut search_from = 0_usize;
            while let Some(sub) = current.get(search_from..) {
                let Some(rel_idx) = find_outside_quotes(sub, &pattern) else {
                    break;
                };
                let idx = search_from + rel_idx;
                let after_kind_pos = idx + pattern.len();
                let after_kind = current.get(after_kind_pos..).unwrap_or("");
                if !after_kind.starts_with(char::is_whitespace) {
                    search_from = after_kind_pos;
                    continue;
                }
                let after_ws = after_kind.trim_start();
                let ws_len = after_kind.len().saturating_sub(after_ws.len());
                if !after_ws.starts_with('!') {
                    search_from = after_kind_pos;
                    continue;
                }

                // Target value is either `!{...}` or `!<ident>`.
                let val_len = if let Some(from_brace) = after_ws.strip_prefix('!')
                    && from_brace.starts_with('{')
                {
                    let Some(close_brace) = find_matching_delim(from_brace, b'{', b'}') else {
                        search_from = after_kind_pos;
                        continue;
                    };
                    1 + close_brace + 1
                } else {
                    let ident_chars = after_ws
                        .get(1..)
                        .unwrap_or("")
                        .bytes()
                        .take_while(|b| {
                            b.is_ascii_alphanumeric() || matches!(*b, b'_' | b'.' | b'$' | b'-')
                        })
                        .count();
                    if ident_chars == 0 {
                        search_from = after_kind_pos;
                        continue;
                    }
                    1 + ident_chars
                };

                let end_span = after_kind_pos + ws_len + val_len;
                let prefix = current.get(..idx).unwrap_or("");
                let suffix = current.get(end_span..).unwrap_or("");
                current = format!("{prefix}{suffix}");
                changed = true;
                break;
            }
            if changed {
                break;
            }
        }
        if !changed {
            break;
        }
    }

    if comment_suffix.is_empty() {
        current
    } else {
        format!("{current}{comment_suffix}")
    }
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
    parse_param_types_and_attrs(params).join(", ")
}

pub(crate) fn split_top_level_commas(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let mut parts = Vec::new();
    let mut start = 0_usize;
    let mut depth = 0_i32;
    let mut in_quotes = false;
    let mut i = 0_usize;

    while let Some(&b) = bytes.get(i) {
        if in_quotes {
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

pub(crate) fn parse_balanced_llvm_type(s: &str) -> Option<(&str, &str)> {
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

pub(crate) fn find_matching_delim(s: &str, open: u8, close: u8) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut depth = 0_i32;
    let mut in_quotes = false;
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if in_quotes {
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
        let mut i = 0_usize;
        let mut in_quotes = false;
        while let Some(&b) = bytes.get(i) {
            if in_quotes {
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

fn extract_thread_local_clause(rhs: &str) -> String {
    let first_part = split_at_top_level_comma(rhs).0;
    if let Some(pos) = find_keyword_outside_quotes(first_part, "thread_local(") {
        let from_tl = first_part.get(pos..).unwrap_or("");
        if let Some(from_paren) = from_tl.get("thread_local".len()..)
            && let Some(close) = find_matching_delim(from_paren, b'(', b')')
            && let Some(clause) = from_tl.get(.."thread_local".len() + close + 1)
        {
            return format!(" {clause}");
        }
    }
    if contains_bare_keyword(first_part, "thread_local") {
        return " thread_local".to_owned();
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
    let scrubbed = mask_quoted_strings(haystack);
    scrubbed
        .split(|c: char| c.is_ascii_whitespace() || c == ',')
        .any(|t| t == kw)
}

#[derive(Default)]
struct ParsedPostParams {
    unnamed_addr: Option<String>,
    addrspace: Option<String>,
    fn_attrs_and_groups: Vec<String>,
    section: Option<String>,
    partition: Option<String>,
    comdat: Option<String>,
    align: Option<String>,
    gc: Option<String>,
    prefix: Option<String>,
    prologue: Option<String>,
    personality: Option<String>,
    metadata: Vec<String>,
}

fn format_declare_post_params(post: &ParsedPostParams) -> String {
    let mut parts: Vec<String> = Vec::new();
    if let Some(as_clause) = &post.addrspace {
        parts.push(as_clause.clone());
    }
    parts.extend(post.fn_attrs_and_groups.iter().cloned());
    if let Some(gc) = &post.gc {
        parts.push(gc.clone());
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" {}", parts.join(" "))
    }
}

fn consume_quoted_span(s: &str) -> usize {
    let bytes = s.as_bytes();
    if bytes.first() != Some(&b'"') {
        return 0;
    }
    let mut i = 1_usize;
    while let Some(&b) = bytes.get(i) {
        i += 1;
        if b == b'"' {
            break;
        }
    }
    i
}

fn consume_llvm_typed_value(s: &str) -> Option<(String, &str)> {
    let (ty, after_ty) = parse_balanced_llvm_type(s)?;
    let val_s = after_ty.trim_start();
    let first = *val_s.as_bytes().first()?;

    if let Some((open, close)) = match first {
        b'{' => Some((b'{', b'}')),
        b'[' => Some((b'[', b']')),
        b'(' => Some((b'(', b')')),
        b'<' => Some((b'<', b'>')),
        _ => None,
    } {
        let end = find_matching_delim(val_s, open, close)?;
        let val = val_s.get(..=end)?;
        return Some((format!("{ty} {val}"), val_s.get(end + 1..).unwrap_or("")));
    }

    if matches!(first, b'@' | b'%' | b'c') && val_s.as_bytes().get(1) == Some(&b'"') {
        let qlen = consume_quoted_span(val_s.get(1..)?);
        let total = 1 + qlen;
        let val = val_s.get(..total)?;
        return Some((format!("{ty} {val}"), val_s.get(total..).unwrap_or("")));
    }
    if first == b'"' {
        let qlen = consume_quoted_span(val_s);
        let val = val_s.get(..qlen)?;
        return Some((format!("{ty} {val}"), val_s.get(qlen..).unwrap_or("")));
    }

    let tok_len = val_s
        .bytes()
        .take_while(|b| !b.is_ascii_whitespace() && !matches!(*b, b',' | b'(' | b')'))
        .count();
    if tok_len == 0 {
        return None;
    }
    let tok = val_s.get(..tok_len)?;
    let mut probe = val_s.get(tok_len..).unwrap_or("").trim_start();
    loop {
        if let Some(after_inrange) = probe.strip_prefix("inrange") {
            let trimmed_ir = after_inrange.trim_start();
            if trimmed_ir.starts_with('(')
                && let Some(close) = find_matching_delim(trimmed_ir, b'(', b')')
            {
                probe = trimmed_ir.get(close + 1..).unwrap_or("").trim_start();
                continue;
            }
        }
        let mod_len = probe
            .bytes()
            .take_while(|b| b.is_ascii_alphabetic() || *b == b'_')
            .count();
        let mod_kw = probe.get(..mod_len).unwrap_or("");
        if matches!(
            mod_kw,
            "inbounds" | "nusw" | "nuw" | "nsw" | "exact" | "samesign" | "nneg" | "disjoint"
        ) && probe
            .as_bytes()
            .get(mod_len)
            .is_some_and(|b| b.is_ascii_whitespace() || *b == b'(')
        {
            probe = probe.get(mod_len..).unwrap_or("").trim_start();
            continue;
        }
        break;
    }
    if probe.starts_with('(')
        && let Some(close) = find_matching_delim(probe, b'(', b')')
    {
        let consumed = val_s.len().saturating_sub(probe.len()) + close + 1;
        let val = val_s.get(..consumed)?;
        return Some((format!("{ty} {val}"), val_s.get(consumed..).unwrap_or("")));
    }
    Some((format!("{ty} {tok}"), val_s.get(tok_len..).unwrap_or("")))
}

fn parse_post_param_header(post: &str) -> ParsedPostParams {
    let mut out = ParsedPostParams::default();
    let mut cur = post;
    while !cur.is_empty() {
        cur = cur.trim_start_matches(|c: char| c.is_ascii_whitespace() || c == ',');
        let Some(&first) = cur.as_bytes().first() else {
            break;
        };

        if first == b'!' {
            let key_len = cur
                .bytes()
                .take_while(|b| !b.is_ascii_whitespace() && *b != b',')
                .count();
            let key = cur.get(..key_len).unwrap_or("");
            let after_key = cur.get(key_len..).unwrap_or("").trim_start();
            if let Some(from_brace) = after_key.strip_prefix('!')
                && from_brace.starts_with('{')
                && let Some(close) = find_matching_delim(from_brace, b'{', b'}')
                && let Some(val) = after_key.get(..1 + close + 1)
            {
                out.metadata.push(format!("{key} {val}"));
                cur = after_key.get(1 + close + 1..).unwrap_or("");
                continue;
            }
            if after_key.starts_with('!') {
                let val_len = after_key
                    .bytes()
                    .take_while(|b| !b.is_ascii_whitespace() && *b != b',')
                    .count();
                if let Some(val) = after_key.get(..val_len) {
                    out.metadata.push(format!("{key} {val}"));
                    cur = after_key.get(val_len..).unwrap_or("");
                    continue;
                }
            }
            cur = cur.get(key_len.max(1)..).unwrap_or("");
            continue;
        }

        if first == b'"' {
            let q1 = consume_quoted_span(cur);
            let mut total = q1;
            if let Some(after_q1) = cur.get(q1..)
                && let Some(after_eq) = after_q1.strip_prefix('=')
                && after_eq.starts_with('"')
            {
                total = q1 + 1 + consume_quoted_span(after_eq);
            }
            if let Some(attr_str) = cur.get(..total) {
                out.fn_attrs_and_groups.push(attr_str.to_owned());
            }
            cur = cur.get(total.max(1)..).unwrap_or("");
            continue;
        }

        if first == b'#' {
            let grp_len = cur
                .bytes()
                .take_while(|b| !b.is_ascii_whitespace() && *b != b',')
                .count();
            if let Some(grp) = cur.get(..grp_len) {
                out.fn_attrs_and_groups.push(grp.to_owned());
            }
            cur = cur.get(grp_len.max(1)..).unwrap_or("");
            continue;
        }

        if first == b'(' {
            let skip = find_matching_delim(cur, b'(', b')').map_or(1, |c| c + 1);
            cur = cur.get(skip..).unwrap_or("");
            continue;
        }

        let word_len = cur
            .bytes()
            .take_while(|b| {
                !b.is_ascii_whitespace() && !matches!(*b, b',' | b'(' | b')' | b'"' | b'!' | b'#')
            })
            .count();
        if word_len == 0 {
            let adv = cur.chars().next().map_or(1, char::len_utf8);
            cur = cur.get(adv..).unwrap_or("");
            continue;
        }
        let word = cur.get(..word_len).unwrap_or("");
        let after_word = cur.get(word_len..).unwrap_or("");

        if after_word.starts_with('(')
            && let Some(close) = find_matching_delim(after_word, b'(', b')')
            && let Some(full_tok) = cur.get(..word_len + close + 1)
        {
            cur = cur.get(word_len + close + 1..).unwrap_or("");
            match word {
                "addrspace" => out.addrspace = Some(full_tok.to_owned()),
                "comdat" => out.comdat = Some(full_tok.to_owned()),
                _ => out.fn_attrs_and_groups.push(full_tok.to_owned()),
            }
            continue;
        }

        cur = after_word;
        match word {
            "unnamed_addr" | "local_unnamed_addr" => {
                out.unnamed_addr = Some(word.to_owned());
            }
            "addrspace" => {
                let rest = cur.trim_start();
                if rest.starts_with('(')
                    && let Some(close) = find_matching_delim(rest, b'(', b')')
                    && let Some(parens) = rest.get(..=close)
                {
                    out.addrspace = Some(format!("addrspace{parens}"));
                    cur = rest.get(close + 1..).unwrap_or("");
                }
            }
            "comdat" => {
                let rest = cur.trim_start();
                if rest.starts_with('(')
                    && let Some(close) = find_matching_delim(rest, b'(', b')')
                    && let Some(parens) = rest.get(..=close)
                {
                    out.comdat = Some(format!("comdat{parens}"));
                    cur = rest.get(close + 1..).unwrap_or("");
                } else {
                    out.comdat = Some("comdat".to_owned());
                }
            }
            "section" | "partition" | "gc" => {
                let rest = cur.trim_start();
                if rest.starts_with('"') {
                    let qlen = consume_quoted_span(rest);
                    if let Some(qstr) = rest.get(..qlen) {
                        let clause = format!("{word} {qstr}");
                        match word {
                            "section" => out.section = Some(clause),
                            "partition" => out.partition = Some(clause),
                            _ => out.gc = Some(clause),
                        }
                        cur = rest.get(qlen..).unwrap_or("");
                    }
                }
            }
            "align" => {
                let rest = cur.trim_start();
                let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
                if !digits.is_empty() {
                    out.align = Some(format!("align {digits}"));
                    cur = rest.get(digits.len()..).unwrap_or("");
                }
            }
            "prefix" | "prologue" | "personality" => {
                if let Some((typed_val, rest)) = consume_llvm_typed_value(cur) {
                    let clause = format!("{word} {typed_val}");
                    match word {
                        "prefix" => out.prefix = Some(clause),
                        "prologue" => out.prologue = Some(clause),
                        _ => out.personality = Some(clause),
                    }
                    cur = rest;
                }
            }
            _ => {
                out.fn_attrs_and_groups.push(word.to_owned());
            }
        }
    }
    out
}
