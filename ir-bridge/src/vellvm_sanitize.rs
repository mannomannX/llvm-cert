use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::error::BridgeError;
use crate::fp_literals::normalize_llvm23_fp_and_comments;
use crate::split_merge::{
    find_matching_delim, is_const_expr_alias_line, is_elided_module_intrinsic_global,
    parse_balanced_llvm_type, split_top_level_commas, validate_target_datalayout,
};

/// Role of an LLVM IR slice entering Vellvm (`cert-validator` or `verified-opt-fallback`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SliceRole {
    /// Unoptimized source IR (`<fn>.input.ll`): dropping source refinements is conservative/sound.
    Source,
    /// `-O2` target IR (`<fn>.opt_fast.ll`): any unmodeled UB/poison construct MUST trigger fallback.
    TargetFastPath,
}

/// Result of checking whether an `-O2` target slice can be soundly validated by Vellvm 3.0.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FastPathEligibility {
    Eligible,
    FallbackRequired { reasons: Vec<String> },
}

impl FastPathEligibility {
    #[must_use]
    pub fn is_eligible(&self) -> bool {
        matches!(self, Self::Eligible)
    }
}

const FAST_MATH_FLAGS: &[&str] = &[
    "nnan", "ninf", "nsz", "arcp", "contract", "afn", "reassoc", "fast",
];

/// Every LLVM 23 instruction/value operator that permits fast-math flags (`F-17`).
const FAST_MATH_OPCODES: &[&str] = &[
    "fadd", "fsub", "fmul", "fdiv", "frem", "fneg", "fcmp", "select", "phi", "fptrunc", "fpext",
    "call",
];

const MEMORY_PASSING_PARAM_ATTRS: &[&str] =
    &["byval", "inalloca", "preallocated", "byref", "initializes"];

const UNWINDING_OPCODES: &[&str] = &[
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

const UNSUPPORTED_CCONVS: &[&str] = &[
    "aarch64_vector_pcs",
    "aarch64_sve_vector_pcs",
    "aarch64_sme_preservemost_from_x0",
    "aarch64_sme_preservemost_from_x1",
    "aarch64_sme_preservemost_from_x2",
    "riscv_vector_cc",
    "riscv_vls_cc",
    "tailcc",
    "preserve_nonecc",
];

/// Returns `true` iff `sym` (with or without leading `@`) is in Vellvm 3.0's formally verified
/// intrinsic catalog (`IntrinsicsDefinitions.v` + `Implementations/Memory.v`, `F-30`).
///
/// Explicitly excludes unmodeled/soundness-hazardous intrinsics (`llvm.assume`, `llvm.va_*`,
/// `llvm.vellvm.internal.throw`, `llvm.lifetime.*`, `llvm.stacksave*`, `llvm.stackrestore*`,
/// `llvm.launder.invariant.group*`, `llvm.experimental.*`, `llvm.expect.with.probability.*`,
/// `llvm.threadlocal.address*`). Note that `memcpy`/`memmove`/`memset` additionally require a
/// constant `i1 false` volatile flag (`F-18`).
#[must_use]
pub fn is_verified_vellvm_intrinsic(sym: &str) -> bool {
    let clean = sym.strip_prefix('@').unwrap_or(sym);
    let Some(rest) = clean.strip_prefix("llvm.") else {
        return false;
    };

    // 1. Pure scalar IEEE-754 f32/f64 intrinsics (`IntrinsicsDefinitions.v:91-154`):
    if let Some((op, fp_ty)) = rest.rsplit_once('.')
        && matches!(fp_ty, "f32" | "f64")
        && matches!(
            op,
            "fabs" | "maxnum" | "minimum" | "minnum" | "maximum" | "copysign" | "fma" | "fmuladd"
        )
    {
        return true;
    }

    // 2. Width-indexed `ushl.sat` and `expect` (`{i1,i8,i16,i32,i64}`):
    if let Some((op, int_ty)) = rest.rsplit_once('.')
        && matches!(int_ty, "i1" | "i8" | "i16" | "i32" | "i64")
        && matches!(op, "ushl.sat" | "expect")
    {
        return true;
    }

    // 3. Byte-swap intrinsics (`{i16,i32,i64}`):
    if matches!(rest, "bswap.i16" | "bswap.i32" | "bswap.i64") {
        return true;
    }

    // 4. Standard pure integer intrinsics (`{i8,i16,i32,i64}`):
    if let Some((op, int_ty)) = rest.rsplit_once('.')
        && matches!(int_ty, "i8" | "i16" | "i32" | "i64")
        && matches!(
            op,
            "smin"
                | "smax"
                | "umin"
                | "umax"
                | "abs"
                | "uadd.sat"
                | "usub.sat"
                | "sadd.sat"
                | "ssub.sat"
                | "uadd.with.overflow"
                | "usub.with.overflow"
                | "umul.with.overflow"
                | "sadd.with.overflow"
                | "ssub.with.overflow"
                | "smul.with.overflow"
                | "ctpop"
                | "ctlz"
                | "cttz"
                | "fshl"
                | "fshr"
        )
    {
        return true;
    }

    // 5. Non-volatile address-space-0 memory intrinsics (`IntrinsicsDefinitions.v:231-260`):
    matches!(
        rest,
        "memcpy.p0.p0.i32"
            | "memcpy.p0.p0.i64"
            | "memcpy.p0i8.p0i8.i32"
            | "memcpy.p0i8.p0i8.i64"
            | "memmove.p0.p0.i32"
            | "memmove.p0.p0.i64"
            | "memmove.p0i8.p0i8.i32"
            | "memmove.p0i8.p0i8.i64"
            | "memset.p0.i32"
            | "memset.p0.i64"
            | "memset.p0i8.i32"
            | "memset.p0i8.i64"
    )
}

/// Audits an `-O2` target IR slice against Vellvm 3.0's ground-truth parser & operational semantics
/// (`F-08`, `F-15`, `F-17`, `F-18`, `F-22`, `F-30`, `F-31`, `F-32`, `F-33`, `F-34`, `F-35`,
/// `F-36`, `F-38`). Any construct whose naive stripping or unmodeled evaluation could mask target
/// poison/UB causes deterministic routing to `verified-opt-fallback`.
#[must_use]
pub fn check_fast_path_eligibility(ir: &str) -> FastPathEligibility {
    match normalize_llvm23_fp_and_comments(ir) {
        Ok(normalized) => check_fast_path_eligibility_normalized(&normalized),
        Err(err) => {
            let mut reasons = vec![err.to_string()];
            if let FastPathEligibility::FallbackRequired { reasons: mut extra } =
                check_fast_path_eligibility_normalized(ir)
            {
                reasons.append(&mut extra);
            }
            reasons.sort();
            reasons.dedup();
            FastPathEligibility::FallbackRequired { reasons }
        }
    }
}

fn check_fast_path_eligibility_normalized(ir: &str) -> FastPathEligibility {
    let mut reasons: Vec<String> = Vec::new();
    let mut type_aliases: BTreeMap<String, String> = BTreeMap::new();
    let mut code_lines: Vec<&str> = Vec::new();

    for raw_line in ir.lines() {
        let code = strip_line_comment_preserving_strings(raw_line).trim();
        if code.is_empty()
            || code.starts_with('!')
            || code.starts_with("#dbg_")
            || code.starts_with("source_filename")
        {
            continue;
        }
        if code.starts_with("target datalayout") {
            if let Err(err) = validate_target_datalayout(code) {
                reasons.push(err.to_string());
            }
            continue;
        }
        if code.starts_with("target ") {
            continue;
        }
        if let Some((alias_ident, alias_rhs)) = parse_type_alias_def(code) {
            type_aliases.insert(alias_ident, alias_rhs);
        }
        code_lines.push(code);
    }

    for code in code_lines {
        let scrubbed = mask_quoted_strings(code);
        let tokens: Vec<&str> = scrubbed
            .split(|c: char| c.is_ascii_whitespace() || matches!(c, ',' | '(' | ')'))
            .filter(|t| !t.is_empty())
            .collect();

        check_line_soundness_hazards(code, &scrubbed, &tokens, &type_aliases, &mut reasons);
    }

    reasons.sort();
    reasons.dedup();
    if reasons.is_empty() {
        FastPathEligibility::Eligible
    } else {
        FastPathEligibility::FallbackRequired { reasons }
    }
}

fn check_line_soundness_hazards(
    raw_code: &str,
    scrubbed: &str,
    tokens: &[&str],
    type_aliases: &BTreeMap<String, String>,
    reasons: &mut Vec<String>,
) {
    let trimmed = scrubbed.trim_start();
    let is_decl_line = trimmed.starts_with("declare ");
    let is_type_line = parse_type_alias_def(raw_code).is_some();
    let is_attr_group_line = trimmed.starts_with("attributes #");
    let is_exec_or_global_line = !is_decl_line && !is_type_line && !is_attr_group_line;

    // F-52: Detect quoted `@"..."` / `%"..."` identifiers on raw unmasked code so LLVM `\XX`
    // hex-escaped symbols and quoted `@"..."` vs bare `@...` symbol-identity desyncs never reach
    // Vellvm Fast-Path validation.
    if has_quoted_llvm_identifier(raw_code) {
        reasons.push(
            "quoted `@\"...\"` / `%\"...\"` identifier requires Safe-Path fallback to prevent LLVM/Vellvm symbol desync (F-52)"
                .to_owned(),
        );
    }

    // F-53: Reject invalid `i0` / `b0` or bitwidths `> 8388608` (`1 << 23`).
    if let Some(bad_bw) = find_invalid_int_bitwidth_token(scrubbed) {
        reasons.push(format!(
            "invalid LLVM integer/byte bitwidth `{bad_bw}` (must be 1..=8388608) (F-53)"
        ));
    }

    for (idx, &tok) in tokens.iter().enumerate() {
        // F-17: Gate all 8 fast-math flags across every LLVM 23 instruction/value operator that
        // permits them (`fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fneg`, `fcmp`, `select`, `phi`,
        // `fptrunc`, `fpext`, `call`).
        if is_exec_or_global_line && FAST_MATH_OPCODES.contains(&tok) {
            let mut off = 1_usize;
            while let Some(&cand) = tokens.get(idx + off) {
                if FAST_MATH_FLAGS.contains(&cand) {
                    reasons.push(format!(
                        "fast-math flag `{cand}` on `{tok}` requires Safe-Path fallback (F-17)"
                    ));
                    off += 1;
                } else {
                    break;
                }
            }
        }

        // F-18: Gate volatile loads/stores, atomic operations, and fences.
        if is_exec_or_global_line
            && matches!(
                tok,
                "volatile" | "atomic" | "cmpxchg" | "atomicrmw" | "fence"
            )
        {
            reasons.push(format!(
                "volatile/atomic memory construct `{tok}` requires Safe-Path fallback (F-18)"
            ));
        }

        // F-31: Gate variadic function prototypes/calls (`...`) and `va_arg` instructions.
        if !is_type_line && tok == "..." {
            reasons.push(
                "variadic prototype/call `...` requires Safe-Path fallback (F-31)".to_owned(),
            );
        }
        if is_exec_or_global_line && tok == "va_arg" {
            reasons.push("`va_arg` instruction requires Safe-Path fallback (F-31)".to_owned());
        }

        // F-32: Gate unmodeled memory-passing parameter attributes (`byval`, `inalloca`,
        // `preallocated`, `byref`, `initializes`).
        if !is_type_line && MEMORY_PASSING_PARAM_ATTRS.contains(&tok) {
            reasons.push(format!(
                "unmodeled memory-passing parameter attribute `{tok}` requires Safe-Path fallback (F-32)"
            ));
        }

        // F-33: Gate `extern_weak` symbols (may resolve to null at link time vs Vellvm non-null alloc).
        if !is_type_line && tok == "extern_weak" {
            reasons.push(
                "`extern_weak` linkage may resolve to null at link time and requires Safe-Path fallback (F-33)"
                    .to_owned(),
            );
        }

        // F-34: Gate unwinding and exception instructions (`invoke`, `landingpad`, `resume`, SEH pads, `callbr`).
        if is_exec_or_global_line
            && (UNWINDING_OPCODES.contains(&tok)
                || (trimmed.starts_with("define ") && tok == "personality"))
        {
            reasons.push(format!(
                "unwinding/exception construct `{tok}` requires Safe-Path fallback (F-34)"
            ));
        }

        // F-35: Gate `getelementptr` `inrange(...)` attributes.
        if is_exec_or_global_line && tok == "inrange" {
            reasons.push(
                "`getelementptr` `inrange` attribute requires Safe-Path fallback (F-35)".to_owned(),
            );
        }

        // F-38: Gate `frem` (`DynamicValues.v` raises `FailureE` on `FRem`).
        if is_exec_or_global_line && tok == "frem" {
            reasons.push(
                "`frem` floating-point remainder is unmodeled in Vellvm and requires Safe-Path fallback (F-38)"
                    .to_owned(),
            );
        }

        // Inline `asm` and unsupported target calling conventions.
        if tok == "asm" && !trimmed.starts_with("module asm") {
            reasons.push("inline `asm` call cannot be validated in Vellvm".to_owned());
        }
        if UNSUPPORTED_CCONVS.contains(&tok) {
            reasons.push(format!(
                "target calling convention `{tok}` unsupported in Vellvm"
            ));
        }

        // F-54: Gate unmodeled function/call attributes (`strictfp`, `naked`, `optnone`).
        if !is_type_line && !is_decl_line && matches!(tok, "strictfp" | "naked" | "optnone") {
            reasons.push(format!(
                "function attribute `{tok}` requires Safe-Path fallback (F-54)"
            ));
        }

        // F-08 & F-51: `half` / `bfloat` / `fp128` runtime values, target FP hex literals, and
        // `%TypeAlias` references expanding to unsupported FP scalar/aggregate/vector types.
        let bare_tok =
            tok.trim_matches(|c: char| matches!(c, '<' | '>' | '[' | ']' | '{' | '}' | '*'));
        let alias_has_unsupported_fp = bare_tok.starts_with('%')
            && type_aliases.contains_key(bare_tok)
            && expanded_type_has_unsupported_fp(&expand_llvm_type(bare_tok, type_aliases));
        if (matches!(
            bare_tok,
            "half" | "bfloat" | "fp128" | "x86_fp80" | "ppc_fp128"
        ) || is_non_f32_f64_fp_hex_literal(bare_tok)
            || alias_has_unsupported_fp)
            && !is_decl_line
            && !is_type_line
        {
            reasons.push(
                "half/bfloat/fp128 value operation requires Safe-Path (Vellvm models f32/f64 values only)"
                    .to_owned(),
            );
        }
    }

    // F-15 & F-51: Gate `icmp samesign` on scalar or vector `ptr`/`iptr` (including `%TypeAlias`).
    if is_exec_or_global_line && has_pointer_icmp_samesign(raw_code, type_aliases) {
        reasons.push(
            "pointer/iptr `icmp samesign` requires Safe-Path fallback under IP64Bit MMIO addresses (F-15)"
                .to_owned(),
        );
    }

    // F-51: Gate `<N x ptr>` parameters, returns, and call arguments carrying `nonnull`, `align`,
    // `dereferenceable`, or `dereferenceable_or_null` (`Semantics/Attributes.v:132-150, 323-329`).
    if !is_type_line && !is_attr_group_line && has_vector_ptr_lane_attrs(raw_code, type_aliases) {
        reasons.push(
            "vector-of-pointer `<N x ptr>` with `nonnull`/`align`/`dereferenceable` is unmodeled per-lane in Vellvm and requires Safe-Path fallback (F-51)"
                .to_owned(),
        );
    }

    // F-30, F-31, F-18 & F-52: Enforce verified `@llvm.*` allowlist, variadic intrinsics, and
    // `i1 false` volatile flag on `raw_code` (with `@"..."` / `\XX` unescaping prior to masking).
    if !is_type_line {
        check_llvm_intrinsics_on_line(raw_code, is_decl_line, is_exec_or_global_line, reasons);
    }

    // F-33: Gate GEP/bitcast/addrspacecast/inttoptr constant-expression global aliases.
    if trimmed.starts_with('@') && is_const_expr_alias_line(raw_code) {
        reasons.push(
            "constant-expression global `alias` requires Safe-Path fallback (F-33)".to_owned(),
        );
    }

    // F-35: Gate multi-pair or vector `range(...)` attributes.
    if !is_type_line {
        check_range_attributes(scrubbed, reasons);
    }

    // F-36 & F-51: Gate `sitofp` / `uitofp` from `> 32`-bit int to `float` and `> 64`-bit int to `double`.
    if is_exec_or_global_line {
        check_wide_int_to_fp_conversions(raw_code, type_aliases, reasons);
    }

    // F-55: Call / invoke operand bundles (`call void @foo() [ "align"(ptr %p, i64 8) ]`),
    // independent of space vs tab whitespace after `call` / `invoke`.
    if tokens.iter().any(|&t| matches!(t, "call" | "invoke"))
        && scrubbed.contains(") [")
        && scrubbed.contains("](").not_or_bundle(scrubbed)
    {
        reasons.push(
            "call/invoke operand bundle `[ ... ]` cannot be stripped soundly on target IR"
                .to_owned(),
        );
    }

    // Non-IEEE `denormal_fpenv(...)` mode changes floating-point flush-to-zero semantics.
    if let Some(pos) = scrubbed.find("denormal_fpenv(") {
        let after = scrubbed.get(pos + "denormal_fpenv(".len()..).unwrap_or("");
        if let Some(end) = after.find(')') {
            let mode = after.get(..end).unwrap_or("").trim();
            if mode != "ieee" && mode != "ieee|ieee" {
                reasons.push(format!(
                    "non-IEEE floating-point environment `denormal_fpenv({mode})`"
                ));
            }
        }
    }
}

fn is_va_intrinsic(sym: &str) -> bool {
    matches!(sym, "llvm.va_start" | "llvm.va_copy" | "llvm.va_end")
        || sym.starts_with("llvm.va_start.")
        || sym.starts_with("llvm.va_copy.")
        || sym.starts_with("llvm.va_end.")
}

fn is_memory_intrinsic(sym: &str) -> bool {
    sym.starts_with("llvm.memcpy.")
        || sym.starts_with("llvm.memmove.")
        || sym.starts_with("llvm.memset.")
}

fn check_llvm_intrinsics_on_line(
    raw_code: &str,
    is_decl_line: bool,
    is_exec_or_global_line: bool,
    reasons: &mut Vec<String>,
) {
    let trimmed = raw_code.trim_start();
    let lhs_global_def = if trimmed.starts_with('@') {
        find_outside_quotes(trimmed, "=")
            .and_then(|eq_idx| trimmed.get(..eq_idx))
            .and_then(|lhs| lhs.trim().strip_prefix('@'))
            .map(canonical_llvm_ident_key)
    } else {
        None
    };

    for (sym, end_pos) in scan_global_symbols_with_end(raw_code) {
        if !sym.starts_with("llvm.") {
            continue;
        }

        // Allow module-level `@llvm.global_ctors` / `@llvm.global_dtors` / `@llvm.used` /
        // `@llvm.compiler.used` array definitions on their own LHS.
        if lhs_global_def.as_deref() == Some(sym.as_str())
            && is_elided_module_intrinsic_global(&sym)
        {
            continue;
        }

        // F-31: Gate `@llvm.va_start*`, `@llvm.va_copy*`, `@llvm.va_end*` even on declarations.
        if is_va_intrinsic(&sym) {
            reasons.push(format!(
                "variadic intrinsic `@{sym}` requires Safe-Path fallback (F-31)"
            ));
            continue;
        }

        if is_decl_line || !is_exec_or_global_line {
            continue;
        }

        // F-30: Enforce explicit verified `@llvm.*` intrinsic allowlist.
        if !is_verified_vellvm_intrinsic(&sym) {
            reasons.push(format!(
                "unverified LLVM intrinsic `@{sym}` requires Safe-Path fallback (F-30)"
            ));
            continue;
        }

        let after_sym = raw_code.get(end_pos..).unwrap_or("").trim_start();
        if !after_sym.starts_with('(') {
            reasons.push(format!(
                "non-call value reference to intrinsic `@{sym}` requires Safe-Path fallback (F-30)"
            ));
            continue;
        }

        // F-18: Memory intrinsics MUST carry a constant `i1 false` 4th `isvolatile` argument.
        if is_memory_intrinsic(&sym) {
            let Some(close_paren) = find_matching_delim(after_sym, b'(', b')') else {
                reasons.push(format!(
                    "malformed argument list on memory intrinsic `@{sym}` (F-18)"
                ));
                continue;
            };
            let inside_args = after_sym.get(1..close_paren).unwrap_or("");
            let args = split_top_level_commas(inside_args);
            let non_volatile_ok = if args.len() == 4 {
                let vol_arg = args.get(3).copied().unwrap_or("");
                let vol_toks: Vec<&str> = vol_arg.split_whitespace().collect();
                vol_toks.first() == Some(&"i1") && vol_toks.last() == Some(&"false")
            } else {
                false
            };
            if !non_volatile_ok {
                reasons.push(format!(
                    "memory intrinsic `@{sym}` without constant `i1 false` volatile flag requires Safe-Path fallback (F-18)"
                ));
            }
        }
    }
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

pub(crate) fn unescape_llvm_quoted_ident(raw_inside_quotes: &str) -> String {
    let bytes = raw_inside_quotes.as_bytes();
    let mut out = String::with_capacity(raw_inside_quotes.len());
    let mut i = 0_usize;
    while i < bytes.len() {
        if bytes.get(i) == Some(&b'\\') {
            if let (Some(&h1), Some(&h2)) = (bytes.get(i + 1), bytes.get(i + 2))
                && let (Some(n1), Some(n2)) = (hex_nibble(h1), hex_nibble(h2))
            {
                out.push(char::from((n1 << 4) | n2));
                i += 3;
                continue;
            }
            if bytes.get(i + 1) == Some(&b'\\') {
                out.push('\\');
                i += 2;
                continue;
            }
        }
        if let Some(ch) = raw_inside_quotes.get(i..).and_then(|s| s.chars().next()) {
            out.push(ch);
            i += ch.len_utf8();
        } else {
            break;
        }
    }
    out
}

pub(crate) fn canonical_llvm_ident_key(ident_without_sigil: &str) -> String {
    let trimmed = ident_without_sigil.trim();
    if let Some(inner) = trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        unescape_llvm_quoted_ident(inner)
    } else {
        trimmed.to_owned()
    }
}

fn has_quoted_llvm_identifier(raw_code: &str) -> bool {
    let bytes = raw_code.as_bytes();
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if b == b'"' {
            i += 1;
            while let Some(&ch) = bytes.get(i) {
                i += 1;
                if ch == b'"' {
                    break;
                }
            }
            continue;
        }
        if matches!(b, b'@' | b'%') && bytes.get(i + 1) == Some(&b'"') {
            return true;
        }
        i += 1;
    }
    false
}

fn scan_global_symbols_with_end(raw_code: &str) -> Vec<(String, usize)> {
    let bytes = raw_code.as_bytes();
    let mut out = Vec::new();
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if b == b'"' {
            i += 1;
            while let Some(&ch) = bytes.get(i) {
                i += 1;
                if ch == b'"' {
                    break;
                }
            }
            continue;
        }
        if b == b'@' {
            let start = i + 1;
            if bytes.get(start) == Some(&b'"') {
                let mut end = start + 1;
                let mut closed = false;
                while let Some(&ch) = bytes.get(end) {
                    end += 1;
                    if ch == b'"' {
                        closed = true;
                        break;
                    }
                }
                let inner_end = if closed { end - 1 } else { end };
                if let Some(inner) = raw_code.get(start + 1..inner_end) {
                    out.push((unescape_llvm_quoted_ident(inner), end));
                }
                i = end;
            } else {
                let mut end = start;
                while let Some(&ch) = bytes.get(end) {
                    if ch.is_ascii_alphanumeric() || matches!(ch, b'_' | b'.' | b'$' | b'-') {
                        end += 1;
                    } else {
                        break;
                    }
                }
                if end > start
                    && let Some(sym) = raw_code.get(start..end)
                {
                    out.push((sym.to_owned(), end));
                }
                i = end;
            }
        } else {
            i += 1;
        }
    }
    out
}

fn parse_type_alias_def(raw_code: &str) -> Option<(String, String)> {
    let trimmed = raw_code.trim_start();
    if !trimmed.starts_with('%') {
        return None;
    }
    let eq_pos = find_outside_quotes(trimmed, "=")?;
    let lhs = trimmed.get(..eq_pos)?.trim();
    let rhs = trimmed.get(eq_pos + 1..)?.trim_start();
    let body = rhs.strip_prefix("type")?;
    if !body.is_empty()
        && !body.starts_with(char::is_whitespace)
        && !body.starts_with('{')
        && !body.starts_with('<')
        && !body.starts_with('[')
    {
        return None;
    }
    Some((lhs.to_owned(), body.trim().to_owned()))
}

fn expand_llvm_type(ty: &str, type_aliases: &BTreeMap<String, String>) -> String {
    let mut visited = BTreeSet::new();
    expand_llvm_type_rec(ty, type_aliases, &mut visited, 0)
}

fn expand_llvm_type_rec(
    ty: &str,
    type_aliases: &BTreeMap<String, String>,
    visited: &mut BTreeSet<String>,
    depth: u32,
) -> String {
    if depth >= 32 || type_aliases.is_empty() {
        return ty.to_owned();
    }
    let bytes = ty.as_bytes();
    let mut out = String::with_capacity(ty.len());
    let mut i = 0_usize;
    while i < bytes.len() {
        if bytes.get(i) == Some(&b'%') {
            let start = i;
            let mut end = i + 1;
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
            if end > start + 1
                && let Some(ident) = ty.get(start..end)
            {
                if let Some(target_rhs) = type_aliases.get(ident)
                    && visited.insert(ident.to_owned())
                {
                    let expanded =
                        expand_llvm_type_rec(target_rhs, type_aliases, visited, depth + 1);
                    visited.remove(ident);
                    out.push_str(&expanded);
                } else {
                    out.push_str(ident);
                }
                i = end;
                continue;
            }
        }
        if let Some(ch) = ty.get(i..).and_then(|s| s.chars().next()) {
            out.push(ch);
            i += ch.len_utf8();
        } else {
            break;
        }
    }
    out
}

fn expanded_type_has_unsupported_fp(expanded_ty: &str) -> bool {
    let masked = mask_quoted_strings(expanded_ty);
    masked
        .split(|c: char| {
            c.is_ascii_whitespace()
                || matches!(c, ',' | '(' | ')' | '[' | ']' | '{' | '}' | '<' | '>' | '*')
        })
        .any(|t| matches!(t, "half" | "bfloat" | "fp128" | "x86_fp80" | "ppc_fp128"))
}

fn is_scalar_or_vector_ptr_or_iptr(expanded_ty: &str) -> bool {
    let t = expanded_ty.trim();
    if t == "ptr" || t == "iptr" || t.starts_with("ptr ") || t.ends_with('*') {
        return true;
    }
    is_vector_of_pointer_or_iptr_type(t)
}

fn is_vector_of_pointer_or_iptr_type(expanded_ty: &str) -> bool {
    let Some(inner) = expanded_ty
        .trim()
        .strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
    else {
        return false;
    };
    let elem = inner.rsplit('x').next().unwrap_or("").trim();
    elem == "ptr" || elem == "iptr" || elem.starts_with("ptr ") || elem.ends_with('*')
}

fn is_vector_of_pointer_type(expanded_ty: &str) -> bool {
    let Some(inner) = expanded_ty
        .trim()
        .strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
    else {
        return false;
    };
    let elem = inner.rsplit('x').next().unwrap_or("").trim();
    elem == "ptr" || elem.starts_with("ptr ") || elem.ends_with('*')
}

fn has_pointer_icmp_samesign(raw_code: &str, type_aliases: &BTreeMap<String, String>) -> bool {
    let mut search_from = 0_usize;
    let bytes = raw_code.as_bytes();
    while let Some(sub) = raw_code.get(search_from..) {
        let Some(rel) = find_outside_quotes(sub, "icmp") else {
            break;
        };
        let abs = search_from + rel;
        let end = abs + "icmp".len();
        search_from = end;
        let prev_ok = abs == 0
            || bytes
                .get(abs - 1)
                .is_some_and(|b| b.is_ascii_whitespace() || matches!(*b, b'(' | b'=' | b','));
        let next_ok = bytes.get(end).is_some_and(u8::is_ascii_whitespace);
        if !prev_ok || !next_ok {
            continue;
        }
        let after_icmp = raw_code.get(end..).unwrap_or("").trim_start();
        let Some(after_ss) = after_icmp.strip_prefix("samesign") else {
            continue;
        };
        if !after_ss.starts_with(char::is_whitespace) {
            continue;
        }
        let after_ss_ws = after_ss.trim_start();
        let pred_end = after_ss_ws
            .find(|c: char| c.is_ascii_whitespace() || c == '(')
            .unwrap_or(after_ss_ws.len());
        let mut after_pred = after_ss_ws.get(pred_end..).unwrap_or("").trim_start();
        if let Some(inside_paren) = after_pred.strip_prefix('(') {
            after_pred = inside_paren.trim_start();
        }
        if let Some((op_ty, _)) = parse_balanced_llvm_type(after_pred) {
            let expanded = expand_llvm_type(op_ty, type_aliases);
            if is_scalar_or_vector_ptr_or_iptr(&expanded) {
                return true;
            }
        }
    }
    false
}

fn has_lane_ptr_attr_token(text: &str) -> bool {
    let masked = mask_quoted_strings(text);
    masked
        .split(|c: char| c.is_ascii_whitespace() || matches!(c, ',' | '(' | ')'))
        .any(|t| {
            matches!(
                t,
                "nonnull" | "align" | "dereferenceable" | "dereferenceable_or_null"
            )
        })
}

fn has_vector_ptr_lane_attrs(raw_code: &str, type_aliases: &BTreeMap<String, String>) -> bool {
    // 1. Check parameter and call-argument lists `(...)`.
    let bytes = raw_code.as_bytes();
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        if b == b'"' {
            i += 1;
            while let Some(&ch) = bytes.get(i) {
                i += 1;
                if ch == b'"' {
                    break;
                }
            }
            continue;
        }
        if b == b'('
            && let Some(from_open) = raw_code.get(i..)
            && let Some(close) = find_matching_delim(from_open, b'(', b')')
        {
            let inside = from_open.get(1..close).unwrap_or("");
            for seg in split_top_level_commas(inside) {
                if let Some((ty, rest)) = parse_balanced_llvm_type(seg)
                    && is_vector_of_pointer_type(&expand_llvm_type(ty, type_aliases))
                    && has_lane_ptr_attr_token(rest)
                {
                    return true;
                }
            }
            i += close + 1;
            continue;
        }
        i += 1;
    }

    // 2. Check return-value attributes preceding `<N x ptr>` / `%VecPtrAlias` before `@callee` / `%fn`.
    if let Some(callee_pos) = find_outside_quotes(raw_code, "@")
        && let Some(prefix) = raw_code.get(..callee_pos)
    {
        let prefix_trim = prefix.trim_end();
        // Check trailing `<...>` vector type or `%Alias` immediately before `@callee`.
        if let Some(lt_pos) = prefix_trim.rfind('<')
            && prefix_trim.ends_with('>')
            && let Some(vec_ty) = prefix_trim.get(lt_pos..)
            && let Some(before_ty) = prefix_trim.get(..lt_pos)
            && is_vector_of_pointer_type(&expand_llvm_type(vec_ty, type_aliases))
            && has_lane_ptr_attr_token(before_ty)
        {
            return true;
        }
        if let Some(pct_pos) = prefix_trim.rfind('%')
            && let Some(alias_ty) = prefix_trim.get(pct_pos..)
            && let Some(before_ty) = prefix_trim.get(..pct_pos)
            && is_vector_of_pointer_type(&expand_llvm_type(alias_ty, type_aliases))
            && has_lane_ptr_attr_token(before_ty)
        {
            return true;
        }
    }
    false
}

fn find_invalid_int_bitwidth_token(scrubbed: &str) -> Option<String> {
    for tok in scrubbed.split(|c: char| {
        c.is_ascii_whitespace()
            || matches!(c, ',' | '(' | ')' | '[' | ']' | '{' | '}' | '<' | '>' | '*')
    }) {
        if let Some(digits) = tok.strip_prefix('i').or_else(|| tok.strip_prefix('b'))
            && !digits.is_empty()
            && digits.bytes().all(|b| b.is_ascii_digit())
        {
            let valid = digits
                .parse::<u32>()
                .ok()
                .is_some_and(|bits| (1..=8_388_608).contains(&bits));
            if !valid {
                return Some(tok.to_owned());
            }
        }
    }
    None
}

fn check_range_attributes(scrubbed: &str, reasons: &mut Vec<String>) {
    let bytes = scrubbed.as_bytes();
    let mut search_from = 0_usize;
    while let Some(sub) = scrubbed.get(search_from..) {
        let Some(rel_pos) = sub.find("range(") else {
            break;
        };
        let abs_pos = search_from + rel_pos;
        let prev_boundary_ok = abs_pos == 0
            || bytes
                .get(abs_pos - 1)
                .is_some_and(|b| b.is_ascii_whitespace() || matches!(*b, b'(' | b'{'));
        if !prev_boundary_ok {
            search_from = abs_pos + "range(".len();
            continue;
        }

        let from_open = scrubbed.get(abs_pos + "range".len()..).unwrap_or("");
        let Some(close_paren) = find_matching_delim(from_open, b'(', b')') else {
            reasons.push(
                "malformed `range(...)` attribute requires Safe-Path fallback (F-35)".to_owned(),
            );
            break;
        };
        let inside = from_open.get(1..close_paren).unwrap_or("");
        let parts = split_top_level_commas(inside);
        let single_scalar_ok = if parts.len() == 2 {
            let first = parts.first().copied().unwrap_or("").trim();
            let second = parts.get(1).copied().unwrap_or("").trim();
            is_scalar_int_typed_literal(first) && is_signed_int_literal(second)
        } else {
            false
        };
        if !single_scalar_ok {
            reasons.push(
                "multi-pair or non-scalar `range(...)` attribute requires Safe-Path fallback (F-35)"
                    .to_owned(),
            );
        }
        search_from = abs_pos + "range".len() + close_paren + 1;
    }
}

fn is_scalar_int_typed_literal(s: &str) -> bool {
    let mut iter = s.split_whitespace();
    let Some(ty) = iter.next() else {
        return false;
    };
    let Some(lo) = iter.next() else {
        return false;
    };
    if iter.next().is_some() {
        return false;
    }
    let is_scalar_int = ty
        .strip_prefix('i')
        .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()));
    is_scalar_int && is_signed_int_literal(lo)
}

fn is_signed_int_literal(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

fn strip_optional_nneg(s: &str) -> &str {
    let trimmed = s.trim_start();
    if let Some(after_nneg) = trimmed.strip_prefix("nneg")
        && (after_nneg.starts_with(char::is_whitespace) || after_nneg.starts_with('('))
    {
        after_nneg.trim_start()
    } else {
        trimmed
    }
}

fn check_wide_int_to_fp_conversions(
    raw_code: &str,
    type_aliases: &BTreeMap<String, String>,
    reasons: &mut Vec<String>,
) {
    let scrubbed = mask_quoted_strings(raw_code);
    for op in ["sitofp", "uitofp"] {
        let bytes = scrubbed.as_bytes();
        let mut search_from = 0_usize;
        while let Some(sub) = scrubbed.get(search_from..) {
            let Some(rel_pos) = sub.find(op) else {
                break;
            };
            let abs_pos = search_from + rel_pos;
            let end_pos = abs_pos + op.len();
            let prev_ok = abs_pos == 0
                || bytes
                    .get(abs_pos - 1)
                    .is_some_and(|b| b.is_ascii_whitespace() || matches!(*b, b'(' | b'=' | b','));
            let next_ok = bytes
                .get(end_pos)
                .is_some_and(|b| b.is_ascii_whitespace() || *b == b'(');
            search_from = end_pos;
            if !prev_ok || !next_ok {
                continue;
            }

            let after_op = strip_optional_nneg(raw_code.get(end_pos..).unwrap_or(""));
            let expr_body = if after_op.starts_with('(') {
                let Some(close) = find_matching_delim(after_op, b'(', b')') else {
                    continue;
                };
                after_op.get(1..close).unwrap_or("")
            } else {
                after_op
            };

            let cur = strip_optional_nneg(expr_body);

            let Some((src_ty, after_src_ty)) = parse_balanced_llvm_type(cur) else {
                continue;
            };
            let expanded_src = expand_llvm_type(src_ty, type_aliases);
            let Some(src_bits) = extract_int_element_bitwidth(&expanded_src) else {
                continue;
            };
            let Some(after_to) = find_top_level_to_keyword(after_src_ty) else {
                continue;
            };
            let Some((dst_ty, _)) = parse_balanced_llvm_type(after_to) else {
                continue;
            };
            let expanded_dst = expand_llvm_type(dst_ty, type_aliases);
            let dst_fp = extract_fp_element_name(&expanded_dst);

            if dst_fp == "float" && src_bits > 32 {
                reasons.push(format!(
                    "`{op}` from `i{src_bits}` (> 32 bits) to `float` requires Safe-Path fallback (F-36)"
                ));
            } else if dst_fp == "double" && src_bits > 64 {
                reasons.push(format!(
                    "`{op}` from `i{src_bits}` (> 64 bits) to `double` requires Safe-Path fallback (F-36)"
                ));
            }
        }
    }
}

fn extract_int_element_bitwidth(ty: &str) -> Option<u32> {
    let trimmed = ty.trim();
    let elem = if let Some(inner) = trimmed.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        inner.rsplit('x').next()?.trim()
    } else {
        trimmed
    };
    elem.strip_prefix('i')?.parse::<u32>().ok()
}

fn extract_fp_element_name(ty: &str) -> &str {
    let trimmed = ty.trim();
    if let Some(inner) = trimmed.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
        inner.rsplit('x').next().unwrap_or("").trim()
    } else {
        trimmed
    }
}

fn find_top_level_to_keyword(s: &str) -> Option<&str> {
    let bytes = s.as_bytes();
    let mut depth = 0_i32;
    let mut i = 0_usize;
    while let Some(&b) = bytes.get(i) {
        match b {
            b'(' | b'[' | b'{' | b'<' => depth += 1,
            b')' | b']' | b'}' | b'>' => {
                if depth == 0 {
                    return None;
                }
                depth -= 1;
            }
            b',' if depth == 0 => return None,
            b't' if depth == 0 && bytes.get(i + 1) == Some(&b'o') => {
                let prev_ok = i == 0
                    || bytes.get(i - 1).is_some_and(|p| {
                        p.is_ascii_whitespace() || matches!(*p, b')' | b'>' | b']' | b'}')
                    });
                let next_ok = bytes.get(i + 2).is_some_and(u8::is_ascii_whitespace);
                if prev_ok && next_ok {
                    return s.get(i + 2..).map(str::trim_start);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

trait BundleCheckExt {
    fn not_or_bundle(self, line: &str) -> bool;
}

impl BundleCheckExt for bool {
    fn not_or_bundle(self, line: &str) -> bool {
        !self && line.contains(") [") && line.contains(']')
    }
}

fn is_non_f32_f64_fp_hex_literal(tok: &str) -> bool {
    for prefix in ["0xH", "0xR", "0xL", "0xK", "0xM"] {
        if let Some(hex) = tok.strip_prefix(prefix) {
            return !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit());
        }
    }
    if let Some(hex) = tok.strip_prefix("f0x") {
        return matches!(hex.len(), 4 | 20 | 32) && hex.bytes().all(|b| b.is_ascii_hexdigit());
    }
    false
}

/// Sanitizes an LLVM 23.1.5 IR module/slice into canonical surface syntax accepted by Vellvm 3.0.
///
/// Validates `target datalayout` (`F-22`) for all roles and, when `role == SliceRole::TargetFastPath`,
/// enforces `check_fast_path_eligibility` so target UB/poison constructs are never silently erased.
pub fn sanitize_for_vellvm(ir: &str, role: SliceRole) -> Result<String, BridgeError> {
    let fp_normalized = normalize_llvm23_fp_and_comments(ir)?;

    for line in fp_normalized.lines() {
        let code = strip_line_comment_preserving_strings(line).trim();
        if code.starts_with("target datalayout") {
            validate_target_datalayout(code)?;
        }
        if !code.is_empty()
            && !code.starts_with('!')
            && !code.starts_with("#dbg_")
            && !code.starts_with("source_filename")
            && !code.starts_with("target ")
        {
            let scrubbed = mask_quoted_strings(code);
            if let Some(bad_bw) = find_invalid_int_bitwidth_token(&scrubbed) {
                return Err(BridgeError::MalformedModule {
                    detail: format!(
                        "invalid LLVM integer/byte bitwidth `{bad_bw}` (must be 1..=8388608)"
                    ),
                });
            }
        }
    }

    if role == SliceRole::TargetFastPath
        && let FastPathEligibility::FallbackRequired { reasons } =
            check_fast_path_eligibility_normalized(&fp_normalized)
    {
        return Err(BridgeError::FastPathIneligible { reasons });
    }

    let mut out_lines: Vec<String> = Vec::new();
    for line in fp_normalized.lines() {
        let trimmed = line.trim();

        // Drop LLVM 20+ non-instruction debug records (`#dbg_value`, `#dbg_declare`, etc.)
        // and `uselistorder` directives rejected by Vellvm.
        if trimmed.starts_with("#dbg_")
            || trimmed.starts_with("uselistorder ")
            || trimmed.starts_with("uselistorder_bb ")
            || is_debug_metadata_line(trimmed)
        {
            continue;
        }

        let cleaned = sanitize_single_line_for_vellvm(line);
        out_lines.push(cleaned);
    }

    let mut result = out_lines.join("\n");
    if ir.ends_with('\n') {
        result.push('\n');
    }
    Ok(result)
}

fn is_debug_metadata_line(trimmed: &str) -> bool {
    if trimmed.starts_with("!llvm.dbg.") {
        return true;
    }
    if trimmed.starts_with('!')
        && let Some((_, rhs)) = trimmed.split_once('=')
    {
        let rhs_trim = rhs.trim().strip_prefix("distinct ").unwrap_or(rhs.trim());
        if rhs_trim.starts_with("!DI") || rhs_trim.starts_with("!GenericDINode(") {
            return true;
        }
    }
    false
}

fn sanitize_single_line_for_vellvm(line: &str) -> String {
    let mut s = line.to_owned();

    // Strip leading `declare !dbg !12 ...` and trailing `declare ... !prof !13` metadata
    // attachments rejected by Vellvm's `declaration` grammar (`F-55`).
    if s.trim_start().starts_with("declare ") {
        s = strip_declare_metadata(&s);
    }

    // Strip instruction `, !dbg !N` and function header ` !dbg !N` attachments.
    s = strip_dbg_attachments(&s);

    // Strip default-IEEE `denormal_fpenv(ieee)` / `denormal_fpenv(ieee|ieee)` inside attribute groups.
    if s.trim_start().starts_with("attributes #") {
        s = s
            .replace("denormal_fpenv(ieee|ieee)", "")
            .replace("denormal_fpenv(ieee)", "");
        s = collapse_extra_spaces_in_braces(&s);
    }

    // Strip `prefalign(N)` rejected by Vellvm function headers.
    s = strip_parenthesized_attr(&s, "prefalign(");

    s
}

fn strip_dbg_attachments(line: &str) -> String {
    let mut current = line.to_owned();
    // Handle `, !dbg !123` on instructions/globals.
    while let Some(idx) = find_outside_quotes(&current, ", !dbg !") {
        let after = current.get(idx + ", !dbg !".len()..).unwrap_or("");
        let digits = after
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        let prefix = current.get(..idx).unwrap_or("");
        let suffix = current.get(idx + ", !dbg !".len() + digits..).unwrap_or("");
        current = format!("{prefix}{suffix}");
    }
    // Handle ` !dbg !123` on `define ... !dbg !123 {`.
    while let Some(idx) = find_outside_quotes(&current, " !dbg !") {
        let after = current.get(idx + " !dbg !".len()..).unwrap_or("");
        let digits = after
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        let prefix = current.get(..idx).unwrap_or("");
        let suffix = current.get(idx + " !dbg !".len() + digits..).unwrap_or("");
        current = format!("{prefix}{suffix}");
    }
    current
}

fn strip_parenthesized_attr(line: &str, attr_prefix: &str) -> String {
    let mut current = line.to_owned();
    while let Some(idx) = find_outside_quotes(&current, attr_prefix) {
        let after = current.get(idx + attr_prefix.len()..).unwrap_or("");
        let Some(close) = after.find(')') else {
            break;
        };
        let prefix = current.get(..idx).unwrap_or("");
        let suffix = current
            .get(idx + attr_prefix.len() + close + 1..)
            .unwrap_or("")
            .strip_prefix(' ')
            .unwrap_or(
                current
                    .get(idx + attr_prefix.len() + close + 1..)
                    .unwrap_or(""),
            );
        current = format!("{prefix}{suffix}");
    }
    current
}

fn collapse_extra_spaces_in_braces(line: &str) -> String {
    let Some((before, rest)) = line.split_once('{') else {
        return line.to_owned();
    };
    let Some((inside, after)) = rest.rsplit_once('}') else {
        return line.to_owned();
    };
    let joined: Vec<&str> = inside.split_whitespace().collect();
    if joined.is_empty() {
        format!("{before}{{}}{after}")
    } else {
        format!("{before}{{ {} }}{after}", joined.join(" "))
    }
}

pub(crate) fn strip_declare_metadata(line: &str) -> String {
    let code_part = strip_line_comment_preserving_strings(line);
    let comment_part = line.get(code_part.len()..).unwrap_or("");
    let Some(rest) = code_part.trim_start().strip_prefix("declare ") else {
        return line.to_owned();
    };
    let indent_len = code_part.len().saturating_sub(code_part.trim_start().len());
    let indent = code_part.get(..indent_len).unwrap_or("");
    let mut cur = rest.trim_start();
    while let Some(after_bang) = cur.strip_prefix('!') {
        let after_key = after_bang.trim_start_matches(|c: char| !c.is_ascii_whitespace());
        let after_ws = after_key.trim_start();
        if let Some(after_val_bang) = after_ws.strip_prefix('!') {
            cur = after_val_bang
                .trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_')
                .trim_start();
        } else {
            break;
        }
    }

    // Also strip trailing `[, ]!<key> !<val>` attachments after parameter `(...)`.
    let cleaned_body = if let Some(open_paren) = find_outside_quotes(cur, "(")
        && let Some(from_open) = cur.get(open_paren..)
        && let Some(close_rel) = find_matching_delim(from_open, b'(', b')')
    {
        let split_idx = open_paren + close_rel + 1;
        let up_to_params = cur.get(..split_idx).unwrap_or(cur);
        let tail = cur.get(split_idx..).unwrap_or("");
        let cleaned_tail = strip_trailing_bang_pairs(tail);
        format!("{up_to_params}{cleaned_tail}")
    } else {
        cur.to_owned()
    };

    let mut rebuilt = format!("{indent}declare {}", cleaned_body.trim_end());
    if !comment_part.is_empty() {
        rebuilt.push(' ');
        rebuilt.push_str(comment_part);
    }
    rebuilt
}

fn strip_trailing_bang_pairs(tail: &str) -> String {
    let mut current = tail.to_owned();
    while let Some(bang_idx) = find_outside_quotes(&current, "!") {
        let after_bang = current.get(bang_idx + 1..).unwrap_or("");
        let key_len = after_bang
            .bytes()
            .take_while(|b| !b.is_ascii_whitespace())
            .count();
        let after_key = after_bang.get(key_len..).unwrap_or("");
        let ws_len = after_key
            .bytes()
            .take_while(u8::is_ascii_whitespace)
            .count();
        let after_ws = after_key.get(ws_len..).unwrap_or("");
        if let Some(after_val_bang) = after_ws.strip_prefix('!') {
            let val_len = after_val_bang
                .bytes()
                .take_while(|b| b.is_ascii_alphanumeric() || matches!(*b, b'_' | b'.' | b'-'))
                .count();
            let mut start_cut = bang_idx;
            while start_cut > 0
                && current
                    .as_bytes()
                    .get(start_cut - 1)
                    .is_some_and(|b| b.is_ascii_whitespace() || *b == b',')
            {
                start_cut -= 1;
            }
            let end_cut = bang_idx + 1 + key_len + ws_len + 1 + val_len;
            let prefix = current.get(..start_cut).unwrap_or("");
            let suffix = current.get(end_cut..).unwrap_or("");
            current = format!("{prefix}{suffix}");
        } else {
            break;
        }
    }
    current
}

pub(crate) fn strip_line_comment_preserving_strings(line: &str) -> &str {
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
        if b == b';' {
            return line.get(..i).unwrap_or(line);
        }
        i += 1;
    }
    line
}

pub(crate) fn mask_quoted_strings(line: &str) -> String {
    let bytes = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut i = 0_usize;
    while i < bytes.len() {
        if bytes.get(i) == Some(&b'"') {
            out.push_str("\"\"");
            i += 1;
            while let Some(&b) = bytes.get(i) {
                i += 1;
                if b == b'"' {
                    break;
                }
            }
            continue;
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

pub(crate) fn find_outside_quotes(haystack: &str, needle: &str) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    let bytes = haystack.as_bytes();
    let mut i = 0_usize;
    let mut in_quotes = false;
    while i < bytes.len() {
        if in_quotes {
            if bytes.get(i) == Some(&b'"') {
                in_quotes = false;
            }
            i += 1;
            continue;
        }
        if bytes.get(i) == Some(&b'"') {
            in_quotes = true;
            i += 1;
            continue;
        }
        if haystack.get(i..).is_some_and(|s| s.starts_with(needle)) {
            return Some(i);
        }
        i += 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_half_bfloat_fp128_gated_to_safe_path() {
        let half_ir = "\
define half @scale_half(half %x) {
entry:
  %y = fadd half %x, 0xH3C00
  ret half %y
}
";
        let verdict = check_fast_path_eligibility(half_ir);
        assert!(!verdict.is_eligible());
        assert_eq!(
            verdict,
            FastPathEligibility::FallbackRequired {
                reasons: vec![
                    "half/bfloat/fp128 value operation requires Safe-Path (Vellvm models f32/f64 values only)"
                        .to_owned()
                ],
            }
        );
        assert!(matches!(
            sanitize_for_vellvm(half_ir, SliceRole::TargetFastPath),
            Err(BridgeError::FastPathIneligible { .. })
        ));
    }

    #[test]
    fn test_target_fp_hex_literals_gated_to_safe_path() {
        for snippet in [
            "define void @f() {\n  %x = bitcast i16 0 to half\n  ret void\n}\n",
            "define void @f() {\n  store bfloat 0xR3F80, ptr null, align 2\n  ret void\n}\n",
            "define void @f() {\n  store fp128 0xL00000000000000003FFF000000000000, ptr null, align 16\n  ret void\n}\n",
            "define void @f() {\n  store x86_fp80 0xK3FFF8000000000000000, ptr null, align 16\n  ret void\n}\n",
        ] {
            assert!(!check_fast_path_eligibility(snippet).is_eligible());
        }
    }

    #[test]
    fn test_half_identifiers_and_non_exec_decls_remain_fast_path_eligible() {
        let eligible_ir = "\
%struct.HalfPacket = type { half, i32 }
declare half @unused_half_decl(half)
declare i32 @half_fn(i32)

define float @compute(i32 %a, float %half_val) {
half:
  %half_width = add i32 %a, 1
  %c = call i32 @half_fn(i32 %half_width)
  %d = sitofp i32 %c to float
  %res = fadd float %half_val, 0x3FF0000000000000
  %sum = fadd float %res, %d
  ret float %sum
}
";
        assert_eq!(
            check_fast_path_eligibility(eligible_ir),
            FastPathEligibility::Eligible
        );
        assert!(sanitize_for_vellvm(eligible_ir, SliceRole::TargetFastPath).is_ok());
    }

    #[test]
    fn test_wp1_fast_path_gates_f17_f18_f30_f31_f32_f33_f34_f35_f36_f38() {
        // F-17: Every fast-math-capable LLVM 23 instruction MUST be gated.
        for fmf_stmt in [
            "%r = fadd nnan float %a, %b",
            "%r = fsub ninf float %a, %b",
            "%r = fmul nsz double %d1, %d2",
            "%r = fdiv arcp float %a, %b",
            "%r = fneg contract float %a",
            "%r = fcmp afn oeq float %a, %b",
            "%r = select reassoc i1 true, float %a, float %b",
            "%r = phi fast float [ %a, %entry ]",
            "%r = fptrunc contract double %d1 to float",
            "%r = fpext nnan float %a to double",
            "%r = call fast float @ext_fp(float %a)",
        ] {
            let ir = format!(
                "declare float @ext_fp(float)\ndefine void @f(float %a, float %b, double %d1, double %d2) {{\nentry:\n  {fmf_stmt}\n  ret void\n}}\n"
            );
            assert!(
                !check_fast_path_eligibility(&ir).is_eligible(),
                "expected F-17 rejection for `{fmf_stmt}`"
            );
        }
        // `nofpclass(ninf)` on a call without fast-math flags must NOT false-positive!
        let nofpclass_ok = "declare float @ext_fp(float)\ndefine float @f(float %x) {\n  %r = call nofpclass(ninf) float @ext_fp(float %x)\n  ret float %r\n}\n";
        assert!(check_fast_path_eligibility(nofpclass_ok).is_eligible());

        // F-18: Volatile, atomics, fence, and non-false volatile mem intrinsics.
        for mem_stmt in [
            "%v = load volatile i32, ptr %p, align 4",
            "store volatile i32 1, ptr %p, align 4",
            "%v = load atomic i32, ptr %p seq_cst, align 4",
            "store atomic i32 1, ptr %p release, align 4",
            "%v = cmpxchg ptr %p, i32 0, i32 1 acq_rel monotonic, align 4",
            "%v = atomicrmw add ptr %p, i32 1 seq_cst, align 4",
            "fence acquire",
            "call void @llvm.memcpy.p0.p0.i64(ptr %p, ptr %q, i64 8, i1 true)",
            "call void @llvm.memmove.p0.p0.i64(ptr %p, ptr %q, i64 8, i1 %dyn_vol)",
            "call void @llvm.memset.p0.i64(ptr %p, i8 0, i64 8, i1 1)",
        ] {
            let ir = format!(
                "define void @f(ptr %p, ptr %q, i1 %dyn_vol) {{\n  {mem_stmt}\n  ret void\n}}\n"
            );
            assert!(
                !check_fast_path_eligibility(&ir).is_eligible(),
                "expected F-18 rejection for `{mem_stmt}`"
            );
        }
        // Non-volatile `i1 false` memcpy/memmove/memset + verified pure intrinsics remain Eligible!
        let verified_intrinsics_ok = "\
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)
declare float @llvm.fma.f32(float, float, float)
declare i32 @llvm.smin.i32(i32, i32)
declare i16 @llvm.bswap.i16(i16)
define float @ok_intrinsics(ptr %d, ptr %s, float %x, i32 %i, i16 %w) {
  call void @llvm.memcpy.p0.p0.i64(ptr %d, ptr %s, i64 16, i1 false)
  %m = call i32 @llvm.smin.i32(i32 %i, i32 7)
  %b = call i16 @llvm.bswap.i16(i16 %w)
  %f = call float @llvm.fma.f32(float %x, float %x, float %x)
  ret float %f
}
";
        assert!(check_fast_path_eligibility(verified_intrinsics_ok).is_eligible());

        // F-30: Unlisted `@llvm.*` intrinsics MUST be gated.
        for bad_intr in [
            "call void @llvm.lifetime.start.p0(i64 4, ptr %p)",
            "call void @llvm.lifetime.end.p0(i64 4, ptr %p)",
            "%sp = call ptr @llvm.stacksave.p0()",
            "call void @llvm.stackrestore.p0(ptr %p)",
            "%q = call ptr @llvm.launder.invariant.group.p0(ptr %p)",
            "call void @llvm.experimental.noalias.scope.decl(metadata !0)",
            "%e = call i64 @llvm.expect.with.probability.i64(i64 1, i64 1, double 0.9)",
            "call void @llvm.assume(i1 true)",
            "%t = call ptr @llvm.threadlocal.address.p0(ptr @tls_g)",
            "%b8 = call i8 @llvm.bswap.i8(i8 1)",
        ] {
            let ir = format!("define void @f(ptr %p) {{\n  {bad_intr}\n  ret void\n}}\n");
            assert!(
                !check_fast_path_eligibility(&ir).is_eligible(),
                "expected F-30 rejection for `{bad_intr}`"
            );
        }

        // F-31: Variadic prototypes/calls, `@llvm.va_*`, and `va_arg`.
        for var_ir in [
            "declare i32 @printf(ptr, ...)\ndefine void @f() {\n  ret void\n}\n",
            "define i32 @var_fn(i32 %x, ...) {\n  ret i32 %x\n}\n",
            "define void @f(ptr %ap) {\n  call void @llvm.va_start.p0(ptr %ap)\n  ret void\n}\n",
            "define i32 @f(ptr %ap) {\n  %v = va_arg ptr %ap, i32\n  ret i32 %v\n}\n",
        ] {
            assert!(!check_fast_path_eligibility(var_ir).is_eligible());
        }

        // F-32: Memory-passing parameter attributes (`byval`, `inalloca`, `preallocated`, `byref`, `initializes`).
        for attr in [
            "byval(i32)",
            "inalloca(i32)",
            "preallocated(i32)",
            "byref(i32)",
            "initializes((0, 4))",
        ] {
            let ir = format!("define void @f(ptr {attr} %p) {{\n  ret void\n}}\n");
            assert!(
                !check_fast_path_eligibility(&ir).is_eligible(),
                "expected F-32 rejection for `{attr}`"
            );
        }

        // F-33: `extern_weak` and constant-expression aliases.
        assert!(
            !check_fast_path_eligibility(
                "declare extern_weak i32 @opt_hook()\ndefine i32 @f() {\n  %r = call i32 @opt_hook()\n  ret i32 %r\n}\n"
            )
            .is_eligible()
        );
        assert!(
            !check_fast_path_eligibility(
                "@buf = global [4 x i32] zeroinitializer\n@mid = alias i32, getelementptr inbounds ([4 x i32], ptr @buf, i64 0, i64 2)\ndefine ptr @f() {\n  ret ptr @mid\n}\n"
            )
            .is_eligible()
        );

        // F-34: Unwinding / exception instructions (`invoke`, `landingpad`, `resume`).
        let invoke_ir = "\
declare i32 @__gxx_personality_v0(...)
declare void @may_throw()
define void @eh_fn() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @may_throw() to label %ok unwind label %lpad
ok:
  ret void
lpad:
  %lp = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %lp
}
";
        assert!(!check_fast_path_eligibility(invoke_ir).is_eligible());

        // F-35: `inrange(...)` GEP and multi-pair / vector `range(...)`.
        assert!(
            !check_fast_path_eligibility(
                "define ptr @f(ptr %vtable) {\n  %p = getelementptr inbounds inrange(-8, 16) i8, ptr %vtable, i64 8\n  ret ptr %p\n}\n"
            )
            .is_eligible()
        );
        assert!(
            !check_fast_path_eligibility(
                "define range(i32 0, 2, 4, 6) i32 @f(i32 %x) {\n  ret i32 %x\n}\n"
            )
            .is_eligible()
        );
        assert!(
            !check_fast_path_eligibility(
                "define range(<2 x i32> 0, 4) <2 x i32> @f(<2 x i32> %x) {\n  ret <2 x i32> %x\n}\n"
            )
            .is_eligible()
        );
        // Single-pair scalar `range(i32 0, 10)` remains Eligible!
        assert!(
            check_fast_path_eligibility("define range(i32 0, 10) i32 @f() {\n  ret i32 3\n}\n")
                .is_eligible()
        );

        // F-36: `sitofp`/`uitofp` >32-bit -> float and >64-bit -> double gated; <=32->float & <=64->double Eligible!
        for wide_conv in [
            "%f = sitofp i64 %x64 to float",
            "%f = uitofp nneg i64 %x64 to float",
            "%f = uitofp i128 %x128 to float",
            "%d = sitofp i128 %x128 to double",
            "%d = uitofp i128 %x128 to double",
            "%vf = uitofp <2 x i64> undef to <2 x float>",
        ] {
            let ir =
                format!("define void @f(i64 %x64, i128 %x128) {{\n  {wide_conv}\n  ret void\n}}\n");
            assert!(
                !check_fast_path_eligibility(&ir).is_eligible(),
                "expected F-36 rejection for `{wide_conv}`"
            );
        }
        let safe_convs = "\
define double @safe_fp_convs(i32 %x32, i64 %x64) {
  %f1 = sitofp i32 %x32 to float
  %f2 = uitofp nneg i16 7 to float
  %d1 = sitofp i64 %x64 to double
  %d2 = uitofp i64 %x64 to double
  %ext = fpext float %f1 to double
  %sum = fadd double %d1, %ext
  ret double %sum
}
";
        assert!(check_fast_path_eligibility(safe_convs).is_eligible());

        // F-38: `frem` MUST be gated.
        assert!(
            !check_fast_path_eligibility(
                "define float @f(float %a, float %b) {\n  %r = frem float %a, %b\n  ret float %r\n}\n"
            )
            .is_eligible()
        );
    }
}
