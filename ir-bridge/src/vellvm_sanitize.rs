use serde::{Deserialize, Serialize};

use crate::error::BridgeError;
use crate::fp_literals::normalize_llvm23_fp_and_comments;

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

/// Audits an `-O2` target IR slice against Vellvm 3.0's ground-truth parser & operational semantics
/// (`F-08` & `F-14`). Any construct whose naive stripping or `TODO` evaluation could mask target
/// poison/UB causes deterministic routing to `verified-opt-fallback`.
#[must_use]
pub fn check_fast_path_eligibility(ir: &str) -> FastPathEligibility {
    let mut reasons: Vec<String> = Vec::new();

    for raw_line in ir.lines() {
        let code = strip_line_comment_preserving_strings(raw_line).trim();
        if code.is_empty()
            || code.starts_with('!')
            || code.starts_with("#dbg_")
            || code.starts_with("source_filename")
            || code.starts_with("target ")
        {
            continue;
        }

        let scrubbed = mask_quoted_strings(code);
        let tokens: Vec<&str> = scrubbed
            .split(|c: char| c.is_ascii_whitespace() || matches!(c, ',' | '(' | ')'))
            .filter(|t| !t.is_empty())
            .collect();

        check_line_soundness_hazards(&scrubbed, &tokens, &mut reasons);
    }

    reasons.sort();
    reasons.dedup();
    if reasons.is_empty() {
        FastPathEligibility::Eligible
    } else {
        FastPathEligibility::FallbackRequired { reasons }
    }
}

fn check_line_soundness_hazards(scrubbed: &str, tokens: &[&str], reasons: &mut Vec<String>) {
    for (idx, &tok) in tokens.iter().enumerate() {
        let next1 = tokens.get(idx + 1).copied().unwrap_or("");
        // 1. Vellvm IP64Bit (`IPtrFinite.v:24,97`) uses unsigned `to_Z` and `msamesign = true`
        // to preserve I2F against unbounded `PInf`, whereas AArch64/RISC-V lower `icmp samesign ult`
        // to signed branches (`b.lt`/`blt`). Keep pointer/`iptr` `icmp samesign` gated (F-15).
        if tok == "icmp"
            && next1 == "samesign"
            && matches!(tokens.get(idx + 3).copied(), Some("ptr" | "iptr"))
        {
            reasons.push(
                "pointer/iptr `icmp samesign` requires Safe-Path fallback under IP64Bit MMIO addresses (F-15)"
                    .to_owned(),
            );
        }
        // 3. Fast-math flags on `call` or `select` are rejected by Vellvm's parser.
        if (tok == "call" || tok == "select") && FAST_MATH_FLAGS.contains(&next1) {
            reasons.push(format!(
                "fast-math flag `{next1}` on `{tok}` unsupported in Vellvm parser"
            ));
        }
        // 4. Inline asm, callbr, and SEH exception pads.
        if tok == "callbr"
            || tok == "catchswitch"
            || tok == "catchpad"
            || tok == "cleanuppad"
            || tok == "catchret"
            || tok == "cleanupret"
        {
            reasons.push(format!("unsupported control-flow instruction `{tok}`"));
        }
        if tok == "asm" && !scrubbed.trim_start().starts_with("module asm") {
            reasons.push("inline `asm` call cannot be validated in Vellvm".to_owned());
        }
        // 5. Unsupported target calling conventions.
        if UNSUPPORTED_CCONVS.contains(&tok) {
            reasons.push(format!(
                "target calling convention `{tok}` unsupported in Vellvm"
            ));
        }
        // 6. `bfloat` / `fp128` runtime values (only `float` and `double` values denote in Vellvm).
        if (tok == "bfloat" || tok == "fp128")
            && !scrubbed.trim_start().starts_with("declare ")
            && !scrubbed.contains(" = type ")
        {
            reasons.push(format!(
                "`{tok}` value computation unsupported in Vellvm Denotation.v (F-08)"
            ));
        }
    }

    // 7. Call / invoke operand bundles (`call void @llvm.assume(i1 true) [ "align"(ptr %p, i64 8) ]`).
    if (scrubbed.contains("call ") || scrubbed.contains("invoke "))
        && scrubbed.contains(") [")
        && scrubbed.contains("](").not_or_bundle(scrubbed)
    {
        reasons.push(
            "call/invoke operand bundle `[ ... ]` cannot be stripped soundly on target IR"
                .to_owned(),
        );
    }

    // 8. Non-IEEE `denormal_fpenv(...)` mode changes floating-point flush-to-zero semantics.
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

trait BundleCheckExt {
    fn not_or_bundle(self, line: &str) -> bool;
}

impl BundleCheckExt for bool {
    fn not_or_bundle(self, line: &str) -> bool {
        !self && line.contains(") [") && line.contains(']')
    }
}

/// Sanitizes an LLVM 23.1.5 IR module/slice into canonical surface syntax accepted by Vellvm 3.0.
///
/// When `role == SliceRole::TargetFastPath`, enforces `check_fast_path_eligibility` first so
/// target UB/poison constructs are never silently erased.
pub fn sanitize_for_vellvm(ir: &str, role: SliceRole) -> Result<String, BridgeError> {
    let fp_normalized = normalize_llvm23_fp_and_comments(ir)?;

    if role == SliceRole::TargetFastPath
        && let FastPathEligibility::FallbackRequired { reasons } =
            check_fast_path_eligibility(&fp_normalized)
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

    // Strip `declare !dbg !12 ...` metadata attachment rejected by Vellvm's `declaration` rule.
    if let Some(rest) = s.trim_start().strip_prefix("declare ") {
        let indent_len = s.len().saturating_sub(s.trim_start().len());
        let indent = s.get(..indent_len).unwrap_or("");
        let mut cur = rest;
        while let Some(after_bang) = cur.strip_prefix('!') {
            // Skip `!<kind> !<N>` pairs on `declare`.
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
        s = format!("{indent}declare {cur}");
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

pub(crate) fn strip_line_comment_preserving_strings(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut i = 0_usize;
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
                if b == b'\\' {
                    i = (i + 2).min(bytes.len());
                    continue;
                }
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
            if bytes.get(i) == Some(&b'\\') {
                i = (i + 2).min(bytes.len());
                continue;
            }
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
