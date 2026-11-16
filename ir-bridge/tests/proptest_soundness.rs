//! High-assurance `proptest` soundness suite for `ir-bridge` (`Phase 2.3b`).
//!
//! Uses `proptest::test_runner::TestRunner` directly inside fallible `Result<(), String>` tests
//! so zero macro-generated `panic!` / `unreachable!` calls or lint-suppression attributes exist.

use std::collections::{BTreeMap, BTreeSet};

use ir_bridge::{
    BridgeError, FastPathEligibility, SliceRole, check_fast_path_eligibility, f32_bits_to_f64_bits,
    f64_bits_to_f32_bits_exact, is_verified_vellvm_intrinsic, merge_module,
    normalize_llvm23_fp_and_comments, sanitize_for_vellvm, split_module, split_module_for_vellvm,
    validate_target_datalayout, verify_f32_f64_roundtrip_invariants,
    verify_f64_f32_exact_image_invariants, verify_utf8_scanner_panic_freedom,
};
use proptest::collection::vec;
use proptest::prelude::{BoxedStrategy, Just, Strategy, any};
use proptest::strategy::Union;
use proptest::test_runner::{Config, TestCaseError, TestRunner};

const PROPTEST_CASES: u32 = 512;

fn runner() -> TestRunner {
    TestRunner::new(Config::with_cases(PROPTEST_CASES))
}

fn prop_ensure(cond: bool, msg: impl Into<String>) -> Result<(), TestCaseError> {
    if cond {
        Ok(())
    } else {
        Err(TestCaseError::fail(msg.into()))
    }
}

fn f32_bits_strategy() -> BoxedStrategy<u32> {
    let special = Union::new([
        Just(0x0000_0000_u32).boxed(),
        Just(0x8000_0000_u32).boxed(),
        Just(0x7F80_0000_u32).boxed(),
        Just(0xFF80_0000_u32).boxed(),
        (any::<bool>(), 1_u32..=0x007F_FFFF_u32)
            .prop_map(|(neg, frac)| (if neg { 0x8000_0000 } else { 0 }) | frac)
            .boxed(),
        (any::<bool>(), 1_u32..=0x003F_FFFF_u32)
            .prop_map(|(neg, payload)| (if neg { 0x8000_0000 } else { 0 }) | 0x7F80_0000 | payload)
            .boxed(),
        (any::<bool>(), 0_u32..=0x003F_FFFF_u32)
            .prop_map(|(neg, payload)| (if neg { 0x8000_0000 } else { 0 }) | 0x7FC0_0000 | payload)
            .boxed(),
    ])
    .boxed();

    Union::new([any::<u32>().boxed(), special]).boxed()
}

#[test]
fn prop_f32_to_f64_ieee754_soundness_and_bijectivity() -> Result<(), String> {
    let mut tr = runner();
    let strat = (f32_bits_strategy(), f32_bits_strategy(), 0_u32..29_u32);

    tr.run(&strat, |(b1, b2, low_bit)| {
        prop_ensure(
            verify_f32_f64_roundtrip_invariants(b1),
            format!("roundtrip invariant failed for b1=0x{b1:08X}"),
        )?;
        prop_ensure(
            verify_f32_f64_roundtrip_invariants(b2),
            format!("roundtrip invariant failed for b2=0x{b2:08X}"),
        )?;

        let w1 = f32_bits_to_f64_bits(b1);
        let w2 = f32_bits_to_f64_bits(b2);

        // Strict bit-level injectivity across all 2^32 binary32 bit patterns (including sNaNs):
        prop_ensure(
            (b1 == b2) == (w1 == w2),
            format!("injectivity violation: 0x{b1:08X} -> 0x{w1:016X}, 0x{b2:08X} -> 0x{w2:016X}"),
        )?;

        // Bit-for-bit agreement with IEEE-754 widening on all non-NaNs (+-0.0, subnormals, normals, +-inf):
        if (b1 & 0x7FFF_FFFF) <= 0x7F80_0000 {
            let cpu_widened = f64::from(f32::from_bits(b1)).to_bits();
            prop_ensure(
                w1 == cpu_widened,
                format!(
                    "non-NaN mismatch on 0x{b1:08X}: got 0x{w1:016X}, expected 0x{cpu_widened:016X}"
                ),
            )?;
        }

        // Setting any low-29 mantissa bit on a non-zero widened binary32 leaves the exact image:
        if (b1 & 0x7FFF_FFFF) != 0 {
            let perturbed = w1 | (1_u64 << low_bit);
            prop_ensure(
                f64_bits_to_f32_bits_exact(perturbed).is_none(),
                format!("perturbed non-zero f64 0x{perturbed:016X} must return None"),
            )?;
        }

        Ok(())
    })
    .map_err(|e| format!("{e}"))
}

#[test]
fn prop_f64_to_f32_exact_right_inverse_and_out_of_image_rejection() -> Result<(), String> {
    let mut tr = runner();
    let out_of_image = Union::new([
        // Binary64 subnormals (`exp64 == 0`, `frac64 != 0`)
        (any::<bool>(), 1_u64..=0x000F_FFFF_FFFF_FFFF_u64)
            .prop_map(|(neg, frac)| (if neg { 1_u64 << 63 } else { 0 }) | frac)
            .boxed(),
        // Binary64 exponents `1..=873` (`873` = 2^-150, strictly below min f32 subnormal 2^-149)
        (
            any::<bool>(),
            1_u64..=873_u64,
            0_u64..=0x000F_FFFF_FFFF_FFFF_u64,
        )
            .prop_map(|(neg, exp, frac)| (if neg { 1_u64 << 63 } else { 0 }) | (exp << 52) | frac)
            .boxed(),
        // Inexact mantissa bits in the binary32 subnormal exponent window `874..=896`
        (any::<bool>(), 874_u64..=896_u64, 0_u32..30_u32)
            .prop_map(|(neg, exp, bit_idx)| {
                let shift = 897 - exp;
                let low_zero_bits = 29 + shift;
                let bad_bit = u64::from(bit_idx) % low_zero_bits;
                (if neg { 1_u64 << 63 } else { 0 }) | (exp << 52) | (1_u64 << bad_bit)
            })
            .boxed(),
        // Finite binary64 overflow exponents `1151..=2046`
        (
            any::<bool>(),
            1151_u64..=2046_u64,
            0_u64..=0x000F_FFFF_FFFF_FFFF_u64,
        )
            .prop_map(|(neg, exp, frac)| (if neg { 1_u64 << 63 } else { 0 }) | (exp << 52) | frac)
            .boxed(),
    ])
    .boxed();

    let strat = (any::<u64>(), out_of_image, f32_bits_strategy());

    tr.run(&strat, |(arb64, non_f32_64, exact_32)| {
        prop_ensure(
            verify_f64_f32_exact_image_invariants(arb64),
            format!("right-inverse failed on 0x{arb64:016X}"),
        )?;
        prop_ensure(
            f64_bits_to_f32_bits_exact(non_f32_64).is_none(),
            format!("out-of-image f64 0x{non_f32_64:016X} must be rejected"),
        )?;
        let widened = f32_bits_to_f64_bits(exact_32);
        prop_ensure(
            verify_f64_f32_exact_image_invariants(widened)
                && f64_bits_to_f32_bits_exact(widened) == Some(exact_32),
            format!("exact image failed on widened 0x{widened:016X}"),
        )?;
        Ok(())
    })
    .map_err(|e| format!("{e}"))
}

fn safe_ascii_word_strategy() -> BoxedStrategy<String> {
    vec(0_u8..26_u8, 1..=10)
        .prop_map(|v| v.into_iter().map(|c| char::from(b'a' + c)).collect())
        .boxed()
}

fn has_block_comment_outside_quotes_and_line_comments(ir: &str) -> bool {
    let bytes = ir.as_bytes();
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
            while let Some(&ch) = bytes.get(i) {
                i += 1;
                if ch == b'\n' {
                    break;
                }
            }
            continue;
        }
        if (b == b'/' && bytes.get(i + 1) == Some(&b'*'))
            || (b == b'*' && bytes.get(i + 1) == Some(&b'/'))
        {
            return true;
        }
        i += 1;
    }
    false
}

#[test]
fn prop_normalize_llvm23_fp_idempotence_and_string_preservation() -> Result<(), String> {
    let mut tr = runner();
    let strat = (
        f32_bits_strategy(),
        any::<u64>(),
        any::<u16>(),
        any::<u128>(),
        1_u32..=0x003F_FFFF_u32,
        1_u64..=((1_u64 << 51) - 1),
        any::<bool>(),
        safe_ascii_word_strategy(),
        safe_ascii_word_strategy(),
    );

    tr.run(
        &strat,
        |(
            f32_bits,
            f64_bits,
            f16_bits,
            f128_bits,
            snan32_pay,
            qnan64_pay,
            sign_flag,
            comment_tag,
            str_tag,
        )| {
            let sign_ch = if sign_flag { '-' } else { '+' };
            let quoted_const = format!(
                "c\"keep /* {str_tag} */ f0x{f32_bits:08x} +inf -qnan +snan(0x1) \\22ok\\22\\00\""
            );
            let const_len = 50 + str_tag.len();
            let ir = format!(
                "\
source_filename = \"norm_{str_tag}.c\"
@MSG = private unnamed_addr constant [{const_len} x i8] {quoted_const}, align 1
declare i1 @llvm.is.fpclass.f32(float, i32)
declare void @inf()

define float @fp_kernel(float %f0x12345678, double %d_in, half %h_in, bfloat %bf_in, fp128 %q_in) {{
f0x00000000:
  ; line comment /* keep unclosed f0xDEADBEEF +inf -snan(0x0)
  call void @inf()
  %a = /* {comment_tag} */ fadd float %f0x12345678, f0x{f32_bits:08x}
  %b = fadd float %a, {sign_ch}snan(0x{snan32_pay:x})
  %c = select i1 true, float {sign_ch}inf, float {sign_ch}qnan
  %cls = call i1 @llvm.is.fpclass.f32(float %c, i32 /* immarg */ 516)
  %d1 = fadd double %d_in, f0x{f64_bits:016X}
  %d2 = fadd double %d1, {sign_ch}nan(0x{qnan64_pay:x})
  %h1 = fadd half %h_in, f0x{f16_bits:04x}
  %bf1 = fadd bfloat %bf_in, f0x{f16_bits:04X}
  %q1 = fadd fp128 %q_in, f0x{f128_bits:032x}
  ret float %b
}}
"
            );

            let norm1 = normalize_llvm23_fp_and_comments(&ir)
                .map_err(|e| TestCaseError::fail(format!("first normalize failed: {e}")))?;
            let norm2 = normalize_llvm23_fp_and_comments(&norm1)
                .map_err(|e| TestCaseError::fail(format!("second normalize failed: {e}")))?;

            // 1. Strict idempotence: `norm(norm(s)) == norm(s)`.
            prop_ensure(
                norm1 == norm2,
                "normalize_llvm23_fp_and_comments is not idempotent",
            )?;

            // 2. Quoted string constants, `%f0x...` SSA names, `@inf` globals, and `f0x...:` labels untouched:
            prop_ensure(
                norm1.contains(&quoted_const),
                format!("quoted string constant was corrupted: expected `{quoted_const}`"),
            )?;
            prop_ensure(
                norm1.contains("%f0x12345678")
                    && norm1.contains("call void @inf()")
                    && norm1.contains("f0x00000000:"),
                "identifier or basic-block label starting with FP keyword was mutated",
            )?;

            // 3. All inline `/* ... */` comments outside quotes and `;` line comments stripped:
            prop_ensure(
                !has_block_comment_outside_quotes_and_line_comments(&norm1),
                format!("unstripped block comment remained in normalized IR:\n{norm1}"),
            )?;

            // 4. Emitted float `0x<16-hex>` bit-invertibly encodes `f32_bits`:
            let expected_f32_hex = format!("0x{:016X}", f32_bits_to_f64_bits(f32_bits));
            prop_ensure(
                norm1.contains(&format!("fadd float %f0x12345678, {expected_f32_hex}")),
                format!("missing exact widened f32 literal `{expected_f32_hex}`"),
            )?;
            let parsed_u64 =
                u64::from_str_radix(expected_f32_hex.strip_prefix("0x").unwrap_or(""), 16)
                    .map_err(|e| TestCaseError::fail(format!("{e}")))?;
            prop_ensure(
                f64_bits_to_f32_bits_exact(parsed_u64) == Some(f32_bits),
                "emitted 0x<hex> float literal failed exact f32 bit recovery",
            )?;

            Ok(())
        },
    )
    .map_err(|e| format!("{e}"))
}

#[derive(Debug, Clone)]
enum MalformedCase {
    UnterminatedComment(String),
    InvalidFloatLiteral(String),
}

fn malformed_fp_or_comment_strategy() -> BoxedStrategy<MalformedCase> {
    let bad_f0x_lengths: [usize; 14] = [1, 2, 3, 5, 6, 7, 9, 12, 15, 17, 19, 24, 31, 36];

    let unclosed_comment = safe_ascii_word_strategy()
        .prop_map(|w| {
            MalformedCase::UnterminatedComment(format!(
                "define void @f() {{\n  /* unclosed {w}\n  ret void\n}}\n"
            ))
        })
        .boxed();

    let wrong_len_f0x = (0_usize..14_usize, 0_u8..16_u8)
        .prop_map(move |(idx, nib)| {
            let n = bad_f0x_lengths.get(idx).copied().unwrap_or(3);
            let ch = if nib < 10 {
                char::from(b'0' + nib)
            } else {
                char::from(b'a' + (nib - 10))
            };
            let hex: String = std::iter::repeat_n(ch, n).collect();
            MalformedCase::InvalidFloatLiteral(format!(
                "define float @f(float %x) {{\n  %r = fadd float %x, f0x{hex}\n  ret float %r\n}}\n"
            ))
        })
        .boxed();

    let zero_snan = (0_usize..5_usize, any::<bool>(), 1_usize..=6_usize)
        .prop_map(|(ty_idx, neg, zeros)| {
            let ty = match ty_idx {
                0 => "half",
                1 => "bfloat",
                2 => "float",
                3 => "double",
                _ => "fp128",
            };
            let sign = if neg { '-' } else { '+' };
            let z: String = std::iter::repeat_n('0', zeros).collect();
            MalformedCase::InvalidFloatLiteral(format!(
                "define {ty} @f({ty} %x) {{\n  %r = fadd {ty} %x, {sign}snan(0x{z})\n  ret {ty} %r\n}}\n"
            ))
        })
        .boxed();

    let overflow_nan = (0_usize..4_usize, any::<bool>(), any::<bool>(), 0_u64..1024_u64)
        .prop_map(|(ty_idx, neg, sig, extra)| {
            let (ty, limit): (&str, u64) = match ty_idx {
                0 => ("bfloat", 1_u64 << 6),
                1 => ("half", 1_u64 << 9),
                2 => ("float", 1_u64 << 22),
                _ => ("double", 1_u64 << 51),
            };
            let sign = if neg { '-' } else { '+' };
            let kind = if sig { "snan" } else { "nan" };
            let bad_pay = limit.saturating_add(extra);
            MalformedCase::InvalidFloatLiteral(format!(
                "define {ty} @f({ty} %x) {{\n  %r = fadd {ty} %x, {sign}{kind}(0x{bad_pay:x})\n  ret {ty} %r\n}}\n"
            ))
        })
        .boxed();

    let malformed_nan_payload = (any::<bool>(), safe_ascii_word_strategy())
        .prop_map(|(missing_0x, w)| {
            let pay = if missing_0x {
                "1234".to_owned()
            } else {
                format!("0xZZ{w}")
            };
            MalformedCase::InvalidFloatLiteral(format!(
                "define float @f(float %x) {{\n  %r = fadd float %x, +nan({pay})\n  ret float %r\n}}\n"
            ))
        })
        .boxed();

    let x86_fp80_special = any::<bool>()
        .prop_map(|neg| {
            let sign = if neg { '-' } else { '+' };
            MalformedCase::InvalidFloatLiteral(format!(
                "define x86_fp80 @f(x86_fp80 %x) {{\n  %r = fadd x86_fp80 %x, {sign}inf\n  ret x86_fp80 %r\n}}\n"
            ))
        })
        .boxed();

    Union::new([
        unclosed_comment,
        wrong_len_f0x,
        zero_snan,
        overflow_nan,
        malformed_nan_payload,
        x86_fp80_special,
    ])
    .boxed()
}

#[test]
fn prop_fail_fast_malformed_fp_and_unterminated_comments() -> Result<(), String> {
    let mut tr = runner();
    let strat = malformed_fp_or_comment_strategy();

    tr.run(&strat, |case| match case {
        MalformedCase::UnterminatedComment(ir) => {
            let res = normalize_llvm23_fp_and_comments(&ir);
            prop_ensure(
                matches!(res, Err(BridgeError::UnterminatedBlockComment)),
                format!("expected UnterminatedBlockComment, got {res:?}"),
            )
        }
        MalformedCase::InvalidFloatLiteral(ir) => {
            let res = normalize_llvm23_fp_and_comments(&ir);
            prop_ensure(
                matches!(res, Err(BridgeError::InvalidFloatLiteral { .. })),
                format!("expected InvalidFloatLiteral, got {res:?} for:\n{ir}"),
            )
        }
    })
    .map_err(|e| format!("{e}"))
}

#[derive(Debug, Clone)]
struct FnSpec {
    linkage_idx: usize,
    has_section: bool,
    has_comdat: bool,
    align_shift: u32,
    use_mut_global: bool,
    use_const_lut: bool,
    inject_memcpy: bool,
    opt_salt: u32,
}

fn fn_spec_strategy() -> BoxedStrategy<FnSpec> {
    (
        0_usize..4_usize,
        any::<bool>(),
        any::<bool>(),
        2_u32..=5_u32,
        any::<bool>(),
        any::<bool>(),
        any::<bool>(),
        0_u32..100_000_u32,
    )
        .prop_map(
            |(
                linkage_idx,
                has_section,
                has_comdat,
                align_shift,
                use_mut_global,
                use_const_lut,
                inject_memcpy,
                opt_salt,
            )| FnSpec {
                linkage_idx,
                has_section,
                has_comdat,
                align_shift,
                use_mut_global,
                use_const_lut,
                inject_memcpy,
                opt_salt,
            },
        )
        .boxed()
}

type IdTable = BTreeMap<u32, String>;

fn parse_defined_attr_and_meta_tables(ir: &str) -> Result<(IdTable, IdTable), TestCaseError> {
    let mut attrs = BTreeMap::new();
    let mut metas = BTreeMap::new();

    for line in ir.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("attributes #")
            && let Some((id_str, rhs)) = rest.split_once('=')
        {
            let id = id_str
                .trim()
                .parse::<u32>()
                .map_err(|e| TestCaseError::fail(format!("bad attr id `{id_str}`: {e}")))?;
            prop_ensure(
                attrs.insert(id, rhs.trim().to_owned()).is_none(),
                format!("duplicate `attributes #{id}` in merged module"),
            )?;
        } else if let Some(rest) = trimmed.strip_prefix('!')
            && let Some((lhs, rhs)) = rest.split_once('=')
            && let Ok(id) = lhs.trim().parse::<u32>()
        {
            prop_ensure(
                metas.insert(id, rhs.trim().to_owned()).is_none(),
                format!("duplicate `!{id}` metadata definition in merged module"),
            )?;
        }
    }

    Ok((attrs, metas))
}

#[test]
fn prop_split_and_merge_structural_and_index_bijection_soundness() -> Result<(), String> {
    let mut tr = runner();
    let strat = (
        vec(fn_spec_strategy(), 2..=5),
        -1000_i32..=1000_i32,
        1_i32..=500_i32,
        0_usize..5_usize,
    );

    tr.run(&strat, |(specs, init_val, lut_val, drop_selector)| {
        let mut lines = vec![
            "source_filename = \"prop_mod.c\"".to_owned(),
            "target datalayout = \"e-m:e-i64:64-n32:64-S128\"".to_owned(),
            "target triple = \"aarch64-unknown-linux-gnu\"".to_owned(),
            "module asm \".ident \\22llvmcert-prop\\22\"".to_owned(),
            String::new(),
            "%struct.Leaf = type { i32 }".to_owned(),
            "%struct.Root = type { %struct.Leaf, ptr }".to_owned(),
            String::new(),
        ];

        for (idx, sp) in specs.iter().enumerate() {
            if sp.has_comdat {
                lines.push(format!("$cd_{idx} = comdat any"));
            }
        }
        lines.push(format!(
            "@mut_state = internal global i32 {init_val}, align 4"
        ));
        lines.push(format!(
            "@CONST_TABLE = private unnamed_addr constant [2 x i32] [i32 {lut_val}, i32 7], align 4"
        ));
        lines.push("declare i32 @ext_sensor(ptr nocapture readonly) #0".to_owned());
        lines.push(String::new());

        let linkages = ["internal", "private", "dso_local", "weak_odr"];
        for (idx, sp) in specs.iter().enumerate() {
            let link = linkages.get(sp.linkage_idx).copied().unwrap_or("internal");
            // Note: in LLVM IR, `private` symbols cannot belong to a comdat, so gate comdat on non-private:
            let use_cd = sp.has_comdat && link != "private";
            let sec_str = if sp.has_section {
                format!(" section \".text.f{idx}\"")
            } else {
                String::new()
            };
            let cd_str = if use_cd {
                format!(" comdat($cd_{idx})")
            } else {
                String::new()
            };
            let align_bytes = 1_u32 << sp.align_shift;
            let meta_id = u32::try_from(idx + 1).unwrap_or(1);

            lines.push(format!(
                "define {link} i32 @fn_{idx}(ptr %root, i32 %x) unnamed_addr{sec_str}{cd_str} align {align_bytes} #{idx} {{"
            ));
            lines.push("entry:".to_owned());
            lines.push("  %leaf_ptr = getelementptr inbounds %struct.Root, ptr %root, i64 0, i32 0".to_owned());
            let mut acc_var = "%x".to_owned();
            if sp.use_mut_global {
                lines.push(format!(
                    "  %g = load i32, ptr @mut_state, align 4, !tbaa !{meta_id}"
                ));
                lines.push(format!("  %acc_g = add i32 {acc_var}, %g"));
                acc_var = "%acc_g".to_owned();
            }
            if sp.use_const_lut {
                lines.push(
                    "  %lut_p = getelementptr inbounds [2 x i32], ptr @CONST_TABLE, i64 0, i64 0"
                        .to_owned(),
                );
                lines.push("  %lut_v = load i32, ptr %lut_p, align 4".to_owned());
                lines.push(format!("  %acc_c = add i32 {acc_var}, %lut_v"));
                acc_var = "%acc_c".to_owned();
            }
            if idx > 0 {
                let prev = idx - 1;
                lines.push(format!(
                    "  %sub_call = call i32 @fn_{prev}(ptr %root, i32 {acc_var})"
                ));
                acc_var = "%sub_call".to_owned();
            } else {
                lines.push("  %ext_v = call i32 @ext_sensor(ptr %leaf_ptr)".to_owned());
                lines.push(format!("  %acc_e = add i32 {acc_var}, %ext_v"));
                acc_var = "%acc_e".to_owned();
            }
            lines.push(format!("  ret i32 {acc_var}"));
            lines.push("}".to_owned());
            lines.push(String::new());
        }

        for idx in 0..specs.len() {
            lines.push(format!(
                "attributes #{idx} = {{ nounwind \"orig-fn\"=\"fn_{idx}\" }}"
            ));
        }
        lines.push("!llvm.module.flags = !{!0}".to_owned());
        lines.push("!0 = !{i32 1, !\"wchar_size\", i32 4}".to_owned());
        for idx in 0..specs.len() {
            let meta_id = idx + 1;
            lines.push(format!("!{meta_id} = !{{!\"orig_tbaa_{idx}\"}}"));
        }

        let module_ir = lines.join("\n");
        let split_plain = split_module(&module_ir)
            .map_err(|e| TestCaseError::fail(format!("split_module failed: {e}")))?;
        prop_ensure(
            split_plain.slices.len() == specs.len(),
            "split_module slice count mismatch",
        )?;

        let split = split_module_for_vellvm(&module_ir)
            .map_err(|e| TestCaseError::fail(format!("split_module_for_vellvm failed: {e}")))?;

        // Simulate independent `opt -O2` runs producing colliding `#0` and `!0` across slices:
        let mut verified_slices = BTreeMap::new();
        for (idx, sp) in specs.iter().enumerate() {
            let fn_name = format!("fn_{idx}");
            let orig_slice = split
                .slices
                .get(&fn_name)
                .ok_or_else(|| TestCaseError::fail(format!("missing slice `{fn_name}`")))?;

            // Soundness checks on isolated slice:
            prop_ensure(
                orig_slice.contains(&format!("define dso_local i32 @{fn_name}(")),
                format!("slice `{fn_name}` did not widen linkage to dso_local"),
            )?;
            prop_ensure(
                !orig_slice.contains("comdat("),
                format!("slice `{fn_name}` retained comdat"),
            )?;
            if sp.use_mut_global {
                prop_ensure(
                    orig_slice.contains("@mut_state = external global i32, align 4")
                        && !orig_slice.contains("@mut_state = internal global"),
                    format!("slice `{fn_name}` failed GlobalOpt mutable-global protection"),
                )?;
            }
            if sp.use_const_lut {
                prop_ensure(
                    orig_slice.contains("@CONST_TABLE = available_externally"),
                    format!("slice `{fn_name}` lost available_externally constant table"),
                )?;
            }
            // Transitive `%struct.Leaf` + `%struct.Root` closure must be present in every slice:
            prop_ensure(
                orig_slice.contains("%struct.Leaf = type { i32 }")
                    && orig_slice.contains("%struct.Root = type { %struct.Leaf, ptr }"),
                format!("slice `{fn_name}` missing transitive struct closure"),
            )?;

            let memcpy_decl = if sp.inject_memcpy {
                "declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly, ptr noalias readonly, i64, i1 immarg) #0\n"
            } else {
                ""
            };
            // Simulate aggressive `opt -O2` output:
            // - Synthesizes helper `declare` with colliding `#0` (`"opt-slice"`),
            // - Attaches `-O2`-inferred return/param/fn attributes (`range(...)`, `noalias`,
            //   `willreturn`, `mustprogress`, `memory(none)`) onto `define` (which F-19 MUST strip!),
            // - Attaches both benign `!prof !0` (preserved & remapped) and unverified `!tbaa !1` /
            //   `!alias.scope !2` / `!noalias !3` / `!invariant.load !{}` (which F-19 MUST strip!).
            let colliding_opt_slice = format!(
                "{memcpy_decl}\
declare void @ext_opt_helper_{idx}() #0
define dso_local noundef range(i32 0, 99) i32 @{fn_name}(ptr noalias nocapture nonnull readonly %0, i32 noundef %1) #1 {{
entry:
  %tmp = load i32, ptr %0, align 4, !tbaa !1, !alias.scope !2, !noalias !3, !invariant.load !{{}}
  %sum = add i32 %tmp, %1, !prof !0
  ret i32 %sum
}}
attributes #0 = {{ nounwind \"opt-slice\"=\"{fn_name}_{}\" }}
attributes #1 = {{ mustprogress nofree norecurse nosync nounwind willreturn memory(none) }}
!0 = !{{!\"branch_weights\", !\"{fn_name}_{}\"}}
!1 = !{{!\"unverified_tbaa_{fn_name}\"}}
!2 = !{{!\"unverified_scope_{fn_name}\"}}
!3 = !{{!\"unverified_noalias_{fn_name}\"}}
",
                sp.opt_salt, sp.opt_salt
            );
            verified_slices.insert(fn_name, colliding_opt_slice);
        }

        // 1. Fail-fast missing-slice check: omitting one manifest function MUST fail with MissingVerifiedSlice:
        let omitted_idx = drop_selector % specs.len();
        let omitted_name = format!("fn_{omitted_idx}");
        let mut incomplete = verified_slices.clone();
        incomplete.remove(&omitted_name);
        let missing_res = merge_module(&split.manifest, &incomplete);
        let missing_ok = matches!(
            &missing_res,
            Err(BridgeError::MissingVerifiedSlice { function_name }) if function_name == &omitted_name
        );
        prop_ensure(
            missing_ok,
            format!("expected MissingVerifiedSlice for `{omitted_name}`, got {missing_res:?}"),
        )?;

        // 2. Full merge soundness, F-19 attribute/metadata hygiene & collision-free `#N` / `!N` bijection:
        let merged = merge_module(&split.manifest, &verified_slices)
            .map_err(|e| TestCaseError::fail(format!("merge_module failed: {e}")))?;

        prop_ensure(
            merged.contains("source_filename = \"prop_mod.c\"")
                && merged.contains("module asm \".ident \\22llvmcert-prop\\22\"")
                && merged.contains(&format!("@mut_state = internal global i32 {init_val}, align 4")),
            "merged module lost header, module asm, or internal global initializer",
        )?;

        // F-19 invariants: `-O2`-inferred `define` header attrs & body alias metadata MUST NOT leak!
        prop_ensure(
            !merged.contains("willreturn")
                && !merged.contains("mustprogress")
                && !merged.contains("memory(none)")
                && !merged.contains("range(i32 0, 99)")
                && !merged.contains("!tbaa")
                && !merged.contains("!alias.scope")
                && !merged.contains("!noalias")
                && !merged.contains("!invariant.load")
                && !merged.contains("unverified_tbaa_"),
            format!("F-19 violation: unverified -O2 attributes or alias metadata leaked:\n{merged}"),
        )?;

        let (attr_table, meta_table) = parse_defined_attr_and_meta_tables(&merged)?;

        // Attribute IDs must be contiguous `0..attr_table.len()` with zero collisions:
        for expected_id in 0..u32::try_from(attr_table.len()).unwrap_or(0) {
            prop_ensure(
                attr_table.contains_key(&expected_id),
                format!("non-contiguous attribute group #{expected_id}"),
            )?;
        }

        let attr_values: BTreeSet<&str> = attr_table.values().map(String::as_str).collect();
        let meta_values: BTreeSet<&str> = meta_table.values().map(String::as_str).collect();

        for (idx, sp) in specs.iter().enumerate() {
            let fn_name = format!("fn_{idx}");
            let link = linkages.get(sp.linkage_idx).copied().unwrap_or("internal");
            // Sibling defined functions must NEVER be emitted as `declare ... @fn_k(`:
            prop_ensure(
                !merged.contains(&format!("@{fn_name}(ptr, i32)")),
                format!("defined function `@{fn_name}` leaked as nameless `declare` in merged module"),
            )?;
            // F-19: Original parameter types (`ptr %0, i32 %1`) restored without `-O2`'s `noalias`/`nonnull`:
            prop_ensure(
                merged.contains(&format!("define {link} i32 @{fn_name}(ptr %0, i32 %1)")),
                format!("original linkage/signature not restored on `@{fn_name}`:\n{merged}"),
            )?;
            if sp.has_section {
                prop_ensure(
                    merged.contains(&format!("section \".text.f{idx}\"")),
                    format!("section lost on `@{fn_name}`"),
                )?;
            }
            if sp.has_comdat && link != "private" {
                prop_ensure(
                    merged.contains(&format!("$cd_{idx} = comdat any"))
                        && merged.contains(&format!("comdat($cd_{idx})")),
                    format!("comdat lost on `@{fn_name}`"),
                )?;
            }

            let orig_attr_tag = format!("\"orig-fn\"=\"fn_{idx}\"");
            let expected_attr_tag = format!("\"opt-slice\"=\"{fn_name}_{}\"", sp.opt_salt);
            let expected_meta_tag = format!("!\"{fn_name}_{}\"", sp.opt_salt);
            prop_ensure(
                attr_values.iter().any(|v| v.contains(&orig_attr_tag)),
                format!("original function attribute group `{orig_attr_tag}` lost"),
            )?;
            prop_ensure(
                attr_values.iter().any(|v| v.contains(&expected_attr_tag)),
                format!("colliding slice #0 overwrote `{expected_attr_tag}`"),
            )?;
            prop_ensure(
                meta_values.iter().any(|v| v.contains(&expected_meta_tag)),
                format!("colliding slice !0 overwrote `{expected_meta_tag}`"),
            )?;
        }

        let memcpy_decl_count = merged
            .lines()
            .filter(|l| l.trim_start().starts_with("declare void @llvm.memcpy.p0.p0.i64("))
            .count();
        let any_memcpy = specs.iter().any(|s| s.inject_memcpy);
        prop_ensure(
            memcpy_decl_count == usize::from(any_memcpy),
            format!("expected at most 1 synthesized memcpy declare, got {memcpy_decl_count}"),
        )?;

        Ok(())
    })
    .map_err(|e| format!("{e}"))
}

#[test]
fn prop_check_fast_path_eligibility_precision() -> Result<(), String> {
    let mut tr = runner();
    let strat = (
        0_usize..26_usize,
        0_usize..5_usize,
        0_usize..8_usize,
        safe_ascii_word_strategy(),
    );

    tr.run(&strat, |(hazard_kind, fp_idx, fmf_idx, ident_suffix)| {
        let fp_tys = ["half", "bfloat", "fp128", "x86_fp80", "ppc_fp128"];
        let fmfs = [
            "nnan", "ninf", "nsz", "arcp", "contract", "afn", "reassoc", "fast",
        ];
        let fp_ty = fp_tys.get(fp_idx).copied().unwrap_or("half");
        let fmf = fmfs.get(fmf_idx).copied().unwrap_or("nnan");

        let hazard_stmt = match hazard_kind {
            0 => format!("  %h = fadd {fp_ty} undef, undef"),
            1 => format!("  %h = load <2 x {fp_ty}>, ptr %p, align 4"),
            2 => "  store half 0xH3C00, ptr %p, align 2".to_owned(),
            3 => "  store bfloat 0xR3F80, ptr %p, align 2".to_owned(),
            4 => "  store fp128 0xL00000000000000003FFF000000000000, ptr %p, align 16".to_owned(),
            5 => "  %h = icmp samesign ult ptr %p, %q".to_owned(),
            6 => "  %h = icmp samesign eq iptr %p, %q".to_owned(),
            7 => format!("  %h = select {fmf} i1 true, float 1.0, float 0.0"),
            8 => format!("  %h = call {fmf} float @safe_fp(float 1.0)"),
            9 => "  call void @llvm.assume(i1 true) [ \"align\"(ptr %p, i64 16) ]".to_owned(),
            10 => format!("  %h = fadd {fmf} float 1.0, 2.0"),
            11 => format!("  %h = fcmp {fmf} oeq float 1.0, 1.0"),
            12 => format!("  %h = fpext {fmf} float 1.0 to double"),
            13 => "  %h = load volatile i32, ptr %p, align 4".to_owned(),
            14 => "  %h = atomicrmw add ptr %p, i32 1 seq_cst, align 4".to_owned(),
            15 => "  fence seq_cst".to_owned(),
            16 => "  call void @llvm.memcpy.p0.p0.i64(ptr %p, ptr %q, i64 8, i1 true)".to_owned(),
            17 => "  call void @llvm.lifetime.start.p0(i64 4, ptr %p)".to_owned(),
            18 => "  %h = call ptr @llvm.stacksave.p0()".to_owned(),
            19 => "  call void @llvm.va_start.p0(ptr %p)".to_owned(),
            20 => "  %h = va_arg ptr %p, i32".to_owned(),
            21 => "  call void @byval_sink(ptr byval(i32) %p)".to_owned(),
            22 => "  %h = getelementptr inbounds inrange(0, 8) i8, ptr %p, i64 4".to_owned(),
            23 => "  %h = sitofp i64 4294967296 to float".to_owned(),
            24 => "  %h = uitofp i128 1 to double".to_owned(),
            25 => "  %h = frem float 1.0, 2.0".to_owned(),
            _ => "  call void asm sideeffect \"nop\", \"\"()".to_owned(),
        };

        let hazardous_ir = format!(
            "\
declare float @safe_fp(float)
declare void @byval_sink(ptr)
declare void @llvm.assume(i1)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)
declare void @llvm.lifetime.start.p0(i64 immarg, ptr nocapture)
declare ptr @llvm.stacksave.p0()
define i32 @haz_fn(ptr %p, ptr %q, i32 %x) {{
entry:
{hazard_stmt}
  ret i32 %x
}}
"
        );

        let haz_verdict = check_fast_path_eligibility(&hazardous_ir);
        prop_ensure(
            !haz_verdict.is_eligible(),
            format!("hazardous target IR was falsely marked Eligible:\n{hazardous_ir}"),
        )?;
        let haz_san = sanitize_for_vellvm(&hazardous_ir, SliceRole::TargetFastPath);
        prop_ensure(
            matches!(haz_san, Err(BridgeError::FastPathIneligible { .. })),
            format!("sanitize_for_vellvm(TargetFastPath) failed to reject:\n{hazardous_ir}"),
        )?;

        // Decoy IR: embeds every hazardous keyword inside `%local`, `@global`, `declare`, `type`,
        // `; comments`, and `"string literals"`, plus verified intrinsics (`@llvm.memcpy` with
        // `i1 false`, `@llvm.smax.i32`), safe `sitofp i32 -> float` / `uitofp i64 -> double`,
        // single-pair `range(i32 0, 100)`, and `nofpclass(ninf)`.
        prop_ensure(
            is_verified_vellvm_intrinsic("llvm.smax.i32")
                && is_verified_vellvm_intrinsic("@llvm.memcpy.p0.p0.i64")
                && !is_verified_vellvm_intrinsic("llvm.lifetime.start.p0"),
            "verified intrinsic catalog mismatch",
        )?;
        let decoy_ir = format!(
            "\
source_filename = \"half_bfloat_fp128_{ident_suffix}.c\"
target datalayout = \"e-m:e-p:64:64-i64:64-n32:64-S128\"
%struct.Decoy_{ident_suffix} = type {{ half, bfloat, fp128, x86_fp80, ppc_fp128 }}
@MSG_{ident_suffix} = private constant [56 x i8] c\"half bfloat fp128 icmp samesign ult ptr asm volatile...\\00\"
declare half @unused_fp_decl_{ident_suffix}(bfloat, fp128, x86_fp80, ppc_fp128)
declare i32 @{fp_ty}_helper_{ident_suffix}(i32)
declare float @nofp_callee_{ident_suffix}(float)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)
declare i32 @llvm.smax.i32(i32, i32)

define range(i32 0, 1000) i32 @eligible_fn_{ident_suffix}(ptr %dst, ptr %src, i32 %local_{fp_ty}, i32 %ppc_fp128_arg) #0 !dbg !4 {{
entry:
  ; comment with half bfloat fp128 frem volatile invoke byval inrange ...
  #dbg_value(i32 %local_{fp_ty}, !5, !DIExpression(), !6)
  call void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %src, i64 4, i1 false)
  %cmp_int = icmp samesign ult i32 %local_{fp_ty}, %ppc_fp128_arg
  %sel = select i1 %cmp_int, i32 %local_{fp_ty}, i32 0
  %ext = zext nneg i32 %sel to i64, !dbg !7
  %f32_ok = sitofp i32 %sel to float
  %nf = call nofpclass(ninf) float @nofp_callee_{ident_suffix}(float %f32_ok)
  %d64_ok = uitofp nneg i64 %ext to double
  %tr = trunc nuw nsw i64 %ext to i32
  %mx = call i32 @llvm.smax.i32(i32 %tr, i32 1)
  %res = call i32 @{fp_ty}_helper_{ident_suffix}(i32 %mx)
  ret i32 %res
}}
attributes #0 = {{ nounwind denormal_fpenv(ieee) }}
!llvm.dbg.cu = !{{!0}}
!4 = distinct !DISubprogram(name: \"half bfloat fp128\")
"
        );

        let decoy_verdict = check_fast_path_eligibility(&decoy_ir);
        prop_ensure(
            decoy_verdict == FastPathEligibility::Eligible,
            format!("decoy IR falsely rejected with {decoy_verdict:?}:\n{decoy_ir}"),
        )?;
        let decoy_san = sanitize_for_vellvm(&decoy_ir, SliceRole::TargetFastPath);
        prop_ensure(
            decoy_san.is_ok(),
            format!("sanitize_for_vellvm(TargetFastPath) rejected eligible decoy IR: {decoy_san:?}"),
        )?;

        Ok(())
    })
    .map_err(|e| format!("{e}"))
}

#[test]
fn prop_wp1_datalayout_non_splittable_tls_and_ctors_soundness() -> Result<(), String> {
    let mut tr = runner();
    let strat = (
        0_usize..4_usize,
        0_usize..4_usize,
        0_usize..3_usize,
        any::<bool>(),
        1_i32..=1000_i32,
        safe_ascii_word_strategy(),
    );

    tr.run(
        &strat,
        |(bad_dl_idx, tls_idx, non_split_kind, include_dtors, init_v, tag)| {
            let bad_dls = [
                "E-m:e-p:64:64-i64:64-S128",
                "e-m:e-p:32:32-i64:64-n32-S128",
                "e-m:e-p0:32:32-i64:64-S128",
                "e-m:e-p:64:32-i64:64-S128",
            ];
            let bad_dl = bad_dls.get(bad_dl_idx).copied().unwrap_or("E-p:64:64");
            prop_ensure(
                matches!(
                    validate_target_datalayout(bad_dl),
                    Err(BridgeError::UnsupportedDataLayout { .. })
                ),
                format!("expected UnsupportedDataLayout for `{bad_dl}`"),
            )?;

            let tls_clauses = [
                "thread_local",
                "thread_local(initialexec)",
                "thread_local(localexec)",
                "thread_local(localdynamic)",
            ];
            let tls_clause = tls_clauses.get(tls_idx).copied().unwrap_or("thread_local");

            let non_split_defs = match non_split_kind {
                0 => "\
define dso_local void @non_split_fn() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @ext_throw() to label %ok unwind label %lp
ok:
  ret void
lp:
  %e = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %e
}"
                .to_owned(),
                1 => "\
define dso_local ptr @non_split_fn() {
entry:
  ret ptr blockaddress(@block_target_fn, %lbl)
}

define dso_local i32 @block_target_fn() {
entry:
  br label %lbl
lbl:
  ret i32 9
}"
                .to_owned(),
                _ => "\
define dso_local ptr @non_split_fn() {
entry:
  ret ptr @gep_alias
}"
                .to_owned(),
            };

            let dtors_line = if include_dtors {
                "@llvm.global_dtors = appending global [1 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @splittable_fn, ptr null }]\n@llvm.compiler.used = appending global [1 x ptr] [ptr @splittable_fn], section \"llvm.metadata\"\n"
            } else {
                ""
            };

            let module_ir = format!(
                "\
source_filename = \"wp1_{tag}.c\"
target datalayout = \"e-m:e-p0:64:64-p270:32:32-i64:64-n32:64-S128\"
target triple = \"aarch64-unknown-none-elf\"

@base_arr = global [4 x i32] zeroinitializer, align 4
@gep_alias = alias i32, getelementptr inbounds ([4 x i32], ptr @base_arr, i64 0, i64 1)
@tls_state_{tag} = internal {tls_clause} global i32 {init_v}, align 4
@llvm.global_ctors = appending global [1 x {{ i32, ptr, ptr }}] [{{ i32, ptr, ptr }} {{ i32 65535, ptr @splittable_fn, ptr null }}]
@llvm.used = appending global [1 x ptr] [ptr @splittable_fn], section \"llvm.metadata\"
{dtors_line}
declare i32 @__gxx_personality_v0(...)
declare void @ext_throw()

define internal void @splittable_fn() #0 {{
entry:
  store i32 {init_v}, ptr @tls_state_{tag}, align 4
  ret void
}}

{non_split_defs}

attributes #0 = {{ nounwind }}
"
            );

            let split = split_module_for_vellvm(&module_ir)
                .map_err(|e| TestCaseError::fail(format!("split failed: {e}")))?;

            // `splittable_fn` MUST be isolated; `non_split_fn` (and `block_target_fn` if present) MUST NOT!
            prop_ensure(
                split.slices.len() == 1 && split.slices.contains_key("splittable_fn"),
                format!("expected only `splittable_fn` in slices, got {:?}", split.slices.keys()),
            )?;
            let sp_slice = split
                .slices
                .get("splittable_fn")
                .cloned()
                .unwrap_or_default();
            prop_ensure(
                sp_slice.contains(&format!(
                    "@tls_state_{tag} = external {tls_clause} global i32, align 4"
                )),
                format!("slice lost `{tls_clause}` on TLS global:\n{sp_slice}"),
            )?;
            prop_ensure(
                !sp_slice.contains("@llvm.global_ctors")
                    && !sp_slice.contains("@llvm.global_dtors")
                    && !sp_slice.contains("@llvm.used")
                    && !sp_slice.contains("@llvm.compiler.used"),
                format!("slice failed to elide module appending arrays:\n{sp_slice}"),
            )?;

            // Omitting `splittable_fn` still fails fast with `MissingVerifiedSlice`:
            let empty_map = BTreeMap::new();
            prop_ensure(
                matches!(
                    merge_module(&split.manifest, &empty_map),
                    Err(BridgeError::MissingVerifiedSlice { ref function_name })
                        if function_name == "splittable_fn"
                ),
                "expected MissingVerifiedSlice when `splittable_fn` is omitted",
            )?;

            // Providing ONLY `splittable_fn` merges cleanly without MissingVerifiedSlice on `non_split_fn`!
            let merged = merge_module(&split.manifest, &split.slices)
                .map_err(|e| TestCaseError::fail(format!("merge failed: {e}")))?;
            prop_ensure(
                merged.contains("@llvm.global_ctors = appending global")
                    && merged.contains("@llvm.used = appending global")
                    && merged.contains("define internal void @splittable_fn() #0 {")
                    && merged.contains("define dso_local ")
                    && merged.contains("@non_split_fn()"),
                format!("merged module lost ctors/used or non-splittable function:\n{merged}"),
            )?;

            Ok(())
        },
    )
    .map_err(|e| format!("{e}"))
}

fn adversarial_ir_soup_strategy() -> BoxedStrategy<String> {
    const FRAGMENTS: [&str; 28] = [
        "/* ",
        " */",
        "\"",
        "\\\"",
        "\\",
        ";",
        "\n",
        "%",
        "@",
        "$",
        "!",
        "#",
        "{",
        "}",
        "(",
        ")",
        "[",
        "]",
        "<",
        ">",
        "=",
        ",",
        ":",
        "f0x3DCCCCCD",
        "f0x123",
        "+inf",
        "-snan(0x1)",
        "define void @f() {",
    ];

    let token_soup = vec(0_usize..28_usize, 0..=32)
        .prop_map(|indices| {
            let mut out = String::new();
            for idx in indices {
                if let Some(&frag) = FRAGMENTS.get(idx) {
                    out.push_str(frag);
                }
            }
            out
        })
        .boxed();

    Union::new([any::<String>().boxed(), token_soup]).boxed()
}

#[test]
fn prop_arbitrary_utf8_and_token_soup_panic_freedom() -> Result<(), String> {
    let mut tr = runner();
    let strat = (adversarial_ir_soup_strategy(), vec(any::<u8>(), 0..=96));

    tr.run(&strat, |(text, raw_bytes)| {
        prop_ensure(
            verify_utf8_scanner_panic_freedom(text.as_bytes()),
            "verify_utf8_scanner_panic_freedom failed on UTF-8 string",
        )?;
        prop_ensure(
            verify_utf8_scanner_panic_freedom(&raw_bytes),
            "verify_utf8_scanner_panic_freedom failed on raw byte slice",
        )?;

        let _ = sanitize_for_vellvm(&text, SliceRole::Source);
        let _ = sanitize_for_vellvm(&text, SliceRole::TargetFastPath);
        let _ = split_module(&text);
        let _ = split_module_for_vellvm(&text);

        Ok(())
    })
    .map_err(|e| format!("{e}"))
}
