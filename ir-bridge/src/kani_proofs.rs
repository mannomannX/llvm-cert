//! Symbolic bounded model-checking harnesses (`cargo kani`) for `ir-bridge`.
//!
//! All core algebraic predicates live in [`crate::fp_literals`] so they are simultaneously
//! type-checked, Clippy-audited, and exercised by unit and `proptest` suites on every build.

use crate::{
    check_fast_path_eligibility, normalize_llvm23_fp_and_comments,
    verify_f32_f64_roundtrip_invariants, verify_f64_f32_exact_image_invariants,
};

/// Exhaustive $2^{32}$ bit-level symbolic proof that `f32_bits_to_f64_bits` is injective,
/// inverted by `f64_bits_to_f32_bits_exact`, preserves sign bits across `+-0.0` / finite / `+-inf` / NaN,
/// and preserves quiet/signaling NaN MSBs and 22-bit payloads without CPU `fcvt` silencing.
#[kani::proof]
fn proof_f32_to_f64_bijectivity_and_nan_bits() {
    let bits32: u32 = kani::any();
    kani::assert(
        verify_f32_f64_roundtrip_invariants(bits32),
        "f32 -> f64 -> f32 roundtrip must preserve exact bits, sign, and NaN signaling/payload bits",
    );
}

/// Exhaustive $2^{64}$ bit-level symbolic proof that `f64_bits_to_f32_bits_exact` accepts ONLY
/// binary64 bit patterns in the exact image of `f32_bits_to_f64_bits`.
#[kani::proof]
fn proof_f64_to_f32_exact_right_inverse() {
    let bits64: u64 = kani::any();
    kani::assert(
        verify_f64_f32_exact_image_invariants(bits64),
        "f64_bits_to_f32_bits_exact must reject every u64 outside the exact binary32 image",
    );
}

/// Bounded symbolic UTF-8 proof of panic, slice-bounds, and arithmetic-overflow freedom on
/// `normalize_llvm23_fp_and_comments`.
#[kani::proof]
#[kani::unwind(10)]
fn proof_normalize_fp_and_comments_panic_free() {
    let bytes: [u8; 8] = kani::any();
    if let Ok(ir) = std::str::from_utf8(&bytes) {
        let _ = normalize_llvm23_fp_and_comments(ir);
    }
}

/// Bounded symbolic UTF-8 proof of panic, slice-bounds, and arithmetic-overflow freedom on
/// `check_fast_path_eligibility`.
#[kani::proof]
#[kani::unwind(10)]
fn proof_check_fast_path_eligibility_panic_free() {
    let bytes: [u8; 8] = kani::any();
    if let Ok(ir) = std::str::from_utf8(&bytes) {
        let _ = check_fast_path_eligibility(ir);
    }
}
