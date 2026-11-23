//! High-assurance LLVM 23.1.5 <-> Vellvm 3.0 IR bridge, per-function module splitter/merger,
//! and Fast-Path soundness eligibility gate (`Phase 1.3`).

pub mod error;
pub mod fp_literals;
#[cfg(kani)]
mod kani_proofs;
pub mod split_merge;
pub mod vellvm_sanitize;

pub use error::BridgeError;
pub use fp_literals::{
    FpScalarType, f32_bits_to_f64_bits, f64_bits_to_f32_bits_exact,
    normalize_llvm23_fp_and_comments, verify_f32_f64_roundtrip_invariants,
    verify_f64_f32_exact_image_invariants, verify_utf8_scanner_panic_freedom,
};
pub use split_merge::{
    DeclRecord, FunctionManifestEntry, GlobalRecord, ModuleManifest, SplitOutput, TypeDefRecord,
    align_slice_prototype, merge_module, split_module, split_module_for_vellvm,
    validate_target_datalayout,
};
pub use vellvm_sanitize::{
    FastPathEligibility, SliceRole, check_fast_path_eligibility, is_verified_vellvm_intrinsic,
    sanitize_for_vellvm,
};

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    #[test]
    fn test_f32_to_f64_bitwise_exact_ieee754() {
        // 0.1f32 = 0x3DCCCCCD -> exact binary64 0x3FB99999A0000000
        assert_eq!(f32_bits_to_f64_bits(0x3DCC_CCCD), 0x3FB9_9999_A000_0000);
        // Verify bit-for-bit agreement with IEEE-754 widening on finite, zero, subnormal, and inf values:
        for bits in [
            0x0000_0000_u32,
            0x8000_0000,
            0x0000_0001,
            0x007F_FFFF,
            0x3DCC_CCCD,
            0x3DCD_6500,
            0x7F80_0000,
            0xFF80_0000,
        ] {
            assert_eq!(
                f32_bits_to_f64_bits(bits),
                f64::from(f32::from_bits(bits)).to_bits()
            );
        }
        // Signaling NaN preserves quiet=0 bit and exact shifted payload (unlike CPU fcvt!)
        assert_eq!(f32_bits_to_f64_bits(0x7F80_0001), 0x7FF0_0000_2000_0000);
    }

    #[test]
    fn test_f64_to_f32_exact_inverse_and_shared_kani_kernels() {
        const POS_ZERO_RT: Option<u32> = f64_bits_to_f32_bits_exact(0x0000_0000_0000_0000);
        const NEG_ZERO_RT: Option<u32> = f64_bits_to_f32_bits_exact(0x8000_0000_0000_0000);
        assert_eq!(POS_ZERO_RT, Some(0x0000_0000));
        assert_eq!(NEG_ZERO_RT, Some(0x8000_0000));

        for bits32 in [
            0x0000_0000_u32,
            0x8000_0000,
            0x0000_0001, // min subnormal -> exp64 = 874
            0x8000_0001,
            0x007F_FFFF, // max subnormal -> exp64 = 896
            0x0080_0000, // min normal    -> exp64 = 897
            0x3DCC_CCCD,
            0x7F7F_FFFF, // max normal    -> exp64 = 1150
            0x7F80_0000, // +inf
            0xFF80_0000, // -inf
            0x7F80_0001, // +snan(0x1)
            0xFFBF_FFFF, // -snan(max payload)
            0x7FC0_0000, // +qnan
            0xFFFF_FFFF, // -qnan(max payload)
        ] {
            assert!(verify_f32_f64_roundtrip_invariants(bits32));
        }

        // Exact-image boundary rejections (`None` for out-of-image f64 bit patterns):
        for non_f32_bits64 in [
            0x0000_0000_0000_0001_u64,       // f64 subnormal
            873_u64 << 52,                   // 2^-150 (half of min f32 subnormal)
            (874_u64 << 52) | (1_u64 << 51), // 1.5 * 2^-149 (inexact subnormal mantissa)
            0x3FB9_9999_9999_999A,           // 0.1f64 (non-zero low 29 mantissa bits)
            1151_u64 << 52,                  // 2^128 (overflows finite f32)
            0x7FF0_0000_0000_0001,           // f64 sNaN with payload only in low 29 bits
        ] {
            assert_eq!(f64_bits_to_f32_bits_exact(non_f32_bits64), None);
            assert!(verify_f64_f32_exact_image_invariants(non_f32_bits64));
        }

        assert!(verify_utf8_scanner_panic_freedom(
            b"float f0x3DCCCCCD /* c */"
        ));
    }

    #[test]
    fn test_llvm23_fp_literals_and_immarg_comments_normalized() {
        let llvm23_ir = "\
define float @fp_demo(float %x) {
entry:
  %a = fadd float %x, f0x3DCCCCCD
  %b = fcmp oeq float %a, +inf
  %c = select i1 %b, float -qnan, float +snan(0x1)
  %cls = call i1 @llvm.is.fpclass.f32(float %c, i32 /* immarg */ 516)
  %h = fadd half f0x3C00, -inf
  %d = fadd double f0x3FF0000000000000, +nan(0xabc)
  ret float %c
}
";
        let res = normalize_llvm23_fp_and_comments(llvm23_ir);
        assert!(res.is_ok());
        let norm = res.unwrap_or_default();
        assert!(norm.contains("%a = fadd float %x, 0x3FB99999A0000000"));
        assert!(norm.contains("%b = fcmp oeq float %a, 0x7FF0000000000000"));
        assert!(
            norm.contains("%c = select i1 %b, float 0xFFF8000000000000, float 0x7FF0000020000000")
        );
        assert!(!norm.contains("/*"));
        assert!(norm.contains("i32   516)"));
        assert!(norm.contains("%h = fadd half 0xH3C00, 0xHFC00"));
        assert!(norm.contains("%d = fadd double 0x3FF0000000000000, 0x7FF8000000000ABC"));
    }

    #[test]
    fn test_fast_path_soundness_gate_catches_f15_and_unlocks_f08_conversions() {
        let unsafe_target = "\
define i1 @opt_ptr(ptr %p, ptr %q) {
  call void @llvm.assume(i1 true) [ \"align\"(ptr %p, i64 16) ]
  %cmp = icmp samesign ult ptr %p, %q
  ret i1 %cmp
}
";
        let verdict = check_fast_path_eligibility(unsafe_target);
        assert!(!verdict.is_eligible());
        let err = sanitize_for_vellvm(unsafe_target, SliceRole::TargetFastPath);
        assert!(matches!(err, Err(BridgeError::FastPathIneligible { .. })));

        let safe_target = "\
define double @clean_conv(i32 %x, i32 %y) !dbg !4 {
  #dbg_value(i32 %x, !5, !DIExpression(), !6)
  %ext = zext nneg i32 %x to i64, !dbg !7
  %tr = trunc nuw nsw i64 %ext to i32
  %cmp = icmp samesign ult i32 %tr, %y
  %sel = select i1 %cmp, i32 %tr, i32 0
  %fp = uitofp nneg i32 %sel to double
  ret double %fp
}
!llvm.dbg.cu = !{!0}
!4 = distinct !DISubprogram(name: \"clean_conv\")
";
        assert!(check_fast_path_eligibility(safe_target).is_eligible());
        let clean = sanitize_for_vellvm(safe_target, SliceRole::TargetFastPath);
        assert!(clean.is_ok());
        let text = clean.unwrap_or_default();
        assert!(!text.contains("#dbg_value"));
        assert!(!text.contains("!dbg"));
        assert!(!text.contains("!DISubprogram"));
        assert!(text.contains("zext nneg i32 %x to i64"));
        assert!(text.contains("trunc nuw nsw i64 %ext to i32"));
        assert!(text.contains("uitofp nneg i32 %sel to double"));
    }

    #[test]
    fn test_half_value_ops_route_to_safe_path_without_false_positives() {
        let half_slice = "\
define half @fp16_step(half %x) {
entry:
  %y = fadd half %x, f0x3C00
  ret half %y
}
";
        assert!(!check_fast_path_eligibility(half_slice).is_eligible());
        assert!(matches!(
            sanitize_for_vellvm(half_slice, SliceRole::TargetFastPath),
            Err(BridgeError::FastPathIneligible { .. })
        ));
        // Source role still normalizes `f0x3C00` -> `0xH3C00` cleanly without rejecting:
        let source_norm = sanitize_for_vellvm(half_slice, SliceRole::Source);
        assert!(source_norm.is_ok());
        assert!(
            source_norm
                .unwrap_or_default()
                .contains("%y = fadd half %x, 0xH3C00")
        );

        let fast_eligible_slice = "\
declare i32 @half_fn(i32)

define i32 @int_step(i32 %a, i32 %half_val) {
entry:
  %half_width = add i32 %a, 1
  %called = call i32 @half_fn(i32 %half_val)
  %out = add i32 %half_width, %called
  ret i32 %out
}
";
        assert!(check_fast_path_eligibility(fast_eligible_slice).is_eligible());
        assert!(sanitize_for_vellvm(fast_eligible_slice, SliceRole::TargetFastPath).is_ok());
    }

    #[test]
    fn test_split_and_merge_preserves_soundness_and_reindexes_cleanly() {
        let module_ir = "\
source_filename = \"sensor.c\"
target datalayout = \"e-m:e-p270:32:32-p271:32:32-i64:64-n32:64-S128\"
target triple = \"aarch64-unknown-linux-gnu\"
module asm \".ident \\\"sensor\\\"\"

%struct.Inner = type { i32 }
%struct.Outer = type { %struct.Inner, ptr }

$grp = comdat any

@mutable_state = internal global i32 0, align 4
@SCALE_LUT = private unnamed_addr constant [2 x i32] [i32 10, i32 20], align 4

declare !dbg !9 i32 @ext_read(ptr nocapture readonly) #0

define internal noundef i32 @helper(ptr nocapture readonly %s, i32 noundef %idx) unnamed_addr section \".text.fast\" comdat($grp) align 4 #0 !dbg !10 {
entry:
  %st = load i32, ptr @mutable_state, align 4, !tbaa !1
  %gep = getelementptr inbounds [2 x i32], ptr @SCALE_LUT, i64 0, i32 %idx
  %lut = load i32, ptr %gep, align 4
  %sum = add nsw i32 %st, %lut
  ret i32 %sum
}

define dso_local i32 @entry_point(ptr %outer) #1 {
entry:
  %f0 = getelementptr inbounds %struct.Outer, ptr %outer, i64 0, i32 0
  %raw = call i32 @ext_read(ptr %f0)
  %res = call i32 @helper(ptr %f0, i32 %raw)
  store i32 %res, ptr @mutable_state, align 4
  ret i32 %res
}

attributes #0 = { nofree norecurse nosync nounwind memory(read) denormal_fpenv(ieee) }
attributes #1 = { nounwind }

!llvm.module.flags = !{!0}
!0 = !{i32 1, !\"wchar_size\", i32 4}
!1 = !{!2, !2, i64 0}
!2 = !{!\"int\", !3, i64 0}
!3 = !{!\"omnipotent char\"}
";

        let split = split_module_for_vellvm(module_ir);
        assert!(split.is_ok());
        let split = split.unwrap_or_else(|_| SplitOutput {
            manifest: ModuleManifest {
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
            },
            slices: BTreeMap::new(),
        });

        let helper_slice = split.slices.get("helper").cloned().unwrap_or_default();
        // 1. GlobalOpt trap check: mutable `@mutable_state` MUST be `external global i32`, NOT `internal global i32 0`!
        assert!(helper_slice.contains("@mutable_state = external global i32, align 4"));
        assert!(!helper_slice.contains("@mutable_state = internal global i32 0"));
        // 2. Read-only constant table preserved as `available_externally`:
        assert!(helper_slice.contains(
            "@SCALE_LUT = available_externally unnamed_addr constant [2 x i32] [i32 10, i32 20], align 4"
        ));
        // 3. GlobalDCE trap check: `internal` widened to `dso_local` and `$grp` comdat stripped in slice:
        assert!(helper_slice.contains("define dso_local noundef i32 @helper("));
        assert!(!helper_slice.contains("comdat"));
        assert!(!helper_slice.contains("denormal_fpenv"));

        let entry_slice = split.slices.get("entry_point").cloned().unwrap_or_default();
        // 4. Transitive `%struct.Inner` + `%struct.Outer` both present (prevents Vellvm DTYPE_Void bug!):
        assert!(entry_slice.contains("%struct.Inner = type { i32 }"));
        assert!(entry_slice.contains("%struct.Outer = type { %struct.Inner, ptr }"));
        // 5. Sibling `@helper` emitted as nameless `declare` preserving param & return attrs:
        assert!(
            entry_slice
                .contains("declare noundef i32 @helper(ptr nocapture readonly, i32 noundef) #0")
        );

        // Simulate `opt -O2` introducing a new intrinsic `@llvm.memcpy.p0.p0.i64` and its own `#0` / `!0` IDs:
        let opt_entry_slice = format!(
            "{entry_slice}\ndeclare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly, ptr noalias readonly, i64, i1 immarg) #2\nattributes #2 = {{ nocallback nofree nounwind willreturn memory(argmem: readwrite) }}\n!0 = !{{!\"loop_unroll\"}}\n"
        );
        let mut verified = BTreeMap::new();
        verified.insert("helper".to_owned(), helper_slice);
        verified.insert("entry_point".to_owned(), opt_entry_slice);

        let merged = merge_module(&split.manifest, &verified);
        assert!(merged.is_ok());
        let merged = merged.unwrap_or_default();

        // Original globals, comdat, module asm, and `internal` linkage + section + comdat on `@helper` restored!
        assert!(merged.contains("module asm \".ident \\\"sensor\\\"\""));
        assert!(merged.contains("$grp = comdat any"));
        assert!(merged.contains("@mutable_state = internal global i32 0, align 4"));
        assert!(merged.contains(
            "define internal noundef i32 @helper(ptr nocapture readonly %s, i32 noundef %idx) unnamed_addr section \".text.fast\" comdat($grp) align 4 #"
        ));
        // Synthesized `@llvm.memcpy` declaration included without duplicating sibling `@helper` as declare!
        assert!(merged.contains("declare void @llvm.memcpy.p0.p0.i64("));
        assert!(!merged.contains("declare noundef i32 @helper("));
        // F-19: Unverified `-O2` `!tbaa` metadata stripped from merged function body!
        assert!(!merged.contains("!tbaa"));
    }

    #[test]
    fn test_wp1_f19_strips_inferred_attrs_and_alias_metadata_on_merge() {
        let input_ir = "\
source_filename = \"f19.c\"
target datalayout = \"e-m:e-p:64:64-i64:64-n32:64-S128\"
target triple = \"aarch64-unknown-none-elf\"

define dso_local i32 @sensor_step(ptr %buf, i32 %n) #0 {
entry:
  %v = load i32, ptr %buf, align 4
  %s = add i32 %v, %n
  ret i32 %s
}

attributes #0 = { nounwind }
";
        let split = split_module_for_vellvm(input_ir);
        assert!(split.is_ok());
        let split = split.unwrap_or_else(|_| SplitOutput {
            manifest: ModuleManifest {
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
            },
            slices: BTreeMap::new(),
        });

        // Simulate aggressive `opt -O2` inferring unverified return/param/fn attrs + alias metadata:
        let opt_fast_slice = "\
define dso_local noundef range(i32 0, 256) i32 @sensor_step(ptr noalias nocapture nonnull readonly dereferenceable(4) %0, i32 noundef %1) local_unnamed_addr #0 {
entry:
  %v = load i32, ptr %0, align 4, !tbaa !0, !alias.scope !3, !noalias !4, !invariant.load !{}
  %s = add nsw i32 %v, %1, !prof !5
  ret i32 %s
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: read) }
!0 = !{!1, !1, i64 0}
!1 = !{!\"int\", !2, i64 0}
!2 = !{!\"omnipotent char\"}
!3 = !{!\"scope\"}
!4 = !{!\"noalias_scope\"}
!5 = !{!\"branch_weights\", i32 16}
";
        let mut verified = BTreeMap::new();
        verified.insert("sensor_step".to_owned(), opt_fast_slice.to_owned());
        let merged = merge_module(&split.manifest, &verified).unwrap_or_default();

        // Original `input.ll` signature & `#0` (`{ nounwind }`) restored with `%0, %1` SSA names:
        assert!(merged.contains("define dso_local i32 @sensor_step(ptr %0, i32 %1) #0 {"));
        assert!(!merged.contains("willreturn"));
        assert!(!merged.contains("mustprogress"));
        assert!(!merged.contains("memory("));
        assert!(!merged.contains("dereferenceable"));
        assert!(!merged.contains("local_unnamed_addr"));
        assert!(!merged.contains("!tbaa"));
        assert!(!merged.contains("!alias.scope"));
        assert!(!merged.contains("!noalias"));
        assert!(!merged.contains("!invariant.load"));
        assert!(!merged.contains("omnipotent char"));
        // Benign non-alias `!prof` metadata preserved and remapped:
        assert!(merged.contains("!prof !0"));
    }

    #[test]
    fn test_wp1_f22_datalayout_and_f24_f33_f34_non_splittable_passthrough() {
        // F-22: Reject big-endian and 32-bit pointer layouts fail-fast:
        for bad_dl in [
            "target datalayout = \"E-m:e-p:64:64-i64:64-S128\"",
            "target datalayout = \"e-m:e-p:32:32-i64:64-n32-S128\"",
            "target datalayout = \"e-m:e-p0:32:32-i64:64-S128\"",
            "target datalayout = \"m:e-i64:64-S128\"",
        ] {
            let ir = format!("{bad_dl}\ndefine void @f() {{\n  ret void\n}}\n");
            assert!(matches!(
                split_module(&ir),
                Err(BridgeError::UnsupportedDataLayout { .. })
            ));
            assert!(matches!(
                sanitize_for_vellvm(&ir, SliceRole::Source),
                Err(BridgeError::UnsupportedDataLayout { .. })
            ));
        }
        assert!(validate_target_datalayout("e-m:e-p0:64:64-p270:32:32-i64:64-S128").is_ok());

        // F-24, F-33, F-34: `thread_local`, `@llvm.global_ctors`/`@llvm.used` elision, `extern_weak`,
        // `invoke`, and cross-function `blockaddress` non-splittable pass-through!
        let complex_mod = "\
source_filename = \"runtime_init.c\"
target datalayout = \"e-m:e-p:64:64-i64:64-n32:64-S128\"
target triple = \"riscv64-unknown-none-elf\"

@tls_errno = internal thread_local(initialexec) global i32 0, align 4
@weak_board_id = extern_weak global i32, align 4
@llvm.global_ctors = appending global [1 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @pure_worker, ptr null }]
@llvm.used = appending global [1 x ptr] [ptr @pure_worker], section \"llvm.metadata\"

declare extern_weak i32 @opt_probe()
declare i32 @__gxx_personality_v0(...)
declare void @callee_may_throw()

define dso_local void @pure_worker() #0 {
entry:
  store i32 1, ptr @tls_errno, align 4
  %w = load i32, ptr @weak_board_id, align 4
  %p = call i32 @opt_probe()
  ret void
}

define dso_local void @eh_runner() personality ptr @__gxx_personality_v0 {
entry:
  invoke void @callee_may_throw() to label %cont unwind label %lpad
cont:
  ret void
lpad:
  %lp = landingpad { ptr, i32 } cleanup
  resume { ptr, i32 } %lp
}

define dso_local ptr @addr_taker() {
entry:
  ret ptr blockaddress(@label_owner, %target_bb)
}

define dso_local i32 @label_owner() {
entry:
  br label %target_bb
target_bb:
  ret i32 42
}

attributes #0 = { nounwind }
";
        let split = split_module_for_vellvm(complex_mod).expect_or_panic_free();
        // Only `@pure_worker` is splittable; `@eh_runner`, `@addr_taker`, and `@label_owner` are non-splittable!
        assert_eq!(split.slices.len(), 1);
        let worker_slice = split.slices.get("pure_worker").cloned().unwrap_or_default();
        assert!(
            worker_slice
                .contains("@tls_errno = external thread_local(initialexec) global i32, align 4")
        );
        assert!(worker_slice.contains("@weak_board_id = extern_weak global i32, align 4"));
        assert!(worker_slice.contains("declare extern_weak i32 @opt_probe()"));
        assert!(!worker_slice.contains("@llvm.global_ctors"));
        assert!(!worker_slice.contains("@llvm.used"));

        // Merging with ONLY `pure_worker` in `verified_slices` succeeds cleanly via F-24 pass-through!
        let merged = merge_module(&split.manifest, &split.slices).unwrap_or_default();
        assert!(merged.contains("@llvm.global_ctors = appending global"));
        assert!(merged.contains("@llvm.used = appending global"));
        assert!(merged.contains("define dso_local void @eh_runner()"));
        assert!(merged.contains("define dso_local ptr @addr_taker()"));
        assert!(merged.contains("define dso_local i32 @label_owner()"));
    }

    #[test]
    fn align_slice_prototype_restores_safe_and_o2_contract() {
        let src_safe = r#"target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i64 @pack_sensor_u64(i32 %_llv_a0, i32 %_llv_a1) noinline nounwind {
entry:
  %hi = zext i32 %_llv_a0 to i64
  %sh = shl nuw i64 %hi, 32
  %lo = zext i32 %_llv_a1 to i64
  %r = or disjoint i64 %sh, %lo
  ret i64 %r
}
"#;
        let tgt_o2 = r#"target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

declare i32 @llvm.smin.i32(i32, i32) #1

define dso_local noundef i64 @pack_sensor_u64(i32 noundef %0, i32 noundef %1) local_unnamed_addr #0 {
entry:
  %hi = zext i32 %0 to i64
  %sh = shl nuw i64 %hi, 32
  %lo = zext i32 %1 to i64
  %r = or disjoint i64 %sh, %lo
  ret i64 %r
}

attributes #0 = { mustprogress nofree norecurse nosync willreturn memory(none) "target-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
"#;
        let aligned = align_slice_prototype(src_safe, tgt_o2).unwrap_or_default();
        assert!(
            aligned.contains(
                "define dso_local i64 @pack_sensor_u64(i32 %0, i32 %1) noinline nounwind {"
            )
        );
        assert!(!aligned.contains("local_unnamed_addr"));
        assert!(!aligned.contains("memory(none)\n"));
        assert!(!aligned.contains("mustprogress"));
        assert!(!aligned.contains("noundef"));
        assert!(aligned.contains("declare i32 @llvm.smin.i32(i32, i32)"));
        assert!(aligned.contains("%sh = shl nuw i64 %hi, 32"));

        let src_attrs = r#"target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"

define i32 @helper_scale_i32(i32 noundef %a) #0 {
entry:
  ret i32 %a
}

attributes #0 = { noinline nounwind optnone }
"#;
        let tgt_stripped = r#"target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"

define noundef i32 @helper_scale_i32(i32 noundef %0) local_unnamed_addr #0 {
entry:
  ret i32 %0
}

attributes #0 = { mustprogress nofree norecurse nosync willreturn memory(none) }
"#;
        let aligned_attrs = align_slice_prototype(src_attrs, tgt_stripped).unwrap_or_default();
        assert!(aligned_attrs.contains("define i32 @helper_scale_i32(i32 noundef %0) #0 {"));
        assert!(aligned_attrs.contains("attributes #0 = { noinline nounwind optnone }"));
        assert!(!aligned_attrs.contains("willreturn"));

        let wrong_fn = tgt_stripped.replace("@helper_scale_i32", "@other_fn");
        assert!(align_slice_prototype(src_attrs, &wrong_fn).is_err());

        let multi_src = format!("{src_safe}\n{src_attrs}");
        assert!(align_slice_prototype(&multi_src, tgt_o2).is_err());
    }

    trait ResultTestExt<T> {
        fn expect_or_panic_free(self) -> T;
    }

    impl ResultTestExt<SplitOutput> for Result<SplitOutput, BridgeError> {
        fn expect_or_panic_free(self) -> SplitOutput {
            assert!(self.is_ok());
            self.unwrap_or_else(|_| SplitOutput {
                manifest: ModuleManifest {
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
                },
                slices: BTreeMap::new(),
            })
        }
    }
}
