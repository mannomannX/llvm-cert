//! High-assurance LLVM 23.1.5 <-> Vellvm 3.0 IR bridge, per-function module splitter/merger,
//! and Fast-Path soundness eligibility gate (`Phase 1.3`).

pub mod error;
pub mod fp_literals;
pub mod split_merge;
pub mod vellvm_sanitize;

pub use error::BridgeError;
pub use fp_literals::{FpScalarType, f32_bits_to_f64_bits, normalize_llvm23_fp_and_comments};
pub use split_merge::{
    DeclRecord, FunctionManifestEntry, GlobalRecord, ModuleManifest, SplitOutput, TypeDefRecord,
    merge_module, split_module, split_module_for_vellvm,
};
pub use vellvm_sanitize::{
    FastPathEligibility, SliceRole, check_fast_path_eligibility, sanitize_for_vellvm,
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
    fn test_fast_path_soundness_gate_catches_f08_and_bundle_hazards() {
        let unsafe_target = "\
define i64 @opt_fn(i32 %x, ptr %p, ptr %q) {
  call void @llvm.assume(i1 true) [ \"align\"(ptr %p, i64 16) ]
  %ext = zext nneg i32 %x to i64
  %cmp = icmp samesign ult ptr %p, %q
  ret i64 %ext
}
";
        let verdict = check_fast_path_eligibility(unsafe_target);
        assert!(!verdict.is_eligible());
        let err = sanitize_for_vellvm(unsafe_target, SliceRole::TargetFastPath);
        assert!(matches!(err, Err(BridgeError::FastPathIneligible { .. })));

        let safe_target = "\
define i32 @clean_add(i32 %x, i32 %y) !dbg !4 {
  #dbg_value(i32 %x, !5, !DIExpression(), !6)
  %sum = add nsw i32 %x, %y, !dbg !7
  ret i32 %sum
}
!llvm.dbg.cu = !{!0}
!4 = distinct !DISubprogram(name: \"clean_add\")
";
        assert!(check_fast_path_eligibility(safe_target).is_eligible());
        let clean = sanitize_for_vellvm(safe_target, SliceRole::TargetFastPath);
        assert!(clean.is_ok());
        let text = clean.unwrap_or_default();
        assert!(!text.contains("#dbg_value"));
        assert!(!text.contains("!dbg"));
        assert!(!text.contains("!DISubprogram"));
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
    }
}
