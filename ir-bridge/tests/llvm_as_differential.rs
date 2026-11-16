//! Differential `llvm-as` oracle and canonical `0x<hex>` equivalence gate (`Phase 2.3b`).
//!
//! Policy:
//! - Always verifies canonical equivalence between LLVM 23 `f0x<hex>` / `+-inf` / `+-s?nan(...)` /
//!   `/* ... */` surface syntax and explicit LLVM `0x<hex>` baseline IR accepted by Vellvm 3.0.
//! - When `LLVM_AS_BIN` is configured in the environment, **fails fast** on any missing binary,
//!   spawn failure, or non-zero exit code, and proves that `llvm-as` assembles both the original
//!   LLVM 23 IR and `normalize_llvm23_fp_and_comments` output to **bit-for-bit identical bitcode**
//!   (and identical `llvm-dis` disassembly when `LLVM_DIS_BIN` is also set).

use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use ir_bridge::{merge_module, normalize_llvm23_fp_and_comments, split_module_for_vellvm};

struct DifferentialCase {
    name: &'static str,
    exact_whitespace_match: bool,
    llvm23_ir: &'static str,
    baseline_0x_ir: &'static str,
}

const DIFFERENTIAL_CORPUS: &[DifferentialCase] = &[
    DifferentialCase {
        name: "f32_ieee754_extremes_subnormals_and_snan",
        exact_whitespace_match: true,
        llvm23_ir: "\
source_filename = \"f32_oracle.ll\"

define float @f32_all_classes(float %x) {
entry:
  %z0 = fadd float %x, f0x00000000
  %z1 = fadd float %z0, f0x80000000
  %sub_min = fadd float %z1, f0x00000001
  %sub_max = fadd float %sub_min, f0x007FFFFF
  %norm_tenth = fadd float %sub_max, f0x3DCCCCCD
  %norm_max = fadd float %norm_tenth, f0x7F7FFFFF
  %pinf = fadd float %norm_max, +inf
  %ninf = fadd float %pinf, -inf
  %pqnan = fadd float %ninf, +qnan
  %nqnan = fadd float %pqnan, -qnan
  %qpay = fadd float %nqnan, +nan(0x12345)
  %spay = fadd float %qpay, -snan(0x1)
  ret float %spay
}
",
        baseline_0x_ir: "\
source_filename = \"f32_oracle.ll\"

define float @f32_all_classes(float %x) {
entry:
  %z0 = fadd float %x, 0x0000000000000000
  %z1 = fadd float %z0, 0x8000000000000000
  %sub_min = fadd float %z1, 0x36A0000000000000
  %sub_max = fadd float %sub_min, 0x380FFFFFC0000000
  %norm_tenth = fadd float %sub_max, 0x3FB99999A0000000
  %norm_max = fadd float %norm_tenth, 0x47EFFFFFE0000000
  %pinf = fadd float %norm_max, 0x7FF0000000000000
  %ninf = fadd float %pinf, 0xFFF0000000000000
  %pqnan = fadd float %ninf, 0x7FF8000000000000
  %nqnan = fadd float %pqnan, 0xFFF8000000000000
  %qpay = fadd float %nqnan, 0x7FF82468A0000000
  %spay = fadd float %qpay, 0xFFF0000020000000
  ret float %spay
}
",
    },
    DifferentialCase {
        name: "f64_half_bfloat_and_fp128_word_order",
        exact_whitespace_match: true,
        llvm23_ir: "\
source_filename = \"multi_fp_oracle.ll\"

define double @f64_ops(double %d) {
entry:
  %d0 = fadd double %d, f0x8000000000000000
  %d1 = fadd double %d0, f0x3FB999999999999A
  %d2 = fadd double %d1, +inf
  %d3 = fadd double %d2, -qnan
  %d4 = fadd double %d3, +nan(0xabcde)
  %d5 = fadd double %d4, -snan(0x1)
  ret double %d5
}

define half @f16_ops(half %h) {
entry:
  %h0 = fadd half %h, f0x3C00
  %h1 = fadd half %h0, -inf
  %h2 = fadd half %h1, +qnan
  %h3 = fadd half %h2, +snan(0x1)
  ret half %h3
}

define bfloat @bf16_ops(bfloat %b) {
entry:
  %b0 = fadd bfloat %b, f0x3F80
  %b1 = fadd bfloat %b0, +inf
  %b2 = fadd bfloat %b1, -qnan
  %b3 = fadd bfloat %b2, +snan(0x1)
  ret bfloat %b3
}

define fp128 @fp128_ops(fp128 %q) {
entry:
  %q0 = fadd fp128 %q, f0x3FFF0000000000000000000000000001
  %q1 = fadd fp128 %q0, +inf
  %q2 = fadd fp128 %q1, -qnan
  %q3 = fadd fp128 %q2, +snan(0x1)
  ret fp128 %q3
}
",
        baseline_0x_ir: "\
source_filename = \"multi_fp_oracle.ll\"

define double @f64_ops(double %d) {
entry:
  %d0 = fadd double %d, 0x8000000000000000
  %d1 = fadd double %d0, 0x3FB999999999999A
  %d2 = fadd double %d1, 0x7FF0000000000000
  %d3 = fadd double %d2, 0xFFF8000000000000
  %d4 = fadd double %d3, 0x7FF80000000ABCDE
  %d5 = fadd double %d4, 0xFFF0000000000001
  ret double %d5
}

define half @f16_ops(half %h) {
entry:
  %h0 = fadd half %h, 0xH3C00
  %h1 = fadd half %h0, 0xHFC00
  %h2 = fadd half %h1, 0xH7E00
  %h3 = fadd half %h2, 0xH7C01
  ret half %h3
}

define bfloat @bf16_ops(bfloat %b) {
entry:
  %b0 = fadd bfloat %b, 0xR3F80
  %b1 = fadd bfloat %b0, 0xR7F80
  %b2 = fadd bfloat %b1, 0xRFFC0
  %b3 = fadd bfloat %b2, 0xR7F81
  ret bfloat %b3
}

define fp128 @fp128_ops(fp128 %q) {
entry:
  %q0 = fadd fp128 %q, 0xL00000000000000013FFF000000000000
  %q1 = fadd fp128 %q0, 0xL00000000000000007FFF000000000000
  %q2 = fadd fp128 %q1, 0xL0000000000000000FFFF800000000000
  %q3 = fadd fp128 %q2, 0xL00000000000000017FFF000000000000
  ret fp128 %q3
}
",
    },
    DifferentialCase {
        name: "inline_immarg_comments_and_quoted_string_literals",
        exact_whitespace_match: false,
        llvm23_ir: "\
source_filename = \"comments_oracle.ll\"

@RAW_STR = private unnamed_addr constant [37 x i8] c\"/* keep */ f0x3DCCCCCD +inf -qnan \\22\\00\", align 1

declare i1 @llvm.is.fpclass.f32(float, i32)

define i1 @classify_fp(float %f0x12345678) {
entry:
  %v = /* block comment */ fadd float %f0x12345678, f0x3DCCCCCD
  %ok = call i1 @llvm.is.fpclass.f32(float %v, i32 /* immarg */ 516)
  ret i1 %ok
}
",
        baseline_0x_ir: "\
source_filename = \"comments_oracle.ll\"

@RAW_STR = private unnamed_addr constant [37 x i8] c\"/* keep */ f0x3DCCCCCD +inf -qnan \\22\\00\", align 1

declare i1 @llvm.is.fpclass.f32(float, i32)

define i1 @classify_fp(float %f0x12345678) {
entry:
  %v = fadd float %f0x12345678, 0x3FB99999A0000000
  %ok = call i1 @llvm.is.fpclass.f32(float %v, i32 516)
  ret i1 %ok
}
",
    },
];

struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(prefix: &str) -> Result<Self, String> {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let path = env::temp_dir().join(format!("llvmcert_{prefix}_{pid}_{nanos}"));
        fs::create_dir_all(&path)
            .map_err(|e| format!("failed to create temp dir `{}`: {e}", path.display()))?;
        Ok(Self { path })
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn collapse_spaces_outside_quotes(ir: &str) -> String {
    let mut normalized_lines = Vec::new();
    for line in ir.lines() {
        let bytes = line.as_bytes();
        let mut out = String::with_capacity(line.len());
        let mut i = 0_usize;
        let mut in_quotes = false;
        let mut prev_space = false;

        while let Some(&b) = bytes.get(i) {
            if in_quotes {
                if b == b'"' {
                    in_quotes = false;
                }
                if let Some(ch) = line.get(i..).and_then(|s| s.chars().next()) {
                    out.push(ch);
                    i += ch.len_utf8();
                } else {
                    break;
                }
                continue;
            }
            if b == b'"' {
                in_quotes = true;
                prev_space = false;
                out.push('"');
                i += 1;
                continue;
            }
            if b == b' ' || b == b'\t' {
                if !prev_space {
                    out.push(' ');
                    prev_space = true;
                }
                i += 1;
                continue;
            }
            prev_space = false;
            if let Some(ch) = line.get(i..).and_then(|s| s.chars().next()) {
                out.push(ch);
                i += ch.len_utf8();
            } else {
                break;
            }
        }
        normalized_lines.push(out.trim_end().to_owned());
    }
    normalized_lines.join("\n")
}

fn assemble_ir_to_bitcode(
    llvm_as_bin: &Path,
    ir_text: &str,
    out_bc: &Path,
) -> Result<Vec<u8>, String> {
    if llvm_as_bin.as_os_str().is_empty() {
        return Err("LLVM_AS_BIN is empty; configured oracle path must be executable".to_owned());
    }
    let mut child = Command::new(llvm_as_bin)
        .arg("-")
        .arg("-o")
        .arg(out_bc)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| {
            format!(
                "failed to spawn configured LLVM_AS_BIN `{}`: {e}",
                llvm_as_bin.display()
            )
        })?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(ir_text.as_bytes()).map_err(|e| {
            format!(
                "failed writing IR to `llvm-as` stdin (`{}`): {e}",
                llvm_as_bin.display()
            )
        })?;
    }

    let output = child.wait_with_output().map_err(|e| {
        format!(
            "failed waiting on `llvm-as` (`{}`): {e}",
            llvm_as_bin.display()
        )
    })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "`llvm-as` (`{}`) exited with {}: {stderr}",
            llvm_as_bin.display(),
            output.status
        ));
    }

    fs::read(out_bc).map_err(|e| {
        format!(
            "failed reading assembled bitcode `{}`: {e}",
            out_bc.display()
        )
    })
}

fn disassemble_bitcode(llvm_dis_bin: &Path, bc_path: &Path) -> Result<String, String> {
    if llvm_dis_bin.as_os_str().is_empty() {
        return Err("LLVM_DIS_BIN is empty; configured oracle path must be executable".to_owned());
    }
    let output = Command::new(llvm_dis_bin)
        .arg(bc_path)
        .arg("-o")
        .arg("-")
        .output()
        .map_err(|e| {
            format!(
                "failed to spawn configured LLVM_DIS_BIN `{}`: {e}",
                llvm_dis_bin.display()
            )
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "`llvm-dis` (`{}`) exited with {}: {stderr}",
            llvm_dis_bin.display(),
            output.status
        ));
    }

    String::from_utf8(output.stdout)
        .map_err(|e| format!("`llvm-dis` emitted non-UTF-8 output: {e}"))
}

#[test]
fn test_canonical_equivalence_and_optional_llvm_as_oracle() -> Result<(), String> {
    // 1. Always verify canonical equivalence against explicit `0x<hex>` LLVM/Vellvm baseline IR:
    for case in DIFFERENTIAL_CORPUS {
        let normalized = normalize_llvm23_fp_and_comments(case.llvm23_ir)
            .map_err(|e| format!("case `{}` normalization failed: {e}", case.name))?;

        if case.exact_whitespace_match {
            if normalized != case.baseline_0x_ir {
                return Err(format!(
                    "case `{}` exact baseline mismatch:\n--- got ---\n{normalized}\n--- expected ---\n{}",
                    case.name, case.baseline_0x_ir
                ));
            }
        } else {
            let norm_collapsed = collapse_spaces_outside_quotes(&normalized);
            let base_collapsed = collapse_spaces_outside_quotes(case.baseline_0x_ir);
            if norm_collapsed != base_collapsed {
                return Err(format!(
                    "case `{}` canonical baseline mismatch:\n--- got ---\n{norm_collapsed}\n--- expected ---\n{base_collapsed}",
                    case.name
                ));
            }
        }
    }

    // 2. If `LLVM_AS_BIN` is set, enforce strict fail-fast bitcode round-trip equivalence:
    let Some(llvm_as_os) = env::var_os("LLVM_AS_BIN") else {
        return Ok(());
    };
    let llvm_as_path = PathBuf::from(llvm_as_os);
    let llvm_dis_path = env::var_os("LLVM_DIS_BIN").map(PathBuf::from);
    let tmp = TempDirGuard::new("llvm_as_diff")?;

    for (idx, case) in DIFFERENTIAL_CORPUS.iter().enumerate() {
        let normalized = normalize_llvm23_fp_and_comments(case.llvm23_ir)
            .map_err(|e| format!("case `{}` normalization failed: {e}", case.name))?;

        let modern_bc_path = tmp.path.join(format!("case_{idx}_modern.bc"));
        let norm_bc_path = tmp.path.join(format!("case_{idx}_norm.bc"));
        let base_bc_path = tmp.path.join(format!("case_{idx}_base.bc"));

        let bc_modern = assemble_ir_to_bitcode(&llvm_as_path, case.llvm23_ir, &modern_bc_path)?;
        let bc_norm = assemble_ir_to_bitcode(&llvm_as_path, &normalized, &norm_bc_path)?;
        let bc_base = assemble_ir_to_bitcode(&llvm_as_path, case.baseline_0x_ir, &base_bc_path)?;

        if bc_modern != bc_norm {
            return Err(format!(
                "case `{}`: `llvm-as` bitcode differs between LLVM 23 IR ({} bytes) and normalized IR ({} bytes)",
                case.name,
                bc_modern.len(),
                bc_norm.len()
            ));
        }
        if bc_norm != bc_base {
            return Err(format!(
                "case `{}`: `llvm-as` bitcode differs between normalized IR and `0x<hex>` baseline",
                case.name
            ));
        }

        if let Some(ref dis_bin) = llvm_dis_path {
            let dis_modern = disassemble_bitcode(dis_bin, &modern_bc_path)?;
            let dis_norm = disassemble_bitcode(dis_bin, &norm_bc_path)?;
            if dis_modern != dis_norm {
                return Err(format!(
                    "case `{}`: `llvm-dis` output differs:\n--- modern ---\n{dis_modern}\n--- norm ---\n{dis_norm}",
                    case.name
                ));
            }
        }
    }

    // 3. Also verify `split_module_for_vellvm` -> `merge_module` output assembles cleanly with `llvm-as`:
    let multi_fn_ir = "\
source_filename = \"roundtrip_merge.c\"
target datalayout = \"e-m:e-i64:64-n32:64-S128\"
target triple = \"aarch64-unknown-linux-gnu\"

$grp = comdat any
@state = internal global float f0x3DCCCCCD, align 4

define internal float @leaf(float %x) comdat($grp) #0 {
entry:
  %cur = load float, ptr @state, align 4
  %acc = fadd float %cur, %x
  %inf_add = fadd float %acc, +inf
  ret float %inf_add
}

define dso_local float @root(float %y) #0 {
entry:
  %r = call float @leaf(float /* comment */ %y)
  ret float %r
}

attributes #0 = { nounwind }
";
    let split = split_module_for_vellvm(multi_fn_ir)
        .map_err(|e| format!("split_module_for_vellvm failed: {e}"))?;
    for (fn_name, slice_ir) in &split.slices {
        let slice_bc = tmp.path.join(format!("slice_{fn_name}.bc"));
        let _ = assemble_ir_to_bitcode(&llvm_as_path, slice_ir, &slice_bc)?;
    }
    let merged =
        merge_module(&split.manifest, &split.slices).map_err(|e| format!("merge failed: {e}"))?;
    // Normalize global initializer in merged module if needed before assembling:
    let merged_norm =
        normalize_llvm23_fp_and_comments(&merged).map_err(|e| format!("norm failed: {e}"))?;
    let merged_bc = tmp.path.join("merged.bc");
    let _ = assemble_ir_to_bitcode(&llvm_as_path, &merged_norm, &merged_bc)?;

    Ok(())
}

#[test]
fn test_llvm_as_oracle_fails_fast_on_missing_or_empty_binary() -> Result<(), String> {
    let tmp = TempDirGuard::new("fail_fast_check")?;
    let out_bc = tmp.path.join("out.bc");
    let sample_ir = "define void @f() {\n  ret void\n}\n";

    let empty_err = assemble_ir_to_bitcode(Path::new(""), sample_ir, &out_bc);
    if empty_err.is_ok() {
        return Err("expected empty LLVM_AS_BIN path to fail fast".to_owned());
    }

    let missing_path = tmp.path.join("nonexistent_llvm_as_executable_99999");
    let missing_err = assemble_ir_to_bitcode(&missing_path, sample_ir, &out_bc);
    if missing_err.is_ok() {
        return Err("expected nonexistent LLVM_AS_BIN path to fail fast".to_owned());
    }

    Ok(())
}
