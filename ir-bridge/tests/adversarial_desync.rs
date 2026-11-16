//! Adversarial desync, lexical-boundary, soundness-gate, and split/merge regression tests
//! for `ir-bridge` (`Stage A` Red-Team Audit).

use std::collections::BTreeMap;

use ir_bridge::{
    BridgeError, FastPathEligibility, SliceRole, check_fast_path_eligibility, merge_module,
    normalize_llvm23_fp_and_comments, sanitize_for_vellvm, split_module_for_vellvm,
};

fn ensure(cond: bool, msg: impl Into<String>) -> Result<(), String> {
    if cond { Ok(()) } else { Err(msg.into()) }
}

fn ensure_ineligible_with(ir: &str, expected_substring: &str) -> Result<(), String> {
    match check_fast_path_eligibility(ir) {
        FastPathEligibility::Eligible => Err(format!(
            "expected Fast-Path rejection containing `{expected_substring}`, got Eligible for:\n{ir}"
        )),
        FastPathEligibility::FallbackRequired { reasons } => ensure(
            reasons.iter().any(|r| r.contains(expected_substring)),
            format!("expected rejection reason containing `{expected_substring}`, got {reasons:?}"),
        ),
    }
}

#[test]
fn c_strings_preserve_comments_fp_tokens_and_hex_quotes_across_pipeline() -> Result<(), String> {
    let payload = r#"c"semi ; keep /* immarg */ f0x3DCCCCCD +inf -snan(0x1) \22quote\22 \5C\00""#;
    let raw_module = format!(
        concat!(
            "target datalayout = \"e-m:e-p:64:64-i64:64-i128:128-n32:64-S128\"\n",
            "target triple = \"x86_64-unknown-linux-gnu\"\n",
            "@k_bytes = private unnamed_addr constant [67 x i8] {payload}, align 1 ; strip-tail\n",
            "define float @probe(float /* immarg */ %x) {{\n",
            "entry:\n",
            "  %a = fadd float %x, f0x3DCCCCCD ; trailing comment\n",
            "  %b = fadd float %a, +snan(0x1)\n",
            "  %p = getelementptr inbounds [67 x i8], ptr @k_bytes, i64 0, i64 0\n",
            "  %byte = load i8, ptr %p, align 1\n",
            "  %keep = sitofp i8 %byte to float\n",
            "  %res = fadd float %b, %keep\n",
            "  ret float %res\n",
            "}}\n",
        ),
        payload = payload,
    );

    let fp_norm = normalize_llvm23_fp_and_comments(&raw_module).map_err(|e| e.to_string())?;
    ensure(
        fp_norm.contains(payload),
        "normalize_llvm23_fp_and_comments mutated valid c\"...\" byte string",
    )?;
    ensure(
        !fp_norm.contains("float /* immarg */ %x"),
        "block comment outside quotes was not stripped",
    )?;
    ensure(
        fp_norm.contains("0x3FB99999A0000000") && fp_norm.contains("0x7FF0000020000000"),
        "f0x3DCCCCCD or +snan(0x1) outside quotes was not rewritten to Vellvm 16-hex IEEE bits",
    )?;

    let src_san = sanitize_for_vellvm(&raw_module, SliceRole::Source).map_err(|e| e.to_string())?;
    ensure(
        src_san.contains(payload) && !src_san.contains("float /* immarg */ %x"),
        "Source sanitization corrupted c\"...\" payload or failed to strip outside block comment",
    )?;

    let tgt_san =
        sanitize_for_vellvm(&raw_module, SliceRole::TargetFastPath).map_err(|e| e.to_string())?;
    ensure(
        tgt_san.contains(payload),
        "TargetFastPath sanitization rejected or corrupted valid c\"...\" byte string",
    )?;

    let split = split_module_for_vellvm(&raw_module).map_err(|e| e.to_string())?;
    let probe_slice = split
        .slices
        .get("probe")
        .ok_or_else(|| "missing `probe` slice".to_owned())?;
    ensure(
        probe_slice.contains("@k_bytes = available_externally unnamed_addr constant [67 x i8]")
            && probe_slice.contains(payload),
        "slice did not preserve available_externally constant @k_bytes payload",
    )?;

    let mut merged_slices = BTreeMap::new();
    merged_slices.insert("probe".to_owned(), probe_slice.clone());
    let merged = merge_module(&split.manifest, &merged_slices).map_err(|e| e.to_string())?;
    ensure(
        merged.contains(payload),
        "merge_module did not restore byte-identical @k_bytes c\"...\" initializer",
    )?;

    Ok(())
}

#[test]
fn fast_math_constexpr_gep_and_type_gates_reject_hazards_and_allow_lookalikes() -> Result<(), String>
{
    let hazard_cases: &[(&str, &str)] = &[
        (
            "define float @h1(float %x) {\n  %r = fneg fast float %x\n  ret float %r\n}\n",
            "fast-math flag",
        ),
        (
            "define float @h2(i1 %c, float %x, float %y) {\n  %r = select reassoc i1 %c, float %x, float %y\n  ret float %r\n}\n",
            "fast-math flag",
        ),
        (
            "define float @h3(float %x) {\nentry:\n  br label %join\njoin:\n  %p = phi nnan float [ %x, %entry ]\n  ret float %p\n}\n",
            "fast-math flag",
        ),
        (
            "define i1 @h4(float %x, float %y) {\n  %c = fcmp contract oeq float %x, %y\n  ret i1 %c\n}\n",
            "fast-math flag",
        ),
        (
            "define float @h5(double %d) {\n  %r = fptrunc afn double %d to float\n  ret float %r\n}\n",
            "fast-math flag",
        ),
        (
            "define double @h6(float %f) {\n  %r = fpext nsz float %f to double\n  ret double %r\n}\n",
            "fast-math flag",
        ),
        (
            "declare float @ext(float)\ndefine float @h7(float %f) {\n  %r = call arcp float @ext(float %f)\n  ret float %r\n}\n",
            "fast-math flag",
        ),
        (
            "define float @h8() {\n  ret float fadd fast (float 0x3FF0000000000000, float 0x4000000000000000)\n}\n",
            "fast-math flag",
        ),
        (
            "define ptr @h9(ptr %p) {\n  %q = getelementptr inbounds inrange(-4, 8) i8, ptr %p, i64 4\n  ret ptr %q\n}\n",
            "inrange",
        ),
        (
            "define i1 @h10(ptr %p, ptr %q) {\n  %c = icmp samesign ult ptr %p, %q\n  ret i1 %c\n}\n",
            "icmp samesign",
        ),
        (
            "define float @h11(i64 %x) {\n  %f = sitofp i64 %x to float\n  ret float %f\n}\n",
            "F-36",
        ),
        (
            "define float @h12(i64 %x) {\n  %f = uitofp nneg i64 %x to float\n  ret float %f\n}\n",
            "F-36",
        ),
        (
            "define double @h13() {\n  ret double uitofp (i128 1 to double)\n}\n",
            "F-36",
        ),
        (
            "declare range(i32 0, 2, 4, 6) i32 @multi_range()\ndefine i32 @h14() {\n  %v = call i32 @multi_range()\n  ret i32 %v\n}\n",
            "range(",
        ),
        (
            "declare void @abi_sink(ptr byval(i64))\ndefine void @h15(ptr %p) {\n  call void @abi_sink(ptr byval(i64) %p)\n  ret void\n}\n",
            "byval",
        ),
        (
            "declare void @init_sink(ptr initializes((0, 4)))\ndefine void @h16(ptr %p) {\n  call void @init_sink(ptr %p)\n  ret void\n}\n",
            "initializes",
        ),
        (
            "declare void @llvm.assume(i1)\ndefine void @h17(i1 %c) {\n  call void @llvm.assume(i1 %c)\n  ret void\n}\n",
            "llvm.assume",
        ),
        (
            "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)\ndefine void @h18(ptr %d, ptr %s) {\n  call void @llvm.memcpy.p0.p0.i64(ptr %d, ptr %s, i64 8, i1 true)\n  ret void\n}\n",
            "volatile",
        ),
        (
            "@maybe_null = extern_weak global i32\ndefine ptr @h19() {\n  ret ptr @maybe_null\n}\n",
            "extern_weak",
        ),
        (
            "@buf = global [4 x i32] zeroinitializer\n@mid = alias i32, getelementptr inbounds ([4 x i32], ptr @buf, i64 0, i64 2)\ndefine ptr @h20() {\n  ret ptr @mid\n}\n",
            "alias",
        ),
        (
            "declare void @bundle_callee()\ndefine void @h21() {\n  call void @bundle_callee() [ \"deopt\"(i32 0) ]\n  ret void\n}\n",
            "operand bundle",
        ),
    ];

    for (ir, reason_sub) in hazard_cases {
        ensure_ineligible_with(ir, reason_sub)?;
    }

    // Identifiers, basic-block labels, and `nofpclass(...)` masks sharing substrings with
    // forbidden tokens must remain Eligible on `TargetFastPath`.
    let clean_lookalike = concat!(
        "declare float @frem_helper(float)\n",
        "define i32 @lookalike(i32 %fast, float %x) {\n",
        "entry:\n",
        "  br label %volatile\n",
        "volatile:\n",
        "  %call_val = call float @frem_helper(float %x)\n",
        "  %cmp = fcmp oeq float %call_val, %x\n",
        "  %ext = zext i1 %cmp to i32\n",
        "  %sum = add i32 %fast, %ext\n",
        "  ret i32 %sum\n",
        "}\n",
    );
    ensure(
        check_fast_path_eligibility(clean_lookalike) == FastPathEligibility::Eligible,
        format!(
            "unexpected false-positive Fast-Path rejection on clean lookalike: {:?}",
            check_fast_path_eligibility(clean_lookalike)
        ),
    )?;

    Ok(())
}

#[test]
fn role_aware_sanitization_strips_debug_noise_while_gating_target_hazards() -> Result<(), String> {
    let ir_with_noise_and_hazard = concat!(
        "declare !dbg !1 range(i32 0, 2, 4, 6) i32 @callee(ptr %p) #0\n",
        "define dso_local i32 @src_fn(i32 %a, ptr %p) prefalign(16) #0 !dbg !4 {\n",
        "entry:\n",
        "    #dbg_value(i32 %a, !2, !DIExpression(), !3)\n",
        "  %v = call i32 @callee(ptr %p), !dbg !5\n",
        "  %sum = add nsw i32 %a, %v\n",
        "  ret i32 %sum\n",
        "}\n",
        "uselistorder ptr @callee, { 0 }\n",
        "attributes #0 = { nounwind denormal_fpenv(ieee|ieee) }\n",
        "!llvm.dbg.cu = !{!0}\n",
        "!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1)\n",
        "!1 = !DIFile(filename: \"t.c\", directory: \".\")\n",
    );

    // TargetFastPath must reject multi-pair `range(...)` before stripping syntax noise.
    ensure(
        sanitize_for_vellvm(ir_with_noise_and_hazard, SliceRole::TargetFastPath).is_err(),
        "TargetFastPath unexpectedly accepted multi-pair range(...) hazard",
    )?;

    // Source role strips debug/syntax directives rejected by Vellvm's grammar while keeping `nsw`.
    let sanitized = sanitize_for_vellvm(ir_with_noise_and_hazard, SliceRole::Source)
        .map_err(|e| e.to_string())?;
    for stripped_tok in [
        "#dbg_value",
        "uselistorder",
        "!llvm.dbg.cu",
        "!DICompileUnit",
        "!DIFile",
        "!dbg",
        "prefalign(",
        "denormal_fpenv(ieee",
    ] {
        ensure(
            !sanitized.contains(stripped_tok),
            format!("Source sanitizer left `{stripped_tok}` in output:\n{sanitized}"),
        )?;
    }
    ensure(
        sanitized.contains("add nsw i32 %a, %v"),
        "Source sanitizer lost `nsw` poison flag that Vellvm models natively",
    )?;

    Ok(())
}

#[test]
fn split_and_merge_roundtrip_remaps_metadata_closures_visibility_and_llvm_arrays()
-> Result<(), String> {
    let module_ir = concat!(
        "source_filename = \"roundtrip.c\"\n",
        "target datalayout = \"e-m:e-p:64:64-i64:64-i128:128-n32:64-S128\"\n",
        "target triple = \"x86_64-unknown-linux-gnu\"\n",
        "$hot_grp = comdat any\n",
        "%struct.Pair = type { i32, ptr }\n",
        "@tls_counter = thread_local(initialexec) global i32 7, align 4\n",
        "@backing_slot = internal global i32 99, align 4\n",
        "@keep_pair = internal constant %struct.Pair { i32 1, ptr @backing_slot }, align 8\n",
        "@llvm.used = appending global [1 x ptr] [ptr @keep_pair], section \"llvm.metadata\"\n",
        "@llvm.global_ctors = appending global [1 x { i32, ptr, ptr }] [{ i32, ptr, ptr } { i32 65535, ptr @ctor_fn, ptr null }]\n",
        "declare i32 @__gxx_personality_v0(...)\n",
        "declare void @may_throw()\n",
        "define internal void @ctor_fn() {\n",
        "entry:\n",
        "  store i32 9, ptr @tls_counter, align 4\n",
        "  ret void\n",
        "}\n",
        "define hidden dso_local i32 @worker(ptr %p) local_unnamed_addr section \".text.hot\" comdat($hot_grp) align 16 #0 !prof !10 {\n",
        "entry:\n",
        "  %f0 = getelementptr inbounds %struct.Pair, ptr @keep_pair, i64 0, i32 0\n",
        "  %v0 = load i32, ptr %f0, align 4, !tbaa !20\n",
        "  %vt = load i32, ptr @tls_counter, align 4\n",
        "  %v1 = load i32, ptr %p, align 4\n",
        "  %s0 = add nsw i32 %v0, %vt\n",
        "  %s = add nsw i32 %s0, %v1\n",
        "  ret i32 %s\n",
        "}\n",
        "define void @eh_passthrough() personality ptr @__gxx_personality_v0 {\n",
        "entry:\n",
        "  invoke void @may_throw() to label %ok unwind label %lpad\n",
        "ok:\n",
        "  ret void\n",
        "lpad:\n",
        "  %lp = landingpad { ptr, i32 } cleanup\n",
        "  resume { ptr, i32 } %lp\n",
        "}\n",
        "attributes #0 = { nounwind }\n",
        "!llvm.ident = !{!0}\n",
        "!0 = !{!\"clang 23.1.5\"}\n",
        "!10 = !{!\"function_entry_count\", i64 42}\n",
        "!20 = !{!21, !21, i64 0}\n",
        "!21 = !{!\"int\", !22, i64 0}\n",
        "!22 = !{!\"omnipotent char\"}\n",
    );

    let split = split_module_for_vellvm(module_ir).map_err(|e| e.to_string())?;

    // Unwinding function must be marked non-splittable and omitted from `slices`.
    let eh_entry = split
        .manifest
        .functions
        .iter()
        .find(|f| f.name == "eh_passthrough")
        .ok_or_else(|| "missing `eh_passthrough` manifest entry".to_owned())?;
    ensure(
        !eh_entry.splittable && !split.slices.contains_key("eh_passthrough"),
        "unwinding function was unexpectedly marked splittable",
    )?;

    let worker_slice = split
        .slices
        .get("worker")
        .ok_or_else(|| "missing `worker` slice".to_owned())?;
    ensure(
        !worker_slice.contains("@llvm.used") && !worker_slice.contains("@llvm.global_ctors"),
        "module-level @llvm.used / @llvm.global_ctors leaked into per-function slice",
    )?;
    ensure(
        worker_slice.contains("@tls_counter = external thread_local(initialexec) global i32")
            && worker_slice.contains("@backing_slot = external global i32"),
        "referenced @tls_counter or transitive @backing_slot global missing in `worker` slice",
    )?;
    ensure(
        worker_slice.contains("%struct.Pair = type { i32, ptr }"),
        "referenced `%struct.Pair` typedef missing from `worker` slice",
    )?;
    // Transitive metadata closure `!20 -> !21 -> !22` must be densely remapped into the slice.
    ensure(
        worker_slice.contains("omnipotent char"),
        "transitive metadata node `!22` missing from `worker` slice",
    )?;

    // Simulate an optimizer rewriting `worker` with colliding `#0` and `!0` IDs, `-O2`-inferred
    // parameter attributes (`nocapture readonly`) + `!tbaa` (which `F-19` must strip), and a
    // non-alias `!annotation !0` attachment (which `merge_module` must remap away from `!0..=!22`).
    let optimized_worker = concat!(
        "define dso_local i32 @worker(ptr nocapture readonly %p) local_unnamed_addr #0 {\n",
        "entry:\n",
        "  %f0 = getelementptr inbounds %struct.Pair, ptr @keep_pair, i64 0, i32 0\n",
        "  %v0 = load i32, ptr %f0, align 4, !tbaa !0, !annotation !0\n",
        "  %v1 = load i32, ptr %p, align 4\n",
        "  %s = add nsw i32 %v0, %v1\n",
        "  ret i32 %s\n",
        "}\n",
        "attributes #0 = { willreturn }\n",
        "!0 = !{!1}\n",
        "!1 = !{!\"custom-note\"}\n",
    );

    let mut merged_inputs = BTreeMap::new();
    let ctor_slice = split
        .slices
        .get("ctor_fn")
        .ok_or_else(|| "missing `ctor_fn` slice".to_owned())?;
    merged_inputs.insert("ctor_fn".to_owned(), ctor_slice.clone());
    merged_inputs.insert("worker".to_owned(), optimized_worker.to_owned());

    let merged = merge_module(&split.manifest, &merged_inputs).map_err(|e| e.to_string())?;
    ensure(
        merged.contains("@llvm.used = appending global")
            && merged.contains("@llvm.global_ctors = appending global"),
        "merge_module failed to restore @llvm.used or @llvm.global_ctors",
    )?;
    ensure(
        merged.contains(
            "define hidden i32 @worker(ptr %p) local_unnamed_addr section \".text.hot\" comdat($hot_grp) align 16 #0 !prof !10 {"
        ),
        format!("merge_module did not restore canonical @worker header:\n{merged}"),
    )?;
    ensure(
        merged.contains("define internal void @ctor_fn()"),
        "merge_module did not restore `internal` linkage on @ctor_fn",
    )?;
    ensure(
        merged.contains("landingpad { ptr, i32 } cleanup"),
        "merge_module did not preserve non-splittable @eh_passthrough body",
    )?;
    ensure(
        !merged.contains("!tbaa")
            && merged.contains("!annotation !23")
            && merged.contains("!24 = !{!\"custom-note\"}"),
        format!(
            "merge_module failed to strip inferred !tbaa or remap slice `!0`/`!1` away from `!0..=!22`:\n{merged}"
        ),
    )?;

    Ok(())
}

#[test]
fn f50_backslash_before_closing_quote_does_not_mask_following_ir() -> Result<(), String> {
    // In LLVM 23 (`LLLexer.cpp`) and Vellvm (`llvm_lexer.mll`), `"` always terminates `"..."`
    // (embedded quotes use `\22`, and a trailing `\` is `\5C` or raw `\` before closing `"`).
    let backslash_quote_smuggle = concat!(
        "declare void @sink(ptr)\n",
        "@q = private constant [2 x i8] c\"\\\\\"\n",
        "define float @smuggle(float %a, float %b) {\n",
        "entry:\n",
        "  call void @sink(ptr @\"\\\") ; closed quote before comment\n",
        "  call void @sink(ptr @\"\\\") %bad = fadd fast float %a, %b\n",
        "  ret float %a\n",
        "}\n",
    );
    ensure_ineligible_with(backslash_quote_smuggle, "fast-math flag")?;

    let fp_after_backslash_quote = concat!(
        "@raw_bs = private constant [1 x i8] c\"\\\", align 1\n",
        "define float @norm_after_bs(float /* strip */ %x) {\n",
        "  %r = fadd float %x, f0x3DCCCCCD\n",
        "  ret float %r\n",
        "}\n",
    );
    let norm =
        normalize_llvm23_fp_and_comments(fp_after_backslash_quote).map_err(|e| e.to_string())?;
    ensure(
        norm.contains("0x3FB99999A0000000") && !norm.contains("/* strip */"),
        format!("c\"\\\" desynchronized quote state across following lines:\n{norm}"),
    )?;

    Ok(())
}

#[test]
fn f51_type_aliases_vector_ptr_samesign_lane_attrs_and_constexpr_nneg_gated() -> Result<(), String>
{
    let cases: &[(&str, &str)] = &[
        (
            "%HalfAlias = type half\n%Chain = type %HalfAlias\ndefine %Chain @f(%Chain %x) {\n  %r = fadd %Chain %x, %x\n  ret %Chain %r\n}\n",
            "half",
        ),
        (
            "%Node = type { ptr, %Node }\n%FpWrap = type { %Node, bfloat }\ndefine void @cyc(ptr %p) {\n  %v = load %FpWrap, ptr %p, align 8\n  ret void\n}\n",
            "bfloat",
        ),
        (
            "define <2 x i1> @vp(<2 x ptr> %a, <2 x ptr> %b) {\n  %c = icmp samesign ult <2 x ptr> %a, %b\n  ret <2 x i1> %c\n}\n",
            "icmp samesign",
        ),
        (
            "%PtrAlias = type ptr\ndefine i1 @pa(%PtrAlias %a, %PtrAlias %b) {\n  %c = icmp samesign ule %PtrAlias %a, %b\n  ret i1 %c\n}\n",
            "icmp samesign",
        ),
        (
            "declare void @vp_sink(<2 x ptr> nonnull)\ndefine void @vp_call(<2 x ptr> %v) {\n  call void @vp_sink(<2 x ptr> nonnull %v)\n  ret void\n}\n",
            "F-51",
        ),
        (
            "define dereferenceable(8) <2 x ptr> @vp_ret(<2 x ptr> %v) {\n  ret <2 x ptr> %v\n}\n",
            "F-51",
        ),
        (
            "define float @ce() {\n  ret float uitofp nneg (i128 -1 to float)\n}\n",
            "F-36",
        ),
        (
            "%Wide = type i128\ndefine double @alias_wide(%Wide %x) {\n  %d = sitofp %Wide %x to double\n  ret double %d\n}\n",
            "F-36",
        ),
    ];

    for (ir, expected_reason) in cases {
        ensure_ineligible_with(ir, expected_reason)?;
    }

    Ok(())
}

#[test]
fn f52_quoted_and_hex_escaped_identifiers_gated_and_tracked_in_split_merge() -> Result<(), String> {
    let quoted_assume_ir = concat!(
        "declare void @\"llvm.assume\"(i1)\n",
        "define void @qa(i1 %c) {\n",
        "  call void @\"llvm.assume\"(i1 %c)\n",
        "  ret void\n",
        "}\n",
    );
    ensure_ineligible_with(quoted_assume_ir, "llvm.assume")?;

    // `\6C` is ASCII `'l'`, so `@"\6Clvm.assume"` names `llvm.assume` in LLVM's symbol table.
    let hex_escaped_assume_ir = concat!(
        "declare void @\"\\6Clvm.assume\"(i1)\n",
        "define void @qhex(i1 %c) {\n",
        "  call void @\"\\6Clvm.assume\"(i1 %c)\n",
        "  ret void\n",
        "}\n",
    );
    ensure_ineligible_with(hex_escaped_assume_ir, "llvm.assume")?;

    let quoted_volatile_memcpy_ir = concat!(
        "declare void @\"llvm.memcpy.p0.p0.i64\"(ptr, ptr, i64, i1)\n",
        "define void @qmc(ptr %d, ptr %s) {\n",
        "  call void @\"llvm.memcpy.p0.p0.i64\"(ptr %d, ptr %s, i64 8, i1 true)\n",
        "  ret void\n",
        "}\n",
    );
    ensure_ineligible_with(quoted_volatile_memcpy_ir, "volatile")?;

    let quoted_symbol_desync_ir = "define i32 @\"foo\"(i32 %\"x\") {\n  ret i32 %\"x\"\n}\n";
    ensure_ineligible_with(quoted_symbol_desync_ir, "F-52")?;

    // Split/merge must track quoted `%type`, `@global`, and cross-function `blockaddress(@"...")`.
    let module_with_quoted_refs = concat!(
        "target datalayout = \"e-m:e-p:64:64-i64:64-i128:128-n32:64-S128\"\n",
        "%\"quoted.Pair\" = type { i32, i32 }\n",
        "@\"quoted.slot\" = internal global %\"quoted.Pair\" zeroinitializer, align 4\n",
        "define i32 @use_quoted() {\n",
        "entry:\n",
        "  %v = load i32, ptr @\"quoted.slot\", align 4\n",
        "  ret i32 %v\n",
        "}\n",
        "define ptr @addr_taker() {\n",
        "entry:\n",
        "  ret ptr blockaddress(@\"quoted.target\", %lbl)\n",
        "}\n",
        "define i32 @\"quoted.target\"() {\n",
        "entry:\n",
        "  br label %lbl\n",
        "lbl:\n",
        "  ret i32 7\n",
        "}\n",
    );
    let split = split_module_for_vellvm(module_with_quoted_refs).map_err(|e| e.to_string())?;
    let use_slice = split
        .slices
        .get("use_quoted")
        .ok_or_else(|| "missing `use_quoted` slice".to_owned())?;
    ensure(
        use_slice.contains("%\"quoted.Pair\" = type { i32, i32 }")
            && use_slice.contains("@\"quoted.slot\" = external global %\"quoted.Pair\", align 4"),
        format!("slice lost quoted `%\"quoted.Pair\"` or `@\"quoted.slot\"`:\n{use_slice}"),
    )?;
    ensure(
        !split.slices.contains_key("\"quoted.target\"") && !split.slices.contains_key("addr_taker"),
        "cross-function blockaddress(@\"quoted.target\", ...) was not marked non-splittable",
    )?;

    Ok(())
}

#[test]
fn f53_zero_and_oversized_integer_bitwidths_rejected_cleanly() -> Result<(), String> {
    for bad_ty in ["i0", "b0", "i8388609", "i99999999999999999999999999"] {
        let ir = format!(
            "define void @bad_bw(ptr %p) {{\n  %v = load {bad_ty}, ptr %p\n  ret void\n}}\n"
        );
        ensure_ineligible_with(&ir, "F-53")?;
        ensure(
            matches!(
                sanitize_for_vellvm(&ir, SliceRole::Source),
                Err(BridgeError::MalformedModule { .. })
            ),
            format!("expected MalformedModule on Source role for `{bad_ty}`"),
        )?;
    }

    // Valid bitwidths (`i1`, `i128`, `i8388608`) and `%i0` / `@i99999999` identifiers remain legal.
    let valid_ir = concat!(
        "declare i32 @i99999999(i1)\n",
        "define i32 @ok_bw(i1 %i0, i128 %wide) {\n",
        "  %tr = trunc i128 %wide to i32\n",
        "  %c = call i32 @i99999999(i1 %i0)\n",
        "  %s = add i32 %tr, %c\n",
        "  ret i32 %s\n",
        "}\n",
    );
    ensure(
        check_fast_path_eligibility(valid_ir) == FastPathEligibility::Eligible,
        format!(
            "valid bitwidths or `%i0` lookalike falsely rejected: {:?}",
            check_fast_path_eligibility(valid_ir)
        ),
    )?;

    Ok(())
}

#[test]
fn f54_multiple_attr_groups_and_inline_fn_attrs_preserved_across_split_merge() -> Result<(), String>
{
    let multi_attr_module = concat!(
        "target datalayout = \"e-m:e-p:64:64-i64:64-i128:128-n32:64-S128\"\n",
        "define internal i32 @multi_attr(i32 %x) unnamed_addr addrspace(1) noinline \"frame-pointer\"=\"all\" alignstack(16) #0 #1 section \".text.m\" align 32 gc \"statepoint-example\" {\n",
        "entry:\n",
        "  ret i32 %x\n",
        "}\n",
        "define i32 @caller(i32 %y) #1 {\n",
        "entry:\n",
        "  %r = call addrspace(1) i32 @multi_attr(i32 %y)\n",
        "  ret i32 %r\n",
        "}\n",
        "attributes #0 = { nounwind }\n",
        "attributes #1 = { \"target-cpu\"=\"generic\" }\n",
    );

    let split = split_module_for_vellvm(multi_attr_module).map_err(|e| e.to_string())?;
    let multi_slice = split
        .slices
        .get("multi_attr")
        .ok_or_else(|| "missing `multi_attr` slice".to_owned())?;
    ensure(
        multi_slice.contains(
            "define dso_local i32 @multi_attr(i32 %x) unnamed_addr addrspace(1) noinline \"frame-pointer\"=\"all\" alignstack(16) #0 #1 align 32 gc \"statepoint-example\" {"
        ),
        format!("multi_attr slice dropped inline attrs or secondary `#1` group:\n{multi_slice}"),
    )?;

    let caller_slice = split
        .slices
        .get("caller")
        .ok_or_else(|| "missing `caller` slice".to_owned())?;
    ensure(
        caller_slice.contains(
            "declare i32 @multi_attr(i32) addrspace(1) noinline \"frame-pointer\"=\"all\" alignstack(16) #0 #1 gc \"statepoint-example\""
        ),
        format!("caller prototype_declare dropped callee attrs/groups:\n{caller_slice}"),
    )?;

    let merged = merge_module(&split.manifest, &split.slices).map_err(|e| e.to_string())?;
    ensure(
        merged.contains(
            "define internal i32 @multi_attr(i32 %x) unnamed_addr addrspace(1) section \".text.m\" align 32 gc \"statepoint-example\" noinline \"frame-pointer\"=\"all\" alignstack(16) #0 #1 {"
        ),
        format!("merge_module failed to restore full multi-attr header:\n{merged}"),
    )?;

    for kw in ["strictfp", "naked", "optnone"] {
        let gated_ir = format!("define i32 @fn_{kw}(i32 %x) noinline {kw} {{\n  ret i32 %x\n}}\n");
        ensure_ineligible_with(&gated_ir, kw)?;
    }

    Ok(())
}

#[test]
fn f55_tab_call_operand_bundles_gated_and_declare_trailing_metadata_stripped() -> Result<(), String>
{
    let tab_bundle_ir = "declare void @callee()\ndefine void @tb() {\n  call\tvoid @callee() [ \"deopt\"() ]\n  ret void\n}\n";
    ensure_ineligible_with(tab_bundle_ir, "operand bundle")?;

    let decl_trailing_md_ir = concat!(
        "target datalayout = \"e-m:e-p:64:64-i64:64-i128:128-n32:64-S128\"\n",
        "declare !dbg !1 i32 @ext_decl(i32) #0 !prof !2, !annotation !3\n",
        "define i32 @use_decl(i32 %x) {\n",
        "entry:\n",
        "  %r = call i32 @ext_decl(i32 %x)\n",
        "  ret i32 %r\n",
        "}\n",
        "attributes #0 = { nounwind }\n",
        "!1 = !{}\n",
        "!2 = !{!\"branch_weights\", i32 1}\n",
        "!3 = !{!\"note\"}\n",
    );
    let src_san =
        sanitize_for_vellvm(decl_trailing_md_ir, SliceRole::Source).map_err(|e| e.to_string())?;
    ensure(
        src_san.contains("declare i32 @ext_decl(i32) #0\n")
            && !src_san.contains("!prof")
            && !src_san.contains("!annotation"),
        format!("Source sanitizer left trailing metadata on `declare`:\n{src_san}"),
    )?;

    let split = split_module_for_vellvm(decl_trailing_md_ir).map_err(|e| e.to_string())?;
    let slice = split
        .slices
        .get("use_decl")
        .ok_or_else(|| "missing `use_decl` slice".to_owned())?;
    ensure(
        slice.contains("declare i32 @ext_decl(i32) #0\n"),
        format!("split_module_for_vellvm left metadata on slice `declare`:\n{slice}"),
    )?;

    Ok(())
}

#[test]
fn f39_fp_to_int_bitcast_gated_on_target_fast_path_for_nan_payload_portability()
-> Result<(), String> {
    let scalar_f32_ir = concat!(
        "define i32 @nan_bits32(float %a, float %b) {\n",
        "entry:\n",
        "  %sum = fadd float %a, %b\n",
        "  %bits = bitcast float %sum to i32\n",
        "  ret i32 %bits\n",
        "}\n",
    );
    ensure_ineligible_with(scalar_f32_ir, "F-39")?;

    let scalar_f64_ir = concat!(
        "define i64 @nan_bits64(double %a) {\n",
        "entry:\n",
        "  %bits = bitcast double %a to i64\n",
        "  ret i64 %bits\n",
        "}\n",
    );
    ensure_ineligible_with(scalar_f64_ir, "F-39")?;

    let vec_and_alias_ir = concat!(
        "%VecF = type <4 x float>\n",
        "%VecI = type <4 x i32>\n",
        "define %VecI @nan_vec_alias(%VecF %v) {\n",
        "entry:\n",
        "  %bits = bitcast %VecF %v to %VecI\n",
        "  ret %VecI %bits\n",
        "}\n",
    );
    ensure_ineligible_with(vec_and_alias_ir, "F-39")?;

    let constexpr_ir = concat!(
        "define i32 @nan_constexpr(i32 %x) {\n",
        "entry:\n",
        "  %y = add i32 %x, bitcast (float 0x7FF8000000000000 to i32)\n",
        "  ret i32 %y\n",
        "}\n",
    );
    ensure_ineligible_with(constexpr_ir, "F-39")?;

    let cross_lane_ir = concat!(
        "define i64 @nan_cross_lane(<2 x float> %v) {\n",
        "entry:\n",
        "  %bits = bitcast <2 x float> %v to i64\n",
        "  ret i64 %bits\n",
        "}\n",
    );
    ensure_ineligible_with(cross_lane_ir, "F-39")?;

    // Source slices may still sanitize FP-to-integer bitcast cleanly for Safe-Path fallback,
    // and integer-to-FP bitcast does not observe hardware-chosen NaN output payloads.
    sanitize_for_vellvm(scalar_f32_ir, SliceRole::Source).map_err(|e| e.to_string())?;
    let int_to_fp_ir = concat!(
        "define float @from_bits(i32 %bits) {\n",
        "entry:\n",
        "  %f = bitcast i32 %bits to float\n",
        "  ret float %f\n",
        "}\n",
    );
    ensure(
        check_fast_path_eligibility(int_to_fp_ir) == FastPathEligibility::Eligible,
        "integer-to-FP `bitcast` was unexpectedly rejected",
    )?;

    Ok(())
}
