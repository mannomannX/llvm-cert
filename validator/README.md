# `CertValidator` Architecture & Audit Map

Logical Rocq namespace: `-Q ../../validator CertValidator` (compiled from [`vellvm/src/_RocqProject`](../vellvm/src/_RocqProject)).

This directory contains **55 Rocq source files** (`49` top-level files in `validator/` and `6` shared helper/tactic modules in `validator/common/`). All validator modules stay in a flat `CertValidator` namespace (instead of nested subdirectories) so leaf module basenames remain globally unique under Rocq `Separate Extraction` ([`Extract.v`](../vellvm/src/ml/extracted/Extract.v)).

---

## 1. Trust Flow & CLI Entrypoints

All untrusted artifacts (`.ll` IR modules, `.cert` / `.mc.cert` witnesses, ELF64 binaries, and DIMACS/LRAT proofs) enter through the thin OCaml wrapper [`cert_validator.ml`](../vellvm/src/ml/bin/cert_validator.ml) (part of the `<= 750` LOC handwritten OCaml TCB) and dispatch into fail-closed Rocq-extracted decision procedures:

```text
Untrusted Inputs                     OCaml TCB Wrapper                   Verified Rocq Validators
----------------                     -----------------                   ------------------------
cnf + lrat       --check-lrat     -> cert_validator.ml ----------------> CertFormat.validate_dimacs_lrat_str
src.ll + tgt.ll  (default / TV)   -> VellvmLib.IO.parse_file + --------> CertValidator.validate_tle_pair_with_cert_str
  + fn.cert                          cert_validator.ml                     (IR open-world TV + LRAT + loops)
ir.ll + bin.elf  --check-mc       -> VellvmLib.IO.parse_file + --------> McValidator.validate_mc_tle_with_cert_str
  + fn.mc.cert                       cert_validator.ml                     (ELF64 + RV64/AArch64 + loops/calls + LRAT)
ir.ll + bin.elf  --emit-mc-cnf    -> cert_validator.ml ----------------> McValidator.emit_mc_dimacs_cnf_str
orig + merged    --check-merge    -> cert_validator.ml (+ per-slice ---> CertPasses.ModuleMerge.validate_module_merge_
  + slices/certs                     IR TV checks via CertValidator)       certified_tle_composed

Outside TCB (Differential ISA Oracle):
  scripts/isa_oracle/isa_oracle_runner.ml ---> Rv64Sem / A64CoreSem concrete evaluators (vs. QEMU & Sail)
```

### Fail-Closed Exit Contract

- `0`: Verified accepted (`Datatypes.Coq_inr ()`).
- `2`: Invalid CLI flags, duplicate arguments, or forbidden `--slice` flag.
- `3`: I/O error, parser failure, stack/OOM exception, or input exceeding the `64 MiB` guard.
- `4`: Verification rejected (`Datatypes.Coq_inl err`) with a standardized `[<gate-tag>]` diagnostic emitted by [`common/Diag.v`](./common/Diag.v).

---

## 2. Shared Infrastructure & Bit-Blasting Core

### 2.1 Shared Tactics, Options & Diagnostics (`common/`, 6 files)

| File | Role |
| :--- | :--- |
| [`common/Options.v`](./common/Options.v) | Global Rocq hygiene (`Set Default Goal Selector "!"`, `Unset Implicit Arguments`) |
| [`common/Diag.v`](./common/Diag.v) | `[<gate-tag>]` diagnostic builders, lazy error combinators, $O(\log n)$ numeric formatters |
| [`common/CoreTactics.v`](./common/CoreTactics.v) | Shared structural, case-splitting, and equality decision tactics |
| [`common/BvTactics.v`](./common/BvTactics.v) | CompCert bitvector / `Integers` simplification and width reasoning tactics |
| [`common/IntBvTactics.v`](./common/IntBvTactics.v) | Integer-to-bitvector arithmetic bridge tactics |
| [`common/EouTactics.v`](./common/EouTactics.v) | Error / OOM / UB (`EOU`) monadic inversion and reasoning tactics |

### 2.2 Zero-Axiom SAT/LRAT & AIG Bit-Blasting (4 files)

Dependency chain: `LratCore.v` $\to$ `AigGates.v` $\to$ `AigArith.v` $\to$ `AigLrat.v`.

| File | Role |
| :--- | :--- |
| [`LratCore.v`](./LratCore.v) | Zero-axiom Stdlib-only `PosTrie`, DIMACS CNF & LRAT proof checker (`check_lrat_unsat_sound`), DPLL auto-solver |
| [`AigGates.v`](./AigGates.v) | Two-rail AIG Tseitin gate encoding, UNSAT counterexample engine, `modulus_pow_sz` |
| [`AigArith.v`](./AigArith.v) | Two-rail bit-blasting encoders for arithmetic, shifts, casts, and `icmp` predicates |
| [`AigLrat.v`](./AigLrat.v) | Facade module re-exporting `LratCore`, `AigGates`, and `AigArith` |

---

## 3. Certificate Format, Algebraic Rules & IR Translation Validator

### 3.1 Certificate Format & Algebraic Refinement (8 files)

```text
CertFormatAst.v --> { CertFormatParse.v, CertFormatGates.v } --> CertFormat.v
AlgRulesEval.v  --> AlgRulesNormBinop.v --> AlgRulesNormRefines.v --> AlgRules.v
```

| File | Role |
| :--- | :--- |
| [`CertFormatAst.v`](./CertFormatAst.v) | Vellvm-free certificate AST, boolean equality deciders, and well-formedness predicates |
| [`CertFormatParse.v`](./CertFormatParse.v) | Linear S-expression and `cert-v1` parser (`parse_sexp`, `parse_cert`) + `parse_cert_wf` |
| [`CertFormatGates.v`](./CertFormatGates.v) | `[F-17..F-39]` IR syntax gates (`check_validator_syntax_gates`) & prototype contracts (`check_prototype_contract`) |
| [`CertFormat.v`](./CertFormat.v) | Standalone DIMACS/LRAT string validator (`validate_dimacs_lrat_str_sound`) + `CertFormat*` facade |
| [`AlgRulesEval.v`](./AlgRulesEval.v) | Two-rail expression evaluator and let-DAG expansion equivalence (`eval_expand_lets_equiv`) |
| [`AlgRulesNormBinop.v`](./AlgRulesNormBinop.v) | Algebraic expression normalization rules for binary operations and poison propagation |
| [`AlgRulesNormRefines.v`](./AlgRulesNormRefines.v) | Pure algebraic refinement checker (`check_expr_refines`, `check_expr_refines_sound`) |
| [`AlgRules.v`](./AlgRules.v) | Combined algebraic + 2-rail LRAT expression checker (`check_expr_refines_with_lrat_sound`) |

### 3.2 Open-World IR Translation Validator (10 files)

```text
CfgDag.v + CertValOpenWorld.v --> CertValExpReify.v --> CertValCfgDag.v
  --> { CertValCfgSum.v, (CertValUbCheck.v --> CertValPathCheck.v) }
  --> CertValLoop.v --> CertValProto.v --> CertValidator.v
```

| File | Role |
| :--- | :--- |
| [`CfgDag.v`](./CfgDag.v) | Decidable bounded CFG DAG acyclicity / loop cutpoint check (`dec_cfg_dag`) |
| [`CertValOpenWorld.v`](./CertValOpenWorld.v) | Open-world Vellvm IR simulation foundation (`draw_strat`, `cfg_steps_to_ret`, memory/alias invariants) |
| [`CertValExpReify.v`](./CertValExpReify.v) | IR scalar/expression symbolic reification (`build_param_env`, `reify_exp`) |
| [`CertValCfgDag.v`](./CertValCfgDag.v) | Acyclic CFG DAG summarization (`summarize_cfg_dag_with_uas`) and phi/code path reification |
| [`CertValCfgSum.v`](./CertValCfgSum.v) | Whole-CFG summary equivalence and memory-alias witness checking (`check_alias_witness_valid`) |
| [`CertValUbCheck.v`](./CertValUbCheck.v) | Side-condition / non-UB / `noundef` / poison safety discharge checks |
| [`CertValPathCheck.v`](./CertValPathCheck.v) | Path-wise DAG refinement checking (`check_cert_cfg`, `check_cert_cfg_with_lrat`) |
| [`CertValLoop.v`](./CertValLoop.v) | Natural loop cutpoint invariant verification (`check_loop_cutpoint_cfg`) |
| [`CertValProto.v`](./CertValProto.v) | Prototype, attribute, global, and `mcfg`/TLE structural verification (`check_cert_defn`) |
| [`CertValidator.v`](./CertValidator.v) | End-to-end string/TLE validator (`validate_mcfg_with_cert_sound`, `validate_tle_pair_with_cert_str_sound`) |

---

## 4. Machine-Code & ELF64 Validator (RV64IMAC & AArch64, 26 files)

Because all validator modules remain flat in `validator/`, the former `validator/mc/` plan scope lives directly in the **26 MC/ELF64 files** documented in this section.

### 4.1 Shared ELF64, Frame Memory, ISA Core & MC Certificate Specs (4 files)

| File | Role |
| :--- | :--- |
| [`Elf64Spec.v`](./Elf64Spec.v) | Zero-axiom ELF64 parser, relocation/symbol checker (`elf64_extract_func*_sound`), `[elf-*]` diagnostics |
| [`McFrameMem.v`](./McFrameMem.v) | Symbolic/concrete stack frame memory model (`mc_stack_mem`, load/store disjointness & soundness) |
| [`McIsaCommon.v`](./McIsaCommon.v) | Architecture-neutral bit/word helpers, shared symbolic state, and fuel-bounded traversal utilities |
| [`McFormat.v`](./McFormat.v) | `.mc.cert` S-expression parser, WF checks (`parse_mc_cert_wf`), loop/call spec checks (`[mc-cert-*]`) |

### 4.2 RISC-V (`RV64IMAC`) Semantics & Symbolic Oracle (6 files)

Dependency order: `Rv64Decode.v` $\to$ `Rv64ExecSym.v` $\to$ `Rv64DagProof.v` $\to$ `Rv64SymOracle.v` $\to$ `Rv64LoopSeg.v` $\to$ `Rv64Sem.v`.

| File | Role |
| :--- | :--- |
| [`Rv64Decode.v`](./Rv64Decode.v) | 32-bit RV64IMAC & 16-bit RVC compressed instruction decoder |
| [`Rv64ExecSym.v`](./Rv64ExecSym.v) | Concrete & symbolic RV64 register file and instruction execution semantics (`rv_regfile`) |
| [`Rv64DagProof.v`](./Rv64DagProof.v) | Single-entry acyclic RV64 DAG summarizer (`summarize_rv64_dag_wf`, `summarize_rv64_dag_sound`) |
| [`Rv64SymOracle.v`](./Rv64SymOracle.v) | Step-level symbolic oracle (`rv_step_sym_oracle_sound`) & Sail 128-bit `divrem` width reduction |
| [`Rv64LoopSeg.v`](./Rv64LoopSeg.v) | Loop-segment symbolic execution (`summarize_rv64_seg`) with frame preservation checks |
| [`Rv64Sem.v`](./Rv64Sem.v) | Compatibility facade re-exporting all RV64 semantic modules |

### 4.3 `AArch64` Semantics & Symbolic Oracle (6 files)

Dependency order: `A64Decode.v` $\to$ `A64ExecSym.v` $\to$ `A64DagProof.v` $\to$ `A64SymOracle.v` $\to$ `A64LoopSeg.v` $\to$ `A64CoreSem.v`.

| File | Role |
| :--- | :--- |
| [`A64Decode.v`](./A64Decode.v) | Fixed-width 32-bit AArch64 instruction decoder (`decode_a64_bytes_valid`) |
| [`A64ExecSym.v`](./A64ExecSym.v) | Concrete & symbolic AArch64 register/flag/SP execution semantics (`a64_regfile`, `a64_flags`) |
| [`A64DagProof.v`](./A64DagProof.v) | Single-entry acyclic AArch64 DAG summarizer (`summarize_a64_dag_wf`, `summarize_a64_dag_sound`) |
| [`A64SymOracle.v`](./A64SymOracle.v) | Step-level symbolic oracle soundness (`a64_step_sym_oracle_sound`) |
| [`A64LoopSeg.v`](./A64LoopSeg.v) | Loop-segment symbolic execution (`summarize_a64_seg`) with callee-saved register & stack frame checks |
| [`A64CoreSem.v`](./A64CoreSem.v) | Compatibility facade re-exporting all AArch64 semantic modules |

### 4.4 MC Obligations, Structured Loops, Call Summaries & Top-Level MC Validator (10 files)

```text
McOblDischarger.v ---> (McLoopIrSpec.v --> McLoopCheck.v --> McLoop.v)
                  \--> (McCallSpec.v --> McCallMcWitness.v --> McCallIrExec.v --> McCall.v)
McLoop.v + McCall.v + McExprRewrite.v ---> McValidator.v
```

| File | Role |
| :--- | :--- |
| [`McOblDischarger.v`](./McOblDischarger.v) | Shared bit-blast + LRAT obligation builder and checker for MC loops and calls (`[lrat-check]`) |
| [`McLoopIrSpec.v`](./McLoopIrSpec.v) | IR natural-loop specification, cutpoint phis/slots, and segment path reification (`prepare_mc_loop_ir`) |
| [`McLoopCheck.v`](./McLoopCheck.v) | MC loop skeleton validation, register/slot obligation collectors, and LRAT CNF assembly |
| [`McLoop.v`](./McLoop.v) | Compositional loop soundness for RV64 and AArch64 (`validate_mc_loop_{rv64,a64}_sound`) |
| [`McCallSpec.v`](./McCallSpec.v) | Call-aware RV64/AArch64 decoders, ABI/callee contract checkers, and call-tree specifications |
| [`McCallMcWitness.v`](./McCallMcWitness.v) | Call-tree symbolic execution and witness extraction over machine code (`[mc-call-mc]`) |
| [`McCallIrExec.v`](./McCallIrExec.v) | IR call-tree symbolic reification (`[mc-call-ir]`) and argument/return obligation collection |
| [`McCall.v`](./McCall.v) | Call soundness & caller/callee composition (`validate_mc_call_*_sound`, `compose_*_caller_callee_sound`) |
| [`McExprRewrite.v`](./McExprRewrite.v) | Machine-code DAG-to-IR expression flattening, normalization & algebraic/LRAT refinement bridges |
| [`McValidator.v`](./McValidator.v) | Top-level ELF64 + IR-to-MC validator (`validate_mc_tle_with_cert_str_sound`, `emit_mc_dimacs_cnf_str`) |

---

## 5. Kernel Audit Gate & Axiom Contract

| File | Role |
| :--- | :--- |
| [`CheckAssumptions.v`](./CheckAssumptions.v) | Top-level `Check @...` audit gate importing both `CertPasses` and `CertValidator` theorems |

Enforced in CI ([`rocq-ci.yml`](../.github/workflows/rocq-ci.yml)) via `rocq check -silent -o` and a `26`-theorem `Print Assumptions` batch audit:

1. **Zero-Axiom Tier (`Closed under the global context`, 8 validator theorems):**
   - `LratCore.check_lrat_unsat_sound`
   - `CertFormat.validate_dimacs_lrat_str_sound`
   - `Elf64Spec.elf64_extract_func_sound`, `Elf64Spec.elf64_extract_func_with_calls_sound`
   - `McFormat.parse_mc_cert_wf`
   - `Rv64DagProof.summarize_rv64_dag_wf`, `A64DagProof.summarize_a64_dag_wf`
   - `Rv64SymOracle.sail_divrem_128_width_reduce`
2. **Validator Soundness Tier (`<= vellvm_base \ {Eqdep.Eq_rect_eq.eq_rect_eq}`, 13 theorems):**
   - `AlgRules.check_expr_refines_with_lrat_sound`, `CertValidator.validate_tle_pair_with_cert_str_sound`
   - `Rv64DagProof.summarize_rv64_dag_sound`, `A64DagProof.summarize_a64_dag_sound`
   - `Rv64SymOracle.rv_step_sym_oracle_sound`, `A64SymOracle.a64_step_sym_oracle_sound`
   - `McLoop.validate_mc_loop_rv64_sound`, `McLoop.validate_mc_loop_a64_sound`
   - `McCall.validate_mc_call_rv64_sound`, `McCall.validate_mc_call_a64_sound`
   - `McCall.compose_rv64_caller_callee_sound`, `McCall.compose_a64_caller_callee_sound`
   - `McValidator.validate_mc_tle_with_cert_str_sound`
3. **Integrity invariants:** `0` `Admitted`/`admit`/`give_up`, `0` custom axioms, and `0` unapproved `eq_rect_eq` uses in validators ([`verify_repo_integrity.py`](../scripts/verify_repo_integrity.py)).
