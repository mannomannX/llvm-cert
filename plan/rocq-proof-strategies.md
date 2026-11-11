# Rocq 9.1 & Vellvm 3.0 Fast-Compute Proof Strategy Playbook

This living knowledge base collects **fast-computing, extraction-clean, kernel-friendly proof strategies** for LLVMCert (`vellvm/`, `passes/`, `validator/`), grounded directly in the Vellvm 3.0 (`main`) codebase under [`vellvm/src/rocq/`](../vellvm/src/rocq).

> **How Agents Use & Extend This Playbook**
> 1. **Before writing or repairing `.v` proofs:** Read the relevant `[PS-XX]` strategies below — starting with **`[PS-09]`** (semantic layer selection) and **`[PS-10]`** (pass vs. validator architecture).
> 2. **When a proof step or `Qed.` takes > 2 seconds:** Profile with `Time` (`[PS-07]`) and apply `[PS-02]` / `[PS-11]` instead of brute-force tactic search.
> 3. **Continuous Learning Loop:** Whenever you discover a reusable lemma pattern or tactic speedup that cuts proof checking time or shrinks extracted OCaml code, append a concise `[PS-XX]` entry at the bottom of this file.

---

## Core Strategies

### `[PS-01]` Computational Reflection (`bool` Checkers + Single Soundness Theorem)
- **Context:** Phase 2 fallback analyses (`passes/`) and Phase 3 translation validation (`validator/` / `cert-validator`).
- **Anti-Pattern:** Constructing per-program `Prop` derivations via heavy `Ltac` search or dependent types (`{ tgt | refines src tgt }`). Proof terms grow super-linearly and stall `Qed.`.
- **Fast Strategy:**
  1. Write the transformation or certificate checker as a pure, total `bool` / `option` function:
     `check_block_cert (src tgt : block dtyp) (c : cert) : bool`.
  2. Prove **once** at compiler build time:
     `Theorem check_block_cert_sound : forall src tgt c, check_block_cert src tgt c = true -> refines_block src tgt.`
  3. Decompose complex boolean checks into small `&&` conjunctions and prove one helper lemma per conjunct using `Bool.andb_true_iff` rather than destructing a 20-way nested `match` in one monolithic proof.

### `[PS-02]` Sub-Second `Qed.` Hygiene (Avoiding Proof-Term & Reduction Blowup)
- **Context:** Arithmetic, bitwidth (`32`, `64`, `128`), and error-message proofs across `Numeric/`, `Semantics/Operations/`, `passes/`, and `validator/`.
- **Anti-Pattern:** Calling bare `cbn` / `simpl` on `two_power_pos 64` or error branches like `raiseUB ("..." ++ show x)`, leaving huge unary/binary or `Ascii`/`String` terms in hypotheses that the Rocq kernel re-normalizes at `Qed.`.
- **Fast Strategy:**
  - Rely on Vellvm's memoized width tables (`two_power_pos_memo`, `half_two_power_pos_memo`, `pos_to_nat_memo` in [`Integers.v`](../vellvm/src/rocq/Numeric/Integers.v)) and rewrite via `modulus_def` / `half_modulus_def` **only** when needed.
  - Pre-evaluate closed constants cleanly before `lia` using the [`Floats.v`](../vellvm/src/rocq/Numeric/Floats.v) pattern:
    ```coq
    Ltac compute_this val :=
      let x := fresh in set val as x in *; vm_compute in x; subst x.
    ```
  - Generalize string error payloads before case splitting using `forget_strings` or `hide_strings'` from [`Tactics.v`](../vellvm/src/rocq/Utils/Tactics.v).
  - Restrict reduction locally via `cbn -[fn1 fn2]` or `#[local] Arguments fn : simpl never` (cf. [`Equational.v`](../vellvm/src/rocq/Theory/Equational.v)) — never global `Strategy opaque` (see Rejected Anti-Patterns below).
  - Wrap heavy leaf arithmetic obligations in `abstract (zify; lia)` so Rocq caches them as opaque helper constants and never re-expands them inside outer `destruct` branches.

### `[PS-03]` Width-Indexed Machine Integers (`@bit_int w`)
- **Context:** Vellvm 3.0 replaced CompCert's separate `Int`/`Int64` functors with width-indexed `Context {wordsize: positive}` (`@bit_int w` in [`Integers.v`](../vellvm/src/rocq/Numeric/Integers.v)).
- **Fast Strategy:**
  - Always pin width typeclasses explicitly (`@repr 32`, `@unsigned 64`, `@modulus 32`) when multiple bitwidths (`1`, `8`, `32`, `64`) appear in the same goal; implicit `{wordsize}` resolution otherwise backtracks or picks the wrong hypothesis width.
  - When matching numeral width patterns like `DVALUE_I 32 x` (which compile to structural binary `xI`/`xO`/`xH` matches rather than `Pos.eq_dec`), discharge impossible bit branches structurally using the `narrow_sz` pattern from [`I2F_interp.v`](../vellvm/src/rocq/Theory/I2F/I2F_interp.v).
  - For bitwise identities (`and`, `or`, `xor`, `shl`, `shru`, `zero_ext`, `sign_ext`), discharge goals in one step via `Integers.bit_solve` (`apply same_bits_eq; intros; autorewrite with bit_ints; auto with bool`) instead of unfolding `Z_mod_modulus`.

### `[PS-04]` Interaction Trees (`ITree`), `Equational.v` & Cut-Aware Refinement (`ruttc`)
- **Context:** Proving pass and validator soundness over Vellvm 3.0's `CFGtop` (`itree CFGEtop`), `MCFGtop` (`itree MCFGEtop`), and `MCFGbot` (`itree MCFGEbot`) trees in [`LLVMEvents.v`](../vellvm/src/rocq/Semantics/LLVMEvents.v) and [`Denotation.v`](../vellvm/src/rocq/Semantics/Denotation.v) (`SemNotations`: `⟦ c ⟧c`, `⟦ phi ⟧Φ from`, `⟦ bk ⟧b`, `⟦ bks ⟧bs` in [`Notations.v`](../vellvm/src/rocq/Semantics/Notations.v)). *(Note: Vellvm 3.0 replaced legacy Vellvm 2.x `L0..L4` layers with `CFGEtop -> MCFGEtop -> MCFGEbot`.)*
- **Anti-Pattern:**
  1. Calling `unfold ITree.bind` or `cbn` on `ITree.iter` / `denote_ocfg`, exposing raw `observe` / `_bind` cofixpoint internals.
  2. Attempting to prove symmetric `eutt eq` (`≈`) for passes that fold `poison` or eliminate source UB (`sccp`, `mem2reg`, `cert-validator`) — `eutt eq` fails whenever the source raises `ThrowUB` and the optimized target returns a defined value.
- **Fast Strategy:**
  - **Use `eutt eq` (`≈`) / `eq_itree eq` (`≅`) for pure structural rewrites:** Step via `bind_ret_l`, `bind_ret_r`, `bind_bind`, `translate_bind`, and [`Equational.v`](../vellvm/src/rocq/Theory/Equational.v) (`denote_code_cons`, `denote_code_app`, `denote_code_singleton`, `denote_phi_hd`, `denote_phi_tl`, `denote_no_phis`, `denote_block_unfold`, `denote_ocfg_unfold_in`, `denote_ocfg_app`, `denote_ocfg_flow_left`, `denote_ocfg_prefix`).
  - **Use `ruttc cutUB` for UB/poison-refining passes & validation:** Instantiate `ruttc` from [`rutt_cutoff.v`](../vellvm/src/rocq/Utils/rutt_cutoff.v) with `cutUB` on the source (left) tree (`EqCutL` immediately discharges any branch where the source emits `ThrowUB`, mirroring [`Refinement.v`](../vellvm/src/rocq/Theory/I2F/Refinement.v)). Rewrite both sides of a `ruttc` goal by `eutt eq` / `eq_itree eq` / `euttge eq` via `ruttc_eutt`, `gruttc_cong_eq_itree`, and `gruttc_cong_euttge`.
  - **Eliminate coinduction wherever possible:**
    - Straight-line code (`⟦ c ⟧c`): use list induction + `denote_code_app` / `denote_code_cons`.
    - CFG postconditions / reachability invariants: use `denote_ocfg_has_post_strong` (`⤳` / `HasPost` in [`Equational.v`](../vellvm/src/rocq/Theory/Equational.v)) instead of manual `pcofix`.
    - Loop simulations (`denote_ocfg` / `ITree.iter`): apply the pre-proved combinators `KTreeFacts.eutt_iter_gen` or `ruttc_iter` ([`rutt_cutoff.v`](../vellvm/src/rocq/Utils/rutt_cutoff.v)), reserving raw `gpaco` (`ginit; gcofix CIH; guclo ruttc_clo_bind`) strictly for CFG transformations that alter loop back-edge structure (e.g., block coalescing or loop unrolling).

### `[PS-05]` Extraction-Clean Decidable Equality & Finite Maps (`rmap` / `IntMap`)
- **Context:** Executable Rocq code in `passes/` and `validator/` extracted via [`Extract.v`](../vellvm/src/ml/extracted/Extract.v).
- **Anti-Pattern:**
  1. Building `{x = y} + {x <> y}` deciders with heavy tactics or `Program Fixpoint` inside extracted pass code.
  2. Sealing computational `{x = y} + {x <> y}` deciders with `Qed.` instead of `Defined.` (fixed in [`DynamicValues.v`](../vellvm/src/rocq/Semantics/DynamicValues.v) under `F-10`).
- **Fast Strategy:**
  - Write all pass/validator syntax & lattice comparators as **transparent structural `bool` functions** (`Pos.eqb`, `N.eqb`, `Z.eqb`, `String.eqb`, `RawIDOrd`) paired with separate `Qed.` reflection lemmas (`foo_eqb_spec : foo_eqb x y = true <-> x = y`).
  - Use Vellvm's AVL finite maps directly: `rmap` (`RawIdMaps.RM` in [`RawIdMaps.v`](../vellvm/src/rocq/Syntax/RawIdMaps.v)) for SSA `raw_id` environments/lattices ($O(\log N)$ lookup vs. quadratic association lists) and `IntMap` ([`IntMaps.v`](../vellvm/src/rocq/Utils/IntMaps.v)) for `Z`-keyed tables.
  - When relating `handle_local` / `handle_global` (`Maps.lookup`) to `RM.find` (`rid_lookup`), **always** `rewrite Maps_lookup_rid_lookup` ([`RawIdMaps.v`](../vellvm/src/rocq/Syntax/RawIdMaps.v)) rather than `replace ... by reflexivity` (which can stall leaving the `ExtLib.Map` instance unresolved), and track relational environment invariants with `RM_Refine` (`RM_Refine_empty`, `RM_Refine_add`, `RM_Refine_lookup`) and `IM_Refine`.
  - Keep proof-only invariants in external `Prop` predicates (`wf_ocfg_bid` in [`ScopeTheory.v`](../vellvm/src/rocq/Syntax/ScopeTheory.v)) so extraction erases them completely.

### `[PS-06]` Fuel-Bounded Iteration Over Well-Founded `Program Fixpoint`
- **Context:** Dataflow fixpoints (`sccp`, dominator / `mem2reg` analysis, `simplifycfg` block coalescing, bounded `inline`).
- **Fast Strategy:**
  - Parameterize iterative passes/analyses by explicit `fuel : nat` (e.g., `List.length cfg.(blks) + 1`).
  - When `fuel = 0`, return the unmodified input CFG (sound by reflexivity) or `None` / `false` (validator rejects and falls back to Safe-Path).
  - This eliminates well-founded termination proof obligations (`Acc` / `measure`) completely: prove **one single-step preservation lemma** `forall g, refines_cfg g (step g)`, and `refines_cfg g (iterate fuel step g)` follows by 5-line `induction fuel` in `< 0.05s`.

### `[PS-07]` Incremental Single-File Verification, `-vos`/`-vok` & `Time` Profiling (User Rule 4)
- **Context:** Local agent / developer edit-compile loop on `.v` files.
- **Anti-Pattern:** Running full `make -C vellvm/src -j` (85+ `.v` files + OCaml extraction) after every tactic edit, or guessing which tactic caused a slow `Qed.`.
- **Fast Strategy:**
  - Build upstream `.vo` dependencies once, then compile **only** the modified target file with `-time` enabled to catch any step exceeding `2.0s`:
    ```bash
    rocq compile -time $(make -s -C vellvm/src print-includes) vellvm/src/rocq/Path/To/Target.v
    ```
  - Use `-vos` (`rocq compile -vos ...`) to check downstream statement/interface compatibility in milliseconds while skipping `Qed.` bodies, and `-vok` (`rocq compile -vok ...`) to verify opaque proof bodies independently in parallel.
  - Run full `make -C vellvm/src` + `python scripts/verify_repo_integrity.py` only after completing a coherent logical task group.

### `[PS-08]` Zero-Axiom Hygiene & Independent Kernel Gate (`rocq check`)
- **Context:** TCB integrity across `vellvm/`, `passes/`, and `validator/` (`rocq-ci.yml`).
- **Anti-Pattern:** Importing `ITree.Eq.EqAxiom`, `JMeq`, or `ProofIrrelevance` (remediated across `Tactics.v`, `IPtrFinite.v`, and `I2F_exp.v` under `F-09`).
- **Fast Strategy:**
  - Never leave `Admitted`, `admit`, `give_up`, `Abort`, unapproved `Axiom`s, or `EqAxiom`/`JMeq`/`ProofIrrelevance` imports in any `.v` file (`scripts/verify_repo_integrity.py` rejects all of them in `< 0.5s`).
  - **Constructive dependent-pair & range-proof idioms:**
    - Never re-introduce `ITree.Eq.EqAxiom.bisimulation_is_eq` (`force_rewrite`) — rewrite modulo `eq_itree` / `eutt` / `ruttc` Proper morphisms instead.
    - `subst_existT` in [`Tactics.v`](../vellvm/src/rocq/Utils/Tactics.v) uses constructive Hedberg UIP (`Eqdep_dec.inj_pair2_eq_dec` over `positive`, `N`, `Z`, `nat`, `bool` — 100% axiom-free).
    - For decidable machine-integer range proofs (`intrange`), use constructive `Integers.mkint_eq` (`Integers.eq_proofs_unicity`) rather than `Stdlib.Logic.ProofIrrelevance`.
  - Before closing any milestone, run `Print Assumptions TopLevelTheorem.` and ensure `rocq check -o` in `rocq-ci.yml` covers `TopLevel`, `Equational`, and all new top-level `passes` / `validator` modules.

---

## Vellvm 3.0 Architecture & Rocq 9.1 Acceleration Strategies

### `[PS-09]` Stratified Semantic Level Selection (Never Unfold `FusedS` / Memory Bytes Unnecessarily)
- **Context:** Choosing the semantic layer in Vellvm 3.0 at which to state and prove each Phase 2 pass (`simplifycfg`, `dce`, `sccp`, `inline`, `mem2reg`) and Phase 3 `cert-validator` rule.
- **Anti-Pattern:** Stating pass lemmas directly over expanded `interp_mcfg` (`FusedS = state * ((stack_frame * stack) * global_env)` in [`InterpretationStack.v`](../vellvm/src/rocq/Semantics/InterpretationStack.v)) and unfolding [`Implementations/Memory.v`](../vellvm/src/rocq/Semantics/Implementations/Memory.v) / [`MemoryBytes.v`](../vellvm/src/rocq/Semantics/MemoryBytes.v) when the pass never touches memory!
- **Fast Strategy:** Prove each transformation at the **highest (most uninterpreted) semantic layer** that interprets *only* the events modified by that pass, then lift once to `interp_mcfg` via generic handler morphism lemmas (mirroring `I2F_interp_intrinsics` + `ruttc_interp_state_specialized` in [`I2F_interp.v`](../vellvm/src/rocq/Theory/I2F/I2F_interp.v)):

  | Pass / Validator Component | Target Semantic Layer in Vellvm 3.0 | Events Interpreted | Events Kept Uninterpreted |
  | :--- | :--- | :--- | :--- |
  | **`simplifycfg`** (unreachable blocks, jump threading, block merge) | Uninterpreted `CFGtop` (`⟦ bks ⟧bs` in [`Equational.v`](../vellvm/src/rocq/Theory/Equational.v)) | None (pure `ITree` + `Phi` assoc laws) | All (`CallE`, `LocalE`, `MemoryE`, ...) |
  | **`dce`, `sccp`, & `cert-validator` scalar/CFG rules** | `EOU` + `LocalE` (`handle_local` / `fused_local` over `rmap dvalue`) | `LocalE` (via `RM_Refine` on live `raw_id`s) + `cutUB` | `MemoryE`, `GlobalE`, `StackE`, `CallE`, `ExternalCallE` (memory component of `FusedS` stays opaque & `eq`) |
  | **`inline`** (bounded non-recursive call inlining) | `denote_mcfg` (`mrec` over `CallE`) + `LocalE +' StackE` ([`Handlers/Stack.v`](../vellvm/src/rocq/Semantics/Handlers/Stack.v)) | `CallE`, `LocalE`, `StackE` (+ `MemPush`/`MemPop` frame balance) | Byte-level `Alloca`/`Load`/`Store` heap representation |
  | **`mem2reg` & `cert-validator` load/store forwarding** | `LocalE` + `memS` free monad / `MemoryModelPrimitives` ([`Interfaces/Memory.v`](../vellvm/src/rocq/Semantics/Interfaces/Memory.v), [`I2F_memS.v`](../vellvm/src/rocq/Theory/I2F/I2F_memS.v)) | `LocalE` + `MemoryE` (frame invariant separating unescaped `alloca` blocks from rest of memory, lifted via `memM_interp`) | `ExternalCallE`, `GlobalE` |

### `[PS-10]` CompCert-Style Self-Validating Passes (Untrusted Rocq Compute + Verified `bool` Checker)
- **Context:** Complex global analyses and transformations in Phase 2 (`mem2reg` dominance/$\phi$-placement, `sccp` sparse worklist, alias/forwarding checks) under the strict `<= 750 LOC` handwritten OCaml TCB cap.
- **Anti-Pattern:** Directly proving functional correctness of Lengauer-Tarjan dominators, iterated dominance frontiers, or sparse SSA worklists by induction over algorithm internals (8,000–15,000 LOC of brittle Rocq per pass).
- **Fast Strategy (Apriori Translation Validation Inside Pure Rocq):**
  1. Implement **both** the fast fuel-bounded optimizer/analyzer `compute_pass : cfg dtyp -> cfg dtyp * witness` **and** a compact boolean validator `check_pass : cfg dtyp -> cfg dtyp -> witness -> bool` in pure Rocq (consuming **0 LOC** of handwritten OCaml TCB).
  2. Wrap them with total fallback on validation failure:
     ```coq
     Definition verified_pass (src : cfg dtyp) : cfg dtyp :=
       let '(tgt, w) := compute_pass src in
       if check_pass src tgt w then tgt else src.
     ```
  3. Prove **only** `check_pass_sound : forall src tgt w, check_pass src tgt w = true -> refines_cfg src tgt` (~5–10x smaller proof: e.g., checking a post-fixpoint of dataflow equations for `sccp`, or checking non-escaping `alloca` uses + per-block symbolic store-to-register substitution for `mem2reg`). The `false` branch returns `src` and discharges in 1 line by reflexivity!
  4. **Reuse Across Phases:** Structure `check_pass` predicates modularly so Phase 3 (`validator/` / `cert-validator`) imports the exact same verified block/SSA/memory checker lemmas to validate `Z3` witnesses.

### `[PS-11]` Taming `setoid_rewrite`, `Proper`, & `ReSum` (`-<`) Typeclass Divergence
- **Context:** Rewriting `ITree` computations over Vellvm's 12-summand `CFGEtop` / 11-summand `MCFGEtop` signatures ([`LLVMEvents.v`](../vellvm/src/rocq/Semantics/LLVMEvents.v)).
- **Anti-Pattern:**
  1. Running `repeat setoid_rewrite ...` under deep `ITree.bind (fun x => ...)` continuations, triggering exponential `Proper` + `pointwise_relation` + `ReSum` (`-<`) typeclass search at every AST node.
  2. Declaring `Variable Pa : Params` as a section variable instead of `Context {Pa : Params}`, which causes `ReSum` (`-<`) typeclass resolution and even `reflexivity` to **diverge** (documented in [`I2F_exp.v`](../vellvm/src/rocq/Theory/I2F/I2F_exp.v) lines 65–71).
- **Fast Strategy:**
  - **Peel binds instead of rewriting under binders:** Rewrite at the head of `ITree.bind t k` with plain `rewrite` (where `Proper` needs no `pointwise_relation`), then step into the continuation via `eqbind` (`apply eutt_eq_bind; intros`, [`Equational.v`](../vellvm/src/rocq/Theory/Equational.v)) or `rbind R` / `erbind` (`eapply ruttc_bind`, [`I2F_exp.v`](../vellvm/src/rocq/Theory/I2F/I2F_exp.v)).
  - **Seal heavy denotations from typeclass unification:** Add `#[local] Typeclasses Opaque denote_exp denote_instr denote_code denote_block denote_ocfg interp_state.` in pass/validator proof files so failed `Proper` lookups fail in `< 1ms` instead of unfolding entire VIR denotations.
  - **Keep `{Pa : Params}` as a `Context` typeclass instance** (or instantiate concretely to `PInf` / `PFin`), normalize `subevent` injections explicitly with `cbnn` (`cbn; unfold resum, ReSum_id, id_, Id_IFun`), and define composite event relations (`prerel`/`postrel`) via **`match` functions** (`Refinement.sum_prerel` in [`Refinement.v`](../vellvm/src/rocq/Theory/I2F/Refinement.v)) rather than nested `Variant` constructors so `cbn` reduces an 11-way event dispatch in one step.

### `[PS-12]` Pure `EOU` / `EOUP` Factoring Before `ITree` Lifting
- **Context:** Phase 2.1 LLVM 23 instruction flags (`zext nneg`, `or disjoint`, `trunc nuw/nsw`, `icmp samesign`, `gep nusw/nuw`), `sccp` constant-folding soundness, and Phase 3 `cert-validator` instruction transfer rules.
- **Anti-Pattern:** Proving arithmetic, comparison, `select`, `gep`, or value-attribute refinements directly on `denote_exp` `ITree`s, repeating monad/event plumbing in every case split.
- **Fast Strategy:**
  - In Vellvm 3.0, nearly all expression semantics in [`Operations/`](../vellvm/src/rocq/Semantics/Operations) and [`Attributes.v`](../vellvm/src/rocq/Semantics/Attributes.v) live in the **pure inductive monads `EOU` and `EOUP`** (`raise_ret | raise_error | raise_oom | raise_ub` in [`EOU.v`](../vellvm/src/rocq/Semantics/EOU.v)), lifted into `itree` only at the end via `EOU_to_itree`.
  - Define a pure `EOU` refinement relation (e.g., `refine_EOU RR m_src m_tgt` allowing `raise_ub` on the left to refine any `m_tgt` and poison to refine defined `dvalue`s, analogous to `I2F_EOU` / `I2F_EOUP` in [`Refinement.v`](../vellvm/src/rocq/Theory/I2F/Refinement.v)).
  - Prove all operator/flag/constant-folding lemmas purely inside `EOU` by simple `destruct` (`< 0.05s` per lemma, zero `ITree` / `paco` imports), and lift them to `CFGtop` / `MCFGtop` in a single step via a generic `EOU_to_itree` lifting lemma (cf. `I2F_refine_lift_gen` in [`Refinement.v`](../vellvm/src/rocq/Theory/I2F/Refinement.v)).

### `[PS-13]` Rocq 9.1 Proof-Script & `Equations` Discipline (`Goal Selector "!"`, `#[local]`, `Proof using.`)
- **Context:** Authoring maintainable, parallel-compilable Rocq 9.1 modules in `passes/` and `validator/`.
- **Fast Strategy:**
  - **Header boilerplate for every new file in `passes/` and `validator/`:**
    ```coq
    Set Default Goal Selector "!".
    Set Implicit Arguments.
    ```
    `Set Default Goal Selector "!"` forces explicit bullets (`-`, `+`, `*`) or goal selectors (`1:`), preventing AST extensions (such as Phase 2.1 LLVM 23 flags) from silently broadcasting expensive automation (`lia`, `eauto`) across unexpected subgoals.
  - **Always close section proofs with `Proof using ...` (or `Proof using Type.`):** Prevents Rocq from over-generalizing unused section hypotheses at `Qed.` and is required for fast `-vos` / `-vok` parallel checking (`[PS-07]`).
  - **Strict `#[local]` attribute scoping & selective `Require`:** Never add bare `Hint Resolve`, `Hint Rewrite`, `Hint Unfold`, or `Opaque` (which leak globally across downstream imports; note `_RocqProject` lines 4–5). Always prefix with `#[local]` (or `#[export]` inside a dedicated `*Hints` module), and prefer `From Vellvm Require Syntax.CFG Theory.Equational` over importing umbrella modules you do not need.
  - **`Equations` (`rocq-equations`) scope:** Use `Equations` strictly for **indexed `Prop` relations** (`prerel` / `postrel` over `CallE T` / `MemoryE T`, stepped via `simp RelName` as in [`Refinement.v`](../vellvm/src/rocq/Theory/I2F/Refinement.v)) and `depelim` in proofs — **never** for executable functions extracted to OCaml (where `Equations` obligation dictionaries bloat extracted code; use plain `Fixpoint` + explicit `fuel` per `[PS-06]`).

---

## Evaluated & Rejected Anti-Patterns (Do Not Re-Introduce)

| Candidate Technique | Verdict | Reason |
| :--- | :---: | :--- |
| Global `Strategy opaque [ITree.bind denote_block]` | **Rejected** | Blocks Rocq **kernel conversion** (not just `cbn`/typeclass search), breaking `Qed.` on lemmas that rely on definitional equality (`denote_code_cons`, `Maps_lookup_rid_lookup`). Use `#[local] Typeclasses Opaque`, `#[local] Arguments ... : simpl never`, and `cbn -[...]` instead. |
| `force_rewrite` / `subst_existT` from `Utils/Tactics.v` | **Rejected** | Silently pulls `ITree.Eq.EqAxiom.bisimulation_is_eq` and `JMeq.JMeq_eq` into `Print Assumptions` (`F-09`). Use `eutt`/`ruttc` rewriting and `Eqdep_dec.inj_pair2_eq_dec`. |
| `Equations` with `wf` / `measure` on extracted pass code | **Rejected** | Generates `FunctionalElimination` / well-foundedness dictionary overhead in extracted OCaml and slows `Qed.`; explicit `fuel : nat` (`[PS-06]`) + self-validation (`[PS-10]`) is faster and zero-overhead. |
| Custom `PropT` / `ctree` nondeterministic memory stack in Phase 2 | **Rejected** | Upstream Vellvm 3.0 has not yet plugged in `memM_model` (see [`Theory/I2F/README.md`](../vellvm/src/rocq/Theory/I2F/README.md)). Proving `mem2reg` against the `memS` free-monad interface (`[PS-09]`) already decouples proofs from `memM_interp` without violating YAGNI. |
| External SMT/hammer plugins (`CoqHammer`, `Mtac2`) inside Rocq | **Rejected** | Outside `rocq-vellvm.opam`, slows CI caching, and unnecessary when `bool` reflection (`[PS-01]`), `zify; lia` (`[PS-02]`), and `Integers.bit_solve` (`[PS-03]`) discharge leaf obligations deterministically in `< 50ms`. |
