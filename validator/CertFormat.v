(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Canonical [cert-v1] Certificate AST, Total S-Expression Parser, and Syntax/Contract Gates

    Defines:
    1. The complete Rocq AST for [cert-v1] translation-validation certificates
       ([cert_binop], [cert_icmp_pred], [cert_cast_kind], [cert_expr] with
       [CE_Let] DAG bindings, [ub_assumption], [value_equivalence],
       [memory_invariant], [return_obligation], [loop_cutpoint_invariant],
       [alias_witness], [block_certificate], [proof_certificate]), together with
       computable bitwidth/well-formedness predicates and decidable equality.
    2. A total, extraction-ready S-expression lexer and bounded-depth stack
       parser ([parse_sexp], [parse_cert]) enforcing canonical integer,
       64-character lowercase SHA-256 hex, and closed [$n0..] [CE_Let] scoping
       invariants, backed by [parse_cert_wf].
    3. Computable IR syntax and prototype contract soundness gates
       ([check_validator_syntax_gates], [check_prototype_contract]) enforcing
       [F-17] (no target fast-math flags), [F-18] (no volatile/atomic/ordering
       or fences), [F-19]/[F-32]/[F-60] (matching prototype/calling-convention/
       ABI/function attributes, forbidding target-invented [noreturn]/
       [nocreateundeforpoison]/[nounwind]/[memory] attributes, and rejecting
       unmodeled [byval]/[inalloca]/[preallocated]/[byref]/[initializes]/
       [naked]/[strictfp]/[returns_twice]), [F-21] (no target-invented [gep]
       [inbounds]/[nusw]/[nuw] flags), [F-39] (no target-invented FP-to-integer
       [bitcast] exposing NaN payload bits), and [F-30]/[F-31]/[F-34] (verified
       intrinsic allowlist, non-variadic IR, and no [invoke]/[landingpad]/
       [resume]), together with [Qed.] inversion lemmas for every gate. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Number
  Decimal
  Hexadecimal
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require Import
  Utils
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Semantics.Attributes
  Semantics.IntrinsicsDefinitions.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  AigLrat.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments N.shiftl : simpl never.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Z.gtb _ _ : simpl nomatch.
#[local] Arguments Z.geb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Canonical [cert-v1] Certificate AST *)

Definition is_supported_bit_width (w : positive) : bool :=
  match w with
  | 1%positive | 8%positive | 16%positive
  | 32%positive | 64%positive | 128%positive => true
  | _ => false
  end.

Variant cert_binop : Set :=
| CB_Add
| CB_Sub
| CB_Mul
| CB_UDiv
| CB_SDiv
| CB_URem
| CB_SRem
| CB_Shl
| CB_LShr
| CB_AShr
| CB_And
| CB_Or
| CB_Xor.

Record cert_binop_flags : Set :=
  mk_cert_binop_flags {
    cbf_nuw : bool;
    cbf_nsw : bool;
    cbf_exact : bool;
    cbf_disjoint : bool;
  }.

Definition no_binop_flags : cert_binop_flags :=
  mk_cert_binop_flags false false false false.

Variant cert_icmp_pred : Set :=
| CIP_Eq
| CIP_Ne
| CIP_Ult
| CIP_Ule
| CIP_Ugt
| CIP_Uge
| CIP_Slt
| CIP_Sle
| CIP_Sgt
| CIP_Sge.

Variant cert_cast_kind : Set :=
| CCK_ZExt
| CCK_SExt
| CCK_Trunc.

Record cert_cast_flags : Set :=
  mk_cert_cast_flags {
    ccf_nneg : bool;
    ccf_nuw : bool;
    ccf_nsw : bool;
  }.

Definition no_cast_flags : cert_cast_flags :=
  mk_cert_cast_flags false false false.

Unset Elimination Schemes.
Inductive cert_expr : Set :=
| CE_BvConst (bit_width : positive) (value : N)
| CE_Poison (bit_width : positive)
| CE_Var (name : string) (bit_width : positive)
| CE_BinOp (op : cert_binop) (bit_width : positive) (flags : cert_binop_flags)
           (lhs rhs : cert_expr)
| CE_ICmp (pred : cert_icmp_pred) (samesign : bool) (operand_width : positive)
          (lhs rhs : cert_expr)
| CE_Cast (kind : cert_cast_kind) (from_width to_width : positive)
          (flags : cert_cast_flags) (operand : cert_expr)
| CE_Select (bit_width : positive) (cond true_val false_val : cert_expr)
| CE_Freeze (bit_width : positive) (operand : cert_expr)
| CE_Let (bindings : list (string * cert_expr)) (body : cert_expr).
Set Elimination Schemes.

Section CertExprInd.
  Variable P : cert_expr -> Prop.
  Hypothesis H_BvConst : forall w v, P (CE_BvConst w v).
  Hypothesis H_Poison : forall w, P (CE_Poison w).
  Hypothesis H_Var : forall nm w, P (CE_Var nm w).
  Hypothesis H_BinOp : forall op w fl l, P l -> forall r, P r -> P (CE_BinOp op w fl l r).
  Hypothesis H_ICmp : forall pr ss w l, P l -> forall r, P r -> P (CE_ICmp pr ss w l r).
  Hypothesis H_Cast : forall k fw tw fl o, P o -> P (CE_Cast k fw tw fl o).
  Hypothesis H_Select : forall w c, P c -> forall t, P t -> forall f, P f -> P (CE_Select w c t f).
  Hypothesis H_Freeze : forall w o, P o -> P (CE_Freeze w o).
  Hypothesis H_Let : forall bs body,
      Forall (fun p => P (snd p)) bs -> P body -> P (CE_Let bs body).

  Fixpoint cert_expr_ind_nested (e : cert_expr) : P e :=
    match e with
    | CE_BvConst w v => H_BvConst w v
    | CE_Poison w => H_Poison w
    | CE_Var nm w => H_Var nm w
    | CE_BinOp op w fl l r =>
        H_BinOp op w fl l (cert_expr_ind_nested l) r (cert_expr_ind_nested r)
    | CE_ICmp pr ss w l r =>
        H_ICmp pr ss w l (cert_expr_ind_nested l) r (cert_expr_ind_nested r)
    | CE_Cast k fw tw fl o =>
        H_Cast k fw tw fl o (cert_expr_ind_nested o)
    | CE_Select w c t f =>
        H_Select w c (cert_expr_ind_nested c) t (cert_expr_ind_nested t) f (cert_expr_ind_nested f)
    | CE_Freeze w o =>
        H_Freeze w o (cert_expr_ind_nested o)
    | CE_Let bs body =>
        let fix bind_all (xs : list (string * cert_expr))
            : Forall (fun p => P (snd p)) xs :=
            match xs with
            | [] => Forall_nil _
            | (nm, be) :: rest =>
                Forall_cons (nm, be) (cert_expr_ind_nested be) (bind_all rest)
            end in
        H_Let bs body (bind_all bs) (cert_expr_ind_nested body)
    end.
End CertExprInd.

Fixpoint cert_expr_bit_width (e : cert_expr) : positive :=
  match e with
  | CE_BvConst w _ => w
  | CE_Poison w => w
  | CE_Var _ w => w
  | CE_BinOp _ w _ _ _ => w
  | CE_ICmp _ _ _ _ _ => 1%positive
  | CE_Cast _ _ tw _ _ => tw
  | CE_Select w _ _ _ => w
  | CE_Freeze w _ => w
  | CE_Let _ body => cert_expr_bit_width body
  end.

Variant block_cert_kind : Set :=
| BCK_Entry
| BCK_Cutpoint
| BCK_Return.

Variant ub_assumption : Set :=
| UBA_ParamNoUndef (param : string) (bit_width : positive)
| UBA_PtrNonNull (param : string)
| UBA_PtrAligned (param : string) (align : N)
| UBA_PtrDereferenceable (param : string) (bytes : N)
| UBA_LoadNoUndef (slot : string) (bit_width : positive)
| UBA_DivisorNonZero (divisor : cert_expr)
| UBA_SignedDivNoOverflow (lhs rhs : cert_expr)
| UBA_BranchCondDefined (cond : cert_expr)
| UBA_UnreachableEliminated.

Record value_equivalence : Set :=
  mk_value_equivalence {
    ve_src_reg : string;
    ve_tgt_reg : string;
    ve_bit_width : positive;
    ve_src_expr : cert_expr;
    ve_tgt_expr : cert_expr;
  }.

Variant memory_invariant : Set :=
| MI_AllocaPromoted (src_slot : string) (bit_width : positive) (promoted_expr : cert_expr)
| MI_SlotRefines (src_slot tgt_slot : string) (bit_width : positive)
                 (src_expr tgt_expr : cert_expr).

Variant return_obligation : Set :=
| RO_VoidEquiv
| RO_ScalarRefines (bit_width : positive) (src_expr tgt_expr : cert_expr)
                   (smt_verified : bool).

Record loop_cutpoint_invariant : Set :=
  mk_loop_cutpoint_invariant {
    lci_src_header : string;
    lci_tgt_header : string;
    lci_guard : cert_expr;
    lci_value_equivs : list value_equivalence;
    lci_memory_invariants : list memory_invariant;
  }.

Variant alias_relation_kind : Set :=
| ARK_NoAlias
| ARK_MustAlias.

Record alias_witness : Set :=
  mk_alias_witness {
    aw_kind : alias_relation_kind;
    aw_lhs_ptr : string;
    aw_rhs_ptr : string;
  }.

Record block_certificate : Set :=
  mk_block_certificate {
    bc_src_block : string;
    bc_tgt_block : string;
    bc_kind : block_cert_kind;
    bc_ub_assumptions : list ub_assumption;
    bc_value_equivs : list value_equivalence;
    bc_memory_invariants : list memory_invariant;
  }.

Record proof_certificate : Set :=
  mk_proof_certificate {
    pc_function_name : string;
    pc_src_ir_sha256 : string;
    pc_tgt_ir_sha256 : string;
    pc_blocks : list block_certificate;
    pc_loop_invariants : list loop_cutpoint_invariant;
    pc_alias_witnesses : list alias_witness;
    pc_return_obligation : return_obligation;
    pc_lrat_proof : option (list lrat_step);
  }.

(** ** 2. Structural Boolean Comparators & Reflection Lemmas for [cert_expr] *)

Definition cert_binop_eqb (a b : cert_binop) : bool :=
  match a, b with
  | CB_Add, CB_Add | CB_Sub, CB_Sub | CB_Mul, CB_Mul
  | CB_UDiv, CB_UDiv | CB_SDiv, CB_SDiv
  | CB_URem, CB_URem | CB_SRem, CB_SRem
  | CB_Shl, CB_Shl | CB_LShr, CB_LShr | CB_AShr, CB_AShr
  | CB_And, CB_And | CB_Or, CB_Or | CB_Xor, CB_Xor => true
  | _, _ => false
  end.

Lemma cert_binop_eqb_eq : forall a b, cert_binop_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intros H; try reflexivity; discriminate.
Qed.

Definition cert_binop_flags_eqb (a b : cert_binop_flags) : bool :=
  Bool.eqb (cbf_nuw a) (cbf_nuw b) &&
  Bool.eqb (cbf_nsw a) (cbf_nsw b) &&
  Bool.eqb (cbf_exact a) (cbf_exact b) &&
  Bool.eqb (cbf_disjoint a) (cbf_disjoint b).

Lemma cert_binop_flags_eqb_eq : forall a b, cert_binop_flags_eqb a b = true <-> a = b.
Proof.
  intros [nuw1 nsw1 ex1 dj1] [nuw2 nsw2 ex2 dj2]; unfold cert_binop_flags_eqb; cbn.
  rewrite !andb_true_iff, !Bool.eqb_true_iff.
  split.
  - intros (((-> & ->) & ->) & ->); reflexivity.
  - intros H; inversion H; repeat split; reflexivity.
Qed.

Definition cert_icmp_pred_eqb (a b : cert_icmp_pred) : bool :=
  match a, b with
  | CIP_Eq, CIP_Eq | CIP_Ne, CIP_Ne
  | CIP_Ult, CIP_Ult | CIP_Ule, CIP_Ule | CIP_Ugt, CIP_Ugt | CIP_Uge, CIP_Uge
  | CIP_Slt, CIP_Slt | CIP_Sle, CIP_Sle | CIP_Sgt, CIP_Sgt | CIP_Sge, CIP_Sge => true
  | _, _ => false
  end.

Lemma cert_icmp_pred_eqb_eq : forall a b, cert_icmp_pred_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intros H; try reflexivity; discriminate.
Qed.

Definition cert_cast_kind_eqb (a b : cert_cast_kind) : bool :=
  match a, b with
  | CCK_ZExt, CCK_ZExt | CCK_SExt, CCK_SExt | CCK_Trunc, CCK_Trunc => true
  | _, _ => false
  end.

Lemma cert_cast_kind_eqb_eq : forall a b, cert_cast_kind_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intros H; try reflexivity; discriminate.
Qed.

Definition cert_cast_flags_eqb (a b : cert_cast_flags) : bool :=
  Bool.eqb (ccf_nneg a) (ccf_nneg b) &&
  Bool.eqb (ccf_nuw a) (ccf_nuw b) &&
  Bool.eqb (ccf_nsw a) (ccf_nsw b).

Lemma cert_cast_flags_eqb_eq : forall a b, cert_cast_flags_eqb a b = true <-> a = b.
Proof.
  intros [nn1 nuw1 nsw1] [nn2 nuw2 nsw2]; unfold cert_cast_flags_eqb; cbn.
  rewrite !andb_true_iff, !Bool.eqb_true_iff.
  split.
  - intros ((-> & ->) & ->); reflexivity.
  - intros H; inversion H; repeat split; reflexivity.
Qed.

Fixpoint cert_expr_eqb (e1 e2 : cert_expr) {struct e1} : bool :=
  match e1, e2 with
  | CE_BvConst w1 v1, CE_BvConst w2 v2 =>
      Pos.eqb w1 w2 && N.eqb v1 v2
  | CE_Poison w1, CE_Poison w2 =>
      Pos.eqb w1 w2
  | CE_Var n1 w1, CE_Var n2 w2 =>
      String.eqb n1 n2 && Pos.eqb w1 w2
  | CE_BinOp op1 w1 fl1 l1 r1, CE_BinOp op2 w2 fl2 l2 r2 =>
      cert_binop_eqb op1 op2 && Pos.eqb w1 w2 && cert_binop_flags_eqb fl1 fl2 &&
      cert_expr_eqb l1 l2 && cert_expr_eqb r1 r2
  | CE_ICmp pr1 ss1 w1 l1 r1, CE_ICmp pr2 ss2 w2 l2 r2 =>
      cert_icmp_pred_eqb pr1 pr2 && Bool.eqb ss1 ss2 && Pos.eqb w1 w2 &&
      cert_expr_eqb l1 l2 && cert_expr_eqb r1 r2
  | CE_Cast k1 fw1 tw1 fl1 o1, CE_Cast k2 fw2 tw2 fl2 o2 =>
      cert_cast_kind_eqb k1 k2 && Pos.eqb fw1 fw2 && Pos.eqb tw1 tw2 &&
      cert_cast_flags_eqb fl1 fl2 && cert_expr_eqb o1 o2
  | CE_Select w1 c1 t1 f1, CE_Select w2 c2 t2 f2 =>
      Pos.eqb w1 w2 && cert_expr_eqb c1 c2 && cert_expr_eqb t1 t2 && cert_expr_eqb f1 f2
  | CE_Freeze w1 o1, CE_Freeze w2 o2 =>
      Pos.eqb w1 w2 && cert_expr_eqb o1 o2
  | CE_Let bs1 b1, CE_Let bs2 b2 =>
      let fix eqb_binds (xs ys : list (string * cert_expr)) {struct xs} : bool :=
          match xs, ys with
          | [], [] => true
          | (k1, x1) :: rx, (k2, x2) :: ry =>
              String.eqb k1 k2 && cert_expr_eqb x1 x2 && eqb_binds rx ry
          | _, _ => false
          end in
      eqb_binds bs1 bs2 && cert_expr_eqb b1 b2
  | _, _ => false
  end.

Lemma cert_expr_eqb_refl : forall e, cert_expr_eqb e e = true.
Proof.
  induction e as
    [ w v
    | w
    | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested; cbn.
  - rewrite Pos.eqb_refl, N.eqb_refl; reflexivity.
  - apply Pos.eqb_refl.
  - rewrite String.eqb_refl, Pos.eqb_refl; reflexivity.
  - rewrite (proj2 (cert_binop_eqb_eq op op) eq_refl), Pos.eqb_refl,
            (proj2 (cert_binop_flags_eqb_eq fl fl) eq_refl), IHl, IHr; reflexivity.
  - rewrite (proj2 (cert_icmp_pred_eqb_eq pr pr) eq_refl), Bool.eqb_reflx,
            Pos.eqb_refl, IHl, IHr; reflexivity.
  - rewrite (proj2 (cert_cast_kind_eqb_eq k k) eq_refl), !Pos.eqb_refl,
            (proj2 (cert_cast_flags_eqb_eq fl fl) eq_refl), IHo; reflexivity.
  - rewrite Pos.eqb_refl, IHc, IHt, IHf; reflexivity.
  - rewrite Pos.eqb_refl, IHo; reflexivity.
  - rewrite IHb, andb_true_r.
    induction IHbs as [| [k be] rest Hbe _ IHrest]; [reflexivity |].
    cbn in *; rewrite String.eqb_refl, Hbe, IHrest; reflexivity.
Qed.

Lemma cert_expr_eqb_eq : forall e1 e2, cert_expr_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1.
  induction e1 as
    [ w1 v1
    | w1
    | nm1 w1
    | op1 w1 fl1 l1 IHl r1 IHr
    | pr1 ss1 w1 l1 IHl r1 IHr
    | k1 fw1 tw1 fl1 o1 IHo
    | w1 c1 IHc t1 IHt f1 IHf
    | w1 o1 IHo
    | bs1 b1 IHbs IHb ] using cert_expr_ind_nested;
    intros e2; split; intros H;
    try (subst; apply cert_expr_eqb_refl).
  - destruct e2; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hw Hv].
    apply Pos.eqb_eq in Hw; apply N.eqb_eq in Hv; subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    apply Pos.eqb_eq in H; subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hn Hw].
    apply String.eqb_eq in Hn; apply Pos.eqb_eq in Hw; subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    rewrite !andb_true_iff in H.
    destruct H as ((((Hop & Hw) & Hfl) & Hl) & Hr).
    apply cert_binop_eqb_eq in Hop; apply Pos.eqb_eq in Hw;
      apply cert_binop_flags_eqb_eq in Hfl; apply IHl in Hl; apply IHr in Hr.
    subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    rewrite !andb_true_iff in H.
    destruct H as ((((Hpr & Hss) & Hw) & Hl) & Hr).
    apply cert_icmp_pred_eqb_eq in Hpr; apply Bool.eqb_prop in Hss;
      apply Pos.eqb_eq in Hw; apply IHl in Hl; apply IHr in Hr.
    subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    rewrite !andb_true_iff in H.
    destruct H as ((((Hk & Hfw) & Htw) & Hfl) & Ho).
    apply cert_cast_kind_eqb_eq in Hk; apply Pos.eqb_eq in Hfw;
      apply Pos.eqb_eq in Htw; apply cert_cast_flags_eqb_eq in Hfl; apply IHo in Ho.
    subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    rewrite !andb_true_iff in H.
    destruct H as (((Hw & Hc) & Ht) & Hf).
    apply Pos.eqb_eq in Hw; apply IHc in Hc; apply IHt in Ht; apply IHf in Hf.
    subst; reflexivity.
  - destruct e2; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hw Ho].
    apply Pos.eqb_eq in Hw; apply IHo in Ho; subst; reflexivity.
  - destruct e2 as [| | | | | | | | bs2 b2]; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hbs Hb].
    apply IHb in Hb; subst b2; f_equal.
    revert bs2 Hbs.
    induction IHbs as [| [k1 x1] rx IHx _ IHrx]; intros [| [k2 x2] ry] Hbs;
      try discriminate; [reflexivity |].
    rewrite !andb_true_iff in Hbs; destruct Hbs as ((Hk & Hx) & Hrest).
    apply String.eqb_eq in Hk; apply IHx in Hx; subst k2 x2.
    f_equal; apply IHrx, Hrest.
Qed.

(** ** 3. Well-Formedness of [cert_expr] and [proof_certificate] ([E-10] Closed Let-DAGs) *)

Definition is_dollar_let_name (s : string) : bool :=
  match s with
  | String c (String _ _) => Nat.eqb (nat_of_ascii c) 36
  | _ => false
  end.

Definition starts_with_dollar (s : string) : bool :=
  match s with
  | String c _ => Nat.eqb (nat_of_ascii c) 36
  | EmptyString => false
  end.

Fixpoint lookup_let_width (env : list (string * positive)) (nm : string) {struct env}
  : option positive :=
  match env with
  | [] => None
  | (k, w) :: rest => if String.eqb k nm then Some w else lookup_let_width rest nm
  end.

Fixpoint string_in_list (s : string) (xs : list string) {struct xs} : bool :=
  match xs with
  | [] => false
  | x :: rest => if String.eqb s x then true else string_in_list s rest
  end.

Definition wf_binop_flags_for (op : cert_binop) (fl : cert_binop_flags) : bool :=
  match op with
  | CB_Add | CB_Sub | CB_Mul | CB_Shl =>
      negb (cbf_exact fl) && negb (cbf_disjoint fl)
  | CB_UDiv | CB_SDiv | CB_LShr | CB_AShr =>
      negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_disjoint fl)
  | CB_Or =>
      negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_exact fl)
  | CB_URem | CB_SRem | CB_And | CB_Xor =>
      negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_exact fl) && negb (cbf_disjoint fl)
  end.

Definition wf_cast_spec (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) : bool :=
  is_supported_bit_width fw &&
  is_supported_bit_width tw &&
  match k with
  | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
  | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
  | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
  end.

Section WfLetBinds.
  Variable wf_sub : list (string * positive) -> cert_expr -> bool.

  Fixpoint wf_let_binds_step (env : list (string * positive)) (seen : list string)
                             (xs : list (string * cert_expr)) {struct xs}
    : option (list (string * positive)) :=
    match xs with
    | [] => Some env
    | (bnm, be) :: rest =>
        if is_dollar_let_name bnm &&
           negb (string_in_list bnm seen) &&
           wf_sub env be
        then wf_let_binds_step ((bnm, cert_expr_bit_width be) :: env) (bnm :: seen) rest
        else None
    end.
End WfLetBinds.

Fixpoint wf_cert_expr (let_env : list (string * positive)) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst w val =>
      is_supported_bit_width w && (val <? N.shiftl 1 (N.pos w))%N
  | CE_Poison w =>
      is_supported_bit_width w
  | CE_Var nm w =>
      negb (String.eqb nm "") &&
      is_supported_bit_width w &&
      match lookup_let_width let_env nm with
      | Some bw => Pos.eqb bw w
      | None => negb (starts_with_dollar nm)
      end
  | CE_BinOp op w fl l r =>
      is_supported_bit_width w &&
      wf_binop_flags_for op fl &&
      wf_cert_expr let_env l &&
      wf_cert_expr let_env r &&
      Pos.eqb (cert_expr_bit_width l) w &&
      Pos.eqb (cert_expr_bit_width r) w
  | CE_ICmp _ _ w l r =>
      is_supported_bit_width w &&
      wf_cert_expr let_env l &&
      wf_cert_expr let_env r &&
      Pos.eqb (cert_expr_bit_width l) w &&
      Pos.eqb (cert_expr_bit_width r) w
  | CE_Cast k fw tw fl o =>
      wf_cast_spec k fw tw fl &&
      wf_cert_expr let_env o &&
      Pos.eqb (cert_expr_bit_width o) fw
  | CE_Select w c t f =>
      is_supported_bit_width w &&
      wf_cert_expr let_env c &&
      wf_cert_expr let_env t &&
      wf_cert_expr let_env f &&
      Pos.eqb (cert_expr_bit_width c) 1%positive &&
      Pos.eqb (cert_expr_bit_width t) w &&
      Pos.eqb (cert_expr_bit_width f) w
  | CE_Freeze w o =>
      is_supported_bit_width w &&
      wf_cert_expr let_env o &&
      Pos.eqb (cert_expr_bit_width o) w
  | CE_Let bs body =>
      match bs with
      | [] => false
      | _ :: _ =>
          match wf_let_binds_step wf_cert_expr let_env [] bs with
          | Some env' => wf_cert_expr env' body
          | None => false
          end
      end
  end.

Definition is_power_of_two_N (n : N) : bool :=
  (0 <? n)%N && N.eqb (N.land n (N.pred n)) 0%N.

Definition wf_ub_assumption (u : ub_assumption) : bool :=
  match u with
  | UBA_ParamNoUndef nm w => negb (String.eqb nm "") && is_supported_bit_width w
  | UBA_PtrNonNull nm => negb (String.eqb nm "")
  | UBA_PtrAligned nm al => negb (String.eqb nm "") && is_power_of_two_N al
  | UBA_PtrDereferenceable nm b => negb (String.eqb nm "") && (0 <? b)%N
  | UBA_LoadNoUndef sl w => negb (String.eqb sl "") && is_supported_bit_width w
  | UBA_DivisorNonZero d => wf_cert_expr [] d
  | UBA_SignedDivNoOverflow l r =>
      wf_cert_expr [] l && wf_cert_expr [] r &&
      Pos.eqb (cert_expr_bit_width l) (cert_expr_bit_width r)
  | UBA_BranchCondDefined c =>
      wf_cert_expr [] c && Pos.eqb (cert_expr_bit_width c) 1%positive
  | UBA_UnreachableEliminated => true
  end.

Definition wf_value_equivalence (ve : value_equivalence) : bool :=
  negb (String.eqb (ve_src_reg ve) "") &&
  negb (String.eqb (ve_tgt_reg ve) "") &&
  is_supported_bit_width (ve_bit_width ve) &&
  wf_cert_expr [] (ve_src_expr ve) &&
  wf_cert_expr [] (ve_tgt_expr ve) &&
  Pos.eqb (cert_expr_bit_width (ve_src_expr ve)) (ve_bit_width ve) &&
  Pos.eqb (cert_expr_bit_width (ve_tgt_expr ve)) (ve_bit_width ve).

Definition wf_memory_invariant (mi : memory_invariant) : bool :=
  match mi with
  | MI_AllocaPromoted sl w e =>
      negb (String.eqb sl "") && is_supported_bit_width w &&
      wf_cert_expr [] e && Pos.eqb (cert_expr_bit_width e) w
  | MI_SlotRefines s1 s2 w e1 e2 =>
      negb (String.eqb s1 "") && negb (String.eqb s2 "") &&
      is_supported_bit_width w &&
      wf_cert_expr [] e1 && wf_cert_expr [] e2 &&
      Pos.eqb (cert_expr_bit_width e1) w && Pos.eqb (cert_expr_bit_width e2) w
  end.

Definition wf_return_obligation (ro : return_obligation) : bool :=
  match ro with
  | RO_VoidEquiv => true
  | RO_ScalarRefines w se te _ =>
      is_supported_bit_width w &&
      wf_cert_expr [] se && wf_cert_expr [] te &&
      Pos.eqb (cert_expr_bit_width se) w && Pos.eqb (cert_expr_bit_width te) w
  end.

Definition wf_block_certificate (bc : block_certificate) : bool :=
  negb (String.eqb (bc_src_block bc) "") &&
  negb (String.eqb (bc_tgt_block bc) "") &&
  forallb wf_ub_assumption (bc_ub_assumptions bc) &&
  forallb wf_value_equivalence (bc_value_equivs bc) &&
  forallb wf_memory_invariant (bc_memory_invariants bc).

Definition wf_loop_cutpoint_invariant (lci : loop_cutpoint_invariant) : bool :=
  negb (String.eqb (lci_src_header lci) "") &&
  negb (String.eqb (lci_tgt_header lci) "") &&
  wf_cert_expr [] (lci_guard lci) &&
  Pos.eqb (cert_expr_bit_width (lci_guard lci)) 1%positive &&
  forallb wf_value_equivalence (lci_value_equivs lci) &&
  forallb wf_memory_invariant (lci_memory_invariants lci).

Definition wf_alias_witness (aw : alias_witness) : bool :=
  negb (String.eqb (aw_lhs_ptr aw) "") &&
  negb (String.eqb (aw_rhs_ptr aw) "").

Definition rev_tr {A : Type} (xs : list A) : list A :=
  List.rev_append xs [].

Lemma rev_tr_eq {A : Type} : forall (xs : list A), rev_tr xs = List.rev xs.
Proof.
  intros xs; unfold rev_tr; rewrite List.rev_append_rev, app_nil_r; reflexivity.
Qed.

Fixpoint str_to_chars_rev_acc (acc : list ascii) (s : string) {struct s} : list ascii :=
  match s with
  | EmptyString => acc
  | String c rest => str_to_chars_rev_acc (c :: acc) rest
  end.

Definition str_to_chars (s : string) : list ascii :=
  List.rev_append (str_to_chars_rev_acc [] s) [].

Fixpoint rev_chars_to_str_acc (acc : string) (rev_cs : list ascii) {struct rev_cs} : string :=
  match rev_cs with
  | [] => acc
  | c :: rest => rev_chars_to_str_acc (String c acc) rest
  end.

Definition chars_to_str (cs : list ascii) : string :=
  rev_chars_to_str_acc EmptyString (List.rev_append cs []).

Lemma str_to_chars_rev_acc_spec : forall s acc,
  List.rev_append (str_to_chars_rev_acc acc s) [] =
  List.rev_append acc (list_ascii_of_string s).
Proof.
  induction s as [| c rest IH]; intros acc; cbn.
  - reflexivity.
  - rewrite (IH (c :: acc)); reflexivity.
Qed.

Lemma str_to_chars_spec : forall s, str_to_chars s = list_ascii_of_string s.
Proof.
  intros s; unfold str_to_chars; exact (str_to_chars_rev_acc_spec s []).
Qed.

Definition is_lower_hex_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n)%nat && (n <=? 57)%nat) || ((97 <=? n)%nat && (n <=? 102)%nat).

Definition is_sha256_hex (s : string) : bool :=
  let cs := str_to_chars s in
  Nat.eqb (List.length cs) 64 && forallb is_lower_hex_char cs.

Definition wf_proof_certificate (cert : proof_certificate) : bool :=
  negb (String.eqb (pc_function_name cert) "") &&
  is_sha256_hex (pc_src_ir_sha256 cert) &&
  is_sha256_hex (pc_tgt_ir_sha256 cert) &&
  forallb wf_block_certificate (pc_blocks cert) &&
  forallb wf_loop_cutpoint_invariant (pc_loop_invariants cert) &&
  forallb wf_alias_witness (pc_alias_witnesses cert) &&
  wf_return_obligation (pc_return_obligation cert).

Fixpoint cf_check_idx_diag_acc {A : Type}
  (chk : nat -> A -> string + unit) (idx : nat) (xs : list A) {struct xs} : string + unit :=
  match xs with
  | [] => inr tt
  | x :: rest =>
      match chk idx x with
      | inl err => inl err
      | inr tt => cf_check_idx_diag_acc chk (S idx) rest
      end
  end.

Lemma cf_check_idx_diag_acc_sound :
  forall {A : Type} (chk : nat -> A -> string + unit) (p : A -> bool) idx xs,
    (forall i x, chk i x = inr tt -> p x = true) ->
    cf_check_idx_diag_acc chk idx xs = inr tt ->
    forallb p xs = true.
Proof.
  intros A chk p idx xs Hc; revert idx; induction xs as [| x rest IH]; intros idx H;
    cbn [cf_check_idx_diag_acc forallb] in *; [reflexivity |].
  destruct (chk idx x) as [| []] eqn:E1; [discriminate H |].
  rewrite (Hc idx x E1), (IH (S idx) H); reflexivity.
Qed.

Definition check_wf_proof_certificate_diag (cert : proof_certificate) : string + unit :=
  bind_err
    (guard_err (negb (String.eqb (pc_function_name cert) ""))
      (fun _ => diag "cert-wf" "empty cert-v1 function name"))
    (fun _ =>
  bind_err
    (guard_err (is_sha256_hex (pc_src_ir_sha256 cert))
      (fun _ => diag "cert-wf" "invalid cert-v1 src-sha256 digest"))
    (fun _ =>
  bind_err
    (guard_err (is_sha256_hex (pc_tgt_ir_sha256 cert))
      (fun _ => diag "cert-wf" "invalid cert-v1 tgt-sha256 digest"))
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc
      (fun idx bc =>
        guard_err (wf_block_certificate bc)
          (fun _ => diag "cert-wf" ("malformed block certificate #" ++ diag_nat_dec idx)))
      0 (pc_blocks cert))
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc
      (fun idx lci =>
        guard_err (wf_loop_cutpoint_invariant lci)
          (fun _ => diag "cert-wf" ("malformed loop invariant #" ++ diag_nat_dec idx)))
      0 (pc_loop_invariants cert))
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc
      (fun idx aw =>
        guard_err (wf_alias_witness aw)
          (fun _ => diag "cert-wf" ("malformed alias witness #" ++ diag_nat_dec idx)))
      0 (pc_alias_witnesses cert))
    (fun _ =>
  guard_err (wf_return_obligation (pc_return_obligation cert))
    (fun _ => diag "cert-wf" "malformed return obligation in cert-v1"))))))).

Lemma check_wf_proof_certificate_diag_sound :
  forall cert,
    check_wf_proof_certificate_diag cert = inr tt ->
    wf_proof_certificate cert = true.
Proof.
  intros cert H; unfold check_wf_proof_certificate_diag in H; unfold wf_proof_certificate.
  destruct (negb (String.eqb (pc_function_name cert) "")); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (is_sha256_hex (pc_src_ir_sha256 cert)); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (is_sha256_hex (pc_tgt_ir_sha256 cert)); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (cf_check_idx_diag_acc
              (fun idx bc =>
                guard_err (wf_block_certificate bc)
                  (fun _ => diag "cert-wf" ("malformed block certificate #" ++ diag_nat_dec idx)))
              0 (pc_blocks cert)) as [| []] eqn:Eblks; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun idx lci =>
                guard_err (wf_loop_cutpoint_invariant lci)
                  (fun _ => diag "cert-wf" ("malformed loop invariant #" ++ diag_nat_dec idx)))
              0 (pc_loop_invariants cert)) as [| []] eqn:Elcis; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun idx aw =>
                guard_err (wf_alias_witness aw)
                  (fun _ => diag "cert-wf" ("malformed alias witness #" ++ diag_nat_dec idx)))
              0 (pc_alias_witnesses cert)) as [| []] eqn:Eaws; cbn [bind_err] in H; [discriminate H |].
  destruct (wf_return_obligation (pc_return_obligation cert)); cbn [guard_err] in H; [| discriminate H].
  rewrite (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hx => guard_err_inr _ _ Hx) Eblks),
          (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hx => guard_err_inr _ _ Hx) Elcis),
          (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hx => guard_err_inr _ _ Hx) Eaws).
  reflexivity.
Qed.

Definition var_pair_eqb (u1 u2 : string * positive) : bool :=
  String.eqb (fst u1) (fst u2) && Pos.eqb (snd u1) (snd u2).

Lemma var_pair_eqb_eq : forall u1 u2,
  var_pair_eqb u1 u2 = true <-> u1 = u2.
Proof.
  intros [s1 w1] [s2 w2]; unfold var_pair_eqb; cbn.
  rewrite andb_true_iff, String.eqb_eq, Pos.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Fixpoint var_pair_in (u : string * positive) (us : list (string * positive))
  {struct us} : bool :=
  match us with
  | [] => false
  | x :: rx => var_pair_eqb u x || var_pair_in u rx
  end.

Lemma var_pair_in_spec : forall u us,
  var_pair_in u us = true <-> In u us.
Proof.
  intros u us; induction us as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (var_pair_eqb u x) eqn:E.
  - apply var_pair_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H]; [
      assert (Hr : var_pair_eqb u u = true) by (apply var_pair_eqb_eq; reflexivity);
      rewrite Hr in E; discriminate | exact H]].
Qed.

(** Shared variable-subset checker over typed parameter pairs (used by
    [AlgRules], [CertValidator], [McFrameMem], [Rv64Sem], [A64CoreSem],
    [McLoop], [McCall], and [McValidator]). *)
Definition vars_subset_b (vs allowed : list (string * positive)) : bool :=
  forallb (fun u => var_pair_in u allowed) vs.

Lemma incl_vars_subset_b :
  forall vs allowed,
    incl vs allowed -> vars_subset_b vs allowed = true.
Proof.
  intros vs allowed Hinc; unfold vars_subset_b; apply forallb_forall.
  intros u Hu; apply var_pair_in_spec; exact (Hinc u Hu).
Qed.

Lemma vars_subset_b_incl :
  forall vs allowed,
    vars_subset_b vs allowed = true -> incl vs allowed.
Proof.
  intros vs allowed H u Hu; unfold vars_subset_b in H.
  rewrite forallb_forall in H; apply var_pair_in_spec; exact (H u Hu).
Qed.

(** ** 4. Total S-Expression Tokenizer & Bounded-Depth Parser ([parse_sexp], [parse_cert]) *)

Unset Elimination Schemes.
Inductive sexp : Set :=
| SAtom (s : string)
| SStr (s : string)
| SList (es : list sexp).
Set Elimination Schemes.

Fixpoint sexp_depth (sx : sexp) : nat :=
  match sx with
  | SAtom _ | SStr _ => 1%nat
  | SList es =>
      let fix max_d_acc (acc : nat) (xs : list sexp) {struct xs} : nat :=
          match xs with
          | [] => acc
          | x :: rest => max_d_acc (Nat.max acc (sexp_depth x)) rest
          end in
      S (max_d_acc 0%nat es)
  end.

Variant sexp_tok : Set :=
| TOK_LParen
| TOK_RParen
| TOK_Atom (s : string)
| TOK_Str (s : string).

Variant tok_mode : Set :=
| TM_Normal
| TM_InString (rev_acc : list ascii)
| TM_InEscape (rev_acc : list ascii)
| TM_InAtom (rev_acc : list ascii).

Definition is_sexp_ws (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 32 || Nat.eqb n 9 || Nat.eqb n 10 || Nat.eqb n 12 || Nat.eqb n 13.

Definition is_valid_atom_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (33 <=? n)%nat && (n <=? 126)%nat &&
  negb (Nat.eqb n 34) &&
  negb (Nat.eqb n 40) &&
  negb (Nat.eqb n 41) &&
  negb (Nat.eqb n 59).

Fixpoint tokenize_loop (mode : tok_mode) (rev_toks : list sexp_tok) (cs : list ascii) {struct cs}
  : string + list sexp_tok :=
  match cs with
  | [] =>
      match mode with
      | TM_Normal => inr (rev_tr rev_toks)
      | TM_InAtom rev_acc =>
          inr (rev_tr (TOK_Atom (rev_chars_to_str_acc EmptyString rev_acc) :: rev_toks))
      | TM_InString _ => inl "unterminated string literal in S-expression"
      | TM_InEscape _ => inl "unterminated escape sequence in S-expression"
      end
  | c :: rest =>
      let n := nat_of_ascii c in
      match mode with
      | TM_Normal =>
          if is_sexp_ws c then tokenize_loop TM_Normal rev_toks rest
          else if Nat.eqb n 40 then tokenize_loop TM_Normal (TOK_LParen :: rev_toks) rest
          else if Nat.eqb n 41 then tokenize_loop TM_Normal (TOK_RParen :: rev_toks) rest
          else if Nat.eqb n 34 then tokenize_loop (TM_InString []) rev_toks rest
          else if is_valid_atom_char c then tokenize_loop (TM_InAtom [c]) rev_toks rest
          else inl "invalid character in S-expression"
      | TM_InString rev_acc =>
          if Nat.eqb n 34 then
            tokenize_loop TM_Normal
              (TOK_Str (rev_chars_to_str_acc EmptyString rev_acc) :: rev_toks) rest
          else if Nat.eqb n 92 then
            tokenize_loop (TM_InEscape rev_acc) rev_toks rest
          else if (n <? 32)%nat || Nat.eqb n 127 then
            inl "raw control character in S-expression string literal"
          else
            tokenize_loop (TM_InString (c :: rev_acc)) rev_toks rest
      | TM_InEscape rev_acc =>
          if Nat.eqb n 92 then
            tokenize_loop (TM_InString (ascii_of_nat 92 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 34 then
            tokenize_loop (TM_InString (ascii_of_nat 34 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 110 then
            tokenize_loop (TM_InString (ascii_of_nat 10 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 114 then
            tokenize_loop (TM_InString (ascii_of_nat 13 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 116 then
            tokenize_loop (TM_InString (ascii_of_nat 9 :: rev_acc)) rev_toks rest
          else
            inl "unsupported escape sequence in S-expression string literal"
      | TM_InAtom rev_acc =>
          let done_atom := TOK_Atom (rev_chars_to_str_acc EmptyString rev_acc) in
          if is_sexp_ws c then
            tokenize_loop TM_Normal (done_atom :: rev_toks) rest
          else if Nat.eqb n 40 then
            tokenize_loop TM_Normal (TOK_LParen :: done_atom :: rev_toks) rest
          else if Nat.eqb n 41 then
            tokenize_loop TM_Normal (TOK_RParen :: done_atom :: rev_toks) rest
          else if is_valid_atom_char c then
            tokenize_loop (TM_InAtom (c :: rev_acc)) rev_toks rest
          else
            inl "invalid character in bare atom"
      end
  end.

Definition max_sexp_depth : nat := 1024%nat.

Definition push_sexp_item (item : sexp) (stack : list (list sexp)) (top_rev : list sexp)
  : list (list sexp) * list sexp :=
  match stack with
  | [] => ([], item :: top_rev)
  | cur :: parents => ((item :: cur) :: parents, top_rev)
  end.

Fixpoint parse_sexp_toks (stack : list (list sexp)) (top_rev : list sexp)
                         (toks : list sexp_tok) {struct toks} : string + sexp :=
  match toks with
  | [] =>
      match stack with
      | _ :: _ => inl "unclosed opening parenthesis in S-expression"
      | [] =>
          match rev_tr top_rev with
          | [root] => inr root
          | [] => inl "empty S-expression input"
          | _ :: _ :: _ => inl "trailing tokens after root S-expression"
          end
      end
  | tok :: rest =>
      match tok with
      | TOK_Atom a =>
          let '(st', top') := push_sexp_item (SAtom a) stack top_rev in
          parse_sexp_toks st' top' rest
      | TOK_Str s =>
          let '(st', top') := push_sexp_item (SStr s) stack top_rev in
          parse_sexp_toks st' top' rest
      | TOK_LParen =>
          if (S (List.length stack) <=? max_sexp_depth)%nat then
            parse_sexp_toks ([] :: stack) top_rev rest
          else
            inl "S-expression exceeds maximum nesting depth 1024"
      | TOK_RParen =>
          match stack with
          | [] => inl "unexpected closing parenthesis in S-expression"
          | cur_rev :: parents =>
              let '(st', top') := push_sexp_item (SList (rev_tr cur_rev)) parents top_rev in
              parse_sexp_toks st' top' rest
          end
      end
  end.

Definition parse_sexp (input : string) : string + sexp :=
  match tokenize_loop TM_Normal [] (str_to_chars input) with
  | inl err => inl err
  | inr toks => parse_sexp_toks [] [] toks
  end.

(** ** 5. Canonical [cert-v1] S-Expression Deserializer ([parse_cert]) *)

Fixpoint parse_digits_acc (acc : N) (cs : list ascii) {struct cs} : option N :=
  match cs with
  | [] => Some acc
  | c :: rest =>
      let n := nat_of_ascii c in
      if (48 <=? n)%nat && (n <=? 57)%nat then
        parse_digits_acc (10 * acc + N.of_nat (n - 48))%N rest
      else
        None
  end.

Definition parse_canonical_N (s : string) : option N :=
  match str_to_chars s with
  | [] => None
  | [c] =>
      let n := nat_of_ascii c in
      if (48 <=? n)%nat && (n <=? 57)%nat then Some (N.of_nat (n - 48)) else None
  | c0 :: rest =>
      let n0 := nat_of_ascii c0 in
      if (49 <=? n0)%nat && (n0 <=? 57)%nat then
        parse_digits_acc (N.of_nat (n0 - 48)) rest
      else
        None
  end.

Definition parse_u64_N (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n =>
          if (n <? N.shiftl 1 64)%N then inr n
          else inl "integer literal exceeds 64-bit unsigned range"
      | None => inl "expected canonical unsigned integer atom"
      end
  | _ => inl "expected unsigned integer atom"
  end.

Definition parse_bv_N (w : positive) (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n =>
          if (n <? N.shiftl 1 (N.pos w))%N then inr n
          else inl "bitvector constant exceeds declared width"
      | None => inl "expected canonical unsigned integer for bitvector constant"
      end
  | _ => inl "expected atom for bitvector constant"
  end.

Lemma parse_bv_N_bound : forall w sx n,
  parse_bv_N w sx = inr n -> (n <? N.shiftl 1 (N.pos w))%N = true.
Proof.
  intros w [s | s | es] n H; cbn in H; try discriminate.
  destruct (parse_canonical_N s) as [m |]; [| discriminate].
  destruct (m <? N.shiftl 1 (N.pos w))%N eqn:Hb; [| discriminate].
  inversion H; subst; exact Hb.
Qed.

Definition parse_bit_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr 1%positive
      else if String.eqb s "8" then inr 8%positive
      else if String.eqb s "16" then inr 16%positive
      else if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else if String.eqb s "128" then inr 128%positive
      else inl "expected supported bit width (1, 8, 16, 32, 64, or 128)"
  | _ => inl "expected supported bit width (1, 8, 16, 32, 64, or 128)"
  end.

Lemma parse_bit_width_supported : forall sx w,
  parse_bit_width_sexp sx = inr w -> is_supported_bit_width w = true.
Proof.
  intros [s | s | es] w H; cbn in H; try discriminate.
  repeat match goal with
  | H0 : (if ?c then _ else _) = _ |- _ =>
      destruct c; [inversion H0; subst; reflexivity |]
  end; discriminate.
Qed.

Definition parse_bool01 (sx : sexp) : string + bool :=
  match sx with
  | SAtom s =>
      if String.eqb s "0" then inr false
      else if String.eqb s "1" then inr true
      else inl "expected boolean flag 0 or 1"
  | _ => inl "expected boolean flag 0 or 1"
  end.

Definition parse_bool_tf (sx : sexp) : string + bool :=
  match sx with
  | SAtom s =>
      if String.eqb s "false" then inr false
      else if String.eqb s "true" then inr true
      else inl "expected boolean atom true or false"
  | _ => inl "expected boolean atom true or false"
  end.

Definition parse_nonempty_str (sx : sexp) : string + string :=
  match sx with
  | SStr s =>
      if negb (String.eqb s "") then inr s
      else inl "expected non-empty string literal"
  | _ => inl "expected string literal"
  end.

Lemma parse_nonempty_str_ok : forall sx s,
  parse_nonempty_str sx = inr s -> negb (String.eqb s "") = true.
Proof.
  intros [a | s0 | es] s H; cbn in H; try discriminate.
  destruct (negb (String.eqb s0 "")) eqn:Hne; [| discriminate].
  inversion H; subst; exact Hne.
Qed.

Definition parse_sha256_atom (sx : sexp) : string + string :=
  match sx with
  | SAtom s =>
      if is_sha256_hex s then inr s
      else inl "expected 64-character lowercase hex SHA-256 digest"
  | _ => inl "expected bare atom for SHA-256 digest"
  end.

Lemma parse_sha256_atom_ok : forall sx s,
  parse_sha256_atom sx = inr s -> is_sha256_hex s = true.
Proof.
  intros [s0 | s0 | es] s H; cbn in H; try discriminate.
  destruct (is_sha256_hex s0) eqn:Hh; [| discriminate].
  inversion H; subst; exact Hh.
Qed.

Definition parse_cert_binop (sx : sexp) : string + cert_binop :=
  match sx with
  | SAtom s =>
      if String.eqb s "add" then inr CB_Add
      else if String.eqb s "sub" then inr CB_Sub
      else if String.eqb s "mul" then inr CB_Mul
      else if String.eqb s "udiv" then inr CB_UDiv
      else if String.eqb s "sdiv" then inr CB_SDiv
      else if String.eqb s "urem" then inr CB_URem
      else if String.eqb s "srem" then inr CB_SRem
      else if String.eqb s "shl" then inr CB_Shl
      else if String.eqb s "lshr" then inr CB_LShr
      else if String.eqb s "ashr" then inr CB_AShr
      else if String.eqb s "and" then inr CB_And
      else if String.eqb s "or" then inr CB_Or
      else if String.eqb s "xor" then inr CB_Xor
      else inl "unknown binary operator in cert-v1 expression"
  | _ => inl "unknown binary operator in cert-v1 expression"
  end.

Definition parse_cert_icmp_pred (sx : sexp) : string + cert_icmp_pred :=
  match sx with
  | SAtom s =>
      if String.eqb s "eq" then inr CIP_Eq
      else if String.eqb s "ne" then inr CIP_Ne
      else if String.eqb s "ult" then inr CIP_Ult
      else if String.eqb s "ule" then inr CIP_Ule
      else if String.eqb s "ugt" then inr CIP_Ugt
      else if String.eqb s "uge" then inr CIP_Uge
      else if String.eqb s "slt" then inr CIP_Slt
      else if String.eqb s "sle" then inr CIP_Sle
      else if String.eqb s "sgt" then inr CIP_Sgt
      else if String.eqb s "sge" then inr CIP_Sge
      else inl "unknown icmp predicate in cert-v1 expression"
  | _ => inl "unknown icmp predicate in cert-v1 expression"
  end.

Definition parse_cert_cast_kind (sx : sexp) : string + cert_cast_kind :=
  match sx with
  | SAtom s =>
      if String.eqb s "zext" then inr CCK_ZExt
      else if String.eqb s "sext" then inr CCK_SExt
      else if String.eqb s "trunc" then inr CCK_Trunc
      else inl "unknown cast kind in cert-v1 expression"
  | _ => inl "unknown cast kind in cert-v1 expression"
  end.

Section ParseLetBinds.
  Variable rec_parse : list (string * positive) -> sexp -> string + cert_expr.

  Fixpoint parse_let_binds_acc
    (acc_rev : list (string * cert_expr))
    (cur_env : list (string * positive)) (seen : list string)
    (bs : list sexp) {struct bs}
    : string + (list (string * cert_expr) * list (string * positive)) :=
    match bs with
    | [] => inr (List.rev_append acc_rev [], cur_env)
    | b_item :: rest =>
        match b_item with
        | SList [SStr bnm; bexpr_sx] =>
            if is_dollar_let_name bnm && negb (string_in_list bnm seen) then
              match rec_parse cur_env bexpr_sx with
              | inl err => inl err
              | inr be =>
                  let env_next := (bnm, cert_expr_bit_width be) :: cur_env in
                  parse_let_binds_acc ((bnm, be) :: acc_rev) env_next (bnm :: seen) rest
              end
            else inl "invalid or duplicate let binding name"
        | _ => inl "malformed let binding entry"
        end
    end.

  Definition parse_let_binds (cur_env : list (string * positive)) (seen : list string)
                             (bs : list sexp)
    : string + (list (string * cert_expr) * list (string * positive)) :=
    parse_let_binds_acc [] cur_env seen bs.
End ParseLetBinds.

Lemma parse_let_binds_acc_wf :
  forall (rec_parse : list (string * positive) -> sexp -> string + cert_expr)
         (Hrec : forall env sx e, rec_parse env sx = inr e -> wf_cert_expr env e = true)
         bs env0 seen0 acc_rev cur_env seen parsed_bs final_env,
    (forall tail env_tail,
       wf_let_binds_step wf_cert_expr cur_env seen tail = Some env_tail ->
       wf_let_binds_step wf_cert_expr env0 seen0 (List.rev_append acc_rev tail) = Some env_tail) ->
    parse_let_binds_acc rec_parse acc_rev cur_env seen bs = inr (parsed_bs, final_env) ->
    wf_let_binds_step wf_cert_expr env0 seen0 parsed_bs = Some final_env.
Proof.
  intros rec_parse Hrec bs env0 seen0.
  induction bs as [| b_item rest IH]; intros acc_rev cur_env seen parsed_bs final_env Hacc Hp;
    cbn [parse_let_binds_acc] in Hp.
  - inversion Hp; subst parsed_bs final_env; clear Hp.
    exact (Hacc [] cur_env eq_refl).
  - destruct b_item as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
    destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)) eqn:Hnm; [| discriminate Hp].
    destruct (rec_parse cur_env bexpr_sx) as [| be] eqn:Hbe; [discriminate Hp |].
    apply andb_true_iff in Hnm as [Hd Hns].
    apply (IH ((bnm, be) :: acc_rev)
              ((bnm, cert_expr_bit_width be) :: cur_env) (bnm :: seen)
              parsed_bs final_env); [| exact Hp].
    intros tail env_tail Htail; cbn [List.rev_append].
    apply Hacc; cbn [wf_let_binds_step].
    rewrite Hd, Hns, (Hrec cur_env bexpr_sx be Hbe); exact Htail.
Qed.

Lemma parse_let_binds_wf :
  forall (rec_parse : list (string * positive) -> sexp -> string + cert_expr)
         (Hrec : forall env sx e, rec_parse env sx = inr e -> wf_cert_expr env e = true)
         bs cur_env seen parsed_bs final_env,
    parse_let_binds rec_parse cur_env seen bs = inr (parsed_bs, final_env) ->
    wf_let_binds_step wf_cert_expr cur_env seen parsed_bs = Some final_env.
Proof.
  intros rec_parse Hrec bs cur_env seen parsed_bs final_env Hp.
  exact (parse_let_binds_acc_wf rec_parse Hrec bs cur_env seen [] cur_env seen
           parsed_bs final_env (fun _ _ H => H) Hp).
Qed.

Lemma rev_append_cons_nonnil : forall {A : Type} (x : A) (acc tail : list A),
  List.rev_append (x :: acc) tail <> [].
Proof.
  intros A x acc; revert x; induction acc as [| y rest IH]; intros x tail; cbn.
  - discriminate.
  - exact (IH y (x :: tail)).
Qed.

Lemma parse_let_binds_acc_nonempty :
  forall rec_parse bs a acc_rev cur_env seen parsed_bs final_env,
    parse_let_binds_acc rec_parse (a :: acc_rev) cur_env seen bs = inr (parsed_bs, final_env) ->
    parsed_bs <> [].
Proof.
  intros rec_parse bs; induction bs as [| b_item rest IH];
    intros a acc_rev cur_env seen parsed_bs final_env Hp; cbn [parse_let_binds_acc] in Hp.
  - inversion Hp; subst parsed_bs; clear Hp; exact (rev_append_cons_nonnil a acc_rev []).
  - destruct b_item as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
    destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)); [| discriminate Hp].
    destruct (rec_parse cur_env bexpr_sx); [discriminate Hp |].
    exact (IH _ _ _ _ _ _ Hp).
Qed.

Lemma parse_let_binds_nonempty :
  forall rec_parse b0 rest cur_env seen parsed_bs final_env,
    parse_let_binds rec_parse cur_env seen (b0 :: rest) = inr (parsed_bs, final_env) ->
    parsed_bs <> [].
Proof.
  intros rec_parse b0 rest cur_env seen parsed_bs final_env Hp.
  unfold parse_let_binds in Hp; cbn [parse_let_binds_acc] in Hp.
  destruct b0 as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
  destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)); [| discriminate Hp].
  destruct (rec_parse cur_env bexpr_sx) as [| be]; [discriminate Hp |].
  exact (parse_let_binds_acc_nonempty rec_parse rest (bnm, be) []
           ((bnm, cert_expr_bit_width be) :: cur_env) (bnm :: seen)
           parsed_bs final_env Hp).
Qed.

Fixpoint parse_cert_expr_fueled (fuel : nat) (let_env : list (string * positive)) (sx : sexp)
                                {struct fuel}
  : string + cert_expr :=
  match fuel with
  | O => inl "cert-v1 expression fuel exhausted"
  | S fuel' =>
      match sx with
      | SList (SAtom tag :: args) =>
          if String.eqb tag "bv" then
            match args with
            | [w_sx; val_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_bv_N w val_sx with
                    | inl err => inl err
                    | inr val => inr (CE_BvConst w val)
                    end
                end
            | _ => inl "malformed bv expression"
            end
          else if String.eqb tag "poison" then
            match args with
            | [w_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w => inr (CE_Poison w)
                end
            | _ => inl "malformed poison expression"
            end
          else if String.eqb tag "var" then
            match args with
            | [nm_sx; w_sx] =>
                match parse_nonempty_str nm_sx, parse_bit_width_sexp w_sx with
                | inr nm, inr w =>
                    match lookup_let_width let_env nm with
                    | Some bw =>
                        if Pos.eqb bw w then inr (CE_Var nm w)
                        else inl "let-bound variable bitwidth mismatch"
                    | None =>
                        if negb (starts_with_dollar nm) then inr (CE_Var nm w)
                        else inl "unbound $-prefixed let variable in cert-v1 expression"
                    end
                | inl err, _ => inl err
                | _, inl err => inl err
                end
            | _ => inl "malformed var expression"
            end
          else if String.eqb tag "binop" then
            match args with
            | [op_sx; w_sx; SList (SAtom f_tag :: [nuw_sx; nsw_sx; ex_sx; dj_sx]);
               lhs_sx; rhs_sx] =>
                if String.eqb f_tag "flags" then
                  match parse_cert_binop op_sx, parse_bit_width_sexp w_sx,
                        parse_bool01 nuw_sx, parse_bool01 nsw_sx,
                        parse_bool01 ex_sx, parse_bool01 dj_sx with
                  | inr op, inr w, inr nuw, inr nsw, inr ex, inr dj =>
                      let fl := mk_cert_binop_flags nuw nsw ex dj in
                      if wf_binop_flags_for op fl then
                        match parse_cert_expr_fueled fuel' let_env lhs_sx,
                              parse_cert_expr_fueled fuel' let_env rhs_sx with
                        | inr l, inr r =>
                            if Pos.eqb (cert_expr_bit_width l) w &&
                               Pos.eqb (cert_expr_bit_width r) w
                            then inr (CE_BinOp op w fl l r)
                            else inl "binop operand bitwidth mismatch"
                        | inl err, _ => inl err
                        | _, inl err => inl err
                        end
                      else inl "invalid poison flags for binary operator"
                  | inl err, _, _, _, _, _ => inl err
                  | _, inl err, _, _, _, _ => inl err
                  | _, _, inl err, _, _, _ => inl err
                  | _, _, _, inl err, _, _ => inl err
                  | _, _, _, _, inl err, _ => inl err
                  | _, _, _, _, _, inl err => inl err
                  end
                else inl "expected flags tag in binop expression"
            | _ => inl "malformed binop expression"
            end
          else if String.eqb tag "icmp" then
            match args with
            | [pr_sx; ss_sx; w_sx; lhs_sx; rhs_sx] =>
                match parse_cert_icmp_pred pr_sx, parse_bool01 ss_sx, parse_bit_width_sexp w_sx with
                | inr pr, inr ss, inr w =>
                    match parse_cert_expr_fueled fuel' let_env lhs_sx,
                          parse_cert_expr_fueled fuel' let_env rhs_sx with
                    | inr l, inr r =>
                        if Pos.eqb (cert_expr_bit_width l) w &&
                           Pos.eqb (cert_expr_bit_width r) w
                        then inr (CE_ICmp pr ss w l r)
                        else inl "icmp operand bitwidth mismatch"
                    | inl err, _ => inl err
                    | _, inl err => inl err
                    end
                | inl err, _, _ => inl err
                | _, inl err, _ => inl err
                | _, _, inl err => inl err
                end
            | _ => inl "malformed icmp expression"
            end
          else if String.eqb tag "cast" then
            match args with
            | [k_sx; fw_sx; tw_sx; SList (SAtom f_tag :: [nn_sx; nuw_sx; nsw_sx]); op_sx] =>
                if String.eqb f_tag "flags" then
                  match parse_cert_cast_kind k_sx,
                        parse_bit_width_sexp fw_sx, parse_bit_width_sexp tw_sx,
                        parse_bool01 nn_sx, parse_bool01 nuw_sx, parse_bool01 nsw_sx with
                  | inr k, inr fw, inr tw, inr nn, inr nuw, inr nsw =>
                      let fl := mk_cert_cast_flags nn nuw nsw in
                      if wf_cast_spec k fw tw fl then
                        match parse_cert_expr_fueled fuel' let_env op_sx with
                        | inr o =>
                            if Pos.eqb (cert_expr_bit_width o) fw
                            then inr (CE_Cast k fw tw fl o)
                            else inl "cast operand bitwidth mismatch"
                        | inl err => inl err
                        end
                      else inl "invalid cast width relation or flags"
                  | inl err, _, _, _, _, _ => inl err
                  | _, inl err, _, _, _, _ => inl err
                  | _, _, inl err, _, _, _ => inl err
                  | _, _, _, inl err, _, _ => inl err
                  | _, _, _, _, inl err, _ => inl err
                  | _, _, _, _, _, inl err => inl err
                  end
                else inl "expected flags tag in cast expression"
            | _ => inl "malformed cast expression"
            end
          else if String.eqb tag "select" then
            match args with
            | [w_sx; c_sx; t_sx; f_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_cert_expr_fueled fuel' let_env c_sx,
                          parse_cert_expr_fueled fuel' let_env t_sx,
                          parse_cert_expr_fueled fuel' let_env f_sx with
                    | inr c, inr tv, inr fv =>
                        if Pos.eqb (cert_expr_bit_width c) 1%positive &&
                           Pos.eqb (cert_expr_bit_width tv) w &&
                           Pos.eqb (cert_expr_bit_width fv) w
                        then inr (CE_Select w c tv fv)
                        else inl "select operand bitwidth mismatch"
                    | inl err, _, _ => inl err
                    | _, inl err, _ => inl err
                    | _, _, inl err => inl err
                    end
                end
            | _ => inl "malformed select expression"
            end
          else if String.eqb tag "freeze" then
            match args with
            | [w_sx; op_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_cert_expr_fueled fuel' let_env op_sx with
                    | inr o =>
                        if Pos.eqb (cert_expr_bit_width o) w
                        then inr (CE_Freeze w o)
                        else inl "freeze operand bitwidth mismatch"
                    | inl err => inl err
                    end
                end
            | _ => inl "malformed freeze expression"
            end
          else if String.eqb tag "let" then
            match args with
            | [SList bind_sxs; body_sx] =>
                match bind_sxs with
                | [] => inl "empty let binding list in cert-v1 expression"
                | b0 :: brest =>
                    match parse_let_binds (parse_cert_expr_fueled fuel')
                                          let_env [] (b0 :: brest) with
                    | inl err => inl err
                    | inr (parsed_bs, env') =>
                        match parse_cert_expr_fueled fuel' env' body_sx with
                        | inl err => inl err
                        | inr body => inr (CE_Let parsed_bs body)
                        end
                    end
                end
            | _ => inl "malformed let expression"
            end
          else inl "unknown cert-v1 expression tag"
      | _ => inl "malformed cert-v1 expression"
      end
  end.

Definition parse_cert_expr (let_env : list (string * positive)) (sx : sexp)
  : string + cert_expr :=
  parse_cert_expr_fueled (sexp_depth sx) let_env sx.

Lemma parse_cert_expr_fueled_wf : forall fuel let_env sx e,
  parse_cert_expr_fueled fuel let_env sx = inr e ->
  wf_cert_expr let_env e = true.
Proof.
  induction fuel as [| fuel' IH]; intros let_env sx e Hp.
  - cbn in Hp; discriminate.
  - cbn [parse_cert_expr_fueled] in Hp.
    destruct sx as [| | [| [tag | |] args]]; try discriminate.
    destruct (String.eqb tag "bv") eqn:Hbv.
    + destruct args as [| w_sx [| val_sx [| ? ?]]]; try discriminate.
      destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
      destruct (parse_bv_N w val_sx) as [| val] eqn:Hv; [discriminate |].
      inversion Hp; subst; cbn.
      rewrite (parse_bit_width_supported w_sx w Hw), (parse_bv_N_bound w val_sx val Hv);
        reflexivity.
    + destruct (String.eqb tag "poison") eqn:Hpsn.
      * destruct args as [| w_sx [| ? ?]]; try discriminate.
        destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
        inversion Hp; subst; cbn; exact (parse_bit_width_supported w_sx w Hw).
      * destruct (String.eqb tag "var") eqn:Hvar.
        -- destruct args as [| nm_sx [| w_sx [| ? ?]]]; try discriminate.
           destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
           destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
           destruct (lookup_let_width let_env nm) as [bw |] eqn:Hlu.
           ++ destruct (Pos.eqb bw w) eqn:Hbw; [| discriminate].
              inversion Hp; subst; cbn.
              rewrite (parse_nonempty_str_ok nm_sx nm Hnm),
                      (parse_bit_width_supported w_sx w Hw), Hlu, Hbw; reflexivity.
           ++ destruct (negb (starts_with_dollar nm)) eqn:Hnd; [| discriminate].
              inversion Hp; subst; cbn.
              rewrite (parse_nonempty_str_ok nm_sx nm Hnm),
                      (parse_bit_width_supported w_sx w Hw), Hlu, Hnd; reflexivity.
        -- destruct (String.eqb tag "binop") eqn:Hbin.
           ++ destruct args as
                [| op_sx [| w_sx [| [| | [| [f_tag | |] [| nuw_sx [| nsw_sx [| ex_sx [| dj_sx [| ? ?]]]]]]]
                                  [| lhs_sx [| rhs_sx [| ? ?]]]]]];
                try discriminate.
              destruct (String.eqb f_tag "flags"); [| discriminate].
              destruct (parse_cert_binop op_sx) as [| op]; [discriminate |].
              destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
              destruct (parse_bool01 nuw_sx) as [| nuw]; [discriminate |].
              destruct (parse_bool01 nsw_sx) as [| nsw]; [discriminate |].
              destruct (parse_bool01 ex_sx) as [| ex]; [discriminate |].
              destruct (parse_bool01 dj_sx) as [| dj]; [discriminate |].
              destruct (wf_binop_flags_for op (mk_cert_binop_flags nuw nsw ex dj)) eqn:Hfl;
                [| discriminate].
              destruct (parse_cert_expr_fueled fuel' let_env lhs_sx) as [| l] eqn:Hl;
                [discriminate |].
              destruct (parse_cert_expr_fueled fuel' let_env rhs_sx) as [| r] eqn:Hr;
                [discriminate |].
              destruct (Pos.eqb (cert_expr_bit_width l) w &&
                        Pos.eqb (cert_expr_bit_width r) w) eqn:Hws; [| discriminate].
              apply andb_true_iff in Hws as [Hwl Hwr].
              inversion Hp; subst; cbn.
              rewrite (parse_bit_width_supported w_sx w Hw), Hfl,
                      (IH _ _ _ Hl), (IH _ _ _ Hr), Hwl, Hwr; reflexivity.
           ++ destruct (String.eqb tag "icmp") eqn:Hicmp.
              ** destruct args as [| pr_sx [| ss_sx [| w_sx [| lhs_sx [| rhs_sx [| ? ?]]]]]];
                   try discriminate.
                 destruct (parse_cert_icmp_pred pr_sx) as [| pr]; [discriminate |].
                 destruct (parse_bool01 ss_sx) as [| ss]; [discriminate |].
                 destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
                 destruct (parse_cert_expr_fueled fuel' let_env lhs_sx) as [| l] eqn:Hl;
                   [discriminate |].
                 destruct (parse_cert_expr_fueled fuel' let_env rhs_sx) as [| r] eqn:Hr;
                   [discriminate |].
                 destruct (Pos.eqb (cert_expr_bit_width l) w &&
                           Pos.eqb (cert_expr_bit_width r) w) eqn:Hws; [| discriminate].
                 apply andb_true_iff in Hws as [Hwl Hwr].
                 inversion Hp; subst; cbn.
                 rewrite (parse_bit_width_supported w_sx w Hw),
                         (IH _ _ _ Hl), (IH _ _ _ Hr), Hwl, Hwr; reflexivity.
              ** destruct (String.eqb tag "cast") eqn:Hcast.
                 --- destruct args as
                       [| k_sx [| fw_sx [| tw_sx
                         [| [| | [| [f_tag | |] [| nn_sx [| nuw_sx [| nsw_sx [| ? ?]]]]]]
                          [| op_sx [| ? ?]]]]]];
                       try discriminate.
                     destruct (String.eqb f_tag "flags"); [| discriminate].
                     destruct (parse_cert_cast_kind k_sx) as [| k]; [discriminate |].
                     destruct (parse_bit_width_sexp fw_sx) as [| fw]; [discriminate |].
                     destruct (parse_bit_width_sexp tw_sx) as [| tw]; [discriminate |].
                     destruct (parse_bool01 nn_sx) as [| nn]; [discriminate |].
                     destruct (parse_bool01 nuw_sx) as [| nuw]; [discriminate |].
                     destruct (parse_bool01 nsw_sx) as [| nsw]; [discriminate |].
                     destruct (wf_cast_spec k fw tw (mk_cert_cast_flags nn nuw nsw)) eqn:Hcs;
                       [| discriminate].
                     destruct (parse_cert_expr_fueled fuel' let_env op_sx) as [| o] eqn:Ho;
                       [discriminate |].
                     destruct (Pos.eqb (cert_expr_bit_width o) fw) eqn:Hwo; [| discriminate].
                     inversion Hp; subst; cbn.
                     rewrite Hcs, (IH _ _ _ Ho), Hwo; reflexivity.
                 --- destruct (String.eqb tag "select") eqn:Hsel.
                     +++ destruct args as [| w_sx [| c_sx [| t_sx [| f_sx [| ? ?]]]]];
                           try discriminate.
                         destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env c_sx) as [| c] eqn:Hc;
                           [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env t_sx) as [| tv] eqn:Ht;
                           [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env f_sx) as [| fv] eqn:Hf;
                           [discriminate |].
                         destruct (Pos.eqb (cert_expr_bit_width c) 1%positive &&
                                   Pos.eqb (cert_expr_bit_width tv) w &&
                                   Pos.eqb (cert_expr_bit_width fv) w) eqn:Hws; [| discriminate].
                         rewrite !andb_true_iff in Hws; destruct Hws as ((Hwc & Hwt) & Hwf).
                         inversion Hp; subst; cbn.
                         rewrite (parse_bit_width_supported w_sx w Hw),
                                 (IH _ _ _ Hc), (IH _ _ _ Ht), (IH _ _ _ Hf),
                                 Hwc, Hwt, Hwf; reflexivity.
                     +++ destruct (String.eqb tag "freeze") eqn:Hfrz.
                         *** destruct args as [| w_sx [| op_sx [| ? ?]]]; try discriminate.
                             destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw;
                               [discriminate |].
                             destruct (parse_cert_expr_fueled fuel' let_env op_sx) as [| o] eqn:Ho;
                               [discriminate |].
                             destruct (Pos.eqb (cert_expr_bit_width o) w) eqn:Hwo;
                               [| discriminate].
                             inversion Hp; subst; cbn.
                             rewrite (parse_bit_width_supported w_sx w Hw),
                                     (IH _ _ _ Ho), Hwo; reflexivity.
                         *** destruct (String.eqb tag "let") eqn:Hlet; [| discriminate].
                             destruct args as [| [| | [| b0 brest]] [| body_sx [| ? ?]]];
                               try discriminate.
                             destruct (parse_let_binds (parse_cert_expr_fueled fuel')
                                                       let_env [] (b0 :: brest))
                               as [| [parsed_bs env']] eqn:Hbs; [discriminate |].
                             destruct (parse_cert_expr_fueled fuel' env' body_sx)
                               as [| body] eqn:Hbody; [discriminate |].
                             inversion Hp; subst; cbn [wf_cert_expr].
                             pose proof (parse_let_binds_nonempty _ _ _ _ _ _ _ Hbs) as Hne.
                             pose proof (parse_let_binds_wf _ IH _ _ _ _ _ Hbs) as Hwfb.
                             destruct parsed_bs as [| p0 pr]; [congruence |].
                             rewrite Hwfb; exact (IH _ _ _ Hbody).
Qed.

Lemma parse_cert_expr_wf : forall sx let_env e,
  parse_cert_expr let_env sx = inr e -> wf_cert_expr let_env e = true.
Proof.
  intros sx let_env e Hp; exact (parse_cert_expr_fueled_wf (sexp_depth sx) let_env sx e Hp).
Qed.

Fixpoint map_parse_list_acc {A : Set} (f : sexp -> string + A)
                            (acc : list A) (xs : list sexp) {struct xs}
  : string + list A :=
  match xs with
  | [] => inr (List.rev_append acc [])
  | x :: rest =>
      match f x with
      | inl err => inl err
      | inr y => map_parse_list_acc f (y :: acc) rest
      end
  end.

Definition map_parse_list {A : Set} (f : sexp -> string + A) (xs : list sexp)
  : string + list A :=
  map_parse_list_acc f [] xs.

Lemma forallb_rev_append {A : Type} :
  forall (p : A -> bool) (xs acc : list A),
    forallb p xs = true ->
    forallb p acc = true ->
    forallb p (List.rev_append xs acc) = true.
Proof.
  intros p xs; induction xs as [| x rest IH]; intros acc Hxs Hacc; cbn in *.
  - exact Hacc.
  - apply andb_true_iff in Hxs as [Hx Hrest].
    apply IH; [exact Hrest | cbn; rewrite Hx, Hacc; reflexivity].
Qed.

Lemma map_parse_list_acc_forallb {A : Set} :
  forall (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall sx y, f sx = inr y -> wf y = true)
         xs acc ys,
    forallb wf acc = true ->
    map_parse_list_acc f acc xs = inr ys ->
    forallb wf ys = true.
Proof.
  intros f wf Hwf xs.
  induction xs as [| x rest IH]; intros acc ys Hacc Hp; cbn in Hp.
  - inversion Hp; subst; exact (forallb_rev_append wf acc [] Hacc eq_refl).
  - destruct (f x) as [| y] eqn:Hy; [discriminate |].
    apply (IH (y :: acc) ys); [| exact Hp].
    cbn; rewrite (Hwf x y Hy), Hacc; reflexivity.
Qed.

Lemma map_parse_list_forallb {A : Set} :
  forall (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall sx y, f sx = inr y -> wf y = true)
         xs ys,
    map_parse_list f xs = inr ys -> forallb wf ys = true.
Proof.
  intros f wf Hwf xs ys Hp.
  exact (map_parse_list_acc_forallb f wf Hwf xs [] ys eq_refl Hp).
Qed.

Definition parse_tagged_nonempty_str_sexp (expected_tag : string) (sx : sexp)
  : string + string :=
  match sx with
  | SList [SAtom tag; val_sx] =>
      if String.eqb tag expected_tag then parse_nonempty_str val_sx
      else inl "unexpected S-expression field tag"
  | _ => inl "expected tagged string S-expression"
  end.

Lemma parse_tagged_nonempty_str_ok : forall tag sx out,
  parse_tagged_nonempty_str_sexp tag sx = inr out -> negb (String.eqb out "") = true.
Proof.
  intros tag [? | ? | [| [t0 | ? | ?] [| val_sx [| ? ?]]]] out H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_nonempty_str_ok val_sx out H).
Qed.

Definition parse_tagged_sha256_sexp (expected_tag : string) (sx : sexp)
  : string + string :=
  match sx with
  | SList [SAtom tag; digest_sx] =>
      if String.eqb tag expected_tag then parse_sha256_atom digest_sx
      else inl "unexpected SHA-256 field tag"
  | _ => inl "expected tagged SHA-256 S-expression"
  end.

Lemma parse_tagged_sha256_ok : forall tag sx out,
  parse_tagged_sha256_sexp tag sx = inr out -> is_sha256_hex out = true.
Proof.
  intros tag [? | ? | [| [t0 | ? | ?] [| d_sx [| ? ?]]]] out H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_sha256_atom_ok d_sx out H).
Qed.

Definition parse_tagged_expr_sexp (expected_tag : string) (sx : sexp)
  : string + cert_expr :=
  match sx with
  | SList [SAtom tag; expr_sx] =>
      if String.eqb tag expected_tag then parse_cert_expr [] expr_sx
      else inl "unexpected expression field tag"
  | _ => inl "expected tagged expression S-expression"
  end.

Lemma parse_tagged_expr_wf : forall tag sx e,
  parse_tagged_expr_sexp tag sx = inr e -> wf_cert_expr [] e = true.
Proof.
  intros tag [| | [| [t0 | |] [| e_sx [| ? ?]]]] e H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_cert_expr_wf e_sx [] e H).
Qed.

Definition parse_ub_assumption_sexp (sx : sexp) : string + ub_assumption :=
  match sx with
  | SList (SAtom tag :: args) =>
      if String.eqb tag "param-noundef" then
        match args with
        | [nm_sx; w_sx] =>
            match parse_nonempty_str nm_sx, parse_bit_width_sexp w_sx with
            | inr nm, inr w => inr (UBA_ParamNoUndef nm w)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed param-noundef assumption"
        end
      else if String.eqb tag "ptr-nonnull" then
        match args with
        | [nm_sx] =>
            match parse_nonempty_str nm_sx with
            | inr nm => inr (UBA_PtrNonNull nm)
            | inl err => inl err
            end
        | _ => inl "malformed ptr-nonnull assumption"
        end
      else if String.eqb tag "ptr-aligned" then
        match args with
        | [nm_sx; al_sx] =>
            match parse_nonempty_str nm_sx, parse_u64_N al_sx with
            | inr nm, inr al =>
                if is_power_of_two_N al then inr (UBA_PtrAligned nm al)
                else inl "ptr-aligned alignment must be a power of two"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed ptr-aligned assumption"
        end
      else if String.eqb tag "ptr-dereferenceable" then
        match args with
        | [nm_sx; b_sx] =>
            match parse_nonempty_str nm_sx, parse_u64_N b_sx with
            | inr nm, inr b =>
                if (0 <? b)%N then inr (UBA_PtrDereferenceable nm b)
                else inl "ptr-dereferenceable byte count must be positive"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed ptr-dereferenceable assumption"
        end
      else if String.eqb tag "load-noundef" then
        match args with
        | [sl_sx; w_sx] =>
            match parse_nonempty_str sl_sx, parse_bit_width_sexp w_sx with
            | inr sl, inr w => inr (UBA_LoadNoUndef sl w)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed load-noundef assumption"
        end
      else if String.eqb tag "divisor-nonzero" then
        match args with
        | [d_sx] =>
            match parse_cert_expr [] d_sx with
            | inr d => inr (UBA_DivisorNonZero d)
            | inl err => inl err
            end
        | _ => inl "malformed divisor-nonzero assumption"
        end
      else if String.eqb tag "sdiv-no-overflow" then
        match args with
        | [l_sx; r_sx] =>
            match parse_cert_expr [] l_sx, parse_cert_expr [] r_sx with
            | inr l, inr r =>
                if Pos.eqb (cert_expr_bit_width l) (cert_expr_bit_width r)
                then inr (UBA_SignedDivNoOverflow l r)
                else inl "sdiv-no-overflow operand width mismatch"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed sdiv-no-overflow assumption"
        end
      else if String.eqb tag "branch-cond-defined" then
        match args with
        | [c_sx] =>
            match parse_cert_expr [] c_sx with
            | inr c =>
                if Pos.eqb (cert_expr_bit_width c) 1%positive
                then inr (UBA_BranchCondDefined c)
                else inl "branch-cond-defined expression must have width 1"
            | inl err => inl err
            end
        | _ => inl "malformed branch-cond-defined assumption"
        end
      else if String.eqb tag "unreachable-eliminated" then
        match args with
        | [] => inr UBA_UnreachableEliminated
        | _ => inl "malformed unreachable-eliminated assumption"
        end
      else inl "unknown ub-assumption tag"
  | _ => inl "malformed ub-assumption entry"
  end.

Lemma parse_ub_assumption_wf : forall sx u,
  parse_ub_assumption_sexp sx = inr u -> wf_ub_assumption u = true.
Proof.
  intros [| | [| [tag | |] args]] u H; cbn in H; try discriminate.
  destruct (String.eqb tag "param-noundef").
  - destruct args as [| nm_sx [| w_sx [| ? ?]]]; try discriminate.
    destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hnm), (parse_bit_width_supported _ _ Hw); reflexivity.
  - destruct (String.eqb tag "ptr-nonnull").
    + destruct args as [| nm_sx [| ? ?]]; try discriminate.
      destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
      inversion H; subst; cbn; exact (parse_nonempty_str_ok _ _ Hnm).
    + destruct (String.eqb tag "ptr-aligned").
      * destruct args as [| nm_sx [| al_sx [| ? ?]]]; try discriminate.
        destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
        destruct (parse_u64_N al_sx) as [| al]; [discriminate |].
        destruct (is_power_of_two_N al) eqn:Hal; [| discriminate].
        inversion H; subst; cbn; rewrite (parse_nonempty_str_ok _ _ Hnm), Hal; reflexivity.
      * destruct (String.eqb tag "ptr-dereferenceable").
        -- destruct args as [| nm_sx [| b_sx [| ? ?]]]; try discriminate.
           destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
           destruct (parse_u64_N b_sx) as [| b]; [discriminate |].
           destruct (0 <? b)%N eqn:Hb; [| discriminate].
           inversion H; subst; cbn; rewrite (parse_nonempty_str_ok _ _ Hnm), Hb; reflexivity.
        -- destruct (String.eqb tag "load-noundef").
           ++ destruct args as [| sl_sx [| w_sx [| ? ?]]]; try discriminate.
              destruct (parse_nonempty_str sl_sx) as [| sl] eqn:Hsl; [discriminate |].
              destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
              inversion H; subst; cbn.
              rewrite (parse_nonempty_str_ok _ _ Hsl), (parse_bit_width_supported _ _ Hw);
                reflexivity.
           ++ destruct (String.eqb tag "divisor-nonzero").
              ** destruct args as [| d_sx [| ? ?]]; try discriminate.
                 destruct (parse_cert_expr [] d_sx) as [| d] eqn:Hd; [discriminate |].
                 inversion H; subst; cbn; exact (parse_cert_expr_wf _ _ _ Hd).
              ** destruct (String.eqb tag "sdiv-no-overflow").
                 --- destruct args as [| l_sx [| r_sx [| ? ?]]]; try discriminate.
                     destruct (parse_cert_expr [] l_sx) as [| l] eqn:Hl; [discriminate |].
                     destruct (parse_cert_expr [] r_sx) as [| r] eqn:Hr; [discriminate |].
                     destruct (Pos.eqb (cert_expr_bit_width l) (cert_expr_bit_width r)) eqn:Hw;
                       [| discriminate].
                     inversion H; subst; cbn.
                     rewrite (parse_cert_expr_wf _ _ _ Hl), (parse_cert_expr_wf _ _ _ Hr), Hw;
                       reflexivity.
                 --- destruct (String.eqb tag "branch-cond-defined").
                     +++ destruct args as [| c_sx [| ? ?]]; try discriminate.
                         destruct (parse_cert_expr [] c_sx) as [| c] eqn:Hc; [discriminate |].
                         destruct (Pos.eqb (cert_expr_bit_width c) 1%positive) eqn:Hw;
                           [| discriminate].
                         inversion H; subst; cbn.
                         rewrite (parse_cert_expr_wf _ _ _ Hc), Hw; reflexivity.
                     +++ destruct (String.eqb tag "unreachable-eliminated"); [| discriminate].
                         destruct args as [| ? ?]; [| discriminate].
                         inversion H; subst; reflexivity.
Qed.

Definition parse_value_equiv_sexp (sx : sexp) : string + value_equivalence :=
  match sx with
  | SList [SAtom tag; sr_sx; tr_sx; w_sx; se_sx; te_sx] =>
      if String.eqb tag "equiv" then
        match parse_nonempty_str sr_sx, parse_nonempty_str tr_sx,
              parse_bit_width_sexp w_sx,
              parse_cert_expr [] se_sx, parse_cert_expr [] te_sx with
        | inr sr, inr tr, inr w, inr se, inr te =>
            if Pos.eqb (cert_expr_bit_width se) w &&
               Pos.eqb (cert_expr_bit_width te) w
            then inr (mk_value_equivalence sr tr w se te)
            else inl "value equivalence expression width mismatch"
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "expected equiv tag in value-equivs"
  | _ => inl "malformed value equivalence entry"
  end.

Lemma parse_value_equiv_wf : forall sx ve,
  parse_value_equiv_sexp sx = inr ve -> wf_value_equivalence ve = true.
Proof.
  intros [| | [| [tag | |] [| sr_sx [| tr_sx [| w_sx [| se_sx [| te_sx [| ? ?]]]]]]]] ve H;
    cbn in H; try discriminate.
  destruct (String.eqb tag "equiv"); [| discriminate].
  destruct (parse_nonempty_str sr_sx) as [| sr] eqn:Hsr; [discriminate |].
  destruct (parse_nonempty_str tr_sx) as [| tr] eqn:Htr; [discriminate |].
  destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
  destruct (parse_cert_expr [] se_sx) as [| se] eqn:Hse; [discriminate |].
  destruct (parse_cert_expr [] te_sx) as [| te] eqn:Hte; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width se) w &&
            Pos.eqb (cert_expr_bit_width te) w) eqn:Hws; [| discriminate].
  apply andb_true_iff in Hws as [Hw1 Hw2].
  inversion H; subst; unfold wf_value_equivalence; cbn.
  rewrite (parse_nonempty_str_ok _ _ Hsr), (parse_nonempty_str_ok _ _ Htr),
          (parse_bit_width_supported _ _ Hw),
          (parse_cert_expr_wf _ _ _ Hse), (parse_cert_expr_wf _ _ _ Hte),
          Hw1, Hw2; reflexivity.
Qed.

Definition parse_mem_invariant_sexp (sx : sexp) : string + memory_invariant :=
  match sx with
  | SList (SAtom tag :: args) =>
      if String.eqb tag "alloca-promoted" then
        match args with
        | [sl_sx; w_sx; e_sx] =>
            match parse_nonempty_str sl_sx, parse_bit_width_sexp w_sx,
                  parse_cert_expr [] e_sx with
            | inr sl, inr w, inr e =>
                if Pos.eqb (cert_expr_bit_width e) w
                then inr (MI_AllocaPromoted sl w e)
                else inl "alloca-promoted expression width mismatch"
            | inl err, _, _ => inl err
            | _, inl err, _ => inl err
            | _, _, inl err => inl err
            end
        | _ => inl "malformed alloca-promoted entry"
        end
      else if String.eqb tag "slot-refines" then
        match args with
        | [s1_sx; s2_sx; w_sx; e1_sx; e2_sx] =>
            match parse_nonempty_str s1_sx, parse_nonempty_str s2_sx,
                  parse_bit_width_sexp w_sx,
                  parse_cert_expr [] e1_sx, parse_cert_expr [] e2_sx with
            | inr s1, inr s2, inr w, inr e1, inr e2 =>
                if Pos.eqb (cert_expr_bit_width e1) w &&
                   Pos.eqb (cert_expr_bit_width e2) w
                then inr (MI_SlotRefines s1 s2 w e1 e2)
                else inl "slot-refines expression width mismatch"
            | inl err, _, _, _, _ => inl err
            | _, inl err, _, _, _ => inl err
            | _, _, inl err, _, _ => inl err
            | _, _, _, inl err, _ => inl err
            | _, _, _, _, inl err => inl err
            end
        | _ => inl "malformed slot-refines entry"
        end
      else inl "unknown memory invariant tag"
  | _ => inl "malformed memory invariant entry"
  end.

Lemma parse_mem_invariant_wf : forall sx mi,
  parse_mem_invariant_sexp sx = inr mi -> wf_memory_invariant mi = true.
Proof.
  intros [| | [| [tag | |] args]] mi H; cbn in H; try discriminate.
  destruct (String.eqb tag "alloca-promoted").
  - destruct args as [| sl_sx [| w_sx [| e_sx [| ? ?]]]]; try discriminate.
    destruct (parse_nonempty_str sl_sx) as [| sl] eqn:Hsl; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    destruct (parse_cert_expr [] e_sx) as [| e] eqn:He; [discriminate |].
    destruct (Pos.eqb (cert_expr_bit_width e) w) eqn:Hwe; [| discriminate].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hsl), (parse_bit_width_supported _ _ Hw),
            (parse_cert_expr_wf _ _ _ He), Hwe; reflexivity.
  - destruct (String.eqb tag "slot-refines"); [| discriminate].
    destruct args as [| s1_sx [| s2_sx [| w_sx [| e1_sx [| e2_sx [| ? ?]]]]]];
      try discriminate.
    destruct (parse_nonempty_str s1_sx) as [| s1] eqn:Hs1; [discriminate |].
    destruct (parse_nonempty_str s2_sx) as [| s2] eqn:Hs2; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    destruct (parse_cert_expr [] e1_sx) as [| e1] eqn:He1; [discriminate |].
    destruct (parse_cert_expr [] e2_sx) as [| e2] eqn:He2; [discriminate |].
    destruct (Pos.eqb (cert_expr_bit_width e1) w &&
              Pos.eqb (cert_expr_bit_width e2) w) eqn:Hws; [| discriminate].
    apply andb_true_iff in Hws as [Hw1 Hw2].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hs1), (parse_nonempty_str_ok _ _ Hs2),
            (parse_bit_width_supported _ _ Hw),
            (parse_cert_expr_wf _ _ _ He1), (parse_cert_expr_wf _ _ _ He2),
            Hw1, Hw2; reflexivity.
Qed.

Definition parse_tagged_section_list {A : Set}
  (expected_tag : string) (item_parser : sexp -> string + A) (sx : sexp)
  : string + list A :=
  match sx with
  | SList (SAtom tag :: items) =>
      if String.eqb tag expected_tag then map_parse_list item_parser items
      else inl "unexpected section tag"
  | _ => inl "expected tagged list section"
  end.

Lemma parse_tagged_section_list_wf {A : Set} :
  forall tag (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall x y, f x = inr y -> wf y = true)
         sx ys,
    parse_tagged_section_list tag f sx = inr ys -> forallb wf ys = true.
Proof.
  intros tag f wf Hwf [| | [| [t0 | |] items]] ys H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (map_parse_list_forallb f wf Hwf items ys H).
Qed.

Definition parse_block_cert_kind (sx : sexp) : string + block_cert_kind :=
  match sx with
  | SList [SAtom tag; SAtom k] =>
      if String.eqb tag "kind" then
        if String.eqb k "entry" then inr BCK_Entry
        else if String.eqb k "cutpoint" then inr BCK_Cutpoint
        else if String.eqb k "return" then inr BCK_Return
        else inl "unknown block certificate kind"
      else inl "expected kind tag in block certificate"
  | _ => inl "malformed kind field in block certificate"
  end.

Definition parse_block_cert_sexp (sx : sexp) : string + block_certificate :=
  match sx with
  | SList [SAtom tag; src_sx; tgt_sx; kind_sx; ub_sx; eq_sx; mem_sx] =>
      if String.eqb tag "block" then
        match parse_tagged_nonempty_str_sexp "src-bb" src_sx,
              parse_tagged_nonempty_str_sexp "tgt-bb" tgt_sx,
              parse_block_cert_kind kind_sx,
              parse_tagged_section_list "ub-assumptions" parse_ub_assumption_sexp ub_sx,
              parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx,
              parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx with
        | inr sbb, inr tbb, inr k, inr ubs, inr eqs, inr mems =>
            inr (mk_block_certificate sbb tbb k ubs eqs mems)
        | inl err, _, _, _, _, _ => inl err
        | _, inl err, _, _, _, _ => inl err
        | _, _, inl err, _, _, _ => inl err
        | _, _, _, inl err, _, _ => inl err
        | _, _, _, _, inl err, _ => inl err
        | _, _, _, _, _, inl err => inl err
        end
      else inl "expected block tag"
  | _ => inl "malformed block certificate"
  end.

Lemma parse_block_cert_wf : forall sx bc,
  parse_block_cert_sexp sx = inr bc -> wf_block_certificate bc = true.
Proof.
  intros [| | [| [tag | |] [| src_sx [| tgt_sx [| kind_sx [| ub_sx [| eq_sx [| mem_sx [| ? ?]]]]]]]]]
         bc H; cbn in H; try discriminate.
  destruct (String.eqb tag "block"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "src-bb" src_sx) as [| sbb] eqn:Hs; [discriminate |].
  destruct (parse_tagged_nonempty_str_sexp "tgt-bb" tgt_sx) as [| tbb] eqn:Ht; [discriminate |].
  destruct (parse_block_cert_kind kind_sx) as [| k]; [discriminate |].
  destruct (parse_tagged_section_list "ub-assumptions" parse_ub_assumption_sexp ub_sx)
    as [| ubs] eqn:Hub; [discriminate |].
  destruct (parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx)
    as [| eqs] eqn:Heq; [discriminate |].
  destruct (parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx)
    as [| mems] eqn:Hmem; [discriminate |].
  inversion H; subst; unfold wf_block_certificate; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hs),
          (parse_tagged_nonempty_str_ok _ _ _ Ht),
          (parse_tagged_section_list_wf _ _ _ parse_ub_assumption_wf _ _ Hub),
          (parse_tagged_section_list_wf _ _ _ parse_value_equiv_wf _ _ Heq),
          (parse_tagged_section_list_wf _ _ _ parse_mem_invariant_wf _ _ Hmem);
    reflexivity.
Qed.

Definition parse_cutpoint_inv_sexp (sx : sexp) : string + loop_cutpoint_invariant :=
  match sx with
  | SList [SAtom tag; sh_sx; th_sx; g_sx; eq_sx; mem_sx] =>
      if String.eqb tag "cutpoint-inv" then
        match parse_tagged_nonempty_str_sexp "src-hdr" sh_sx,
              parse_tagged_nonempty_str_sexp "tgt-hdr" th_sx,
              parse_tagged_expr_sexp "guard" g_sx,
              parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx,
              parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx with
        | inr sh, inr th, inr g, inr eqs, inr mems =>
            if Pos.eqb (cert_expr_bit_width g) 1%positive
            then inr (mk_loop_cutpoint_invariant sh th g eqs mems)
            else inl "cutpoint-inv guard expression must have width 1"
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "expected cutpoint-inv tag"
  | _ => inl "malformed cutpoint-inv entry"
  end.

Lemma parse_cutpoint_inv_wf : forall sx lci,
  parse_cutpoint_inv_sexp sx = inr lci -> wf_loop_cutpoint_invariant lci = true.
Proof.
  intros [| | [| [tag | |] [| sh_sx [| th_sx [| g_sx [| eq_sx [| mem_sx [| ? ?]]]]]]]]
         lci H; cbn in H; try discriminate.
  destruct (String.eqb tag "cutpoint-inv"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "src-hdr" sh_sx) as [| sh] eqn:Hsh; [discriminate |].
  destruct (parse_tagged_nonempty_str_sexp "tgt-hdr" th_sx) as [| th] eqn:Hth; [discriminate |].
  destruct (parse_tagged_expr_sexp "guard" g_sx) as [| g] eqn:Hg; [discriminate |].
  destruct (parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx)
    as [| eqs] eqn:Heq; [discriminate |].
  destruct (parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx)
    as [| mems] eqn:Hmem; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width g) 1%positive) eqn:Hwg; [| discriminate].
  inversion H; subst; unfold wf_loop_cutpoint_invariant; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hsh),
          (parse_tagged_nonempty_str_ok _ _ _ Hth),
          (parse_tagged_expr_wf _ _ _ Hg), Hwg,
          (parse_tagged_section_list_wf _ _ _ parse_value_equiv_wf _ _ Heq),
          (parse_tagged_section_list_wf _ _ _ parse_mem_invariant_wf _ _ Hmem);
    reflexivity.
Qed.

Definition parse_alias_witness_sexp (sx : sexp) : string + alias_witness :=
  match sx with
  | SList [SAtom tag; l_sx; r_sx] =>
      let kind_res :=
          if String.eqb tag "noalias" then inr ARK_NoAlias
          else if String.eqb tag "mustalias" then inr ARK_MustAlias
          else inl "unknown alias witness relation tag" in
      match kind_res, parse_nonempty_str l_sx, parse_nonempty_str r_sx with
      | inr k, inr l, inr r => inr (mk_alias_witness k l r)
      | inl err, _, _ => inl err
      | _, inl err, _ => inl err
      | _, _, inl err => inl err
      end
  | _ => inl "malformed alias witness entry"
  end.

Lemma parse_alias_witness_wf : forall sx aw,
  parse_alias_witness_sexp sx = inr aw -> wf_alias_witness aw = true.
Proof.
  intros [| | [| [tag | |] [| l_sx [| r_sx [| ? ?]]]]] aw H; cbn in H; try discriminate.
  destruct (if String.eqb tag "noalias" then inr ARK_NoAlias
            else if String.eqb tag "mustalias" then inr ARK_MustAlias
            else inl "unknown alias witness relation tag") as [| k]; [discriminate |].
  destruct (parse_nonempty_str l_sx) as [| l] eqn:Hl; [discriminate |].
  destruct (parse_nonempty_str r_sx) as [| r] eqn:Hr; [discriminate |].
  inversion H; subst; unfold wf_alias_witness; cbn.
  rewrite (parse_nonempty_str_ok _ _ Hl), (parse_nonempty_str_ok _ _ Hr); reflexivity.
Qed.

Definition parse_return_obligation_sexp (sx : sexp) : string + return_obligation :=
  match sx with
  | SList [SAtom rtag; body_sx] =>
      if String.eqb rtag "return" then
        match body_sx with
        | SList [SAtom vtag] =>
            if String.eqb vtag "void-equiv" then inr RO_VoidEquiv
            else inl "unknown return obligation tag"
        | SList [SAtom stag;
                 SList [SAtom wtag; w_sx];
                 src_sx; tgt_sx;
                 SList [SAtom vftag; vf_sx]] =>
            if String.eqb stag "scalar-refines" &&
               String.eqb wtag "width" &&
               String.eqb vftag "smt-verified"
            then
              match parse_bit_width_sexp w_sx,
                    parse_tagged_expr_sexp "src" src_sx,
                    parse_tagged_expr_sexp "tgt" tgt_sx,
                    parse_bool_tf vf_sx with
              | inr w, inr se, inr te, inr vf =>
                  if Pos.eqb (cert_expr_bit_width se) w &&
                     Pos.eqb (cert_expr_bit_width te) w
                  then inr (RO_ScalarRefines w se te vf)
                  else inl "scalar-refines expression width mismatch"
              | inl err, _, _, _ => inl err
              | _, inl err, _, _ => inl err
              | _, _, inl err, _ => inl err
              | _, _, _, inl err => inl err
              end
            else inl "malformed scalar-refines obligation"
        | _ => inl "malformed return obligation body"
        end
      else inl "expected return section tag"
  | _ => inl "malformed return section"
  end.

Lemma parse_return_obligation_wf : forall sx ro,
  parse_return_obligation_sexp sx = inr ro -> wf_return_obligation ro = true.
Proof.
  intros [| | [| [rtag | |] [| body_sx [| ? ?]]]] ro H; cbn in H; try discriminate.
  destruct (String.eqb rtag "return"); [| discriminate].
  destruct body_sx as [| | [| [stag | |] rest]]; try discriminate.
  destruct rest as [| [| | [| [wtag | |] [| w_sx [| ? ?]]]]
                    [| src_sx [| tgt_sx [| [| | [| [vftag | |] [| vf_sx [| ? ?]]]] [| ? ?]]]]];
    try (destruct (String.eqb stag "void-equiv"); [inversion H; subst; reflexivity | discriminate]);
    try discriminate.
  destruct (String.eqb stag "scalar-refines" && String.eqb wtag "width" &&
            String.eqb vftag "smt-verified"); [| discriminate].
  destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
  destruct (parse_tagged_expr_sexp "src" src_sx) as [| se] eqn:Hse; [discriminate |].
  destruct (parse_tagged_expr_sexp "tgt" tgt_sx) as [| te] eqn:Hte; [discriminate |].
  destruct (parse_bool_tf vf_sx) as [| vf]; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width se) w &&
            Pos.eqb (cert_expr_bit_width te) w) eqn:Hws; [| discriminate].
  apply andb_true_iff in Hws as [Hw1 Hw2].
  inversion H; subst; cbn.
  rewrite (parse_bit_width_supported _ _ Hw),
          (parse_tagged_expr_wf _ _ _ Hse), (parse_tagged_expr_wf _ _ _ Hte),
          Hw1, Hw2; reflexivity.
Qed.

Definition parse_nonempty_tagged_section {A : Set}
  (expected_tag : string) (item_parser : sexp -> string + A) (sx : sexp)
  : string + list A :=
  match sx with
  | SList (SAtom tag :: first_item :: more_items) =>
      if String.eqb tag expected_tag then
        map_parse_list item_parser (first_item :: more_items)
      else inl "unexpected optional section tag"
  | _ => inl "optional cert-v1 section must be a non-empty tagged list"
  end.

Lemma parse_nonempty_tagged_section_wf {A : Set} :
  forall tag (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall x y, f x = inr y -> wf y = true)
         sx ys,
    parse_nonempty_tagged_section tag f sx = inr ys -> forallb wf ys = true.
Proof.
  intros tag f wf Hwf [| | [| [t0 | |] [| x0 xr]]] ys H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (map_parse_list_forallb f wf Hwf (x0 :: xr) ys H).
Qed.

Definition parse_optional_tail (tail : list sexp)
  : string + (list loop_cutpoint_invariant * list alias_witness * return_obligation) :=
  match tail with
  | [ret_sx] =>
      match parse_return_obligation_sexp ret_sx with
      | inr ro => inr ([], [], ro)
      | inl err => inl err
      end
  | [sec1_sx; ret_sx] =>
      match sec1_sx with
      | SList (SAtom sec_tag :: _) =>
          if String.eqb sec_tag "loop-invariants" then
            match parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp sec1_sx,
                  parse_return_obligation_sexp ret_sx with
            | inr lcis, inr ro => inr (lcis, [], ro)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
          else if String.eqb sec_tag "alias-witnesses" then
            match parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp sec1_sx,
                  parse_return_obligation_sexp ret_sx with
            | inr aws, inr ro => inr ([], aws, ro)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
          else inl "unknown optional section in cert-v1"
      | _ => inl "malformed optional section in cert-v1"
      end
  | [loop_sx; alias_sx; ret_sx] =>
      match parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp loop_sx,
            parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp alias_sx,
            parse_return_obligation_sexp ret_sx with
      | inr lcis, inr aws, inr ro => inr (lcis, aws, ro)
      | inl err, _, _ => inl err
      | _, inl err, _ => inl err
      | _, _, inl err => inl err
      end
  | _ => inl "invalid optional/return section sequence in cert-v1"
  end.

Lemma parse_optional_tail_wf : forall tail lcis aws ro,
  parse_optional_tail tail = inr (lcis, aws, ro) ->
  forallb wf_loop_cutpoint_invariant lcis = true /\
  forallb wf_alias_witness aws = true /\
  wf_return_obligation ro = true.
Proof.
  intros tail lcis aws ro H.
  destruct tail as [| s1 [| s2 [| s3 [| ? ?]]]]; cbn in H; try discriminate.
  - destruct (parse_return_obligation_sexp s1) as [| r0] eqn:Hr; [discriminate |].
    inversion H; subst; repeat split; exact (parse_return_obligation_wf _ _ Hr).
  - destruct s1 as [| | [| [sec_tag | |] s1_rest]]; try discriminate.
    destruct (String.eqb sec_tag "loop-invariants") eqn:Hli.
    + destruct (parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp
                  (SList (SAtom sec_tag :: s1_rest))) as [| ls] eqn:Hls; [discriminate |].
      destruct (parse_return_obligation_sexp s2) as [| r0] eqn:Hr; [discriminate |].
      inversion H; subst; repeat split.
      * exact (parse_nonempty_tagged_section_wf _ _ _ parse_cutpoint_inv_wf _ _ Hls).
      * exact (parse_return_obligation_wf _ _ Hr).
    + destruct (String.eqb sec_tag "alias-witnesses") eqn:Haw; [| discriminate].
      destruct (parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp
                  (SList (SAtom sec_tag :: s1_rest))) as [| ws] eqn:Hws; [discriminate |].
      destruct (parse_return_obligation_sexp s2) as [| r0] eqn:Hr; [discriminate |].
      inversion H; subst; repeat split.
      * exact (parse_nonempty_tagged_section_wf _ _ _ parse_alias_witness_wf _ _ Hws).
      * exact (parse_return_obligation_wf _ _ Hr).
  - destruct (parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp s1)
      as [| ls] eqn:Hls; [discriminate |].
    destruct (parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp s2)
      as [| ws] eqn:Hws; [discriminate |].
    destruct (parse_return_obligation_sexp s3) as [| r0] eqn:Hr; [discriminate |].
    inversion H; subst; repeat split.
    + exact (parse_nonempty_tagged_section_wf _ _ _ parse_cutpoint_inv_wf _ _ Hls).
    + exact (parse_nonempty_tagged_section_wf _ _ _ parse_alias_witness_wf _ _ Hws).
    + exact (parse_return_obligation_wf _ _ Hr).
Qed.

Definition parse_pos_str (s : string) : option positive :=
  match parse_canonical_N s with
  | Some (Npos p) => Some p
  | _ => None
  end.

Definition parse_signed_lit_str (s : string) : option lit :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 45 then
        match parse_pos_str rest with
        | Some p => Some (Z.neg p)
        | None => None
        end
      else
        match parse_pos_str s with
        | Some p => Some (Z.pos p)
        | None => None
        end
  | EmptyString => None
  end.

Definition parse_pos_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      match parse_pos_str s with
      | Some p => inr p
      | None => inl "expected canonical positive integer in LRAT section"
      end
  | _ => inl "expected positive integer atom in LRAT section"
  end.

Definition parse_lit_sexp (sx : sexp) : string + lit :=
  match sx with
  | SAtom s =>
      match parse_signed_lit_str s with
      | Some l => inr l
      | None => inl "expected non-zero canonical literal in LRAT section"
      end
  | _ => inl "expected literal atom in LRAT section"
  end.

Definition parse_lrat_step_sexp (sx : sexp) : string + lrat_step :=
  match sx with
  | SList [SAtom tag; cid_sx; SList lit_sxs; SList hint_sxs] =>
      if String.eqb tag "add" then
        match parse_pos_sexp cid_sx,
              map_parse_list parse_lit_sexp lit_sxs,
              map_parse_list parse_pos_sexp hint_sxs with
        | inr cid, inr cl, inr hints => inr (LRAT_Add cid cl hints)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "unknown LRAT step tag"
  | SList [SAtom tag; SList cid_sxs] =>
      if String.eqb tag "del" then
        match map_parse_list parse_pos_sexp cid_sxs with
        | inr cids => inr (LRAT_Del cids)
        | inl err => inl err
        end
      else inl "unknown LRAT step tag"
  | _ => inl "malformed LRAT step S-expression"
  end.

Definition is_lrat_section_sexp (sx : sexp) : bool :=
  match sx with
  | SList (SAtom tag :: _) => String.eqb tag "lrat"
  | _ => false
  end.

Definition parse_optional_tail_with_lrat (tail : list sexp)
  : string + (list loop_cutpoint_invariant * list alias_witness *
              return_obligation * option (list lrat_step)) :=
  match rev_tr tail with
  | last_sx :: rev_prefix =>
      if is_lrat_section_sexp last_sx then
        match parse_optional_tail (rev_tr rev_prefix),
              parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp last_sx with
        | inr (lcis, aws, ro), inr pf => inr (lcis, aws, ro, Some pf)
        | inl err, _ => inl err
        | _, inl err => inl err
        end
      else
        match parse_optional_tail tail with
        | inr (lcis, aws, ro) => inr (lcis, aws, ro, None)
        | inl err => inl err
        end
  | [] => inl "missing return section in cert-v1"
  end.

Lemma parse_optional_tail_with_lrat_wf : forall tail lcis aws ro opt_pf,
  parse_optional_tail_with_lrat tail = inr (lcis, aws, ro, opt_pf) ->
  forallb wf_loop_cutpoint_invariant lcis = true /\
  forallb wf_alias_witness aws = true /\
  wf_return_obligation ro = true.
Proof.
  intros tail lcis aws ro opt_pf H.
  unfold parse_optional_tail_with_lrat in H.
  destruct (rev_tr tail) as [| last_sx rev_prefix]; [discriminate H |].
  destruct (is_lrat_section_sexp last_sx).
  - destruct (parse_optional_tail (rev_tr rev_prefix)) as [| [[ls ws] r0]] eqn:Ht;
      [discriminate H |].
    destruct (parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp last_sx)
      as [| pf]; [discriminate H |].
    inversion H; subst; exact (parse_optional_tail_wf _ _ _ _ Ht).
  - destruct (parse_optional_tail tail) as [| [[ls ws] r0]] eqn:Ht;
      [discriminate H |].
    inversion H; subst; exact (parse_optional_tail_wf _ _ _ _ Ht).
Qed.

Definition parse_cert_sexp (root : sexp) : string + proof_certificate :=
  match root with
  | SList (SAtom schema_tag :: fn_sx :: sh_sx :: th_sx :: blks_sx :: tail) =>
      if String.eqb schema_tag "cert-v1" then
        match parse_tagged_nonempty_str_sexp "fn" fn_sx,
              parse_tagged_sha256_sexp "src-sha256" sh_sx,
              parse_tagged_sha256_sexp "tgt-sha256" th_sx,
              parse_tagged_section_list "blocks" parse_block_cert_sexp blks_sx,
              parse_optional_tail_with_lrat tail with
        | inr fn_nm, inr sh, inr th, inr blks, inr (lcis, aws, ro, opt_pf) =>
            inr (mk_proof_certificate fn_nm sh th blks lcis aws ro opt_pf)
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "unsupported certificate schema tag (expected cert-v1)"
  | _ => inl "malformed cert-v1 root S-expression"
  end.

Definition parse_cert (input : string) : string + proof_certificate :=
  match parse_sexp input with
  | inl err => inl (diag "cert-parse" err)
  | inr root =>
      match parse_cert_sexp root with
      | inl err => inl (diag "cert-parse" err)
      | inr cert => inr cert
      end
  end.

Theorem parse_cert_sexp_wf : forall root cert,
  parse_cert_sexp root = inr cert -> wf_proof_certificate cert = true.
Proof.
  intros [| | [| [schema_tag | |] [| fn_sx [| sh_sx [| th_sx [| blks_sx tail]]]]]] cert H;
    cbn in H; try discriminate.
  destruct (String.eqb schema_tag "cert-v1"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "fn" fn_sx) as [| fn_nm] eqn:Hfn; [discriminate |].
  destruct (parse_tagged_sha256_sexp "src-sha256" sh_sx) as [| sh] eqn:Hsh; [discriminate |].
  destruct (parse_tagged_sha256_sexp "tgt-sha256" th_sx) as [| th] eqn:Hth; [discriminate |].
  destruct (parse_tagged_section_list "blocks" parse_block_cert_sexp blks_sx)
    as [| blks] eqn:Hblks; [discriminate |].
  destruct (parse_optional_tail_with_lrat tail) as [| [[[lcis aws] ro] opt_pf]] eqn:Htail;
    [discriminate |].
  pose proof (parse_optional_tail_with_lrat_wf _ _ _ _ _ Htail) as (Hlcis & Haws & Hro).
  inversion H; subst; unfold wf_proof_certificate; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hfn),
          (parse_tagged_sha256_ok _ _ _ Hsh),
          (parse_tagged_sha256_ok _ _ _ Hth),
          (parse_tagged_section_list_wf _ _ _ parse_block_cert_wf _ _ Hblks),
          Hlcis, Haws, Hro; reflexivity.
Qed.

Theorem parse_cert_wf : forall input cert,
  parse_cert input = inr cert -> wf_proof_certificate cert = true.
Proof.
  intros input cert H; unfold parse_cert in H.
  destruct (parse_sexp input) as [| root]; [discriminate |].
  destruct (parse_cert_sexp root) as [| c0] eqn:Es; [discriminate |].
  inversion H; subst c0; exact (parse_cert_sexp_wf root cert Es).
Qed.

(** ** 6. Syntax & Prototype Contract Soundness Gates ([F-17], [F-18], [F-19], [F-21], [F-30], [F-31], [F-32], [F-34]) *)

(** *** 6.1 Structural Comparators on Vellvm Types & Expressions *)

Definition raw_id_eqb (r1 r2 : raw_id) : bool :=
  match RawIDOrd.cmp r1 r2 with
  | Datatypes.Eq => true
  | _ => false
  end.

Lemma raw_id_eqb_eq : forall r1 r2, raw_id_eqb r1 r2 = true <-> r1 = r2.
Proof.
  intros r1 r2; unfold raw_id_eqb.
  destruct (RawIDOrd.cmp r1 r2) eqn:Hc;
    split; intros H; try discriminate; try reflexivity.
  - apply RawIDOrd.cmp_eq in Hc; exact Hc.
  - subst; rewrite (proj2 (RawIDOrd.cmp_eq r2 r2) eq_refl) in Hc; discriminate.
  - subst; rewrite (proj2 (RawIDOrd.cmp_eq r2 r2) eq_refl) in Hc; discriminate.
Qed.

Definition ident_eqb (i1 i2 : ident) : bool :=
  match i1, i2 with
  | ID_Global r1, ID_Global r2 => raw_id_eqb r1 r2
  | ID_Local r1, ID_Local r2 => raw_id_eqb r1 r2
  | _, _ => false
  end.

Lemma ident_eqb_eq : forall i1 i2, ident_eqb i1 i2 = true <-> i1 = i2.
Proof.
  intros [r1 | r1] [r2 | r2]; cbn;
    try (split; intros; discriminate);
    (rewrite raw_id_eqb_eq; split; intros H; [subst; reflexivity | inversion H; reflexivity]).
Qed.

Definition fp_variant_eqb (f1 f2 : floating_point_variant) : bool :=
  if floating_point_variant_beq f1 f2 then true else false.

Lemma fp_variant_eqb_eq : forall f1 f2, fp_variant_eqb f1 f2 = true <-> f1 = f2.
Proof.
  intros [] []; cbn; split; intros H; try reflexivity; discriminate.
Qed.

Fixpoint typ_eqb (t1 t2 : typ) {struct t1} : bool :=
  let fix list_typ_eqb (xs ys : list typ) {struct xs} : bool :=
      match xs, ys with
      | [], [] => true
      | x :: rx, y :: ry => typ_eqb x y && list_typ_eqb rx ry
      | _, _ => false
      end in
  match t1, t2 with
  | TYPE_I s1, TYPE_I s2 => Pos.eqb s1 s2
  | TYPE_B s1, TYPE_B s2 => Pos.eqb s1 s2
  | TYPE_Iptr, TYPE_Iptr => true
  | TYPE_Pointer None, TYPE_Pointer None => true
  | TYPE_Pointer (Some u1), TYPE_Pointer (Some u2) => typ_eqb u1 u2
  | TYPE_Void, TYPE_Void => true
  | TYPE_FP f1, TYPE_FP f2 => fp_variant_eqb f1 f2
  | TYPE_Label, TYPE_Label => true
  | TYPE_Token, TYPE_Token => true
  | TYPE_Metadata, TYPE_Metadata => true
  | TYPE_X86_mmx, TYPE_X86_mmx => true
  | TYPE_Array n1 u1, TYPE_Array n2 u2 => N.eqb n1 n2 && typ_eqb u1 u2
  | TYPE_Function r1 a1 v1, TYPE_Function r2 a2 v2 =>
      typ_eqb r1 r2 && list_typ_eqb a1 a2 && Bool.eqb v1 v2
  | TYPE_Struct f1, TYPE_Struct f2 => list_typ_eqb f1 f2
  | TYPE_Packed_struct f1, TYPE_Packed_struct f2 => list_typ_eqb f1 f2
  | TYPE_Opaque, TYPE_Opaque => true
  | TYPE_Vector n1 u1, TYPE_Vector n2 u2 => N.eqb n1 n2 && typ_eqb u1 u2
  | TYPE_Identified i1, TYPE_Identified i2 => ident_eqb i1 i2
  | _, _ => false
  end.

Lemma typ_eqb_refl : forall t, typ_eqb t t = true.
Proof.
  induction t as
    [ sz
    | sz
    |
    | u IHu
    |
    |
    | fp
    |
    |
    |
    |
    | sz u IHu
    | ret args varargs IHret IHargs
    | fields IHfields
    | fields IHfields
    |
    | sz u IHu
    | id ] using AstLib.typ_ind; cbn;
    try reflexivity;
    try apply Pos.eqb_refl;
    try (rewrite N.eqb_refl; exact IHu);
    try exact IHu.
  - destruct fp; reflexivity.
  - rewrite IHret, Bool.eqb_reflx, andb_true_r; cbn.
    induction args as [| u rest IH]; [reflexivity |].
    cbn; rewrite (IHargs u (or_introl eq_refl)), IH; [reflexivity |].
    intros u' Hin; apply IHargs; right; exact Hin.
  - induction fields as [| u rest IH]; [reflexivity |].
    cbn; rewrite (IHfields u (or_introl eq_refl)), IH; [reflexivity |].
    intros u' Hin; apply IHfields; right; exact Hin.
  - induction fields as [| u rest IH]; [reflexivity |].
    cbn; rewrite (IHfields u (or_introl eq_refl)), IH; [reflexivity |].
    intros u' Hin; apply IHfields; right; exact Hin.
  - exact (proj2 (ident_eqb_eq id id) eq_refl).
Qed.

Lemma typ_eqb_eq : forall t1 t2, typ_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros t1.
  induction t1 as
    [ sz1
    | sz1
    |
    | u1 IHu1
    |
    |
    | fp1
    |
    |
    |
    |
    | sz1 u1 IHu1
    | ret1 args1 varargs1 IHret1 IHargs1
    | fields1 IHfields1
    | fields1 IHfields1
    |
    | sz1 u1 IHu1
    | id1 ] using AstLib.typ_ind; intros t2; split; intros H;
    try (subst; apply typ_eqb_refl).
  - destruct t2; cbn in H; try discriminate; apply Pos.eqb_eq in H; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate; apply Pos.eqb_eq in H; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2 as [| | | [u2 |] | | | | | | | | | | | | |]; cbn in H; try discriminate.
    apply IHu1 in H; subst; reflexivity.
  - destruct t2 as [| | | [u2 |] | | | | | | | | | | | | |]; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; apply fp_variant_eqb_eq in H; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hn Ht]; apply N.eqb_eq in Hn; apply IHu1 in Ht; subst; reflexivity.
  - destruct t2 as [| | | | | | | | | | | r2 a2 v2 | | | | |]; cbn in H; try discriminate.
    rewrite !andb_true_iff in H; destruct H as ((Hr & Ha) & Hv).
    apply IHret1 in Hr; apply Bool.eqb_prop in Hv; subst r2 v2; f_equal.
    revert a2 Ha; induction args1 as [| x rx IHrx]; intros [| y ry] Ha; try discriminate; [reflexivity |].
    apply andb_true_iff in Ha as [Hxy Hrest].
    apply (IHargs1 x (or_introl eq_refl)) in Hxy; subst y; f_equal.
    apply IHrx; [intros u Hin; apply IHargs1; right; exact Hin | exact Hrest].
  - destruct t2 as [| | | | | | | | | | | | f2 | | | |]; cbn in H; try discriminate; f_equal.
    revert f2 H; induction fields1 as [| x rx IHrx]; intros [| y ry] Hf; try discriminate; [reflexivity |].
    apply andb_true_iff in Hf as [Hxy Hrest].
    apply (IHfields1 x (or_introl eq_refl)) in Hxy; subst y; f_equal.
    apply IHrx; [intros u Hin; apply IHfields1; right; exact Hin | exact Hrest].
  - destruct t2 as [| | | | | | | | | | | | | f2 | | |]; cbn in H; try discriminate; f_equal.
    revert f2 H; induction fields1 as [| x rx IHrx]; intros [| y ry] Hf; try discriminate; [reflexivity |].
    apply andb_true_iff in Hf as [Hxy Hrest].
    apply (IHfields1 x (or_introl eq_refl)) in Hxy; subst y; f_equal.
    apply IHrx; [intros u Hin; apply IHfields1; right; exact Hin | exact Hrest].
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hn Ht]; apply N.eqb_eq in Hn; apply IHu1 in Ht; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate; apply ident_eqb_eq in H; subst; reflexivity.
Qed.

Definition dtyp_eqb (d1 d2 : dtyp) : bool :=
  if dtyp_eq_dec d1 d2 then true else false.

Definition int_syntax_val_eqb (a b : int_syntax) : bool :=
  Z.eqb (BinIntDef.Z.of_num_int a) (BinIntDef.Z.of_num_int b).

Fixpoint simple_exp_dtyp_eqb (e1 e2 : exp dtyp) {struct e1} : bool :=
  match e1, e2 with
  | EXP_Ident i1, EXP_Ident i2 => ident_eqb i1 i2
  | EXP_Integer n1, EXP_Integer n2 => int_syntax_val_eqb n1 n2
  | EXP_Bool b1, EXP_Bool b2 => Bool.eqb b1 b2
  | EXP_Null, EXP_Null
  | EXP_Zero_initializer, EXP_Zero_initializer
  | EXP_Undef, EXP_Undef
  | EXP_Poison, EXP_Poison => true
  | OP_GetElementPtr f1 t1 (pt1, pe1) idxs1, OP_GetElementPtr f2 t2 (pt2, pe2) idxs2 =>
      let fix eqb_idxs (xs ys : list (dtyp * exp dtyp)) {struct xs} : bool :=
          match xs, ys with
          | [], [] => true
          | (xt, xe) :: rx, (yt, ye) :: ry =>
              dtyp_eqb xt yt && simple_exp_dtyp_eqb xe ye && eqb_idxs rx ry
          | _, _ => false
          end in
      Bool.eqb (gep_inbounds f1) (gep_inbounds f2) &&
      Bool.eqb (gep_nusw f1) (gep_nusw f2) &&
      Bool.eqb (gep_nuw f1) (gep_nuw f2) &&
      dtyp_eqb t1 t2 && dtyp_eqb pt1 pt2 &&
      simple_exp_dtyp_eqb pe1 pe2 && eqb_idxs idxs1 idxs2
  | _, _ => false
  end.

(** *** 6.2 [F-17]: Reject Target Fast-Math Flags Across All FP Operations *)

Definition list_empty_b {A : Type} (xs : list A) : bool :=
  match xs with
  | [] => true
  | _ :: _ => false
  end.

Fixpoint exp_no_fast_math {T : Set} (e : exp T) : bool :=
  let fix texp_list_ok (xs : list (T * exp T)) : bool :=
      match xs with
      | [] => true
      | (_, x) :: r => exp_no_fast_math x && texp_list_ok r
      end in
  match e with
  | EXP_Ident _ | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ => true
  | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
  | EXP_Array elts | EXP_Vector elts => texp_list_ok elts
  | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ _ v1 v2 =>
      exp_no_fast_math v1 && exp_no_fast_math v2
  | OP_FBinop _ fm _ v1 v2 | OP_FCmp _ fm _ v1 v2 =>
      list_empty_b fm && exp_no_fast_math v1 && exp_no_fast_math v2
  | OP_Fneg fm (_, v) =>
      list_empty_b fm && exp_no_fast_math v
  | OP_Conversion (CONV_Pure (Fptrunc fm)) _ v _
  | OP_Conversion (CONV_Pure (Fpext fm)) _ v _ =>
      list_empty_b fm && exp_no_fast_math v
  | OP_Conversion _ _ v _ =>
      exp_no_fast_math v
  | OP_GetElementPtr _ _ (_, pv) idxs =>
      exp_no_fast_math pv && texp_list_ok idxs
  | OP_ExtractElement (_, v1) (_, v2)
  | OP_InsertValue (_, v1) (_, v2) _ =>
      exp_no_fast_math v1 && exp_no_fast_math v2
  | OP_InsertElement (_, v1) (_, v2) (_, v3)
  | OP_ShuffleVector (_, v1) (_, v2) (_, v3) =>
      exp_no_fast_math v1 && exp_no_fast_math v2 && exp_no_fast_math v3
  | OP_ExtractValue (_, v) _
  | OP_Freeze (_, v)
  | EXP_Splat (_, v) =>
      exp_no_fast_math v
  | OP_Select fm (_, c) (_, v1) (_, v2) =>
      list_empty_b fm && exp_no_fast_math c && exp_no_fast_math v1 && exp_no_fast_math v2
  | EXP_Metadata md => metadata_no_fast_math md
  end
with metadata_no_fast_math {T : Set} (md : metadata T) : bool :=
  let fix md_list_ok (ms : list (metadata T)) : bool :=
      match ms with
      | [] => true
      | m :: r => metadata_no_fast_math m && md_list_ok r
      end in
  match md with
  | METADATA_Null | METADATA_Id _ | METADATA_Debug _ _ | METADATA_File_info _ => true
  | METADATA_Const (_, e) => exp_no_fast_math e
  | METADATA_Node ms => md_list_ok ms
  | METADATA_Pair m1 m2 => metadata_no_fast_math m1 && metadata_no_fast_math m2
  end.

Definition phi_no_fast_math {T : Set} (p : phi T) : bool :=
  match p with
  | Phi fm _ args =>
      list_empty_b fm && forallb (fun '(_, e) => exp_no_fast_math e) args
  end.

Definition ann_no_fast_math {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_fast_math_flag _ => false
  | ANN_prefix (_, e) | ANN_prologue (_, e)
  | ANN_personality (_, e) | ANN_num_elements (_, e) => exp_no_fast_math e
  | _ => true
  end.

Definition instr_no_fast_math {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_Comment _ | INSTR_Fence _ _ => true
  | INSTR_Op e => exp_no_fast_math e
  | INSTR_Call (_, fn_e) args anns _ =>
      exp_no_fast_math fn_e &&
      forallb (fun '((_, ae), _) => exp_no_fast_math ae) args &&
      forallb ann_no_fast_math anns
  | INSTR_Alloca _ anns => forallb ann_no_fast_math anns
  | INSTR_Load _ (_, pe) anns => exp_no_fast_math pe && forallb ann_no_fast_math anns
  | INSTR_Store (_, ve) (_, pe) anns =>
      exp_no_fast_math ve && exp_no_fast_math pe && forallb ann_no_fast_math anns
  | INSTR_AtomicCmpXchg cx =>
      exp_no_fast_math (snd (c_ptr cx)) &&
      exp_no_fast_math (snd (c_cmp cx)) &&
      exp_no_fast_math (snd (c_new cx))
  | INSTR_AtomicRMW rmw =>
      exp_no_fast_math (snd (a_ptr rmw)) && exp_no_fast_math (snd (a_val rmw))
  | INSTR_VAArg (_, ve) _ => exp_no_fast_math ve
  | INSTR_LandingPad _ _ _ => true
  end.

Definition term_no_fast_math {T : Set} (tm : terminator T) : bool :=
  match tm with
  | TERM_Ret (_, e) | TERM_Br (_, e) _ _ | TERM_Switch (_, e) _ _
  | TERM_IndirectBr (_, e) _ _ | TERM_Resume (_, e) => exp_no_fast_math e
  | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => true
  | TERM_Invoke (_, fn_e) args _ _ anns _ =>
      exp_no_fast_math fn_e &&
      forallb (fun '((_, ae), _) => exp_no_fast_math ae) args &&
      forallb ann_no_fast_math anns
  end.

Definition block_no_fast_math {T : Set} (b : block T) : bool :=
  forallb (fun '(_, p, _) => phi_no_fast_math p) (blk_phis b) &&
  forallb (fun '(_, ins, _) => instr_no_fast_math ins) (blk_code b) &&
  let '(_, tm, _) := blk_term b in term_no_fast_math tm.

Definition cfg_no_fast_math {T : Set} (G : CFG.cfg T) : bool :=
  forallb block_no_fast_math (blks G).

(** *** 6.3 [F-18]: Reject Volatile, Atomic, Ordering, Syncscope, Inline Asm, and Fences *)

Fixpoint exp_no_inline_asm {T : Set} (e : exp T) : bool :=
  let fix texp_list_ok (xs : list (T * exp T)) : bool :=
      match xs with
      | [] => true
      | (_, x) :: r => exp_no_inline_asm x && texp_list_ok r
      end in
  match e with
  | EXP_Asm _ _ _ _ _ _ => false
  | EXP_Ident _ | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_BlockAddress _ _ | EXP_Metadata _ => true
  | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
  | EXP_Array elts | EXP_Vector elts => texp_list_ok elts
  | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ _ v1 v2
  | OP_FBinop _ _ _ v1 v2 | OP_FCmp _ _ _ v1 v2 =>
      exp_no_inline_asm v1 && exp_no_inline_asm v2
  | OP_Fneg _ (_, v) | OP_Conversion _ _ v _
  | OP_ExtractValue (_, v) _ | OP_Freeze (_, v) | EXP_Splat (_, v) =>
      exp_no_inline_asm v
  | OP_GetElementPtr _ _ (_, pv) idxs =>
      exp_no_inline_asm pv && texp_list_ok idxs
  | OP_ExtractElement (_, v1) (_, v2) | OP_InsertValue (_, v1) (_, v2) _ =>
      exp_no_inline_asm v1 && exp_no_inline_asm v2
  | OP_InsertElement (_, v1) (_, v2) (_, v3)
  | OP_ShuffleVector (_, v1) (_, v2) (_, v3)
  | OP_Select _ (_, v1) (_, v2) (_, v3) =>
      exp_no_inline_asm v1 && exp_no_inline_asm v2 && exp_no_inline_asm v3
  end.

Definition ann_no_concurrency {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_volatile | ANN_atomic | ANN_syncscope _ | ANN_ordering _ => false
  | _ => true
  end.

Definition instr_no_concurrency {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_Fence _ _ | INSTR_AtomicCmpXchg _ | INSTR_AtomicRMW _ => false
  | INSTR_Comment _ => true
  | INSTR_Op e => exp_no_inline_asm e
  | INSTR_Call (_, fn_e) args anns _ =>
      exp_no_inline_asm fn_e &&
      forallb (fun '((_, ae), _) => exp_no_inline_asm ae) args &&
      forallb ann_no_concurrency anns
  | INSTR_Alloca _ anns => forallb ann_no_concurrency anns
  | INSTR_Load _ (_, pe) anns => exp_no_inline_asm pe && forallb ann_no_concurrency anns
  | INSTR_Store (_, ve) (_, pe) anns =>
      exp_no_inline_asm ve && exp_no_inline_asm pe && forallb ann_no_concurrency anns
  | INSTR_VAArg (_, ve) _ => exp_no_inline_asm ve
  | INSTR_LandingPad _ _ _ => true
  end.

Definition term_no_concurrency {T : Set} (tm : terminator T) : bool :=
  match tm with
  | TERM_Ret (_, e) | TERM_Br (_, e) _ _ | TERM_Switch (_, e) _ _
  | TERM_IndirectBr (_, e) _ _ | TERM_Resume (_, e) => exp_no_inline_asm e
  | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => true
  | TERM_Invoke (_, fn_e) args _ _ anns _ =>
      exp_no_inline_asm fn_e &&
      forallb (fun '((_, ae), _) => exp_no_inline_asm ae) args &&
      forallb ann_no_concurrency anns
  end.

Definition block_no_concurrency {T : Set} (b : block T) : bool :=
  forallb (fun '(_, Phi _ _ args, _) => forallb (fun '(_, e) => exp_no_inline_asm e) args)
          (blk_phis b) &&
  forallb (fun '(_, ins, _) => instr_no_concurrency ins) (blk_code b) &&
  let '(_, tm, _) := blk_term b in term_no_concurrency tm.

Definition cfg_no_concurrency {T : Set} (G : CFG.cfg T) : bool :=
  forallb block_no_concurrency (blks G).

(** *** 6.4 [F-19], [F-32] & [F-60]: Prototype Contract, Calling Conventions, ABI Parameter Attributes, and Function Attributes *)

Fixpoint forallb2 {A B : Type} (f : A -> B -> bool) (xs : list A) (ys : list B) {struct xs} : bool :=
  match xs, ys with
  | [], [] => true
  | x :: rx, y :: ry => f x y && forallb2 f rx ry
  | _, _ => false
  end.

Definition is_unmodeled_param_attr (pa : param_attr) : bool :=
  match pa with
  | PARAMATTR_Byval _
  | PARAMATTR_Byref _
  | PARAMATTR_Preallocated _
  | PARAMATTR_Inalloca _
  | PARAMATTR_Initializes _ => true
  | _ => false
  end.

Definition is_abi_param_attr (pa : param_attr) : bool :=
  match pa with
  | PARAMATTR_Zeroext
  | PARAMATTR_Signext
  | PARAMATTR_Inreg
  | PARAMATTR_Sret _
  | PARAMATTR_Swiftself
  | PARAMATTR_Swiftasync
  | PARAMATTR_Swifterror => true
  | _ => false
  end.

Definition param_attr_eqb (a b : param_attr) : bool :=
  match a, b with
  | PARAMATTR_Zeroext, PARAMATTR_Zeroext
  | PARAMATTR_Signext, PARAMATTR_Signext
  | PARAMATTR_Inreg, PARAMATTR_Inreg
  | PARAMATTR_Noalias, PARAMATTR_Noalias
  | PARAMATTR_Nocapture, PARAMATTR_Nocapture
  | PARAMATTR_Nofree, PARAMATTR_Nofree
  | PARAMATTR_Nest, PARAMATTR_Nest
  | PARAMATTR_Returned, PARAMATTR_Returned
  | PARAMATTR_Nonnull, PARAMATTR_Nonnull
  | PARAMATTR_Swiftself, PARAMATTR_Swiftself
  | PARAMATTR_Swiftasync, PARAMATTR_Swiftasync
  | PARAMATTR_Swifterror, PARAMATTR_Swifterror
  | PARAMATTR_Immarg, PARAMATTR_Immarg
  | PARAMATTR_Noundef, PARAMATTR_Noundef
  | PARAMATTR_Nofreeobj, PARAMATTR_Nofreeobj
  | PARAMATTR_Allocalign, PARAMATTR_Allocalign
  | PARAMATTR_Allocptr, PARAMATTR_Allocptr
  | PARAMATTR_Readnone, PARAMATTR_Readnone
  | PARAMATTR_Readonly, PARAMATTR_Readonly
  | PARAMATTR_Writeonly, PARAMATTR_Writeonly
  | PARAMATTR_Writable, PARAMATTR_Writable
  | PARAMATTR_Dead_on_unwind, PARAMATTR_Dead_on_unwind => true
  | PARAMATTR_Byval t1, PARAMATTR_Byval t2
  | PARAMATTR_Byref t1, PARAMATTR_Byref t2
  | PARAMATTR_Preallocated t1, PARAMATTR_Preallocated t2
  | PARAMATTR_Inalloca t1, PARAMATTR_Inalloca t2
  | PARAMATTR_Sret t1, PARAMATTR_Sret t2
  | PARAMATTR_Elementtype t1, PARAMATTR_Elementtype t2 => typ_eqb t1 t2
  | PARAMATTR_Align n1, PARAMATTR_Align n2
  | PARAMATTR_Dereferenceable n1, PARAMATTR_Dereferenceable n2
  | PARAMATTR_Dereferenceable_or_null n1, PARAMATTR_Dereferenceable_or_null n2
  | PARAMATTR_Alignstack n1, PARAMATTR_Alignstack n2 => int_syntax_val_eqb n1 n2
  | PARAMATTR_Nofpclass m1, PARAMATTR_Nofpclass m2 => Z.eqb m1 m2
  | PARAMATTR_Dead_on_return None, PARAMATTR_Dead_on_return None => true
  | PARAMATTR_Dead_on_return (Some n1), PARAMATTR_Dead_on_return (Some n2) =>
      int_syntax_val_eqb n1 n2
  | PARAMATTR_Range t1 l1 h1, PARAMATTR_Range t2 l2 h2 =>
      typ_eqb t1 t2 && int_syntax_val_eqb l1 l2 && int_syntax_val_eqb h1 h2
  | PARAMATTR_Initializes xs1, PARAMATTR_Initializes xs2 =>
      forallb2 (fun '(a1, b1) '(a2, b2) => int_syntax_val_eqb a1 a2 && int_syntax_val_eqb b1 b2)
               xs1 xs2
  | PARAMATTR_Captures (l1, r1), PARAMATTR_Captures (l2, r2) =>
      forallb2 String.eqb l1 l2 && forallb2 String.eqb r1 r2
  | _, _ => false
  end.

Definition opt_int_syntax_val_eqb (o1 o2 : option int_syntax) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x1, Some x2 => int_syntax_val_eqb x1 x2
  | _, _ => false
  end.

Definition opt_range_val_eqb (o1 o2 : option (int_syntax * int_syntax)) : bool :=
  match o1, o2 with
  | None, None => true
  | Some (l1, h1), Some (l2, h2) => int_syntax_val_eqb l1 l2 && int_syntax_val_eqb h1 h2
  | _, _ => false
  end.

Definition opt_Z_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with
  | None, None => true
  | Some z1, Some z2 => Z.eqb z1 z2
  | _, _ => false
  end.

Definition opt_deref_refines_b (src_d tgt_d : option (bool * int_syntax)) : bool :=
  match tgt_d with
  | None => true
  | Some (t_ornull, t_n) =>
      match src_d with
      | None => false
      | Some (s_ornull, s_n) =>
          Bool.eqb s_ornull t_ornull && int_syntax_val_eqb s_n t_n
      end
  end.

Definition opt_is_some {A : Type} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Definition value_attrs_poison_match_b (src_attrs tgt_attrs : list param_attr) : bool :=
  implb (existsb attr_is_noundef tgt_attrs) (existsb attr_is_noundef src_attrs) &&
  Bool.eqb (existsb attr_is_nonnull src_attrs) (existsb attr_is_nonnull tgt_attrs) &&
  opt_int_syntax_val_eqb (find_option attr_align src_attrs)
                         (find_option attr_align tgt_attrs) &&
  opt_range_val_eqb (find_option attr_range src_attrs)
                    (find_option attr_range tgt_attrs) &&
  opt_Z_eqb (find_option attr_nofpclass src_attrs)
            (find_option attr_nofpclass tgt_attrs) &&
  opt_deref_refines_b (find_option attr_dereferenceable src_attrs)
                      (find_option attr_dereferenceable tgt_attrs).

Definition attr_subset_b (sub sup : list param_attr) : bool :=
  forallb (fun a => existsb (param_attr_eqb a) sup) sub.

Definition abi_attrs_match_b (l1 l2 : list param_attr) : bool :=
  let a1 := List.filter is_abi_param_attr l1 in
  let a2 := List.filter is_abi_param_attr l2 in
  attr_subset_b a1 a2 && attr_subset_b a2 a1.

Definition param_attrs_refine_b (src_attrs tgt_attrs : list param_attr) : bool :=
  forallb (fun a => negb (is_unmodeled_param_attr a)) src_attrs &&
  forallb (fun a => negb (is_unmodeled_param_attr a)) tgt_attrs &&
  abi_attrs_match_b src_attrs tgt_attrs &&
  attr_subset_b tgt_attrs src_attrs &&
  value_attrs_poison_match_b src_attrs tgt_attrs.

Definition ret_attrs_refine_b (src_rattrs tgt_rattrs : list param_attr) : bool :=
  param_attrs_refine_b src_rattrs tgt_rattrs &&
  implb (opt_is_some (find_option attr_dereferenceable tgt_rattrs))
        (existsb attr_is_noundef src_rattrs).

Definition mem_loc_eqb (x y : mem_loc) : bool :=
  match x, y with
  | LOC_Default, LOC_Default
  | LOC_Argmem, LOC_Argmem
  | LOC_Inaccessiblemem, LOC_Inaccessiblemem
  | LOC_Errnomem, LOC_Errnomem => true
  | _, _ => false
  end.

Definition mem_access_kind_eqb (x y : mem_access_kind) : bool :=
  match x, y with
  | ACC_None, ACC_None
  | ACC_Read, ACC_Read
  | ACC_Write, ACC_Write
  | ACC_Readwrite, ACC_Readwrite => true
  | _, _ => false
  end.

Definition fn_attr_nullary_tag (x : fn_attr) : option positive :=
  match x with
  | FNATTR_Alwaysinline => Some 1%positive
  | FNATTR_Builtin => Some 2%positive
  | FNATTR_Cold => Some 3%positive
  | FNATTR_Convergent => Some 4%positive
  | FNATTR_Disable_sanitizer_instrumentation => Some 5%positive
  | FNATTR_Fn_ret_thunk_extern => Some 6%positive
  | FNATTR_Hot => Some 7%positive
  | FNATTR_Inaccessiblememonly => Some 8%positive
  | FNATTR_Inaccessiblemem_or_argmemonly => Some 9%positive
  | FNATTR_Inlinehint => Some 10%positive
  | FNATTR_Jumptable => Some 11%positive
  | FNATTR_Minsize => Some 12%positive
  | FNATTR_Naked => Some 13%positive
  | FNATTR_No_jump_tables => Some 14%positive
  | FNATTR_Nobuiltin => Some 15%positive
  | FNATTR_Noduplicate => Some 16%positive
  | FNATTR_Nofree => Some 17%positive
  | FNATTR_Noimplicitfloat => Some 18%positive
  | FNATTR_Noinline => Some 19%positive
  | FNATTR_Nomerge => Some 20%positive
  | FNATTR_Nonlazybind => Some 21%positive
  | FNATTR_Noprofile => Some 22%positive
  | FNATTR_Noredzone => Some 23%positive
  | FNATTR_Indirect_tls_seg_refs => Some 24%positive
  | FNATTR_Noreturn => Some 25%positive
  | FNATTR_Norecurse => Some 26%positive
  | FNATTR_Willreturn => Some 27%positive
  | FNATTR_Nosync => Some 28%positive
  | FNATTR_Nounwind => Some 29%positive
  | FNATTR_Nocreateundeforpoison => Some 30%positive
  | FNATTR_Nosanitize_bounds => Some 31%positive
  | FNATTR_Nosanitize_coverage => Some 32%positive
  | FNATTR_Null_pointer_is_valid => Some 33%positive
  | FNATTR_Optforfuzzing => Some 34%positive
  | FNATTR_Optnone => Some 35%positive
  | FNATTR_Optsize => Some 36%positive
  | FNATTR_Readnone => Some 37%positive
  | FNATTR_Readonly => Some 38%positive
  | FNATTR_Writeonly => Some 39%positive
  | FNATTR_Argmemonly => Some 40%positive
  | FNATTR_Returns_twice => Some 41%positive
  | FNATTR_Safestack => Some 42%positive
  | FNATTR_Sanitize_address => Some 43%positive
  | FNATTR_Sanitize_memory => Some 44%positive
  | FNATTR_Sanitize_thread => Some 45%positive
  | FNATTR_Sanitize_hwaddress => Some 46%positive
  | FNATTR_Sanitize_memtag => Some 47%positive
  | FNATTR_Speculative_load_hardening => Some 48%positive
  | FNATTR_Speculatable => Some 49%positive
  | FNATTR_Ssp => Some 50%positive
  | FNATTR_Sspstrong => Some 51%positive
  | FNATTR_Sspreq => Some 52%positive
  | FNATTR_Strictfp => Some 53%positive
  | FNATTR_Tls_load_hoist => Some 54%positive
  | FNATTR_Nocf_check => Some 55%positive
  | FNATTR_Shadowcallstack => Some 56%positive
  | FNATTR_Mustprogress => Some 57%positive
  | _ => None
  end.

Definition fn_attr_eqb (x y : fn_attr) : bool :=
  match fn_attr_nullary_tag x, fn_attr_nullary_tag y with
  | Some t1, Some t2 => Pos.eqb t1 t2
  | None, None =>
      match x, y with
      | FNATTR_Alignstack a1, FNATTR_Alignstack a2 => int_syntax_val_eqb a1 a2
      | FNATTR_Allockind k1, FNATTR_Allockind k2 => String.eqb k1 k2
      | FNATTR_Allocsize a1 b1, FNATTR_Allocsize a2 b2 =>
          int_syntax_val_eqb a1 a2 && opt_int_syntax_val_eqb b1 b2
      | FNATTR_Uwtable None, FNATTR_Uwtable None => true
      | FNATTR_Uwtable (Some s1), FNATTR_Uwtable (Some s2) => Bool.eqb s1 s2
      | FNATTR_Vscale_range lo1 hi1, FNATTR_Vscale_range lo2 hi2 =>
          int_syntax_val_eqb lo1 lo2 && opt_int_syntax_val_eqb hi1 hi2
      | FNATTR_String s1, FNATTR_String s2 => String.eqb s1 s2
      | FNATTR_Key_value (k1, v1), FNATTR_Key_value (k2, v2) =>
          String.eqb k1 k2 && String.eqb v1 v2
      | FNATTR_Attr_grp g1, FNATTR_Attr_grp g2 => Z.eqb g1 g2
      | FNATTR_Memory e1, FNATTR_Memory e2 =>
          forallb2 (fun '(l1, a1) '(l2, a2) => mem_loc_eqb l1 l2 && mem_access_kind_eqb a1 a2)
                   e1 e2
      | FNATTR_UNKNOWN s1, FNATTR_UNKNOWN s2 => String.eqb s1 s2
      | _, _ => false
      end
  | _, _ => false
  end.

Definition is_unmodeled_fn_attr (fa : fn_attr) : bool :=
  match fa with
  | FNATTR_Naked
  | FNATTR_Strictfp
  | FNATTR_Returns_twice
  | FNATTR_Attr_grp _
  | FNATTR_UNKNOWN _ => true
  | _ => false
  end.

Definition is_semantic_fn_attr (fa : fn_attr) : bool :=
  match fa with
  | FNATTR_Noreturn
  | FNATTR_Nocreateundeforpoison
  | FNATTR_Nounwind
  | FNATTR_Willreturn
  | FNATTR_Mustprogress
  | FNATTR_Norecurse
  | FNATTR_Nosync
  | FNATTR_Nofree
  | FNATTR_Convergent
  | FNATTR_Noduplicate
  | FNATTR_Nomerge
  | FNATTR_Readnone
  | FNATTR_Readonly
  | FNATTR_Writeonly
  | FNATTR_Argmemonly
  | FNATTR_Inaccessiblememonly
  | FNATTR_Inaccessiblemem_or_argmemonly
  | FNATTR_Memory _
  | FNATTR_Null_pointer_is_valid
  | FNATTR_Speculatable
  | FNATTR_Alignstack _
  | FNATTR_Allockind _
  | FNATTR_Allocsize _ _
  | FNATTR_Nobuiltin
  | FNATTR_Builtin => true
  | _ => false
  end.

Definition check_fn_attrs_contract (src_fattrs tgt_fattrs : list fn_attr) : bool :=
  forallb (fun a => negb (is_unmodeled_fn_attr a)) src_fattrs &&
  forallb (fun a => negb (is_unmodeled_fn_attr a)) tgt_fattrs &&
  forallb (fun a => implb (is_semantic_fn_attr a) (existsb (fn_attr_eqb a) src_fattrs)) tgt_fattrs &&
  implb (existsb fn_attr_is_noreturn tgt_fattrs)
        (existsb fn_attr_is_noreturn src_fattrs) &&
  implb (existsb fn_attr_is_nounwind tgt_fattrs)
        (existsb fn_attr_is_nounwind src_fattrs) &&
  implb (existsb fn_attr_is_nocreateundeforpoison tgt_fattrs)
        (existsb fn_attr_is_nocreateundeforpoison src_fattrs).

Lemma check_fn_attrs_contract_inv :
  forall src_fattrs tgt_fattrs,
    check_fn_attrs_contract src_fattrs tgt_fattrs = true ->
    forallb (fun a => negb (is_unmodeled_fn_attr a)) src_fattrs = true /\
    forallb (fun a => negb (is_unmodeled_fn_attr a)) tgt_fattrs = true /\
    forallb (fun a => implb (is_semantic_fn_attr a) (existsb (fn_attr_eqb a) src_fattrs)) tgt_fattrs = true /\
    (existsb fn_attr_is_noreturn tgt_fattrs = true ->
     existsb fn_attr_is_noreturn src_fattrs = true) /\
    (existsb fn_attr_is_nounwind tgt_fattrs = true ->
     existsb fn_attr_is_nounwind src_fattrs = true) /\
    (existsb fn_attr_is_nocreateundeforpoison tgt_fattrs = true ->
     existsb fn_attr_is_nocreateundeforpoison src_fattrs = true).
Proof.
  intros src_fattrs tgt_fattrs H; unfold check_fn_attrs_contract in H.
  rewrite !andb_true_iff in H.
  destruct H as (((((Hu1 & Hu2) & Hsem) & Hnr) & Hnuw) & Hnc).
  repeat split; try assumption; intros Hx; rewrite Hx in *; cbn in *; assumption.
Qed.

Definition decl_ann_supported {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_inalloca | ANN_personality _
  | ANN_volatile | ANN_atomic | ANN_syncscope _ | ANN_ordering _
  | ANN_fast_math_flag _ => false
  | ANN_ret_attribute pa => negb (is_unmodeled_param_attr pa)
  | ANN_fun_attribute fa => negb (is_unmodeled_fn_attr fa)
  | _ => true
  end.

Definition cf_raw_id_str (rid : raw_id) : string :=
  match rid with
  | Name s => s
  | Anon z => diag_Z_dec z
  | Raw z => "_RAW_" ++ diag_Z_dec z
  end.

Definition check_prototype_contract (src_decl tgt_decl : declaration typ) : bool :=
  raw_id_eqb (dc_name src_decl) (dc_name tgt_decl) &&
  match dc_type src_decl, dc_type tgt_decl with
  | TYPE_Function sret sargs false, TYPE_Function tret targs false =>
      let '(s_rattrs, s_pattrs) := dc_param_attrs src_decl in
      let '(t_rattrs, t_pattrs) := dc_param_attrs tgt_decl in
      typ_eqb sret tret &&
      forallb2 typ_eqb sargs targs &&
      Nat.eqb (List.length s_pattrs) (List.length sargs) &&
      Nat.eqb (List.length t_pattrs) (List.length targs) &&
      cconv_eqb (anns_cconv (dc_annotations src_decl))
                (anns_cconv (dc_annotations tgt_decl)) &&
      ret_attrs_refine_b s_rattrs t_rattrs &&
      forallb2 param_attrs_refine_b s_pattrs t_pattrs &&
      check_fn_attrs_contract (dc_attrs src_decl) (dc_attrs tgt_decl) &&
      check_fn_attrs_contract
        (dc_attrs src_decl ++ ann_fun_attributes (dc_annotations src_decl))
        (dc_attrs tgt_decl ++ ann_fun_attributes (dc_annotations tgt_decl)) &&
      forallb decl_ann_supported (dc_annotations src_decl) &&
      forallb decl_ann_supported (dc_annotations tgt_decl)
  | _, _ => false
  end.

Fixpoint cf_first_mismatch_idx {A B : Type}
  (p : A -> B -> bool) (idx : nat) (xs : list A) (ys : list B) {struct xs} : nat :=
  match xs, ys with
  | x :: rx, y :: ry =>
      if p x y then cf_first_mismatch_idx p (S idx) rx ry else idx
  | _, _ => idx
  end.

Definition check_prototype_contract_diag
  (src_decl tgt_decl : declaration typ) : string + unit :=
  let fn_s := cf_raw_id_str (dc_name src_decl) in
  let pfx : string := ("function '" ++ fn_s ++ "': ")%string in
  bind_err
    (guard_err (raw_id_eqb (dc_name src_decl) (dc_name tgt_decl))
      (fun _ => diag "ir-proto"
        ("function name mismatch: source '" ++ fn_s ++ "' vs target '" ++
         cf_raw_id_str (dc_name tgt_decl) ++ "'")))
    (fun _ =>
  match dc_type src_decl, dc_type tgt_decl with
  | TYPE_Function sret sargs false, TYPE_Function tret targs false =>
      let '(s_rattrs, s_pattrs) := dc_param_attrs src_decl in
      let '(t_rattrs, t_pattrs) := dc_param_attrs tgt_decl in
      bind_err
        (guard_err (typ_eqb sret tret)
          (fun _ => diag "ir-proto" (pfx ++ "source and target return types differ")))
        (fun _ =>
      bind_err
        (guard_err (forallb2 typ_eqb sargs targs)
          (fun _ => diag "ir-proto"
            (pfx ++ "parameter type or arity mismatch at param #" ++
             diag_nat_dec (cf_first_mismatch_idx typ_eqb 0 sargs targs))))
        (fun _ =>
      bind_err
        (guard_err (Nat.eqb (List.length s_pattrs) (List.length sargs))
          (fun _ => diag "ir-proto"
            (pfx ++ "source param attribute list length disagrees with argument count")))
        (fun _ =>
      bind_err
        (guard_err (Nat.eqb (List.length t_pattrs) (List.length targs))
          (fun _ => diag "ir-proto"
            (pfx ++ "target param attribute list length disagrees with argument count")))
        (fun _ =>
      bind_err
        (guard_err
          (cconv_eqb (anns_cconv (dc_annotations src_decl))
                     (anns_cconv (dc_annotations tgt_decl)))
          (fun _ => diag "ir-proto" (pfx ++ "calling convention mismatch between source and target")))
        (fun _ =>
      bind_err
        (guard_err (ret_attrs_refine_b s_rattrs t_rattrs)
          (fun _ => diag "ir-proto" (pfx ++ "target return attributes violate refinement contract")))
        (fun _ =>
      bind_err
        (guard_err (forallb2 param_attrs_refine_b s_pattrs t_pattrs)
          (fun _ => diag "ir-proto"
            (pfx ++ "target parameter attributes violate refinement contract at param #" ++
             diag_nat_dec (cf_first_mismatch_idx param_attrs_refine_b 0 s_pattrs t_pattrs))))
        (fun _ =>
      bind_err
        (guard_err (check_fn_attrs_contract (dc_attrs src_decl) (dc_attrs tgt_decl))
          (fun _ => diag "ir-proto" (pfx ++ "function attributes violate refinement/modeling contract")))
        (fun _ =>
      bind_err
        (guard_err
          (check_fn_attrs_contract
            (dc_attrs src_decl ++ ann_fun_attributes (dc_annotations src_decl))
            (dc_attrs tgt_decl ++ ann_fun_attributes (dc_annotations tgt_decl)))
          (fun _ => diag "ir-proto" (pfx ++ "annotation function attributes violate refinement/modeling contract")))
        (fun _ =>
      bind_err
        (guard_err (forallb decl_ann_supported (dc_annotations src_decl))
          (fun _ => diag "ir-proto" (pfx ++ "unsupported declaration annotation on source function")))
        (fun _ =>
      guard_err (forallb decl_ann_supported (dc_annotations tgt_decl))
        (fun _ => diag "ir-proto" (pfx ++ "unsupported declaration annotation on target function"))))))))))))
  | _, _ =>
      inl (diag "ir-proto" (pfx ++ "varargs or non-function prototype is unsupported"))
  end).

Lemma check_prototype_contract_diag_sound :
  forall src_decl tgt_decl,
    check_prototype_contract_diag src_decl tgt_decl = inr tt ->
    check_prototype_contract src_decl tgt_decl = true.
Proof.
  intros src_decl tgt_decl H.
  unfold check_prototype_contract_diag in H; unfold check_prototype_contract.
  destruct (raw_id_eqb (dc_name src_decl) (dc_name tgt_decl));
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (dc_type src_decl) as [| | | | | | | | | | | sret sargs [|] | | | | |],
           (dc_type tgt_decl) as [| | | | | | | | | | | tret targs [|] | | | | |];
    try discriminate H.
  destruct (dc_param_attrs src_decl) as [s_rattrs s_pattrs],
           (dc_param_attrs tgt_decl) as [t_rattrs t_pattrs].
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | guard_err ?c _ = inr tt =>
      destruct c; cbn [guard_err] in H; [| discriminate H]
  end.
  reflexivity.
Qed.

Definition ann_supported_abi {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_inalloca => false
  | ANN_ret_attribute pa => negb (is_unmodeled_param_attr pa)
  | _ => true
  end.

Definition instr_supported_abi {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_Call _ args anns _ =>
      forallb (fun '(_, pas) => forallb (fun pa => negb (is_unmodeled_param_attr pa)) pas) args &&
      forallb ann_supported_abi anns
  | INSTR_Alloca _ anns | INSTR_Load _ _ anns | INSTR_Store _ _ anns =>
      forallb ann_supported_abi anns
  | _ => true
  end.

Definition cfg_supported_abi {T : Set} (G : CFG.cfg T) : bool :=
  forallb (fun b => forallb (fun '(_, ins, _) => instr_supported_abi ins) (blk_code b)) (blks G).

(** *** 6.5 [F-21]: Reject Target-Invented [OP_GetElementPtr] [inbounds]/[nusw]/[nuw] Flags *)

Definition gep_flags_is_none (gf : gep_flags) : bool :=
  negb (gep_inbounds gf) && negb (gep_nusw gf) && negb (gep_nuw gf).

Definition gep_flags_le (tgt_f src_f : gep_flags) : bool :=
  implb (gep_inbounds tgt_f) (gep_inbounds src_f) &&
  implb (gep_nusw tgt_f) (gep_nusw src_f || gep_inbounds src_f) &&
  implb (gep_nuw tgt_f) (gep_nuw src_f).

Record gep_site : Set :=
  mk_gep_site {
    gs_flags : gep_flags;
    gs_base_ty : dtyp;
    gs_ptr : dtyp * exp dtyp;
    gs_idxs : list (dtyp * exp dtyp);
  }.

Fixpoint collect_exp_geps_acc (e : exp dtyp) (acc : list gep_site) {struct e} : list gep_site :=
  let fix collect_texps (xs : list (dtyp * exp dtyp)) (a : list gep_site) {struct xs} : list gep_site :=
      match xs with
      | [] => a
      | (_, x) :: r => collect_texps r (collect_exp_geps_acc x a)
      end in
  match e with
  | EXP_Ident _ | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ | EXP_Metadata _ => acc
  | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
  | EXP_Array elts | EXP_Vector elts => collect_texps elts acc
  | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ _ v1 v2
  | OP_FBinop _ _ _ v1 v2 | OP_FCmp _ _ _ v1 v2 =>
      collect_exp_geps_acc v2 (collect_exp_geps_acc v1 acc)
  | OP_Fneg _ (_, v) | OP_Conversion _ _ v _
  | OP_ExtractValue (_, v) _ | OP_Freeze (_, v) | EXP_Splat (_, v) =>
      collect_exp_geps_acc v acc
  | OP_GetElementPtr gf t ptr idxs =>
      collect_texps idxs (collect_exp_geps_acc (snd ptr) (mk_gep_site gf t ptr idxs :: acc))
  | OP_ExtractElement (_, v1) (_, v2) | OP_InsertValue (_, v1) (_, v2) _ =>
      collect_exp_geps_acc v2 (collect_exp_geps_acc v1 acc)
  | OP_InsertElement (_, v1) (_, v2) (_, v3)
  | OP_ShuffleVector (_, v1) (_, v2) (_, v3)
  | OP_Select _ (_, v1) (_, v2) (_, v3) =>
      collect_exp_geps_acc v3 (collect_exp_geps_acc v2 (collect_exp_geps_acc v1 acc))
  end.

Fixpoint collect_tvalue_args_geps_acc {A : Set}
  (args : list ((dtyp * exp dtyp) * A)) (acc : list gep_site) {struct args} : list gep_site :=
  match args with
  | [] => acc
  | ((_, ae), _) :: rest => collect_tvalue_args_geps_acc rest (collect_exp_geps_acc ae acc)
  end.

Definition collect_instr_geps_acc (ins : instr dtyp) (acc : list gep_site) : list gep_site :=
  match ins with
  | INSTR_Op e => collect_exp_geps_acc e acc
  | INSTR_Call (_, fn_e) args _ _ =>
      collect_tvalue_args_geps_acc args (collect_exp_geps_acc fn_e acc)
  | INSTR_Load _ (_, pe) _ => collect_exp_geps_acc pe acc
  | INSTR_Store (_, ve) (_, pe) _ =>
      collect_exp_geps_acc pe (collect_exp_geps_acc ve acc)
  | INSTR_VAArg (_, ve) _ => collect_exp_geps_acc ve acc
  | _ => acc
  end.

Definition collect_term_geps_acc (tm : terminator dtyp) (acc : list gep_site) : list gep_site :=
  match tm with
  | TERM_Ret (_, e) | TERM_Br (_, e) _ _ | TERM_Switch (_, e) _ _
  | TERM_IndirectBr (_, e) _ _ | TERM_Resume (_, e) => collect_exp_geps_acc e acc
  | TERM_Invoke (_, fn_e) args _ _ _ _ =>
      collect_tvalue_args_geps_acc args (collect_exp_geps_acc fn_e acc)
  | _ => acc
  end.

Fixpoint collect_phi_args_geps_acc (args : list (block_id * exp dtyp)) (acc : list gep_site)
  {struct args} : list gep_site :=
  match args with
  | [] => acc
  | (_, e) :: rest => collect_phi_args_geps_acc rest (collect_exp_geps_acc e acc)
  end.

Fixpoint collect_phis_geps_acc (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (acc : list gep_site) {struct phis} : list gep_site :=
  match phis with
  | [] => acc
  | (_, Phi _ _ args, _) :: rest => collect_phis_geps_acc rest (collect_phi_args_geps_acc args acc)
  end.

Fixpoint collect_code_geps_acc (c : code dtyp) (acc : list gep_site) {struct c} : list gep_site :=
  match c with
  | [] => acc
  | (_, ins, _) :: rest => collect_code_geps_acc rest (collect_instr_geps_acc ins acc)
  end.

Definition collect_block_geps_acc (b : block dtyp) (acc : list gep_site) : list gep_site :=
  let acc1 := collect_phis_geps_acc (blk_phis b) acc in
  let acc2 := collect_code_geps_acc (blk_code b) acc1 in
  let '(_, tm, _) := blk_term b in collect_term_geps_acc tm acc2.

Fixpoint collect_blocks_geps_acc (bs : list (block dtyp)) (acc : list gep_site)
  {struct bs} : list gep_site :=
  match bs with
  | [] => acc
  | b :: rest => collect_blocks_geps_acc rest (collect_block_geps_acc b acc)
  end.

Definition collect_cfg_geps (G : CFG.cfg dtyp) : list gep_site :=
  collect_blocks_geps_acc (blks G) [].

Definition gep_operands_match_b (g1 g2 : gep_site) : bool :=
  dtyp_eqb (gs_base_ty g1) (gs_base_ty g2) &&
  dtyp_eqb (fst (gs_ptr g1)) (fst (gs_ptr g2)) &&
  simple_exp_dtyp_eqb (snd (gs_ptr g1)) (snd (gs_ptr g2)) &&
  forallb2 (fun '(t1, e1) '(t2, e2) => dtyp_eqb t1 t2 && simple_exp_dtyp_eqb e1 e2)
           (gs_idxs g1) (gs_idxs g2).

Definition gep_site_justified_by (src_geps : list gep_site) (tg : gep_site) : bool :=
  gep_flags_is_none (gs_flags tg) ||
  existsb (fun sg => gep_operands_match_b tg sg && gep_flags_le (gs_flags tg) (gs_flags sg))
          src_geps.

Definition cfg_no_invented_gep_flags (src_cfg tgt_cfg : CFG.cfg dtyp) : bool :=
  let src_geps := collect_cfg_geps src_cfg in
  forallb (gep_site_justified_by src_geps) (collect_cfg_geps tgt_cfg).

(** *** 6.6 [F-30], [F-31], [F-34]: Intrinsic Allowlist, Non-Variadic IR, and No Unwind/Exceptions *)

Definition is_forbidden_intrinsic_name (s : string) : bool :=
  function_name_eq (Name s) (dc_name va_start_decl) ||
  function_name_eq (Name s) (dc_name va_end_decl) ||
  function_name_eq (Name s) (dc_name va_copy_decl) ||
  function_name_eq (Name s) (dc_name vellvm_internal_throw_decl) ||
  String.prefix "llvm.va_" s.

Definition is_allowed_intrinsic_name (s : string) : bool :=
  negb (is_forbidden_intrinsic_name s) &&
  declares defined_intrinsics_decls s.

Definition call_callee_allowlisted {T : Set} (fn_e : exp T) : bool :=
  match fn_e with
  | EXP_Ident (ID_Global (Name s)) =>
      if String.prefix "llvm." s then is_allowed_intrinsic_name s else true
  | _ => true
  end.

Definition instr_intrinsics_allowlisted {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_Call (_, fn_e) _ _ obs =>
      list_empty_b obs && call_callee_allowlisted fn_e
  | _ => true
  end.

Definition cfg_intrinsics_allowlisted {T : Set} (G : CFG.cfg T) : bool :=
  forallb (fun b => forallb (fun '(_, ins, _) => instr_intrinsics_allowlisted ins) (blk_code b))
          (blks G).

Definition instr_no_vaarg {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_VAArg _ _ => false
  | _ => true
  end.

Definition cfg_no_vaarg {T : Set} (G : CFG.cfg T) : bool :=
  forallb (fun b => forallb (fun '(_, ins, _) => instr_no_vaarg ins) (blk_code b)) (blks G).

Definition ann_no_personality {T : Set} (a : annotation T) : bool :=
  match a with
  | ANN_personality _ => false
  | _ => true
  end.

Definition instr_no_exceptions {T : Set} (ins : instr T) : bool :=
  match ins with
  | INSTR_LandingPad _ _ _ => false
  | INSTR_Call _ _ anns _ | INSTR_Alloca _ anns
  | INSTR_Load _ _ anns | INSTR_Store _ _ anns => forallb ann_no_personality anns
  | _ => true
  end.

Definition term_no_exceptions {T : Set} (tm : terminator T) : bool :=
  match tm with
  | TERM_Invoke _ _ _ _ _ _ | TERM_Resume _ => false
  | _ => true
  end.

Definition block_no_exceptions {T : Set} (b : block T) : bool :=
  forallb (fun '(_, ins, _) => instr_no_exceptions ins) (blk_code b) &&
  let '(_, tm, _) := blk_term b in term_no_exceptions tm.

Definition cfg_no_exceptions {T : Set} (G : CFG.cfg T) : bool :=
  forallb block_no_exceptions (blks G).

(** *** 6.6b [F-39]: Reject Target-Invented FP-to-Integer [CONV_Bitcast] *)

Fixpoint dtyp_contains_fp (dt : dtyp) {struct dt} : bool :=
  let fix any_fp (xs : list dtyp) {struct xs} : bool :=
      match xs with
      | [] => false
      | x :: r => dtyp_contains_fp x || any_fp r
      end in
  match dt with
  | DTYPE_Base (DTYPE_FP _) => true
  | DTYPE_Base _ => false
  | DTYPE_Struct _ fs => any_fp fs
  | DTYPE_Array _ _ u => dtyp_contains_fp u
  end.

Fixpoint dtyp_contains_int (dt : dtyp) {struct dt} : bool :=
  let fix any_int (xs : list dtyp) {struct xs} : bool :=
      match xs with
      | [] => false
      | x :: r => dtyp_contains_int x || any_int r
      end in
  match dt with
  | DTYPE_Base (DTYPE_I _)
  | DTYPE_Base DTYPE_Iptr
  | DTYPE_Base (DTYPE_B _) => true
  | DTYPE_Base _ => false
  | DTYPE_Struct _ fs => any_int fs
  | DTYPE_Array _ _ u => dtyp_contains_int u
  end.

Record bitcast_site : Set :=
  mk_bitcast_site {
    bcs_from : dtyp;
    bcs_val : exp dtyp;
    bcs_to : dtyp;
  }.

Fixpoint collect_exp_bitcasts_acc (e : exp dtyp) (acc : list bitcast_site) {struct e} : list bitcast_site :=
  let fix collect_texps (xs : list (dtyp * exp dtyp)) (a : list bitcast_site) {struct xs} : list bitcast_site :=
      match xs with
      | [] => a
      | (_, x) :: r => collect_texps r (collect_exp_bitcasts_acc x a)
      end in
  match e with
  | EXP_Ident _ | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ | EXP_Metadata _ => acc
  | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
  | EXP_Array elts | EXP_Vector elts => collect_texps elts acc
  | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ _ v1 v2
  | OP_FBinop _ _ _ v1 v2 | OP_FCmp _ _ _ v1 v2 =>
      collect_exp_bitcasts_acc v2 (collect_exp_bitcasts_acc v1 acc)
  | OP_Conversion CONV_Bitcast tf v tt_ty =>
      collect_exp_bitcasts_acc v (mk_bitcast_site tf v tt_ty :: acc)
  | OP_Fneg _ (_, v) | OP_Conversion _ _ v _
  | OP_ExtractValue (_, v) _ | OP_Freeze (_, v) | EXP_Splat (_, v) =>
      collect_exp_bitcasts_acc v acc
  | OP_GetElementPtr _ _ (_, pv) idxs =>
      collect_texps idxs (collect_exp_bitcasts_acc pv acc)
  | OP_ExtractElement (_, v1) (_, v2) | OP_InsertValue (_, v1) (_, v2) _ =>
      collect_exp_bitcasts_acc v2 (collect_exp_bitcasts_acc v1 acc)
  | OP_InsertElement (_, v1) (_, v2) (_, v3)
  | OP_ShuffleVector (_, v1) (_, v2) (_, v3)
  | OP_Select _ (_, v1) (_, v2) (_, v3) =>
      collect_exp_bitcasts_acc v3 (collect_exp_bitcasts_acc v2 (collect_exp_bitcasts_acc v1 acc))
  end.

Fixpoint collect_tvalue_args_bitcasts_acc {A : Set}
  (args : list ((dtyp * exp dtyp) * A)) (acc : list bitcast_site) {struct args} : list bitcast_site :=
  match args with
  | [] => acc
  | ((_, ae), _) :: rest => collect_tvalue_args_bitcasts_acc rest (collect_exp_bitcasts_acc ae acc)
  end.

Definition collect_instr_bitcasts_acc (ins : instr dtyp) (acc : list bitcast_site) : list bitcast_site :=
  match ins with
  | INSTR_Op e => collect_exp_bitcasts_acc e acc
  | INSTR_Call (_, fn_e) args _ _ =>
      collect_tvalue_args_bitcasts_acc args (collect_exp_bitcasts_acc fn_e acc)
  | INSTR_Load _ (_, pe) _ => collect_exp_bitcasts_acc pe acc
  | INSTR_Store (_, ve) (_, pe) _ =>
      collect_exp_bitcasts_acc pe (collect_exp_bitcasts_acc ve acc)
  | INSTR_VAArg (_, ve) _ => collect_exp_bitcasts_acc ve acc
  | _ => acc
  end.

Definition collect_term_bitcasts_acc (tm : terminator dtyp) (acc : list bitcast_site) : list bitcast_site :=
  match tm with
  | TERM_Ret (_, e) | TERM_Br (_, e) _ _ | TERM_Switch (_, e) _ _
  | TERM_IndirectBr (_, e) _ _ | TERM_Resume (_, e) => collect_exp_bitcasts_acc e acc
  | TERM_Invoke (_, fn_e) args _ _ _ _ =>
      collect_tvalue_args_bitcasts_acc args (collect_exp_bitcasts_acc fn_e acc)
  | _ => acc
  end.

Fixpoint collect_phi_args_bitcasts_acc (args : list (block_id * exp dtyp)) (acc : list bitcast_site)
  {struct args} : list bitcast_site :=
  match args with
  | [] => acc
  | (_, e) :: rest => collect_phi_args_bitcasts_acc rest (collect_exp_bitcasts_acc e acc)
  end.

Fixpoint collect_phis_bitcasts_acc (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  (acc : list bitcast_site) {struct phis} : list bitcast_site :=
  match phis with
  | [] => acc
  | (_, Phi _ _ args, _) :: rest => collect_phis_bitcasts_acc rest (collect_phi_args_bitcasts_acc args acc)
  end.

Fixpoint collect_code_bitcasts_acc (c : code dtyp) (acc : list bitcast_site) {struct c} : list bitcast_site :=
  match c with
  | [] => acc
  | (_, ins, _) :: rest => collect_code_bitcasts_acc rest (collect_instr_bitcasts_acc ins acc)
  end.

Definition collect_block_bitcasts_acc (b : block dtyp) (acc : list bitcast_site) : list bitcast_site :=
  let acc1 := collect_phis_bitcasts_acc (blk_phis b) acc in
  let acc2 := collect_code_bitcasts_acc (blk_code b) acc1 in
  let '(_, tm, _) := blk_term b in collect_term_bitcasts_acc tm acc2.

Fixpoint collect_blocks_bitcasts_acc (bs : list (block dtyp)) (acc : list bitcast_site)
  {struct bs} : list bitcast_site :=
  match bs with
  | [] => acc
  | b :: rest => collect_blocks_bitcasts_acc rest (collect_block_bitcasts_acc b acc)
  end.

Definition collect_cfg_bitcasts (G : CFG.cfg dtyp) : list bitcast_site :=
  collect_blocks_bitcasts_acc (blks G) [].

Definition bitcast_site_eqb (b1 b2 : bitcast_site) : bool :=
  dtyp_eqb (bcs_from b1) (bcs_from b2) &&
  dtyp_eqb (bcs_to b1) (bcs_to b2) &&
  simple_exp_dtyp_eqb (bcs_val b1) (bcs_val b2).

Definition is_fp_to_int_bitcast (b : bitcast_site) : bool :=
  dtyp_contains_fp (bcs_from b) && dtyp_contains_int (bcs_to b).

Definition bitcast_site_justified_by (src_bcs : list bitcast_site) (tb : bitcast_site) : bool :=
  negb (is_fp_to_int_bitcast tb) ||
  existsb (bitcast_site_eqb tb) src_bcs.

Definition cfg_no_invented_fp_int_bitcast (src_cfg tgt_cfg : CFG.cfg dtyp) : bool :=
  let src_bcs := collect_cfg_bitcasts src_cfg in
  forallb (bitcast_site_justified_by src_bcs) (collect_cfg_bitcasts tgt_cfg).

(** *** 6.7 Combined Syntax Gate & [Qed.] Inversion Lemmas *)

Definition check_validator_syntax_gates (src_cfg tgt_cfg : CFG.cfg dtyp) : bool :=
  cfg_no_fast_math tgt_cfg &&
  cfg_no_concurrency src_cfg &&
  cfg_no_concurrency tgt_cfg &&
  cfg_supported_abi src_cfg &&
  cfg_supported_abi tgt_cfg &&
  cfg_no_invented_gep_flags src_cfg tgt_cfg &&
  cfg_intrinsics_allowlisted src_cfg &&
  cfg_intrinsics_allowlisted tgt_cfg &&
  cfg_no_vaarg src_cfg &&
  cfg_no_vaarg tgt_cfg &&
  cfg_no_exceptions src_cfg &&
  cfg_no_exceptions tgt_cfg &&
  cfg_no_invented_fp_int_bitcast src_cfg tgt_cfg.

Theorem check_validator_syntax_gates_inv :
  forall src_cfg tgt_cfg,
    check_validator_syntax_gates src_cfg tgt_cfg = true ->
    cfg_no_fast_math tgt_cfg = true /\
    cfg_no_concurrency src_cfg = true /\
    cfg_no_concurrency tgt_cfg = true /\
    cfg_supported_abi src_cfg = true /\
    cfg_supported_abi tgt_cfg = true /\
    cfg_no_invented_gep_flags src_cfg tgt_cfg = true /\
    cfg_intrinsics_allowlisted src_cfg = true /\
    cfg_intrinsics_allowlisted tgt_cfg = true /\
    cfg_no_vaarg src_cfg = true /\
    cfg_no_vaarg tgt_cfg = true /\
    cfg_no_exceptions src_cfg = true /\
    cfg_no_exceptions tgt_cfg = true /\
    cfg_no_invented_fp_int_bitcast src_cfg tgt_cfg = true.
Proof.
  intros src_cfg tgt_cfg H; unfold check_validator_syntax_gates in H.
  rewrite !andb_true_iff in H.
  destruct H as ((((((((((((H1 & H2) & H3) & H4) & H5) & H6) & H7) & H8) & H9) & H10) & H11) & H12) & H13).
  repeat split; assumption.
Qed.

Fixpoint cf_find_bad_instr_idx {T : Set}
  (p : instr T -> bool) (idx : nat) (c : code T) {struct c} : option nat :=
  match c with
  | [] => None
  | (_, ins, _) :: rest =>
      if p ins then cf_find_bad_instr_idx p (S idx) rest else Some idx
  end.

Fixpoint cf_find_bad_block_loc {T : Set}
  (bp : block T -> bool) (ip : option (instr T -> bool)) (bs : list (block T))
  {struct bs} : string :=
  match bs with
  | [] => ""
  | b :: rest =>
      if bp b then cf_find_bad_block_loc bp ip rest
      else
        let blk_part := (" in block '" ++ cf_raw_id_str (blk_id b) ++ "'")%string in
        match ip with
        | None => blk_part
        | Some p =>
            match cf_find_bad_instr_idx p 0 (blk_code b) with
            | Some i => (blk_part ++ " instr #" ++ diag_nat_dec i)%string
            | None => blk_part
            end
        end
  end.

Definition check_validator_syntax_gates_diag (src_cfg tgt_cfg : CFG.cfg dtyp) : string + unit :=
  bind_err
    (guard_err (cfg_no_fast_math tgt_cfg)
      (fun _ => diag "ir-syntax-F17"
        ("fast-math flags not allowed in target IR" ++
         cf_find_bad_block_loc block_no_fast_math (Some instr_no_fast_math) (blks tgt_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_concurrency src_cfg)
      (fun _ => diag "ir-syntax-F18"
        ("volatile/atomic/fence/inline-asm not allowed in source IR" ++
         cf_find_bad_block_loc block_no_concurrency (Some instr_no_concurrency) (blks src_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_concurrency tgt_cfg)
      (fun _ => diag "ir-syntax-F18"
        ("volatile/atomic/fence/inline-asm not allowed in target IR" ++
         cf_find_bad_block_loc block_no_concurrency (Some instr_no_concurrency) (blks tgt_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_supported_abi src_cfg)
      (fun _ => diag "ir-syntax-F19"
        ("unsupported ABI/call annotation in source IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_supported_abi ins) (blk_code b))
           (Some instr_supported_abi) (blks src_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_supported_abi tgt_cfg)
      (fun _ => diag "ir-syntax-F19"
        ("unsupported ABI/call annotation in target IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_supported_abi ins) (blk_code b))
           (Some instr_supported_abi) (blks tgt_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_invented_gep_flags src_cfg tgt_cfg)
      (fun _ => diag "ir-syntax-F21" "target-invented GEP inbounds/nusw/nuw flag"))
    (fun _ =>
  bind_err
    (guard_err (cfg_intrinsics_allowlisted src_cfg)
      (fun _ => diag "ir-syntax-F30"
        ("disallowed or variadic intrinsic call in source IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_intrinsics_allowlisted ins) (blk_code b))
           (Some instr_intrinsics_allowlisted) (blks src_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_intrinsics_allowlisted tgt_cfg)
      (fun _ => diag "ir-syntax-F30"
        ("disallowed or variadic intrinsic call in target IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_intrinsics_allowlisted ins) (blk_code b))
           (Some instr_intrinsics_allowlisted) (blks tgt_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_vaarg src_cfg)
      (fun _ => diag "ir-syntax-F31"
        ("va_arg instruction not supported in source IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_no_vaarg ins) (blk_code b))
           (Some instr_no_vaarg) (blks src_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_vaarg tgt_cfg)
      (fun _ => diag "ir-syntax-F31"
        ("va_arg instruction not supported in target IR" ++
         cf_find_bad_block_loc (fun b => forallb (fun '(_, ins, _) => instr_no_vaarg ins) (blk_code b))
           (Some instr_no_vaarg) (blks tgt_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_exceptions src_cfg)
      (fun _ => diag "ir-syntax-F34"
        ("exception/unwind/personality construct not allowed in source IR" ++
         cf_find_bad_block_loc block_no_exceptions (Some instr_no_exceptions) (blks src_cfg))))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_exceptions tgt_cfg)
      (fun _ => diag "ir-syntax-F34"
        ("exception/unwind/personality construct not allowed in target IR" ++
         cf_find_bad_block_loc block_no_exceptions (Some instr_no_exceptions) (blks tgt_cfg))))
    (fun _ =>
  guard_err (cfg_no_invented_fp_int_bitcast src_cfg tgt_cfg)
    (fun _ => diag "ir-syntax-F39" "target-invented FP-to-integer bitcast"))))))))))))).

Lemma check_validator_syntax_gates_diag_sound :
  forall src_cfg tgt_cfg,
    check_validator_syntax_gates_diag src_cfg tgt_cfg = inr tt ->
    check_validator_syntax_gates src_cfg tgt_cfg = true.
Proof.
  intros src_cfg tgt_cfg H.
  unfold check_validator_syntax_gates_diag in H; unfold check_validator_syntax_gates.
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | guard_err ?c _ = inr tt =>
      destruct c; cbn [guard_err] in H; [| discriminate H]
  end.
  reflexivity.
Qed.

Lemma cfg_no_fast_math_block_inv {T : Set} :
  forall (G : CFG.cfg T) b,
    cfg_no_fast_math G = true -> In b (blks G) -> block_no_fast_math b = true.
Proof.
  intros G b H Hin; unfold cfg_no_fast_math in H.
  rewrite forallb_forall in H; exact (H b Hin).
Qed.

Lemma cfg_no_concurrency_block_inv {T : Set} :
  forall (G : CFG.cfg T) b,
    cfg_no_concurrency G = true -> In b (blks G) -> block_no_concurrency b = true.
Proof.
  intros G b H Hin; unfold cfg_no_concurrency in H.
  rewrite forallb_forall in H; exact (H b Hin).
Qed.

Lemma cfg_no_vaarg_instr_inv {T : Set} :
  forall (G : CFG.cfg T) b iid ins mds,
    cfg_no_vaarg G = true ->
    In b (blks G) ->
    In (iid, ins, mds) (blk_code b) ->
    instr_no_vaarg ins = true.
Proof.
  intros G b iid ins mds H Hb Hins; unfold cfg_no_vaarg in H.
  rewrite forallb_forall in H; specialize (H b Hb).
  rewrite forallb_forall in H; specialize (H (iid, ins, mds) Hins).
  exact H.
Qed.

Lemma cfg_no_exceptions_block_inv {T : Set} :
  forall (G : CFG.cfg T) b,
    cfg_no_exceptions G = true ->
    In b (blks G) ->
    (forall iid ins mds, In (iid, ins, mds) (blk_code b) -> instr_no_exceptions ins = true) /\
    term_no_exceptions (let '(_, tm, _) := blk_term b in tm) = true.
Proof.
  intros G b H Hb; unfold cfg_no_exceptions in H.
  rewrite forallb_forall in H; specialize (H b Hb); unfold block_no_exceptions in H.
  apply andb_true_iff in H as [Hc Ht]; split; [| destruct (blk_term b) as [[? ?] ?]; exact Ht].
  intros iid ins mds Hins; rewrite forallb_forall in Hc.
  exact (Hc (iid, ins, mds) Hins).
Qed.

Lemma cfg_no_invented_gep_flags_inv :
  forall src_cfg tgt_cfg tg,
    cfg_no_invented_gep_flags src_cfg tgt_cfg = true ->
    In tg (collect_cfg_geps tgt_cfg) ->
    gep_flags_is_none (gs_flags tg) = true \/
    exists sg,
      In sg (collect_cfg_geps src_cfg) /\
      gep_operands_match_b tg sg = true /\
      gep_flags_le (gs_flags tg) (gs_flags sg) = true.
Proof.
  intros src_cfg tgt_cfg tg H Hin; unfold cfg_no_invented_gep_flags in H.
  rewrite forallb_forall in H; specialize (H tg Hin); unfold gep_site_justified_by in H.
  apply orb_true_iff in H as [Hnone | Hex]; [left; exact Hnone | right].
  apply existsb_exists in Hex as [sg [Hsg Hm]].
  apply andb_true_iff in Hm as [Hop Hle].
  exists sg; repeat split; assumption.
Qed.

Lemma cfg_no_invented_fp_int_bitcast_inv :
  forall src_cfg tgt_cfg tb,
    cfg_no_invented_fp_int_bitcast src_cfg tgt_cfg = true ->
    In tb (collect_cfg_bitcasts tgt_cfg) ->
    is_fp_to_int_bitcast tb = false \/
    exists sb,
      In sb (collect_cfg_bitcasts src_cfg) /\
      bitcast_site_eqb tb sb = true.
Proof.
  intros src_cfg tgt_cfg tb H Hin; unfold cfg_no_invented_fp_int_bitcast in H.
  rewrite forallb_forall in H; specialize (H tb Hin); unfold bitcast_site_justified_by in H.
  apply orb_true_iff in H as [Hnot | Hex].
  - left; apply negb_true_iff in Hnot; exact Hnot.
  - right; apply existsb_exists in Hex as [sb [Hsb Heq]].
    exists sb; split; assumption.
Qed.

Lemma forallb2_typ_eqb_eq : forall xs ys,
  forallb2 typ_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x rx IH]; intros [| y ry] H; cbn in H; try discriminate; [reflexivity |].
  apply andb_true_iff in H as [Hxy Hr].
  apply typ_eqb_eq in Hxy; subst y; f_equal; exact (IH ry Hr).
Qed.

Theorem check_prototype_contract_inv :
  forall src_decl tgt_decl,
    check_prototype_contract src_decl tgt_decl = true ->
    dc_name src_decl = dc_name tgt_decl /\
    exists ret_ty arg_tys,
      dc_type src_decl = TYPE_Function ret_ty arg_tys false /\
      dc_type tgt_decl = TYPE_Function ret_ty arg_tys false /\
      List.length (snd (dc_param_attrs src_decl)) = List.length arg_tys /\
      List.length (snd (dc_param_attrs tgt_decl)) = List.length arg_tys /\
      cconv_eqb (anns_cconv (dc_annotations src_decl))
                (anns_cconv (dc_annotations tgt_decl)) = true /\
      ret_attrs_refine_b (fst (dc_param_attrs src_decl))
                         (fst (dc_param_attrs tgt_decl)) = true /\
      param_attrs_refine_b (fst (dc_param_attrs src_decl))
                           (fst (dc_param_attrs tgt_decl)) = true /\
      forallb2 param_attrs_refine_b (snd (dc_param_attrs src_decl))
                                    (snd (dc_param_attrs tgt_decl)) = true /\
      check_fn_attrs_contract (dc_attrs src_decl) (dc_attrs tgt_decl) = true.
Proof.
  intros src_decl tgt_decl H; unfold check_prototype_contract in H.
  apply andb_true_iff in H as [Hnm Hbody].
  apply raw_id_eqb_eq in Hnm.
  destruct (dc_type src_decl) as [| | | | | | | | | | | sret sargs svar | | | | |];
    try discriminate.
  destruct svar; [discriminate |].
  destruct (dc_type tgt_decl) as [| | | | | | | | | | | tret targs tvar | | | | |];
    try discriminate.
  destruct tvar; [discriminate |].
  destruct (dc_param_attrs src_decl) as [sr sp] eqn:Hspa.
  destruct (dc_param_attrs tgt_decl) as [tr tp] eqn:Htpa.
  rewrite !andb_true_iff in Hbody.
  destruct Hbody as
    ((((((((((Hret & Hargs) & Hlens) & Hlent) & Hcc) & Hra) & Hpa) & Hfattrs) & _) & _) & _).
  apply typ_eqb_eq in Hret; apply forallb2_typ_eqb_eq in Hargs; subst tret targs.
  apply Nat.eqb_eq in Hlens; apply Nat.eqb_eq in Hlent.
  pose proof Hra as Hra_copy; unfold ret_attrs_refine_b in Hra_copy.
  apply andb_true_iff in Hra_copy as [Hra_param _].
  split; [exact Hnm |].
  exists sret, sargs; cbn [fst snd]; repeat split; assumption.
Qed.

(** *** 6.8 Fail-Closed Check for Undefined [TYPE_Identified] References *)

Definition ident_defined_in_env (env : list (ident * typ)) (id : ident) : bool :=
  existsb (fun '(id', _) => ident_eqb id id') env.

Fixpoint typ_identified_defined (env : list (ident * typ)) (t : typ) {struct t} : bool :=
  let fix list_typ_def (xs : list typ) {struct xs} : bool :=
      match xs with
      | [] => true
      | x :: rx => typ_identified_defined env x && list_typ_def rx
      end in
  match t with
  | TYPE_I _ | TYPE_B _ | TYPE_Iptr | TYPE_Pointer None
  | TYPE_Void | TYPE_FP _ | TYPE_Label | TYPE_Token
  | TYPE_Metadata | TYPE_X86_mmx | TYPE_Opaque => true
  | TYPE_Pointer (Some u) | TYPE_Array _ u | TYPE_Vector _ u =>
      typ_identified_defined env u
  | TYPE_Function ret args _ =>
      typ_identified_defined env ret && list_typ_def args
  | TYPE_Struct fs | TYPE_Packed_struct fs => list_typ_def fs
  | TYPE_Identified id => ident_defined_in_env env id
  end.

Lemma typ_identified_defined_id_inv :
  forall env id,
    typ_identified_defined env (TYPE_Identified id) = true ->
    exists body, In (id, body) env.
Proof.
  intros env id H; cbn in H; unfold ident_defined_in_env in H.
  apply existsb_exists in H as [[id' body] [Hin Heq]].
  apply ident_eqb_eq in Heq; subst id'.
  exists body; exact Hin.
Qed.

Fixpoint exp_identified_defined (env : list (ident * typ)) (e : exp typ) {struct e} : bool :=
  let fix list_texp_def (xs : list (typ * exp typ)) {struct xs} : bool :=
      match xs with
      | [] => true
      | (t, u) :: rx =>
          typ_identified_defined env t && exp_identified_defined env u && list_texp_def rx
      end in
  match e with
  | EXP_Ident _ | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ => true
  | EXP_Cstring xs | EXP_Struct xs | EXP_Packed_struct xs
  | EXP_Array xs | EXP_Vector xs => list_texp_def xs
  | OP_IBinop _ t v1 v2 | OP_ICmp _ _ t v1 v2
  | OP_FBinop _ _ t v1 v2 | OP_FCmp _ _ t v1 v2 =>
      typ_identified_defined env t &&
      exp_identified_defined env v1 && exp_identified_defined env v2
  | OP_Fneg _ (t, v1) | OP_Freeze (t, v1) | EXP_Splat (t, v1)
  | OP_ExtractValue (t, v1) _ =>
      typ_identified_defined env t && exp_identified_defined env v1
  | OP_Conversion _ tf v1 tto =>
      typ_identified_defined env tf && exp_identified_defined env v1 &&
      typ_identified_defined env tto
  | OP_GetElementPtr _ t (tp, ep) idxs =>
      typ_identified_defined env t && typ_identified_defined env tp &&
      exp_identified_defined env ep && list_texp_def idxs
  | OP_ExtractElement (t1, v1) (t2, v2) | OP_InsertValue (t1, v1) (t2, v2) _ =>
      typ_identified_defined env t1 && exp_identified_defined env v1 &&
      typ_identified_defined env t2 && exp_identified_defined env v2
  | OP_InsertElement (t1, v1) (t2, v2) (t3, v3)
  | OP_ShuffleVector (t1, v1) (t2, v2) (t3, v3)
  | OP_Select _ (t1, v1) (t2, v2) (t3, v3) =>
      typ_identified_defined env t1 && exp_identified_defined env v1 &&
      typ_identified_defined env t2 && exp_identified_defined env v2 &&
      typ_identified_defined env t3 && exp_identified_defined env v3
  | EXP_Metadata m => metadata_identified_defined env m
  end
with metadata_identified_defined (env : list (ident * typ)) (m : metadata typ) {struct m} : bool :=
  let fix list_md_def (ms : list (metadata typ)) {struct ms} : bool :=
      match ms with
      | [] => true
      | m1 :: rm => metadata_identified_defined env m1 && list_md_def rm
      end in
  match m with
  | METADATA_Null | METADATA_Id _ | METADATA_Debug _ _ | METADATA_File_info _ => true
  | METADATA_Const (t, u) => typ_identified_defined env t && exp_identified_defined env u
  | METADATA_Node ms => list_md_def ms
  | METADATA_Pair m1 m2 =>
      metadata_identified_defined env m1 && metadata_identified_defined env m2
  end.

Definition texp_identified_defined (env : list (ident * typ)) (te : texp typ) : bool :=
  let '(t, e) := te in typ_identified_defined env t && exp_identified_defined env e.

Definition param_attr_identified_defined (env : list (ident * typ)) (pa : param_attr) : bool :=
  match pa with
  | PARAMATTR_Byval t | PARAMATTR_Byref t | PARAMATTR_Preallocated t
  | PARAMATTR_Inalloca t | PARAMATTR_Sret t | PARAMATTR_Elementtype t
  | PARAMATTR_Range t _ _ => typ_identified_defined env t
  | _ => true
  end.

Definition ann_identified_defined (env : list (ident * typ)) (a : annotation typ) : bool :=
  match a with
  | ANN_metadata ms => forallb (metadata_identified_defined env) ms
  | ANN_prefix te | ANN_prologue te | ANN_personality te | ANN_num_elements te =>
      texp_identified_defined env te
  | ANN_ret_attribute pa => param_attr_identified_defined env pa
  | _ => true
  end.

Definition operand_bundle_identified_defined (env : list (ident * typ)) (ob : @operand_bundle typ) : bool :=
  forallb (fun op =>
    match op with
    | SSA_value te => texp_identified_defined env te
    | Metadata_string md => metadata_identified_defined env md
    end) (ob_ops ob).

Definition instr_identified_defined (env : list (ident * typ)) (ins : instr typ) : bool :=
  match ins with
  | INSTR_Comment _ | INSTR_Fence _ _ => true
  | INSTR_Op e => exp_identified_defined env e
  | INSTR_Call fn args anns obs =>
      texp_identified_defined env fn &&
      forallb (fun '(te, pas) =>
        texp_identified_defined env te && forallb (param_attr_identified_defined env) pas) args &&
      forallb (ann_identified_defined env) anns &&
      forallb (operand_bundle_identified_defined env) obs
  | INSTR_Alloca t anns =>
      typ_identified_defined env t && forallb (ann_identified_defined env) anns
  | INSTR_Load t ptr anns =>
      typ_identified_defined env t && texp_identified_defined env ptr &&
      forallb (ann_identified_defined env) anns
  | INSTR_Store val ptr anns =>
      texp_identified_defined env val && texp_identified_defined env ptr &&
      forallb (ann_identified_defined env) anns
  | INSTR_AtomicCmpXchg c =>
      texp_identified_defined env (c_ptr c) &&
      texp_identified_defined env (c_cmp c) &&
      texp_identified_defined env (c_new c)
  | INSTR_AtomicRMW a =>
      texp_identified_defined env (a_ptr a) &&
      texp_identified_defined env (a_val a)
  | INSTR_VAArg va t =>
      texp_identified_defined env va && typ_identified_defined env t
  | INSTR_LandingPad rty _ cs =>
      typ_identified_defined env rty &&
      forallb (fun cl => match cl with CATCH te | FILTER te => texp_identified_defined env te end) cs
  end.

Definition term_identified_defined (env : list (ident * typ)) (tm : terminator typ) : bool :=
  match tm with
  | TERM_Ret_void | TERM_Br_1 _ | TERM_Unreachable => true
  | TERM_Ret te | TERM_Br te _ _ | TERM_Switch te _ _
  | TERM_IndirectBr te _ _ | TERM_Resume te => texp_identified_defined env te
  | TERM_Invoke fn args _ _ anns obs =>
      texp_identified_defined env fn &&
      forallb (fun '(te, pas) =>
        texp_identified_defined env te && forallb (param_attr_identified_defined env) pas) args &&
      forallb (ann_identified_defined env) anns &&
      forallb (operand_bundle_identified_defined env) obs
  end.

Definition block_identified_defined (env : list (ident * typ)) (b : block typ) : bool :=
  forallb (fun '(_, Phi _ t args, mds) =>
    typ_identified_defined env t &&
    forallb (fun '(_, e) => exp_identified_defined env e) args &&
    forallb (metadata_identified_defined env) mds) (blk_phis b) &&
  forallb (fun '(_, ins, mds) =>
    instr_identified_defined env ins && forallb (metadata_identified_defined env) mds) (blk_code b) &&
  let '(_, tm, mds) := blk_term b in
  term_identified_defined env tm && forallb (metadata_identified_defined env) mds.

Definition cfg_identified_defined (env : list (ident * typ)) (G : CFG.cfg typ) : bool :=
  forallb (block_identified_defined env) (blks G).

Definition decl_identified_defined (env : list (ident * typ)) (dc : declaration typ) : bool :=
  typ_identified_defined env (dc_type dc) &&
  forallb (param_attr_identified_defined env) (fst (dc_param_attrs dc)) &&
  forallb (forallb (param_attr_identified_defined env)) (snd (dc_param_attrs dc)) &&
  forallb (ann_identified_defined env) (dc_annotations dc).

Definition global_identified_defined (env : list (ident * typ)) (g : global typ) : bool :=
  typ_identified_defined env (g_typ g) &&
  match g_exp g with Some e => exp_identified_defined env e | None => true end &&
  forallb (ann_identified_defined env) (g_annotations g).

Definition defn_identified_defined
  (env : list (ident * typ)) (df : definition typ (CFG.cfg typ)) : bool :=
  decl_identified_defined env (df_prototype df) &&
  cfg_identified_defined env (df_instrs df).

Definition mcfg_identified_typs_defined (M : CFG.mcfg typ) : bool :=
  let env := m_type_defs M in
  forallb (fun '(_, t) => typ_identified_defined env t) env &&
  forallb (global_identified_defined env) (m_globals M) &&
  forallb (decl_identified_defined env) (m_declarations M) &&
  forallb (defn_identified_defined env) (m_definitions M).

Definition cf_ident_str (id : ident) : string :=
  match id with
  | ID_Global r => "@" ++ cf_raw_id_str r
  | ID_Local r => "%" ++ cf_raw_id_str r
  end.

Definition check_mcfg_identified_typs_defined_diag (side : string) (M : CFG.mcfg typ) : string + unit :=
  let env := m_type_defs M in
  bind_err
    (cf_check_idx_diag_acc
      (fun _ p =>
        guard_err (typ_identified_defined env (snd p))
          (fun _ => diag "ir-type"
            ("undefined identified type referenced by " ++ side ++ " type def '" ++ cf_ident_str (fst p) ++ "'")))
      0 env)
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc
      (fun _ g =>
        guard_err (global_identified_defined env g)
          (fun _ => diag "ir-type"
            ("undefined identified type referenced by " ++ side ++ " global '" ++ cf_raw_id_str (g_ident g) ++ "'")))
      0 (m_globals M))
    (fun _ =>
  bind_err
    (cf_check_idx_diag_acc
      (fun _ dc =>
        guard_err (decl_identified_defined env dc)
          (fun _ => diag "ir-type"
            ("undefined identified type referenced by " ++ side ++ " declaration '" ++ cf_raw_id_str (dc_name dc) ++ "'")))
      0 (m_declarations M))
    (fun _ =>
  cf_check_idx_diag_acc
    (fun _ df =>
      guard_err (defn_identified_defined env df)
        (fun _ => diag "ir-type"
          ("undefined identified type referenced in " ++ side ++ " definition '" ++
           cf_raw_id_str (dc_name (df_prototype df)) ++ "'")))
    0 (m_definitions M)))).

Lemma check_mcfg_identified_typs_defined_diag_sound :
  forall side M,
    check_mcfg_identified_typs_defined_diag side M = inr tt ->
    mcfg_identified_typs_defined M = true.
Proof.
  intros side M H; unfold check_mcfg_identified_typs_defined_diag in H; unfold mcfg_identified_typs_defined.
  destruct (cf_check_idx_diag_acc
              (fun _ p =>
                guard_err (typ_identified_defined (m_type_defs M) (snd p))
                  (fun _ => diag "ir-type"
                    ("undefined identified type referenced by " ++ side ++ " type def '" ++ cf_ident_str (fst p) ++ "'")))
              0 (m_type_defs M)) as [| []] eqn:E1; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun _ g =>
                guard_err (global_identified_defined (m_type_defs M) g)
                  (fun _ => diag "ir-type"
                    ("undefined identified type referenced by " ++ side ++ " global '" ++ cf_raw_id_str (g_ident g) ++ "'")))
              0 (m_globals M)) as [| []] eqn:E2; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun _ dc =>
                guard_err (decl_identified_defined (m_type_defs M) dc)
                  (fun _ => diag "ir-type"
                    ("undefined identified type referenced by " ++ side ++ " declaration '" ++ cf_raw_id_str (dc_name dc) ++ "'")))
              0 (m_declarations M)) as [| []] eqn:E3; cbn [bind_err] in H; [discriminate H |].
  pose proof (cf_check_idx_diag_acc_sound _ (fun p => typ_identified_defined (m_type_defs M) (snd p)) _ _
                (fun _ p Ht => guard_err_inr _ _ Ht) E1) as Ht1.
  assert (Ht1' : forallb (fun '(_, t) => typ_identified_defined (m_type_defs M) t) (m_type_defs M) = true).
  { rewrite forallb_forall in Ht1 |- *; intros [tid t] Hin; exact (Ht1 (tid, t) Hin). }
  rewrite Ht1',
          (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hg => guard_err_inr _ _ Hg) E2),
          (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hdc => guard_err_inr _ _ Hdc) E3),
          (cf_check_idx_diag_acc_sound _ _ _ _ (fun _ _ Hdf => guard_err_inr _ _ Hdf) H).
  reflexivity.
Qed.

(** ** 7. Tail-Recursive DIMACS CNF & Standard ASCII LRAT Parsers ([D-01]) *)

Fixpoint split_lines_acc (cur_rev : list ascii) (acc : list string) (cs : list ascii)
  {struct cs} : list string :=
  match cs with
  | [] =>
      let last_ln := rev_chars_to_str_acc EmptyString cur_rev in
      rev_tr (last_ln :: acc)
  | c :: rest =>
      let n := nat_of_ascii c in
      if Nat.eqb n 10 then
        let ln := rev_chars_to_str_acc EmptyString cur_rev in
        split_lines_acc [] (ln :: acc) rest
      else if Nat.eqb n 13 then
        split_lines_acc cur_rev acc rest
      else
        split_lines_acc (c :: cur_rev) acc rest
  end.

Definition split_lines (s : string) : list string :=
  split_lines_acc [] [] (str_to_chars s).

Definition is_line_ws (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 32 || Nat.eqb n 9 || Nat.eqb n 11 || Nat.eqb n 12.

Fixpoint split_ws_tokens_acc (cur_opt : option (list ascii)) (acc : list string)
                             (cs : list ascii) {struct cs} : list string :=
  match cs with
  | [] =>
      match cur_opt with
      | None => rev_tr acc
      | Some rev_cs => rev_tr (rev_chars_to_str_acc EmptyString rev_cs :: acc)
      end
  | c :: rest =>
      if is_line_ws c then
        match cur_opt with
        | None => split_ws_tokens_acc None acc rest
        | Some rev_cs =>
            split_ws_tokens_acc None (rev_chars_to_str_acc EmptyString rev_cs :: acc) rest
        end
      else
        match cur_opt with
        | None => split_ws_tokens_acc (Some [c]) acc rest
        | Some rev_cs => split_ws_tokens_acc (Some (c :: rev_cs)) acc rest
        end
  end.

Definition split_ws_tokens (s : string) : list string :=
  split_ws_tokens_acc None [] (str_to_chars s).

Definition is_comment_toks (toks : list string) : bool :=
  match toks with
  | [] => true
  | t :: _ =>
      match t with
      | String c _ => Nat.eqb (nat_of_ascii c) 99
      | EmptyString => false
      end
  end.

Fixpoint find_dimacs_header (lines : list string) {struct lines}
  : string + (N * N * list string) :=
  match lines with
  | [] => inl "missing 'p cnf <vars> <clauses>' header in DIMACS CNF"
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        find_dimacs_header rest
      else
        match toks with
        | [p_tok; cnf_tok; nv_s; nc_s] =>
            if String.eqb p_tok "p" && String.eqb cnf_tok "cnf" then
              match parse_canonical_N nv_s, parse_canonical_N nc_s with
              | Some nv, Some nc => inr (nv, nc, rest)
              | _, _ => inl "invalid variable or clause count in DIMACS header"
              end
            else inl "expected 'p cnf <vars> <clauses>' header before clauses"
        | _ => inl "malformed 'p cnf <vars> <clauses>' DIMACS header"
        end
  end.

Fixpoint parse_dimacs_line_toks
  (max_var : N) (next_cid : positive) (cur_rev : list lit) (acc_rev : cnf)
  (toks : list string) {struct toks}
  : string + (positive * list lit * cnf) :=
  match toks with
  | [] => inr (next_cid, cur_rev, acc_rev)
  | tok :: rest =>
      if String.eqb tok "0" then
        parse_dimacs_line_toks max_var (Pos.succ next_cid) []
          ((next_cid, rev_tr cur_rev) :: acc_rev) rest
      else
        match parse_signed_lit_str tok with
        | Some (Zpos v) =>
            if (N.pos v <=? max_var)%N then
              parse_dimacs_line_toks max_var next_cid (Z.pos v :: cur_rev) acc_rev rest
            else inl "DIMACS literal exceeds declared num_vars bound"
        | Some (Zneg v) =>
            if (N.pos v <=? max_var)%N then
              parse_dimacs_line_toks max_var next_cid (Z.neg v :: cur_rev) acc_rev rest
            else inl "DIMACS literal exceeds declared num_vars bound"
        | _ => inl "invalid literal token in DIMACS CNF"
        end
  end.

Fixpoint parse_dimacs_lines
  (max_var expected_clauses : N)
  (next_cid : positive) (cur_rev : list lit) (acc_rev : cnf)
  (lines : list string) {struct lines} : string + cnf :=
  match lines with
  | [] =>
      match cur_rev with
      | _ :: _ => inl "unterminated clause without trailing 0 in DIMACS CNF"
      | [] =>
          if N.eqb (N.pred (N.pos next_cid)) expected_clauses then
            inr (rev_tr acc_rev)
          else inl "DIMACS clause count does not match 'p cnf' header"
      end
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        parse_dimacs_lines max_var expected_clauses next_cid cur_rev acc_rev rest
      else
        match parse_dimacs_line_toks max_var next_cid cur_rev acc_rev toks with
        | inl err => inl err
        | inr (next_cid', cur_rev', acc_rev') =>
            parse_dimacs_lines max_var expected_clauses next_cid' cur_rev' acc_rev' rest
        end
  end.

Definition parse_dimacs_cnf (input : string) : string + cnf :=
  match find_dimacs_header (split_lines input) with
  | inl err => inl err
  | inr (nv, nc, rest) => parse_dimacs_lines nv nc 1%positive [] [] rest
  end.

Fixpoint parse_lrat_lits_to_zero (acc_rev : list lit) (toks : list string) {struct toks}
  : string + (list lit * list string) :=
  match toks with
  | [] => inl "missing 0 terminator after LRAT literals"
  | tok :: rest =>
      if String.eqb tok "0" then inr (rev_tr acc_rev, rest)
      else
        match parse_signed_lit_str tok with
        | Some l => parse_lrat_lits_to_zero (l :: acc_rev) rest
        | None => inl "invalid literal in ASCII LRAT line"
        end
  end.

Fixpoint parse_lrat_pos_to_end (acc_rev : list positive) (toks : list string) {struct toks}
  : string + list positive :=
  match toks with
  | [] => inl "missing trailing 0 terminator in ASCII LRAT line"
  | [tok] =>
      if String.eqb tok "0" then inr (rev_tr acc_rev)
      else inl "expected trailing 0 terminator in ASCII LRAT line"
  | tok :: rest =>
      match parse_pos_str tok with
      | Some p => parse_lrat_pos_to_end (p :: acc_rev) rest
      | None => inl "invalid or non-positive clause hint ID in ASCII LRAT line"
      end
  end.

Definition parse_ascii_lrat_line (toks : list string) : string + lrat_step :=
  match toks with
  | [] => inl "empty LRAT line"
  | cid_s :: rest =>
      match parse_pos_str cid_s, rest with
      | Some cid, tag_s :: rest2 =>
          if String.eqb tag_s "d" then
            match parse_lrat_pos_to_end [] rest2 with
            | inr cids => inr (LRAT_Del cids)
            | inl err => inl err
            end
          else
            match parse_lrat_lits_to_zero [] rest with
            | inl err => inl err
            | inr (cl, hint_toks) =>
                match parse_lrat_pos_to_end [] hint_toks with
                | inr hints => inr (LRAT_Add cid cl hints)
                | inl err => inl err
                end
            end
      | _, _ => inl "malformed ASCII LRAT proof line"
      end
  end.

Fixpoint parse_ascii_lrat_lines (acc_rev : list lrat_step) (lines : list string)
  {struct lines} : string + list lrat_step :=
  match lines with
  | [] => inr (rev_tr acc_rev)
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        parse_ascii_lrat_lines acc_rev rest
      else
        match parse_ascii_lrat_line toks with
        | inl err => inl err
        | inr step => parse_ascii_lrat_lines (step :: acc_rev) rest
        end
  end.

Definition parse_ascii_lrat (input : string) : string + list lrat_step :=
  parse_ascii_lrat_lines [] (split_lines input).

Definition validate_dimacs_lrat_str (cnf_str lrat_str : string) : string + unit :=
  match parse_dimacs_cnf cnf_str, parse_ascii_lrat lrat_str with
  | inr f, inr pf =>
      if check_lrat_unsat f pf then inr tt
      else
        inl (diag "lrat-check"
          ("LRAT UNSAT proof (" ++ diag_nat_dec (length_tr pf) ++ " step(s)) verification failed"))
  | inl err, _ => inl (diag "dimacs-parse" err)
  | _, inl err => inl (diag "lrat-parse" err)
  end.

Theorem validate_dimacs_lrat_str_sound :
  forall cnf_str lrat_str,
    validate_dimacs_lrat_str cnf_str lrat_str = inr tt ->
    exists f pf,
      parse_dimacs_cnf cnf_str = inr f /\
      parse_ascii_lrat lrat_str = inr pf /\
      forall assign : positive -> bool, eval_cnf assign f = false.
Proof.
  intros cnf_str lrat_str H.
  unfold validate_dimacs_lrat_str in H.
  destruct (parse_dimacs_cnf cnf_str) as [| f] eqn:Ef; [discriminate H |].
  destruct (parse_ascii_lrat lrat_str) as [| pf] eqn:Ep; [discriminate H |].
  destruct (check_lrat_unsat f pf) eqn:Hchk; [| discriminate H].
  exists f, pf; split;
    [first [reflexivity | exact Ef]
    | split; [first [reflexivity | exact Ep] | exact (check_lrat_unsat_sound f pf Hchk)]].
Qed.
