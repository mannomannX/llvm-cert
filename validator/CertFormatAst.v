(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Canonical [cert-v1] Certificate AST & Well-Formedness ([CertValidator.CertFormatAst])

    Purpose:
      Defines the canonical [cert-v1] AST ([cert_binop], [cert_icmp_pred],
      [cert_cast_kind], [cert_expr] with [CE_Let], [ub_assumption],
      [proof_certificate]), boolean comparators, and closed let-DAG checks.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed well-formedness checker ([check_wf_proof_certificate_diag],
      [check_wf_proof_certificate_diag_sound]); rejects unsupported widths,
      invalid flags, unbound vars, and malformed [CE_Let] scopes with [inl].

    Assumptions:
      Depends on Stdlib, [CertValidator.common.Diag], and
      [CertValidator.LratCore]; zero Vellvm dependencies and zero custom axioms.

    Section Outline:
      1. Canonical [cert-v1] Certificate AST; 2. Structural Comparators &
      Reflection Lemmas; 3. Well-Formedness ([E-10] Closed Let-DAGs). *)

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

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  LratCore.

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

