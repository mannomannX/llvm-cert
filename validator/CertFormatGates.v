(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * IR Syntax & Prototype Contract Soundness Gates ([CertValidator.CertFormatGates])

    Purpose:
      Defines computable IR syntax and prototype contract gates
      ([check_validator_syntax_gates_diag], [check_prototype_contract_diag],
      [check_mcfg_identified_typs_defined_diag]) with [Qed.] inversion lemmas.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed syntactic gates; rejects fast-math ([F-17]), volatile/atomic/
      fences/asm ([F-18]), prototype/ABI mismatches ([F-19]/[F-32]/[F-60]), GEP
      flags ([F-21]), FP bitcasts ([F-39]), bad intrinsics, and undef types.

    Assumptions:
      Depends on Stdlib, Vellvm ([Syntax.*], [Attributes], [IntrinsicsDefinitions]),
      [CertValidator.common.Diag], and [CertValidator.{LratCore,CertFormatAst}].

    Section Outline:
      6. Syntax & Prototype Gates: 6.1 Comparators; 6.2-6.6b Flag/Intrinsic
      Checks; 6.7 Combined Gates & Inversions; 6.8 Identified-Type Check. *)

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
  LratCore
  CertFormatAst.

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

(** ** 6. Syntax & Prototype Contract Soundness Gates
       ([F-17], [F-18], [F-19], [F-21], [F-30], [F-31], [F-32], [F-34]) *)

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
    (rewrite raw_id_eqb_eq; split;
     intros H; [subst; reflexivity | inversion H; reflexivity]).
Qed.

Definition fp_variant_eqb (f1 f2 : floating_point_variant) : bool :=
  if floating_point_variant_beq f1 f2 then true else false.

Lemma fp_variant_eqb_eq : forall f1 f2, fp_variant_eqb f1 f2 = true <-> f1 = f2.
Proof.
  intros [] []; cbn; split;
    intros H; try reflexivity; discriminate.
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
  - destruct t2; cbn in H; try discriminate;
      apply Pos.eqb_eq in H; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate;
      apply Pos.eqb_eq in H; subst; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2 as [| | | [u2 |] | | | | | | | | | | | | |]; cbn in H; try discriminate.
    apply IHu1 in H; subst; reflexivity.
  - destruct t2 as [| | | [u2 |] | | | | | | | | | | | | |]; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate; reflexivity.
  - destruct t2; cbn in H; try discriminate;
      apply fp_variant_eqb_eq in H; subst; reflexivity.
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
  - destruct t2; cbn in H; try discriminate;
      apply ident_eqb_eq in H; subst; reflexivity.
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

(** *** 6.4 [F-19], [F-32] & [F-60]: Prototype Contract, Calling Conventions,
       ABI Parameter Attributes, and Function Attributes *)

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
  repeat split; try assumption;
    intros Hx; rewrite Hx in *; cbn in *; assumption.
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
            ("undefined identified type referenced by " ++ side ++
             " declaration '" ++ cf_raw_id_str (dc_name dc) ++ "'")))
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
                    ("undefined identified type referenced by " ++ side ++
                     " type def '" ++ cf_ident_str (fst p) ++ "'")))
              0 (m_type_defs M)) as [| []] eqn:E1; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun _ g =>
                guard_err (global_identified_defined (m_type_defs M) g)
                  (fun _ => diag "ir-type"
                    ("undefined identified type referenced by " ++ side ++
                     " global '" ++ cf_raw_id_str (g_ident g) ++ "'")))
              0 (m_globals M)) as [| []] eqn:E2; cbn [bind_err] in H; [discriminate H |].
  destruct (cf_check_idx_diag_acc
              (fun _ dc =>
                guard_err (decl_identified_defined (m_type_defs M) dc)
                  (fun _ => diag "ir-type"
                    ("undefined identified type referenced by " ++ side ++
                     " declaration '" ++ cf_raw_id_str (dc_name dc) ++ "'")))
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

