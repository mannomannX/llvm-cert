(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Module-Merge Poison Value & Relational DrawE Core ([CertPasses.ModuleMergeVDrawCore])

    Purpose:
      Defines poison-to-concrete value refinement ([mm_dvalue_refines],
      [prog_value_refines]), the relational [DrawE]+[ProvE] model
      ([refine_prov_draw], [prog_value_draw_refines]), and the generalized
      stack/CFG simulation ([vds_sim], [cfg_vdraw_sim], [mcfg_vdraw_sim]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml (imported by
      [ModuleMergeVDrawLift] and re-exported by [CertPasses.ModuleMerge]).

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, and
      [CertPasses.{PassCommon,SimplifyCFG,DCE,SCCP,Mem2Reg,Inline,Pipeline,
      McfgExport}]; zero custom axioms (arbitrary [IPtr] / [IPtrTheory]).

    Section Outline:
      (8) Value-refinement & relational [DrawE] composition: (8.1)
      [prog_value_refines]; (8.2) [refine_prov_draw] &
      [prog_value_draw_refines]; (8.3) [VDrawGenSim] ([vds_sim], [mcfg_vdraw_sim]). *)

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
  Lia
  Classes.RelationClasses.
Import ListNotations.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
  Semantics.VellvmIntegers
  Utils
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Semantics
  ScopeTheory
  Utils.rutt_cutoff
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.Denotation
  Semantics.TopLevel
  Semantics.Libraries
  Semantics.LLVMEvents
  Theory.I2F.Refinement
  Theory.I2F.I2F_interp
  Theory.I2F.I2F_toplevel.

From CertPasses Require Import
  PassCommon
  SimplifyCFG
  DCE
  SCCP
  Mem2Reg
  Inline
  Pipeline
  McfgExport.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.
#[local] Open Scope list_scope.
#[local] Existing Instance MemoryModelStateV.
#[local] Existing Instance MemoryModelPrimitivesV.

(** * 8. Value-Refinement ([Poison -> Concrete]), Parameter Renaming, & Relational-[DrawE] Composition (F-59) *)

Definition mm_scalar_nonptr_base {Pa : Params} (b : @dvalue_base Pa) : Prop :=
  match b with
  | DVALUE_Pointer _ => False
  | _ => True
  end.

Definition mm_scalar_nonptr_dvalue {Pa : Params} (v : @dvalue Pa) : Prop :=
  match v with
  | DVALUE_Base b => mm_scalar_nonptr_base b
  | _ => False
  end.

Definition mm_ret_dvalue_refines {Pa : Params} (v1 v2 : @dvalue Pa) : Prop :=
  v1 = v2 \/ (v1 = DVALUE_Base DVALUE_Poison /\ mm_scalar_nonptr_dvalue v2).

Lemma mm_ret_dvalue_refines_refl {Pa : Params} (v : @dvalue Pa) :
  mm_ret_dvalue_refines v v.
Proof.
  left; reflexivity.
Qed.

Lemma mm_ret_dvalue_refines_trans {Pa : Params} (v1 v2 v3 : @dvalue Pa) :
  mm_ret_dvalue_refines v1 v2 ->
  mm_ret_dvalue_refines v2 v3 ->
  mm_ret_dvalue_refines v1 v3.
Proof.
  intros [<- | [-> H2]] [<- | [-> H3]];
    first [left; reflexivity | right; split; [reflexivity | assumption]].
Qed.

#[global] Instance mm_ret_dvalue_refines_PreOrder {Pa : Params} :
  PreOrder (@mm_ret_dvalue_refines Pa) :=
  Build_PreOrder _ (@mm_ret_dvalue_refines_refl Pa) (@mm_ret_dvalue_refines_trans Pa).

Inductive mm_dvalue_refines {Pa : Params} : @dvalue Pa -> @dvalue Pa -> Prop :=
| mm_dvr_refl v : mm_dvalue_refines v v
| mm_dvr_poison v : mm_dvalue_refines (DVALUE_Base DVALUE_Poison) v
| mm_dvr_struct pk fs1 fs2 :
    Forall2 mm_dvalue_refines fs1 fs2 ->
    mm_dvalue_refines (DVALUE_Struct pk fs1) (DVALUE_Struct pk fs2)
| mm_dvr_array dt es1 es2 :
    Forall2 mm_dvalue_refines es1 es2 ->
    mm_dvalue_refines (DVALUE_Array dt es1) (DVALUE_Array dt es2).

Lemma mm_dvalue_refines_refl {Pa : Params} (v : @dvalue Pa) :
  mm_dvalue_refines v v.
Proof.
  constructor.
Qed.

Fixpoint mm_dvalue_depth {Pa : Params} (v : @dvalue Pa) : nat :=
  let fix list_depth (l : list (@dvalue Pa)) : nat :=
    match l with
    | [] => 0%nat
    | x :: xs => S (Nat.max (mm_dvalue_depth x) (list_depth xs))
    end
  in
  match v with
  | DVALUE_Base _ => 0%nat
  | DVALUE_Struct _ fs => S (list_depth fs)
  | DVALUE_Array _ es => S (list_depth es)
  end.

Lemma mm_dvalue_refines_trans_bounded {Pa : Params} :
  forall (n : nat) (v1 v2 v3 : @dvalue Pa),
    (mm_dvalue_depth v1 <= n)%nat ->
    mm_dvalue_refines v1 v2 ->
    mm_dvalue_refines v2 v3 ->
    mm_dvalue_refines v1 v3.
Proof.
  induction n as [| n' IH]; intros v1 v2 v3 Hle H12 H23.
  - inversion H12 as [| | pk fs1 fs2 _ | dt es1 es2 _]; subst; cbn in Hle;
      [exact H23 | constructor | lia | lia].
  - inversion H12 as [| | pk fs1 fs2 Hfs12 | dt es1 es2 Hes12]; subst;
      [exact H23 | constructor | |].
    + inversion H23 as [| | ? ? fs3 Hfs23 |]; subst; [constructor; exact Hfs12 | constructor].
      cbn in Hle; apply le_S_n in Hle.
      clear H12 H23; revert fs3 Hfs23 Hle;
        induction Hfs12 as [| x1 x2 r1 r2 Hx12 _ IHr]; intros fs3 Hfs23 Hle;
        inversion Hfs23 as [| ? x3 ? r3 Hx23 Hr23]; subst; [constructor |].
      cbn in Hle; constructor.
      * eapply IH; [| exact Hx12 | exact Hx23]; lia.
      * apply IHr; [exact Hr23 | lia].
    + inversion H23 as [| | | ? ? es3 Hes23]; subst; [constructor; exact Hes12 | constructor].
      cbn in Hle; apply le_S_n in Hle.
      clear H12 H23; revert es3 Hes23 Hle;
        induction Hes12 as [| x1 x2 r1 r2 Hx12 _ IHr]; intros es3 Hes23 Hle;
        inversion Hes23 as [| ? x3 ? r3 Hx23 Hr23]; subst; [constructor |].
      cbn in Hle; constructor.
      * eapply IH; [| exact Hx12 | exact Hx23]; lia.
      * apply IHr; [exact Hr23 | lia].
Qed.

Lemma mm_dvalue_refines_trans {Pa : Params} (v1 v2 v3 : @dvalue Pa) :
  mm_dvalue_refines v1 v2 ->
  mm_dvalue_refines v2 v3 ->
  mm_dvalue_refines v1 v3.
Proof.
  exact (mm_dvalue_refines_trans_bounded (mm_dvalue_depth v1) v1 v2 v3 (Nat.le_refl _)).
Qed.

#[global] Instance mm_dvalue_refines_PreOrder {Pa : Params} :
  PreOrder (@mm_dvalue_refines Pa) :=
  Build_PreOrder _ (@mm_dvalue_refines_refl Pa) (@mm_dvalue_refines_trans Pa).

Lemma mm_ret_dvalue_refines_sub {Pa : Params} (v1 v2 : @dvalue Pa) :
  mm_ret_dvalue_refines v1 v2 ->
  mm_dvalue_refines v1 v2.
Proof.
  intros [<- | [-> _]]; constructor.
Qed.

Lemma value_attrs_poison_poison {Pa : Params} (attrs : list param_attr) :
  @value_attrs_poison Pa attrs (DVALUE_Base DVALUE_Poison) = DVALUE_Base DVALUE_Poison.
Proof.
  unfold value_attrs_poison, value_attr_nonnull, value_attr_align, value_attr_range,
         value_metadata_range, value_metadata_range_base, value_attr_nofpclass.
  destruct (find_option attr_range attrs) as [r |];
    cbn [option_map value_metadata_range value_metadata_range_base];
    destruct (find_option attr_nofpclass attrs) as [m |];
    cbn [value_nofpclass fp_class]; reflexivity.
Qed.

Lemma value_attrs_poison_scalar_nonptr {Pa : Params}
  (attrs : list param_attr) (v : @dvalue Pa) :
  mm_scalar_nonptr_dvalue v ->
  mm_scalar_nonptr_dvalue (value_attrs_poison attrs v).
Proof.
  intros Hv.
  assert (Hnn : value_attr_nonnull attrs v = v)
    by (destruct v as [[| | | | | | |] | |]; try contradiction; reflexivity).
  assert (Hal : value_attr_align attrs v = v)
    by (destruct v as [[| | | | | | |] | |]; try contradiction; reflexivity).
  unfold value_attrs_poison; rewrite Hnn, Hal.
  assert (Hrg : mm_scalar_nonptr_dvalue (value_attr_range attrs v)).
  { unfold value_attr_range.
    destruct (find_option attr_range attrs) as [r |]; [| exact Hv].
    destruct v as [[| sz x | | | | | |] | |]; try contradiction;
      cbn [option_map value_metadata_range value_metadata_range_base]; try exact I.
    destruct (in_metadata_ranges sz (VellvmIntegers.unsigned x) [r]); exact I. }
  unfold value_attr_nofpclass.
  destruct (find_option attr_nofpclass attrs) as [m |]; [| exact Hrg].
  destruct (value_attr_range attrs v) as [b | |]; try contradiction.
  cbn [value_nofpclass]; destruct (fp_class b); [| exact Hrg].
  destruct (Z.land m z =? 0)%Z; [exact Hrg | exact I].
Qed.

Lemma combine_lists_varargs_same_len {A1 A2 B : Type}
  (l1 : list A1) (l2 : list A2) (args : list B) :
  List.length l1 = List.length l2 ->
  (exists msg,
     combine_lists_varargs l1 args = raise_error msg /\
     combine_lists_varargs l2 args = raise_error msg) \/
  (exists fvs vargs,
     List.length fvs = List.length l1 /\
     combine_lists_varargs l1 args = raise_ret (List.combine l1 fvs, vargs) /\
     combine_lists_varargs l2 args = raise_ret (List.combine l2 fvs, vargs)).
Proof.
  revert l2 args; induction l1 as [| x1 xs1 IH]; intros [| x2 xs2] args Hlen;
    try discriminate Hlen.
  - right; exists [], args; split; [reflexivity |]; destruct args; split; reflexivity.
  - injection Hlen as Hlen'.
    destruct args as [| y ys].
    + left; exists "combine_lists_varargs: too few arguments"%string; split; reflexivity.
    + destruct (IH xs2 ys Hlen') as [[msg [E1 E2]] | (fvs & vargs & Hlf & E1 & E2)].
      * cbn [combine_lists_varargs]; rewrite E1, E2; cbn.
        left; exists msg; split; reflexivity.
      * cbn [combine_lists_varargs]; rewrite E1, E2; cbn.
        right; exists (y :: fvs), vargs.
        split; [cbn; f_equal; exact Hlf | split; reflexivity].
Qed.

Lemma map_fst_combine_eq {A B : Type} (xs : list A) (ys : list B) :
  List.length ys = List.length xs ->
  List.map fst (List.combine xs ys) = xs.
Proof.
  revert ys; induction xs as [| x r IH]; intros [| y ry] Hlen; try discriminate Hlen.
  - reflexivity.
  - injection Hlen as Hlen'; cbn; f_equal; exact (IH ry Hlen').
Qed.

Section ValueDrawRefinement.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.
  #[local] Hint Resolve refine_prov__mon cfg_local_sim__mon gen_stack_sim__mon : paco.

  #[local] Notation PaV := (@ParamsV IP IPT).

  (** ** 8.1 Whole-Module Poison->Concrete Value Refinement over [run_mcfg_model] *)

  Definition prog_value_refines (M1 M2 : CFG.mcfg dtyp) : Prop :=
    forall (ret_typ : dtyp) (entry : function_id) (args : list (@dvalue PaV)) (U : list N),
      refine_prov (fun _ r1 r2 => mm_ret_dvalue_refines (snd r1) (snd r2)) U
        (run_mcfg_model ret_typ entry args M1)
        (run_mcfg_model ret_typ entry args M2).

  Lemma prog_value_refines_refl (M : CFG.mcfg dtyp) :
    prog_value_refines M M.
  Proof using.
    intros ret_typ entry args U.
    apply refine_prov_refl; intros; apply mm_ret_dvalue_refines_refl.
  Qed.

  Lemma prog_refines_to_value_refines (M1 M2 : CFG.mcfg dtyp) :
    @prog_refines IP IPT M1 M2 ->
    prog_value_refines M1 M2.
  Proof using.
    intros Href ret_typ entry args U.
    pose proof (Href ret_typ entry args U) as Hm.
    eapply refine_prov_obs_eq;
      [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply refine_prov_bind; [exact Hm |].
    intros U' r1 r2 _ Heq; apply refine_prov_obs_eq with (t1 := Ret r1) (t2 := Ret r2);
      [reflexivity | reflexivity | pstep; apply RP_Step; cbn; left; exact Heq].
  Qed.

  (** ** 8.2 Relational-[DrawE] + [ProvE] Whole-Module Model ([prog_value_draw_refines]) *)

  Definition ProvDrawBotE : Type -> Type := @DrawE PaV +' ProvBotE.

  Definition mm_valid_draw (dt : dtyp) (v : @dvalue PaV) : Prop :=
    is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt /\ dvalue_well_defined v = true.

  Definition mm_canonical_draw (dt : dtyp) : @dvalue PaV :=
    match default_dvalue_of_dtyp dt with
    | raise_ret dv => dv
    | _ => DVALUE_Base DVALUE_None
    end.

  Lemma mm_canonical_draw_valid (dt : dtyp) :
    mm_valid_draw dt (mm_canonical_draw dt).
  Proof using.
    intros Hsc; unfold mm_canonical_draw.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    destruct dtb as [sz | | | | fp | | | | | | bsz]; try discriminate Hsc;
      try (destruct fp; try discriminate Hsc);
      cbn [default_dvalue_of_dtyp];
      (split; [apply DVALUE_Base_typ; cbn; try apply Pos.eqb_refl; reflexivity | reflexivity]).
  Qed.

  Definition lift_prov_to_draw {T} (t : itree ProvBotE T) : itree ProvDrawBotE T :=
    translate inr1 t.

  Definition interp_vellvm_rel_draw_h :
    @MCFGEtop PaV ~> Monads.stateT FusedS (itree ProvDrawBotE) :=
    case_ ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT (@ExternalCallE PaV) (fun _ x => inr1 (inl1 x)) T e s))
             : @ExternalCallE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (fused_intrinsic_prov T e s))
             : @IntrinsicE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (fused_global_prov T e s))
             : @GlobalE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ (case_ ((fun T e s => lift_prov_to_draw (fused_local_prov T e s))
                    : @LocalE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
                 ((fun T e s => lift_prov_to_draw (fused_stack_prov T e s))
                    : @StackE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE)))
   (case_ ((fun T e s => lift_prov_to_draw (fused_memory_prov T e s))
             : @MemoryE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T (e : @DrawE PaV T) s =>
             ITree.bind (ITree.trigger (inl1 e)) (fun r => Ret (s, r)))
             : @DrawE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT OOME (fun _ x => inr1 (inr1 (inl1 x))) T e s))
             : OOME ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT (@LLVMExcE PaV) (fun _ x => inr1 (inr1 (inr1 (inl1 x)))) T e s))
             : @LLVMExcE PaV ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT UBE (fun _ x => inr1 (inr1 (inr1 (inr1 (inl1 x))))) T e s))
             : UBE ~> Monads.stateT FusedS (itree ProvDrawBotE))
   (case_ ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT DebugE (fun _ x => inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))) T e s))
             : DebugE ~> Monads.stateT FusedS (itree ProvDrawBotE))
          ((fun T e s => lift_prov_to_draw (@fused_trigger_prov IP IPT FailureE (fun _ x => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x)))))) T e s))
             : FailureE ~> Monads.stateT FusedS (itree ProvDrawBotE))))))))))).

  Arguments interp_vellvm_rel_draw_h [T] _ _.

  Definition interp_mcfg_rel_draw_model {R}
    (t : @MCFGtop PaV R) (s : FusedS) : itree ProvDrawBotE (Res R) :=
    interp_state interp_vellvm_rel_draw_h (interp_intrinsics t) s.

  Definition run_mcfg_rel_draw_model
    (ret_typ : dtyp) (entry : function_id) (args : list (@dvalue PaV))
    (M : CFG.mcfg dtyp) : itree ProvDrawBotE (Res (@dvalue PaV)) :=
    interp_mcfg_rel_draw_model (denote_vellvm ret_typ entry args M) init_fused_state.

  Definition is_ub_prov_draw {X} (e : ProvDrawBotE X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 pe => is_ub_prov pe
    end.

  Definition rpd_vis_both {R1 R2}
    (r : list N -> itree ProvDrawBotE R1 -> itree ProvDrawBotE R2 -> Prop)
    (U : list N)
    {X1} (e1 : ProvDrawBotE X1) (k1 : X1 -> itree ProvDrawBotE R1)
    {X2} (e2 : ProvDrawBotE X2) (k2 : X2 -> itree ProvDrawBotE R2) : Prop :=
    match e1 return (X1 -> itree ProvDrawBotE R1) -> Prop with
    | inl1 d1 => fun k1' =>
        match e2 return (X2 -> itree ProvDrawBotE R2) -> Prop with
        | inl1 d2 => fun k2' =>
            match d1 in DrawE Z1 return (Z1 -> itree ProvDrawBotE R1) -> Prop with
            | Draw dt1 => fun k1'' =>
                match d2 in DrawE Z2 return (Z2 -> itree ProvDrawBotE R2) -> Prop with
                | Draw dt2 => fun k2'' =>
                    dt1 = dt2 /\
                    forall v, mm_valid_draw dt1 v -> r U (k1'' v) (k2'' v)
                end k2'
            end k1'
        | inr1 _ => fun _ => False
        end k2
    | inr1 pe1 => fun k1' =>
        match e2 return (X2 -> itree ProvDrawBotE R2) -> Prop with
        | inl1 _ => fun _ => False
        | inr1 pe2 => fun k2' =>
            match pe1 return (X1 -> itree ProvDrawBotE R1) -> Prop with
            | inl1 p1 => fun kp1 =>
                match pe2 return (X2 -> itree ProvDrawBotE R2) -> Prop with
                | inl1 p2 => fun kp2 =>
                    match p1 in ProvE Z1 return (Z1 -> itree ProvDrawBotE R1) -> Prop with
                    | FreshProv => fun kp1' =>
                        match p2 in ProvE Z2 return (Z2 -> itree ProvDrawBotE R2) -> Prop with
                        | FreshProv => fun kp2' =>
                            forall p : N, ~ In p U -> r (p :: U) (kp1' p) (kp2' p)
                        end kp2
                    end kp1
                | inr1 _ => fun _ => False
                end k2'
            | inr1 b1 => fun kb1 =>
                match pe2 return (X2 -> itree ProvDrawBotE R2) -> Prop with
                | inl1 _ => fun _ => False
                | inr1 b2 => fun kb2 =>
                    EqE_bot _ _ b1 b2 /\
                    forall a1 a2, EqA_bot _ _ b1 a1 b2 a2 ->
                      r (bot_ans_provs b1 a1 ++ U) (kb1 a1) (kb2 a2)
                end k2'
            end k1'
        end k2
    end k1.

  Definition rpd_step_body {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvDrawBotE R1 -> itree ProvDrawBotE R2 -> Prop)
    (U : list N)
    (ot1 : itree' ProvDrawBotE R1) (ot2 : itree' ProvDrawBotE R2)
    (t2 : itree ProvDrawBotE R2) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => RR U r1 r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r U m1 m2
        | _ => False
        end
    | VisF _ e1 k1 =>
        is_ub_prov_draw e1 = true
        \/ (match e1 with
            | inl1 _ => fun _ => False
            | inr1 pe1 => fun k1' =>
                match pe1 with
                | inl1 p1 => fun kp1 =>
                    match p1 in ProvE Z1 return (Z1 -> itree ProvDrawBotE R1) -> Prop with
                    | FreshProv => fun kp1' =>
                        forall p : N, ~ In p U -> r (p :: U) (kp1' p) t2
                    end kp1
                | inr1 _ => fun _ => False
                end k1'
            end k1)
        \/ (match ot2 with
            | VisF _ e2 k2 => rpd_vis_both r U e1 k1 e2 k2
            | _ => False
            end)
    end.

  Inductive refine_prov_draw_ {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvDrawBotE R1 -> itree ProvDrawBotE R2 -> Prop)
    : list N -> itree ProvDrawBotE R1 -> itree ProvDrawBotE R2 -> Prop :=
  | RPD_Step U t1 t2 :
      rpd_step_body RR r U (observe t1) (observe t2) t2 ->
      refine_prov_draw_ RR r U t1 t2
  | RPD_TauL U t1 m1 t2 :
      observe t1 = TauF m1 ->
      refine_prov_draw_ RR r U m1 t2 ->
      refine_prov_draw_ RR r U t1 t2
  | RPD_TauR U t1 t2 m2 :
      observe t2 = TauF m2 ->
      refine_prov_draw_ RR r U t1 m2 ->
      refine_prov_draw_ RR r U t1 t2
  | RPD_DrawL U t1 dt v k1 t2 :
      t1 ≅ ITree.bind (ITree.trigger (inl1 (Draw dt))) k1 ->
      mm_valid_draw dt v ->
      refine_prov_draw_ RR r U (k1 v) t2 ->
      refine_prov_draw_ RR r U t1 t2
  | RPD_DrawR U t1 t2 dt k2 :
      t2 ≅ ITree.bind (ITree.trigger (inl1 (Draw dt))) k2 ->
      (forall v, mm_valid_draw dt v -> refine_prov_draw_ RR r U t1 (k2 v)) ->
      refine_prov_draw_ RR r U t1 t2.

  Lemma refine_prov_draw__mon {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    monotone3 (refine_prov_draw_ RR).
  Proof using.
    intros U t1 t2 r r' IN LE.
    induction IN as [U t1 t2 Hstep
                     | U t1 m1 t2 Ht1 _ IH
                     | U t1 t2 m2 Ht2 _ IH
                     | U t1 dt v k1 t2 Ht1 Hv _ IH
                     | U t1 t2 dt k2 Ht2 _ IH].
    - apply RPD_Step; unfold rpd_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left.
          destruct e1 as [d1 | [p1 | b1]]; try contradiction.
          destruct p1; intros p Hp; apply LE, Hleft, Hp.
        * right; right.
          destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [d1 | [p1 | b1]], e2 as [d2 | [p2 | b2]]; cbn in *; try contradiction.
          -- destruct d1 as [dt1], d2 as [dt2]; destruct Hboth as [Hdt Hk]; split; [exact Hdt |].
             intros v Hv; apply LE, Hk, Hv.
          -- destruct p1, p2; intros p Hp; apply LE, Hboth, Hp.
          -- destruct Hboth as [HE HA]; split; [exact HE | intros a1 a2 Ha; apply LE, HA, Ha].
    - eapply RPD_TauL; [exact Ht1 | exact IH].
    - eapply RPD_TauR; [exact Ht2 | exact IH].
    - eapply RPD_DrawL; [exact Ht1 | exact Hv | exact IH].
    - eapply RPD_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv)].
  Qed.
  #[local] Hint Resolve refine_prov_draw__mon : paco.

  Definition refine_prov_draw {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvDrawBotE R1) (t2 : itree ProvDrawBotE R2) : Prop :=
    paco3 (refine_prov_draw_ RR) bot3 U t1 t2.

  Lemma refine_prov_draw__obs_eq {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r r' : list N -> itree ProvDrawBotE R1 -> itree ProvDrawBotE R2 -> Prop)
    (Hr_eq : forall U a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r U a1 a2 -> r' U a1' a2') :
    forall U (t1 t1' : itree ProvDrawBotE R1) (t2 t2' : itree ProvDrawBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov_draw_ RR r U t1 t2 ->
      refine_prov_draw_ RR r' U t1' t2'.
  Proof using.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    revert t1' t2' E1 E2;
      induction Hrel as [U t1 t2 Hstep
                         | U t1 m1 t2 Ht1 _ IH
                         | U t1 t2 m2 Ht2 _ IH
                         | U t1 dt v k1 t2 Ht1 Hv _ IH
                         | U t1 t2 dt k2 Ht2 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply RPD_Step; unfold rpd_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [d1 | [p1 | b1]]; try contradiction; destruct p1.
          intros p Hp; eapply Hr_eq; [apply Hk1 | pstep; exact E2 | exact (Hleft p Hp)].
        * right; right.
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct e1 as [d1 | [p1 | b1]], e2 as [d2 | [p2 | b2]]; cbn in *; try contradiction.
          -- destruct d1 as [dt1], d2 as [dt2]; destruct Hboth as [Hdt Hk]; split; [exact Hdt |].
             intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (Hk v Hv)].
          -- destruct p1, p2; intros p Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (Hboth p Hp)].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha)].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply RPD_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
    - punfold E2; red in E2; rewrite Ht2 in E2;
        apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
      eapply RPD_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
    - eapply RPD_DrawL;
        [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
        | exact Hv
        | eapply IH; [reflexivity | exact E2]].
    - eapply RPD_DrawR;
        [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
        | intros v Hv; eapply IH; [exact Hv | exact E1 | reflexivity]].
  Qed.

  Lemma refine_prov_draw_obs_eq {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 t1' : itree ProvDrawBotE R1) (t2 t2' : itree ProvDrawBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov_draw RR U t1 t2 ->
      refine_prov_draw RR U t1' t2'.
  Proof using.
    pcofix CIH.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    pstep; punfold Hrel.
    eapply refine_prov_draw__obs_eq; [| exact E1 | exact E2 | exact Hrel].
    intros U0 a1 a1' a2 a2' Ea1 Ea2 Hr; pclearbot.
    right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
  Qed.

  Lemma refine_prov_draw_refl {R} (RR : list N -> R -> R -> Prop)
    (HRR : forall U r, RR U r r) :
    forall U (t : itree ProvDrawBotE R), refine_prov_draw RR U t t.
  Proof using.
    pcofix CIH; intros U t; pstep; apply RPD_Step; unfold rpd_step_body.
    destruct (observe t) as [x | m | X e k].
    - apply HRR.
    - right; apply CIH.
    - right; right.
      revert k; destruct e as [[dt] | [p | b]]; intros k; cbn.
      + split; [reflexivity | intros v _; right; apply CIH].
      + revert k; destruct p; intros k; intros q _; right; apply CIH.
      + split; [apply EqE_bot_refl |].
        intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2; right; apply CIH.
  Qed.

  Lemma refine_prov_draw_antitone {R1 R2} (RR1 RR2 : list N -> R1 -> R2 -> Prop)
    (HRR : forall U U' r1 r2, incl U U' -> RR1 U r1 r2 -> RR2 U' r1 r2) :
    forall U U' t1 t2,
      incl U U' ->
      refine_prov_draw RR1 U t1 t2 ->
      refine_prov_draw RR2 U' t1 t2.
  Proof using.
    pcofix CIH.
    intros U U' t1 t2 Hincl Hrel; pstep; punfold Hrel.
    revert U' Hincl;
      induction Hrel as [U t1 t2 Hstep
                         | U t1 m1 t2 Ht1 _ IH
                         | U t1 t2 m2 Ht2 _ IH
                         | U t1 dt v k1 t2 Ht1 Hv _ IH
                         | U t1 t2 dt k2 Ht2 _ IH];
      intros U' Hincl.
    - apply RPD_Step; unfold rpd_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; eapply HRR; eassumption.
      + destruct (observe t2); try contradiction; pclearbot; right; eapply CIH; eassumption.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [d1 | [p1 | b1]]; try contradiction; destruct p1.
          intros p Hp.
          assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
          specialize (Hleft p HpU); pclearbot; right; eapply CIH; [| exact Hleft].
          intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
        * right; right; destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [d1 | [p1 | b1]], e2 as [d2 | [p2 | b2]]; cbn in *; try contradiction.
          -- destruct d1 as [dt1], d2 as [dt2]; destruct Hboth as [Hdt Hk]; split; [exact Hdt |].
             intros v Hv; specialize (Hk v Hv); pclearbot; right; eapply CIH; [exact Hincl | exact Hk].
          -- destruct p1, p2; intros p Hp.
             assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
             specialize (Hboth p HpU); pclearbot; right; eapply CIH; [| exact Hboth].
             intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; eapply CIH; [| exact HA].
             intros z Hz; apply in_app_iff in Hz; apply in_app_iff.
             destruct Hz as [Hz | Hz]; [left; exact Hz | right; apply Hincl, Hz].
    - eapply RPD_TauL; [exact Ht1 | apply IH, Hincl].
    - eapply RPD_TauR; [exact Ht2 | apply IH, Hincl].
    - eapply RPD_DrawL; [exact Ht1 | exact Hv | apply IH, Hincl].
    - eapply RPD_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv U' Hincl)].
  Qed.

  Lemma refine_prov_draw_bind {R1 R2 S1 S2}
    (RR : list N -> R1 -> R2 -> Prop) (RS : list N -> S1 -> S2 -> Prop)
    (U : list N)
    (t1 : itree ProvDrawBotE R1) (t2 : itree ProvDrawBotE R2)
    (k1 : R1 -> itree ProvDrawBotE S1) (k2 : R2 -> itree ProvDrawBotE S2)
    (Ht : refine_prov_draw RR U t1 t2)
    (Hk : forall U' r1 r2, incl U U' -> RR U' r1 r2 -> refine_prov_draw RS U' (k1 r1) (k2 r2)) :
    refine_prov_draw RS U (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    revert U t1 t2 Ht Hk; pcofix CIH; intros U t1 t2 Ht Hk.
    punfold Ht.
    revert Hk;
      induction Ht as [U t1 t2 Hstep
                       | U t1 m1 t2 Ht1 _ IH
                       | U t1 t2 m2 Ht2 _ IH
                       | U t1 dt v k1' t2 Ht1 Hv _ IH
                       | U t1 t2 dt k2' Ht2 _ IH];
      intros Hk.
    - unfold rpd_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        eapply paco3_mon;
          [eapply refine_prov_draw_obs_eq;
             [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
             | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
             | exact (Hk U r1 r2 (incl_refl U) Hstep)]
          | intros ? ? ? []].
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        pclearbot; pstep; apply RPD_Step; unfold rpd_step_body.
        rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
        right; eapply CIH; [exact Hstep | exact Hk].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * pstep; apply RPD_Step; unfold rpd_step_body; rewrite (observe_bind t1 k1), Hot1; left; exact Hub.
        * pstep; apply RPD_Step; unfold rpd_step_body; rewrite (observe_bind t1 k1), Hot1; right; left.
          destruct e1 as [d1 | [p1 | b1]]; try contradiction; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; eapply CIH; [exact Hleft |].
          intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
          intros z Hz; apply Hincl; right; exact Hz.
        * destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          pstep; apply RPD_Step; unfold rpd_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2; right; right.
          destruct e1 as [d1 | [p1 | b1]], e2 as [d2 | [p2 | b2]]; cbn in *; try contradiction.
          -- destruct d1 as [dt1], d2 as [dt2]; destruct Hboth as [Hdt Hd]; split; [exact Hdt |].
             intros v Hv; specialize (Hd v Hv); pclearbot.
             right; eapply CIH; [exact Hd | exact Hk].
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             right; eapply CIH; [exact Hboth |].
             intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
             intros z Hz; apply Hincl; right; exact Hz.
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             right; eapply CIH; [exact HA |].
             intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
             intros z Hz; apply Hincl, in_app_iff; right; exact Hz.
    - specialize (IH Hk); punfold IH; pstep.
      eapply RPD_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply RPD_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply RPD_DrawL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hv | exact IH].
    - pstep; eapply RPD_DrawR; [rewrite Ht2, Eqit.bind_bind; reflexivity |].
      intros v Hv; specialize (IH v Hv Hk); punfold IH; exact IH.
  Qed.

  Lemma refine_prov_to_rel_draw {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2),
      refine_prov RR U t1 t2 ->
      refine_prov_draw RR U (lift_prov_to_draw t1) (lift_prov_to_draw t2).
  Proof using.
    pcofix CIH; intros U t1 t2 Ht; pstep; punfold Ht.
    induction Ht as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH].
    - apply RPD_Step; unfold rpd_step_body, rp_step_body, lift_prov_to_draw in *.
      rewrite !observe_translate.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; exact Hstep.
      + destruct (observe t2); try contradiction; pclearbot; right; apply CIH, Hstep.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot; right; apply CIH, Hleft.
        * right; right; destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot; right; apply CIH, Hboth.
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; apply CIH, HA.
    - eapply RPD_TauL; [unfold lift_prov_to_draw; rewrite observe_translate, Ht1; reflexivity | exact IH].
    - eapply RPD_TauR; [unfold lift_prov_to_draw; rewrite observe_translate, Ht2; reflexivity | exact IH].
  Qed.

  Lemma lift_prov_to_draw_ret {T} (x : T) :
    lift_prov_to_draw (Ret x) ≅ Ret x.
  Proof using.
    unfold lift_prov_to_draw; rewrite unfold_translate; reflexivity.
  Qed.

  Definition prog_value_draw_refines (M1 M2 : CFG.mcfg dtyp) : Prop :=
    forall (ret_typ : dtyp) (entry : function_id) (args : list (@dvalue PaV)) (U : list N),
      refine_prov_draw (fun _ r1 r2 => mm_ret_dvalue_refines (snd r1) (snd r2)) U
        (run_mcfg_rel_draw_model ret_typ entry args M1)
        (run_mcfg_rel_draw_model ret_typ entry args M2).

  Lemma prog_value_draw_refines_refl (M : CFG.mcfg dtyp) :
    prog_value_draw_refines M M.
  Proof using.
    intros ret_typ entry args U.
    apply refine_prov_draw_refl; intros; apply mm_ret_dvalue_refines_refl.
  Qed.

  (** ** 8.3 Generalized Stack/CFG Simulation with Asymmetric [DrawE] & Parameter Renaming *)

  Definition vds_vis_both {E : Type -> Type}
    (is_sync : forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_local : forall X, E X -> option (@LocalE PaV X))
    (as_stack : forall X, E X -> option (@StackE PaV X))
    {R1 R2}
    (r : env_stack -> @local_env PaV -> @local_env PaV ->
         itree E R1 -> itree E R2 -> Prop)
    (stk : env_stack)
    (env1 env2 : @local_env PaV)
    {X1} (e1 : E X1) (k1 : X1 -> itree E R1)
    {X2} (e2 : E X2) (k2 : X2 -> itree E R2) : Prop :=
    (is_sync X1 e1 = true /\
     EqE X1 X2 e1 e2 /\
     forall a1 a2,
       EqA X1 X2 e1 a1 e2 a2 ->
       ev_post X1 e1 a1 ->
       r stk env1 env2 (k1 a1) (k2 a2))
    \/
    (match as_local X1 e1, as_local X2 e2 with
     | Some le1, Some le2 =>
         match le1 in LocalE Y1 return (Y1 -> itree E R1) -> Prop with
         | LocalRead x1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalRead x2 => fun k2' =>
                 x1 = x2 /\
                 Maps.lookup x1 env1 = Maps.lookup x1 env2 /\
                 forall v, Maps.lookup x1 env1 = Some v -> r stk env1 env2 (k1' v) (k2' v)
             | _ => fun _ => False
             end k2
         | LocalWrite x1 v1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalWrite x2 v2 => fun k2' =>
                 x1 = x2 /\ v1 = v2 /\
                 r stk (Maps.add x1 v1 env1) (Maps.add x1 v1 env2) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         end k1
     | _, _ => False
     end)
    \/
    (match as_stack X1 e1, as_stack X2 e2 with
     | Some se1, Some se2 =>
         match se1 in StackE Y1 return (Y1 -> itree E R1) -> Prop with
         | StackPush bs1 => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPush bs2 => fun k2' =>
                 r ((env1, env2) :: stk) (init_local_env bs1) (init_local_env bs2) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         | StackPop => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPop => fun k2' =>
                 match stk with
                 | (p1, p2) :: rest => r rest p1 p2 (k1' tt) (k2' tt)
                 | [] => True
                 end
             | _ => fun _ => False
             end k2
         | _ => fun _ => False
         end k1
     | _, _ => False
     end).

  Section VDrawGenSim.
    Context {E : Type -> Type} `{@LocalE PaV -< E} `{@DrawE PaV -< E}.
    Variable (is_ub : forall X, E X -> bool).
    Variable (is_sync : forall X, E X -> bool).
    Variable (EqE : prerel E E).
    Variable (EqA : postrel E E).
    Variable (ev_post : forall X, E X -> X -> Prop).
    Variable (as_loc : forall X, E X -> option (@LocalE PaV X)).
    Variable (as_stk : forall X, E X -> option (@StackE PaV X)).

    Definition vds_step_body {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env PaV -> @local_env PaV -> itree E R1 -> itree E R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env PaV)
      (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
      match ot1 with
      | RetF r1 =>
          match ot2 with
          | RetF r2 => RR stk env1 env2 r1 r2
          | _ => False
          end
      | TauF m1 =>
          match ot2 with
          | TauF m2 => r stk env1 env2 m1 m2
          | _ => False
          end
      | VisF _ e1 k1 =>
          is_ub _ e1 = true \/
          match ot2 with
          | VisF _ e2 k2 => vds_vis_both is_sync EqE EqA ev_post as_loc as_stk r stk env1 env2 e1 k1 e2 k2
          | _ => False
          end
      end.

    Inductive vds_sim_ {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env PaV -> @local_env PaV -> itree E R1 -> itree E R2 -> Prop)
      : env_stack -> @local_env PaV -> @local_env PaV -> itree E R1 -> itree E R2 -> Prop :=
    | VDS_Step stk env1 env2 t1 t2 :
        vds_step_body RR r stk env1 env2 (observe t1) (observe t2) ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_TauL stk env1 env2 t1 m1 t2 :
        observe t1 = TauF m1 ->
        vds_sim_ RR r stk env1 env2 m1 t2 ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_TauR stk env1 env2 t1 t2 m2 :
        observe t2 = TauF m2 ->
        vds_sim_ RR r stk env1 env2 t1 m2 ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_ReadL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k1 ->
        Maps.lookup x env1 = Some v ->
        vds_sim_ RR r stk env1 env2 (k1 v) t2 ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_ReadR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k2 ->
        Maps.lookup x env2 = Some v ->
        vds_sim_ RR r stk env1 env2 t1 (k2 v) ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_WriteL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k1 ->
        vds_sim_ RR r stk (Maps.add x v env1) env2 (k1 tt) t2 ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_WriteR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k2 ->
        vds_sim_ RR r stk env1 (Maps.add x v env2) t1 (k2 tt) ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_DrawL stk env1 env2 t1 dt v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (Draw dt))) k1 ->
        mm_valid_draw dt v ->
        vds_sim_ RR r stk env1 env2 (k1 v) t2 ->
        vds_sim_ RR r stk env1 env2 t1 t2
    | VDS_DrawR stk env1 env2 t1 t2 dt k2 :
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (Draw dt))) k2 ->
        (forall v, mm_valid_draw dt v -> vds_sim_ RR r stk env1 env2 t1 (k2 v)) ->
        vds_sim_ RR r stk env1 env2 t1 t2.

    Lemma vds_sim__mon {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
      monotone5 (vds_sim_ RR).
    Proof using.
      intros stk env1 env2 t1 t2 r r' IN LE.
      induction IN as [stk env1 env2 t1 t2 Hstep
                       | stk env1 env2 t1 m1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 m2 Ht2 _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 _ IH
                       | stk env1 env2 t1 dt v k1 t2 Ht1 Hv _ IH
                       | stk env1 env2 t1 t2 dt k2 Ht2 _ IH].
      - apply VDS_Step; unfold vds_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE | intros a1 a2 Ha Hp; apply LE, (HA a1 a2 Ha Hp)]].
          * right; left.
             destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
             -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply LE, Hr]].
             -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk | intros v Hv; apply LE, Hrd, Hv]].
          * right; right.
             destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
             destruct se1, se2; try contradiction.
             -- apply LE, Hstk.
             -- destruct stk as [| [p1 p2] rest]; [exact I | apply LE, Hstk].
      - eapply VDS_TauL; [exact Ht1 | exact IH].
      - eapply VDS_TauR; [exact Ht2 | exact IH].
      - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
      - eapply VDS_WriteL; [exact Ht1 | exact IH].
      - eapply VDS_WriteR; [exact Ht2 | exact IH].
      - eapply VDS_DrawL; [exact Ht1 | exact Hv | exact IH].
      - eapply VDS_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv)].
    Qed.
    #[local] Hint Resolve vds_sim__mon : paco.

    Definition vds_sim {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env PaV)
      (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      paco5 (vds_sim_ RR) bot5 stk env1 env2 t1 t2.

    Lemma vds_sim__obs_eq {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (r r' : env_stack -> @local_env PaV -> @local_env PaV -> itree E R1 -> itree E R2 -> Prop)
      (Hr_eq : forall stk e1 e2 a1 a1' a2 a2',
                 a1 ≅ a1' -> a2 ≅ a2' -> r stk e1 e2 a1 a2 -> r' stk e1 e2 a1' a2') :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        vds_sim_ RR r stk env1 env2 t1 t2 ->
        vds_sim_ RR r' stk env1 env2 t1' t2'.
    Proof using.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      revert t1' t2' E1 E2;
        induction Hsim as [stk env1 env2 t1 t2 Hstep
                           | stk env1 env2 t1 m1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 m2 Ht2 _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 _ IH
                           | stk env1 env2 t1 dt v k1 t2 Ht1 Hv _ IH
                           | stk env1 env2 t1 t2 dt k2 Ht2 _ IH];
        intros t1' t2' E1 E2.
      - punfold E1; red in E1; punfold E2; red in E2.
        apply VDS_Step; unfold vds_step_body in *.
        destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; pclearbot.
        + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; exact Hstep.
        + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hr]]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hrd, Hv].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hstk].
            -- destruct stk as [| [p1 p2] rest]; [exact I | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hstk]].
      - punfold E1; red in E1; rewrite Ht1 in E1;
          apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
        eapply VDS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
      - punfold E2; red in E2; rewrite Ht2 in E2;
          apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
        eapply VDS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
      - eapply VDS_ReadL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hlk | apply IH; [reflexivity | exact E2]].
      - eapply VDS_ReadR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | exact Hlk | apply IH; [exact E1 | reflexivity]].
      - eapply VDS_WriteL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | apply IH; [reflexivity | exact E2]].
      - eapply VDS_WriteR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | apply IH; [exact E1 | reflexivity]].
      - eapply VDS_DrawL; [symmetry; etransitivity; [symmetry; exact Ht1 | exact E1] | exact Hv | apply IH; [reflexivity | exact E2]].
      - eapply VDS_DrawR; [symmetry; etransitivity; [symmetry; exact Ht2 | exact E2] | intros v Hv; eapply IH; [exact Hv | exact E1 | reflexivity]].
    Qed.

    Lemma vds_sim_obs_eq {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        vds_sim RR stk env1 env2 t1 t2 ->
        vds_sim RR stk env1 env2 t1' t2'.
    Proof using.
      pcofix CIH.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      pstep; punfold Hsim.
      eapply vds_sim__obs_eq; [| exact E1 | exact E2 | exact Hsim].
      intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 [Hr | Hb]; [| inversion Hb].
      right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
    Qed.

    Lemma vds_sim_ret {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      stk env1 env2 (r1 : R1) (r2 : R2) :
      RR stk env1 env2 r1 r2 ->
      vds_sim RR stk env1 env2 (Ret r1) (Ret r2).
    Proof using.
      intros HR; pstep; apply VDS_Step; cbn; exact HR.
    Qed.

    Lemma vds_sim_bind {R1 R2 S1 S2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (RS : env_stack -> @local_env PaV -> @local_env PaV -> S1 -> S2 -> Prop)
      stk env1 env2
      (t1 : itree E R1) (t2 : itree E R2)
      (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2)
      (Ht : vds_sim RR stk env1 env2 t1 t2)
      (Hk : forall stk' e1' e2' r1 r2,
              RR stk' e1' e2' r1 r2 ->
              vds_sim RS stk' e1' e2' (k1 r1) (k2 r2)) :
      vds_sim RS stk env1 env2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      revert stk env1 env2 t1 t2 Ht Hk; pcofix CIH;
        intros stk env1 env2 t1 t2 Ht Hk; punfold Ht.
      revert Hk;
        induction Ht as [stk env1 env2 t1 t2 Hstep
                         | stk env1 env2 t1 m1 t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 m2 Ht2 _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 Hlk _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 Hlk _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 _ IH
                         | stk env1 env2 t1 dt v k1' t2 Ht1 Hv _ IH
                         | stk env1 env2 t1 t2 dt k2' Ht2 _ IH];
        intros Hk.
      - unfold vds_step_body in Hstep.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          eapply paco5_mon;
            [eapply vds_sim_obs_eq;
               [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
               | exact (Hk stk env1 env2 r1 r2 Hstep)]
            | intros ? ? ? ? ? []].
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          destruct Hstep as [Hstep | Hb]; [| inversion Hb].
          pstep; apply VDS_Step; unfold vds_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
          right; eapply CIH; [exact Hstep | exact Hk].
        + pstep; apply VDS_Step; unfold vds_step_body.
          rewrite (observe_bind t1 k1), Hot1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          rewrite (observe_bind t2 k2), Hot2.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            right; eapply CIH; [exact HA | exact Hk].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv | right; eapply CIH; [exact Hr | exact Hk]]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hrd | exact Hk].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hr | exact Hk].
            -- destruct stk as [| [p1 p2] rest]; [exact I |].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hr | exact Hk].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_ReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_ReadR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_WriteL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_WriteR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact IH].
      - specialize (IH Hk); punfold IH; pstep.
        eapply VDS_DrawL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hv | exact IH].
      - pstep; eapply VDS_DrawR; [rewrite Ht2, Eqit.bind_bind; reflexivity |].
        intros v Hv; specialize (IH v Hv Hk); punfold IH; exact IH.
    Qed.

    Lemma vds_sim_weaken {R1 R2}
      (RR RS : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      (HRR : forall stk e1 e2 r1 r2, RR stk e1 e2 r1 r2 -> RS stk e1 e2 r1 r2) :
      forall stk env1 env2 t1 t2,
        vds_sim RR stk env1 env2 t1 t2 ->
        vds_sim RS stk env1 env2 t1 t2.
    Proof using.
      intros stk env1 env2 t1 t2 Hsim.
      eapply vds_sim_obs_eq;
        [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
      eapply vds_sim_bind; [exact Hsim |].
      intros s0 e1 e2 r1 r2 Hr; apply vds_sim_ret, HRR, Hr.
    Qed.

    Lemma gen_stack_to_vds_sim {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
      forall stk env1 env2 (t1 : itree E R1) (t2 : itree E R2),
        gen_stack_sim is_ub is_sync EqE EqA ev_post as_loc as_stk RR stk env1 env2 t1 t2 ->
        vds_sim RR stk env1 env2 t1 t2.
    Proof using.
      pcofix CIH; intros stk env1 env2 t1 t2 Hgs; pstep; punfold Hgs.
      induction Hgs as [stk env1 env2 t1 t2 Hstep
                        | stk env1 env2 t1 m1 t2 Ht1 _ IH
                        | stk env1 env2 t1 t2 m2 Ht2 _ IH
                        | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                        | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                        | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                        | stk env1 env2 t1 t2 x v k2 Ht2 _ IH].
      - apply VDS_Step; unfold vds_step_body, gss_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | destruct Hstep as [Hs | Hb]; [right; apply CIH, Hs | inversion Hb] | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [right; apply CIH, HA | inversion Hb].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv | right; apply CIH, Hr]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [right; apply CIH, Hrd | inversion Hb].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [-> [Hr | Hb]]; [right; apply CIH, Hr | inversion Hb].
            -- destruct stk as [| [p1 p2] rest]; [exact I |].
               destruct Hstk as [Hr | Hb]; [right; apply CIH, Hr | inversion Hb].
      - eapply VDS_TauL; [exact Ht1 | exact IH].
      - eapply VDS_TauR; [exact Ht2 | exact IH].
      - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
      - eapply VDS_WriteL; [exact Ht1 | exact IH].
      - eapply VDS_WriteR; [exact Ht2 | exact IH].
    Qed.

  End VDrawGenSim.
  #[local] Hint Extern 1 (monotone5 (vds_sim_ _ _ _ _ _ _ _ _)) => apply vds_sim__mon : paco.

  Definition cfg_vdraw_sim {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    : env_stack -> @local_env PaV -> @local_env PaV -> @CFGtop PaV R1 -> @CFGtop PaV R2 -> Prop :=
    vds_sim (@is_ub_cfg IP IPT) (@sync_non_local_cfg IP IPT) EqE_CFG EqA_CFG
      (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT) RR.

  Definition mcfg_vdraw_sim {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    : env_stack -> @local_env PaV -> @local_env PaV -> @MCFGtop PaV R1 -> @MCFGtop PaV R2 -> Prop :=
    vds_sim (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
      (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) RR.

  Lemma cfg_stack_to_vdraw_sim {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) :
    cfg_stack_sim RR stk env1 env2 t1 t2 ->
    cfg_vdraw_sim RR stk env1 env2 t1 t2.
  Proof using.
    apply gen_stack_to_vds_sim.
  Qed.

  Lemma mcfg_stack_to_vdraw_sim {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 (t1 : @MCFGtop PaV R1) (t2 : @MCFGtop PaV R2) :
    mcfg_stack_sim RR stk env1 env2 t1 t2 ->
    mcfg_vdraw_sim RR stk env1 env2 t1 t2.
  Proof using.
    apply gen_stack_to_vds_sim.
  Qed.

  Lemma cfg_local_to_vdraw_sim {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 t1 t2 ->
    cfg_vdraw_sim (fun stk' e1' e2' r1 r2 => stk' = stk /\ RR e1' e2' r1 r2)
      stk env1 env2 t1 t2.
  Proof using.
    revert env1 env2 t1 t2; pcofix CIH; intros env1 env2 t1 t2 Hls; pstep; punfold Hls.
    induction Hls as [env1 env2 t1 t2 Hstep
                      | env1 env2 t1 m1 t2 Ht1 _ IH
                      | env1 env2 t1 t2 m2 Ht2 _ IH
                      | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                      | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                      | env1 env2 t1 x v k1 t2 Ht1 _ IH
                      | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply VDS_Step; unfold vds_step_body, cls_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe t2); [split; [reflexivity | exact Hstep] | exact Hstep | exact Hstep].
      + destruct (observe t2); [exact Hstep | pclearbot; right; apply CIH, Hstep | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot; right; apply CIH, HA.
        * right; left.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [| x1]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [| x2]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot; right; apply CIH, Hrd'.
    - eapply VDS_TauL; [exact Ht1 | exact IH].
    - eapply VDS_TauR; [exact Ht2 | exact IH].
    - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply VDS_WriteL; [exact Ht1 | exact IH].
    - eapply VDS_WriteR; [exact Ht2 | exact IH].
  Qed.

  Lemma ruttc_cfg_to_vdraw_sim {R1 R2} (RR : R1 -> R2 -> Prop)
    stk env (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2)
    (Hstk : Forall (fun '(p1, p2) => p1 = p2) stk) :
    @refine_cfg PaV R1 R2 RR t1 t2 ->
    cfg_vdraw_sim
      (fun stk' e1' e2' r1 r2 =>
         Forall (fun '(p1, p2) => p1 = p2) stk' /\ e1' = e2' /\ RR r1 r2)
      stk env env t1 t2.
  Proof using.
    revert stk env Hstk t1 t2; pcofix CIH;
      intros stk env Hstk t1 t2 Hr; pstep; punfold Hr; red in Hr.
    remember (observe t1) as ot1 eqn:Hot1; remember (observe t2) as ot2 eqn:Hot2.
    revert t1 t2 Hot1 Hot2;
      induction Hr as [r1 r2 HR
                       | m1 m2 Hrel
                       | X1 X2 e1 e2 k1 k2 HE HA
                       | m1 ot2_ _ IH
                       | ot1_ m2 _ IH
                       | X1 t1_ k1_ ot2_ Hcut
                       | X2 t2_ k2_ ot1_ Hcut];
      intros t1 t2 Hot1 Hot2.
    - apply VDS_Step; unfold vds_step_body; rewrite <- Hot1, <- Hot2;
        split; [exact Hstk | split; [reflexivity | exact HR]].
    - pclearbot; apply VDS_Step; unfold vds_step_body; rewrite <- Hot1, <- Hot2;
        right; apply CIH; [exact Hstk | exact Hrel].
    - apply VDS_Step; unfold vds_step_body; rewrite <- Hot1, <- Hot2; right.
      destruct (sync_non_local_cfg e1) eqn:Esync.
      + left; split; [exact Esync | split; [exact HE |]].
        intros a1 a2 Ha _; specialize (HA a1 a2 Ha); pclearbot;
          right; apply CIH; [exact Hstk | exact HA].
      + destruct e1 as [c1 | m1], e2 as [c2 | m2];
          cbn in Esync, HE; try discriminate Esync; try contradiction.
        destruct_sum2 m1 m2 HE;
          cbn in Esync, HE; try discriminate Esync; try contradiction.
        * destruct m1 as [x1 v1 | x1], m2 as [x2 v2 | x2]; cbn in HE; try contradiction.
          -- destruct HE as [<- <-]; right; left; cbn; split; [reflexivity | split; [reflexivity |]].
             specialize (HA tt tt Logic.eq_refl); pclearbot;
               right; apply CIH; [exact Hstk | exact HA].
          -- subst x2; right; left; cbn; split; [reflexivity | split; [reflexivity |]].
             intros v _; specialize (HA v v Logic.eq_refl); pclearbot;
               right; apply CIH; [exact Hstk | exact HA].
        * destruct m1 as [bs1 | | |], m2 as [bs2 | | |];
            cbn in Esync, HE; try discriminate Esync; try contradiction.
          -- subst bs2; right; right; cbn.
             specialize (HA tt tt Logic.eq_refl); pclearbot;
               right; apply CIH; [constructor; [reflexivity | exact Hstk] | exact HA].
          -- right; right; cbn; destruct stk as [| [p1 p2] rest]; [exact I |].
             inversion Hstk as [| ? ? Hp Hrest]; subst p2.
             specialize (HA tt tt Logic.eq_refl); pclearbot;
               right; apply CIH; [exact Hrest | exact HA].
    - eapply VDS_TauL; [symmetry; exact Hot1 | apply (IH m1 t2 Logic.eq_refl Hot2)].
    - eapply VDS_TauR; [symmetry; exact Hot2 | apply (IH t1 m2 Hot1 Logic.eq_refl)].
    - apply VDS_Step; unfold vds_step_body; rewrite <- Hot1; left.
      destruct t1_ as [c1 | m1]; [inversion Hcut |].
      destruct_sum1 m1; inversion Hcut; reflexivity.
    - exfalso; inversion Hcut.
  Qed.

End ValueDrawRefinement.
