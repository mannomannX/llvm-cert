(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Inlining Stack-Frame & Global-Env Invariants ([CertPasses.InlineFrameGenv])

    Purpose:
      Establishes nested [dvalue]/[exp] induction principles, fused global
      handler reductions, empty stack-frame memory simulation
      ([handle_memoryM_empty_frame] over [push_empty_frame]), and Hoare
      address-monotonicity invariants for [build_global_environment].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.common.ItreeTactics], [CertPasses.InlineSpec], and
      [CertPasses.InlineSyntaxProof]; zero custom axioms (arbitrary [IPtr]).

    Section Outline:
      (7A) Nested [dvalue]/[exp] induction; (7B) Fused global handler & attr
      reductions; (7C) Empty stack-frame memory simulation; (7D) Address
      monotonicity & [build_global_environment_inline_post]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Strings.Ascii
  List
  Bool
  Morphisms
  RelationClasses
  Lia.
Import ListNotations.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Events.State
  Events.StateFacts
  Eq.Eqit
  Basics.HeterogeneousRelations
  Interp.Recursion
  Interp.TranslateFacts
  Interp.InterpFacts.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
From CertPasses.common Require Import ItreeTactics.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Import InlineSpec InlineSyntaxProof.

(** * 7. Model-Semantics Preliminaries, Empty Memory Frame & Global Environment Invariant *)

Section InliningSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Hint Resolve refine_prov__mon : paco.

  (** ** 7A. Nested Induction Principles for [dvalue] and [exp] *)

  Fixpoint dvalue_ind_nested
    (P : @dvalue PaV -> Prop)
    (Hbase   : forall db, P (DVALUE_Base db))
    (Hstruct : forall pk fs, Forall P fs -> P (DVALUE_Struct pk fs))
    (Harray  : forall vc es, Forall P es -> P (DVALUE_Array vc es))
    (dv : @dvalue PaV) {struct dv} : P dv :=
    let fix list_ind (l : list (@dvalue PaV)) : Forall P l :=
      match l with
      | [] => Forall_nil P
      | x :: xs => Forall_cons x (dvalue_ind_nested P Hbase Hstruct Harray x) (list_ind xs)
      end
    in
    match dv with
    | DVALUE_Base db => Hbase db
    | DVALUE_Struct pk fs => Hstruct pk fs (list_ind fs)
    | DVALUE_Array vc es => Harray vc es (list_ind es)
    end.

  Fixpoint exp_denote_ind {T : Set}
    (P : exp T -> Prop)
    (Hident  : forall id, P (EXP_Ident id))
    (Hint    : forall x, P (EXP_Integer x))
    (Hfloat  : forall f, P (EXP_Float f))
    (Hbool   : forall b, P (EXP_Bool b))
    (Hnull   : P EXP_Null)
    (Hzero   : P EXP_Zero_initializer)
    (Hcstr   : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Cstring es))
    (Hundef  : P EXP_Undef)
    (Hpoison : P EXP_Poison)
    (Hstruct : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Struct es))
    (Hpstr   : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Packed_struct es))
    (Harr    : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Array es))
    (Hvec    : forall es, Forall (fun te => P (snd te)) es -> P (EXP_Vector es))
    (Hibin   : forall iop dt e1 e2, P e1 -> P e2 -> P (OP_IBinop iop dt e1 e2))
    (Hicmp   : forall ss cmp dt e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp dt e1 e2))
    (Hfbin   : forall fop fm dt e1 e2, P e1 -> P e2 -> P (OP_FBinop fop fm dt e1 e2))
    (Hfneg   : forall fm dt e1, P e1 -> P (OP_Fneg fm (dt, e1)))
    (Hfcmp   : forall cmp fm dt e1 e2, P e1 -> P e2 -> P (OP_FCmp cmp fm dt e1 e2))
    (Hconv   : forall ct tf e1 tt0, P e1 -> P (OP_Conversion ct tf e1 tt0))
    (Hgep    : forall fl dt1 dt2 ep idxs,
                 P ep -> Forall (fun te => P (snd te)) idxs ->
                 P (OP_GetElementPtr fl dt1 (dt2, ep) idxs))
    (Hextel  : forall t1 e1 t2 e2, P e1 -> P e2 -> P (OP_ExtractElement (t1, e1) (t2, e2)))
    (Hinsel  : forall t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_InsertElement (t1, e1) (t2, e2) (t3, e3)))
    (Hshuf   : forall t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_ShuffleVector (t1, e1) (t2, e2) (t3, e3)))
    (Hextv   : forall t1 e1 idxs, P e1 -> P (OP_ExtractValue (t1, e1) idxs))
    (Hinsv   : forall t1 e1 t2 e2 idxs,
                 P e1 -> P e2 -> P (OP_InsertValue (t1, e1) (t2, e2) idxs))
    (Hsel    : forall fm t1 e1 t2 e2 t3 e3,
                 P e1 -> P e2 -> P e3 -> P (OP_Select fm (t1, e1) (t2, e2) (t3, e3)))
    (Hfrz    : forall t1 e1, P e1 -> P (OP_Freeze (t1, e1)))
    (Hasm    : forall b1 b2 s1 s2 s3 s4, P (EXP_Asm b1 b2 s1 s2 s3 s4))
    (Hba     : forall f b, P (EXP_BlockAddress f b))
    (Hsplat  : forall t1 e1, P e1 -> P (EXP_Splat (t1, e1)))
    (Hmd_c   : forall t1 e1, P e1 -> P (EXP_Metadata (METADATA_Const (t1, e1))))
    (Hmd_o   : forall md,
                 (forall t1 e1, md <> METADATA_Const (t1, e1)) ->
                 P (EXP_Metadata md))
    (e : exp T) {struct e} : P e :=
    let fix texp_list_ind (l : list (T * exp T)) : Forall (fun te => P (snd te)) l :=
      match l with
      | [] => Forall_nil _
      | (t, ex) :: rest =>
          Forall_cons (t, ex)
            (exp_denote_ind P Hident Hint Hfloat Hbool Hnull Hzero Hcstr Hundef Hpoison
               Hstruct Hpstr Harr Hvec Hibin Hicmp Hfbin Hfneg Hfcmp Hconv Hgep
               Hextel Hinsel Hshuf Hextv Hinsv Hsel Hfrz Hasm Hba Hsplat Hmd_c Hmd_o ex)
            (texp_list_ind rest)
      end
    in
    let rec_e :=
      exp_denote_ind P Hident Hint Hfloat Hbool Hnull Hzero Hcstr Hundef Hpoison
        Hstruct Hpstr Harr Hvec Hibin Hicmp Hfbin Hfneg Hfcmp Hconv Hgep
        Hextel Hinsel Hshuf Hextv Hinsv Hsel Hfrz Hasm Hba Hsplat Hmd_c Hmd_o
    in
    match e with
    | EXP_Ident id => Hident id
    | EXP_Integer x => Hint x
    | EXP_Float f => Hfloat f
    | EXP_Bool b => Hbool b
    | EXP_Null => Hnull
    | EXP_Zero_initializer => Hzero
    | EXP_Cstring es => Hcstr es (texp_list_ind es)
    | EXP_Undef => Hundef
    | EXP_Poison => Hpoison
    | EXP_Struct es => Hstruct es (texp_list_ind es)
    | EXP_Packed_struct es => Hpstr es (texp_list_ind es)
    | EXP_Array es => Harr es (texp_list_ind es)
    | EXP_Vector es => Hvec es (texp_list_ind es)
    | OP_IBinop iop dt e1 e2 => Hibin iop dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_ICmp ss cmp dt e1 e2 => Hicmp ss cmp dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_FBinop fop fm dt e1 e2 => Hfbin fop fm dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_Fneg fm (dt, e1) => Hfneg fm dt e1 (rec_e e1)
    | OP_FCmp cmp fm dt e1 e2 => Hfcmp cmp fm dt e1 e2 (rec_e e1) (rec_e e2)
    | OP_Conversion ct tf e1 tt0 => Hconv ct tf e1 tt0 (rec_e e1)
    | OP_GetElementPtr fl dt1 (dt2, ep) idxs =>
        Hgep fl dt1 dt2 ep idxs (rec_e ep) (texp_list_ind idxs)
    | OP_ExtractElement (t1, e1) (t2, e2) =>
        Hextel t1 e1 t2 e2 (rec_e e1) (rec_e e2)
    | OP_InsertElement (t1, e1) (t2, e2) (t3, e3) =>
        Hinsel t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_ShuffleVector (t1, e1) (t2, e2) (t3, e3) =>
        Hshuf t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_ExtractValue (t1, e1) idxs => Hextv t1 e1 idxs (rec_e e1)
    | OP_InsertValue (t1, e1) (t2, e2) idxs =>
        Hinsv t1 e1 t2 e2 idxs (rec_e e1) (rec_e e2)
    | OP_Select fm (t1, e1) (t2, e2) (t3, e3) =>
        Hsel fm t1 e1 t2 e2 t3 e3 (rec_e e1) (rec_e e2) (rec_e e3)
    | OP_Freeze (t1, e1) => Hfrz t1 e1 (rec_e e1)
    | EXP_Asm b1 b2 s1 s2 s3 s4 => Hasm b1 b2 s1 s2 s3 s4
    | EXP_BlockAddress f b => Hba f b
    | EXP_Splat (t1, e1) => Hsplat t1 e1 (rec_e e1)
    | EXP_Metadata md =>
        match md with
        | METADATA_Const (t1, e1) => Hmd_c t1 e1 (rec_e e1)
        | METADATA_Null => Hmd_o METADATA_Null (fun _ _ H => ltac:(discriminate H))
        | METADATA_Id id => Hmd_o (METADATA_Id id) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Node mds => Hmd_o (METADATA_Node mds) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Pair m1 m2 => Hmd_o (METADATA_Pair m1 m2) (fun _ _ H => ltac:(discriminate H))
        | METADATA_Debug s1 s2 => Hmd_o (METADATA_Debug s1 s2) (fun _ _ H => ltac:(discriminate H))
        | METADATA_File_info fi => Hmd_o (METADATA_File_info fi) (fun _ _ H => ltac:(discriminate H))
        end
    end.

  (** ** 7B. Fused Global Handler, [inl_mrec_ctx], and Attribute Reductions *)

  Lemma fused_global_prov_read_some (k : raw_id) (v : @dvalue PaV) (s : FusedS)
    (Hlk : Maps.lookup k (snd (snd s)) = Some v) :
    fused_global_prov _ (GlobalRead k) s ≅ Ret (s, v).
  Proof using.
    destruct s as [m [ls g]]; cbn [snd] in Hlk.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
    match goal with
    | |- context [lift_bot_prov ?t] =>
        let t' := eval cbn -[Maps.lookup Maps.add raise show globals_set globals_object ITree.bind] in t in
        change t with t'
    end.
    rewrite Hlk.
    rewrite !lift_bot_prov_bind_ret, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma fused_global_prov_read_none (k : raw_id) (s : FusedS)
    (Hlk : Maps.lookup k (snd (snd s)) = None) :
    exists (u : unit) (kf : void -> itree ProvBotE (FusedS * @dvalue PaV)),
      fused_global_prov _ (GlobalRead k) s ≅
      Vis (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (Throw u))))))) kf.
  Proof using.
    destruct s as [m [ls g]]; cbn [snd] in Hlk.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref,
           raise, trigger_cast, ITree.trigger;
      cbn - [Maps.lookup Maps.add lift_bot_prov globals_set globals_object show].
    rewrite Hlk; cbn iota.
    eexists _, _; unfold lift_bot_prov;
      rewrite ?Eqit.bind_vis, translate_vis, ?Eqit.bind_vis;
      norm_subevent;
      reflexivity.
  Qed.

  Lemma fused_global_prov_write (k : raw_id) (v : @dvalue PaV)
    (m : state) (ls : @stack_frame PaV * stack) (g : global_env) :
    fused_global_prov _ (GlobalWrite k v) (m, (ls, g)) ≅
    Ret ((m, (ls, Maps.add k v g)), tt).
  Proof using.
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
    match goal with
    | |- context [lift_bot_prov ?t] =>
        let t' := eval cbn -[Maps.lookup Maps.add raise show globals_set globals_object ITree.bind] in t in
        change t with t'
    end.
    rewrite !lift_bot_prov_bind_ret, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition inl_mrec_ctx
    (fundefs : IntMap (@function_denotation PaV))
    : @CallE PaV ~> @CFGtop PaV :=
    fun T call_ev =>
      match call_ev with
      | Call dt cc fv args =>
          @ExtLib.Structures.Monad.bind (@CFGtop PaV) _ _ _ (EOU_to_itree (check_callee fv))
            (fun _ =>
               match lookup_defn fv fundefs with
               | Some f_den => f_den cc args
               | None => Functor.fmap inr (external_call dt fv args)
               end)
      end.

  Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation PaV))
    (dt : dtyp) (fv : @dvalue PaV) (args : list (@dvalue PaV)) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (inl_mrec_ctx fundefs) (inl_mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  Lemma combine_lists_varargs_exact {A B : Type} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    combine_lists_varargs xs ys = raise_ret (combine xs ys, []).
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [List.length] in Hlen; injection Hlen as Hlen.
      cbn [combine_lists_varargs combine]; rewrite (IH ys' Hlen); reflexivity.
  Qed.

  Lemma init_local_env_lookup_in (bs : list (local_id * @dvalue PaV)) (x : local_id) (v : @dvalue PaV) :
    Maps.lookup x (init_local_env bs) = Some v ->
    In (x, v) bs.
  Proof using.
    unfold local_id in *; induction bs as [| [k dv] rest IH]; cbn [init_local_env fold_right].
    - cbn [Maps.lookup Maps.empty Map_rmap]; rewrite RMF.F.empty_o; discriminate.
    - destruct (RawIDOrd.eq_dec k x) as [-> | Hne].
      + cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_eq_o by reflexivity;
          intros H; injection H as <-; left; reflexivity.
      + cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne;
          intros H; right; apply IH, H.
  Qed.

  Lemma init_local_env_nodup_lookup (xs : list local_id) (ys : list (@dvalue PaV))
    (x : local_id) (v : @dvalue PaV)
    (Hnd : NoDup xs)
    (Hlen : List.length xs = List.length ys)
    (Hin : In (x, v) (combine xs ys)) :
    Maps.lookup x (init_local_env (combine xs ys)) = Some v.
  Proof using.
    unfold local_id in *; revert ys Hlen Hin; induction Hnd as [| a xs' Hnin _ IH];
      intros [| b ys'] Hlen Hin; try discriminate Hlen; [contradiction |].
    cbn [List.length] in Hlen; injection Hlen as Hlen.
    cbn [combine init_local_env fold_right In] in *.
    destruct Hin as [Heq | Hin].
    - injection Heq as -> ->; cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity.
    - assert (Hne : a <> x).
      { intros ->; apply Hnin; eapply in_combine_l; exact Hin. }
      cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      apply (IH ys'); assumption.
  Qed.

  Lemma existsb_false_forall {A : Type} (p : A -> bool) (xs : list A) :
    (forall x, In x xs -> p x = false) ->
    existsb p xs = false.
  Proof using.
    induction xs as [| x xs' IH]; intros H; [reflexivity |].
    cbn [existsb]; rewrite (H x (or_introl Logic.eq_refl)), IH; [reflexivity |].
    intros y Hy; apply H; right; exact Hy.
  Qed.

  Lemma value_attrs_poison_nil (v : @dvalue PaV) :
    value_attrs_poison [] v = v.
  Proof using.
    unfold value_attrs_poison, value_attr_nofpclass, value_attr_range,
           value_attr_align, value_attr_nonnull.
    destruct v as [[p | | | | | | |] | |]; reflexivity.
  Qed.

  Lemma apply_value_attrs_nil (msg : string) (v : @dvalue PaV) :
    apply_value_attrs [] msg v = raise_ret v.
  Proof using.
    unfold apply_value_attrs; rewrite value_attrs_poison_nil; reflexivity.
  Qed.

  Lemma apply_attrs_nil_eq {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (msg : string) (v : @dvalue PaV) :
    apply_attrs (E := E) [] msg v ≅ Ret v.
  Proof using.
    unfold apply_attrs, assert_attrs_dereferenceable; rewrite apply_value_attrs_nil.
    cbn [EOU_to_itree find_option ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma apply_args_attrs_all_nil_eq {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (attrss : list (list param_attr)) (msg : string) (args : list (@dvalue PaV))
    (Hnil : forallb is_empty_list attrss = true) :
    apply_args_attrs (E := E) attrss msg args ≅ Ret args.
  Proof using.
    revert attrss Hnil; induction args as [| v vs IH]; intros attrss Hnil; cbn [apply_args_attrs].
    - reflexivity.
    - destruct attrss as [| a rest].
      + cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l, (IH [] Logic.eq_refl), Eqit.bind_ret_l.
        reflexivity.
      + cbn [forallb] in Hnil; apply andb_prop in Hnil as [Ha Hrest].
        apply is_empty_list_spec in Ha; subst a.
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l, (IH rest Hrest), Eqit.bind_ret_l.
        reflexivity.
  Qed.

  Lemma check_cconv_eq_true (fcc cc : cconv) (fname : string) :
    cconv_eqb cc fcc = true ->
    check_cconv fcc cc fname = raise_ret tt.
  Proof using.
    intros H; unfold check_cconv; rewrite H; reflexivity.
  Qed.

  Lemma check_call_result_safe_inr (fattrs : list fn_attr) (msg : string)
    (args : list (@dvalue PaV)) (v : @dvalue PaV)
    (Hsafe : forallb is_safe_fn_attr fattrs = true) :
    check_call_result fattrs msg args (inr v) = raise_ret tt.
  Proof using.
    unfold check_call_result.
    rewrite forallb_forall in Hsafe.
    assert (Hnr : existsb fn_attr_is_noreturn fattrs = false).
    { apply existsb_false_forall; intros fa Hfa.
      specialize (Hsafe fa Hfa); unfold is_safe_fn_attr in Hsafe.
      apply andb_prop in Hsafe as [H1 _]; apply negb_true_iff in H1; exact H1. }
    assert (Hnc : existsb fn_attr_is_nocreateundeforpoison fattrs = false).
    { apply existsb_false_forall; intros fa Hfa.
      specialize (Hsafe fa Hfa); unfold is_safe_fn_attr in Hsafe.
      apply andb_prop in Hsafe as [_ H2]; apply negb_true_iff in H2; exact H2. }
    rewrite Hnr, Hnc; reflexivity.
  Qed.

  Lemma check_call_return_safe_inr_eq {E}
    `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}
    (fattrs : list fn_attr) (loc : string)
    (args : list (@dvalue PaV)) (v : @dvalue PaV)
    (Hsafe : forallb is_safe_fn_attr fattrs = true) :
    check_call_return (E := E) fattrs [] None loc args (inr v) ≅ Ret (inr v).
  Proof using.
    unfold check_call_return; rewrite (check_call_result_safe_inr fattrs loc args v Hsafe).
    cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l, apply_attrs_nil_eq, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma check_callee_nonnull_ptr (p : @ptr (@PROV PaV) (@PTR PaV))
    (Hnn : (ptr_to_int p > 0)%Z) :
    check_callee (DVALUE_Base (DVALUE_Pointer p)) = raise_ret tt.
  Proof using.
    unfold check_callee.
    assert (Hnull : ptr_to_int (@null (@PROV PaV) (@PTR PaV)) = 0%Z).
    { cbn [ptr_to_int null PointerV fst]; apply to_Z_0. }
    rewrite Hnull.
    destruct (Z.eqb_spec (ptr_to_int p) 0%Z) as [Heq | _]; [lia | reflexivity].
  Qed.

  Lemma intrinsic_exp_global_none (gid : function_id) :
    lookup_intrinsic_declaration gid = None ->
    intrinsic_exp (T := dtyp) (EXP_Ident (ID_Global gid)) = None.
  Proof using.
    intros Hnone; destruct gid as [s | |]; cbn [intrinsic_exp];
      [rewrite Hnone; reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma denote_operand_bundles_nil_eq (loc : string) (f : exp dtyp) :
    @denote_operand_bundles PaV loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma inl_withCall_ret {R : Type} (x : R) :
    @withCall PaV R (Ret x) ≅ Ret x.
  Proof using.
    unfold withCall; apply translate_ret.
  Qed.

  Lemma inl_withCall_bind {A B : Type}
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B) :
    @withCall PaV B (ITree.bind t k) ≅
    ITree.bind (@withCall PaV A t) (fun x => @withCall PaV B (k x)).
  Proof using.
    unfold withCall; apply translate_bind.
  Qed.

  (** ** 7C. Empty Stack-Frame Memory Simulation ([push_empty_frame]) *)

  Definition push_empty_frame (σ : state) : state :=
    {| state_memory_stack :=
         {| Memory_stack_memory      := σ.(state_memory_stack).(Memory_stack_memory);
            Memory_stack_frame_stack := Snoc σ.(state_memory_stack).(Memory_stack_frame_stack) [];
            Memory_stack_heap        := σ.(state_memory_stack).(Memory_stack_heap) |};
       state_provenance := σ.(state_provenance) |}.

  Lemma mempush_empty_frame (σ : state) :
    memM_interp_prov _ (handle_memoryM MemPush) σ = Ret (push_empty_frame σ, tt).
  Proof using.
    reflexivity.
  Qed.

  Lemma mempop_empty_frame (σ : state) :
    memM_interp_prov _ (handle_memoryM MemPop) (push_empty_frame σ) = Ret (σ, tt).
  Proof using.
    destruct σ as [[mem fs hp] pr]; reflexivity.
  Qed.

  Lemma store_zero_struct_noop (varg : @ptr (@PROV PaV) (@PTR PaV)) (σ : state) :
    memM_interp_prov _
      (handle_memoryM
         (Store (DTYPE_Struct true [])
            (DVALUE_Base (DVALUE_Pointer varg))
            (DVALUE_Struct true [])))
      σ = Ret (σ, tt).
  Proof using.
    reflexivity.
  Qed.

  Definition is_callee_sync_mem {X : Type} (me : @MemoryE PaV X) : bool :=
    match me with
    | MemPush => false
    | MemPop => false
    | Alloca dt n al =>
        dtyp_eqb dt (DTYPE_Struct true []) && N.eqb n 1%N &&
        match al with None => true | Some _ => false end
    | Load _ _ => true
    | Store _ _ _ => true
    | Conv _ _ _ _ => true
    end.

  Definition inl_mcfg_event_post {X : Type} (e : @MCFGEtop PaV X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 e1 =>
        match e1 return X -> Prop with
        | inl1 _ => fun _ => True
        | inr1 e2 =>
            match e2 return X -> Prop with
            | inl1 _ => fun _ => True
            | inr1 e3 =>
                match e3 return X -> Prop with
                | inl1 _ => fun _ => True
                | inr1 e4 =>
                    match e4 return X -> Prop with
                    | inl1 me =>
                        match me in MemoryE Y return Y -> Prop with
                        | Alloca _ _ _ =>
                            fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
                        | _ => fun _ => True
                        end
                    | inr1 _ => fun _ => True
                    end
                end
            end
        end
    end a.

  Definition inl_cfg_event_post {X : Type} (e : @CFGEtop PaV X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 m => inl_mcfg_event_post m
    end a.

  Lemma handle_memoryM_inl_post {X : Type} (me : @MemoryE PaV X) :
    memM_all_ret
      (match me in MemoryE Y return Y -> Prop with
       | Alloca _ _ _ => fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
       | _ => fun _ => True
       end)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | t n al | dt a | dt a v | cv tf v tt0]; cbn [handle_memoryM];
      try apply memM_all_ret_true.
    eapply memM_all_ret_bind; [apply memM_all_ret_true |].
    intros p _; exists p; reflexivity.
  Qed.

  (** Relational lift on [memM] relating execution on [push_empty_frame σ] vs [σ]. *)
  Definition memM_rel_empty {X : Type} (P : X -> Prop)
    (m1 m2 : @memM PaV _ X) : Prop :=
    forall (σ : state) (U : list N),
      refine_prov
        (fun _ '(σ1', r1) '(σ2', r2) =>
           σ1' = push_empty_frame σ2' /\ r1 = r2 /\ P r1)
        U
        (memM_interp_prov _ m1 (push_empty_frame σ))
        (memM_interp_prov _ m2 σ).

  Lemma memM_interp_prov_bind_eq {A B : Type}
    (m : @memM PaV _ A) (k : A -> @memM PaV _ B) (σ : state) :
    memM_interp_prov _ (ExtLib.Structures.Monad.bind m k) σ ≅
    ITree.bind (memM_interp_prov _ m σ) (fun '(σ', x) => memM_interp_prov _ (k x) σ').
  Proof using.
    revert σ; induction m as [x | s | s | s | g IH | σ' g IH | c g IH]; intros σ;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - unfold raiseOOM, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - unfold raiseUB, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - unfold raise, trigger_cast; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - apply IH.
    - exact (IH tt σ').
    - destruct c as [sz al | |]; cbn [memM_interp_prov].
      + apply IH.
      + rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros p _ <-; apply IH].
      + apply IH.
  Qed.

  Lemma memM_interp_prov_memS_bind_eq {A B : Type}
    (m : @memM PaV _ A) (k : A -> @memM PaV _ B) (σ : state) :
    memM_interp_prov _ (memS_bind m k) σ ≅
    ITree.bind (memM_interp_prov _ m σ) (fun '(σ', x) => memM_interp_prov _ (k x) σ').
  Proof using.
    apply (@memM_interp_prov_bind_eq A B m k σ).
  Qed.

  Lemma memM_rel_empty_ret {X : Type} (P : X -> Prop) (x : X) (Hx : P x) :
    memM_rel_empty P (ExtLib.Structures.Monad.ret x) (ExtLib.Structures.Monad.ret x).
  Proof using.
    intros σ U; pstep; apply RP_Step; cbn.
    split; [reflexivity | split; [reflexivity | exact Hx]].
  Qed.

  Lemma memM_rel_empty_bind {X Y : Type} (P : X -> Prop) (Q : Y -> Prop)
    (m1 m2 : @memM PaV _ X)
    (f1 f2 : X -> @memM PaV _ Y)
    (Hm : memM_rel_empty P m1 m2)
    (Hf : forall x, P x -> memM_rel_empty Q (f1 x) (f2 x)) :
    memM_rel_empty Q (ExtLib.Structures.Monad.bind m1 f1) (ExtLib.Structures.Monad.bind m2 f2).
  Proof using.
    intros σ U.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind_eq
      | symmetry; apply memM_interp_prov_bind_eq |].
    eapply refine_prov_bind; [apply Hm |].
    intros U' [σ1' x1] [σ2' x2] _ (-> & <- & Hx).
    apply (Hf x1 Hx).
  Qed.

  Lemma memM_rel_empty_lift {X : Type} (e : EOU X) :
    memM_rel_empty (fun _ => True)
      (Vellvm.Semantics.Interfaces.Memory.lift e)
      (Vellvm.Semantics.Interfaces.Memory.lift e).
  Proof using.
    intros σ U; destruct e as [s | s | s | x]; cbn.
    - unfold raise, trigger_cast, ITree.trigger; pstep; apply RP_Step; cbn;
        right; right; split; [exact I | intros [] [] _].
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        cbn; left; reflexivity.
    - pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma memM_rel_empty_mub {X : Type} (P : X -> Prop) (msg : string) :
    memM_rel_empty P (mub msg) (mub msg).
  Proof using.
    intros σ U; cbn; unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply RP_Step; cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_merr {X : Type} (P : X -> Prop) (msg : string) :
    memM_rel_empty P (merr msg) (merr msg).
  Proof using.
    intros σ U; cbn; unfold raise, trigger_cast, ITree.trigger.
    pstep; apply RP_Step; cbn;
      right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma memM_rel_empty_read_byte (p : @ptr (@PROV PaV) (@PTR PaV)) :
    memM_rel_empty (fun _ => True) (read_byte p) (read_byte p).
  Proof using.
    intros σ U; cbn [read_byte MemoryModelPrimitivesV].
    unfold Read_byte, read_byte_raw, get;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
           state_get_memory MemoryModelStateV push_empty_frame state_memory_stack Memory_stack_memory].
    destruct (read_byte_raw_mem (Memory_stack_memory (state_memory_stack σ)) (ptr_to_int p))
      as [[b aid] |]; cbn [memS_bind memM_interp_prov].
    - destruct (access_allowed (ptr_provenance p) aid); cbn [memM_interp_prov].
      + pstep; apply RP_Step; cbn; auto.
      + unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
          cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_write_byte (p : @ptr (@PROV PaV) (@PTR PaV)) (mb : @memory_byte PaV) :
    memM_rel_empty (fun _ => True) (write_byte p mb) (write_byte p mb).
  Proof using.
    intros σ U; cbn [write_byte MemoryModelPrimitivesV].
    unfold Write_byte, read_byte_raw, set_byte_raw, get_mem, upd_mem, app_mem, get, put;
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
           state_get_memory MemoryModelStateV push_empty_frame
           state_memory_stack Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap state_provenance].
    destruct (read_byte_raw_mem (Memory_stack_memory (state_memory_stack σ)) (ptr_to_int p))
      as [[b aid] |]; cbn [memS_bind memM_interp_prov].
    - destruct (access_allowed (ptr_provenance p) aid); cbn [memM_interp_prov].
      + pstep; apply RP_Step; cbn;
          unfold push_empty_frame; cbn; auto.
      + unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
          cbn; left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        cbn; left; reflexivity.
  Qed.

  Lemma memM_rel_empty_map_monad_acc {A B : Type} (f : A -> @memM PaV _ B) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (map_monad_acc f xs) (map_monad_acc f xs).
  Proof using.
    unfold map_monad_acc.
    assert (Hgo :
      forall (ys : list A) (acc : list B),
        memM_rel_empty (fun _ => True)
          ((fix loop (acc0 : list B) (l : list A) : @memM PaV _ (list B) :=
              match l with
              | [] => ExtLib.Structures.Monad.ret (rev_append acc0 [])
              | a :: l' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc0) l')
              end) acc ys)
          ((fix loop (acc0 : list B) (l : list A) : @memM PaV _ (list B) :=
              match l with
              | [] => ExtLib.Structures.Monad.ret (rev_append acc0 [])
              | a :: l' => ExtLib.Structures.Monad.bind (f a) (fun b => loop (b :: acc0) l')
              end) acc ys)).
    { induction ys as [| a ys' IH]; intros acc.
      - apply memM_rel_empty_ret, I.
      - eapply memM_rel_empty_bind; [apply Hf | intros b _; apply IH]. }
    apply Hgo.
  Qed.

  Lemma memM_rel_empty_map_monad {A B : Type} (f : A -> @memM PaV _ B) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (map_monad f xs) (map_monad f xs).
  Proof using.
    induction xs as [| a xs' IH]; cbn [map_monad].
    - apply memM_rel_empty_ret, I.
    - eapply memM_rel_empty_bind; [apply Hf | intros b _].
      eapply memM_rel_empty_bind; [exact IH | intros bs _; apply memM_rel_empty_ret, I].
  Qed.

  Lemma memM_rel_empty_loop_monad {A : Type} (f : A -> @memM PaV _ unit) (xs : list A)
    (Hf : forall a, memM_rel_empty (fun _ => True) (f a) (f a)) :
    memM_rel_empty (fun _ => True) (loop_monad f xs) (loop_monad f xs).
  Proof using.
    induction xs as [| a xs' IH]; cbn [loop_monad].
    - apply memM_rel_empty_ret, I.
    - eapply memM_rel_empty_bind; [apply Hf | intros [] _; exact IH].
  Qed.

  Lemma memM_rel_empty_convert_impure_base
    (ct : impure_conversion) (tf : dtyp_base) (dv : @dvalue_base PaV) (tt0 : dtyp_base) :
    memM_rel_empty (fun _ => True)
      (convert_impure_base ct tf dv tt0)
      (convert_impure_base ct tf dv tt0).
  Proof using.
    unfold convert_impure_base.
    destruct ct.
    - eapply memM_rel_empty_bind with (P := fun _ => True).
      + unfold assert_inttoptr_types_ok;
          destruct tf, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_ret, I.
      + intros [] _; destruct dv; apply memM_rel_empty_lift.
    - destruct dv, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_lift.
    - destruct dv, tt0; try apply memM_rel_empty_mub; apply memM_rel_empty_lift.
    - apply memM_rel_empty_merr.
  Qed.

  Lemma memM_rel_empty_zero_alloca :
    memM_rel_empty
      (fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p))
      (handle_memoryM (Alloca (DTYPE_Struct true []) 1%N None))
      (handle_memoryM (Alloca (DTYPE_Struct true []) 1%N None)).
  Proof using.
    cbn [handle_memoryM]; unfold allocate_dtyp.
    change (dtyp_eqb (DTYPE_Struct true []) DTYPE_Void) with false.
    change (concat_acc (repeatN 1%N (generate_poison_bytes (DTYPE_Struct true []))))
      with ([] : list (@memory_byte PaV)).
    set (al := preferred_alignment (dtyp_alignment (DTYPE_Struct true []))).
    eapply memM_rel_empty_bind with (P := fun _ => True);
      [| intros p _; apply memM_rel_empty_ret; exists p; reflexivity].
    intros σ U.
    unfold allocate_bytes, fresh_prov, Mfresh_prov; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
    right; right; intros pr _.
    left; eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    change {| state_memory_stack := state_memory_stack (push_empty_frame σ);
              state_provenance   := pr |}
      with (push_empty_frame {| state_memory_stack := state_memory_stack σ;
                                state_provenance   := pr |}).
    set (σ' := {| state_memory_stack := state_memory_stack σ; state_provenance := pr |}).
    unfold Allocate_bytes_with_pr; cbv zeta;
      repeat match goal with
      | |- context [memory_bytes_to_bytes ?a []] =>
          replace (memory_bytes_to_bytes a []) with ([] : list byte)
            by (unfold memory_bytes_to_bytes; rewrite map_acc_eq; reflexivity)
      end;
      try change (N.length ([] : list (@memory_byte PaV))) with 0%N;
      try change (N.length ([] : list byte)) with 0%N.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind_eq
      | symmetry; apply memM_interp_prov_bind_eq |].
    eapply refine_prov_bind with
      (RR := fun _ '(σ1', x1) '(σ2', x2) =>
               σ1' = push_empty_frame σ2' /\ x1 = x2 /\ snd x1 = []).
    - unfold get_free_block, next_key, Mnext_key.
      cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind
           Vellvm.Semantics.Interfaces.Memory.lift EOU_monad
           ExtLib.Structures.Monad.ret memM_interp_prov
           push_empty_frame state_memory_stack Memory_stack_memory].
      match goal with
      | |- context [from_Z ?z] =>
          destruct (from_Z z) as [s | s | s | ip_a] eqn:Ept
      end;
        cbn [Vellvm.Semantics.Interfaces.Memory.lift EOU_monad
             ExtLib.Structures.Monad.bind memS_mon memS_bind
             ExtLib.Structures.Monad.ret memM_interp_prov].
      + unfold raise, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite ?observe_bind;
          unfold subevent, resum;
          cbn [observe match_vis_both is_ub_prov is_ub_bot
               ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
          unfold resum, ReSum_id, id_, Id_IFun;
          right; right; split; [first [exact I | reflexivity | apply EqE_bot_refl] | intros [] [] _].
      + unfold raiseOOM, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite ?observe_bind;
          unfold subevent, resum;
          cbn [observe is_ub_prov is_ub_bot
               ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
          unfold resum, ReSum_id, id_, Id_IFun;
          left; reflexivity.
      + unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite ?observe_bind;
          unfold subevent, resum;
          cbn [observe is_ub_prov is_ub_bot
               ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
          unfold resum, ReSum_id, id_, Id_IFun;
          left; reflexivity.
      + assert (Hptrs : forall pt0 n0, n0 = 0%N ->
          get_consecutive_ptrs pt0 n0 = @raise_ret (list (@ptr (@PROV PaV) (@PTR PaV))) []).
        { intros pt0 n0 ->; unfold get_consecutive_ptrs, intptr_seq.
          rewrite N_to_nat_safe_eq, seq_map_monad_acc_eq.
          cbn; reflexivity. }
        repeat match goal with
        | |- context [get_consecutive_ptrs ?pt0 ?n0] =>
            erewrite (Hptrs pt0 n0)
              by (try (unfold memory_bytes_to_bytes; rewrite map_acc_eq); cbn; reflexivity)
        end;
        try (unfold get_consecutive_ptrs, intptr_seq;
             rewrite ?N_to_nat_safe_eq, ?seq_map_monad_acc_eq).
        cbn [Vellvm.Semantics.Interfaces.Memory.lift EOU_monad ExtLib.Structures.Monad.bind
             memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
             N_to_nat_safe N.to_nat seq_map_monad_acc map_monad map_monad_acc Nseq rev_append app].
        pstep; apply RP_Step; cbn; auto.
    - intros U1 [σ1' [p1 ptrs1]] [σ2' [p2 ptrs2]] _ (-> & Heq & Hptrs).
      cbn [snd] in Hptrs; subst ptrs1; injection Heq as <- <-.
      unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem,
             app_mem_stack, get, put.
      destruct σ2' as [[mem0 fs0 hp0] pr0].
      try replace (memory_bytes_to_bytes (provenance_to_allocation_id pr) [])
        with ([] : list byte)
        by (unfold memory_bytes_to_bytes; rewrite map_acc_eq; reflexivity).
      cbn [add_all_index_acc add_all_to_frame fold_left ExtLib.Structures.Monad.bind
           memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
           push_empty_frame state_get_memory MemoryModelStateV state_memory_stack
           Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap state_provenance].
      pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma handle_memoryM_empty_frame {X : Type} (me : @MemoryE PaV X)
    (Hok : is_callee_sync_mem me = true) :
    memM_rel_empty
      (match me in MemoryE Y return Y -> Prop with
       | Alloca _ _ _ => fun dv => exists p, dv = DVALUE_Base (DVALUE_Pointer p)
       | _ => fun _ => True
       end)
      (handle_memoryM me)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | dt n al | dt a | dt a v | ct tf v tt0];
      try discriminate Hok.
    - cbn [is_callee_sync_mem] in Hok.
      apply andb_prop in Hok as [Hok Hal].
      apply andb_prop in Hok as [Hdt Hn].
      apply dtyp_eqb_eq in Hdt; apply N.eqb_eq in Hn.
      destruct al; [discriminate Hal |].
      subst dt n; apply memM_rel_empty_zero_alloca.
    - cbn [handle_memoryM].
      destruct a as [[p | | | | | | |] | |]; try apply memM_rel_empty_mub.
      unfold read_dvalue, read_bytes.
      eapply memM_rel_empty_bind.
      + eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
        intros ptrs _; apply memM_rel_empty_map_monad_acc, memM_rel_empty_read_byte.
      + intros bytes _; apply memM_rel_empty_lift.
    - cbn [handle_memoryM].
      destruct a as [[p | | | | | | |] | |]; try apply memM_rel_empty_mub.
      unfold write_dvalue, write_bytes.
      eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
      intros bytes _.
      eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
      intros ptrs _.
      apply memM_rel_empty_loop_monad.
      intros [p' mb]; apply memM_rel_empty_write_byte.
    - cbn [handle_memoryM]; unfold convert_impure.
      destruct v as [db | pk fs | vc es]; try apply memM_rel_empty_merr.
      + destruct (get_base_conversion_type tf tt0) as [[tf' tt'] |]; [| apply memM_rel_empty_merr].
        cbn [Functor.fmap Functor_Monad].
        eapply memM_rel_empty_bind; [apply memM_rel_empty_convert_impure_base |].
        intros db' _; apply memM_rel_empty_ret, I.
      + destruct vc; [| apply memM_rel_empty_merr].
        destruct (get_vector_conversion_type tf tt0) as [[tf' tt'] |]; [| apply memM_rel_empty_merr].
        eapply memM_rel_empty_bind; [apply memM_rel_empty_lift |].
        intros es' _.
        eapply memM_rel_empty_bind.
        * apply memM_rel_empty_map_monad; intros db'; apply memM_rel_empty_convert_impure_base.
        * intros val _; apply memM_rel_empty_ret, I.
  Qed.

  (** ** 7D. Address Monotonicity & [build_global_environment] Hoare Postcondition *)

  Lemma next_key_with_alignment_ge_1 {A : Type} (m : IntMap A) (align : N) :
    (next_key_with_alignment m align >= 1)%Z.
  Proof using.
    unfold next_key_with_alignment, Vellvm.Semantics.Handlers.Memory.pad_to.
    destruct (IM_greatest_key m) as [gk |]; lia.
  Qed.

  Lemma next_key_with_alignment_gt_in {A : Type} (m : IntMap A) (align : N) (k : Z) :
    IM.In k m ->
    (k < next_key_with_alignment m align)%Z.
  Proof using.
    intros Hin.
    destruct (IM_greatest_key_In' m k Hin) as [gk Hgk].
    pose proof (IM_greatest_key_lt m gk Hgk) as Hlt.
    unfold IM.In in Hin; apply IM.Raw.Proofs.In_alt in Hin.
    red in Hlt; specialize (Hlt k Hin); unfold IM.E.lt in Hlt.
    unfold next_key_with_alignment, Vellvm.Semantics.Handlers.Memory.pad_to.
    rewrite Hgk.
    destruct (Z_le_gt_dec 0 gk) as [Hpos | Hneg].
    - assert (Hz : Z.of_N (1 + Z.to_N gk)%N = (1 + gk)%Z) by (rewrite N2Z.inj_add, Z2N.id; lia).
      lia.
    - assert (Hz : Z.to_N gk = 0%N) by lia.
      rewrite Hz; lia.
  Qed.

  Lemma IM_In_add_all_index_acc {A : Type} (vs : list A) (base k : Z) (m : IntMap A) :
    (IM.In k m \/ (base <= k < base + Z.of_nat (List.length vs))%Z) ->
    IM.In k (add_all_index_acc vs base m).
  Proof using.
    revert base m; induction vs as [| v tl IH]; intros base m Hk; cbn [add_all_index_acc List.length] in *.
    - destruct Hk as [Hin | [Hle Hlt]];
        [ exact Hin
        | cbn [Z.of_nat] in Hlt; rewrite Z.add_0_r in Hlt;
          exfalso; exact (Z.lt_irrefl _ (Z.le_lt_trans _ _ _ Hle Hlt)) ].
    - apply IH.
      destruct Hk as [Hin | [Hle Hlt]].
      + left; unfold add; apply IntMaps.IP.F.add_in_iff; right; exact Hin.
      + destruct (Z.eq_dec k base) as [-> | Hne].
        * left; unfold add; apply IntMaps.IP.F.add_in_iff; left; reflexivity.
        * right; rewrite Nat2Z.inj_succ in Hlt; unfold Z.succ in Hlt; split; lia.
  Qed.

  Definition model_hoare {R : Type} (P : FusedS -> Prop) (u : @MCFGtop PaV R)
    (Q : FusedS -> R -> Prop) : Prop :=
    forall (s : FusedS) (U : list N),
      P s ->
      refine_prov
        (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ r1 = r2 /\ Q s1 r1)
        U (interp_mcfg_model u s) (interp_mcfg_model u s).

  Lemma interp_mcfg_model_ret_eq {R : Type} (x : R) (s : FusedS) :
    interp_mcfg_model (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_mcfg_model_bind_eq {A B : Type}
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B) (s : FusedS) :
    interp_mcfg_model (ITree.bind t k) s ≅
    ITree.bind (interp_mcfg_model t s) (fun '(s', x) => interp_mcfg_model (k x) s').
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_bind, interp_state_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq);
      [reflexivity | intros [s' x] _ <-; reflexivity].
  Qed.

  Lemma interp_mcfg_model_non_intr_eq {X : Type}
    (me : @MCFGEtop PaV X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_mcfg_model (ITree.trigger me) s ≅
    ITree.bind (interp_vellvm_prov_h _ me s)
      (fun '(s', x) => Tau (Tau (Ret (s', x)))).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics, ITree.trigger.
    rewrite interp_vis, Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, interp_state_tau, interp_ret, interp_state_ret.
    reflexivity.
  Qed.

  Lemma model_hoare_ret {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (x : R)
    (Hx : forall s, P s -> Q s x) :
    model_hoare P (Ret x) Q.
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret_eq
      | symmetry; apply interp_mcfg_model_ret_eq |].
    pstep; apply RP_Step; cbn;
      split; [reflexivity | split; [reflexivity | apply Hx, Hs]].
  Qed.

  Lemma model_hoare_bind {A B : Type}
    (P : FusedS -> Prop) (Q : FusedS -> A -> Prop) (R : FusedS -> B -> Prop)
    (t : @MCFGtop PaV A) (k : A -> @MCFGtop PaV B)
    (Ht : model_hoare P t Q)
    (Hk : forall a, model_hoare (fun s => Q s a) (k a) R) :
    model_hoare P (ITree.bind t k) R.
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq
      | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_bind; [apply Ht, Hs |].
    intros U' [s1 a1] [s2 a2] _ (-> & <- & HQ).
    apply (Hk a1 s2 U' HQ).
  Qed.

  Lemma model_hoare_weaken {R : Type}
    (P P' : FusedS -> Prop) (Q Q' : FusedS -> R -> Prop)
    (u : @MCFGtop PaV R)
    (HP : forall s, P' s -> P s)
    (HQ : forall s r, Q s r -> Q' s r)
    (Hu : model_hoare P u Q) :
    model_hoare P' u Q'.
  Proof using.
    intros s U Hs.
    eapply refine_prov_antitone with (U := U); [| apply incl_refl | apply Hu, HP, Hs].
    intros _ _ [s1 r1] [s2 r2] _ (-> & <- & Hq).
    split; [reflexivity | split; [reflexivity | apply HQ, Hq]].
  Qed.

  Lemma model_hoare_loop_monad {A : Type} (I : FusedS -> Prop)
    (f : A -> @MCFGtop PaV unit) (xs : list A)
    (Hf : forall x, In x xs -> model_hoare I (f x) (fun s' _ => I s')) :
    model_hoare I (loop_monad f xs) (fun s' _ => I s').
  Proof using.
    induction xs as [| x xs' IH]; cbn [loop_monad].
    - apply model_hoare_ret; intros s Hs; exact Hs.
    - eapply model_hoare_bind; [apply (Hf x (or_introl Logic.eq_refl)) |].
      intros []; apply IH; intros y Hy;
        apply Hf; right; exact Hy.
  Qed.

  Lemma model_hoare_map_monad {A B : Type} (I : FusedS -> Prop)
    (f : A -> @MCFGtop PaV B) (xs : list A)
    (Hf : forall x, In x xs -> model_hoare I (f x) (fun s' _ => I s')) :
    model_hoare I (map_monad f xs) (fun s' _ => I s').
  Proof using.
    induction xs as [| x xs' IH]; cbn [map_monad].
    - apply model_hoare_ret; intros s Hs; exact Hs.
    - eapply model_hoare_bind; [apply (Hf x (or_introl Logic.eq_refl)) |].
      intros b; eapply model_hoare_bind.
      + apply IH; intros y Hy; apply Hf; right; exact Hy.
      + intros bs; apply model_hoare_ret; intros s Hs; exact Hs.
  Qed.

  Lemma model_hoare_raise {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raise msg) Q.
  Proof using.
    intros s U _; unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | symmetry; apply interp_mcfg_model_bind_eq |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite interp_mcfg_model_non_intr_eq by reflexivity; reflexivity
      | symmetry; rewrite interp_mcfg_model_non_intr_eq by reflexivity; reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
    right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma model_hoare_raiseUB {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raiseUB msg) Q.
  Proof using.
    intros s U _; unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite interp_mcfg_model_non_intr_eq by reflexivity; reflexivity
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body;
      rewrite !observe_bind; cbn; left; reflexivity.
  Qed.

  Lemma model_hoare_raiseOOM {R : Type} (P : FusedS -> Prop) (Q : FusedS -> R -> Prop) (msg : string) :
    model_hoare P (raiseOOM msg) Q.
  Proof using.
    intros s U _; unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind_eq | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite interp_mcfg_model_non_intr_eq by reflexivity; reflexivity
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    pstep; apply RP_Step; unfold rp_step_body;
      rewrite !observe_bind; cbn; left; reflexivity.
  Qed.

  Lemma model_hoare_EOU {A : Type} (I : FusedS -> Prop) (m : EOU A) :
    model_hoare I (EOU_to_itree m) (fun s' _ => I s').
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply model_hoare_raise.
    - apply model_hoare_raiseOOM.
    - apply model_hoare_raiseUB.
    - apply model_hoare_ret; intros s Hs; exact Hs.
  Qed.

  Lemma refine_prov_tau2_ret {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (r1 : R1) (r2 : R2) (H : RR U r1 r2) :
    refine_prov RR U (Tau (Tau (Ret r1))) (Tau (Tau (Ret r2))).
  Proof using.
    pstep; eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |].
    eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |].
    apply RP_Step; cbn; exact H.
  Qed.

  Lemma model_hoare_non_intr_refl_preserve {X : Type}
    (I : FusedS -> Prop) (me : @MCFGEtop PaV X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hpres : forall s U,
               I s ->
               refine_prov
                 (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ r1 = r2 /\ I s1)
                 U (interp_vellvm_prov_h _ me s) (interp_vellvm_prov_h _ me s)) :
    model_hoare I (ITree.trigger me) (fun s' _ => I s').
  Proof using.
    intros s U Hs.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq, Hni
      | symmetry; apply interp_mcfg_model_non_intr_eq, Hni |].
    eapply refine_prov_bind; [apply Hpres, Hs |].
    intros U' [s1 r1] [s2 r2] _ (-> & <- & HI).
    apply refine_prov_tau2_ret; auto.
  Qed.

  Lemma model_hoare_memory_lsg_preserve {X : Type}
    (I : FusedS -> Prop) (me : @MemoryE PaV X)
    (Hlsg : forall m m' lsg, I (m, lsg) -> I (m', lsg)) :
    model_hoare I (ITree.trigger (subevent _ me)) (fun s' _ => I s').
  Proof using.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros [m lsg] U HI.
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    try change (resum IFun X me) with me.
    eapply refine_prov_bind;
      [apply (memM_interp_prov_post (fun _ => True)); apply memM_all_ret_true |].
    intros U' [m1 r1] [m2 r2] _ (-> & <- & _).
    pstep; apply RP_Step; cbn;
      split; [reflexivity | split; [reflexivity | eapply Hlsg, HI]].
  Qed.

  Lemma model_hoare_gread_preserve (I : FusedS -> Prop) (k : raw_id) :
    model_hoare I (gread k) (fun s' _ => I s').
  Proof using.
    unfold gread, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros s U HI.
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try change (resum IFun (@dvalue PaV) (GlobalRead k)) with (GlobalRead k).
    destruct (Maps.lookup k (snd (snd s))) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; apply (fused_global_prov_read_some k v s Elk)
        | symmetry; apply (fused_global_prov_read_some k v s Elk) |].
      pstep; apply RP_Step; cbn; auto.
    - destruct (fused_global_prov_read_none k s Elk) as (u & kf & Ef).
      eapply refine_prov_obs_eq; [symmetry; exact Ef | symmetry; exact Ef |].
      pstep; apply RP_Step; cbn;
        right; right; split; [exact Logic.I | intros [] [] _].
  Qed.

  Lemma model_hoare_lread_preserve (I : FusedS -> Prop) (k : raw_id) :
    model_hoare I (lread k) (fun s' _ => I s').
  Proof using.
    unfold lread, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros [m [[sf fstk] g]] U HI.
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try change (resum IFun (@dvalue PaV) (LocalRead k)) with (LocalRead k).
    destruct (Maps.lookup k sf.(stack_vars)) as [v |] eqn:Elk.
    - eapply refine_prov_obs_eq;
        [symmetry; apply (fused_local_prov_read_some k v (m, ((sf, fstk), g)) Elk)
        | symmetry; apply (fused_local_prov_read_some k v (m, ((sf, fstk), g)) Elk) |].
      pstep; apply RP_Step; cbn; auto.
    - destruct (fused_local_prov_read_none k (m, ((sf, fstk), g)) Elk) as (msg & kf & Ef).
      eapply refine_prov_obs_eq; [symmetry; exact Ef | symmetry; exact Ef |].
      pstep; apply RP_Step; cbn;
        right; right; split; [exact Logic.I | intros [] [] _].
  Qed.

  Lemma model_hoare_draw_preserve (I : FusedS -> Prop) (dt : dtyp) :
    model_hoare I (draw dt) (fun s' _ => I s').
  Proof using.
    unfold draw, trigger_cast.
    apply model_hoare_non_intr_refl_preserve; [reflexivity |].
    intros s U HI.
    norm_subevent;
    unfold interp_vellvm_prov_h, case_, Case_sum1, case_sum1,
           Case_sum1_Handler, Handler.case_, fused_draw_prov, handle_draw;
    norm_subevent;
    lazymatch goal with
    | |- context [default_dvalue_of_dtyp ?dt'] =>
        destruct (default_dvalue_of_dtyp dt') as [msg | msg | msg | dv]
    end;
      cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
    - unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        norm_subevent;
        cbn [match_vis_both is_ub_prov is_ub_bot observe];
        right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
    - unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        norm_subevent;
        cbn [observe is_ub_prov is_ub_bot];
        left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
        norm_subevent;
        cbn [observe is_ub_prov is_ub_bot];
        left; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
      pstep; apply RP_Step; cbn; auto.
  Qed.

  Lemma model_hoare_gwrite (P : FusedS -> Prop) (k : raw_id) (v : @dvalue PaV)
    (Q : FusedS -> unit -> Prop)
    (HQ : forall m ls g, P (m, (ls, g)) -> Q (m, (ls, Maps.add k v g)) tt) :
    model_hoare P (gwrite k v) Q.
  Proof using.
    intros [m [ls g]] U HP.
    unfold gwrite, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    try change (resum IFun unit (GlobalWrite k v)) with (GlobalWrite k v).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite fused_global_prov_write, Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite fused_global_prov_write, Eqit.bind_ret_l; reflexivity |].
    apply refine_prov_tau2_ret; split; [reflexivity | split; [reflexivity | apply HQ, HP]].
  Qed.

  Lemma model_hoare_freeze_preserve (I : FusedS -> Prop) (dv : @dvalue PaV) :
    forall dt : dtyp,
      model_hoare I (freeze dt dv) (fun s' _ => I s').
  Proof using.
    induction dv as [db | pk fs IHfs | vc es IHes] using dvalue_ind_nested; intros dt;
      unfold freeze.
    - assert (Hfmap_ret :
        forall (b : @dvalue_base PaV),
          model_hoare I (Functor.fmap DVALUE_Base (ExtLib.Structures.Monad.ret b)) (fun s' _ => I s')).
      { intros b.
        unfold Functor.fmap, Functor_itree, ITree.map; try unfold Functor_Monad.
        first [apply model_hoare_ret; intros s Hs; exact Hs
              | eapply model_hoare_bind;
                [first [apply model_hoare_ret; intros s Hs; exact Hs
                       | unfold ExtLib.Structures.Monad.ret, Monad_itree;
                         apply model_hoare_ret; intros s Hs; exact Hs]
                | intros ?;
                  first [apply model_hoare_ret; intros s Hs; exact Hs
                        | unfold ExtLib.Structures.Monad.ret, Monad_itree;
                          apply model_hoare_ret; intros s Hs; exact Hs]]]. }
      destruct db as [| | | | | | | sz bv]; unfold freeze_base;
        try first [apply Hfmap_ret | apply model_hoare_ret; intros s Hs; exact Hs].
      + apply model_hoare_draw_preserve.
      + destruct bv as [| | bits];
          try first [apply Hfmap_ret | apply model_hoare_ret; intros s Hs; exact Hs].
        destruct (existsb is_poison_bit bits).
        * eapply model_hoare_bind; [apply model_hoare_draw_preserve |].
          intros x; apply model_hoare_ret; intros s Hs; exact Hs.
        * first [apply Hfmap_ret | apply model_hoare_ret; intros s Hs; exact Hs].
    - destruct dt as [| p dts |]; cbv beta iota zeta;
        lazymatch goal with
        | |- model_hoare _ (raise _) _ => apply model_hoare_raise
        | _ => idtac
        end.
      eapply model_hoare_bind; [| intros val; apply model_hoare_ret; intros s Hs; exact Hs].
      lazymatch goal with
      | |- model_hoare ?I0 (?go fs dts []) ?Q0 =>
          cut (forall acc : list (@dvalue PaV), model_hoare I0 (go fs dts acc) Q0);
            [intros Hcut; exact (Hcut []) |]
      end.
      revert dts;
      induction IHfs as [| f fs' Hf _ IH]; intros [| t ts] acc; cbv beta iota zeta;
        lazymatch goal with
        | |- model_hoare _ (raise _) _ => apply model_hoare_raise
        | _ => idtac
        end.
      + apply model_hoare_ret; intros s Hs; exact Hs.
      + eapply model_hoare_bind; [apply (Hf t) | intros v; apply IH].
    - destruct dt as [| | v sz t]; cbv beta iota zeta;
        lazymatch goal with
        | |- model_hoare _ (raise _) _ => apply model_hoare_raise
        | _ => idtac
        end.
      eapply model_hoare_bind; [| intros val; apply model_hoare_ret; intros s Hs; exact Hs].
      lazymatch goal with
      | |- model_hoare ?I0 (?go es []) ?Q0 =>
          cut (forall acc : list (@dvalue PaV), model_hoare I0 (go es acc) Q0);
            [intros Hcut; exact (Hcut []) |]
      end.
      induction IHes as [| e es' He _ IH]; intros acc.
      + apply model_hoare_ret; intros s Hs; exact Hs.
      + eapply model_hoare_bind; [apply (He t) | intros v'; apply IH].
  Qed.

  Lemma model_hoare_denote_exp_lsg_preserve (I : FusedS -> Prop)
    (Hlsg : forall m m' lsg, I (m, lsg) -> I (m', lsg))
    (e : exp dtyp) :
    forall top : option dtyp,
      model_hoare I (denote_exp top e) (fun s' _ => I s').
  Proof using.
    induction e using exp_denote_ind; intros top; cbn [denote_exp];
      try (apply model_hoare_ret; intros s Hs; exact Hs);
      lazymatch goal with
      | |- model_hoare _ (raise _) _ => apply model_hoare_raise
      | |- model_hoare _ (match top with Some _ => _ | None => _ end) _ =>
          destruct top; [apply model_hoare_EOU | apply model_hoare_raise]
      | _ => idtac
      end.
    - (* EXP_Ident *)
      destruct id as [gid | lid]; [apply model_hoare_gread_preserve | apply model_hoare_lread_preserve].
    - (* EXP_Bool *)
      destruct b; apply model_hoare_ret; intros s Hs; exact Hs.
    - (* EXP_Cstring *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_ret; auto].
    - (* EXP_Struct *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_ret; auto].
    - (* EXP_Packed_struct *)
      eapply model_hoare_bind; [apply model_hoare_EOU | intros u0].
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_ret; auto].
    - (* EXP_Array *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_ret; auto].
    - (* EXP_Vector *)
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_ret; auto].
    - (* OP_IBinop *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_ICmp *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_FBinop *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_Fneg *)
      eapply model_hoare_bind; [apply IHe | intros v1; apply model_hoare_EOU].
    - (* OP_FCmp *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_Conversion *)
      eapply model_hoare_bind; [apply IHe | intros dv].
      unfold convert; destruct ct as [| pct | ict].
      + destruct (dtyp_eqb tf tt0); [apply model_hoare_ret; auto |].
        destruct (bit_sizeof_dtyp tf =? bit_sizeof_dtyp tt0)%N;
          [apply model_hoare_EOU | apply model_hoare_raise].
      + apply model_hoare_EOU.
      + unfold conv; apply (model_hoare_memory_lsg_preserve I _ Hlsg).
    - (* OP_GetElementPtr *)
      eapply model_hoare_bind; [apply IHe | intros vp].
      eapply model_hoare_bind;
        [apply model_hoare_map_monad; intros [t ex] Hin;
         rewrite Forall_forall in H; exact (H (t, ex) Hin (Some t))
        | intros vs; apply model_hoare_EOU].
    - (* OP_ExtractElement *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_InsertElement *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU] | intros b2].
      eapply model_hoare_bind; [apply IHe3 | intros v3; apply model_hoare_EOU].
    - (* OP_ShuffleVector *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2].
      eapply model_hoare_bind; [apply IHe3 | intros v3; apply model_hoare_EOU].
    - (* OP_ExtractValue *)
      eapply model_hoare_bind; [apply IHe | intros v1; apply model_hoare_EOU].
    - (* OP_InsertValue *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2; apply model_hoare_EOU].
    - (* OP_Select *)
      eapply model_hoare_bind; [apply IHe1 | intros v1].
      eapply model_hoare_bind; [apply IHe2 | intros v2].
      eapply model_hoare_bind; [apply IHe3 | intros v3; apply model_hoare_EOU].
    - (* OP_Freeze *)
      eapply model_hoare_bind; [apply IHe | intros dv; apply model_hoare_freeze_preserve].
    - (* EXP_BlockAddress *)
      apply model_hoare_gread_preserve.
    - (* EXP_Splat *)
      eapply model_hoare_bind; [apply model_hoare_EOU | intros [_sz _t]].
      eapply model_hoare_bind; [apply IHe | intros v1; apply model_hoare_ret; auto].
    - (* EXP_Metadata (METADATA_Const) *)
      apply IHe.
    - (* EXP_Metadata (other) *)
      destruct md as [| | [t1 e1] | | | |];
        [| | exfalso; exact (H t1 e1 Logic.eq_refl) | | | |];
        apply model_hoare_ret; auto.
  Qed.

  (** Allocating one pointer slot (`alloca DTYPE_Pointer 1%N None`) yields a fresh
      positive address strictly greater than all previously allocated keys in [mem],
      and inserts that address into [mem']. *)
  Lemma model_hoare_alloca_fn_ptr (P : FusedS -> Prop) :
    model_hoare P (alloca (DTYPE_Base DTYPE_Pointer) 1%N None)
      (fun '(m', lsg') dv =>
         exists m0 p,
           P (m0, lsg') /\
           dv = DVALUE_Base (DVALUE_Pointer p) /\
           (ptr_to_int p >= 1)%Z /\
           IM.In (ptr_to_int p) (Memory_stack_memory (state_memory_stack m')) /\
           (forall k,
              IM.In k (Memory_stack_memory (state_memory_stack m0)) ->
              (k < ptr_to_int p)%Z /\
              IM.In k (Memory_stack_memory (state_memory_stack m')))).
  Proof using.
    intros [m0 lsg] U HP.
    unfold alloca; eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr_eq; reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler
         Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
         cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    cbn [handle_memoryM]; unfold allocate_dtyp.
    change (dtyp_eqb (DTYPE_Base DTYPE_Pointer) DTYPE_Void) with false; cbv iota.
    set (pbytes := concat_acc (repeatN 1%N (generate_poison_bytes (DTYPE_Base DTYPE_Pointer)))).
    set (al := preferred_alignment (dtyp_alignment (DTYPE_Base DTYPE_Pointer))).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite ?memM_interp_prov_bind_eq, ?memM_interp_prov_memS_bind_eq, ?Eqit.bind_bind; reflexivity
      | symmetry; rewrite ?memM_interp_prov_bind_eq, ?memM_interp_prov_memS_bind_eq, ?Eqit.bind_bind; reflexivity |].
    unfold allocate_bytes, fresh_prov, Mfresh_prov; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
      norm_subevent;
      cbn [ITree.trigger observe rp_step_body match_vis_both is_ub_prov].
    right; right; intros pr _.
    left; eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    set (m_pr := {| state_memory_stack := state_memory_stack m0; state_provenance := pr |}).
    unfold MemoryModelPrimitivesV, allocate_bytes_with_pr; cbn beta iota;
      unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key;
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret memS_mon memS_bind];
      cbv beta zeta;
      try fold m_pr; try fold pbytes; try fold al.
    lazymatch goal with
    | |- context [@provenance_to_allocation_id ?PR ?p] =>
        set (aid := @provenance_to_allocation_id PR p)
    end.
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack m0)) al).
    cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret
         memM_interp_prov m_pr state_memory_stack Memory_stack_memory].
    fold addr; try fold m_pr.
    unfold int_to_ptr;
      cbn [P2I ParamsV PIV PointerV EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret].
    destruct (from_Z addr) as [s | s | s | ip_a] eqn:Efz;
      cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Vellvm.Semantics.Interfaces.Memory.lift
           memS_mon memS_bind memM_interp_prov].
    - unfold raise, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
        norm_subevent;
        cbn [observe rp_step_body match_vis_both is_ub_prov is_ub_bot];
        right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
    - unfold raiseOOM, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
        norm_subevent;
        cbn [observe rp_step_body is_ub_prov is_ub_bot];
        left; reflexivity.
    - unfold raiseUB, trigger_cast, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
        norm_subevent;
        cbn [observe rp_step_body is_ub_prov is_ub_bot];
        left; reflexivity.
    - set (p := (ip_a, allocation_id_to_prov aid) : @ptr (@PROV PaV) (@PTR PaV)).
      assert (Hp_addr : ptr_to_int p = addr).
      { cbn [ptr_to_int P2I ParamsV PIV PointerV fst]; apply from_Z_to_Z, Efz. }
      match goal with
      | |- context [get_consecutive_ptrs ?p0 _] => change p0 with p
      end.
      destruct (get_consecutive_ptrs p (N.length pbytes)) as [s | s | s | ptrs] eqn:Ecptrs;
        cbn [Vellvm.Semantics.Interfaces.Memory.lift EOU_monad memS_mon
             memS_bind ExtLib.Structures.Monad.ret memM_interp_prov].
      + unfold raise, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
          norm_subevent;
          cbn [observe rp_step_body match_vis_both is_ub_prov is_ub_bot];
          right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
      + unfold raiseOOM, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
          norm_subevent;
          cbn [observe rp_step_body is_ub_prov is_ub_bot];
          left; reflexivity.
      + unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
          norm_subevent;
          cbn [observe rp_step_body is_ub_prov is_ub_bot];
          left; reflexivity.
      + unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem,
               app_mem_stack, get, put.
        unfold m_pr in *; clear m_pr.
        destruct m0 as [[mem0 fs0 hp0] pr0].
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind ExtLib.Structures.Monad.ret memM_interp_prov
             state_memory_stack state_get_memory MemoryModelStateV Memory_stack_memory
             Memory_stack_frame_stack Memory_stack_heap state_provenance].
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
        assert (Hmem_eq :
          forall (ks : list (@ptr (@PROV PaV) (@PTR PaV))) (ms : @Memory_stack PaV),
            Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { unfold add_all_to_frame; intros ks; induction ks as [| k0 ks' IHks]; intros [mm ss hh]; [reflexivity |].
          cbn [fold_left]; rewrite IHks; destruct ss; reflexivity. }
        apply refine_prov_tau2_ret.
        split; [reflexivity | split; [reflexivity |]].
        exists {| state_memory_stack := {| Memory_stack_memory := mem0;
                                           Memory_stack_frame_stack := fs0;
                                           Memory_stack_heap := hp0 |};
                  state_provenance := pr0 |}, p.
        split; [exact HP |].
        split; [reflexivity |].
        split;
          [ assert (Hp_ge : (ptr_to_int p >= 1)%Z)
              by (rewrite Hp_addr; apply next_key_with_alignment_ge_1);
            exact Hp_ge | ].
        cbn [state_memory_stack];
        repeat lazymatch goal with
               | |- context [Memory_stack_memory (add_all_to_frame ?ks ?ms)] =>
                   let H := fresh "Hm" in
                   assert (H : Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms)
                     by apply Hmem_eq;
                   rewrite H; clear H
               end;
        cbn [Memory_stack_memory].
        assert (Hlen_pos : (1 <= List.length (memory_bytes_to_bytes aid pbytes))%nat).
        { unfold memory_bytes_to_bytes; rewrite map_acc_eq, length_map.
          unfold pbytes; rewrite concat_acc_eq.
          set (gb := generate_poison_bytes (DTYPE_Base DTYPE_Pointer)).
          replace (repeatN 1%N gb) with [gb] by reflexivity.
          cbn [List.concat]; rewrite app_nil_r.
          unfold gb, generate_poison_bytes, generate_num_poison_bytes, generate_num_poison_bytes_h.
          rewrite seq_map_acc_eq, length_map, Nseq_length, N_to_nat_safe_eq.
          pose proof (@store_size_dtyp_ptr_pos (@SIZE PaV) (@SIZET PaV)) as Hptr.
          lia. }
        split.
        * apply IM_In_add_all_index_acc; right; cbn [ptr_to_int P2I ParamsV PIV PointerV fst] in *; lia.
        * intros k Hk.
          assert (Hk_lt : (k < ptr_to_int p)%Z).
          { rewrite Hp_addr; apply next_key_with_alignment_gt_in, Hk. }
          split; [exact Hk_lt | apply IM_In_add_all_index_acc; left; exact Hk].
  Qed.

  Definition decl_alloc_inv (seen : list (raw_id * Z)) (s : FusedS) : Prop :=
    let '(m, ((sf, fstk), g)) := s in
    sf.(stack_vars) = Maps.empty /\
    sf.(stack_exc) = None /\
    sf.(stack_loc) = None /\
    fstk = [] /\
    (forall x z,
       In (x, z) seen ->
       (z >= 1)%Z /\
       IM.In z (Memory_stack_memory (state_memory_stack m)) /\
       exists p : @ptr (@PROV PaV) (@PTR PaV),
         ptr_to_int p = z /\
         Maps.lookup x g = Some (DVALUE_Base (DVALUE_Pointer p))) /\
    (forall x v,
       Maps.lookup x g = Some v ->
       In x (List.map fst seen)) /\
    (forall x1 z1 x2 z2,
       In (x1, z1) seen ->
       In (x2, z2) seen ->
       x1 <> x2 ->
       z1 <> z2).

  Definition decl_loop_inv (prev_ds : list (declaration dtyp)) (s : FusedS) : Prop :=
    exists seen : list (raw_id * Z),
      incl (List.map fst seen) (List.map dc_name prev_ds) /\
      (forall d,
         In d prev_ds ->
         lookup_intrinsic_declaration (dc_name d) = None ->
         exists z, In (dc_name d, z) seen) /\
      decl_alloc_inv seen s.

  Lemma model_hoare_allocate_declarations_aux :
    forall (ds prev_ds : list (declaration dtyp)),
      NoDup (List.map dc_name (prev_ds ++ ds)) ->
      model_hoare (decl_loop_inv prev_ds) (allocate_declarations ds)
        (fun s' _ => decl_loop_inv (prev_ds ++ ds) s').
  Proof using.
    induction ds as [| d ds' IH]; intros prev_ds Hnd; unfold allocate_declarations; cbn [loop_monad].
    - rewrite app_nil_r; apply model_hoare_ret; intros s Hs; exact Hs.
    - assert (Hnot_prev : ~ In (dc_name d) (List.map dc_name prev_ds)).
      { rewrite map_app in Hnd; cbn [List.map] in Hnd.
        intros Hin; eapply (inl_nodup_app_disj _ _ Hnd); [exact Hin | left; reflexivity]. }
      assert (Hnd_next : NoDup (List.map dc_name ((prev_ds ++ [d]) ++ ds'))).
      { rewrite <- app_assoc; exact Hnd. }
      replace (prev_ds ++ d :: ds') with ((prev_ds ++ [d]) ++ ds')
        by (rewrite <- app_assoc; reflexivity).
      eapply model_hoare_bind with (Q := fun s _ => decl_loop_inv (prev_ds ++ [d]) s);
        [| intros []; apply IH, Hnd_next].
      unfold allocate_declaration.
      destruct (lookup_intrinsic_declaration (dc_name d)) as [intr_fn |] eqn:Eintr.
      + apply model_hoare_ret; intros s (seen & Hincl & Hall & Hinv).
        exists seen; split; [| split; [| exact Hinv]].
        * intros x Hx; rewrite map_app; apply in_or_app; left; apply Hincl, Hx.
        * intros d0 Hd0 Hnone; apply in_app_or in Hd0 as [Hd0 | [<- | []]].
          -- apply Hall; assumption.
          -- congruence.
      + eapply model_hoare_bind; [apply model_hoare_alloca_fn_ptr | intros dv].
        apply model_hoare_gwrite.
        intros m' [sf fstk] g0
          (m0 & p & (seen & Hincl & Hall & Hinv) & -> & Hp_ge1 & Hp_in & Hprev_lt).
        cbn [decl_alloc_inv] in Hinv.
        destruct Hinv as (Hvars & Hexc & Hloc & -> & Hseen_ok & Hseen_dom & Hseen_disj).
        exists ((dc_name d, ptr_to_int p) :: seen).
        split.
        * intros x [<- | Hx]; rewrite map_app; apply in_or_app;
            [right; left; reflexivity | left; apply Hincl, Hx].
        * split.
          -- intros d0 Hd0 Hnone; apply in_app_or in Hd0 as [Hd0 | [<- | []]].
             ++ destruct (Hall d0 Hd0 Hnone) as [z Hz]; exists z; right; exact Hz.
             ++ exists (ptr_to_int p); left; reflexivity.
          -- cbn [decl_alloc_inv].
             split; [exact Hvars |].
             split; [exact Hexc |].
             split; [exact Hloc |].
             split; [reflexivity |].
             split.
             ++ intros x z [Heq | Hin_s].
                ** injection Heq as <- <-.
                   split; [exact Hp_ge1 |].
                   split; [exact Hp_in |].
                   exists p; split;
                     [ reflexivity
                     | cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity ].
                ** destruct (Hseen_ok x z Hin_s) as (Hz_ge1 & Hz_in0 & p0 & Hp0_z & Hlk0).
                   destruct (Hprev_lt z Hz_in0) as (_ & Hz_in').
                   assert (Hne : dc_name d <> x).
                   { intros Heq; rewrite Heq in Hnot_prev; apply Hnot_prev, Hincl.
                     change x with (fst (x, z)); apply in_map, Hin_s. }
                   split; [exact Hz_ge1 |].
                   split; [exact Hz_in' |].
                   exists p0; split; [exact Hp0_z |].
                   cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne; exact Hlk0.
             ++ split.
                ** intros x v0 Hlk.
                   cbn [List.map fst].
                   destruct (RawIDOrd.eq_dec (dc_name d) x) as [-> | Hne].
                   --- left; reflexivity.
                   --- cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_neq_o in Hlk by exact Hne.
                       right; eapply Hseen_dom, Hlk.
                ** intros x1 z1 x2 z2 [Heq1 | H1] [Heq2 | H2] Hne.
                   --- injection Heq1 as Hx1 <-; injection Heq2 as Hx2 <-; rewrite <- Hx1, <- Hx2 in Hne; contradiction.
                   --- injection Heq1 as _ <-.
                       destruct (Hseen_ok x2 z2 H2) as (_ & Hz2_in0 & _).
                       destruct (Hprev_lt z2 Hz2_in0) as (Hlt & _).
                       intros Heq; apply (Z.lt_irrefl z2); pattern z2 at 2; rewrite <- Heq; exact Hlt.
                   --- injection Heq2 as _ <-.
                       destruct (Hseen_ok x1 z1 H1) as (_ & Hz1_in0 & _).
                       destruct (Hprev_lt z1 Hz1_in0) as (Hlt & _).
                       intros Heq; apply (Z.lt_irrefl z1); pattern z1 at 2; rewrite Heq; exact Hlt.
                   --- eapply Hseen_disj; eassumption.
  Qed.

  Definition post_decl_inv (all_decls : list (declaration dtyp)) (s : FusedS) : Prop :=
    let decl_names := List.map dc_name all_decls in
    let '(_, ((sf, fstk), g)) := s in
    sf.(stack_vars) = Maps.empty /\
    sf.(stack_exc) = None /\
    sf.(stack_loc) = None /\
    fstk = [] /\
    exists seen : list (raw_id * Z),
      incl (List.map fst seen) decl_names /\
      (forall d,
         In d all_decls ->
         lookup_intrinsic_declaration (dc_name d) = None ->
         exists z, In (dc_name d, z) seen) /\
      (forall x z,
         In (x, z) seen ->
         (z >= 1)%Z /\
         exists p : @ptr (@PROV PaV) (@PTR PaV),
           ptr_to_int p = z /\
           Maps.lookup x g = Some (DVALUE_Base (DVALUE_Pointer p))) /\
      (forall x v,
         In x decl_names ->
         Maps.lookup x g = Some v ->
         In x (List.map fst seen)) /\
      (forall x1 z1 x2 z2,
         In (x1, z1) seen ->
         In (x2, z2) seen ->
         x1 <> x2 ->
         z1 <> z2).

  Lemma post_decl_inv_lsg (all_decls : list (declaration dtyp))
    (m m' : state) (lsg : (@stack_frame PaV * stack) * global_env) :
    post_decl_inv all_decls (m, lsg) ->
    post_decl_inv all_decls (m', lsg).
  Proof using.
    destruct lsg as [[sf fstk] g]; intros H; exact H.
  Qed.

  Lemma model_hoare_gwrite_post_decl (all_decls : list (declaration dtyp))
    (k : raw_id) (v : @dvalue PaV)
    (Hnin : ~ In k (List.map dc_name all_decls)) :
    model_hoare (post_decl_inv all_decls) (gwrite k v)
      (fun s' _ => post_decl_inv all_decls s').
  Proof using.
    apply model_hoare_gwrite.
    intros m [sf fstk] g
      (Hvars & Hexc & Hloc & Hfstk & seen & Hincl & Hall & Hok & Hdom & Hdisj).
    split; [exact Hvars |].
    split; [exact Hexc |].
    split; [exact Hloc |].
    split; [exact Hfstk |].
    exists seen.
    split; [exact Hincl |].
    split; [exact Hall |].
    split; [| split; [| exact Hdisj]].
    - intros x z Hxz.
      destruct (Hok x z Hxz) as (Hz_ge1 & p & Hp_z & Hlk).
      assert (Hne : k <> x).
      { intros Heq; rewrite Heq in Hnin; apply Hnin, Hincl; change x with (fst (x, z)); apply in_map, Hxz. }
      split; [exact Hz_ge1 |].
      exists p; split; [exact Hp_z |].
      cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne; exact Hlk.
    - intros x v0 Hx_in Hlk.
      assert (Hne : k <> x) by (intros Heq; rewrite Heq in Hnin; contradiction).
      cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_neq_o in Hlk by exact Hne.
      eapply Hdom; eassumption.
  Qed.

  Lemma build_global_environment_inline_post (M : CFG.mcfg dtyp)
    (Hhyg : is_hygienic_module M = true) :
    let all_decls := m_declarations M ++ List.map df_prototype (m_definitions M) in
    model_hoare
      (fun s => s = init_fused_state)
      (build_global_environment M)
      (fun s' _ => post_decl_inv all_decls s').
  Proof using.
    intros all_decls.
    unfold is_hygienic_module in Hhyg; cbn zeta in Hhyg.
    apply nodup_raw_ids_spec in Hhyg.
    fold all_decls in Hhyg.
    set (decl_names := List.map dc_name all_decls) in *.
    set (ba_names := List.map (fun '(f, b) => blockaddress_id f b) (mcfg_block_addresses M)) in *.
    set (glob_names := List.map g_ident (m_globals M)) in *.
    pose proof (inl_nodup_app_l decl_names (ba_names ++ glob_names) Hhyg) as Hnd_decl.
    pose proof (inl_nodup_app_disj decl_names (ba_names ++ glob_names) Hhyg) as Hdisj_decl.
    unfold build_global_environment; fold all_decls.
    eapply model_hoare_bind with (Q := fun s _ => post_decl_inv all_decls s).
    - eapply model_hoare_weaken with
        (P := decl_loop_inv [])
        (Q := fun s' _ => decl_loop_inv ([] ++ all_decls) s').
      + intros s ->.
        exists []; split; [apply incl_refl | split; [intros _ [] |]].
        cbn [decl_alloc_inv init_fused_state stack_vars stack_exc stack_loc].
        split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
        split; [intros _ _ [] | split; [intros ? ? Hlk; cbn in Hlk; discriminate Hlk | intros _ _ _ _ []]].
      + intros [m [[sf fstk] g]] _ (seen & Hincl & Hall & Hvars & Hexc & Hloc & Hfstk & Hok & Hdom & Hdisj).
        cbn [app] in *.
        split; [exact Hvars | split; [exact Hexc | split; [exact Hloc | split; [exact Hfstk |]]]].
        exists seen; split;
          [ exact Hincl
          | split; [exact Hall | split; [| split; [| exact Hdisj]]] ].
        * intros x z Hxz; destruct (Hok x z Hxz) as (Hz1 & _ & p & Hpz & Hlk).
          split; [exact Hz1 | exists p; split; assumption].
        * intros x v _ Hlk; eapply Hdom, Hlk.
      + apply model_hoare_allocate_declarations_aux; cbn [app]; exact Hnd_decl.
    - intros [].
      eapply model_hoare_bind with (Q := fun s _ => post_decl_inv all_decls s).
      + unfold allocate_block_addresses.
        apply model_hoare_loop_monad; intros [f b] Hfb.
        apply nodup_In in Hfb.
        assert (Hnot_decl : ~ In (blockaddress_id f b) decl_names).
        { intros Hin; eapply Hdisj_decl; [exact Hin |].
          apply in_or_app; left; unfold ba_names.
          change (blockaddress_id f b) with ((fun '(f0, b0) => blockaddress_id f0 b0) (f, b)).
          apply in_map, Hfb. }
        unfold allocate_block_address.
        eapply model_hoare_bind;
          [unfold alloca; apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls))
          | intros v; apply model_hoare_gwrite_post_decl, Hnot_decl].
      + intros [].
        eapply model_hoare_bind with (Q := fun s _ => post_decl_inv all_decls s).
        * unfold allocate_globals.
          apply model_hoare_loop_monad; intros g Hg.
          assert (Hnot_decl : ~ In (g_ident g) decl_names).
          { intros Hin; eapply Hdisj_decl; [exact Hin |].
            apply in_or_app; right; unfold glob_names; apply in_map, Hg. }
          unfold allocate_global; destruct (g_alias g).
          -- apply model_hoare_ret; intros s Hs; exact Hs.
          -- eapply model_hoare_bind;
               [unfold alloca; apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls))
               | intros v; apply model_hoare_gwrite_post_decl, Hnot_decl].
        * intros [].
          unfold initialize_globals.
          apply model_hoare_loop_monad; intros g Hg.
          assert (Hnot_decl : ~ In (g_ident g) decl_names).
          { intros Hin; eapply Hdisj_decl; [exact Hin |].
            apply in_or_app; right; unfold glob_names; apply in_map, Hg. }
          unfold initialize_global; destruct (g_alias g).
          -- destruct (g_exp g) as [ge |]; [| apply model_hoare_raiseUB].
             destruct ge; cbv beta iota zeta;
               lazymatch goal with
               | |- model_hoare _ (raiseUB _) _ => apply model_hoare_raiseUB
               | _ => idtac
               end.
             destruct id as [g_src |]; [| apply model_hoare_raiseUB].
             eapply model_hoare_bind;
               [apply model_hoare_gread_preserve
               | intros p; apply model_hoare_gwrite_post_decl, Hnot_decl].
          -- eapply model_hoare_bind; [apply model_hoare_gread_preserve | intros a].
             eapply model_hoare_bind.
             ++ destruct (g_exp g) as [ge |].
                ** apply (model_hoare_denote_exp_lsg_preserve _ (post_decl_inv_lsg all_decls)).
                ** apply model_hoare_ret; intros s Hs; exact Hs.
             ++ intros uv; unfold store.
                apply (model_hoare_memory_lsg_preserve _ _ (post_decl_inv_lsg all_decls)).
  Qed.


  (** * 8. Elastic Inlining Simulation ([gen_inline_sim], [cfg_inline_sim], [mcfg_inline_sim]) *)

End InliningSemantics.
