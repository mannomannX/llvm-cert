(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Provenance-Choice Model Semantics & Whole-Program Refinement ([CertPasses.PassCommonModel])

    Provides vanilla-CIC event relations (zero [JMeq], zero [Equations]),
    provenance-choice elasticity ([ProvE] / [refine_prov]), the [PreOrder]
    whole-program refinement relation ([prog_refines]), and the modular
    whole-CFG lifter ([lift_cfg_pass]). *)

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
  Basics.HeterogeneousRelations.

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
  Utils.rutt_cutoff
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.
From CertPasses.common Require Export
  ItreeTactics.
Export LLVMAst.
Import Logic.

Arguments exp_block_addresses {T} _.
Arguments texps_block_addresses {T} _.
Arguments instr_block_addresses {T} _.
Arguments term_block_addresses {T} _.
Arguments block_block_addresses {T} _.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Import PassCommonSyntax.

(** * 5. Vanilla-CIC Event & Answer Relations (Zero [JMeq], Zero [Equations]) *)

Definition sum_prerel_c {E1 E2 D1 D2 : Type -> Type}
  (PR1 : prerel E1 D1) (PR2 : prerel E2 D2) : prerel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 e2 =>
    match e1, e2 with
    | inl1 x1, inl1 x2 => PR1 A B x1 x2
    | inr1 y1, inr1 y2 => PR2 A B y1 y2
    | _, _ => False
    end.

Definition sum_postrel_c {E1 E2 D1 D2 : Type -> Type}
  (PO1 : postrel E1 D1) (PO2 : postrel E2 D2) : postrel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 a1 e2 a2 =>
    match e1 return A -> (D1 +' D2) B -> B -> Prop with
    | inl1 x1 => fun a1' e2' a2' =>
        match e2' return B -> Prop with
        | inl1 x2 => fun a2'' => PO1 _ _ x1 a1' x2 a2''
        | inr1 _ => fun _ => False
        end a2'
    | inr1 y1 => fun a1' e2' a2' =>
        match e2' return B -> Prop with
        | inl1 _ => fun _ => False
        | inr1 y2 => fun a2'' => PO2 _ _ y1 a1' y2 a2''
        end a2'
    end a1 e2 a2.

Variant cutNone {E : Type -> Type} : forall [A : Type], E A -> Prop := .

Variant cutUB_rel {E : Type -> Type} `{UBE -< E} : forall [A : Type], E A -> Prop :=
  | CutUB_rel u : cutUB_rel (subevent _ (ThrowUB u)).

Ltac destruct_sum2 e1 e2 HE :=
  repeat (let Te := type of e1 in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ =>
              match type of HE with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in HE
              end;
              destruct e1 as [e1 | e1], e2 as [e2 | e2];
              cbn [sum_prerel_c sum_postrel_c] in HE;
              try contradiction
          end).

Ltac destruct_sum3 e1 e2 e3 H12 H23 :=
  repeat (let Te := type of e1 in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ =>
              match type of H12 with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in H12
              end;
              match type of H23 with
              | sum_prerel_c _ _ _ _ _ _ => idtac
              | sum_postrel_c _ _ _ _ _ _ _ _ => idtac
              | _ => try red in H23
              end;
              destruct e1 as [e1 | e1], e2 as [e2 | e2], e3 as [e3 | e3];
              cbn [sum_prerel_c sum_postrel_c] in H12, H23;
              try contradiction
          end).

Section EventRelations.
  Context {Pa : Params}.

  Definition EqE_Call : prerel CallE CallE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Call t1 cc1 f1 args1, Call t2 cc2 f2 args2 =>
          t1 = t2 /\ cc1 = cc2 /\ f1 = f2 /\ args1 = args2
      end.

  Definition EqA_Call : postrel CallE CallE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in CallE A' return A' -> CallE _ -> _ -> Prop with
      | Call _ _ _ _ => fun r1 e2' r2 =>
          match e2' in CallE B' return B' -> Prop with
          | Call _ _ _ _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_ExternalCall : prerel ExternalCallE ExternalCallE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | ExternalCall t1 f1 args1, ExternalCall t2 f2 args2 =>
          t1 = t2 /\ f1 = f2 /\ args1 = args2
      | IO_stdout s1, IO_stdout s2 => s1 = s2
      | IO_stderr s1, IO_stderr s2 => s1 = s2
      | _, _ => False
      end.

  Definition EqA_ExternalCall : postrel ExternalCallE ExternalCallE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in ExternalCallE A' return A' -> ExternalCallE _ -> _ -> Prop with
      | ExternalCall _ _ _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | ExternalCall _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | IO_stdout _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | IO_stdout _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | IO_stderr _ => fun r1 e2' r2 =>
          match e2' in ExternalCallE B' return B' -> Prop with
          | IO_stderr _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Intrinsic : prerel IntrinsicE IntrinsicE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Intrinsic t1 f1 args1 va1, Intrinsic t2 f2 args2 va2 =>
          t1 = t2 /\ f1 = f2 /\ args1 = args2 /\ va1 = va2
      end.

  Definition EqA_Intrinsic : postrel IntrinsicE IntrinsicE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in IntrinsicE A' return A' -> IntrinsicE _ -> _ -> Prop with
      | Intrinsic _ _ _ _ => fun r1 e2' r2 =>
          match e2' in IntrinsicE B' return B' -> Prop with
          | Intrinsic _ _ _ _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_Global : prerel GlobalE GlobalE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | GlobalWrite x1 v1, GlobalWrite x2 v2 => x1 = x2 /\ v1 = v2
      | GlobalRead x1, GlobalRead x2 => x1 = x2
      | _, _ => False
      end.

  Definition EqA_Global : postrel GlobalE GlobalE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in GlobalE A' return A' -> GlobalE _ -> _ -> Prop with
      | GlobalWrite _ _ => fun r1 e2' r2 =>
          match e2' in GlobalE B' return B' -> Prop with
          | GlobalWrite _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | GlobalRead _ => fun r1 e2' r2 =>
          match e2' in GlobalE B' return B' -> Prop with
          | GlobalRead _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Local : prerel LocalE LocalE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | LocalWrite x1 v1, LocalWrite x2 v2 => x1 = x2 /\ v1 = v2
      | LocalRead x1, LocalRead x2 => x1 = x2
      | _, _ => False
      end.

  Definition EqA_Local : postrel LocalE LocalE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in LocalE A' return A' -> LocalE _ -> _ -> Prop with
      | LocalWrite _ _ => fun r1 e2' r2 =>
          match e2' in LocalE B' return B' -> Prop with
          | LocalWrite _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | LocalRead _ => fun r1 e2' r2 =>
          match e2' in LocalE B' return B' -> Prop with
          | LocalRead _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Stack : prerel StackE StackE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | StackPush args1, StackPush args2 => args1 = args2
      | StackPop, StackPop => True
      | StackRaise exc1, StackRaise exc2 => exc1 = exc2
      | StackGetExc, StackGetExc => True
      | _, _ => False
      end.

  Definition EqA_Stack : postrel StackE StackE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in StackE A' return A' -> StackE _ -> _ -> Prop with
      | StackPush _ => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackPush _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackPop => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackPop => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackRaise _ => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackRaise _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | StackGetExc => fun r1 e2' r2 =>
          match e2' in StackE B' return B' -> Prop with
          | StackGetExc => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Memory : prerel MemoryE MemoryE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | MemPush, MemPush => True
      | MemPop, MemPop => True
      | Alloca t1 n1 al1, Alloca t2 n2 al2 => t1 = t2 /\ n1 = n2 /\ al1 = al2
      | Load t1 a1, Load t2 a2 => t1 = t2 /\ a1 = a2
      | Store t1 a1 v1, Store t2 a2 v2 => t1 = t2 /\ a1 = a2 /\ v1 = v2
      | Conv cv1 tf1 v1 tt1, Conv cv2 tf2 v2 tt2 =>
          cv1 = cv2 /\ tf1 = tf2 /\ v1 = v2 /\ tt1 = tt2
      | _, _ => False
      end.

  Definition EqA_Memory : postrel MemoryE MemoryE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in MemoryE A' return A' -> MemoryE _ -> _ -> Prop with
      | MemPush => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | MemPush => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | MemPop => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | MemPop => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Alloca _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Alloca _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Load _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Load _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Store _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Store _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      | Conv _ _ _ _ => fun r1 e2' r2 =>
          match e2' in MemoryE B' return B' -> Prop with
          | Conv _ _ _ _ => fun r2' => r1 = r2'
          | _ => fun _ => False
          end r2
      end a1 e2 a2.

  Definition EqE_Draw : prerel DrawE DrawE :=
    fun _ _ e1 e2 =>
      match e1, e2 with
      | Draw t1, Draw t2 => t1 = t2
      end.

  Definition EqA_Draw : postrel DrawE DrawE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in DrawE A' return A' -> DrawE _ -> _ -> Prop with
      | Draw _ => fun r1 e2' r2 =>
          match e2' in DrawE B' return B' -> Prop with
          | Draw _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_OOM : prerel OOME OOME :=
    fun _ _ e1 e2 => match e1, e2 with ThrowOOM _, ThrowOOM _ => True end.

  Definition EqA_OOM : postrel OOME OOME :=
    fun _ _ e1 a1 _ _ => match e1 in OOME A' return A' -> Prop with ThrowOOM _ => fun v : void => match v with end end a1.

  Definition EqE_Exc : prerel LLVMExcE LLVMExcE :=
    fun _ _ e1 e2 => match e1, e2 with LLVMExc x1, LLVMExc x2 => x1 = x2 end.

  Definition EqA_Exc : postrel LLVMExcE LLVMExcE :=
    fun _ _ e1 a1 _ _ => match e1 in LLVMExcE A' return A' -> Prop with LLVMExc _ => fun v : void => match v with end end a1.

  Definition EqE_UB : prerel UBE UBE :=
    fun _ _ e1 e2 => match e1, e2 with ThrowUB _, ThrowUB _ => True end.

  Definition EqA_UB : postrel UBE UBE :=
    fun _ _ e1 a1 _ _ => match e1 in UBE A' return A' -> Prop with ThrowUB _ => fun v : void => match v with end end a1.

  Definition EqE_Debug : prerel DebugE DebugE :=
    fun _ _ e1 e2 => match e1, e2 with Debug _, Debug _ => True end.

  Definition EqA_Debug : postrel DebugE DebugE :=
    fun _ _ e1 a1 e2 a2 =>
      match e1 in DebugE A' return A' -> DebugE _ -> _ -> Prop with
      | Debug _ => fun r1 e2' r2 =>
          match e2' in DebugE B' return B' -> Prop with
          | Debug _ => fun r2' => r1 = r2'
          end r2
      end a1 e2 a2.

  Definition EqE_Failure : prerel FailureE FailureE :=
    fun _ _ e1 e2 => match e1, e2 with Throw _, Throw _ => True end.

  Definition EqA_Failure : postrel FailureE FailureE :=
    fun _ _ e1 a1 _ _ => match e1 in FailureE A' return A' -> Prop with Throw _ => fun v : void => match v with end end a1.

  Definition EqE_MCFG : prerel MCFGEtop MCFGEtop :=
    sum_prerel_c EqE_ExternalCall
      (sum_prerel_c EqE_Intrinsic
         (sum_prerel_c EqE_Global
            (sum_prerel_c (sum_prerel_c EqE_Local EqE_Stack)
               (sum_prerel_c EqE_Memory
                  (sum_prerel_c EqE_Draw
                     (sum_prerel_c EqE_OOM
                        (sum_prerel_c EqE_Exc
                           (sum_prerel_c EqE_UB
                              (sum_prerel_c EqE_Debug EqE_Failure))))))))).

  Definition EqA_MCFG : postrel MCFGEtop MCFGEtop :=
    sum_postrel_c EqA_ExternalCall
      (sum_postrel_c EqA_Intrinsic
         (sum_postrel_c EqA_Global
            (sum_postrel_c (sum_postrel_c EqA_Local EqA_Stack)
               (sum_postrel_c EqA_Memory
                  (sum_postrel_c EqA_Draw
                     (sum_postrel_c EqA_OOM
                        (sum_postrel_c EqA_Exc
                           (sum_postrel_c EqA_UB
                              (sum_postrel_c EqA_Debug EqA_Failure))))))))).

  Definition EqE_CFG : prerel CFGEtop CFGEtop :=
    sum_prerel_c EqE_Call EqE_MCFG.

  Definition EqA_CFG : postrel CFGEtop CFGEtop :=
    sum_postrel_c EqA_Call EqA_MCFG.

  Definition EqE_bot : prerel MCFGEbot MCFGEbot :=
    sum_prerel_c EqE_ExternalCall
      (sum_prerel_c EqE_OOM
         (sum_prerel_c EqE_Exc
            (sum_prerel_c EqE_UB
               (sum_prerel_c EqE_Debug EqE_Failure)))).

  Definition EqA_bot : postrel MCFGEbot MCFGEbot :=
    sum_postrel_c EqA_ExternalCall
      (sum_postrel_c EqA_OOM
         (sum_postrel_c EqA_Exc
            (sum_postrel_c EqA_UB
               (sum_postrel_c EqA_Debug EqA_Failure)))).

  Lemma EqE_MCFG_refl {A} (e : MCFGEtop A) : EqE_MCFG A A e e.
  Proof using.
    destruct_sum1 e; destruct e; cbn; auto.
  Qed.

  Lemma EqA_MCFG_refl {A} (e : MCFGEtop A) (a : A) : EqA_MCFG A A e a e a.
  Proof using.
    destruct_sum1 e; destruct e; cbn; try destruct a; reflexivity.
  Qed.

  Lemma EqE_CFG_refl {A} (e : CFGEtop A) : EqE_CFG A A e e.
  Proof using.
    destruct e as [c | m]; [destruct c; cbn; auto | apply EqE_MCFG_refl].
  Qed.

  Lemma EqE_bot_refl {A} (e : MCFGEbot A) : EqE_bot A A e e.
  Proof using.
    destruct_sum1 e; destruct e; cbn; auto.
  Qed.

  Lemma EqE_bot_trans {A B C} (e1 : MCFGEbot A) (e2 : MCFGEbot B) (e3 : MCFGEbot C) :
    EqE_bot A B e1 e2 -> EqE_bot B C e2 e3 -> EqE_bot A C e1 e3.
  Proof using.
    intros H12 H23; destruct_sum3 e1 e2 e3 H12 H23;
      destruct e1; destruct e2; destruct e3; cbn in *; try contradiction; intuition congruence.
  Qed.

  Lemma EqA_MCFG_eq {A} (e : MCFGEtop A) (a1 a2 : A) :
    EqA_MCFG A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct_sum1 e; destruct e; cbn;
      intros HA; match type of a1 with void => destruct a1 | _ => exact HA end.
  Qed.

  Lemma EqA_CFG_eq {A} (e : CFGEtop A) (a1 a2 : A) :
    EqA_CFG A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct e as [c | m]; [destruct c; cbn; intros HA; exact HA | apply EqA_MCFG_eq].
  Qed.

  Lemma EqA_bot_eq {A} (e : MCFGEbot A) (a1 a2 : A) :
    EqA_bot A A e a1 e a2 -> a1 = a2.
  Proof using.
    destruct_sum1 e; destruct e; cbn;
      intros HA; match type of a1 with void => destruct a1 | _ => exact HA end.
  Qed.

  Lemma EqA_bot_refl_diag {A B} (e1 : MCFGEbot A) (e2 : MCFGEbot B) (a : A) :
    EqE_bot A B e1 e2 ->
    exists b : B, EqA_bot A B e1 a e2 b.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE |- *; try contradiction;
      match type of a with void => destruct a | _ => exists a; reflexivity end.
  Qed.

  Lemma EqA_bot_trans {A B C}
    (e1 : MCFGEbot A) (e2 : MCFGEbot B) (e3 : MCFGEbot C)
    (a1 : A) (a3 : C) :
    EqE_bot A B e1 e2 ->
    EqE_bot B C e2 e3 ->
    EqA_bot A C e1 a1 e3 a3 ->
    exists a2 : B, EqA_bot A B e1 a1 e2 a2 /\ EqA_bot B C e2 a2 e3 a3.
  Proof using.
    intros H12 H23 Ha13; destruct_sum3 e1 e2 e3 H12 H23;
      destruct e1; destruct e2; destruct e3; cbn in H12, H23, Ha13 |- *;
      try contradiction;
      match type of a1 with
      | void => destruct a1
      | _ => exists a3; split; [exact Ha13 | reflexivity]
      end.
  Qed.

  (** ** Cut-Aware [CFGtop] & [MCFGtop] Refinements *)

  Definition refine_cfg {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : CFGtop R1) (t2 : CFGtop R2) : Prop :=
    ruttc cutUB_rel cutNone EqE_CFG EqA_CFG RR t1 t2.

  Definition refine_mcfg {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2) : Prop :=
    ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2.

  Lemma refine_cfg_refl {R} (t : CFGtop R) :
    refine_cfg Logic.eq t t.
  Proof using.
    revert t; ginit; gcofix CIH; intros t.
    destruct (observe t) eqn:Hot.
    - gstep; red; rewrite Hot; constructor; reflexivity.
    - gstep; red; rewrite Hot; constructor; gfinal; left; apply CIH.
    - gstep; red; rewrite Hot; constructor.
      + apply EqE_CFG_refl.
      + intros a1 a2 Ha; apply EqA_CFG_eq in Ha; subst a2.
        gfinal; left; apply CIH.
  Qed.

  Lemma refine_mcfg_refl {R} (t : MCFGtop R) :
    refine_mcfg Logic.eq t t.
  Proof using.
    revert t; ginit; gcofix CIH; intros t.
    destruct (observe t) eqn:Hot.
    - gstep; red; rewrite Hot; constructor; reflexivity.
    - gstep; red; rewrite Hot; constructor; gfinal; left; apply CIH.
    - gstep; red; rewrite Hot; constructor.
      + apply EqE_MCFG_refl.
      + intros a1 a2 Ha; apply EqA_MCFG_eq in Ha; subst a2.
        gfinal; left; apply CIH.
  Qed.

  Variant refine_EOU {A1 A2} (RR : A1 -> A2 -> Prop) : EOU A1 -> EOU A2 -> Prop :=
    | Refine_EOU_ret a1 a2 : RR a1 a2 -> refine_EOU RR (raise_ret a1) (raise_ret a2)
    | Refine_EOU_err s1 s2 : refine_EOU RR (raise_error s1) (raise_error s2)
    | Refine_EOU_oom s1 s2 : refine_EOU RR (raise_oom s1) (raise_oom s2)
    | Refine_EOU_ub s m2   : refine_EOU RR (raise_ub s) m2.

  Lemma refine_EOU_refl {A} (m : EOU A) :
    refine_EOU Logic.eq m m.
  Proof using.
    destruct m; constructor; reflexivity.
  Qed.

  Lemma refine_EOU_to_cfg {A1 A2} (RR : A1 -> A2 -> Prop) (m1 : EOU A1) (m2 : EOU A2) :
    refine_EOU RR m1 m2 ->
    refine_cfg RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof using.
    intros H; destruct H; cbn [EOU_to_itree].
    - apply ruttc_ret; assumption.
    - unfold raise, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseOOM, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s)).
  Qed.

  Lemma refine_EOU_to_mcfg {A1 A2} (RR : A1 -> A2 -> Prop) (m1 : EOU A1) (m2 : EOU A2) :
    refine_EOU RR m1 m2 ->
    refine_mcfg RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof using.
    intros H; destruct H; cbn [EOU_to_itree].
    - apply ruttc_ret; assumption.
    - unfold raise, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseOOM, trigger_cast; eapply ruttc_trigger';
        [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; exact (CutUB_rel (print_msg s)).
  Qed.

  Lemma unfold_run_exc_obs {A} (t : CFGtop A) :
    run_exc t ≅
      match observe t with
      | RetF a => Ret (inr a)
      | TauF u' => Tau (run_exc u')
      | VisF _ e k =>
          match exc_of_event e with
          | Some x => Ret (inl x)
          | None => Vis e (fun y => Tau (run_exc (k y)))
          end
      end.
  Proof using.
    unfold run_exc; rewrite unfold_iter.
    destruct (observe t) as [a | u' | X e k]; cbn.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - destruct (exc_of_event e) as [x |].
      + rewrite Eqit.bind_ret_l; reflexivity.
      + rewrite bind_vis; apply eqit_Vis; intros y; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma cutUB_exc_none {X} (e : CFGEtop X) :
    cutUB_rel e -> exc_of_event e = None.
  Proof using.
    intros Hcut; destruct Hcut; reflexivity.
  Qed.

  Lemma EqE_CFG_exc_of_event {A B} (e1 : CFGEtop A) (e2 : CFGEtop B) :
    EqE_CFG A B e1 e2 -> exc_of_event e1 = exc_of_event e2.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE |- *; try contradiction; try reflexivity; subst; reflexivity.
  Qed.

  Lemma refine_cfg_run_exc {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : CFGtop R1) (t2 : CFGtop R2) :
    refine_cfg RR t1 t2 ->
    refine_cfg (sum_rel Logic.eq RR) (run_exc t1) (run_exc t2).
  Proof using.
    revert t1 t2; ginit; gcofix CIH; intros t1 t2 HR.
    rewrite 2 unfold_run_exc_obs.
    punfold HR; red in HR.
    induction HR; pclearbot.
    - gstep; constructor; constructor; assumption.
    - gstep; constructor; gfinal; left; apply CIH; assumption.
    - rewrite (EqE_CFG_exc_of_event e1 e2 H).
      destruct (exc_of_event e2) as [x |].
      + gstep; constructor; constructor; reflexivity.
      + gstep; constructor; [exact H |].
        intros a b Hab; gstep; constructor; gfinal; left; apply CIH, H0, Hab.
    - rewrite tau_euttge, unfold_run_exc_obs; exact IHHR.
    - rewrite tau_euttge, unfold_run_exc_obs; exact IHHR.
    - rewrite (cutUB_exc_none e H); gstep; constructor; exact H.
    - inversion H.
  Qed.

  Lemma refine_cfg_denote_function (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs  : df_args df1 = df_args df2)
    (Hbody  : forall va, refine_cfg Logic.eq (denote_cfg (df_instrs df1) va)
                                             (denote_cfg (df_instrs df2) va)) :
    forall cc args,
      refine_cfg Logic.eq (denote_function df1 cc args) (denote_function df2 cc args).
  Proof using.
    intros cc args.
    unfold denote_function.
    rewrite Hproto.
    destruct (dc_param_attrs (df_prototype df2)) as [ret_attrs args_attrs].
    eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
    eapply ruttc_bind; [apply refine_cfg_refl | intros args' _ <-].
    eapply ruttc_bind; [unfold push_call_frame; rewrite Hargs; apply refine_cfg_refl | intros varg _ <-].
    eapply ruttc_bind.
    { eapply ruttc_weaken; cycle -1.
      - apply refine_cfg_run_exc; apply (Hbody (Some varg)).
      - auto.
      - auto.
      - auto.
      - auto.
      - intros r1 r2 [x1 x2 <- | y1 y2 <-]; reflexivity. }
    intros rv _ <-.
    eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
    apply refine_cfg_refl.
  Qed.

  Definition fn_ctx_refines (ctx1 ctx2 : IntMap function_denotation) : Prop :=
    forall k,
      option_rel (fun f1 f2 => forall cc args, refine_cfg Logic.eq (f1 cc args) (f2 cc args))
        (lookup k ctx1) (lookup k ctx2).

  Lemma cutUB_cfg_sum {A} (e : (CallE +' MCFGEtop) A) :
    cutUB_rel e <-> sum_pred1 (@FF1 CallE) (@cutUB_rel MCFGEtop _) A e.
  Proof using.
    split; intros H.
    - destruct H as [u]; constructor; exact (CutUB_rel u).
    - destruct H as [? ? [] | ? ? HC]; destruct HC as [u]; exact (CutUB_rel u).
  Qed.

  Lemma cutNone_cfg_sum {A} (e : (CallE +' MCFGEtop) A) :
    cutNone e <-> sum_pred1 (@FF1 CallE) (@cutNone MCFGEtop) A e.
  Proof using.
    split; intros H; [inversion H | destruct H as [? ? [] | ? ? HC]; inversion HC].
  Qed.

  Lemma refine_mcfg_denote_mcfg (ctx1 ctx2 : IntMap function_denotation)
    (dt : dtyp) (fv : dvalue) (args : list dvalue)
    (Hctx : fn_ctx_refines ctx1 ctx2) :
    refine_mcfg Logic.eq (denote_mcfg ctx1 dt fv args) (denote_mcfg ctx2 dt fv args).
  Proof using.
    unfold refine_mcfg, denote_mcfg.
    eapply ruttc_weaken with (Rcutl := cutUB_rel) (Rcutr := cutNone) (REv := EqE_MCFG) (RAns := EqA_MCFG); cycle -1.
    { eapply ruttc_mrec with (RCall := EqE_Call) (RCall' := EqA_Call).
      2: { cbn; auto. }
      intros A B [dt1 cc1 fv1 fas1] [dt2 cc2 fv2 fas2] HC.
      cbn in HC; destruct HC as (<- & <- & <- & <-).
      eapply ruttc_weaken with
        (Rcutl := cutUB_rel) (Rcutr := cutNone) (REv := EqE_CFG) (RAns := EqA_CFG)
        (RR := @Logic.eq (exc + dvalue)).
      { intros ? e Hcut; exact (proj1 (cutUB_cfg_sum e) Hcut). }
      { intros ? e Hcut; exact (proj1 (cutNone_cfg_sum e) Hcut). }
      { intros * HE; destruct e1 as [c1 | m1], e2 as [c2 | m2]; cbn in HE; try contradiction; constructor; exact HE. }
      { intros * HA; destruct HA; exact H. }
      { intros r1 r2 <-; cbn; reflexivity. }
      eapply ruttc_bind; [apply refine_cfg_refl | intros [] _ <-].
      unfold lookup_defn.
      destruct fv1 as [[p | | | | | | |] | |]; try apply refine_cfg_refl.
      pose proof (Hctx (ptr_to_int p)) as Hlk.
      destruct (lookup (ptr_to_int p) ctx1) as [f1 |],
               (lookup (ptr_to_int p) ctx2) as [f2 |]; inversion Hlk; subst.
      - apply H1.
      - apply refine_cfg_refl. }
    all: cbn; auto.
  Qed.

  Lemma refine_mcfg_interp_intrinsics {R} (t1 t2 : MCFGtop R) :
    refine_mcfg Logic.eq t1 t2 ->
    refine_mcfg Logic.eq (interp_intrinsics t1) (interp_intrinsics t2).
  Proof using.
    intros HR.
    apply ruttc_interp_itree; auto.
    - intros A1 e1 Hcut; destruct Hcut as [u]; reflexivity.
    - intros A2 e2 Hcut; inversion Hcut.
    - intros A1 A2 e1 e2 HEv.
      destruct e1 as [e1 | e1], e2 as [e2 | e2]; cbn in HEv; try contradiction.
      + cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger]; unfold trigger.
        apply ruttc_trigger; [cbn; exact HEv | intros a b Hab; exact Hab].
      + destruct e1 as [i1 | f1], e2 as [i2 | f2]; cbn in HEv; try contradiction.
        * destruct i1 as [dt1 fn1 args1 va1], i2 as [dt2 fn2 args2 va2].
          destruct HEv as (<- & <- & <- & <-).
          cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
          eapply ruttc_weaken; cycle -1; [apply refine_mcfg_refl | auto | auto | auto | auto |].
          intros r1 r2 <-; cbn; reflexivity.
        * cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger]; unfold trigger.
          apply ruttc_trigger; [cbn; exact HEv | intros a b Hab; exact Hab].
  Qed.

End EventRelations.

(** * 6. Provenance-Choice Model Semantics ([ProvE]) & [prog_refines] [PreOrder] *)

Variant ProvE : Type -> Type :=
  | FreshProv : ProvE N.

Section ModelSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  Existing Instance MemoryModelStateV.
  Existing Instance MemoryModelPrimitivesV.

  Definition ProvBotE : Type -> Type := ProvE +' (@MCFGEbot (@ParamsV IP IPT)).

  (** Collect all concrete provenance IDs occurring inside a [dvalue]. *)
  Definition ptr_provs (p : @ptr ProvenanceV (@PointerV IP)) : list N :=
    match snd p with
    | None => []
    | Some ps => ps
    end.

  Definition mem_bit_provs (b : @memory_bit (@ParamsV IP IPT)) : list N :=
    match b with
    | Bit_ptr p _ => ptr_provs p
    | Bit_psn | Bit_bit _ => []
    end.

  Definition dvalue_bv_provs {sz} (bv : @dvalue_bv (@ParamsV IP IPT) sz) : list N :=
    match bv with
    | BYTE_I _ => []
    | BYTE_Pointer p _ => ptr_provs p
    | BYTE_Mixed bits => flat_map mem_bit_provs bits
    end.

  Definition dvalue_base_provs (db : @dvalue_base (@ParamsV IP IPT)) : list N :=
    match db with
    | DVALUE_Pointer p => ptr_provs p
    | DVALUE_B _ bv => dvalue_bv_provs bv
    | _ => []
    end.

  Fixpoint dvalue_provs (dv : @dvalue (@ParamsV IP IPT)) : list N :=
    let fix list_provs (l : list (@dvalue (@ParamsV IP IPT))) : list N :=
      match l with
      | [] => []
      | x :: xs => dvalue_provs x ++ list_provs xs
      end
    in
    match dv with
    | DVALUE_Base db => dvalue_base_provs db
    | DVALUE_Struct _ fs => list_provs fs
    | DVALUE_Array _ es => list_provs es
    end.

  Definition bot_ans_provs {X} (e : @MCFGEbot (@ParamsV IP IPT) X) (a : X) : list N :=
    match e return X -> list N with
    | inl1 ec =>
        match ec in ExternalCallE Y return Y -> list N with
        | ExternalCall _ _ _ => dvalue_provs
        | IO_stdout _ => fun _ => []
        | IO_stderr _ => fun _ => []
        end
    | inr1 _ => fun _ => []
    end a.

  Lemma bot_ans_provs_eq {A B}
    (e1 : @MCFGEbot (@ParamsV IP IPT) A) (e2 : @MCFGEbot (@ParamsV IP IPT) B)
    (a1 : A) (a2 : B) :
    EqE_bot A B e1 e2 ->
    EqA_bot A B e1 a1 e2 a2 ->
    bot_ans_provs e1 a1 = bot_ans_provs e2 a2.
  Proof using.
    intros HE HA; destruct_sum2 e1 e2 HE;
      destruct e1; destruct e2; cbn in HE, HA |- *;
      try contradiction; subst; reflexivity.
  Qed.

  (** ** Model Memory & Fused Interpreter (Generalizing [interp_mcfg]) *)

  Fixpoint memM_interp_prov : @memM (@ParamsV IP IPT) _ ~> Monads.stateT state (itree ProvBotE) :=
    fun T m σ =>
      match m with
      | Mret x => Ret (σ, x)
      | Moom s => raiseOOM s
      | Mub s => raiseUB s
      | Merr s => raise s
      | Mget k => memM_interp_prov T (k σ) σ
      | Mput σ' k => memM_interp_prov T (k tt) σ'
      | Mchoose (Cnext_key _ align) k =>
          memM_interp_prov T
            (k (next_key_with_alignment σ.(state_memory_stack).(Memory_stack_memory) align))
            σ
      | Mchoose Cfresh_prov k =>
          ITree.bind (ITree.trigger (inl1 FreshProv)) (fun p =>
            memM_interp_prov T (k p)
              {| state_memory_stack := σ.(state_memory_stack);
                 state_provenance   := p |})
      | Mchoose Cexposed_prov k => memM_interp_prov T (k None) σ
      end.

  Arguments memM_interp_prov [T] _ _.

  Definition on_mem_prov {T} (f : Monads.stateT state (itree ProvBotE) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, rest) => ITree.bind (f m) (fun '(m', r) => Ret ((m', rest), r)).

  Definition lift_bot_prov {T} (t : itree MCFGEbot T) : itree ProvBotE T :=
    translate inr1 t.

  Definition on_ls_prov {T} (f : Monads.stateT (stack_frame * stack) (itree MCFGEbot) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, (ls, g)) =>
      ITree.bind (lift_bot_prov (f ls)) (fun '(ls', r) => Ret ((m, (ls', g)), r)).

  Definition on_genv_prov {T} (f : Monads.stateT global_env (itree MCFGEbot) T)
    : Monads.stateT FusedS (itree ProvBotE) T :=
    fun '(m, (ls, g)) =>
      ITree.bind (lift_bot_prov (f g)) (fun '(g', r) => Ret ((m, (ls, g')), r)).

  Definition fused_trigger_prov {F} `{F -< ProvBotE}
    : forall T, F T -> Monads.stateT FusedS (itree ProvBotE) T :=
    fun _ e s => ITree.bind (ITree.trigger (subevent _ e)) (fun r => Ret (s, r)).

  Definition fused_intrinsic_prov : IntrinsicE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_mem_prov (handle_intrinsic memM_interp_prov e).
  Definition fused_global_prov : GlobalE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_genv_prov (handle_global_debug e).
  Definition fused_local_prov : LocalE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_ls_prov (handle_local_stack handle_local_debug e).
  Definition fused_stack_prov : StackE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_ls_prov (handle_stack e).
  Definition fused_memory_prov : MemoryE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e => on_mem_prov (handle_memory memM_interp_prov e).
  Definition fused_draw_prov : DrawE ~> Monads.stateT FusedS (itree ProvBotE) :=
    fun T e s => ITree.bind (lift_bot_prov (handle_draw e)) (fun r => Ret (s, r)).

  Definition interp_vellvm_prov_h : MCFGEtop ~> Monads.stateT FusedS (itree ProvBotE) :=
    case_ (fused_trigger_prov (F := ExternalCallE))
   (case_ fused_intrinsic_prov
   (case_ fused_global_prov
   (case_ (case_ fused_local_prov fused_stack_prov)
   (case_ fused_memory_prov
   (case_ fused_draw_prov
   (case_ (fused_trigger_prov (F := OOME))
   (case_ (fused_trigger_prov (F := LLVMExcE))
   (case_ (fused_trigger_prov (F := UBE))
   (case_ (fused_trigger_prov (F := DebugE))
          (fused_trigger_prov (F := FailureE))))))))))).

  Arguments interp_vellvm_prov_h [T] _ _.

  Definition interp_mcfg_model {R} (t : MCFGtop R) (s : FusedS) : itree ProvBotE (Res R) :=
    interp_state interp_vellvm_prov_h (interp_intrinsics t) s.

  Definition init_fused_state : FusedS :=
    (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).

  Definition run_mcfg_model (ret_typ : dtyp) (entry : function_id)
    (args : list dvalue) (M : CFG.mcfg dtyp) : itree ProvBotE (Res dvalue) :=
    interp_mcfg_model (denote_vellvm ret_typ entry args M) init_fused_state.

  (** ** Deterministic Specialization Equivalence ([interp_mcfg_model] -> [interp_mcfg]) *)

  Definition det_prov_h
    : ProvBotE ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT))) :=
    case_
      ((fun T (e : ProvE T) (pr : N) =>
          match e in ProvE Y return itree (@MCFGEbot (@ParamsV IP IPT)) (N * Y) with
          | FreshProv => let p' := N.succ pr in Ret (p', p')
          end) : ProvE ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT))))
      ((fun T (e : @MCFGEbot (@ParamsV IP IPT) T) (pr : N) =>
          ITree.bind (ITree.trigger e) (fun r => Ret (pr, r)))
       : @MCFGEbot (@ParamsV IP IPT) ~> Monads.stateT N (itree (@MCFGEbot (@ParamsV IP IPT)))).

  Lemma det_prov_h_inl1 (pr : N) :
    det_prov_h N (inl1 FreshProv) pr = Ret (N.succ pr, N.succ pr).
  Proof using. reflexivity. Qed.

  Lemma det_prov_h_inr1 {X} (e : @MCFGEbot (@ParamsV IP IPT) X) (pr : N) :
    det_prov_h X (inr1 e) pr = ITree.bind (ITree.trigger e) (fun r => Ret (pr, r)).
  Proof using. reflexivity. Qed.

  Local Opaque det_prov_h.

  Lemma interp_det_prov_lift_bot {R} (t : itree MCFGEbot R) (pr : N) :
    interp_state det_prov_h (lift_bot_prov t) pr ≈ ITree.map (fun r => (pr, r)) t.
  Proof using.
    unfold lift_bot_prov, ITree.map.
    revert t pr; ginit; gcofix CIH; intros t pr.
    destruct (observe t) as [rv | m | X e k] eqn:Hot.
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h];
          rewrite interp_state_ret; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; reflexivity.
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h];
          rewrite interp_state_tau; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; gfinal; left; exact (CIH m pr).
    - gclo; econstructor; auto_ctrans_eq.
      + rewrite unfold_translate, Hot; cbn -[det_prov_h].
        rewrite interp_state_vis, det_prov_h_inr1; unfold ITree.trigger.
        rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity.
      + rewrite unfold_bind, Hot; cbn; reflexivity.
      + gstep; constructor; intros x.
        gclo; econstructor; auto_ctrans_eq.
        * rewrite 2 Eqit.bind_ret_l; cbn [fst snd]; apply eqit_Tau_l; reflexivity.
        * reflexivity.
        * gfinal; left; exact (CIH (k x) pr).
  Qed.

  Local Transparent det_prov_h.

  Fixpoint memM_put_preserves_prov {R} (m : memM R) (σ : state) : Prop :=
    match m with
    | Mret _ | Moom _ | Mub _ | Merr _ => True
    | Mget k => memM_put_preserves_prov (k σ) σ
    | Mput σ' k =>
        σ'.(state_provenance) = σ.(state_provenance) /\
        memM_put_preserves_prov (k tt) σ'
    | Mchoose (Cnext_key _ align) k =>
        memM_put_preserves_prov
          (k (next_key_with_alignment σ.(state_memory_stack).(Memory_stack_memory) align)) σ
    | Mchoose Cfresh_prov k =>
        forall p,
          memM_put_preserves_prov (k p)
            {| state_memory_stack := σ.(state_memory_stack);
               state_provenance   := p |}
    | Mchoose Cexposed_prov k => memM_put_preserves_prov (k None) σ
    end.

  Definition memM_wf_prov {R} (m : memM R) : Prop :=
    forall σ, memM_put_preserves_prov m σ.

  Local Lemma memM_put_preserves_prov_bind {X Y}
    (m : memM X) (f : X -> memM Y) (σ : state)
    (Hm : memM_put_preserves_prov m σ)
    (Hf : forall x, memM_wf_prov (f x)) :
    memM_put_preserves_prov (ExtLib.Structures.Monad.bind m f) σ.
  Proof using.
    revert σ Hm; induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ Hm; cbn in *.
    - exact (Hf x σ).
    - exact I.
    - exact I.
    - exact I.
    - exact (IH σ σ Hm).
    - destruct Hm as [Heq Hm']; exact (conj Heq (IH tt σ' Hm')).
    - destruct c as [sz align | |];
        [exact (IH _ σ Hm) | intros p; exact (IH p _ (Hm p)) | exact (IH None σ Hm)].
  Qed.

  Local Lemma memM_wf_prov_bind {X Y}
    (m : memM X) (f : X -> memM Y)
    (Hm : memM_wf_prov m) (Hf : forall x, memM_wf_prov (f x)) :
    memM_wf_prov (ExtLib.Structures.Monad.bind m f).
  Proof using.
    intros σ; exact (memM_put_preserves_prov_bind m f σ (Hm σ) Hf).
  Qed.

  Local Lemma memM_wf_prov_ret {X} (x : X) :
    memM_wf_prov (ExtLib.Structures.Monad.ret x).
  Proof using.
    intros σ; exact I.
  Qed.

  Local Lemma memM_wf_prov_lift {X} (c : EOU X) :
    memM_wf_prov (Vellvm.Semantics.Interfaces.Memory.lift c).
  Proof using.
    destruct c; intros σ; exact I.
  Qed.

  Local Lemma memM_wf_prov_loop_monad {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (loop_monad f l).
  Proof using.
    induction l as [| a l' IH]; cbn [loop_monad];
      [apply memM_wf_prov_ret
      | apply memM_wf_prov_bind; [exact (Hf a) | intros _; exact IH]].
  Qed.

  Local Lemma memM_wf_prov_map_monad {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (map_monad f l).
  Proof using.
    induction l as [| a l' IH]; cbn [map_monad]; [apply memM_wf_prov_ret |].
    apply memM_wf_prov_bind; [exact (Hf a) | intros b].
    apply memM_wf_prov_bind; [exact IH | intros bs; apply memM_wf_prov_ret].
  Qed.

  Local Lemma memM_wf_prov_map_monad_acc {A B} (f : A -> memM B) (l : list A)
    (Hf : forall a, memM_wf_prov (f a)) :
    memM_wf_prov (map_monad_acc f l).
  Proof using.
    unfold map_monad_acc.
    lazymatch goal with
    | |- memM_wf_prov (?go [] l) =>
        cut (forall acc : list B, memM_wf_prov (go acc l)); [intros H; exact (H []) |]
    end.
    induction l as [| a l' IH]; intros acc;
      [apply memM_wf_prov_ret
      | apply memM_wf_prov_bind; [exact (Hf a) | intros b; exact (IH (b :: acc))]].
  Qed.

  Local Lemma Read_byte_wf_prov (p : ptr) :
    memM_wf_prov (Read_byte p).
  Proof using.
    unfold Read_byte, read_byte_raw; cbn zeta; apply memM_wf_prov_bind.
    - intros σ;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind get
             ExtLib.Structures.Monad.ret memM_put_preserves_prov];
        destruct (read_byte_raw_mem _ _); exact I.
    - intros [b0 aid]; destruct (access_allowed _ _); intros σ; exact I.
  Qed.

  Local Lemma Write_byte_wf_prov (p : ptr) (b : memory_byte) :
    memM_wf_prov (Write_byte p b).
  Proof using.
    unfold Write_byte, read_byte_raw; cbn zeta; apply memM_wf_prov_bind.
    - intros σ;
        cbn [ExtLib.Structures.Monad.bind memS_mon memS_bind get
             ExtLib.Structures.Monad.ret memM_put_preserves_prov];
        destruct (read_byte_raw_mem _ _); exact I.
    - intros [b0 aid]; destruct (access_allowed _ _); [| intros σ; exact I].
      unfold set_byte_raw; apply memM_wf_prov_bind;
        [intros σ; exact I | intros m0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma get_free_block_wf_prov (size align : N) (pr : provenance) :
    memM_wf_prov (get_free_block size align pr).
  Proof using.
    unfold get_free_block; cbn zeta;
      apply memM_wf_prov_bind; [intros σ; exact I | intros addr].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros p].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs; apply memM_wf_prov_ret].
  Qed.

  Local Lemma add_block_wf_prov (aid : allocationId) (p : ptr) (ptrs : list ptr) (init_bytes : list memory_byte) :
    memM_wf_prov (add_block aid p ptrs init_bytes).
  Proof using.
    unfold add_block; cbn zeta.
    apply memM_wf_prov_bind; [intros σ; exact I | intros m0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Allocate_bytes_with_pr_wf_prov (init_bytes : list memory_byte) (align : N) (pr : provenance) :
    memM_wf_prov (Allocate_bytes_with_pr init_bytes align pr).
  Proof using.
    unfold Allocate_bytes_with_pr; cbn zeta.
    apply memM_wf_prov_bind; [apply get_free_block_wf_prov | intros [p ptrs]].
    apply memM_wf_prov_bind; [| intros u0; apply memM_wf_prov_ret].
    unfold add_block_to_stack, add_ptrs_to_frame.
    apply memM_wf_prov_bind; [apply add_block_wf_prov | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Malloc_bytes_with_pr_wf_prov (init_bytes : list memory_byte) (align : N) (pr : provenance) :
    memM_wf_prov (Malloc_bytes_with_pr init_bytes align pr).
  Proof using.
    unfold Malloc_bytes_with_pr; cbn zeta.
    apply memM_wf_prov_bind; [apply get_free_block_wf_prov | intros [p ptrs]].
    apply memM_wf_prov_bind; [| intros u0; apply memM_wf_prov_ret].
    unfold add_block_to_heap, add_ptrs_to_heap.
    apply memM_wf_prov_bind; [apply add_block_wf_prov | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma Mempop_wf_prov :
    memM_wf_prov Mempop.
  Proof using.
    unfold Mempop; apply memM_wf_prov_bind.
    - unfold get_frame; apply memM_wf_prov_bind;
        [intros σ; exact I | intros [f0 | s0 f0]; apply memM_wf_prov_ret].
    - intros f; apply memM_wf_prov_bind.
      + unfold app_frame_stack_eob; apply memM_wf_prov_bind; [intros σ; exact I | intros fs].
        apply memM_wf_prov_bind;
          [apply memM_wf_prov_lift | intros fs' σ; exact (conj Logic.eq_refl I)].
      + intros u0 σ; exact (conj Logic.eq_refl I).
  Qed.

  Local Lemma Free_wf_prov (p : ptr) :
    memM_wf_prov (Free p).
  Proof using.
    unfold Free; cbn zeta; apply memM_wf_prov_bind; [intros σ; exact I | intros h].
    lazymatch goal with
    | |- memM_wf_prov match ?e with _ => _ end => destruct e as [blk |]
    end; [| intros σ; exact I].
    cbn zeta; apply memM_wf_prov_bind;
      [intros σ; exact (conj Logic.eq_refl I) | intros u0 σ; exact (conj Logic.eq_refl I)].
  Qed.

  Local Lemma read_bytes_wf_prov (p : ptr) (size : N) :
    memM_wf_prov (read_bytes p size).
  Proof using.
    unfold read_bytes; cbn [read_byte MemoryModelPrimitivesV].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs].
    apply memM_wf_prov_map_monad_acc, Read_byte_wf_prov.
  Qed.

  Local Lemma write_bytes_wf_prov (p : ptr) (bytes : list memory_byte) :
    memM_wf_prov (write_bytes p bytes).
  Proof using.
    unfold write_bytes; cbn zeta; cbn [write_byte MemoryModelPrimitivesV].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros ptrs].
    apply memM_wf_prov_loop_monad; intros [q b]; exact (Write_byte_wf_prov q b).
  Qed.

  Local Lemma convert_impure_base_wf_prov
    (conv : impure_conversion) (tf : dtyp_base) (dv : dvalue_base) (tt0 : dtyp_base) :
    memM_wf_prov (convert_impure_base conv tf dv tt0).
  Proof using.
    unfold convert_impure_base; destruct conv.
    - apply memM_wf_prov_bind.
      + unfold assert_inttoptr_types_ok; destruct tf, tt0; intros σ; exact I.
      + intros u0; destruct dv; apply memM_wf_prov_lift.
    - destruct dv, tt0; try apply memM_wf_prov_lift; intros σ; exact I.
    - destruct dv, tt0; try apply memM_wf_prov_lift; intros σ; exact I.
    - intros σ; exact I.
  Qed.

  Local Lemma convert_impure_wf_prov
    (conv : impure_conversion) (tf : dtyp) (dv : dvalue) (tt0 : dtyp) :
    memM_wf_prov (convert_impure conv tf dv tt0).
  Proof using.
    unfold convert_impure; destruct dv as [db | ? ? | vc elts]; try (intros σ; exact I).
    - destruct (get_base_conversion_type tf tt0) as [[tf' tt'] |]; [| intros σ; exact I].
      cbn [Functor.fmap Functor_Monad].
      apply memM_wf_prov_bind; [apply convert_impure_base_wf_prov | intros db'; apply memM_wf_prov_ret].
    - destruct vc; [| intros σ; exact I].
      destruct (get_vector_conversion_type tf tt0) as [[tf' tt'] |]; [| intros σ; exact I].
      apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros elts'].
      apply memM_wf_prov_bind.
      + apply memM_wf_prov_map_monad; intros v; apply convert_impure_base_wf_prov.
      + intros val; apply memM_wf_prov_ret.
  Qed.

  Local Lemma handle_memoryM_wf_prov {T} (e : MemoryE T) :
    memM_wf_prov (handle_memoryM e).
  Proof using.
    destruct e as [| | dt n al | dt a | dt a v | ct tf v tt0]; cbn [handle_memoryM].
    - intros σ; exact (conj Logic.eq_refl I).
    - exact Mempop_wf_prov.
    - cbn zeta; apply memM_wf_prov_bind; [| intros p; apply memM_wf_prov_ret].
      unfold allocate_dtyp; destruct (dtyp_eqb dt DTYPE_Void); [intros σ; exact I |].
      cbn zeta; unfold allocate_bytes; cbn [allocate_bytes_with_pr MemoryModelPrimitivesV].
      apply memM_wf_prov_bind; [intros σ p; exact I | intros pr; apply Allocate_bytes_with_pr_wf_prov].
    - destruct a as [[p | | | | | | |] | |]; try (intros σ; exact I).
      unfold read_dvalue; apply memM_wf_prov_bind;
        [apply read_bytes_wf_prov | intros bs; apply memM_wf_prov_lift].
    - destruct a as [[p | | | | | | |] | |]; try (intros σ; exact I).
      unfold write_dvalue; apply memM_wf_prov_bind;
        [apply memM_wf_prov_lift | intros bs; apply write_bytes_wf_prov].
    - apply convert_impure_wf_prov.
  Qed.

  Local Lemma handle_memtransfer_wf_prov (overlap_ok : bool) (args : list dvalue_base) :
    memM_wf_prov (handle_memtransfer overlap_ok args).
  Proof using.
    unfold handle_memtransfer; cbn zeta.
    destruct args as [| dst [| src [| len [| vol rest]]]]; try (intros σ; exact I).
    destruct vol, rest; try (intros σ; exact I).
    apply memM_wf_prov_bind.
    - destruct len; intros σ; exact I.
    - intros size; destruct dst, src; try (intros σ; exact I);
        try (destruct (size =? 0)%N; intros σ; exact I).
      destruct overlap_ok.
      + unfold memmove; apply memM_wf_prov_bind;
          [apply read_bytes_wf_prov | intros bs; apply write_bytes_wf_prov].
      + unfold memcpy; destruct (orb _ _); [| intros σ; exact I].
        apply memM_wf_prov_bind;
          [apply read_bytes_wf_prov | intros bs; apply write_bytes_wf_prov].
  Qed.

  Local Lemma handle_memset_wf_prov (args : list dvalue_base) :
    memM_wf_prov (handle_memset args).
  Proof using.
    unfold handle_memset.
    destruct args as [| dst [| val [| len [| vol rest]]]]; try (intros σ; exact I).
    destruct vol, rest; try (intros σ; exact I).
    apply memM_wf_prov_bind.
    - destruct val; try (intros σ; exact I).
      destruct (Pos.eqb _ 8); intros σ; exact I.
    - intros byte; apply memM_wf_prov_bind.
      + destruct len; intros σ; exact I.
      + intros size; destruct dst; try (intros σ; exact I).
        * unfold memset; apply write_bytes_wf_prov.
        * destruct (size =? 0)%N; intros σ; exact I.
  Qed.

  Local Lemma handle_malloc_wf_prov (args : list dvalue_base) (align : N) :
    memM_wf_prov (handle_malloc args align).
  Proof using.
    unfold handle_malloc.
    destruct args as [| a0 rest]; [intros σ; exact I |].
    destruct a0, rest; try (intros σ; exact I);
      (unfold malloc_bytes; cbn [malloc_bytes_with_pr MemoryModelPrimitivesV];
       apply memM_wf_prov_bind; [intros σ p; exact I | intros pr; apply Malloc_bytes_with_pr_wf_prov]).
  Qed.

  Local Lemma handle_free_wf_prov (args : list dvalue_base) :
    memM_wf_prov (handle_free args).
  Proof using.
    unfold handle_free; cbn [free MemoryModelPrimitivesV].
    destruct args as [| a0 rest]; [intros σ; exact I |].
    destruct a0, rest; try (intros σ; exact I).
    destruct (_ =? _)%Z; [apply memM_wf_prov_ret | apply Free_wf_prov].
  Qed.

  Local Lemma handle_intrinsicM_wf_prov {T} (e : IntrinsicE T) :
    memM_wf_prov (handle_intrinsicM e).
  Proof using.
    destruct e as [t name args ?]; cbn [handle_intrinsicM].
    apply memM_wf_prov_bind; [apply memM_wf_prov_lift | intros args'].
    destruct (is_memcpy_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memtransfer_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (is_memmove_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memtransfer_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (is_memset_name name);
      [apply memM_wf_prov_bind;
       [apply handle_memset_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (Numeric.Rocqlib.proj_sumbool (string_dec name "malloc"));
      [apply memM_wf_prov_bind;
       [apply handle_malloc_wf_prov | intros r; apply memM_wf_prov_ret] |].
    destruct (Numeric.Rocqlib.proj_sumbool (string_dec name "free"));
      [apply memM_wf_prov_bind;
       [apply handle_free_wf_prov | intros r; apply memM_wf_prov_ret]
      | intros σ; exact I].
  Qed.

  Lemma memM_interp_prov_det {R} (m : memM R) (σ : state)
    (Hwf : memM_put_preserves_prov m σ) :
    interp_state det_prov_h (memM_interp_prov m σ) σ.(state_provenance) ≈
      ITree.map (fun '(σ', r) => (σ'.(state_provenance), (σ', r))) (memM_interp m σ).
  Proof using.
    revert σ Hwf; induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ Hwf;
      cbn [memM_interp_prov memM_interp memM_put_preserves_prov
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree] in Hwf |- *.
    - rewrite interp_state_ret; unfold ITree.map; rewrite Eqit.bind_ret_l; reflexivity.
    - unfold raiseOOM, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - unfold raiseUB, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - unfold raise, trigger_cast, ITree.map;
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; apply eqit_Vis; intros [].
    - exact (IH σ σ Hwf).
    - destruct Hwf as [Heq Hwf']; rewrite <- Heq; exact (IH tt σ' Hwf').
    - destruct c as [sz align | |];
        cbn [memM_interp_prov memM_interp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      + exact (IH _ σ Hwf).
      + rewrite interp_state_bind, interp_state_trigger, det_prov_h_inl1, Eqit.bind_ret_l.
        unfold fresh_provenance, ITree.map;
          cbn [next_provenance ProvenanceV MemoryModelPrimitivesV ParamsV
               ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite Eqit.bind_bind, Eqit.bind_ret_l.
        exact (IH (N.succ (state_provenance σ))
                  {| state_memory_stack := state_memory_stack σ;
                     state_provenance   := N.succ (state_provenance σ) |}
                  (Hwf (N.succ (state_provenance σ)))).
      + exact (IH None σ Hwf).
  Qed.

  Lemma interp_vellvm_prov_h_det {T} (e : MCFGEtop T) (s : FusedS) :
    interp_state det_prov_h (interp_vellvm_prov_h e s) (fst s).(state_provenance) ≈
      ITree.map (fun '(s', r) => ((fst s').(state_provenance), (s', r))) (interp_vellvm_h e s).
  Proof using.
    destruct s as [m [[sf stk] g]]; cbn [fst].
    unfold interp_vellvm_prov_h, interp_vellvm_h.
    destruct_sum1 e; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    - (* ExternalCallE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* IntrinsicE *)
      unfold fused_intrinsic_prov, fused_intrinsic, on_mem_prov, on_mem, handle_intrinsic;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, (memM_interp_prov_det _ _ (handle_intrinsicM_wf_prov e m)).
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [m' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* GlobalE *)
      unfold fused_global_prov, fused_global, on_genv_prov, on_genv;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [g' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* LocalE *)
      unfold fused_local_prov, fused_local, on_ls_prov, on_ls;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [ls' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* StackE *)
      unfold fused_stack_prov, fused_stack, on_ls_prov, on_ls;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [ls' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* MemoryE *)
      unfold fused_memory_prov, fused_memory, on_mem_prov, on_mem, handle_memory;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, (memM_interp_prov_det _ _ (handle_memoryM_wf_prov e m)).
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros [m' r]; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* DrawE *)
      unfold fused_draw_prov, fused_draw;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite interp_state_bind, interp_det_prov_lift_bot.
      unfold ITree.map; rewrite !Eqit.bind_bind.
      apply eutt_eq_bind; intros r; cbn [fst].
      rewrite !Eqit.bind_ret_l; cbn [fst snd]; rewrite interp_state_ret; reflexivity.
    - (* OOME *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* LLVMExcE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* UBE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* DebugE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
    - (* FailureE *)
      unfold fused_trigger_prov, fused_trigger, ITree.map;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite interp_state_bind, interp_state_trigger;
        unfold det_prov_h, subevent, resum;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        unfold resum, ReSum_id, id_, Id_IFun;
        cbn -[print_msg ITree.trigger interp_state ITree.bind];
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        rewrite Eqit.bind_bind, bind_trigger; symmetry;
        apply eqit_Vis; intros x;
        rewrite Eqit.bind_ret_l, interp_state_ret, Eqit.bind_ret_l; reflexivity.
  Qed.

  Local Opaque det_prov_h.

  Lemma interp_vellvm_prov_h_det_rel {T} (e : MCFGEtop T) (s : FusedS) :
    eutt (fun '(pr', sx1) (sx2 : FusedS * T) => pr' = (fst (fst sx2)).(state_provenance) /\ sx1 = sx2)
      (interp_state det_prov_h (interp_vellvm_prov_h e s) (fst s).(state_provenance))
      (interp_vellvm_h e s).
  Proof using.
    rewrite interp_vellvm_prov_h_det; unfold ITree.map.
    bind_ret_r2_eutt.
    eapply Eqit.eqit_bind'; [reflexivity |].
    intros [s' r] ? <-; apply Eqit.eqit_Ret; split; reflexivity.
  Qed.

  Theorem interp_mcfg_model_det {R} (t : MCFGtop R) (s : FusedS) :
    ITree.map snd (interp_state det_prov_h (interp_mcfg_model t s) (fst s).(state_provenance)) ≈
      interp_mcfg t s.
  Proof using.
    unfold interp_mcfg_model, interp_mcfg, ITree.map.
    generalize (interp_intrinsics t) as u; intros u.
    revert u s; ginit; gcofix CIH; intros u s.
    destruct (observe u) as [rv | m | X e k] eqn:Hou.
    - assert (Hu : u ≅ Ret rv) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, 2 interp_state_ret, Eqit.bind_ret_l; reflexivity.
      + rewrite Hu, interp_state_ret; reflexivity.
      + gstep; constructor; reflexivity.
    - assert (Hu : u ≅ Tau m) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, 2 interp_state_tau, Eqit.bind_tau; reflexivity.
      + rewrite Hu, interp_state_tau; reflexivity.
      + gstep; constructor; gfinal; left; exact (CIH m s).
    - assert (Hu : u ≅ Vis e k) by (rewrite (itree_eta u), Hou; reflexivity).
      gclo; econstructor; auto_ctrans_eq.
      + rewrite Hu, interp_state_vis;
          cbn [ExtLib.Structures.Monad.bind Monad_itree];
          rewrite interp_state_bind, Eqit.bind_bind; reflexivity.
      + rewrite Hu, interp_state_vis;
          cbn [ExtLib.Structures.Monad.bind Monad_itree]; reflexivity.
      + guclo eqit_clo_bind; econstructor.
        * exact (interp_vellvm_prov_h_det_rel e s).
        * intros [pr' [s' x]] [s2 x2] [-> Hsx]; inversion Hsx; subst s2 x2; clear Hsx; cbn [fst snd].
          gclo; econstructor; auto_ctrans_eq.
          -- rewrite interp_state_tau, Eqit.bind_tau; reflexivity.
          -- reflexivity.
          -- gstep; constructor; gfinal; left; exact (CIH (k x) s').
  Qed.

  (** ** Coinductive Provenance-Elastic Refinement ([refine_prov]) *)

  Definition is_ub_bot {X} (e : MCFGEbot X) : bool :=
    match e with
    | inr1 (inl1 (ThrowOOM _)) => true
    | inr1 (inr1 (inr1 (inl1 (ThrowUB _)))) => true
    | _ => false
    end.

  Definition is_ub_prov {X} (e : ProvBotE X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 b => is_ub_bot b
    end.

  Lemma EqE_bot_is_ub {A B} (b1 : MCFGEbot A) (b2 : MCFGEbot B) :
    EqE_bot A B b1 b2 -> is_ub_bot b1 = is_ub_bot b2.
  Proof using.
    intros HE; destruct_sum2 b1 b2 HE;
      destruct b1; destruct b2; reflexivity.
  Qed.

  Definition match_vis_both {R1 R2}
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (U : list N)
    {X1} (e1 : ProvBotE X1) (k1 : X1 -> itree ProvBotE R1)
    {X2} (e2 : ProvBotE X2) (k2 : X2 -> itree ProvBotE R2) : Prop :=
    match e1 return (X1 -> itree ProvBotE R1) -> Prop with
    | inl1 p1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R2) -> Prop with
        | inl1 p2 => fun k2' =>
            match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R1) -> Prop with
            | FreshProv => fun k1'' =>
                match p2 in ProvE Y2 return (Y2 -> itree ProvBotE R2) -> Prop with
                | FreshProv => fun k2'' =>
                    forall p : N, ~ In p U -> r (p :: U) (k1'' p) (k2'' p)
                end k2'
            end k1'
        | inr1 _ => fun _ => False
        end k2
    | inr1 b1 => fun k1' =>
        match e2 return (X2 -> itree ProvBotE R2) -> Prop with
        | inl1 _ => fun _ => False
        | inr1 b2 => fun k2' =>
            EqE_bot _ _ b1 b2 /\
            forall a1 a2, EqA_bot _ _ b1 a1 b2 a2 ->
              r (bot_ans_provs b1 a1 ++ U) (k1' a1) (k2' a2)
        end k2
    end k1.

  Definition rp_step_body {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (U : list N)
    (ot1 : itree' ProvBotE R1) (ot2 : itree' ProvBotE R2) (t2 : itree ProvBotE R2) : Prop :=
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
        is_ub_prov e1 = true
        \/ (match e1 with
            | inl1 p1 =>
                match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R1) -> Prop with
                | FreshProv => fun k1' =>
                    forall p : N, ~ In p U -> r (p :: U) (k1' p) t2
                end
            | inr1 _ => fun _ => False
            end k1)
        \/ (match ot2 with
            | VisF _ e2 k2 => match_vis_both r U e1 k1 e2 k2
            | _ => False
            end)
    end.

  Inductive refine_prov_ {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop :=
  | RP_Step U t1 t2 :
      rp_step_body RR r U (observe t1) (observe t2) t2 ->
      refine_prov_ RR r U t1 t2
  | RP_TauL U t1 m1 t2 :
      observe t1 = TauF m1 ->
      refine_prov_ RR r U m1 t2 ->
      refine_prov_ RR r U t1 t2
  | RP_TauR U t1 t2 m2 :
      observe t2 = TauF m2 ->
      refine_prov_ RR r U t1 m2 ->
      refine_prov_ RR r U t1 t2.

  Lemma refine_prov__mon {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    monotone3 (refine_prov_ RR).
  Proof using.
    intros U t1 t2 r r' IN LE.
    induction IN as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH].
    - apply RP_Step.
      unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left.
          destruct e1 as [p1 | b1]; [| contradiction].
          destruct p1; intros p Hp; apply LE, Hleft, Hp.
        * right; right.
          destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; apply LE, Hboth, Hp.
          -- destruct Hboth as [HE HA]; split; [exact HE | intros a1 a2 Ha; apply LE, HA, Ha].
    - eapply RP_TauL; [exact Ht1 | exact IH].
    - eapply RP_TauR; [exact Ht2 | exact IH].
  Qed.
  #[local] Hint Resolve refine_prov__mon : paco.

  Definition refine_prov {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) : Prop :=
    paco3 (refine_prov_ RR) bot3 U t1 t2.

  Lemma refine_prov_antitone {R1 R2} (RR1 RR2 : list N -> R1 -> R2 -> Prop)
    (HRR : forall U U' r1 r2, incl U U' -> RR1 U r1 r2 -> RR2 U' r1 r2) :
    forall U U' t1 t2,
      incl U U' ->
      refine_prov RR1 U t1 t2 ->
      refine_prov RR2 U' t1 t2.
  Proof using.
    pcofix CIH.
    intros U U' t1 t2 Hincl Hrel.
    pstep; punfold Hrel.
    revert U' Hincl; induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros U' Hincl.
    - apply RP_Step; unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; eapply HRR; eassumption.
      + destruct (observe t2); try contradiction; pclearbot; right; eapply CIH; eassumption.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp.
          assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
          specialize (Hleft p HpU); pclearbot; right; eapply CIH; [| exact Hleft].
          intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
        * right; right; destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp.
             assert (HpU : ~ In p U) by (intros Hx; apply Hp, Hincl, Hx).
             specialize (Hboth p HpU); pclearbot; right; eapply CIH; [| exact Hboth].
             intros z [<- | Hz]; [left; reflexivity | right; apply Hincl, Hz].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; eapply CIH; [| exact HA].
             intros z Hz; apply in_app_iff in Hz; apply in_app_iff.
             destruct Hz as [Hz | Hz]; [left; exact Hz | right; apply Hincl, Hz].
    - eapply RP_TauL; [exact Ht1 | apply IH, Hincl].
    - eapply RP_TauR; [exact Ht2 | apply IH, Hincl].
  Qed.

  Lemma refine_prov_inv_Tau_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    U (m1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U (Tau m1) t2 ->
    refine_prov RR U m1 t2.
  Proof using.
    intros H; punfold H.
    remember (Tau m1) as tm1 eqn:Etm1.
    assert (Hot1 : observe tm1 = TauF m1) by (subst tm1; reflexivity).
    clear Etm1.
    revert m1 Hot1; induction H as [U t1 t2 Hstep | U t1 m1' t2 Ht1 Hrel _ | U t1 t2 m2 Ht2 _ IH];
      intros m1 Hot1.
    - unfold rp_step_body in Hstep; rewrite Hot1 in Hstep.
      destruct (observe t2) as [x2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
      pclearbot; punfold Hstep.
      pstep; eapply RP_TauR; [exact Hot2 | eapply refine_prov__mon; [exact Hstep | auto]].
    - rewrite Hot1 in Ht1; inversion Ht1; subst m1'.
      pstep; eapply refine_prov__mon; [exact Hrel | auto].
    - specialize (IH m1 Hot1); punfold IH.
      pstep; eapply RP_TauR; [exact Ht2 | eapply refine_prov__mon; [exact IH | auto]].
  Qed.

  Lemma observe_bind {E : Type -> Type} {R S : Type}
    (t : itree E R) (k : R -> itree E S) :
    observe (ITree.bind t k) =
      match observe t with
      | RetF r => observe (k r)
      | TauF m => TauF (ITree.bind m k)
      | VisF _ e h => VisF e (fun x => ITree.bind (h x) k)
      end.
  Proof using.
    unfold ITree.bind, ITree.subst; unfold observe at 1; cbn.
    destruct (observe t); reflexivity.
  Qed.

  Lemma observe_translate {E F : Type -> Type} {R : Type}
    (h : E ~> F) (t : itree E R) :
    observe (translate h t) =
      match observe t with
      | RetF r => RetF r
      | TauF m => TauF (translate h m)
      | VisF _ e k => VisF (h _ e) (fun x => translate h (k x))
      end.
  Proof using.
    unfold translate; unfold observe at 1; cbn; destruct (observe t); reflexivity.
  Qed.

  Lemma eqitF_inv_Ret_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {vsim : (itree E R1 -> itree E R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    (r1 : R1) (ot2 : itree' E R2) :
    eqitF RR false false vsim sim (RetF r1) ot2 ->
    exists r2 : R2, ot2 = RetF r2 /\ RR r1 r2.
  Proof using.
    intros H.
    change (match RetF r1 : itree' E R1 with
            | RetF x1 => exists r2 : R2, ot2 = RetF r2 /\ RR x1 r2
            | _ => True
            end).
    generalize (RetF r1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [x1 x2 Hrr | | | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists x2; split; [reflexivity | exact Hrr].
  Qed.

  Lemma eqitF_inv_Tau_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {vsim : (itree E R1 -> itree E R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    (m1 : itree E R1) (ot2 : itree' E R2) :
    eqitF RR false false vsim sim (TauF m1) ot2 ->
    exists m2 : itree E R2, ot2 = TauF m2 /\ sim m1 m2.
  Proof using.
    intros H.
    change (match TauF m1 : itree' E R1 with
            | TauF u1 => exists m2 : itree E R2, ot2 = TauF m2 /\ sim u1 m2
            | _ => True
            end).
    generalize (TauF m1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [| u1 u2 Hsim | | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists u2; split; [reflexivity | exact Hsim].
  Qed.

  Lemma eqitF_inv_Vis_l {E : Type -> Type} {R1 R2 : Type}
    {RR : R1 -> R2 -> Prop}
    {sim : itree E R1 -> itree E R2 -> Prop}
    {X : Type} (e : E X) (k1 : X -> itree E R1) (ot2 : itree' E R2) :
    eqitF RR false false id sim (VisF e k1) ot2 ->
    exists k2 : X -> itree E R2,
      ot2 = VisF e k2 /\ forall x : X, sim (k1 x) (k2 x).
  Proof using.
    intros H.
    change (match VisF e k1 : itree' E R1 with
            | VisF Y e1 h1 =>
                exists k2 : Y -> itree E R2,
                  ot2 = VisF e1 k2 /\ forall x : Y, sim (h1 x) (k2 x)
            | _ => True
            end).
    generalize (VisF e k1 : itree' E R1) H; clear H; intros ot1 H.
    destruct H as [| | Y e0 h1 h2 Hrel | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; try exact I.
    exists h2; split; [reflexivity | exact Hrel].
  Qed.

  Lemma refine_prov__obs_eq {R1 R2}
    (RR : list N -> R1 -> R2 -> Prop)
    (r r' : list N -> itree ProvBotE R1 -> itree ProvBotE R2 -> Prop)
    (Hr_eq : forall U a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r U a1 a2 -> r' U a1' a2') :
    forall U (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov_ RR r U t1 t2 ->
      refine_prov_ RR r' U t1' t2'.
  Proof using.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    revert t1' t2' E1 E2;
      induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply RP_Step; unfold rp_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp).
          eapply Hr_eq; [apply Hk1 | pstep; exact E2 | exact Hleft].
        * right; right.
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp).
             eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hboth].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha).
             eapply Hr_eq; [apply Hk1 | apply Hk2 | exact HA].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply RP_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
    - punfold E2; red in E2; rewrite Ht2 in E2;
        apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
      eapply RP_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
  Qed.

  Lemma refine_prov_obs_eq {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      refine_prov RR U t1 t2 ->
      refine_prov RR U t1' t2'.
  Proof using.
    pcofix CIH.
    intros U t1 t1' t2 t2' E1 E2 Hrel.
    pstep; punfold Hrel.
    eapply refine_prov__obs_eq; [| exact E1 | exact E2 | exact Hrel].
    intros U0 a1 a1' a2 a2' Ea1 Ea2 Hr; pclearbot.
    right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
  Qed.

  Lemma refine_prov_inv_Tau_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall U (t1 : itree ProvBotE R1) (m2 : itree ProvBotE R2),
      refine_prov RR U t1 (Tau m2) ->
      refine_prov RR U t1 m2.
  Proof using.
    pcofix CIH.
    intros U t1 m2 H; pstep; punfold H.
    remember (Tau m2) as tm2 eqn:Etm2.
    assert (Hot2 : observe tm2 = TauF m2) by (subst tm2; reflexivity).
    clear Etm2.
    revert m2 Hot2; induction H as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2' Ht2 Hrel _];
      intros m2 Hot2.
    - unfold rp_step_body in Hstep; rewrite Hot2 in Hstep.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1] eqn:Hot1; try contradiction.
      + pclearbot; punfold Hstep.
        eapply RP_TauL;
          [exact Hot1
          | eapply refine_prov__mon;
              [exact Hstep | intros ? ? ? [Hl | []]; left; eapply paco3_mon; [exact Hl | intros ? ? ? []]]].
      + apply RP_Step; unfold rp_step_body; rewrite Hot1.
        destruct Hstep as [Hub | [Hleft | Hboth]]; [left; exact Hub | | contradiction].
        right; left.
        destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
        intros p Hp; specialize (Hleft p Hp); pclearbot.
        right; apply CIH.
        eapply refine_prov_obs_eq; [apply reflexivity | | exact Hleft].
        rewrite (itree_eta t2), Hot2; reflexivity.
    - eapply RP_TauL; [exact Ht1 | apply IH, Hot2].
    - rewrite Hot2 in Ht2; inversion Ht2; subst m2'.
      eapply refine_prov__mon;
        [exact Hrel | intros ? ? ? [Hl | []]; left; eapply paco3_mon; [exact Hl | intros ? ? ? []]].
  Qed.

  Lemma refine_prov_bind {R1 R2 S1 S2}
    (RR : list N -> R1 -> R2 -> Prop) (RS : list N -> S1 -> S2 -> Prop)
    (U : list N)
    (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (k1 : R1 -> itree ProvBotE S1) (k2 : R2 -> itree ProvBotE S2)
    (Ht : refine_prov RR U t1 t2)
    (Hk : forall U' r1 r2, incl U U' -> RR U' r1 r2 -> refine_prov RS U' (k1 r1) (k2 r2)) :
    refine_prov RS U (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    revert U t1 t2 Ht Hk; pcofix CIH; intros U t1 t2 Ht Hk.
    punfold Ht.
    revert Hk; induction Ht as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH]; intros Hk.
    - unfold rp_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        eapply paco3_mon;
          [eapply refine_prov_obs_eq;
             [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
             | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
             | exact (Hk U r1 r2 (incl_refl U) Hstep)]
          | intros ? ? ? []].
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        pclearbot; pstep; apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
        right; eapply CIH; [exact Hstep | exact Hk].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * pstep; apply RP_Step; unfold rp_step_body; rewrite (observe_bind t1 k1), Hot1; left; exact Hub.
        * pstep; apply RP_Step; unfold rp_step_body; rewrite (observe_bind t1 k1), Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; eapply CIH; [exact Hleft |].
          intros U' r1 r2 Hincl HR; eapply Hk; [| exact HR].
          intros z Hz; apply Hincl; right; exact Hz.
        * destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          pstep; apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2; right; right.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
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
      eapply RP_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply RP_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
  Qed.

  Lemma refine_prov_refl {R} (RR : list N -> R -> R -> Prop)
    (HRR : forall U r, RR U r r) :
    forall U (t : itree ProvBotE R), refine_prov RR U t t.
  Proof using.
    pcofix CIH; intros U t; pstep; apply RP_Step; unfold rp_step_body.
    destruct (observe t) as [x | m | X e k].
    - apply HRR.
    - right; apply CIH.
    - right; right.
      destruct e as [p | b]; cbn.
      + destruct p; intros q _; right; apply CIH.
      + split; [apply EqE_bot_refl |].
        intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2; right; apply CIH.
  Qed.

  Lemma refine_prov_trans {R} (f : R -> dvalue) :
    let RR := fun (_ : list N) (r1 r2 : R) => f r1 = f r2 in
    forall U (t1 t2 t3 : itree ProvBotE R),
      refine_prov RR U t1 t2 ->
      refine_prov RR U t2 t3 ->
      refine_prov RR U t1 t3.
  Proof using.
    cbv zeta; set (RR := fun (_ : list N) (r1 r2 : R) => f r1 = f r2).
    assert (HRR_anti : forall U1 U2 r1 r2, incl U1 U2 -> RR U1 r1 r2 -> RR U2 r1 r2)
      by (intros ? ? ? ? _ H; exact H).
    pcofix CIH.
    intros U t1 t2 t3 H12 H23.
    pstep; punfold H12.
    revert t3 H23;
      induction H12 as [U t1 t2 Hstep12 | U t1 m1 t2 Ht1 _ IH12 | U t1 t2 m2 Ht2 _ IH12];
      intros t3 H23.
    - unfold rp_step_body in Hstep12.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1] eqn:Hot1.
      + (* observe t1 = RetF r1 *)
        destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
        punfold H23.
        revert Hot2 Hstep12;
          induction H23 as [U t2_ t3 Hstep23 | U t2_ m2' t3 Ht2_ _ _ | U t2_ t3 m3 Ht3 _ IH23];
          intros Hot2 Hstep12.
        * unfold rp_step_body in Hstep23; rewrite Hot2 in Hstep23.
          destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3; try contradiction.
          apply RP_Step; unfold rp_step_body; rewrite Hot1, Hot3.
          unfold RR in *; congruence.
        * congruence.
        * eapply RP_TauR; [exact Ht3 | apply IH23; assumption].
      + (* observe t1 = TauF m1 *)
        destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
        pclearbot.
        assert (Hm23 : refine_prov RR U m2 t3).
        { apply refine_prov_inv_Tau_l.
          eapply refine_prov_obs_eq; [| apply reflexivity | exact H23].
          rewrite (itree_eta t2), Hot2; reflexivity. }
        destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3.
        * (* observe t3 = RetF r3 *)
          eapply RP_TauL; [exact Hot1 |].
          punfold Hm23; clear Hot1 Hot2 H23.
          revert m1 Hstep12 Hot3;
            induction Hm23 as [U m2_ t3_ Hs23 | U m2_ m2' t3_ Hm2_ _ IHm23 | U m2_ t3_ m3' Ht3_ _ _];
            intros m1 Hm12 Hot3.
          -- unfold rp_step_body in Hs23; rewrite Hot3 in Hs23.
             destruct (observe m2_) as [r2 | mm | X2 e2 k2] eqn:Hotm2; try contradiction.
             ++ punfold Hm12.
                revert Hotm2 Hs23;
                  induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                  intros Hotm2 Hs23; try congruence.
                ** unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                   destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                   --- apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3; unfold RR in *; congruence.
                   --- apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3.
                       destruct Hs12 as [Hub | [Hl | Hb]]; [left; exact Hub | | contradiction].
                       right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                       intros p Hp; specialize (Hl p Hp); pclearbot.
                       right; eapply CIH; [exact Hl |].
                       pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2, Hot3; exact Hs23.
                ** eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
             ++ destruct Hs23 as [Hub2 | [Hl2 | Hb2]]; [| | contradiction].
                ** punfold Hm12.
                   revert Hotm2 Hub2;
                     induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                     intros Hotm2 Hub2; try congruence.
                   --- unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                       destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                       apply RP_Step; unfold rp_step_body; rewrite Hotm1.
                       destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                       +++ left; exact Hub1.
                       +++ right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                           intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                           pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2; left; exact Hub2.
                       +++ left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                           [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
                   --- eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
                ** punfold Hm12.
                   revert Hotm2 Hl2;
                     induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
                     intros Hotm2 Hl2; try congruence.
                   --- unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                       destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                       apply RP_Step; unfold rp_step_body; rewrite Hotm1.
                       destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                       +++ left; exact Hub1.
                       +++ right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                           intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                           pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2; right; left.
                           destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                           intros q Hq; assert (HqU : ~ In q U) by (intros Hx; apply Hq; right; exact Hx).
                           specialize (Hl2 q HqU); pclearbot; left.
                           eapply refine_prov_antitone; [exact HRR_anti | | exact Hl2].
                           intros z [<- | Hz]; [left; reflexivity | right; right; exact Hz].
                       +++ right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                           destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                           intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                           right; eapply CIH; [exact Hb1 | exact Hl2].
                   --- eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
          -- apply IHm23; [| exact Hot3].
             apply refine_prov_inv_Tau_r.
             eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm12].
             rewrite (itree_eta m2_), Hm2_; reflexivity.
          -- congruence.
        * (* observe t3 = TauF m3 *)
          apply RP_Step; unfold rp_step_body; rewrite Hot1, Hot3.
          right; eapply CIH; [exact Hstep12 |].
          apply refine_prov_inv_Tau_r.
          eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm23].
          rewrite (itree_eta t3), Hot3; reflexivity.
        * (* observe t3 = VisF e3 k3 *)
          eapply RP_TauL; [exact Hot1 |].
          punfold Hm23; clear Hot1 Hot2 H23.
          revert m1 Hstep12 Hot3;
            induction Hm23 as [U m2_ t3_ Hs23 | U m2_ m2' t3_ Hm2_ _ IHm23 | U m2_ t3_ m3' Ht3_ _ _];
            intros m1 Hm12 Hot3.
          -- unfold rp_step_body in Hs23; rewrite Hot3 in Hs23.
             destruct (observe m2_) as [r2 | mm | X2 e2 k2] eqn:Hotm2; try contradiction.
             punfold Hm12.
             revert Hotm2 Hs23;
               induction Hm12 as [U m1_ m2__ Hs12 | U m1_ m1' m2__ Hm1_ _ IHm12 | U m1_ m2__ mm2 Hm2__ _ _];
               intros Hotm2 Hs23; try congruence.
             ++ unfold rp_step_body in Hs12; rewrite Hotm2 in Hs12.
                destruct (observe m1_) as [r1 | mm1 | X1 e1 k1] eqn:Hotm1; try contradiction.
                apply RP_Step; unfold rp_step_body; rewrite Hotm1, Hot3.
                destruct Hs12 as [Hub1 | [Hl1 | Hb1]].
                ** left; exact Hub1.
                ** right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
                   intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
                   eapply refine_prov_antitone; [exact HRR_anti | intros z Hz; right; exact Hz |].
                   pstep; apply RP_Step; unfold rp_step_body; rewrite Hotm2, Hot3; exact Hs23.
                ** destruct Hs23 as [Hub2 | [Hl2 | Hb2]].
                   --- left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                       [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
                   --- right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                       destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                       intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                       right; eapply CIH; [exact Hb1 | exact Hl2].
                   --- right; right.
                       destruct e1 as [p1 | b1], e2 as [p2 | b2], e3 as [p3 | b3];
                         cbn in *; try contradiction.
                       +++ destruct p1, p2, p3; intros p Hp.
                           specialize (Hb1 p Hp); specialize (Hb2 p Hp); pclearbot.
                           right; eapply CIH; [exact Hb1 | exact Hb2].
                       +++ destruct Hb1 as [HE12 HA12], Hb2 as [HE23 HA23].
                           split; [eapply EqE_bot_trans; eassumption |].
                           intros a1 a3 Ha13.
                           destruct (EqA_bot_trans b1 b2 b3 a1 a3 HE12 HE23 Ha13) as [a2 [Ha12 Ha23]].
                           specialize (HA12 a1 a2 Ha12); specialize (HA23 a2 a3 Ha23); pclearbot.
                           rewrite <- (bot_ans_provs_eq b1 b2 a1 a2 HE12 Ha12) in HA23.
                           right; eapply CIH; [exact HA12 | exact HA23].
             ++ eapply RP_TauL; [exact Hm1_ | apply IHm12; assumption].
          -- apply IHm23; [| exact Hot3].
             apply refine_prov_inv_Tau_r.
             eapply refine_prov_obs_eq; [apply reflexivity | | exact Hm12].
             rewrite (itree_eta m2_), Hm2_; reflexivity.
          -- congruence.
      + (* observe t1 = VisF e1 k1 *)
        destruct Hstep12 as [Hub1 | [Hl1 | Hb1]].
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; left; exact Hub1.
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hl1 p Hp); pclearbot; right; eapply CIH; [exact Hl1 |].
          eapply refine_prov_antitone; [exact HRR_anti | intros z Hz; right; exact Hz | exact H23].
        * destruct (observe t2) as [r2 | m2 | X2 e2 k2] eqn:Hot2; try contradiction.
          punfold H23.
          revert Hot2 Hb1;
            induction H23 as [U t2_ t3 Hs23 | U t2_ m2' t3 Ht2_ _ _ | U t2_ t3 m3 Ht3 _ IH23];
            intros Hot2 Hb1; try congruence.
          -- unfold rp_step_body in Hs23; rewrite Hot2 in Hs23.
             apply RP_Step; unfold rp_step_body; rewrite Hot1.
             destruct Hs23 as [Hub2 | [Hl2 | Hb2]].
             ++ left; destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction;
                [destruct p1; discriminate | destruct Hb1 as [HE _]; rewrite (EqE_bot_is_ub _ _ HE); exact Hub2].
             ++ right; left; destruct e2 as [p2 | b2]; [| contradiction]; destruct p2.
                destruct e1 as [p1 | b1]; [| cbn in Hb1; contradiction]; destruct p1.
                intros p Hp; specialize (Hb1 p Hp); specialize (Hl2 p Hp); pclearbot.
                right; eapply CIH; [exact Hb1 | exact Hl2].
             ++ right; right.
                destruct (observe t3) as [r3 | m3 | X3 e3 k3] eqn:Hot3; try contradiction.
                destruct e1 as [p1 | b1], e2 as [p2 | b2], e3 as [p3 | b3];
                  cbn in *; try contradiction.
                ** destruct p1, p2, p3; intros p Hp.
                   specialize (Hb1 p Hp); specialize (Hb2 p Hp); pclearbot.
                   right; eapply CIH; [exact Hb1 | exact Hb2].
                ** destruct Hb1 as [HE12 HA12], Hb2 as [HE23 HA23].
                   split; [eapply EqE_bot_trans; eassumption |].
                   intros a1 a3 Ha13.
                   destruct (EqA_bot_trans b1 b2 b3 a1 a3 HE12 HE23 Ha13) as [a2 [Ha12 Ha23]].
                   specialize (HA12 a1 a2 Ha12); specialize (HA23 a2 a3 Ha23); pclearbot.
                   rewrite <- (bot_ans_provs_eq b1 b2 a1 a2 HE12 Ha12) in HA23.
                   right; eapply CIH; [exact HA12 | exact HA23].
          -- eapply RP_TauR; [exact Ht3 | apply IH23; assumption].
    - eapply RP_TauL; [exact Ht1 | apply IH12, H23].
    - apply IH12, refine_prov_inv_Tau_l.
      eapply refine_prov_obs_eq; [| apply reflexivity | exact H23].
      rewrite (itree_eta t2), Ht2; reflexivity.
  Qed.

  (** ** Lifting [refine_mcfg] to [interp_mcfg_model] *)

  Lemma refine_mcfg_lift_bot_prov {R} (t : itree MCFGEbot R) (U : list N) :
    refine_prov (fun _ r1 r2 => r1 = r2) U (lift_bot_prov t) (lift_bot_prov t).
  Proof using.
    apply refine_prov_refl; intros; reflexivity.
  Qed.

  Lemma interp_vellvm_prov_h_refines_same {T}
    (e : MCFGEtop T) (s : FusedS) (U : list N) :
    refine_prov
      (fun _ '(s1', r1) '(s2', r2) => s1' = s2' /\ EqA_MCFG T T e r1 e r2)
      U (interp_vellvm_prov_h e s) (interp_vellvm_prov_h e s).
  Proof using.
    apply refine_prov_refl; intros U' [s' r]; split; [reflexivity | apply EqA_MCFG_refl].
  Qed.

  Lemma interp_vellvm_prov_h_refines {T1 T2}
    (e1 : MCFGEtop T1) (e2 : MCFGEtop T2)
    (HE : EqE_MCFG T1 T2 e1 e2)
    (s : FusedS) (U : list N) :
    refine_prov
      (fun _ '(s1', r1) '(s2', r2) => s1' = s2' /\ EqA_MCFG T1 T2 e1 r1 e2 r2)
      U (interp_vellvm_prov_h e1 s) (interp_vellvm_prov_h e2 s).
  Proof using.
    destruct_sum2 e1 e2 HE.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; cbn in HE; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - destruct e1, e2; cbn in HE; subst;
        apply interp_vellvm_prov_h_refines_same.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
      right; right; split; [exact I | intros [] [] _].
      left; eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      pstep; apply RP_Step; cbn; split; reflexivity.
    - destruct e1, e2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition model_step_state (R : Type) : Type :=
    (FusedS * R) + (FusedS * @MCFGtop (@ParamsV IP IPT) R).

  Definition model_cont (R : Type) (x : model_step_state R)
    : itree ProvBotE (FusedS * R) :=
    match x with
    | inl sr => Ret sr
    | inr (s', t') => Tau (interp_state interp_vellvm_prov_h t' s')
    end.

  Definition model_step_rel {R1 R2} (RR : R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) => s1 = s2 /\ RR r1 r2
      | inr (s1, t1), inr (s2, t2) =>
          s1 = s2 /\ ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2
      | _, _ => False
      end.

  Lemma interp_state_decomp {R} (t : MCFGtop R) (s : FusedS) :
    exists w : itree ProvBotE (model_step_state R),
      interp_state interp_vellvm_prov_h t s ≅ ITree.bind w (model_cont R).
  Proof using.
    destruct (observe t) as [r | m | X e k] eqn:Hot.
    - exists (Ret (inl (s, r))).
      rewrite (unfold_interp_state interp_vellvm_prov_h t s), Hot; cbn -[interp_vellvm_prov_h].
      rewrite Eqit.bind_ret_l; reflexivity.
    - exists (Ret (inr (s, m))).
      rewrite (unfold_interp_state interp_vellvm_prov_h t s), Hot; cbn -[interp_vellvm_prov_h].
      rewrite Eqit.bind_ret_l; reflexivity.
    - exists (ITree.bind (interp_vellvm_prov_h e s) (fun '(s', x) => Ret (inr (s', k x)))).
      rewrite (unfold_interp_state interp_vellvm_prov_h t s), Hot; cbn -[interp_vellvm_prov_h].
      rewrite Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma ruttc_model_step_decomp {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2)
    (HR : ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2)
    (s : FusedS) (U : list N) :
    exists w1 w2,
      interp_state interp_vellvm_prov_h t1 s ≅ ITree.bind w1 (model_cont R1) /\
      interp_state interp_vellvm_prov_h t2 s ≅ ITree.bind w2 (model_cont R2) /\
      refine_prov (model_step_rel RR) U w1 w2.
  Proof using.
    punfold HR; red in HR.
    remember (observe t1) as ot1 eqn:Hot1.
    remember (observe t2) as ot2 eqn:Hot2.
    revert t1 t2 Hot1 Hot2 s U;
      induction HR as [r1 r2 HRR | m1 m2 Hm | X1 X2 e1 e2 k1 k2 HE Hk
                       | m1 ot2_ _ IH | ot1_ m2 _ IH
                       | X1 e1 k1 ot2_ Hcut | X2 ot1_ e2 k2 Hcut];
      intros t1 t2 Hot1 Hot2 s U; pclearbot.
    - exists (Ret (inl (s, r1))), (Ret (inl (s, r2))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_ret_l; reflexivity.
        * pstep; apply RP_Step; cbn; split; [reflexivity | exact HRR].
    - exists (Ret (inr (s, m1))), (Ret (inr (s, m2))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_ret_l; reflexivity.
        * pstep; apply RP_Step; cbn; split; [reflexivity | exact Hm].
    - exists (ITree.bind (interp_vellvm_prov_h e1 s) (fun '(s', x) => Ret (inr (s', k1 x)))),
             (ITree.bind (interp_vellvm_prov_h e2 s) (fun '(s', x) => Ret (inr (s', k2 x)))).
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
      + split.
        * rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
          rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
          intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
        * eapply refine_prov_bind; [apply interp_vellvm_prov_h_refines, HE |].
          intros U' [s1' a1] [s2' a2] _ [<- HA].
          specialize (Hk a1 a2 HA); pclearbot.
          pstep; apply RP_Step; cbn; split; [reflexivity | exact Hk].
    - destruct (IH m1 t2 Logic.eq_refl Hot2 s U) as (w1' & w2' & Ew1 & Ew2 & Hw).
      exists (Tau w1'), w2'.
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_tau, Ew1; reflexivity.
      + split; [exact Ew2 |].
        punfold Hw; pstep; eapply RP_TauL; [reflexivity | exact Hw].
    - destruct (IH t1 m2 Hot1 Logic.eq_refl s U) as (w1' & w2' & Ew1 & Ew2 & Hw).
      exists w1', (Tau w2').
      split; [exact Ew1 |].
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t2 s), <- Hot2; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_tau, Ew2; reflexivity.
      + punfold Hw; pstep; eapply RP_TauR; [reflexivity | exact Hw].
    - destruct (interp_state_decomp t2 s) as [w2 Ew2].
      exists (ITree.bind (interp_vellvm_prov_h e1 s) (fun '(s', x) => Ret (inr (s', k1 x)))), w2.
      split.
      + rewrite (unfold_interp_state interp_vellvm_prov_h t1 s), <- Hot1; cbn -[interp_vellvm_prov_h].
        rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
      + split; [exact Ew2 |].
        clear Hot1; destruct Hcut as [u].
        pstep; apply RP_Step; unfold rp_step_body.
        rewrite !observe_bind; cbn; left; reflexivity.
    - inversion Hcut.
  Qed.

  Lemma refine_mcfg_to_model_aux {R1 R2} (RR : R1 -> R2 -> Prop) :
    forall (U : list N)
      (w1 : itree ProvBotE (model_step_state R1))
      (w2 : itree ProvBotE (model_step_state R2))
      (t1 : itree ProvBotE (FusedS * R1))
      (t2 : itree ProvBotE (FusedS * R2)),
      ITree.bind w1 (model_cont R1) ≅ t1 ->
      ITree.bind w2 (model_cont R2) ≅ t2 ->
      refine_prov (model_step_rel RR) U w1 w2 ->
      refine_prov (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ RR r1 r2) U t1 t2.
  Proof using.
    pcofix CIH.
    intros U w1 w2 t1 t2 Et1 Et2 Hw.
    pstep.
    set (r_rel := fun U0 a1 a2 =>
                    exists v1 v2,
                      ITree.bind v1 (model_cont R1) ≅ a1 /\
                      ITree.bind v2 (model_cont R2) ≅ a2 /\
                      refine_prov (model_step_rel RR) U0 v1 v2).
    assert (Hr_eq : forall U0 a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> r_rel U0 a1 a2 -> r_rel U0 a1' a2').
    { intros U0 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
      exists v1, v2; split; [etransitivity; [exact Ev1 | exact Ea1] | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]]. }
    eapply refine_prov__mon with (r := r_rel);
      [| intros U0 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
    punfold Hw; clear t1 t2 Et1 Et2 CIH r.
    induction Hw as [U w1 w2 Hstep | U w1 mw1 w2 Hw1 _ IH | U w1 w2 mw2 Hw2 _ IH].
    - unfold rp_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct x1 as [[s1 r1] | [s1 u1']], x2 as [[s2 r2] | [s2 u2']]; cbn in Hstep; try contradiction.
        * apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind w1 (model_cont R1)), How1,
                  (observe_bind w2 (model_cont R2)), How2; cbn.
          exact Hstep.
        * destruct Hstep as [<- HR'].
          apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind w1 (model_cont R1)), How1,
                  (observe_bind w2 (model_cont R2)), How2; cbn.
          destruct (ruttc_model_step_decomp RR u1' u2' HR' s1 U) as (v1 & v2 & Ev1 & Ev2 & Hv).
          exists v1, v2; split; [symmetry; exact Ev1 | split; [symmetry; exact Ev2 | exact Hv]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
        apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind w1 (model_cont R1)), How1,
                (observe_bind w2 (model_cont R2)), How2.
        exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + apply RP_Step; unfold rp_step_body.
        rewrite (observe_bind w1 (model_cont R1)), How1.
        destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct ev1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          exists (kw1 p), w2; split; [reflexivity | split; [reflexivity | exact Hleft]].
        * right; right.
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 (model_cont R2)), How2.
          destruct ev1 as [p1 | b1], ev2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             exists (kw1 p), (kw2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
    - eapply RP_TauL; [rewrite (observe_bind w1 (model_cont R1)), Hw1; reflexivity | exact IH].
    - eapply RP_TauR; [rewrite (observe_bind w2 (model_cont R2)), Hw2; reflexivity | exact IH].
  Qed.

  Lemma refine_mcfg_to_model {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : MCFGtop R1) (t2 : MCFGtop R2)
    (HR : ruttc cutUB_rel cutNone EqE_MCFG EqA_MCFG RR t1 t2) :
    forall (s : FusedS) (U : list N),
      refine_prov (fun _ '(s1, r1) '(s2, r2) => s1 = s2 /\ RR r1 r2) U
        (interp_state interp_vellvm_prov_h t1 s)
        (interp_state interp_vellvm_prov_h t2 s).
  Proof using.
    intros s U.
    destruct (ruttc_model_step_decomp RR t1 t2 HR s U) as (w1 & w2 & Ew1 & Ew2 & Hw).
    eapply refine_mcfg_to_model_aux; [symmetry; exact Ew1 | symmetry; exact Ew2 | exact Hw].
  Qed.

  (** ** Whole-Program Refinement ([prog_refines]) & [PreOrder] *)

  Definition prog_refines (M1 M2 : CFG.mcfg dtyp) : Prop :=
    forall (ret_typ : dtyp) (entry : function_id)
           (args : list (@dvalue (@ParamsV IP IPT))) (U : list N),
      refine_prov (fun _ r1 r2 => snd r1 = snd r2) U
        (run_mcfg_model ret_typ entry args M1)
        (run_mcfg_model ret_typ entry args M2).

  Lemma prog_refines_refl (M : CFG.mcfg dtyp) :
    prog_refines M M.
  Proof using.
    intros ret_typ entry args U.
    apply refine_prov_refl; intros; reflexivity.
  Qed.

  Lemma prog_refines_trans (M1 M2 M3 : CFG.mcfg dtyp) :
    prog_refines M1 M2 ->
    prog_refines M2 M3 ->
    prog_refines M1 M3.
  Proof using.
    intros H12 H23 ret_typ entry args U.
    eapply (refine_prov_trans snd); [apply H12 | apply H23].
  Qed.

  #[export] Instance prog_refines_PreOrder : PreOrder prog_refines :=
    {| PreOrder_Reflexive  := prog_refines_refl;
       PreOrder_Transitive := prog_refines_trans |}.

  Lemma refine_vellvm_to_prog (M1 M2 : CFG.mcfg dtyp)
    (Hden : forall ret_typ entry args,
              @refine_mcfg (@ParamsV IP IPT) _ _ Logic.eq
                (denote_vellvm ret_typ entry args M1)
                (denote_vellvm ret_typ entry args M2)) :
    prog_refines M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [| apply incl_refl | apply refine_mcfg_to_model, refine_mcfg_interp_intrinsics, Hden].
    intros _ _ [s1 r1] [s2 r2] _ [<- <-]; reflexivity.
  Qed.

  (** ** Modular Per-CFG Lifter ([lift_cfg_pass]) *)

  Lemma of_list_fn_ctx_refines
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2
            (fun '(k1, f1) '(k2, f2) =>
               k1 = k2 /\
               forall cc args, refine_cfg Logic.eq (f1 cc args) (f2 cc args))
            l1 l2) :
    fn_ctx_refines (IntMaps.IP.of_list l1) (IntMaps.IP.of_list l2).
  Proof using.
    unfold fn_ctx_refines; induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros k.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      destruct (Z.eq_dec k1 k) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity.
        constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne.
        apply IH.
  Qed.

  Lemma map_monad_address_one_function_refines
    (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hbody : forall c va,
               @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                 (denote_cfg c va) (denote_cfg (f c) va))
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    refine_mcfg
      (Forall2
         (fun '(k1, fn1) '(k2, fn2) =>
            k1 = k2 /\
            forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)))
      (map_monad address_one_function defs)
      (map_monad address_one_function (List.map (map_defn_cfg f) defs)).
  Proof using.
    induction defs as [| df defs' IH]; cbn [List.map map_monad].
    - apply ruttc_ret; constructor.
    - eapply ruttc_bind with
        (RR := fun '(k1, fn1) '(k2, fn2) =>
                 k1 = k2 /\
                 forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)).
      + unfold address_one_function; cbn [map_defn_cfg df_prototype].
        eapply ruttc_bind; [apply refine_mcfg_refl | intros fv _ <-].
        destruct fv as [[p | | | | | | |] | |];
          [| unfold raise, trigger_cast; eapply ruttc_trigger';
               [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _] ..].
        apply ruttc_ret; split; [reflexivity |].
        apply refine_cfg_denote_function; [reflexivity | reflexivity |].
        intros va; apply Hbody.
      + intros [k1 fn1] [k2 fn2] Hhd.
        eapply ruttc_bind; [exact IH |].
        intros tl1 tl2 Htl; apply ruttc_ret; constructor; assumption.
  Qed.

  Lemma Forall2_fn_refl (l : list (Z * @function_denotation (@ParamsV IP IPT))) :
    Forall2
      (fun '(k1, fn1) '(k2, fn2) =>
         k1 = k2 /\
         forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args))
      l l.
  Proof using.
    induction l as [| [k fn] l' IH]; constructor; [| exact IH].
    split; [reflexivity | intros; apply refine_cfg_refl].
  Qed.

  Theorem lift_cfg_pass (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall c,
             flat_map block_block_addresses (blks (f c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall c va,
               @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                 (denote_cfg c va) (denote_cfg (f c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_cfg f M).
  Proof using.
    intros M; apply refine_vellvm_to_prog; intros ret_typ entry args.
    unfold denote_vellvm.
    assert (Hbg : @build_global_environment (@ParamsV IP IPT) (map_mcfg_cfg f M) =
                  @build_global_environment (@ParamsV IP IPT) M).
    { unfold build_global_environment.
      rewrite map_mcfg_cfg_prototypes, (map_mcfg_cfg_block_addresses f M Hba).
      reflexivity. }
    rewrite Hbg.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros [] _ <-].
    cbn [m_definitions m_declarations map_mcfg_cfg].
    eapply ruttc_bind; [apply (map_monad_address_one_function_refines f Hbody) |].
    intros defns1 defns2 Hdefns.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros libs _ <-].
    eapply ruttc_bind; [apply refine_mcfg_refl | intros addr _ <-].
    eapply ruttc_bind.
    - apply refine_mcfg_denote_mcfg.
      apply of_list_fn_ctx_refines.
      apply Forall2_app; [exact Hdefns | apply Forall2_fn_refl].
    - intros rv _ <-; destruct rv; apply refine_mcfg_refl.
  Qed.


End ModelSemantics.
