(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Loop Cutpoint Naming, Substitution & Pure-SSA IR Segment Reification ([CertValidator.McLoopIrSpec])

    1. Cutpoint variable naming ([!cut_k], [!mc_hi_rk], [!mc_ur_r], [!mc_us_i]
       — never [$]-prefixed), let-free substitution ([subst_cert_expr]), and
       32-bit upper-half recombination ([combine_hi32_expr]).
    2. General pure-SSA IR segment reification ([ir_seg_tree], [reify_ir_seg])
       supporting rotated loops, entry guards, exit-block phis, LICM, and
       self-loops. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  Numbers.DecimalString
  Numbers.DecimalZ
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.LLVMEvents.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  McIsaCommon
  A64Decode
  A64ExecSym
  A64DagProof
  McOblDischarger.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.
#[local] Arguments Integers.modulus : simpl never.
#[local] Arguments Integers.half_modulus : simpl never.
#[local] Arguments Integers.max_unsigned : simpl never.
#[local] Arguments Integers.max_signed : simpl never.
#[local] Arguments Integers.min_signed : simpl never.
#[local] Arguments Integers.unsigned : simpl never.
#[local] Arguments Integers.signed : simpl never.
#[local] Arguments Integers.repr : simpl never.
#[local] Arguments Integers.zero : simpl never.
#[local] Arguments Integers.one : simpl never.
#[local] Arguments Integers.mone : simpl never.
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Cutpoint Names, 32-Bit Upper-Half Recombination & Substitution *)

Definition mc_cut_var_name (k : nat) : string :=
  ("!cut_" ++ show_Z_dec (Z.of_nat k))%string.

Definition mc_hi_var_name (r : N) : string :=
  ("!mc_hi_r" ++ show_Z_dec (Z.of_N r))%string.

Definition mc_skel_reg_name (r : N) : string :=
  ("!mc_ur_" ++ show_Z_dec (Z.of_N r))%string.

Definition mc_skel_slot_name (idx : nat) : string :=
  ("!mc_us_" ++ show_Z_dec (Z.of_nat idx))%string.

Lemma mc_cut_var_name_inj : forall k1 k2,
  mc_cut_var_name k1 = mc_cut_var_name k2 -> k1 = k2.
Proof.
  intros k1 k2 Heq; unfold mc_cut_var_name in Heq.
  inversion Heq as [Hs].
  apply show_Z_dec_pos_inj in Hs; lia.
Qed.

Lemma mc_hi_var_name_inj : forall r1 r2,
  mc_hi_var_name r1 = mc_hi_var_name r2 -> r1 = r2.
Proof.
  intros r1 r2 Heq; unfold mc_hi_var_name in Heq.
  inversion Heq as [Hs].
  apply show_Z_dec_pos_inj in Hs; lia.
Qed.

Lemma mc_skel_reg_name_inj : forall r1 r2,
  mc_skel_reg_name r1 = mc_skel_reg_name r2 -> r1 = r2.
Proof.
  intros r1 r2 Heq; unfold mc_skel_reg_name in Heq.
  inversion Heq as [Hs].
  apply show_Z_dec_pos_inj in Hs; lia.
Qed.

Lemma mc_skel_slot_name_inj : forall i1 i2,
  mc_skel_slot_name i1 = mc_skel_slot_name i2 -> i1 = i2.
Proof.
  intros i1 i2 Heq; unfold mc_skel_slot_name in Heq.
  inversion Heq as [Hs].
  apply show_Z_dec_pos_inj in Hs; lia.
Qed.

Definition mc_hi32_mask : N := (N.shiftl 1%N 64%N - N.shiftl 1%N 32%N)%N.

Definition combine_hi32_expr (hi_e lo32_e : cert_expr) : cert_expr :=
  CE_BinOp CB_Or 64%positive no_binop_flags
    (CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags lo32_e)
    (CE_BinOp CB_And 64%positive no_binop_flags hi_e (CE_BvConst 64%positive mc_hi32_mask)).

Lemma combine_hi32_expr_wf : forall allowed hi_e lo32_e,
  wf_sym_expr allowed 64%positive hi_e ->
  wf_sym_expr allowed 32%positive lo32_e ->
  wf_sym_expr allowed 64%positive (combine_hi32_expr hi_e lo32_e).
Proof.
  intros allowed hi_e lo32_e Hhi Hlo; unfold combine_hi32_expr.
  apply a64_wf_sym_binop;
    [apply wf_sym_cast; [reflexivity | exact Hlo]
    | apply a64_wf_sym_binop; [exact Hhi | apply wf_sym_bv_const]].
Qed.

Lemma combine_hi32_expr_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle hi_e lo32_e (rk : @Integers.bit_int 64%positive)
         (vlo : @Integers.bit_int 32%positive),
    eval_closed_cert_expr penv foracle hi_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive rk)) ->
    eval_closed_cert_expr penv foracle lo32_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 32%positive vlo)) ->
    vlo = @Integers.repr 32%positive (@Integers.unsigned 64%positive rk) ->
    eval_closed_cert_expr penv foracle (combine_hi32_expr hi_e lo32_e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive rk)).
Proof.
  intros penv foracle hi_e lo32_e rk vlo Hhi Hlo Htrunc; unfold combine_hi32_expr.
  assert (Hz : eval_closed_cert_expr penv foracle
                 (CE_Cast CCK_ZExt 32%positive 64%positive no_cast_flags lo32_e) =
               raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive vlo)))))
    by (apply eval_ce_zext; [reflexivity | exact Hlo]).
  assert (Ha : eval_closed_cert_expr penv foracle
                 (CE_BinOp CB_And 64%positive no_binop_flags hi_e (CE_BvConst 64%positive mc_hi32_mask)) =
               raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
                 (@Integers.and 64%positive rk (@Integers.repr 64%positive (Z.of_N mc_hi32_mask)))))).
  { rewrite eval_ce_binop, Hhi, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
  rewrite eval_ce_binop, Hz, Ha; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.or Integers.and Integers.repr Integers.unsigned].
  replace 18446744069414584320%Z with (Z.of_N mc_hi32_mask) by reflexivity.
  rewrite (or_low_hi_mask_eq 32%positive rk vlo mc_hi32_mask eq_refl eq_refl Htrunc).
  reflexivity.
Qed.

Fixpoint lookup_subst (nm : string) (sub : list (string * positive * cert_expr))
  : option (positive * cert_expr) :=
  match sub with
  | [] => None
  | (x, w, e) :: rest =>
      if String.eqb nm x then Some (w, e) else lookup_subst nm rest
  end.

Fixpoint subst_cert_expr (sub : list (string * positive * cert_expr)) (e : cert_expr)
  {struct e} : cert_expr :=
  match e with
  | CE_BvConst w v => CE_BvConst w v
  | CE_Poison w => CE_Poison w
  | CE_Var nm w =>
      match lookup_subst nm sub with
      | Some (w', e') => if Pos.eqb w w' then e' else CE_Var nm w
      | None => CE_Var nm w
      end
  | CE_BinOp op w fl l r =>
      CE_BinOp op w fl (subst_cert_expr sub l) (subst_cert_expr sub r)
  | CE_ICmp pred ss w l r =>
      CE_ICmp pred ss w (subst_cert_expr sub l) (subst_cert_expr sub r)
  | CE_Cast k fw tw fl o =>
      CE_Cast k fw tw fl (subst_cert_expr sub o)
  | CE_Select w c t f =>
      CE_Select w (subst_cert_expr sub c) (subst_cert_expr sub t) (subst_cert_expr sub f)
  | CE_Freeze w o =>
      CE_Freeze w (subst_cert_expr sub o)
  | CE_Let bs body => CE_Let bs body
  end.

Definition subst_entry_wf (allowed : list (string * positive)) (ent : string * positive * cert_expr) : Prop :=
  let '(_, w, e') := ent in
  wt_cert_expr [] e' = true /\
  cert_expr_bit_width e' = w /\
  is_let_free_expr e' = true /\
  ub_free_expr e' = true /\
  incl (collect_free_vars [] e') allowed.

Lemma lookup_subst_in : forall nm sub w e,
  lookup_subst nm sub = Some (w, e) -> In (nm, w, e) sub.
Proof.
  intros nm sub; induction sub as [| [[x wx] ex] rest IH]; intros w e H;
    cbn [lookup_subst] in H; [discriminate H |].
  destruct (String.eqb nm x) eqn:Ex.
  - apply String.eqb_eq in Ex; inversion H; subst; left; reflexivity.
  - right; exact (IH _ _ H).
Qed.

Lemma lookup_subst_nodup_eq : forall nm sub w1 e1 w2 e2,
  NoDup (List.map (fun '(x, _, _) => x) sub) ->
  In (nm, w1, e1) sub ->
  lookup_subst nm sub = Some (w2, e2) ->
  w1 = w2 /\ e1 = e2.
Proof.
  intros nm sub; induction sub as [| [[x wx] ex] rest IH];
    intros w1 e1 w2 e2 Hnd Hin Hlk; cbn [lookup_subst] in Hlk; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hnd']; subst; clear Hnd.
  destruct (String.eqb nm x) eqn:Ex.
  - apply String.eqb_eq in Ex; subst x; inversion Hlk; subst w2 e2.
    destruct Hin as [Heq | Hinr].
    + inversion Heq; split; reflexivity.
    + exfalso; apply Hnin; apply in_map_iff; exists (nm, w1, e1); split; [reflexivity | exact Hinr].
  - destruct Hin as [Heq | Hinr].
    + inversion Heq; subst; rewrite String.eqb_refl in Ex; discriminate Ex.
    + exact (IH _ _ _ _ Hnd' Hinr Hlk).
Qed.

Lemma subst_cert_expr_wf : forall sub allowed e,
  NoDup (List.map (fun '(x, _, _) => x) sub) ->
  Forall (subst_entry_wf allowed) sub ->
  wt_cert_expr [] e = true ->
  is_let_free_expr e = true ->
  ub_free_expr e = true ->
  incl (collect_free_vars [] e) (List.map (fun '(nm, w, _) => (nm, w)) sub ++ allowed) ->
  (forall nm w, In (nm, w) (collect_free_vars [] e) -> In (nm, w) allowed -> lookup_subst nm sub = None) ->
  wt_cert_expr [] (subst_cert_expr sub e) = true /\
  cert_expr_bit_width (subst_cert_expr sub e) = cert_expr_bit_width e /\
  is_let_free_expr (subst_cert_expr sub e) = true /\
  ub_free_expr (subst_cert_expr sub e) = true /\
  incl (collect_free_vars [] (subst_cert_expr sub e)) allowed.
Proof.
  intros sub allowed e Hnd Hsub.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf Hub Hfv Hdisj;
    cbn [subst_cert_expr wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars] in *.
  - repeat split; try exact Hwt; intros x Hx; contradiction.
  - repeat split; try exact Hwt; intros x Hx; contradiction.
  - destruct (lookup_subst nm sub) as [[w' e'] |] eqn:Els.
    + pose proof (lookup_subst_in _ _ _ _ Els) as Hin.
      rewrite Forall_forall in Hsub; destruct (Hsub _ Hin) as (Hwt' & Hbw' & Hlf' & Hub' & Hfv').
      destruct (Pos.eqb w w') eqn:Eww.
      * apply Pos.eqb_eq in Eww; subst w.
        repeat split; try assumption.
      * exfalso; pose proof (Hfv (nm, w) (or_introl eq_refl)) as Hin_all.
        apply in_app_iff in Hin_all as [Hins | Hina].
        -- apply in_map_iff in Hins as [[[nm0 w0] e0] [Heq Hin0]].
           inversion Heq; subst nm0 w0.
           destruct (lookup_subst_nodup_eq nm sub w e0 w' e' Hnd Hin0 Els) as [Hw _].
           rewrite Hw, Pos.eqb_refl in Eww; discriminate Eww.
        -- rewrite (Hdisj nm w (or_introl eq_refl) Hina) in Els; discriminate Els.
    + pose proof (Hfv (nm, w) (or_introl eq_refl)) as Hin_all.
      apply in_app_iff in Hin_all as [Hins | Hina].
      * exfalso; apply in_map_iff in Hins as [[[nm0 w0] e0] [Heq Hin0]].
        inversion Heq; subst nm0 w0.
        clear -Els Hin0; induction sub as [| [[x wx] ex] rest IHs]; cbn in Els; [contradiction |].
        destruct (String.eqb nm x) eqn:Ex; [discriminate Els |].
        destruct Hin0 as [Heq0 | Hr0];
          [inversion Heq0; subst; rewrite String.eqb_refl in Ex; discriminate Ex | exact (IHs Els Hr0)].
      * repeat split; cbn; try exact Hwt; try reflexivity.
        intros [x wx] [Hx | []]; inversion Hx; subst; exact Hina.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    destruct Hwt as ((((Hsh & Hwtl) & Hwtr) & Hbw1) & Hbw2).
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [[Hnop Hubl] Hubr].
    destruct (IHl Hwtl Hlfl Hubl
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_introl Hx)))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_introl Hx)) Ha))
      as (Hwtl' & Hbwl' & Hlfl' & Hubl' & Hfvl').
    destruct (IHr Hwtr Hlfr Hubr
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_intror Hx)))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_intror Hx)) Ha))
      as (Hwtr' & Hbwr' & Hlfr' & Hubr' & Hfvr').
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hbwl', Hbwr', Hwtl', Hwtr', Hbw1, Hbw2, Hsh, Hlfl', Hlfr', Hnop, Hubl', Hubr'.
    repeat split; try reflexivity.
    intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; [exact (Hfvl' x Hx) | exact (Hfvr' x Hx)].
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    destruct Hwt as (((Hwtl & Hwtr) & Hbw1) & Hbw2).
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [Hubl Hubr].
    destruct (IHl Hwtl Hlfl Hubl
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_introl Hx)))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_introl Hx)) Ha))
      as (Hwtl' & Hbwl' & Hlfl' & Hubl' & Hfvl').
    destruct (IHr Hwtr Hlfr Hubr
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_intror Hx)))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_intror Hx)) Ha))
      as (Hwtr' & Hbwr' & Hlfr' & Hubr' & Hfvr').
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hbwl', Hbwr', Hwtl', Hwtr', Hbw1, Hbw2, Hlfl', Hlfr', Hubl', Hubr'.
    repeat split; try reflexivity.
    intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; [exact (Hfvl' x Hx) | exact (Hfvr' x Hx)].
  - rewrite !andb_true_iff in Hwt; destruct Hwt as [[Hck Hwto] Hbwo].
    destruct (IHo Hwto Hlf Hub Hfv Hdisj) as (Hwto' & Hbwo' & Hlfo' & Hubo' & Hfvo').
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hwto', Hbwo', Hbwo, Hck, Hlfo', Hubo'.
    repeat split; try reflexivity; exact Hfvo'.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hbwc) & Hbwt) & Hbwf).
    destruct Hlf as [[Hlfc Hlft] Hlff]; destruct Hub as [[Hubc Hubt] Hubf].
    destruct (IHc Hwtc Hlfc Hubc
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_introl Hx)))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_introl Hx)) Ha))
      as (Hwtc' & Hbwc' & Hlfc' & Hubc' & Hfvc').
    destruct (IHt Hwtt Hlft Hubt
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))) Ha))
      as (Hwtt' & Hbwt' & Hlft' & Hubt' & Hfvt').
    destruct (IHf Hwtf Hlff Hubf
                (fun x Hx => Hfv x (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))))
                (fun x wx Hx Ha => Hdisj x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))) Ha))
      as (Hwtf' & Hbwf' & Hlff' & Hubf' & Hfvf').
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hbwc', Hbwt', Hbwf', Hwtc', Hwtt', Hwtf', Hbwc, Hbwt, Hbwf, Hlfc', Hlft', Hlff', Hubc', Hubt', Hubf'.
    repeat split; try reflexivity.
    intros x Hx; apply in_app_iff in Hx as [Hx | Hx];
      [exact (Hfvc' x Hx) | apply in_app_iff in Hx as [Hx | Hx]; [exact (Hfvt' x Hx) | exact (Hfvf' x Hx)]].
  - rewrite !andb_true_iff in Hwt; destruct Hwt as [Hwto Hbwo].
    destruct (IHo Hwto Hlf Hub Hfv Hdisj) as (Hwto' & Hbwo' & Hlfo' & Hubo' & Hfvo').
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hwto', Hbwo', Hbwo, Hlfo', Hubo'.
    repeat split; try reflexivity; exact Hfvo'.
  - discriminate Hlf.
Qed.

Lemma subst_cert_expr_eval {Pa : Params} :
  forall sub (penv_c penv_src : param_env Pa) foracle e,
    (forall w x y, foracle w x = foracle w y) ->
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) ->
       match lookup_subst nm sub with
       | Some (w', e') =>
           w = w' /\
           exists dv,
             penv_c nm = Some dv /\
             wf_scalar_dvalue w dv /\
             eval_closed_cert_expr penv_src foracle e' = raise_ret dv
       | None => penv_c nm = penv_src nm
       end) ->
    eval_closed_cert_expr penv_c foracle e =
    eval_closed_cert_expr penv_src foracle (subst_cert_expr sub e).
Proof.
  intros sub penv_c penv_src foracle e Hfrz.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hag;
    unfold eval_closed_cert_expr in *;
    cbn [subst_cert_expr is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *.
  - reflexivity.
  - reflexivity.
  - pose proof (Hag nm w (or_introl eq_refl)) as Hn.
    destruct (lookup_subst nm sub) as [[w' e'] |].
    + destruct Hn as [<- [dv [Hp [Hsc Hev]]]].
      rewrite Pos.eqb_refl, Hp, Hev.
      destruct Hsc as [-> | [v ->]]; cbn [check_scalar_width]; [reflexivity | rewrite Pos.eqb_refl; reflexivity].
    + rewrite Hn; reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hlfc Hlft] Hlff].
    rewrite (IHc Hlfc (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHt Hlft (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))))),
            (IHf Hlff (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))))); reflexivity.
  - rewrite (IHo Hlf Hag).
    destruct (eval_cert_expr penv_src [] foracle (subst_cert_expr sub o)); cbn [eou_bind]; try reflexivity.
    match goal with d : @dvalue Pa |- _ => destruct d; try reflexivity end.
    match goal with b : @dvalue_base Pa |- _ => destruct b; try reflexivity end.
    rewrite (Hfrz w (expand_lets_with (let_val_exprs []) o)
                    (expand_lets_with (let_val_exprs []) (subst_cert_expr sub o))).
    reflexivity.
  - discriminate Hlf.
Qed.

(** ** 2. General Pure-SSA IR Segment Reification ([ir_seg_tree], [reify_ir_seg]) *)

Inductive ir_seg_tree : Type :=
| IST_Cut (lmap_cut : rmap (positive * cert_expr)) (phi_vals : list (positive * cert_expr))
| IST_Ret (ret_w : positive) (ret_e : cert_expr)
| IST_UB
| IST_Branch (cond : cert_expr) (on_t on_f : ir_seg_tree).

Definition extract_hdr_phi_widths (phis : list (raw_id * positive)) : list positive :=
  List.map snd phis.

Fixpoint wrap_cut_mc_at
  (idx : nat) (base : rmap (positive * cert_expr)) (hspecs : list (raw_id * positive))
  {struct hspecs} : rmap (positive * cert_expr) :=
  match hspecs with
  | [] => base
  | (id, w) :: rest =>
      RM.add id (w, CE_Var (mc_cut_var_name idx) w) (wrap_cut_mc_at (S idx) base rest)
  end.

Definition wrap_cut_mc (base : rmap (positive * cert_expr)) (hspecs : list (raw_id * positive))
  : rmap (positive * cert_expr) :=
  wrap_cut_mc_at 0%nat base hspecs.

Fixpoint cut_vars_from (idx : nat) (hspecs : list (raw_id * positive))
  {struct hspecs} : list (string * positive) :=
  match hspecs with
  | [] => []
  | (_, w) :: rest => (mc_cut_var_name idx, w) :: cut_vars_from (S idx) rest
  end.

Definition cevals_ub_free (cevals : list cert_expr) : bool :=
  forallb ub_free_expr cevals.

Fixpoint check_list_eq_id_w (xs ys : list (raw_id * positive)) {struct xs} : bool :=
  match xs, ys with
  | [], [] => true
  | (ix, wx) :: rx, (iy, wy) :: ry =>
      raw_id_eqb ix iy && Pos.eqb wx wy && check_list_eq_id_w rx ry
  | _, _ => false
  end.

Definition mc_raw_id_name (id : raw_id) : string :=
  cert_raw_id_bare id.

Definition mc_sum_map {E A B : Type} (f : A -> B) (r : E + A) : E + B :=
  match r with
  | inl err => inl err
  | inr a => inr (f a)
  end.

Fixpoint mc_find_dup_raw_id (xs : list raw_id) : option raw_id :=
  match xs with
  | [] => None
  | x :: rest => if raw_id_in_list x rest then Some x else mc_find_dup_raw_id rest
  end.

Fixpoint mc_find_overlap_raw_id (xs ys : list raw_id) : option raw_id :=
  match xs with
  | [] => None
  | x :: rest => if raw_id_in_list x ys then Some x else mc_find_overlap_raw_id rest ys
  end.

Definition mc_format_first_dup_raw_id (xs : list raw_id) : string :=
  match mc_find_dup_raw_id xs with
  | Some id => mc_raw_id_name id
  | None => "<unknown>"
  end.

Definition mc_format_first_overlap_raw_id (xs ys : list raw_id) : string :=
  match mc_find_overlap_raw_id xs ys with
  | Some id => mc_raw_id_name id
  | None => "<unknown>"
  end.

Fixpoint mc_find_first_bang_var (xs : list (string * positive)) : option string :=
  match xs with
  | [] => None
  | (nm, _) :: rest => if mc_starts_with_bang nm then Some nm else mc_find_first_bang_var rest
  end.

Definition mc_format_first_bang_var (xs : list (string * positive)) : string :=
  match mc_find_first_bang_var xs with
  | Some nm => nm
  | None => "<unknown>"
  end.

Fixpoint mc_find_missing_var
  (allowed vs : list (string * positive)) : option (string * positive) :=
  match vs with
  | [] => None
  | (nm, w) :: rest =>
      if vars_subset_b [(nm, w)] allowed then mc_find_missing_var allowed rest
      else Some (nm, w)
  end.

Definition mc_format_missing_var (allowed : list (string * positive)) (e : cert_expr) : string :=
  match mc_find_missing_var allowed (collect_free_vars [] e) with
  | Some (nm, w) => (nm ++ ":i" ++ diag_pos_dec w)%string
  | None => "<unknown>"
  end.

Fixpoint reify_ir_seg
  (phase : string) (fuel : nat) (bmap : rmap (block dtyp)) (hdr_id : block_id)
  (hdr_phis : list (raw_id * positive)) (req_step : bool) (visited : list block_id)
  (bid_from cur_bid : block_id) (lmap : rmap (positive * cert_expr))
  {struct fuel} : string + ir_seg_tree :=
  let loc (_ : unit) : string :=
    (phase ++ " IR segment at block '" ++ mc_raw_id_name cur_bid ++
     if req_step then "'"
     else "' (from '" ++ mc_raw_id_name bid_from ++ "')")%string
  in
  if negb req_step && raw_id_eqb cur_bid hdr_id then
    match RM.find cur_bid bmap with
    | None => inl (diag "mc-loop-ir" ("missing header block in " ++ loc tt))
    | Some b_hdr =>
        match reify_pure_phis bid_from lmap (blk_phis b_hdr) with
        | None => inl (diag "mc-loop-ir" ("unsupported header phi expression in " ++ loc tt))
        | Some pevals =>
            let got := List.map (fun '(id, w, _) => (id, w)) pevals in
            if negb (check_list_eq_id_w got hdr_phis) then
              inl (diag "mc-loop-ir" ("header phi list/width mismatch in " ++ loc tt))
            else if negb (pevals_ub_free pevals) then
              inl (diag "mc-loop-ir" ("non-UB-free header phi expression in " ++ loc tt))
            else
              inr (IST_Cut lmap (List.map (fun '(_, w, ce) => (w, ce)) pevals))
        end
    end
  else if raw_id_in_list cur_bid visited then
    inl (diag "mc-loop-ir" ("inner cycle detected in " ++ loc tt))
  else
    match fuel with
    | O => inl (diag "mc-loop-ir" ("CFG fuel exhausted in " ++ loc tt))
    | S fuel' =>
        match RM.find cur_bid bmap with
        | None => inl (diag "mc-loop-ir" ("missing CFG block in " ++ loc tt))
        | Some b =>
            let visited' := cur_bid :: visited in
            let lmap_phis_res : string + rmap (positive * cert_expr) :=
              if req_step then inr lmap
              else
                match reify_pure_phis bid_from lmap (blk_phis b) with
                | None => inl (diag "mc-loop-ir" ("unsupported phi instruction in " ++ loc tt))
                | Some pevals =>
                    if pevals_ub_free pevals then inr (apply_reified_phis lmap pevals)
                    else inl (diag "mc-loop-ir" ("non-UB-free phi incoming value in " ++ loc tt))
                end
            in
            match lmap_phis_res with
            | inl err => inl err
            | inr lmap1 =>
                match reify_pure_code lmap1 (blk_code b) with
                | None => inl (diag "mc-loop-ir" ("unsupported non-pure instruction in " ++ loc tt))
                | Some (cevals, lmap2) =>
                    if negb (cevals_ub_free cevals) then
                      inl (diag "mc-loop-ir" ("non-UB-free instruction expression in " ++ loc tt))
                    else
                      let '(_, term) := fst (blk_term b) in
                      match term with
                      | TERM_Unreachable => inr IST_UB
                      | TERM_Ret (DTYPE_Base (DTYPE_I rw), op) =>
                          if is_supported_bit_width rw then
                            match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I rw))) op with
                            | Some (_, ret_e) =>
                                if ub_free_expr ret_e then inr (IST_Ret rw ret_e)
                                else inl (diag "mc-loop-ir" ("non-UB-free return expression in " ++ loc tt))
                            | None => inl (diag "mc-loop-ir" ("unsupported return operand in " ++ loc tt))
                            end
                          else inl (diag "mc-loop-ir" ("unsupported return width i" ++ diag_pos_dec rw ++ " in " ++ loc tt))
                      | TERM_Br_1 next_bid =>
                          reify_ir_seg phase fuel' bmap hdr_id hdr_phis false visited' cur_bid next_bid lmap2
                      | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2 =>
                          match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                          | Some (_, cond_e) =>
                              if negb (ub_free_expr cond_e) then
                                inl (diag "mc-loop-ir" ("non-UB-free branch condition in " ++ loc tt))
                              else
                                match reify_ir_seg phase fuel' bmap hdr_id hdr_phis false visited' cur_bid br1 lmap2 with
                                | inl err => inl err
                                | inr dt =>
                                    match reify_ir_seg phase fuel' bmap hdr_id hdr_phis false visited' cur_bid br2 lmap2 with
                                    | inl err => inl err
                                    | inr df => inr (IST_Branch cond_e dt df)
                                    end
                                end
                          | None => inl (diag "mc-loop-ir" ("unsupported branch condition in " ++ loc tt))
                          end
                      | _ => inl (diag "mc-loop-ir" ("unsupported terminator in " ++ loc tt))
                      end
                end
            end
        end
    end.

Fixpoint push_phi_ids_acc {A B : Type} (xs : list (raw_id * A * B)) (acc : list raw_id)
  {struct xs} : list raw_id :=
  match xs with
  | [] => acc
  | (id, _, _) :: rest => push_phi_ids_acc rest (id :: acc)
  end.

Fixpoint code_written_ids_acc (c : code dtyp) (acc : list raw_id) {struct c} : list raw_id :=
  match c with
  | [] => acc
  | (IId id, _, _) :: rest => code_written_ids_acc rest (id :: acc)
  | (IVoid _, _, _) :: rest => code_written_ids_acc rest acc
  end.

Fixpoint ir_seg_written_ids_acc (phase : string) (fuel : nat) (bmap : rmap (block dtyp)) (hdr_id : block_id)
  (req_step : bool) (visited : list block_id) (cur_bid : block_id) (acc : list raw_id)
  {struct fuel} : string + list raw_id :=
  let loc (_ : unit) : string :=
    (phase ++ " IR segment at block '" ++ mc_raw_id_name cur_bid ++ "'")%string
  in
  if negb req_step && raw_id_eqb cur_bid hdr_id then inr acc
  else if raw_id_in_list cur_bid visited then
    inl (diag "mc-loop-ir" ("inner cycle collecting written IDs in " ++ loc tt))
  else
    match fuel with
    | O => inl (diag "mc-loop-ir" ("CFG fuel exhausted collecting written IDs in " ++ loc tt))
    | S fuel' =>
        match RM.find cur_bid bmap with
        | None => inl (diag "mc-loop-ir" ("missing CFG block collecting written IDs in " ++ loc tt))
        | Some b =>
            let visited' := cur_bid :: visited in
            let acc_ph := if req_step then acc else push_phi_ids_acc (blk_phis b) acc in
            let acc' := code_written_ids_acc (blk_code b) acc_ph in
            let '(_, term) := fst (blk_term b) in
            match term with
            | TERM_Unreachable | TERM_Ret _ => inr acc'
            | TERM_Br_1 next_bid =>
                ir_seg_written_ids_acc phase fuel' bmap hdr_id false visited' next_bid acc'
            | TERM_Br _ br1 br2 =>
                match ir_seg_written_ids_acc phase fuel' bmap hdr_id false visited' br1 acc' with
                | inr wr1 => ir_seg_written_ids_acc phase fuel' bmap hdr_id false visited' br2 wr1
                | inl err => inl err
                end
            | _ => inl (diag "mc-loop-ir" ("unsupported terminator collecting written IDs in " ++ loc tt))
            end
        end
    end.

Definition ir_seg_written_ids (phase : string) (fuel : nat) (bmap : rmap (block dtyp)) (hdr_id : block_id)
  (req_step : bool) (visited : list block_id) (cur_bid : block_id)
  : string + list raw_id :=
  ir_seg_written_ids_acc phase fuel bmap hdr_id req_step visited cur_bid [].

Fixpoint collect_entry_cut_lmaps (t : ir_seg_tree) : list (rmap (positive * cert_expr)) :=
  match t with
  | IST_Cut lm _ => [lm]
  | IST_Ret _ _ | IST_UB => []
  | IST_Branch _ dt df => collect_entry_cut_lmaps dt ++ collect_entry_cut_lmaps df
  end.

Definition intersect_lmaps (l1 l2 : rmap (positive * cert_expr))
  : rmap (positive * cert_expr) :=
  RM.fold (fun k '(w1, e1) acc =>
    match RM.find k l2 with
    | Some (w2, e2) =>
        if Pos.eqb w1 w2 && cert_expr_eqb e1 e2 then RM.add k (w1, e1) acc else acc
    | None => acc
    end) l1 (RM.empty (positive * cert_expr)).

Fixpoint common_cut_lmap (base : rmap (positive * cert_expr)) (lms : list (rmap (positive * cert_expr)))
  {struct lms} : rmap (positive * cert_expr) :=
  match lms with
  | [] => base
  | [lm] => lm
  | lm :: rest => intersect_lmaps lm (common_cut_lmap base rest)
  end.

Definition lmap_keys (lm : rmap (positive * cert_expr)) : list raw_id :=
  List.map fst (RM.elements lm).

Lemma check_list_eq_id_w_spec : forall xs ys,
  check_list_eq_id_w xs ys = true -> xs = ys.
Proof.
  induction xs as [| [ix wx] rx IH]; intros [| [iy wy] ry] H; cbn in H; try discriminate H; [reflexivity |].
  rewrite !andb_true_iff in H; destruct H as [[Hid Hw] Hr].
  apply raw_id_eqb_eq in Hid; apply Pos.eqb_eq in Hw; subst iy wy.
  rewrite (IH _ Hr); reflexivity.
Qed.

Lemma in_lmap_keys_iff : forall lm r,
  In r (lmap_keys lm) <-> exists v, RM.find r lm = Some v.
Proof.
  intros lm r; unfold lmap_keys; split.
  - intro Hin; apply in_map_iff in Hin as [[k v] [<- Hin]].
    exists v; apply RM.find_1, RM.elements_2.
    clear -Hin; induction (RM.elements lm) as [| [k' v'] rest IH]; [contradiction |].
    destruct Hin as [Heq | Hin].
    + inversion Heq; constructor 1; split; reflexivity.
    + constructor 2; exact (IH Hin).
  - intros [v Hf]; pose proof (RM.elements_1 (RM.find_2 Hf)) as Hina.
    apply in_map_iff; induction Hina as [[k' v'] rest [Heqk Heqv] | [k' v'] rest _ IH].
    + cbn in Heqk, Heqv; subst k' v'; exists (r, v); split; [reflexivity | left; reflexivity].
    + destruct IH as [[k0 v0] [Hk0 Hin0]]; exists (k0, v0); split; [exact Hk0 | right; exact Hin0].
Qed.

Lemma in_intersect_lmaps : forall l1 l2 r w e,
  RM.find r (intersect_lmaps l1 l2) = Some (w, e) ->
  RM.find r l1 = Some (w, e) /\ RM.find r l2 = Some (w, e).
Proof.
  intros l1 l2 r w e Hf; unfold intersect_lmaps in Hf.
  rewrite RM.fold_1 in Hf.
  remember (RM.elements l1) as xs.
  assert (Hspec : forall init,
    (forall r0 w0 e0, RM.find r0 init = Some (w0, e0) -> RM.find r0 l1 = Some (w0, e0) /\ RM.find r0 l2 = Some (w0, e0)) ->
    (forall k v, In (k, v) xs -> RM.find k l1 = Some v) ->
    RM.find r (List.fold_left (fun acc p =>
      (fun k '(w1, e1) acc0 =>
        match RM.find k l2 with
        | Some (w2, e2) => if Pos.eqb w1 w2 && cert_expr_eqb e1 e2 then RM.add k (w1, e1) acc0 else acc0
        | None => acc0
        end) (fst p) (snd p) acc) xs init) = Some (w, e) ->
    RM.find r l1 = Some (w, e) /\ RM.find r l2 = Some (w, e)).
  { clear Hf Heqxs; induction xs as [| [k [w1 e1]] rest IH]; intros init Hinit Hxs Hres; cbn in Hres.
    - exact (Hinit r w e Hres).
    - eapply IH; [| intros k0 v0 Hk0; exact (Hxs k0 v0 (or_intror Hk0)) | exact Hres].
      intros r0 w0 e0 Hr0; cbn [fst snd] in Hr0.
      destruct (RM.find k l2) as [[w2 e2] |] eqn:Hl2; [| exact (Hinit r0 w0 e0 Hr0)].
      destruct (Pos.eqb w1 w2 && cert_expr_eqb e1 e2) eqn:Eeq; [| exact (Hinit r0 w0 e0 Hr0)].
      apply andb_true_iff in Eeq as [Hw_eq He_eq]; apply Pos.eqb_eq in Hw_eq; apply cert_expr_eqb_eq in He_eq; subst w2 e2.
      destruct (RawIDOrd.eq_dec k r0) as [-> | Hneq].
      + rewrite RMF.F.add_eq_o in Hr0 by reflexivity; inversion Hr0; subst w0 e0.
        split; [exact (Hxs r0 (w1, e1) (or_introl eq_refl)) | exact Hl2].
      + rewrite RMF.F.add_neq_o in Hr0 by exact Hneq; exact (Hinit r0 w0 e0 Hr0). }
  eapply Hspec with (init := RM.empty (positive * cert_expr)); [| | exact Hf].
  - intros r0 w0 e0 H0; rewrite RMF.F.empty_o in H0; discriminate H0.
  - intros k v Hk; rewrite Heqxs in Hk; apply RM.find_1, RM.elements_2.
    clear -Hk; induction (RM.elements l1) as [| [k' v'] rest IH]; [contradiction |].
    destruct Hk as [Heq | Hk]; [inversion Heq; constructor 1; split; reflexivity | constructor 2; exact (IH Hk)].
Qed.

Lemma common_cut_lmap_in : forall base lms lm,
  In lm lms ->
  forall r w e, RM.find r (common_cut_lmap base lms) = Some (w, e) -> RM.find r lm = Some (w, e).
Proof.
  intros base lms; induction lms as [| lm0 rest IH]; intros lm Hin r w e Hf; [contradiction |].
  destruct rest as [| lm1 rest'].
  - destruct Hin as [<- | []]; exact Hf.
  - cbn [common_cut_lmap] in Hf.
    apply in_intersect_lmaps in Hf as [H0 Hr].
    destruct Hin as [<- | Hinr]; [exact H0 | exact (IH lm Hinr r w e Hr)].
Qed.

Lemma wrap_cut_mc_at_wf : forall idx allowed lmap hspecs,
  wf_pure_lmap allowed lmap ->
  wf_pure_lmap (allowed ++ cut_vars_from idx hspecs) (wrap_cut_mc_at idx lmap hspecs).
Proof.
  intros idx allowed lmap hspecs; revert idx lmap;
    induction hspecs as [| [id w] rest IH]; intros idx lmap Hlmap; cbn [wrap_cut_mc_at cut_vars_from].
  - rewrite app_nil_r; exact Hlmap.
  - assert (Hrec : wf_pure_lmap (allowed ++ cut_vars_from (S idx) rest) (wrap_cut_mc_at (S idx) lmap rest))
      by (exact (IH (S idx) lmap Hlmap)).
    assert (Hmono : wf_pure_lmap (allowed ++ (mc_cut_var_name idx, w) :: cut_vars_from (S idx) rest)
                      (wrap_cut_mc_at (S idx) lmap rest)).
    { intros r wr cer Hr; destruct (Hrec r wr cer Hr) as (Hwt & Hbw & Hlf & Hfv); repeat split; try assumption.
      eapply incl_tran; [exact Hfv | intros [x wx] Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]]. }
    apply wf_pure_lmap_add; try assumption; try reflexivity.
    intros [x wx] [Hx | []]; inversion Hx; subst; apply in_app_iff; right; left; reflexivity.
Qed.

Lemma wrap_cut_mc_at_preserves : forall idx lmap hspecs id,
  ~ In id (List.map fst hspecs) ->
  RM.find id (wrap_cut_mc_at idx lmap hspecs) = RM.find id lmap.
Proof.
  intros idx lmap hspecs; revert idx; induction hspecs as [| [i0 w0] rest IH];
    intros idx id Hnin; cbn [wrap_cut_mc_at List.map] in *; [reflexivity |].
  rewrite RMF.F.add_neq_o by (intro Heq; apply Hnin; left; exact Heq).
  exact (IH (S idx) id (fun H => Hnin (or_intror H))).
Qed.

Definition ir_seg_wf (allowed : list (string * positive)) (hdr_ws : list positive) (t : ir_seg_tree) : Prop :=
  (forall lm, In lm (collect_entry_cut_lmaps t) -> wf_pure_lmap allowed lm) /\
  (let fix go (u : ir_seg_tree) : Prop :=
     match u with
     | IST_Cut _ phis =>
         Forall2 (fun w '(wp, ce) =>
           w = wp /\ wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
           is_let_free_expr ce = true /\ ub_free_expr ce = true /\ incl (collect_free_vars [] ce) allowed)
           hdr_ws phis
     | IST_Ret rw ret_e =>
         is_supported_bit_width rw = true /\
         wt_cert_expr [] ret_e = true /\
         cert_expr_bit_width ret_e = rw /\
         is_let_free_expr ret_e = true /\
         ub_free_expr ret_e = true /\
         incl (collect_free_vars [] ret_e) allowed
     | IST_UB => True
     | IST_Branch cond dt df =>
         wt_cert_expr [] cond = true /\
         cert_expr_bit_width cond = 1%positive /\
         is_let_free_expr cond = true /\
         ub_free_expr cond = true /\
         incl (collect_free_vars [] cond) allowed /\
         go dt /\ go df
     end in go t).

Lemma pevals_to_ist_cut_wf : forall pevals allowed,
  pevals_ub_free pevals = true ->
  Forall (fun '(_, w, ce) =>
    is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals ->
  Forall2 (fun w '(wp, ce) =>
    w = wp /\ wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
    is_let_free_expr ce = true /\ ub_free_expr ce = true /\ incl (collect_free_vars [] ce) allowed)
    (extract_hdr_phi_widths (List.map (fun '(id, w, _) => (id, w)) pevals))
    (List.map (fun '(_, w, ce) => (w, ce)) pevals).
Proof.
  induction pevals as [| [[id w] ce] rest IH]; intros allowed Eub Htp; cbn in *; [constructor |].
  unfold pevals_ub_free in Eub; cbn [forallb] in Eub; apply andb_true_iff in Eub as [Ece Eub_rest].
  inversion Htp as [| ? ? Hhd Htpre]; subst; destruct Hhd as (_ & Hbw & (Hwt & Hlf & Hfv)).
  constructor; [repeat split; assumption | exact (IH allowed Eub_rest Htpre)].
Qed.

Lemma reify_ir_seg_wf :
  forall phase fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap allowed t,
    wf_pure_lmap allowed lmap ->
    reify_ir_seg phase fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap = inr t ->
    ir_seg_wf allowed (extract_hdr_phi_widths hdr_phis) t.
Proof.
  intros phase fuel; induction fuel as [| fuel' IH];
    intros bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap allowed t Hlmap Hr;
    cbn [reify_ir_seg] in Hr.
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id); [| destruct (raw_id_in_list cur_bid visited); discriminate Hr].
    destruct (RM.find cur_bid bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
    destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
    destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis) eqn:Eids;
      cbn [negb] in Hr; [| discriminate Hr].
    destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in Hr; [| discriminate Hr].
    apply check_list_eq_id_w_spec in Eids.
    inversion Hr; subst t; clear Hr.
    split; [intros lm [<- | []]; exact Hlmap |].
    rewrite <- Eids; exact (pevals_to_ist_cut_wf pevals allowed Eub (reify_pure_phis_typing (blk_phis b_hdr) allowed bid_from lmap pevals Hlmap Erp)).
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id).
    + destruct (RM.find cur_bid bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
      destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
      destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis) eqn:Eids;
        cbn [negb] in Hr; [| discriminate Hr].
      destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in Hr; [| discriminate Hr].
      apply check_list_eq_id_w_spec in Eids.
      inversion Hr; subst t; clear Hr.
      split; [intros lm [<- | []]; exact Hlmap |].
      rewrite <- Eids; exact (pevals_to_ist_cut_wf pevals allowed Eub (reify_pure_phis_typing (blk_phis b_hdr) allowed bid_from lmap pevals Hlmap Erp)).
    + destruct (raw_id_in_list cur_bid visited); [discriminate Hr |].
      destruct (RM.find cur_bid bmap) as [b |] eqn:Efb; [| discriminate Hr].
      match type of Hr with
      | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1] eqn:El1
      end; [discriminate Hr |].
      assert (Hlmap1 : wf_pure_lmap allowed lmap1).
      { destruct req_step; [inversion El1; subst; exact Hlmap |].
        destruct (reify_pure_phis bid_from lmap (blk_phis b)) as [pevals |] eqn:Erp; [| discriminate El1].
        destruct (pevals_ub_free pevals); inversion El1; subst lmap1.
        exact (apply_reified_phis_wf pevals allowed lmap Hlmap (reify_pure_phis_typing _ _ _ _ _ Hlmap Erp)). }
      destruct (reify_pure_code lmap1 (blk_code b)) as [[cevals lmap2] |] eqn:Erc; [| discriminate Hr].
      destruct (negb (cevals_ub_free cevals)); [discriminate Hr |].
      destruct (reify_pure_code_typing (blk_code b) allowed lmap1 cevals lmap2 Hlmap1 Erc) as [_ Hlmap2].
      destruct (blk_term b) as [[tid term] tmd] eqn:Etm; cbn [fst] in Hr.
      destruct term; try discriminate Hr.
      * destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hr.
        destruct (is_supported_bit_width rw) eqn:Esup; [| discriminate Hr].
        destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I rw))) op) as [[rw0 ret_e] |] eqn:Ere; [| discriminate Hr].
        destruct (ub_free_expr ret_e) eqn:Eub; inversion Hr; subst t; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Ere)) as ->.
        destruct (reify_pure_exp_typing op allowed lmap2 (Some (DTYPE_Base (DTYPE_I rw))) rw ret_e Hlmap2 Ere) as (_ & Hwt & Hbw & Hlf & Hfv).
        split; [intros lm Hlm; contradiction | repeat split; assumption].
      * match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hr.
        destruct rw; try discriminate Hr.
        destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) e_cond) as [[cw cond_e] |] eqn:Ercd; [| discriminate Hr].
        destruct (ub_free_expr cond_e) eqn:Eub; [cbn [negb] in Hr | discriminate Hr].
        destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2) as [| dt] eqn:Hdt; [discriminate Hr |].
        destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2) as [| df] eqn:Hdf; [discriminate Hr |].
        inversion Hr; subst t; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Ercd)) as ->.
        destruct (reify_pure_exp_typing e_cond allowed lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cond_e Hlmap2 Ercd) as (_ & Hwt & Hbw & Hlf & Hfv).
        destruct (IH _ _ _ _ _ _ _ _ _ _ Hlmap2 Hdt) as [Hlms_t Hwf_t].
        destruct (IH _ _ _ _ _ _ _ _ _ _ Hlmap2 Hdf) as [Hlms_f Hwf_f].
        split; [intros lm Hin; apply in_app_iff in Hin as [Hin | Hin]; [exact (Hlms_t lm Hin) | exact (Hlms_f lm Hin)] | repeat split; assumption].
      * exact (IH _ _ _ _ _ _ _ _ _ _ Hlmap2 Hr).
      * inversion Hr; subst t; split; [intros lm Hlm; contradiction | exact I].
Qed.

Fixpoint ir_seg_eval_spec {Pa : Params}
  (bmap : rmap (block dtyp)) (hdr_id : block_id) (hdr_phis : list (raw_id * positive))
  (wr_keep : list raw_id) (penv : param_env Pa)
  (env0 : rmap (@dvalue Pa)) (bid_from cur_bid : block_id)
  (t : ir_seg_tree) {struct t} : Prop :=
  match t with
  | IST_Cut lmap_cut phis =>
      (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
      exists env_c bid_c b_hdr dvs,
        ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
         pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
           env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
        RM.find hdr_id bmap = Some b_hdr /\
        lmap_matches_env penv lmap_cut env_c /\
        (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
        Forall2 (fun '(wp, ce) '(_, dv) =>
          eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
          wf_scalar_dvalue wp dv) phis dvs /\
        Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
        pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt
  | IST_Ret _ ret_e =>
      (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
      exists env_out dv_ir,
        pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
        eval_closed_cert_expr penv dummy_freeze_oracle ret_e = raise_ret dv_ir
  | IST_UB =>
      forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
  | IST_Branch cond dt df =>
      (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
      exists env_mid bid_step br_t br_f (b : bool),
        pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
          env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f)) /\
        eval_closed_cert_expr penv dummy_freeze_oracle cond =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
        (forall r, In r wr_keep -> RM.find r env_mid = RM.find r env0) /\
        ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv env_mid bid_step (if b then br_t else br_f) (if b then dt else df)
  end.

Lemma ir_seg_eval_spec_step_front {Pa : Params} :
  forall bmap hdr_id hdr_phis wr_keep penv env0 env1 bf0 cb0 bf1 cb1 t,
    @pure_cfg_steps_to_tau Pa (@dvalue Pa) env0 (@denote_cfg_from Pa bmap None (bf0, cb0))
      env1 (@denote_cfg_from Pa bmap None (bf1, cb1)) ->
    (forall r, In r wr_keep -> RM.find r env1 = RM.find r env0) ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv env1 bf1 cb1 t ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv env0 bf0 cb0 t.
Proof.
  intros bmap hdr_id hdr_phis wr_keep penv env0 env1 bf0 cb0 bf1 cb1 t Htau Hpres Hspec.
  destruct t as [lm phis | rw ret_e | | cond dt df]; cbn [ir_seg_eval_spec] in *.
  - destruct Hspec as [Hub | (env_c & bid_c & b_hdr & dvs & Htau2 & Ebh & Hlm & Hk2 & Hph & Hids & Hst)].
    + left; intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hub sigma)).
    + right; exists env_c, bid_c, b_hdr, dvs;
        repeat split; try assumption;
        [right; destruct Htau2 as [[-> [-> ->]] | Htau2];
           [exact Htau | exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau Htau2)]
        | intros r Hr; rewrite (Hk2 r Hr), (Hpres r Hr); reflexivity].
  - destruct Hspec as [Hub | (env_out & dv_ir & Hst & Hev)].
    + left; intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hub sigma)).
    + right; exists env_out, dv_ir; split; [exact (pure_cfg_steps_to_tau_then_ret _ _ _ _ _ _ Htau Hst) | exact Hev].
  - intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hspec sigma)).
  - destruct Hspec as [Hub | (env_mid & bid_step & br_t & br_f & b & Htau2 & Hevc & Hk2 & Hsub)].
    + left; intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hub sigma)).
    + right; exists env_mid, bid_step, br_t, br_f, b;
        repeat split; try assumption;
        [exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau Htau2)
        | intros r Hr; rewrite (Hk2 r Hr), (Hpres r Hr); reflexivity].
Qed.

Lemma apply_phi_env_preserves_not_in_dvs {Pa : Params} :
  forall (pevals : list (raw_id * positive * cert_expr)) (dvs : list (raw_id * @dvalue Pa)) penv env r,
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    ~ In r (List.map (fun '(id, _, _) => id) pevals) ->
    RM.find r (apply_phi_env env dvs) = RM.find r env.
Proof.
  intros pevals dvs penv env r Hfa2; revert env;
    induction Hfa2 as [| [[id w] ce] [id' dv] restp restdvs Hpair Hrest IH];
    intros env Hnin; cbn [apply_phi_env List.map] in *; [reflexivity |].
  destruct Hpair as [Heq _]; subst id'.
  rewrite IH by (intro H; apply Hnin; right; exact H).
  rewrite RMF.F.add_neq_o; [reflexivity | intro H; apply Hnin; left; exact H].
Qed.

Lemma push_phi_ids_acc_app : forall {A B : Type} (xs : list (raw_id * A * B)) acc1 acc2,
  push_phi_ids_acc xs (acc1 ++ acc2) = push_phi_ids_acc xs acc1 ++ acc2.
Proof.
  intros A B xs; induction xs as [| [[id a] b] rest IH]; intros acc1 acc2;
    cbn [push_phi_ids_acc]; [reflexivity | exact (IH (id :: acc1) acc2)].
Qed.

Lemma code_written_ids_acc_app : forall c acc1 acc2,
  code_written_ids_acc c (acc1 ++ acc2) = code_written_ids_acc c acc1 ++ acc2.
Proof.
  induction c as [| [[iid ins] md] rest IH]; intros acc1 acc2;
    cbn [code_written_ids_acc]; [reflexivity | destruct iid; [exact (IH (id :: acc1) acc2) | exact (IH acc1 acc2)]].
Qed.

Lemma push_phi_ids_acc_in : forall {A B : Type} (xs : list (raw_id * A * B)) acc r,
  In r (push_phi_ids_acc xs acc) <-> In r (List.map (fun '(id, _, _) => id) xs) \/ In r acc.
Proof.
  intros A B xs; induction xs as [| [[id a] b] rest IH]; intros acc r;
    cbn [push_phi_ids_acc List.map In]; [tauto |].
  rewrite IH; cbn [In]; tauto.
Qed.

Lemma code_written_ids_acc_in : forall c acc r,
  In r (code_written_ids_acc c acc) <-> In r (code_written_ids c) \/ In r acc.
Proof.
  induction c as [| [[iid ins] md] rest IH]; intros acc r;
    unfold code_written_ids in *; cbn [code_written_ids_acc List.flat_map In]; [tauto |].
  destruct iid; cbn [In app]; [rewrite IH; cbn [In]; tauto | exact (IH acc r)].
Qed.

Lemma ir_seg_written_ids_acc_shift :
  forall phase fuel bmap hdr_id req_step visited cur_bid acc,
    ir_seg_written_ids_acc phase fuel bmap hdr_id req_step visited cur_bid acc =
    mc_sum_map (fun d => d ++ acc)
      (ir_seg_written_ids_acc phase fuel bmap hdr_id req_step visited cur_bid []).
Proof.
  intros phase fuel; induction fuel as [| fuel' IH];
    intros bmap hdr_id req_step visited cur_bid acc;
    cbn [ir_seg_written_ids_acc].
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id); [reflexivity |].
    destruct (raw_id_in_list cur_bid visited); reflexivity.
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id); [reflexivity |].
    destruct (raw_id_in_list cur_bid visited); [reflexivity |].
    destruct (RM.find cur_bid bmap) as [b |]; [| reflexivity].
    destruct (blk_term b) as [[tid term] tmd]; cbn [fst].
    set (base := code_written_ids_acc (blk_code b)
                   (if req_step then [] else push_phi_ids_acc (blk_phis b) [])).
    assert (Happ : code_written_ids_acc (blk_code b)
                     (if req_step then acc else push_phi_ids_acc (blk_phis b) acc) =
                   base ++ acc).
    { unfold base; destruct req_step;
        [rewrite <- (app_nil_l acc) at 1 | rewrite <- (app_nil_l acc) at 1; rewrite push_phi_ids_acc_app];
        exact (code_written_ids_acc_app (blk_code b) _ acc). }
    rewrite Happ.
    destruct term; try reflexivity.
    + rewrite IH, (IH _ _ _ _ _ base).
      destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br1 []);
        cbn [mc_sum_map]; [reflexivity |].
      rewrite IH, (IH _ _ _ _ _ (l ++ base));
        destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br2 []);
        cbn [mc_sum_map]; [reflexivity | rewrite !app_assoc; reflexivity].
    + rewrite IH, (IH _ _ _ _ _ base).
      destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br []);
        cbn [mc_sum_map]; [reflexivity | rewrite app_assoc; reflexivity].
Qed.

Lemma ir_seg_written_disjoint_block : forall phase fuel bmap hdr_id req_step visited cur_bid wr_all r,
  ir_seg_written_ids phase fuel bmap hdr_id req_step visited cur_bid = inr wr_all ->
  ~ In r wr_all ->
  negb req_step && raw_id_eqb cur_bid hdr_id = false ->
  raw_id_in_list cur_bid visited = false ->
  forall b, RM.find cur_bid bmap = Some b ->
    (req_step = false -> ~ In r (List.map (fun '(id, _, _) => id) (blk_phis b))) /\
    ~ In r (code_written_ids (blk_code b)).
Proof.
  intros phase fuel bmap hdr_id req_step visited cur_bid wr_all r Hwr Hnin Hnstop Hnvis b Efb.
  unfold ir_seg_written_ids in Hwr.
  destruct fuel as [| fuel']; cbn [ir_seg_written_ids_acc] in Hwr;
    rewrite Hnstop, Hnvis in Hwr; [discriminate Hwr |].
  rewrite Efb in Hwr; destruct (blk_term b) as [[tid term] tmd]; cbn [fst] in Hwr.
  set (acc0 := code_written_ids_acc (blk_code b)
                 (if req_step then [] else push_phi_ids_acc (blk_phis b) [])) in Hwr.
  assert (Hsub : incl acc0 wr_all).
  { destruct term; try discriminate Hwr.
    - inversion Hwr; subst; apply incl_refl.
    - rewrite ir_seg_written_ids_acc_shift in Hwr.
      destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br1 []);
        cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
      rewrite ir_seg_written_ids_acc_shift in Hwr.
      destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br2 []);
        cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
      inversion Hwr; subst wr_all; intros x Hx; apply in_app_iff; right; apply in_app_iff; right; exact Hx.
    - rewrite ir_seg_written_ids_acc_shift in Hwr.
      destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br []);
        cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
      inversion Hwr; subst wr_all; intros x Hx; apply in_app_iff; right; exact Hx.
    - inversion Hwr; subst; apply incl_refl. }
  split.
  - intro Hrs; intro Hin; apply Hnin, Hsub; unfold acc0; rewrite Hrs, code_written_ids_acc_in; right; rewrite push_phi_ids_acc_in; left; exact Hin.
  - intro Hin; apply Hnin, Hsub; unfold acc0; rewrite code_written_ids_acc_in; left; exact Hin.
Qed.

Lemma reify_pure_phis_ids : forall phis bid_from lmap pevals,
  reify_pure_phis bid_from lmap phis = Some pevals ->
  List.map (fun '(id, _, _) => id) pevals = List.map (fun '(id, _, _) => id) phis.
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros bid_from lmap pevals H; cbn [reify_pure_phis List.map] in *.
  - inversion H; reflexivity.
  - destruct dt as [[w | | | | | | | | | |] | |]; try discriminate H.
    destruct (is_supported_bit_width w); [| discriminate H].
    destruct (assoc bid_from pargs); [| discriminate H].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) _) as [[w' ce'] |]; [| discriminate H].
    destruct (reify_pure_phis bid_from lmap rest) as [rrest |] eqn:Hr; [| discriminate H].
    inversion H; subst; cbn; f_equal; exact (IH _ _ _ Hr).
Qed.

Lemma phi_matches_to_ist_cut {Pa : Params} :
  forall penv (pevals : list (raw_id * positive * cert_expr)) (dvs : list (raw_id * @dvalue Pa)) hdr_phis,
    List.map (fun '(id, w, _) => (id, w)) pevals = hdr_phis ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    Forall2 (fun '(wp, ce) '(_, dv) =>
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\ wf_scalar_dvalue wp dv)
      (List.map (fun '(_, w, ce) => (w, ce)) pevals) dvs /\
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs.
Proof.
  intros penv pevals dvs hdr_phis Heq Hfa2; subst hdr_phis; split.
  - induction Hfa2 as [| [[id w] ce] [id' dv] rp rd Hpair Hr IH]; cbn; [constructor | constructor; [exact (proj2 Hpair) | exact IH]].
  - induction Hfa2 as [| [[id w] ce] [id' dv] rp rd Hpair Hr IH]; cbn; [constructor | constructor; [exact (proj1 Hpair) | exact IH]].
Qed.

Lemma reify_ir_seg_sound {Pa : Params} :
  forall phase fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap
         wr_keep wr_all (penv : param_env Pa) env_prev env_hdr t,
    ir_seg_written_ids phase fuel bmap hdr_id req_step visited cur_bid = inr wr_all ->
    disjoint_raw_ids wr_keep wr_all = true ->
    (if req_step then
       exists b,
         RM.find cur_bid bmap = Some b /\
         pure_cfg_steps env_prev (denote_phis bid_from (blk_phis b)) env_hdr tt /\
         (forall r, In r wr_keep -> RM.find r env_hdr = RM.find r env_prev) /\
         lmap_matches_env penv lmap env_hdr
     else
       env_hdr = env_prev /\ lmap_matches_env penv lmap env_prev) ->
    reify_ir_seg phase fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap = inr t ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv env_prev bid_from cur_bid t.
Proof.
  intros phase fuel; induction fuel as [| fuel' IH];
    intros bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap
           wr_keep wr_all penv env_prev env_hdr t Hwr Hdisj Hinit Hr;
    cbn [reify_ir_seg ir_seg_written_ids] in Hr, Hwr.
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id) eqn:Estp;
      [| destruct (raw_id_in_list cur_bid visited); discriminate Hr].
    apply andb_true_iff in Estp as [Hnr Hhd]; apply negb_true_iff in Hnr; apply raw_id_eqb_eq in Hhd; subst cur_bid req_step.
    destruct Hinit as [-> Henv].
    destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
    destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
    destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis) eqn:Eids;
      cbn [negb] in Hr; [| discriminate Hr].
    destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in Hr; [| discriminate Hr].
    apply check_list_eq_id_w_spec in Eids.
    inversion Hr; subst t; clear Hr; cbn [ir_seg_eval_spec].
    destruct (pure_phis_denote_step (blk_phis b_hdr) penv bid_from lmap env_prev pevals Henv Erp)
      as [[Hub _] | [dvs [Hpm Hstp]]].
    + left; intro sigma; eapply denote_cfg_from_block_ub; [exact Ebh |].
      unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub sigma).
    + right; destruct (phi_matches_to_ist_cut penv pevals dvs hdr_phis Eids Hpm) as [Hph1 Hph2].
      exists env_prev, bid_from, b_hdr, dvs;
        split; [left; repeat split; reflexivity | split; [exact Ebh | split; [exact Henv | split; [intros r0 _; reflexivity | split; [exact Hph1 | split; [exact Hph2 | exact Hstp]]]]]].
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id) eqn:Estp.
    + apply andb_true_iff in Estp as [Hnr Hhd]; apply negb_true_iff in Hnr; apply raw_id_eqb_eq in Hhd; subst cur_bid req_step.
      destruct Hinit as [-> Henv].
      destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
      destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
      destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis) eqn:Eids;
        cbn [negb] in Hr; [| discriminate Hr].
      destruct (pevals_ub_free pevals) eqn:Eub; cbn [negb] in Hr; [| discriminate Hr].
      apply check_list_eq_id_w_spec in Eids.
      inversion Hr; subst t; clear Hr; cbn [ir_seg_eval_spec].
      destruct (pure_phis_denote_step (blk_phis b_hdr) penv bid_from lmap env_prev pevals Henv Erp)
        as [[Hub _] | [dvs [Hpm Hstp]]].
      * left; intro sigma; eapply denote_cfg_from_block_ub; [exact Ebh |].
        unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub sigma).
      * right; destruct (phi_matches_to_ist_cut penv pevals dvs hdr_phis Eids Hpm) as [Hph1 Hph2].
        exists env_prev, bid_from, b_hdr, dvs;
          split; [left; repeat split; reflexivity | split; [exact Ebh | split; [exact Henv | split; [intros r0 _; reflexivity | split; [exact Hph1 | split; [exact Hph2 | exact Hstp]]]]]].
    + destruct (raw_id_in_list cur_bid visited) eqn:Evis; [discriminate Hr |].
      destruct (RM.find cur_bid bmap) as [b |] eqn:Efb; [| discriminate Hr].
      assert (Hblk_disj : forall r, In r wr_keep ->
                (req_step = false -> ~ In r (List.map (fun '(id, _, _) => id) (blk_phis b))) /\
                ~ In r (code_written_ids (blk_code b))).
      { intros r Hrk; eapply (ir_seg_written_disjoint_block phase (S fuel') bmap hdr_id req_step visited cur_bid wr_all r);
          [exact Hwr | exact (disjoint_raw_ids_spec _ _ r Hdisj Hrk) | exact Estp | exact Evis | exact Efb]. }
      match type of Hr with
      | match ?x with inl _ => _ | inr _ => _ end = _ => destruct x as [| lmap1] eqn:El1
      end; [discriminate Hr |].
      assert (Hphase1 :
        (forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap None (bid_from, cur_bid))) \/
        exists env1,
          lmap_matches_env penv lmap1 env1 /\
          (forall r, In r wr_keep -> RM.find r env1 = RM.find r env_prev) /\
          pure_cfg_steps env_prev (denote_phis bid_from (blk_phis b)) env1 tt).
      { destruct req_step.
        - inversion El1; subst lmap1.
          destruct Hinit as [b0 [Efb0 [Hstp_p [Hpres_p Hlm_p]]]].
          try rewrite Efb in Efb0; inversion Efb0; subst b0.
          right; exists env_hdr; repeat split; assumption.
        - destruct Hinit as [-> Henv].
          destruct (reify_pure_phis bid_from lmap (blk_phis b)) as [pevals |] eqn:Erp; [| discriminate El1].
          destruct (pevals_ub_free pevals); inversion El1; subst lmap1; clear El1.
          destruct (pure_phis_denote_step (blk_phis b) penv bid_from lmap env_prev pevals Henv Erp)
            as [[Hub _] | [dvs [Hpm Hstp]]].
          + left; intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
            unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub sigma).
          + right; exists (apply_phi_env env_prev dvs); split;
              [exact (apply_reified_phis_matches _ _ _ _ _ Henv Hpm) | split].
            * intros r Hrk; apply (apply_phi_env_preserves_not_in_dvs pevals dvs penv env_prev r Hpm).
              rewrite (reify_pure_phis_ids _ _ _ _ Erp); exact (proj1 (Hblk_disj r Hrk) eq_refl).
            * exact Hstp. }
      destruct (reify_pure_code lmap1 (blk_code b)) as [[cevals lmap2] |] eqn:Erc; [| discriminate Hr].
      destruct (negb (cevals_ub_free cevals)); [discriminate Hr |].
      destruct (blk_term b) as [[tid term] tmd] eqn:Etm; cbn [fst] in Hr;
        unfold ir_seg_written_ids in Hwr; cbn [ir_seg_written_ids_acc] in Hwr;
        rewrite Estp, Evis, Efb, Etm in Hwr; cbn [fst] in Hwr.
      destruct Hphase1 as [Hub_ph | (env1 & Henv1 & Hpres1 & Hstp_ph)].
      { destruct term; try discriminate Hr.
        - destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hr.
          destruct (is_supported_bit_width rw); [| discriminate Hr].
          destruct (reify_pure_exp lmap2 _ op) as [[? ret_e] |]; [| discriminate Hr].
          destruct (ub_free_expr ret_e); inversion Hr; left; exact Hub_ph.
        - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hr; destruct rw; try discriminate Hr.
          destruct (reify_pure_exp lmap2 _ e_cond) as [[? cond_e] |]; [| discriminate Hr].
          destruct (ub_free_expr cond_e); cbn [negb] in Hr; [| discriminate Hr].
          destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2); [discriminate Hr |].
          destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2); inversion Hr; left; exact Hub_ph.
        - destruct t; cbn [ir_seg_eval_spec]; exact Hub_ph || (left; exact Hub_ph).
        - inversion Hr; exact Hub_ph. }
      destruct (eval_reified_pure_code (blk_code b) None penv lmap1 env1 cevals lmap2 Henv1 Erc)
        as [[Hub_c _] | (env2 & Henv2 & _ & Hpres2 & Hst_c)].
      { assert (Hub_all : forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap None (bid_from, cur_bid))).
        { intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
          unfold denote_block; eapply cfg_steps_to_ub_bind_r;
            [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hstp_ph)
            | apply cfg_steps_to_ub_bind_l; exact (Hub_c sigma)]. }
        destruct term; try discriminate Hr.
        - destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hr.
          destruct (is_supported_bit_width rw); [| discriminate Hr].
          destruct (reify_pure_exp lmap2 _ op) as [[? ret_e] |]; [| discriminate Hr].
          destruct (ub_free_expr ret_e); inversion Hr; left; exact Hub_all.
        - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hr; destruct rw; try discriminate Hr.
          destruct (reify_pure_exp lmap2 _ e_cond) as [[? cond_e] |]; [| discriminate Hr].
          destruct (ub_free_expr cond_e); cbn [negb] in Hr; [| discriminate Hr].
          destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2); [discriminate Hr |].
          destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2); inversion Hr; left; exact Hub_all.
        - destruct t; cbn [ir_seg_eval_spec]; exact Hub_all || (left; exact Hub_all).
        - inversion Hr; exact Hub_all. }
      assert (Hpres12 : forall r, In r wr_keep -> RM.find r env2 = RM.find r env_prev).
      { intros r Hrk; rewrite (Hpres2 r (proj2 (Hblk_disj r Hrk))); exact (Hpres1 r Hrk). }
      destruct term; try discriminate Hr.
      * destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hr.
        destruct (is_supported_bit_width rw) eqn:Esup; [| discriminate Hr].
        destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I rw))) op) as [[rw0 ret_e] |] eqn:Ere; [| discriminate Hr].
        destruct (ub_free_expr ret_e); inversion Hr; subst t; clear Hr; cbn [ir_seg_eval_spec].
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Ere)) as ->.
        destruct (eval_reified_pure_exp op penv lmap2 env2 (Some (DTYPE_Base (DTYPE_I rw))) rw ret_e Henv2 Ere)
          as [[Hub_r _] | [dv_r [Hev_r [_ Hst_r]]]].
        -- left; intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
           unfold denote_block; rewrite Etm.
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hstp_ph) |].
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_c) |].
           cbn [denote_terminator]; apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_r sigma).
        -- right; exists env2, dv_r; split; [| exact Hev_r].
           eapply denote_cfg_from_block_ret; [exact Efb |].
           unfold denote_block; rewrite Etm.
           eapply pure_cfg_steps_bind; [exact Hstp_ph |].
           eapply pure_cfg_steps_bind; [exact Hst_c |].
           cbn [denote_terminator]; eapply pure_cfg_steps_bind;
             [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_r) | apply PCS_Ret; reflexivity].
      * match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hr; destruct rw; try discriminate Hr.
        destruct (reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) e_cond) as [[cw cond_e] |] eqn:Ercd; [| discriminate Hr].
        destruct (ub_free_expr cond_e); cbn [negb] in Hr; [| discriminate Hr].
        destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2) as [| dt] eqn:Hdt; [discriminate Hr |].
        destruct (reify_ir_seg phase fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2) as [| df] eqn:Hdf; [discriminate Hr |].
        inversion Hr; subst t; clear Hr; cbn [ir_seg_eval_spec].
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Ercd)) as ->.
        destruct (eval_reified_pure_exp e_cond penv lmap2 env2 (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cond_e Henv2 Ercd)
          as [[Hub_cd _] | [dv_cd [Hev_cd [Hsc_cd Hst_cd]]]].
        -- left; intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
           unfold denote_block; rewrite Etm.
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hstp_ph) |].
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_c) |].
           cbn [denote_terminator]; unfold denote_exp'; apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_cd sigma).
        -- destruct Hsc_cd as [-> | [cbit ->]].
           ++ left; intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
              unfold denote_block; rewrite Etm.
              eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hstp_ph) |].
              eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_c) |].
              cbn [denote_terminator]; unfold denote_exp'.
              eapply cfg_steps_to_ub_bind_r;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst_cd))
                | apply cfg_steps_raiseUB].
           ++ right; exists env2, cur_bid, br1, br2, (@Integers.unsigned 1%positive cbit =? 1)%Z.
              split.
              ** eapply denote_cfg_from_block_jump; [exact Efb |].
                 unfold denote_block; rewrite Etm.
                 eapply pure_cfg_steps_bind; [exact Hstp_ph |].
                 eapply pure_cfg_steps_bind; [exact Hst_c |].
                 cbn [denote_terminator]; unfold denote_exp'.
                 eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_cd) |].
                 cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned.
                 destruct (@Integers.unsigned 1%positive cbit =? 1)%Z; apply PCS_Ret; reflexivity.
              ** split; [| split; [exact Hpres12 |]].
                 --- destruct ((@Integers.unsigned 1%positive cbit =? 1)%Z) eqn:Eb.
                     +++ assert (Hcbit : @Integers.one 1%positive = cbit).
                         { apply Integers.same_bits_eq; intros i Hi; change (@Integers.zwordsize 1%positive) with 1%Z in Hi.
                           assert (Hi0 : i = 0%Z) by lia; subst i.
                           apply Z.eqb_eq in Eb; unfold Integers.testbit; rewrite Eb; reflexivity. }
                         rewrite Hcbit; exact Hev_cd.
                     +++ assert (Hcbit : @Integers.zero 1%positive = cbit).
                         { pose proof (@Integers.unsigned_range 1%positive cbit) as Hrng1; change (@Integers.modulus 1%positive) with 2%Z in Hrng1.
                           apply Z.eqb_neq in Eb; assert (Hz0 : @Integers.unsigned 1%positive cbit = 0%Z) by lia.
                           apply Integers.same_bits_eq; intros i Hi; change (@Integers.zwordsize 1%positive) with 1%Z in Hi.
                           assert (Hi0 : i = 0%Z) by lia; subst i; unfold Integers.testbit; rewrite Hz0; reflexivity. }
                         rewrite Hcbit; exact Hev_cd.
                 --- rewrite ir_seg_written_ids_acc_shift in Hwr.
                     destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br1 []) as [| wr1] eqn:Ewr1;
                       cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
                     rewrite ir_seg_written_ids_acc_shift in Hwr.
                     destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br2 []) as [| wr2] eqn:Ewr2;
                       cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
                     inversion Hwr; subst wr_all; clear Hwr.
                     assert (Hdisj1 : disjoint_raw_ids wr_keep wr1 = true).
                     { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
                       pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
                       destruct (raw_id_in_list x wr1) eqn:Ex1; [| reflexivity].
                       exfalso; rewrite raw_id_in_list_spec in Ex1.
                       assert (Htru : raw_id_in_list x (wr2 ++ wr1 ++ code_written_ids_acc (blk_code b) (if req_step then [] else push_phi_ids_acc (blk_phis b) [])) = true)
                         by (apply raw_id_in_list_spec; apply in_app_iff; right; apply in_app_iff; left; exact Ex1).
                       rewrite Htru in Hnx; discriminate Hnx. }
                     assert (Hdisj2 : disjoint_raw_ids wr_keep wr2 = true).
                     { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
                       pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
                       destruct (raw_id_in_list x wr2) eqn:Ex2; [| reflexivity].
                       exfalso; rewrite raw_id_in_list_spec in Ex2.
                       assert (Htru : raw_id_in_list x (wr2 ++ wr1 ++ code_written_ids_acc (blk_code b) (if req_step then [] else push_phi_ids_acc (blk_phis b) [])) = true)
                         by (apply raw_id_in_list_spec; apply in_app_iff; left; exact Ex2).
                       rewrite Htru in Hnx; discriminate Hnx. }
                     destruct (@Integers.unsigned 1%positive cbit =? 1)%Z;
                       [exact (IH _ _ _ _ _ _ _ _ _ _ _ env2 env2 dt Ewr1 Hdisj1 (conj eq_refl Henv2) Hdt)
                       | exact (IH _ _ _ _ _ _ _ _ _ _ _ env2 env2 df Ewr2 Hdisj2 (conj eq_refl Henv2) Hdf)].
      * rewrite ir_seg_written_ids_acc_shift in Hwr.
        destruct (ir_seg_written_ids_acc phase fuel' bmap hdr_id false (cur_bid :: visited) br []) as [| wr_n] eqn:Ewrn;
          cbn [mc_sum_map] in Hwr; [discriminate Hwr |].
        inversion Hwr; subst wr_all; clear Hwr.
        assert (Hdisjn : disjoint_raw_ids wr_keep wr_n = true).
        { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
          pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
          destruct (raw_id_in_list x wr_n) eqn:Exn; [| reflexivity].
          exfalso; rewrite raw_id_in_list_spec in Exn.
          assert (Htru : raw_id_in_list x (wr_n ++ code_written_ids_acc (blk_code b) (if req_step then [] else push_phi_ids_acc (blk_phis b) [])) = true)
            by (apply raw_id_in_list_spec; apply in_app_iff; left; exact Exn).
          rewrite Htru in Hnx; discriminate Hnx. }
        assert (Htau_j : pure_cfg_steps_to_tau env_prev (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
                           env2 (@denote_cfg_from Pa bmap None (cur_bid, br))).
        { eapply denote_cfg_from_block_jump; [exact Efb |].
          unfold denote_block; rewrite Etm.
          eapply pure_cfg_steps_bind; [exact Hstp_ph |].
          eapply pure_cfg_steps_bind; [exact Hst_c | apply PCS_Ret; reflexivity]. }
        exact (ir_seg_eval_spec_step_front _ _ _ _ _ _ _ _ _ _ _ _ Htau_j Hpres12
                 (IH _ _ _ _ _ _ _ _ _ _ _ env2 env2 t Ewrn Hdisjn (conj eq_refl Henv2) Hr)).
      * inversion Hr; subst t; clear Hr; cbn [ir_seg_eval_spec].
        intro sigma; eapply denote_cfg_from_block_ub; [exact Efb |].
        unfold denote_block; rewrite Etm.
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hstp_ph) |].
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_c) |].
        cbn [denote_terminator]; apply cfg_steps_raiseUB.
Qed.

