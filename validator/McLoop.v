(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Structured Loop Cutpoint Validator ([CertValidator.McLoop])

    Implements Milestone M3b of Phase 8.3a for single-header structured loops
    on RV64IM+RVC and AArch64:
    1. Cutpoint variable naming ([!cut_k], [!mc_hi_rk], [!mc_ur_r], [!mc_us_i]
       — never [$]-prefixed), let-free substitution ([subst_cert_expr]), and
       32-bit upper-half recombination ([combine_hi32_expr]).
    2. General pure-SSA IR segment reification ([ir_seg_tree], [reify_ir_seg])
       supporting rotated loops, entry guards, exit-block phis, LICM, and
       self-loops.
    3. Single-CNF multi-obligation SAT/LRAT refinement discharger
       ([check_mc_loop_obls]) where [ml_inv] guards ONLY Body obligations
       (never asserted as a global unit clause).
    4. Cutpoint & skeleton state construction and leaf-pair obligation
       collection for RV64 and AArch64.
    5. End-to-end validators & CNF emitters ([validate_mc_loop_rv64],
       [validate_mc_loop_a64], [emit_mc_loop_cnf_rv64], [emit_mc_loop_cnf_a64]).
    6. Backward partial-correctness and arbitrary-depth forward progress
       soundness theorems ([validate_mc_loop_rv64_sound],
       [validate_mc_loop_a64_sound]) with [0 Admitted] and zero custom axioms. *)

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

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  Rv64Sem
  A64CoreSem
  McFormat.

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

Definition mc_starts_with_bang (s : string) : bool :=
  match s with
  | String c _ => Ascii.eqb c "!"%char
  | EmptyString => false
  end.

Definition mc_cut_var_name (k : nat) : string :=
  ("!cut_" ++ show_Z_dec (Z.of_nat k))%string.

Definition mc_hi_var_name (r : N) : string :=
  ("!mc_hi_r" ++ show_Z_dec (Z.of_N r))%string.

Definition mc_skel_reg_name (r : N) : string :=
  ("!mc_ur_" ++ show_Z_dec (Z.of_N r))%string.

Definition mc_skel_slot_name (idx : nat) : string :=
  ("!mc_us_" ++ show_Z_dec (Z.of_nat idx))%string.

Lemma show_Z_dec_pos_inj : forall n1 n2 : Z,
  (0 <= n1)%Z -> (0 <= n2)%Z ->
  show_Z_dec n1 = show_Z_dec n2 -> n1 = n2.
Proof.
  intros n1 n2 Hn1 Hn2 Heq.
  unfold show_Z_dec in Heq.
  pose proof (f_equal NilEmpty.int_of_string Heq) as Hinv.
  rewrite !NilEmpty.isi in Hinv.
  inversion Hinv as [Hi].
  pose proof (f_equal Z.of_int Hi) as Hz.
  rewrite !DecimalZ.of_to in Hz; exact Hz.
Qed.

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

Fixpoint apply_reified_phis
  (lmap : rmap (positive * cert_expr)) (pevals : list (raw_id * positive * cert_expr))
  {struct pevals} : rmap (positive * cert_expr) :=
  match pevals with
  | [] => lmap
  | (id, w, ce) :: rest => apply_reified_phis (RM.add id (w, ce) lmap) rest
  end.

Definition pevals_ub_free (pevals : list (raw_id * positive * cert_expr)) : bool :=
  forallb (fun '(_, _, ce) => ub_free_expr ce) pevals.

Definition cevals_ub_free (cevals : list cert_expr) : bool :=
  forallb ub_free_expr cevals.

Fixpoint check_list_eq_id_w (xs ys : list (raw_id * positive)) {struct xs} : bool :=
  match xs, ys with
  | [], [] => true
  | (ix, wx) :: rx, (iy, wy) :: ry =>
      raw_id_eqb ix iy && Pos.eqb wx wy && check_list_eq_id_w rx ry
  | _, _ => false
  end.

Fixpoint reify_ir_seg
  (fuel : nat) (bmap : rmap (block dtyp)) (hdr_id : block_id)
  (hdr_phis : list (raw_id * positive)) (req_step : bool) (visited : list block_id)
  (bid_from cur_bid : block_id) (lmap : rmap (positive * cert_expr))
  {struct fuel} : option ir_seg_tree :=
  if negb req_step && raw_id_eqb cur_bid hdr_id then
    match RM.find cur_bid bmap with
    | None => None
    | Some b_hdr =>
        match reify_pure_phis bid_from lmap (blk_phis b_hdr) with
        | None => None
        | Some pevals =>
            let got := List.map (fun '(id, w, _) => (id, w)) pevals in
            if check_list_eq_id_w got hdr_phis && pevals_ub_free pevals then
              Some (IST_Cut lmap (List.map (fun '(_, w, ce) => (w, ce)) pevals))
            else None
        end
    end
  else if raw_id_in_list cur_bid visited then None
  else
    match fuel with
    | O => None
    | S fuel' =>
        match RM.find cur_bid bmap with
        | None => None
        | Some b =>
            let visited' := cur_bid :: visited in
            let lmap_phis_opt :=
              if req_step then Some lmap
              else
                match reify_pure_phis bid_from lmap (blk_phis b) with
                | None => None
                | Some pevals =>
                    if pevals_ub_free pevals then Some (apply_reified_phis lmap pevals) else None
                end
            in
            match lmap_phis_opt with
            | None => None
            | Some lmap1 =>
                match reify_pure_code lmap1 (blk_code b) with
                | None => None
                | Some (cevals, lmap2) =>
                    if negb (cevals_ub_free cevals) then None
                    else
                      let '(_, term) := fst (blk_term b) in
                      match term with
                      | TERM_Unreachable => Some IST_UB
                      | TERM_Ret (DTYPE_Base (DTYPE_I rw), op) =>
                          if is_supported_bit_width rw then
                            match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I rw))) op with
                            | Some (_, ret_e) =>
                                if ub_free_expr ret_e then Some (IST_Ret rw ret_e) else None
                            | None => None
                            end
                          else None
                      | TERM_Br_1 next_bid =>
                          reify_ir_seg fuel' bmap hdr_id hdr_phis false visited' cur_bid next_bid lmap2
                      | TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2 =>
                          match reify_pure_exp lmap2 (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                          | Some (_, cond_e) =>
                              if negb (ub_free_expr cond_e) then None
                              else
                                match reify_ir_seg fuel' bmap hdr_id hdr_phis false visited' cur_bid br1 lmap2,
                                      reify_ir_seg fuel' bmap hdr_id hdr_phis false visited' cur_bid br2 lmap2 with
                                | Some dt, Some df => Some (IST_Branch cond_e dt df)
                                | _, _ => None
                                end
                          | None => None
                          end
                      | _ => None
                      end
                end
            end
        end
    end.

Fixpoint ir_seg_written_ids (fuel : nat) (bmap : rmap (block dtyp)) (hdr_id : block_id)
  (req_step : bool) (visited : list block_id) (cur_bid : block_id)
  {struct fuel} : option (list raw_id) :=
  if negb req_step && raw_id_eqb cur_bid hdr_id then Some []
  else if raw_id_in_list cur_bid visited then None
  else
    match fuel with
    | O => None
    | S fuel' =>
        match RM.find cur_bid bmap with
        | None => None
        | Some b =>
            let visited' := cur_bid :: visited in
            let phi_ids := if req_step then [] else List.map (fun '(id, _, _) => id) (blk_phis b) in
            let code_ids := code_written_ids (blk_code b) in
            let '(_, term) := fst (blk_term b) in
            match term with
            | TERM_Unreachable | TERM_Ret _ => Some (phi_ids ++ code_ids)
            | TERM_Br_1 next_bid =>
                match ir_seg_written_ids fuel' bmap hdr_id false visited' next_bid with
                | Some wr => Some (phi_ids ++ code_ids ++ wr)
                | None => None
                end
            | TERM_Br _ br1 br2 =>
                match ir_seg_written_ids fuel' bmap hdr_id false visited' br1,
                      ir_seg_written_ids fuel' bmap hdr_id false visited' br2 with
                | Some wr1, Some wr2 => Some (phi_ids ++ code_ids ++ wr1 ++ wr2)
                | _, _ => None
                end
            | _ => None
            end
        end
    end.

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

Lemma apply_reified_phis_wf : forall pevals allowed lmap,
  wf_pure_lmap allowed lmap ->
  Forall (fun '(_, w, ce) => is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals ->
  wf_pure_lmap allowed (apply_reified_phis lmap pevals).
Proof.
  intros pevals allowed lmap Hlmap Hfa; revert lmap Hlmap;
    induction Hfa as [| [[id w] ce] rest (_ & Hbw & (Hwt & Hlf & Hfv)) _ IH];
    intros lmap Hlmap; cbn [apply_reified_phis]; [exact Hlmap |].
  apply IH; exact (wf_pure_lmap_add allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv).
Qed.

Lemma apply_reified_phis_matches {Pa : Params} :
  forall pevals dvs (penv : param_env Pa) lmap env,
    lmap_matches_env penv lmap env ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    lmap_matches_env penv (apply_reified_phis lmap pevals) (apply_phi_env env dvs).
Proof.
  intros pevals dvs penv lmap env Henv Hfa2; revert lmap env Henv;
    induction Hfa2 as [| [[id w] ce] [id' dv] restp restdvs Hpair Hrest IH];
    intros lmap env Henv; cbn [apply_reified_phis apply_phi_env]; [exact Henv |].
  destruct Hpair as [Heq [Hev Hsc]]; subst id'.
  exact (IH _ _ (lmap_matches_env_add penv lmap env id w ce dv Henv Hev Hsc)).
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

Lemma pevals_ub_free_split : forall pevals,
  pevals_ub_free pevals = true ->
  forall id w ce, In (id, w, ce) pevals -> ub_free_expr ce = true.
Proof.
  intros pevals H id w ce Hin; unfold pevals_ub_free in H; rewrite forallb_forall in H.
  exact (H (id, w, ce) Hin).
Qed.

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
  forall fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap allowed t,
    wf_pure_lmap allowed lmap ->
    reify_ir_seg fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap = Some t ->
    ir_seg_wf allowed (extract_hdr_phi_widths hdr_phis) t.
Proof.
  intros fuel; induction fuel as [| fuel' IH];
    intros bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap allowed t Hlmap Hr;
    cbn [reify_ir_seg] in Hr.
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id); [| destruct (raw_id_in_list cur_bid visited); discriminate Hr].
    destruct (RM.find cur_bid bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
    destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
    destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis && pevals_ub_free pevals) eqn:Echk; [| discriminate Hr].
    apply andb_true_iff in Echk as [Eids Eub]; apply check_list_eq_id_w_spec in Eids.
    inversion Hr; subst t; clear Hr.
    split; [intros lm [<- | []]; exact Hlmap |].
    rewrite <- Eids; exact (pevals_to_ist_cut_wf pevals allowed Eub (reify_pure_phis_typing (blk_phis b_hdr) allowed bid_from lmap pevals Hlmap Erp)).
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id).
    + destruct (RM.find cur_bid bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
      destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
      destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis && pevals_ub_free pevals) eqn:Echk; [| discriminate Hr].
      apply andb_true_iff in Echk as [Eids Eub]; apply check_list_eq_id_w_spec in Eids.
      inversion Hr; subst t; clear Hr.
      split; [intros lm [<- | []]; exact Hlmap |].
      rewrite <- Eids; exact (pevals_to_ist_cut_wf pevals allowed Eub (reify_pure_phis_typing (blk_phis b_hdr) allowed bid_from lmap pevals Hlmap Erp)).
    + destruct (raw_id_in_list cur_bid visited); [discriminate Hr |].
      destruct (RM.find cur_bid bmap) as [b |] eqn:Efb; [| discriminate Hr].
      set (lmap_phis_opt := if req_step then Some lmap else match reify_pure_phis bid_from lmap (blk_phis b) with Some pevals => if pevals_ub_free pevals then Some (apply_reified_phis lmap pevals) else None | None => None end) in *.
      destruct lmap_phis_opt as [lmap1 |] eqn:El1; [| discriminate Hr].
      assert (Hlmap1 : wf_pure_lmap allowed lmap1).
      { unfold lmap_phis_opt in El1; destruct req_step; [inversion El1; subst; exact Hlmap |].
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
        destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2) as [dt |] eqn:Hdt; [| discriminate Hr].
        destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2) as [df |] eqn:Hdf; [| discriminate Hr].
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

Lemma ir_seg_written_disjoint_block : forall fuel bmap hdr_id req_step visited cur_bid wr_all r,
  ir_seg_written_ids fuel bmap hdr_id req_step visited cur_bid = Some wr_all ->
  ~ In r wr_all ->
  negb req_step && raw_id_eqb cur_bid hdr_id = false ->
  raw_id_in_list cur_bid visited = false ->
  forall b, RM.find cur_bid bmap = Some b ->
    (req_step = false -> ~ In r (List.map (fun '(id, _, _) => id) (blk_phis b))) /\
    ~ In r (code_written_ids (blk_code b)).
Proof.
  intros fuel bmap hdr_id req_step visited cur_bid wr_all r Hwr Hnin Hnstop Hnvis b Efb.
  destruct fuel as [| fuel']; cbn [ir_seg_written_ids] in Hwr;
    rewrite Hnstop, Hnvis in Hwr; [discriminate Hwr |].
  rewrite Efb in Hwr; destruct (blk_term b) as [[tid term] tmd]; cbn [fst] in Hwr.
  assert (Hsub : incl ((if req_step then [] else List.map (fun '(id, _, _) => id) (blk_phis b)) ++ code_written_ids (blk_code b)) wr_all).
  { destruct term; try discriminate Hwr.
    - inversion Hwr; subst; apply incl_refl.
    - destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br1); [| discriminate Hwr].
      destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br2); [| discriminate Hwr].
      inversion Hwr; subst; intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
        [left; exact Hx | right; apply in_app_iff; left; exact Hx].
    - destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br); [| discriminate Hwr].
      inversion Hwr; subst; intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
        [left; exact Hx | right; apply in_app_iff; left; exact Hx].
    - inversion Hwr; subst; apply incl_refl. }
  split.
  - intro Hrs; rewrite Hrs in Hsub; cbn [app] in Hsub.
    intro Hin; apply Hnin, Hsub, in_app_iff; left; exact Hin.
  - intro Hin; apply Hnin, Hsub, in_app_iff; right; exact Hin.
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
  forall fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap
         wr_keep wr_all (penv : param_env Pa) env_prev env_hdr t,
    ir_seg_written_ids fuel bmap hdr_id req_step visited cur_bid = Some wr_all ->
    disjoint_raw_ids wr_keep wr_all = true ->
    (if req_step then
       exists b,
         RM.find cur_bid bmap = Some b /\
         pure_cfg_steps env_prev (denote_phis bid_from (blk_phis b)) env_hdr tt /\
         (forall r, In r wr_keep -> RM.find r env_hdr = RM.find r env_prev) /\
         lmap_matches_env penv lmap env_hdr
     else
       env_hdr = env_prev /\ lmap_matches_env penv lmap env_prev) ->
    reify_ir_seg fuel bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap = Some t ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv env_prev bid_from cur_bid t.
Proof.
  intros fuel; induction fuel as [| fuel' IH];
    intros bmap hdr_id hdr_phis req_step visited bid_from cur_bid lmap
           wr_keep wr_all penv env_prev env_hdr t Hwr Hdisj Hinit Hr;
    cbn [reify_ir_seg ir_seg_written_ids] in Hr, Hwr.
  - destruct (negb req_step && raw_id_eqb cur_bid hdr_id) eqn:Estp;
      [| destruct (raw_id_in_list cur_bid visited); discriminate Hr].
    apply andb_true_iff in Estp as [Hnr Hhd]; apply negb_true_iff in Hnr; apply raw_id_eqb_eq in Hhd; subst cur_bid req_step.
    destruct Hinit as [-> Henv].
    destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Hr].
    destruct (reify_pure_phis bid_from lmap (blk_phis b_hdr)) as [pevals |] eqn:Erp; [| discriminate Hr].
    destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis && pevals_ub_free pevals) eqn:Echk; [| discriminate Hr].
    apply andb_true_iff in Echk as [Eids _]; apply check_list_eq_id_w_spec in Eids.
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
      destruct (check_list_eq_id_w (List.map (fun '(id, w, _) => (id, w)) pevals) hdr_phis && pevals_ub_free pevals) eqn:Echk; [| discriminate Hr].
      apply andb_true_iff in Echk as [Eids _]; apply check_list_eq_id_w_spec in Eids.
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
      { intros r Hrk; eapply (ir_seg_written_disjoint_block (S fuel') bmap hdr_id req_step visited cur_bid wr_all r);
          [cbn [ir_seg_written_ids]; rewrite Estp, Evis, Efb; exact Hwr
          | exact (disjoint_raw_ids_spec _ _ r Hdisj Hrk) | exact Estp | exact Evis | exact Efb]. }
      set (lmap_phis_opt := if req_step then Some lmap else match reify_pure_phis bid_from lmap (blk_phis b) with Some pevals => if pevals_ub_free pevals then Some (apply_reified_phis lmap pevals) else None | None => None end) in *.
      destruct lmap_phis_opt as [lmap1 |] eqn:El1; [| discriminate Hr].
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
          unfold lmap_phis_opt in El1.
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
      destruct (blk_term b) as [[tid term] tmd] eqn:Etm; cbn [fst] in Hr, Hwr.
      destruct Hphase1 as [Hub_ph | (env1 & Henv1 & Hpres1 & Hstp_ph)].
      { destruct term; try discriminate Hr.
        - destruct v as [[[rw | | | | | | | | | |] | |] op]; try discriminate Hr.
          destruct (is_supported_bit_width rw); [| discriminate Hr].
          destruct (reify_pure_exp lmap2 _ op) as [[? ret_e] |]; [| discriminate Hr].
          destruct (ub_free_expr ret_e); inversion Hr; left; exact Hub_ph.
        - match goal with x : texp dtyp |- _ => destruct x as [[[rw | | | | | | | | | |] | |] e_cond] end; try discriminate Hr; destruct rw; try discriminate Hr.
          destruct (reify_pure_exp lmap2 _ e_cond) as [[? cond_e] |]; [| discriminate Hr].
          destruct (ub_free_expr cond_e); cbn [negb] in Hr; [| discriminate Hr].
          destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2); [| discriminate Hr].
          destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2); inversion Hr; left; exact Hub_ph.
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
          destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2); [| discriminate Hr].
          destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2); inversion Hr; left; exact Hub_all.
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
        destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br1 lmap2) as [dt |] eqn:Hdt; [| discriminate Hr].
        destruct (reify_ir_seg fuel' bmap hdr_id hdr_phis false (cur_bid :: visited) cur_bid br2 lmap2) as [df |] eqn:Hdf; [| discriminate Hr].
        destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br1) as [wr1 |] eqn:Ewr1; [| discriminate Hwr].
        destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br2) as [wr2 |] eqn:Ewr2; [| discriminate Hwr].
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
                 --- assert (Hdisj1 : disjoint_raw_ids wr_keep wr1 = true).
                     { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
                       pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
                       destruct (raw_id_in_list x wr1) eqn:Ex1; [| reflexivity].
                       inversion Hwr; subst wr_all.
                       exfalso; rewrite raw_id_in_list_spec in Ex1.
                       assert (Htru : raw_id_in_list x ((if req_step then [] else List.map (fun '(id, _, _) => id) (blk_phis b)) ++ code_written_ids (blk_code b) ++ wr1 ++ wr2) = true)
                         by (apply raw_id_in_list_spec; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Ex1).
                       rewrite Htru in Hnx; discriminate Hnx. }
                     assert (Hdisj2 : disjoint_raw_ids wr_keep wr2 = true).
                     { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
                       pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
                       destruct (raw_id_in_list x wr2) eqn:Ex2; [| reflexivity].
                       inversion Hwr; subst wr_all.
                       exfalso; rewrite raw_id_in_list_spec in Ex2.
                       assert (Htru : raw_id_in_list x ((if req_step then [] else List.map (fun '(id, _, _) => id) (blk_phis b)) ++ code_written_ids (blk_code b) ++ wr1 ++ wr2) = true)
                         by (apply raw_id_in_list_spec; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Ex2).
                       rewrite Htru in Hnx; discriminate Hnx. }
                     destruct (@Integers.unsigned 1%positive cbit =? 1)%Z;
                       [exact (IH _ _ _ _ _ _ _ _ _ _ _ env2 env2 dt Ewr1 Hdisj1 (conj eq_refl Henv2) Hdt)
                       | exact (IH _ _ _ _ _ _ _ _ _ _ _ env2 env2 df Ewr2 Hdisj2 (conj eq_refl Henv2) Hdf)].
      * destruct (ir_seg_written_ids fuel' bmap hdr_id false (cur_bid :: visited) br) as [wr_n |] eqn:Ewrn; [| discriminate Hwr].
        assert (Hdisjn : disjoint_raw_ids wr_keep wr_n = true).
        { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
          pose proof (Hdisj x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
          destruct (raw_id_in_list x wr_n) eqn:Exn; [| reflexivity].
          inversion Hwr; subst wr_all.
          exfalso; rewrite raw_id_in_list_spec in Exn.
          assert (Htru : raw_id_in_list x ((if req_step then [] else List.map (fun '(id, _, _) => id) (blk_phis b)) ++ code_written_ids (blk_code b) ++ wr_n) = true)
            by (apply raw_id_in_list_spec; apply in_app_iff; right; apply in_app_iff; right; exact Exn).
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

(** ** 3. Single-CNF Multi-Obligation SAT/LRAT Discharger ([check_mc_loop_obls]) *)

Inductive mc_loop_obl : Set :=
| MLO_Refine (is_body : bool) (path : list (bool * cert_expr)) (w : positive) (e_src e_tgt : cert_expr)
| MLO_Defined (is_body : bool) (path : list (bool * cert_expr)) (w : positive) (e : cert_expr).

Definition obl_is_body (o : mc_loop_obl) : bool :=
  match o with
  | MLO_Refine ib _ _ _ _ => ib
  | MLO_Defined ib _ _ _ => ib
  end.

Definition obl_path (o : mc_loop_obl) : list (bool * cert_expr) :=
  match o with
  | MLO_Refine _ p _ _ _ => p
  | MLO_Defined _ p _ _ => p
  end.

Definition obl_wf_exprs (allowed : list (string * positive)) (o : mc_loop_obl) : bool :=
  forallb (fun '(_, c) =>
    wt_cert_expr [] c && Pos.eqb (cert_expr_bit_width c) 1%positive &&
    is_let_free_expr c && ub_free_expr c &&
    AlgRules.vars_subset_b (collect_free_vars [] c) allowed) (obl_path o) &&
  match o with
  | MLO_Refine _ _ w s t =>
      wt_cert_expr [] s && wt_cert_expr [] t &&
      Pos.eqb (cert_expr_bit_width s) w && Pos.eqb (cert_expr_bit_width t) w &&
      is_let_free_expr s && is_let_free_expr t &&
      ub_free_expr s && ub_free_expr t &&
      AlgRules.vars_subset_b (collect_free_vars [] s) allowed &&
      AlgRules.vars_subset_b (collect_free_vars [] t) allowed
  | MLO_Defined _ _ w e =>
      wt_cert_expr [] e && Pos.eqb (cert_expr_bit_width e) w &&
      is_let_free_expr e && ub_free_expr e &&
      AlgRules.vars_subset_b (collect_free_vars [] e) allowed
  end.

Lemma blast_refinement_cex_opt_gates_step :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (asg : positive -> bool) cex_lit st',
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) src_no_ub ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    blast_refinement_cex_opt_gates sz src_no_ub src_r tgt_r st = (cex_lit, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      wf_lit_bound (bs_next_var st') cex_lit /\
      (eval_lit asg' cex_lit = false ->
       eval_lit asg src_no_ub = true ->
       eval_rail_psn asg src_r = false ->
       eval_rail_psn asg tgt_r = false /\
       eval_rail_val sz asg tgt_r = eval_rail_val sz asg src_r).
Proof.
  intros sz src_no_ub src_r tgt_r st asg cex_lit st' Hsat Hnub Hbs Hbt Hgates.
  destruct Hbs as ((Hws & Hls) & Hbs0 & Hps).
  destruct Hbt as ((Hwt & Hlt) & Hbt0 & Hpt).
  unfold blast_refinement_cex_opt_gates in Hgates.
  destruct (map2_emit emit_xor2_opt (rbv_bits src_r) (rbv_bits tgt_r) st) as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list_opt xor_bits st1) as [val_diff st2] eqn:Horl.
  destruct (emit_or2_opt (rbv_psn tgt_r) val_diff st2) as [bad_tgt st3] eqn:Hbad.
  destruct (emit_and2_opt (neg_lit (rbv_psn src_r)) bad_tgt st3) as [def_bad st4] eqn:Hdef.
  destruct (emit_and2_opt src_no_ub def_bad st4) as [cex_lit0 st5] eqn:Hcex.
  inversion Hgates; subst cex_lit0 st5; clear Hgates.
  assert (Hlen_st : List.length (rbv_bits src_r) = List.length (rbv_bits tgt_r)) by congruence.
  destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st xor_bits st1
              Hlen_st Hbs0 Hbt0 Hsat Hm)
    as (asg1 & Hs1 & Hxlen & Hxwf & Hxev).
  destruct (emit_or_list_opt_step xor_bits asg1 st1 val_diff st2 Hxwf (proj2 (proj2 Hs1)) Horl)
    as (asg2 & Hs2 & Hvd_wf & Hvd_ev).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs12.
  destruct (emit_or2_opt_step asg2 (rbv_psn tgt_r) val_diff st2 bad_tgt st3 (proj2 (proj2 Hs2))
              (wf_lit_bound_mono _ _ _ (proj1 Hs12) Hpt) Hvd_wf Hbad)
    as (asg3 & Hs3 & Hbt_wf & Hbt_ev).
  pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs12 Hs3) as Hs13.
  destruct (emit_and2_opt_step asg3 (neg_lit (rbv_psn src_r)) bad_tgt st3 def_bad st4
              (proj2 (proj2 Hs3))
              (wf_lit_bound_neg _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hps))
              Hbt_wf Hdef)
    as (asg4 & Hs4 & Hdb_wf & Hdb_ev).
  pose proof (step_spec_trans st st3 st4 asg asg3 asg4 Hs13 Hs4) as Hs14.
  destruct (emit_and2_opt_step asg4 src_no_ub def_bad st4 cex_lit st' (proj2 (proj2 Hs4))
              (wf_lit_bound_mono _ _ _ (proj1 Hs14) Hnub) Hdb_wf Hcex)
    as (asg5 & Hs5 & Hcx_wf & Hcx_ev).
  pose proof (step_spec_trans st st4 st' asg asg4 asg5 Hs14 Hs5) as Hs15.
  exists asg5; split; [exact Hs15 | split; [exact Hcx_wf |]].
  intros Hqf Hno_ub Hps_f.
  unfold eval_rail_psn in Hps_f.
  rewrite Hcx_ev,
          (step_spec_eval_lit st st4 asg asg4 src_no_ub Hs14 Hnub),
          Hno_ub, Hdb_ev,
          (eval_neg_lit_nonzero asg3 (rbv_psn src_r) (wf_lit_bound_nonzero _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hps))),
          (step_spec_eval_lit st st3 asg asg3 (rbv_psn src_r) Hs13 Hps),
          Hps_f, Hbt_ev,
          (step_spec_eval_lit st st2 asg asg2 (rbv_psn tgt_r) Hs12 Hpt),
          Hvd_ev in Hqf.
  cbn [andb] in Hqf; apply orb_false_iff in Hqf as [Htgt_def Hxor_false].
  split; [exact Htgt_def |].
  destruct (eval_rail_agree sz _ asg asg1 src_r (proj1 (proj2 Hs1)) (conj (conj Hws Hls) (conj Hbs0 Hps))) as [_ Hvs1].
  destruct (eval_rail_agree sz _ asg asg1 tgt_r (proj1 (proj2 Hs1)) (conj (conj Hwt Hlt) (conj Hbt0 Hpt))) as [_ Hvt1].
  rewrite Hvs1, Hvt1.
  apply (existsb_xor_bits_diff sz asg1 src_r tgt_r xor_bits (conj Hws Hls) (conj Hwt Hlt)); [congruence | |].
  - intros k Hk.
    unfold wf_lits_bound in Hbs0, Hbt0; rewrite Forall_forall in Hbs0, Hbt0.
    assert (Hs_eq : List.map (eval_lit asg1) (rbv_bits src_r) = List.map (eval_lit asg) (rbv_bits src_r))
      by (apply map_ext_in; intros l Hl; exact (step_spec_eval_lit _ _ _ _ _ Hs1 (Hbs0 l Hl))).
    assert (Ht_eq : List.map (eval_lit asg1) (rbv_bits tgt_r) = List.map (eval_lit asg) (rbv_bits tgt_r))
      by (apply map_ext_in; intros l Hl; exact (step_spec_eval_lit _ _ _ _ _ Hs1 (Hbt0 l Hl))).
    rewrite Hxev, Hs_eq, Ht_eq.
    clear -Hws Hls Hwt Hlt Hk.
    remember (List.map (eval_lit asg) (rbv_bits src_r)) as xs eqn:Exs.
    remember (List.map (eval_lit asg) (rbv_bits tgt_r)) as ys eqn:Eys.
    assert (Hlen_xs : (k < List.length xs)%nat) by (subst xs; rewrite length_map; congruence).
    assert (Hlen_eq : List.length xs = List.length ys) by (subst xs ys; rewrite !length_map; congruence).
    clear -Hlen_xs Hlen_eq; revert xs ys Hlen_xs Hlen_eq.
    induction k as [| k' IHk]; intros [| x rx] [| y ry] Hlt Hleq; cbn in *; try lia;
      [reflexivity | exact (IHk rx ry ltac:(lia) ltac:(lia))].
  - rewrite <- existsb_id_map_eval_lit; exact Hxor_false.
Qed.

Definition mc_ms_opt (e : cert_expr) : option (sized_let_map * nat) :=
  if expr_has_freeze e then Some ([], default_let_expand_budget) else None.

Fixpoint emit_path_lits
  (ctx : ub_ctx) (g_lit : lit) (path : list (bool * cert_expr)) (env : blast_env)
  {struct path} : option (lit * blast_env) :=
  match path with
  | [] => Some (g_lit, env)
  | (b, c) :: rest =>
      match blast_cert_expr ctx [] (mc_ms_opt c) c env with
      | None => None
      | Some (rc, env1) =>
          let b0 := match rbv_bits rc with x :: _ => if b then x else neg_lit x | [] => lit_false end in
          let '(cond_lit, st1) := emit_and2_opt (neg_lit (rbv_psn rc)) b0 (be_st env1) in
          let '(g', st2) := emit_and2_opt g_lit cond_lit st1 in
          emit_path_lits ctx g' rest (mk_blast_env st2 (be_vars env1) (be_freezes env1))
      end
  end.

Definition blast_mc_obl
  (ctx : ub_ctx) (body_hyp_lit : lit) (env : blast_env) (o : mc_loop_obl)
  : option (lit * blast_env) :=
  let g0 := if obl_is_body o then body_hyp_lit else lit_true in
  match emit_path_lits ctx g0 (obl_path o) env with
  | None => None
  | Some (g_lit, env1) =>
      match o with
      | MLO_Refine _ _ w e_src e_tgt =>
          match blast_cert_expr ctx [] (mc_ms_opt e_src) e_src env1 with
          | None => None
          | Some (rs, env2) =>
              match blast_cert_expr ctx [] (mc_ms_opt e_tgt) e_tgt env2 with
              | None => None
              | Some (rt, env3) =>
                  let '(cex, st4) := blast_refinement_cex_opt_gates w g_lit rs rt (be_st env3) in
                  Some (cex, mk_blast_env st4 (be_vars env3) (be_freezes env3))
              end
          end
      | MLO_Defined _ _ w e =>
          match blast_cert_expr ctx [] (mc_ms_opt e) e env1 with
          | None => None
          | Some (re, env2) =>
              let '(cex, st3) := emit_and2_opt g_lit (rbv_psn re) (be_st env2) in
              Some (cex, mk_blast_env st3 (be_vars env2) (be_freezes env2))
          end
      end
  end.

Fixpoint blast_mc_obls_list
  (ctx : ub_ctx) (body_hyp_lit : lit) (obls : list mc_loop_obl) (env : blast_env)
  {struct obls} : option (list lit * blast_env) :=
  match obls with
  | [] => Some ([], env)
  | o :: rest =>
      match blast_mc_obl ctx body_hyp_lit env o with
      | None => None
      | Some (cex, env1) =>
          match blast_mc_obls_list ctx body_hyp_lit rest env1 with
          | None => None
          | Some (cexs, env2) => Some (cex :: cexs, env2)
          end
      end
  end.

Definition obl_is_alg_ok (ctx : ub_ctx) (o : mc_loop_obl) : bool :=
  match o with
  | MLO_Refine false [] _ s t => check_expr_refines ctx s t
  | _ => false
  end.

Definition build_mc_loop_cnf
  (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  : option (positive * cnf) :=
  if negb (forallb (obl_wf_exprs known_vars) obls) then None
  else
    let init_env := mk_blast_env (init_blast_state 2%positive) [] [] in
    let env0 := blast_ub_ctx ctx known_vars ctx init_env in
    let hyp_res :=
      match opt_inv with
      | None => Some (lit_true, env0)
      | Some inv_e =>
          if wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive &&
             is_let_free_expr inv_e && ub_free_expr inv_e &&
             AlgRules.vars_subset_b (collect_free_vars [] inv_e) known_vars
          then
            match blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0 with
            | None => None
            | Some (ri, env_i) =>
                let b0 := match rbv_bits ri with x :: _ => x | [] => lit_false end in
                let '(hlit, st1) := emit_and2_opt (neg_lit (rbv_psn ri)) b0 (be_st env_i) in
                Some (hlit, mk_blast_env st1 (be_vars env_i) (be_freezes env_i))
            end
          else None
      end in
    match hyp_res with
    | None => None
    | Some (body_hyp_lit, env1) =>
        match blast_mc_obls_list ctx body_hyp_lit obls env1 with
        | None => None
        | Some (cex_lits, env2) =>
            let '(any_cex, st_or) := emit_or_list_opt cex_lits (be_st env2) in
            let st_fin := add_clauses [[any_cex]] st_or in
            Some (Pos.pred (bs_next_var st_fin), bs_cnf st_fin)
        end
    end.

Definition check_mc_loop_obls
  (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  (opt_pf : option (list lrat_step)) : bool :=
  if negb (forallb (obl_wf_exprs known_vars) obls) then false
  else
    let rem := List.filter (fun o => negb (obl_is_alg_ok ctx o)) obls in
    match rem with
    | [] => true
    | _ :: _ =>
        match build_mc_loop_cnf ctx known_vars opt_inv rem with
        | None => false
        | Some (_, f) => check_cex_unsat f opt_pf
        end
    end.

Definition emit_mc_loop_cnf
  (ctx : ub_ctx) (known_vars : list (string * positive))
  (opt_inv : option cert_expr) (obls : list mc_loop_obl)
  : option (option (positive * cnf)) :=
  if negb (forallb (obl_wf_exprs known_vars) obls) then None
  else
    let rem := List.filter (fun o => negb (obl_is_alg_ok ctx o)) obls in
    match rem with
    | [] => Some None
    | _ :: _ =>
        match build_mc_loop_cnf ctx known_vars opt_inv rem with
        | None => None
        | Some nf => Some (Some nf)
        end
    end.

Definition mc_obl_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (opt_inv : option cert_expr) (is_body_mode : bool) (o : mc_loop_obl) : Prop :=
  (obl_is_body o = is_body_mode) ->
  (is_body_mode = true ->
   match opt_inv with
   | None => True
   | Some inv_e =>
       eval_closed_cert_expr penv foracle inv_e =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
   end) ->
  (forall b c, In (b, c) (obl_path o) ->
     eval_closed_cert_expr penv foracle c =
     raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
       (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
  match o with
  | MLO_Refine _ _ _ e_src e_tgt =>
      refine_eou_dvalue (eval_closed_cert_expr penv foracle e_src)
                        (eval_closed_cert_expr penv foracle e_tgt)
  | MLO_Defined _ _ w e =>
      exists (v : @Integers.bit_int w),
        eval_closed_cert_expr penv foracle e =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w v))
  end.

Lemma mc_ms_opt_sync {Pa : Params} : forall e,
  wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) (mc_ms_opt e).
Proof.
  intro e; unfold mc_ms_opt; destruct (expr_has_freeze e);
    cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial.
Qed.

Lemma emit_path_lits_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars g_lit path env out_lit env' asg,
    forallb (fun '(_, c) =>
      wt_cert_expr [] c && Pos.eqb (cert_expr_bit_width c) 1%positive &&
      is_let_free_expr c && ub_free_expr c &&
      AlgRules.vars_subset_b (collect_free_vars [] c) known_vars) path = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) g_lit ->
    emit_path_lits ctx g_lit path env = Some (out_lit, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lit_bound (bs_next_var (be_st env')) out_lit /\
      (eval_lit asg g_lit = true ->
       (forall b c, In (b, c) path ->
          eval_closed_cert_expr penv foracle c =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
       eval_lit asg' out_lit = true).
Proof.
  intros ctx penv foracle known_vars g_lit path; revert g_lit.
  induction path as [| [b c] rest IH];
    intros g_lit env out_lit env' asg Hwf Hpenv Hctx Henv Hwg Hem;
    cbn [emit_path_lits] in Hem.
  - inversion Hem; subst out_lit env'; exists asg.
    split; [exact (step_spec_refl _ _ (proj1 Henv)) | split; [exact Henv | split; [exact Hwg | intros Hg _; exact Hg]]].
  - cbn [forallb] in Hwf; apply andb_true_iff in Hwf as [Hc Hrest].
    rewrite !andb_true_iff in Hc; destruct Hc as ((((Hwt & Hbw1) & Hlf) & _) & Hsub).
    apply Pos.eqb_eq in Hbw1.
    destruct (blast_cert_expr ctx [] (mc_ms_opt c) c env) as [[rc env1] |] eqn:Ebc; [| discriminate Hem].
    destruct (emit_and2_opt (neg_lit (rbv_psn rc))
                match rbv_bits rc with x :: _ => if b then x else neg_lit x | [] => lit_false end (be_st env1))
      as [cond_lit st1] eqn:Ea1.
    destruct (emit_and2_opt g_lit cond_lit st1) as [g' st2] eqn:Ea2.
    destruct (blast_cert_expr_sat c ctx [] [] (mc_ms_opt c) penv [] foracle asg env env1 rc
                Ebc Hwt (wf_let_rails_sync_nil asg _) (mc_ms_opt_sync c)
                (vars_subset_b_wf_param_env _ _ penv Hsub Hpenv) Hctx Henv)
      as (asg1 & vc & Evc & Hs1 & Henv1 & Hwfc & Hmrc).
    rewrite Hbw1 in Hwfc, Hmrc.
    destruct Hwfc as ((Hrwc & Hlen1) & Hlbs1 & Hps1).
    destruct (rbv_bits rc) as [| b0 rbits] eqn:Ebits; [cbn in Hlen1; discriminate Hlen1 |].
    assert (Hb0_wf : wf_lit_bound (bs_next_var (be_st env1)) (if b then b0 else neg_lit b0)).
    { inversion Hlbs1; destruct b; [exact H1 | apply wf_lit_bound_neg; exact H1]. }
    destruct (emit_and2_opt_step asg1 (neg_lit (rbv_psn rc)) (if b then b0 else neg_lit b0) (be_st env1) cond_lit st1
                (proj1 Henv1) (wf_lit_bound_neg _ _ Hps1) Hb0_wf Ea1)
      as (asg2 & Hs2 & Hwc_wf & Hwc_ev).
    pose proof (step_spec_trans (be_st env) (be_st env1) st1 asg asg1 asg2 Hs1 Hs2) as Hs12.
    destruct (emit_and2_opt_step asg2 g_lit cond_lit st1 g' st2 (proj2 (proj2 Hs2))
                (wf_lit_bound_mono _ _ _ (proj1 Hs12) Hwg) Hwc_wf Ea2)
      as (asg3 & Hs3 & Hwg'_wf & Hwg'_ev).
    pose proof (step_spec_trans (be_st env) st1 st2 asg asg2 asg3 Hs12 Hs3) as Hs13.
    pose proof (sat_blast_env_step penv foracle asg1 asg3 env1 st2 Henv1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3)) as Henv3.
    destruct (IH g' (mk_blast_env st2 (be_vars env1) (be_freezes env1)) out_lit env' asg3
                Hrest Hpenv Hctx Henv3 Hwg'_wf Hem)
      as (asg4 & Hs4 & Henv4 & Hwo_wf & Hwo_ev).
    exists asg4; split; [exact (step_spec_trans _ _ _ _ _ _ Hs13 Hs4) | split; [exact Henv4 | split; [exact Hwo_wf |]]].
    intros Hg Hpath; apply Hwo_ev; [| intros b1 c1 Hc1; apply Hpath; right; exact Hc1].
    rewrite Hwg'_ev, (step_spec_eval_lit _ _ _ _ _ Hs12 Hwg), Hg, Hwc_ev,
            (eval_neg_lit_nonzero asg1 (rbv_psn rc) (wf_lit_bound_nonzero _ _ Hps1)).
    pose proof (Hpath b c (or_introl eq_refl)) as Hpc.
    unfold eval_closed_cert_expr in Hpc; rewrite Evc in Hpc; inversion Hpc; subst vc; clear Hpc.
    unfold rail_matches_dvalue in Hmrc.
    destruct (eval_rail_psn asg1 rc) eqn:Eps; [discriminate Hmrc |].
    unfold eval_rail_val in Hmrc; rewrite Ebits in Hmrc.
    unfold eval_rail_psn in Eps; rewrite Eps; cbn [negb andb].
    pose proof (f_equal dvalue_int_unsigned Hmrc) as Hu; cbn in Hu.
    destruct rbits as [| ? ?]; [| cbn in Hlen1; discriminate Hlen1].
    assert (Hevb0 : eval_lit asg1 b0 = b).
    { destruct b;
        rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive) in Hu;
        destruct (eval_lit asg1 b0); try reflexivity;
        cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite Integers.unsigned_repr in Hu by (change (@Integers.max_unsigned 1%positive) with 1%Z; lia); lia. }
    destruct b; [exact Hevb0 |].
    rewrite (eval_neg_lit_nonzero asg1 b0 (wf_lit_bound_nonzero _ _ ltac:(inversion Hlbs1; exact H1))), Hevb0; reflexivity.
Qed.

Lemma blast_mc_obl_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars opt_inv is_body_mode body_hyp_lit env o cex env' asg,
    obl_wf_exprs known_vars o = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) body_hyp_lit ->
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg body_hyp_lit = true) ->
    blast_mc_obl ctx body_hyp_lit env o = Some (cex, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lit_bound (bs_next_var (be_st env')) cex /\
      (eval_lit asg' cex = false -> mc_obl_holds penv foracle opt_inv is_body_mode o).
Proof.
  intros ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit env o cex env' asg
         Hwf Hpenv Hctx Henv Hwbh Hbh_true Hbl.
  unfold obl_wf_exprs in Hwf; apply andb_true_iff in Hwf as [Hwfp Hwfo].
  unfold blast_mc_obl in Hbl.
  set (g0 := if obl_is_body o then body_hyp_lit else lit_true) in *.
  assert (Hwg0 : wf_lit_bound (bs_next_var (be_st env)) g0).
  { unfold g0; destruct (obl_is_body o); [exact Hwbh | cbn; pose proof (proj1 (proj1 (proj1 Henv))); lia]. }
  destruct (emit_path_lits ctx g0 (obl_path o) env) as [[g_lit env1] |] eqn:Epl; [| discriminate Hbl].
  destruct (emit_path_lits_sat ctx penv foracle known_vars g0 (obl_path o) env g_lit env1 asg
              Hwfp Hpenv Hctx Henv Hwg0 Epl)
    as (asg1 & Hs1 & Henv1 & Hwg1 & Hg1_true).
  destruct o as [ib p w s t | ib p w e]; cbn [obl_is_body obl_path] in *.
  - rewrite !andb_true_iff in Hwfo; destruct Hwfo as (((((((((Hwts & Hwtt) & Hbws) & Hbwt) & Hlfs) & Hlft) & _) & _) & Hsubs) & Hsubt).
    apply Pos.eqb_eq in Hbws; apply Pos.eqb_eq in Hbwt.
    destruct (blast_cert_expr ctx [] (mc_ms_opt s) s env1) as [[rs env2] |] eqn:Ebs; [| discriminate Hbl].
    destruct (blast_cert_expr ctx [] (mc_ms_opt t) t env2) as [[rt env3] |] eqn:Ebt; [| discriminate Hbl].
    destruct (blast_refinement_cex_opt_gates w g_lit rs rt (be_st env3)) as [cex0 st4] eqn:Hgat.
    inversion Hbl; subst cex0 env'; clear Hbl.
    destruct (blast_cert_expr_sat s ctx [] [] (mc_ms_opt s) penv [] foracle asg1 env1 env2 rs
                Ebs Hwts (wf_let_rails_sync_nil asg1 _) (mc_ms_opt_sync s)
                (vars_subset_b_wf_param_env _ _ penv Hsubs Hpenv) Hctx Henv1)
      as (asg2 & vs & Evs & Hs2 & Henv2 & Hwfs & Hms).
    destruct (blast_cert_expr_sat t ctx [] [] (mc_ms_opt t) penv [] foracle asg2 env2 env3 rt
                Ebt Hwtt (wf_let_rails_sync_nil asg2 _) (mc_ms_opt_sync t)
                (vars_subset_b_wf_param_env _ _ penv Hsubt Hpenv) Hctx Henv2)
      as (asg3 & vt & Evt & Hs3 & Henv3 & Hwft & Hmt).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs2 Hs3) as Hs23.
    rewrite Hbws in Hwfs, Hms; rewrite Hbwt in Hwft, Hmt.
    pose proof (wf_rail_bound_mono w _ _ rs (proj1 Hs3) Hwfs) as Hwfs3.
    pose proof (wf_lit_bound_mono _ _ g_lit (proj1 Hs23) Hwg1) as Hwg3.
    destruct (blast_refinement_cex_opt_gates_step w g_lit rs rt (be_st env3) asg3 cex st4
                (proj1 Henv3) Hwg3 Hwfs3 Hwft Hgat)
      as (asg4 & Hs4 & Hwcex & Hcex_sound).
    pose proof (sat_blast_env_step penv foracle asg3 asg4 env3 st4 Henv3 Hs4) as Henv4.
    exists asg4; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs23 Hs4))
                       | split; [exact Henv4 | split; [exact Hwcex |]]].
    intros Hqf Hib Hinv Hpath; unfold eval_closed_cert_expr; rewrite Evs, Evt; cbn [refine_eou_dvalue].
    pose proof (rail_matches_dvalue_agree w _ asg2 asg3 rs vs (proj1 (proj2 Hs3)) Hwfs Hms) as Hms3.
    unfold rail_matches_dvalue in Hms3, Hmt.
    destruct (eval_rail_psn asg3 rs) eqn:Eps; [subst vs; apply dvalue_refines_poison_l |].
    assert (Hg3 : eval_lit asg3 g_lit = true).
    { rewrite (step_spec_eval_lit _ _ _ _ _ Hs23 Hwg1); apply Hg1_true; [| exact Hpath].
      cbn [obl_is_body] in Hib; subst ib; unfold g0; destruct is_body_mode.
      - exact (Hbh_true eq_refl (Hinv eq_refl)).
      - exact (proj1 (proj2 (proj1 Henv))). }
    destruct (Hcex_sound Hqf Hg3 eq_refl) as [Ept Heqv].
    rewrite Ept, Heqv in Hmt; subst vs vt; apply dvalue_refines_refl.
  - rewrite !andb_true_iff in Hwfo; destruct Hwfo as ((((Hwte & Hbwe) & Hlfe) & _) & Hsube).
    apply Pos.eqb_eq in Hbwe.
    destruct (blast_cert_expr ctx [] (mc_ms_opt e) e env1) as [[re env2] |] eqn:Ebe; [| discriminate Hbl].
    destruct (emit_and2_opt g_lit (rbv_psn re) (be_st env2)) as [cex0 st3] eqn:Ea2.
    inversion Hbl; subst cex0 env'; clear Hbl.
    destruct (blast_cert_expr_sat e ctx [] [] (mc_ms_opt e) penv [] foracle asg1 env1 env2 re
                Ebe Hwte (wf_let_rails_sync_nil asg1 _) (mc_ms_opt_sync e)
                (vars_subset_b_wf_param_env _ _ penv Hsube Hpenv) Hctx Henv1)
      as (asg2 & ve & Eve & Hs2 & Henv2 & Hwfe & Hme).
    rewrite Hbwe in Hwfe, Hme.
    destruct (emit_and2_opt_step asg2 g_lit (rbv_psn re) (be_st env2) cex st3 (proj1 Henv2)
                (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwg1) (proj2 (proj2 Hwfe)) Ea2)
      as (asg3 & Hs3 & Hwcex & Hevcex).
    pose proof (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hs3) as Henv3.
    exists asg3; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3))
                       | split; [exact Henv3 | split; [exact Hwcex |]]].
    intros Hqf Hib Hinv Hpath.
    assert (Hg2 : eval_lit asg2 g_lit = true).
    { rewrite (step_spec_eval_lit _ _ _ _ _ Hs2 Hwg1); apply Hg1_true; [| exact Hpath].
      cbn [obl_is_body] in Hib; subst ib; unfold g0; destruct is_body_mode.
      - exact (Hbh_true eq_refl (Hinv eq_refl)).
      - exact (proj1 (proj2 (proj1 Henv))). }
    rewrite Hevcex, Hg2 in Hqf; cbn [andb] in Hqf.
    unfold rail_matches_dvalue in Hme; unfold eval_rail_psn in Hme; rewrite Hqf in Hme.
    subst ve; exists (eval_rail_val w asg2 re); exact Eve.
Qed.

Lemma blast_mc_obls_list_sat {Pa : Params} :
  forall ctx (penv : param_env Pa) foracle known_vars opt_inv is_body_mode body_hyp_lit obls env cexs env' asg,
    forallb (obl_wf_exprs known_vars) obls = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    wf_lit_bound (bs_next_var (be_st env)) body_hyp_lit ->
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg body_hyp_lit = true) ->
    blast_mc_obls_list ctx body_hyp_lit obls env = Some (cexs, env') ->
    exists asg',
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_lits_bound (bs_next_var (be_st env')) cexs /\
      ((forall l, In l cexs -> eval_lit asg' l = false) ->
       Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls).
Proof.
  intros ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit obls;
    induction obls as [| o rest IH];
    intros env cexs env' asg Hwf Hpenv Hctx Henv Hwbh Hbh_true Hbl;
    cbn [blast_mc_obls_list] in Hbl.
  - inversion Hbl; subst cexs env'; exists asg; split;
      [exact (step_spec_refl _ _ (proj1 Henv)) | split; [exact Henv | split; [constructor | intros _; constructor]]].
  - cbn [forallb] in Hwf; apply andb_true_iff in Hwf as [Ho Hrest].
    destruct (blast_mc_obl ctx body_hyp_lit env o) as [[cx env1] |] eqn:Ebo; [| discriminate Hbl].
    destruct (blast_mc_obls_list ctx body_hyp_lit rest env1) as [[cxs env2] |] eqn:Ebr; [| discriminate Hbl].
    inversion Hbl; subst cexs env'; clear Hbl.
    destruct (blast_mc_obl_sat ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit env o cx env1 asg
                Ho Hpenv Hctx Henv Hwbh Hbh_true Ebo)
      as (asg1 & Hs1 & Henv1 & Hwcx & Ho_sound).
    assert (Hbh1_wf : wf_lit_bound (bs_next_var (be_st env1)) body_hyp_lit)
      by exact (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hwbh).
    assert (Hbh1_true : is_body_mode = true -> match opt_inv with None => True | Some inv_e => eval_closed_cert_expr penv foracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))) end -> eval_lit asg1 body_hyp_lit = true).
    { intros Hbm Hinv; rewrite (step_spec_eval_lit _ _ _ _ _ Hs1 Hwbh); exact (Hbh_true Hbm Hinv). }
    destruct (IH env1 cxs env2 asg1 Hrest Hpenv Hctx Henv1 Hbh1_wf Hbh1_true Ebr)
      as (asg2 & Hs2 & Henv2 & Hwcxs & Hrest_sound).
    exists asg2; split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 Hs2) | split; [exact Henv2 | split]].
    + constructor; [exact (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwcx) | exact Hwcxs].
    + intros Hall; constructor.
      * apply Ho_sound; rewrite <- (step_spec_eval_lit _ _ _ _ _ Hs2 Hwcx); apply Hall; left; reflexivity.
      * apply Hrest_sound; intros l Hl; apply Hall; right; exact Hl.
Qed.

Theorem check_mc_loop_obls_sound {Pa : Params} :
  forall ctx known_vars opt_inv obls opt_pf (penv : param_env Pa) foracle is_body_mode,
    check_mc_loop_obls ctx known_vars opt_inv obls opt_pf = true ->
    wf_param_env_for known_vars penv ->
    ub_ctx_holds penv foracle ctx ->
    Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls.
Proof.
  intros ctx known_vars opt_inv obls opt_pf penv foracle is_body_mode Hchk Hpenv Hctx.
  unfold check_mc_loop_obls in Hchk.
  destruct (forallb (obl_wf_exprs known_vars) obls) eqn:Hwf_all; cbn [negb] in Hchk; [| discriminate Hchk].
  remember (List.filter (fun o => negb (obl_is_alg_ok ctx o)) obls) as rem eqn:Erem.
  assert (Halg : forall o, In o obls -> obl_is_alg_ok ctx o = true -> mc_obl_holds penv foracle opt_inv is_body_mode o).
  { intros o Ho Hal Hbm Hinv Hpath.
    rewrite forallb_forall in Hwf_all; pose proof (Hwf_all o Ho) as Hwfo.
    unfold obl_wf_exprs in Hwfo; apply andb_true_iff in Hwfo as [_ Hwfo].
    destruct o as [ib p w s t | ib p w e]; cbn in Hal; try discriminate Hal.
    destruct ib; [discriminate Hal |]; destruct p; [| discriminate Hal].
    rewrite !andb_true_iff in Hwfo; destruct Hwfo as (((((((((Hwts & Hwtt) & Hbws) & Hbwt) & Hlfs) & Hlft) & _) & _) & Hsubs) & Hsubt).
    exact (check_expr_refines_sound ctx s t penv foracle Hal
             (vars_subset_b_wf_param_env _ _ penv Hsubs Hpenv)
             (vars_subset_b_wf_param_env _ _ penv Hsubt Hpenv) Hctx). }
  assert (Hrem_wf : forallb (obl_wf_exprs known_vars) rem = true).
  { rewrite forallb_forall; intros o Ho; rewrite Erem in Ho; apply filter_In in Ho as [Ho _].
    rewrite forallb_forall in Hwf_all; exact (Hwf_all o Ho). }
  assert (Hfrom_rem : Forall (mc_obl_holds penv foracle opt_inv is_body_mode) rem ->
                      Forall (mc_obl_holds penv foracle opt_inv is_body_mode) obls).
  { intro Hfr; rewrite Forall_forall in Hfr |- *; intros o Ho.
    destruct (obl_is_alg_ok ctx o) eqn:Eal; [exact (Halg o Ho Eal) |].
    apply Hfr; rewrite Erem; apply filter_In; split; [exact Ho | rewrite Eal; reflexivity]. }
  apply Hfrom_rem.
  destruct rem as [| r0 rem']; [constructor |].
  destruct (build_mc_loop_cnf ctx known_vars opt_inv (r0 :: rem')) as [[nv f] |] eqn:Ebld; [| discriminate Hchk].
  unfold build_mc_loop_cnf in Ebld; rewrite Hrem_wf in Ebld; cbn [negb] in Ebld.
  set (init_env := mk_blast_env (init_blast_state 2%positive) [] []) in *.
  set (env0 := blast_ub_ctx ctx known_vars ctx init_env) in *.
  assert (Hinit_env : sat_blast_env penv foracle (fun _ => true) init_env)
    by (split; [exact init_blast_state_sat | split; intros; discriminate]).
  destruct (blast_ub_ctx_sat ctx known_vars ctx penv foracle (fun _ => true) init_env
              Hctx Hctx Hpenv Hinit_env) as [asg0 Henv0].
  set (hyp_res := match opt_inv with None => Some (lit_true, env0) | Some inv_e => if wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive && is_let_free_expr inv_e && ub_free_expr inv_e && AlgRules.vars_subset_b (collect_free_vars [] inv_e) known_vars then match blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0 with Some (ri, env_i) => let b0 := match rbv_bits ri with x :: _ => x | [] => lit_false end in let '(hlit, st1) := emit_and2_opt (neg_lit (rbv_psn ri)) b0 (be_st env_i) in Some (hlit, mk_blast_env st1 (be_vars env_i) (be_freezes env_i)) | None => None end else None end) in *.
  destruct hyp_res as [[body_hyp_lit env1] |] eqn:Ehyp; [| discriminate Ebld].
  assert (Hhyp_sat : exists asg1,
    sat_blast_env penv foracle asg1 env1 /\
    wf_lit_bound (bs_next_var (be_st env1)) body_hyp_lit /\
    (is_body_mode = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv foracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end ->
     eval_lit asg1 body_hyp_lit = true)).
  { unfold hyp_res in Ehyp; destruct opt_inv as [inv_e |].
    - destruct (wt_cert_expr [] inv_e && Pos.eqb (cert_expr_bit_width inv_e) 1%positive && is_let_free_expr inv_e && ub_free_expr inv_e && AlgRules.vars_subset_b (collect_free_vars [] inv_e) known_vars) eqn:Ewi; [| discriminate Ehyp].
      rewrite !andb_true_iff in Ewi; destruct Ewi as ((((Hwti & Hbwi) & _) & _) & Hsubi); apply Pos.eqb_eq in Hbwi.
      destruct (blast_cert_expr ctx [] (mc_ms_opt inv_e) inv_e env0) as [[ri env_i] |] eqn:Ebi; [| discriminate Ehyp].
      destruct (blast_cert_expr_sat inv_e ctx [] [] (mc_ms_opt inv_e) penv [] foracle asg0 env0 env_i ri
                  Ebi Hwti (wf_let_rails_sync_nil asg0 _) (mc_ms_opt_sync inv_e)
                  (vars_subset_b_wf_param_env _ _ penv Hsubi Hpenv) Hctx Henv0)
        as (asg_i & vi & Evi & Hsi & Henv_i & Hwfi & Hmri).
      rewrite Hbwi in Hwfi, Hmri; destruct Hwfi as ((_ & Hleni) & Hlbsi & Hpsi).
      destruct (rbv_bits ri) as [| bi0 rbitsi] eqn:Ebitsi; [cbn in Hleni; discriminate Hleni |].
      destruct (emit_and2_opt (neg_lit (rbv_psn ri)) bi0 (be_st env_i)) as [hlit st1] eqn:Ea_h.
      inversion Ehyp; subst body_hyp_lit env1; clear Ehyp.
      destruct (emit_and2_opt_step asg_i (neg_lit (rbv_psn ri)) bi0 (be_st env_i) hlit st1
                  (proj1 Henv_i) (wf_lit_bound_neg _ _ Hpsi) ltac:(inversion Hlbsi; assumption) Ea_h)
        as (asg1 & Hs1 & Hwhl & Hevh).
      exists asg1; split; [exact (sat_blast_env_step penv foracle asg_i asg1 env_i st1 Henv_i Hs1) | split; [exact Hwhl |]].
      intros _ Hinv; unfold eval_closed_cert_expr in Hinv; rewrite Evi in Hinv; inversion Hinv; subst vi; clear Hinv.
      unfold rail_matches_dvalue in Hmri.
      destruct (eval_rail_psn asg_i ri) eqn:Epsi; [discriminate Hmri |].
      unfold eval_rail_val in Hmri; rewrite Ebitsi in Hmri.
      unfold eval_rail_psn in Epsi; rewrite Hevh, (eval_neg_lit_nonzero asg_i _ (wf_lit_bound_nonzero _ _ Hpsi)), Epsi; cbn [negb andb].
      destruct rbitsi as [| ? ?]; [| cbn in Hleni; discriminate Hleni].
      pose proof (f_equal dvalue_int_unsigned Hmri) as Hu; cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite (@Integers.unsigned_one 1%positive) in Hu.
      destruct (eval_lit asg_i bi0); [reflexivity |
        cbn [List.map bools_to_Z Zshiftin dvalue_int_unsigned] in Hu;
        rewrite Integers.unsigned_repr in Hu by (change (@Integers.max_unsigned 1%positive) with 1%Z; lia); lia].
    - inversion Ehyp; subst body_hyp_lit env1; exists asg0.
      pose proof Henv0 as [[Hwf0 [Ht _]] _]; destruct Hwf0 as [Hge0 _].
      split; [exact Henv0 | split; [unfold env0, wf_lit_bound, lit_true; lia | intros _ _; cbn [eval_lit]; exact Ht]]. }
  destruct Hhyp_sat as (asg1 & Henv1 & Hbh_wf & Hbh_true).
  destruct (blast_mc_obls_list ctx body_hyp_lit (r0 :: rem') env1) as [[cex_lits env2] |] eqn:Eobls; [| discriminate Ebld].
  destruct (emit_or_list_opt cex_lits (be_st env2)) as [any_cex st_or] eqn:Eor.
  inversion Ebld; subst f; clear Ebld.
  destruct (blast_mc_obls_list_sat ctx penv foracle known_vars opt_inv is_body_mode body_hyp_lit (r0 :: rem')
              env1 cex_lits env2 asg1 Hrem_wf Hpenv Hctx Henv1 Hbh_wf Hbh_true Eobls)
    as (asg2 & Hs2 & Henv2 & Hwcexs & Hsound).
  destruct (emit_or_list_opt_step cex_lits asg2 (be_st env2) any_cex st_or Hwcexs (proj1 Henv2) Eor)
    as (asg3 & Hs3 & Hwany & Hev_any).
  assert (Hany_false : eval_lit asg3 any_cex = false).
  { destruct (eval_lit asg3 any_cex) eqn:Etrue; [| reflexivity].
    destruct (proj2 (proj2 Hs3)) as ([Hge3 Hwf_st3] & Ha1_3 & Hev_st3).
    assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st_or)) [[any_cex]]) by (repeat constructor; exact Hwany).
    assert (Hcls_sat : forall cl, In cl [[any_cex]] -> eval_clause asg3 cl = true)
      by (intros cl [<- | []]; cbn; rewrite Etrue; reflexivity).
    pose proof (add_clauses_sat_intro asg3 st_or [[any_cex]] Hge3 Ha1_3 Hwf_st3 Hcls_wf Hev_st3 Hcls_sat) as Hsat_fin.
    pose proof (check_cex_unsat_sound _ opt_pf Hchk asg3) as Huns.
    destruct Hsat_fin as [_ [_ Hsat_cnf]]; unfold add_clauses, bs_cnf in Hsat_cnf, Huns; cbn [append_clauses fst snd] in Hsat_cnf.
    rewrite Huns in Hsat_cnf; discriminate Hsat_cnf. }
  apply Hsound; intros l Hl.
  rewrite Hev_any, existsb_id_map_eval_lit in Hany_false.
  destruct (eval_lit asg2 l) eqn:Elt; [| reflexivity].
  exfalso; assert (Hex : existsb (eval_lit asg2) cex_lits = true)
    by (apply existsb_exists; exists l; split; [exact Hl | exact Elt]).
  congruence.
Qed.



(** ** 4. Shared MC Tree, Cutpoint/Skeleton States & Obligation Collection *)

Definition ir_seg_exprs_freeze_free_cut (phis : list (positive * cert_expr)) : bool :=
  forallb (fun '(_, ce) => negb (expr_has_freeze ce)) phis.

Fixpoint ir_seg_freeze_free (t : ir_seg_tree) : bool :=
  match t with
  | IST_Cut _ phis => ir_seg_exprs_freeze_free_cut phis
  | IST_Ret _ ret_e => negb (expr_has_freeze ret_e)
  | IST_UB => true
  | IST_Branch cond dt df =>
      negb (expr_has_freeze cond) && ir_seg_freeze_free dt && ir_seg_freeze_free df
  end.

Lemma binop_flags_weaken_refl : forall fl,
  binop_flags_weaken fl fl = true.
Proof.
  intros [nuw nsw ex disj]; unfold binop_flags_weaken; cbn.
  destruct nuw, nsw, ex, disj; reflexivity.
Qed.

Lemma cast_flags_weaken_refl : forall fl,
  cast_flags_weaken fl fl = true.
Proof.
  intros [nn nu ns]; unfold cast_flags_weaken; cbn.
  destruct nn, nu, ns; reflexivity.
Qed.

Lemma eval_cert_expr_refine_mono {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    ub_free_expr e = true ->
    expr_has_freeze e = false ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) ->
       exists d1 d2 : @dvalue Pa,
         penv1 nm = Some d1 /\
         penv2 nm = Some d2 /\
         wf_scalar_dvalue w d1 /\
         wf_scalar_dvalue w d2 /\
         dvalue_refines d1 d2) ->
    exists v1 v2 : @dvalue Pa,
      eval_closed_cert_expr penv1 foracle e = raise_ret v1 /\
      eval_closed_cert_expr penv2 foracle e = raise_ret v2 /\
      wf_scalar_dvalue (cert_expr_bit_width e) v1 /\
      wf_scalar_dvalue (cert_expr_bit_width e) v2 /\
      dvalue_refines v1 v2.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o _
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf Hub Hnfrz Hvars;
    unfold eval_closed_cert_expr in *;
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr expr_has_freeze collect_free_vars eval_cert_expr lookup_let_val] in *.
  - eexists _, _; repeat split; try reflexivity;
      [right; eexists; reflexivity | right; eexists; reflexivity | apply dvalue_refines_refl].
  - eexists _, _; repeat split; try reflexivity;
      [left; reflexivity | left; reflexivity | apply dvalue_refines_refl].
  - destruct (Hvars nm w (or_introl eq_refl)) as (d1 & d2 & Hp1 & Hp2 & Hwf1 & Hwf2 & Href).
    rewrite Hp1, Hp2.
    assert (Hck1 : check_scalar_width w d1 = raise_ret d1)
      by (destruct Hwf1 as [-> | [i1 ->]]; cbn; rewrite ?Pos.eqb_refl; reflexivity).
    assert (Hck2 : check_scalar_width w d2 = raise_ret d2)
      by (destruct Hwf2 as [-> | [i2 ->]]; cbn; rewrite ?Pos.eqb_refl; reflexivity).
    rewrite Hck1, Hck2; eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_l Hnf_r].
    destruct Hwt as ((((Hsh & Hwtl) & Hwtr) & Hbw1) & Hbw2); apply Pos.eqb_eq in Hbw1; apply Pos.eqb_eq in Hbw2.
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [[Hnop Hubl] Hubr].
    destruct (IHl Hwtl Hlfl Hubl Hnf_l (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vl1 & vl2 & El1 & El2 & Wl1 & Wl2 & Rl).
    destruct (IHr Hwtr Hlfr Hubr Hnf_r (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror Hx))))
      as (vr1 & vr2 & Er1 & Er2 & Wr1 & Wr2 & Rr).
    rewrite Hbw1 in Wl1, Wl2; rewrite Hbw2 in Wr1, Wr2; apply negb_true_iff in Hnop.
    destruct (eval_iop_non_div_rem_no_ub op fl w vl1 vr1 Hnop Wl1 Wr1) as [v1 [Ev1 W1]].
    destruct (eval_iop_non_div_rem_no_ub op fl w vl2 vr2 Hnop Wl2 Wr2) as [v2 [Ev2 W2]].
    pose proof (eval_iop_non_div_rem_monotone op fl fl w vl1 vl2 vr1 vr2 Hnop (binop_flags_weaken_refl fl) Wl1 Wl2 Wr1 Wr2 Rl Rr) as Hm.
    rewrite El1, El2, Er1, Er2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_l Hnf_r].
    destruct Hwt as (((Hwtl & Hwtr) & Hbw1) & Hbw2); apply Pos.eqb_eq in Hbw1; apply Pos.eqb_eq in Hbw2.
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [Hubl Hubr].
    destruct (IHl Hwtl Hlfl Hubl Hnf_l (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vl1 & vl2 & El1 & El2 & Wl1 & Wl2 & Rl).
    destruct (IHr Hwtr Hlfr Hubr Hnf_r (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror Hx))))
      as (vr1 & vr2 & Er1 & Er2 & Wr1 & Wr2 & Rr).
    rewrite Hbw1 in Wl1, Wl2; rewrite Hbw2 in Wr1, Wr2.
    destruct (eval_icmp_wf_scalar ss pr w vl1 vr1 Wl1 Wr1) as [v1 [Ev1 W1]].
    destruct (eval_icmp_wf_scalar ss pr w vl2 vr2 Wl2 Wr2) as [v2 [Ev2 W2]].
    assert (Himp : implb ss ss = true) by (destruct ss; reflexivity).
    pose proof (eval_icmp_monotone ss ss pr w vl1 vl2 vr1 vr2 Himp Wl1 Wl2 Wr1 Wr2 Rl Rr) as Hm.
    rewrite El1, El2, Er1, Er2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; destruct Hwt as [[Hck Hwto] Hbwo]; apply Pos.eqb_eq in Hbwo.
    destruct (IHo Hwto Hlf Hub Hnfrz Hvars) as (vo1 & vo2 & Eo1 & Eo2 & Wo1 & Wo2 & Ro).
    rewrite Hbwo in Wo1, Wo2.
    destruct (eval_cast_wf_scalar k fw tw fl vo1 Hck Wo1) as [v1 [Ev1 W1]].
    destruct (eval_cast_wf_scalar k fw tw fl vo2 Hck Wo2) as [v2 [Ev2 W2]].
    pose proof (eval_cast_monotone k fw tw fl fl vo1 vo2 Hck Hck (cast_flags_weaken_refl fl) Wo1 Wo2 Ro) as Hm.
    rewrite Eo1, Eo2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_ct Hnf_f]; apply orb_false_iff in Hnf_ct as [Hnf_c Hnf_t].
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hbwc) & Hbwt) & Hbwf).
    apply Pos.eqb_eq in Hbwc; apply Pos.eqb_eq in Hbwt; apply Pos.eqb_eq in Hbwf.
    destruct Hlf as [[Hlfc Hlft] Hlff]; destruct Hub as [[Hubc Hubt] Hubf].
    destruct (IHc Hwtc Hlfc Hubc Hnf_c (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vc1 & vc2 & Ec1 & Ec2 & Wc1 & Wc2 & Rc).
    destruct (IHt Hwtt Hlft Hubt Hnf_t (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx))))))
      as (vt1 & vt2 & Et1 & Et2 & Wt1 & Wt2 & Rt).
    destruct (IHf Hwtf Hlff Hubf Hnf_f (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx))))))
      as (vf1 & vf2 & Ef1 & Ef2 & Wf1 & Wf2 & Rf).
    rewrite Hbwc in Wc1, Wc2; rewrite Hbwt in Wt1, Wt2; rewrite Hbwf in Wf1, Wf2.
    destruct (eval_select_wf_scalar w vc1 vt1 vf1 Wc1 Wt1 Wf1) as [v1 [Ev1 W1]].
    destruct (eval_select_wf_scalar w vc2 vt2 vf2 Wc2 Wt2 Wf2) as [v2 [Ev2 W2]].
    pose proof (eval_select_monotone w vc1 vc2 vt1 vt2 vf1 vf2 Wc1 Wc2 Wt1 Wt2 Wf1 Wf2 Rc Rt Rf) as Hm.
    rewrite Ec1, Ec2, Et1, Et2, Ef1, Ef2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - discriminate Hnfrz.
  - discriminate Hlf.
Qed.

Inductive mc_seg_tree : Type :=
| MST_Cut (sp_off : Z) (rr : N -> mc_sym_val) (astk : mc_sym_stack)
| MST_Ret (ret_e : cert_expr)
| MST_Branch (cond : cert_expr) (dt df : mc_seg_tree).

Fixpoint rv_seg_to_mc_seg (t : rv_seg_tree) : mc_seg_tree :=
  match t with
  | RST_Cut sp vrf stk => MST_Cut sp (fun r => rv_val_read r vrf) stk
  | RST_Ret ret_e => MST_Ret ret_e
  | RST_Branch cond dt df => MST_Branch cond (rv_seg_to_mc_seg dt) (rv_seg_to_mc_seg df)
  end.

Fixpoint a64_seg_to_mc_seg (t : a64_seg_tree) : mc_seg_tree :=
  match t with
  | AST_Cut sp vrf stk => MST_Cut sp (fun r => a64_val_read r vrf) stk
  | AST_Ret ret_e => MST_Ret ret_e
  | AST_Branch cond dt df => MST_Branch cond (a64_seg_to_mc_seg dt) (a64_seg_to_mc_seg df)
  end.

Fixpoint mc_seg_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (P_cut : Z -> (N -> mc_sym_val) -> mc_sym_stack -> Prop)
  (P_ret : cert_expr -> Prop)
  (t : mc_seg_tree) {struct t} : Prop :=
  match t with
  | MST_Cut sp rr astk => P_cut sp rr astk
  | MST_Ret ret_e => P_ret ret_e
  | MST_Branch cond dt df =>
      exists b : bool,
        eval_closed_cert_expr penv foracle cond =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
        mc_seg_holds penv foracle P_cut P_ret (if b then dt else df)
  end.

Lemma rv_seg_exec_to_mc {Pa : Params} :
  forall penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w (t : rv_seg_tree),
    @rv_seg_exec_spec Pa penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w t ->
    mc_seg_holds penv foracle
      (fun sp_off' rr' astk' =>
         exists n rf' mstk',
           (req_step = true -> (1 <= n)%nat) /\
           rv_exec_steps n insts (rv_read_reg 2%N rf0) pc rf mstk = Some (cut_pc, rf', mstk') /\
           (- mc_frame_cap <= sp_off' <= 0)%Z /\
           rr' 2%N = MSV_StackPtr sp_off' /\
           (forall r, mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) (rr' r) (rv_read_reg r rf')) /\
           mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk' mstk')
      (fun ret_e =>
         exists fuel_end rf_end mstk_end,
           rv_exec_mem fuel_end insts pc (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
           rv_callee_saved_preserved rf0 rf_end /\
           rf_end 1%N = rf0 1%N /\
           eval_closed_cert_expr penv foracle ret_e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rf_end 10%N)))))
      (rv_seg_to_mc_seg t).
Proof.
  intros penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w t.
  induction t as [sp' vrf' astk' | ret_e | cond dt IHt df IHf];
    intro Hspec; cbn [rv_seg_exec_spec rv_seg_to_mc_seg mc_seg_holds] in *.
  - exact Hspec.
  - exact Hspec.
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |].
    destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Lemma a64_seg_exec_to_mc {Pa : Params} :
  forall penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w (t : a64_seg_tree),
    @a64_seg_exec_spec Pa penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w t ->
    mc_seg_holds penv foracle
      (fun sp_off' rr' astk' =>
         exists n rf' sp' fl' mstk',
           (req_step = true -> (1 <= n)%nat) /\
           a64_exec_steps n insts sp0 pc rf sp fl mstk = Some (cut_pc, rf', sp', fl', mstk') /\
           (- mc_frame_cap <= sp_off' <= 0)%Z /\
           sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
           (forall r, mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 (rr' r) (a64_read_reg r rf')) /\
           mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk')
      (fun ret_e =>
         exists fuel_end rf_end fl_end mstk_end,
           a64_exec_mem fuel_end insts pc sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
           a64_callee_saved_preserved rf0 rf_end /\
           eval_closed_cert_expr penv foracle ret_e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))
      (a64_seg_to_mc_seg t).
Proof.
  intros penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w t.
  induction t as [sp' vrf' astk' | ret_e | cond dt IHt df IHf];
    intro Hspec; cbn [a64_seg_exec_spec a64_seg_to_mc_seg mc_seg_holds] in *.
  - exact Hspec.
  - exact Hspec.
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |].
    destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Fixpoint extract_hdr_phis (phis : list (raw_id * phi dtyp * list (metadata dtyp)))
  : option (list (raw_id * positive)) :=
  match phis with
  | [] => Some []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) _, _) :: rest =>
      if is_supported_bit_width w then
        match extract_hdr_phis rest with
        | Some rs => Some ((id, w) :: rs)
        | None => None
        end
      else None
  | _ :: _ => None
  end.

Definition hi32_vars (ls : mc_loop_spec) : list (string * positive) :=
  List.flat_map (fun rb =>
    if Pos.eqb (mlr_width rb) 32%positive then [(mc_hi_var_name (mlr_reg rb), 64%positive)] else [])
    (ml_regs ls).

Definition cut_reg_expr (rb : mc_loop_reg_bind) : cert_expr :=
  if Pos.eqb (mlr_width rb) 64%positive then mlr_expr rb
  else combine_hi32_expr (CE_Var (mc_hi_var_name (mlr_reg rb)) 64%positive) (mlr_expr rb).

Definition cut_slot_expr (sz : mc_mem_size) (e : cert_expr) : cert_expr :=
  match sz with
  | MS_8 => e
  | _ => CE_Cast CCK_ZExt (mc_mem_bits sz) 64%positive no_cast_flags e
  end.

Definition slot_has_saved_reg (slots : list mc_loop_slot_bind) (r : N) : bool :=
  existsb (fun sb => match sb with MLS_SavedReg _ r0 => N.eqb r0 r | _ => false end) slots.

Definition build_cut_astk (slots : list mc_loop_slot_bind) : mc_sym_stack :=
  List.map (fun sb =>
    match sb with
    | MLS_Expr off sz e => (off, sz, MSV_Expr (cut_slot_expr sz e))
    | MLS_SavedReg off r => (off, MS_8, MSV_SavedReg r)
    end) slots.

Fixpoint build_skel_astk (idx : nat) (slots : list mc_loop_slot_bind) {struct slots} : mc_sym_stack :=
  match slots with
  | [] => []
  | MLS_Expr off sz _ :: rest =>
      (off, sz, MSV_Expr (CE_Var (mc_skel_slot_name idx) 64%positive)) :: build_skel_astk (S idx) rest
  | MLS_SavedReg off r :: rest =>
      (off, MS_8, MSV_SavedReg r) :: build_skel_astk (S idx) rest
  end.

Definition rv_cut_base_vrf (ls : mc_loop_spec) : rv_val_regs :=
  fun r =>
    if N.eqb r 0%N then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if N.eqb r 2%N then MSV_StackPtr (ml_sp_off ls)
    else if n_in_list r rv_preserved_non_sp_regs && negb (slot_has_saved_reg (ml_slots ls) r) then MSV_SavedReg r
    else MSV_Undef.

Definition rv_cut_vrf (ls : mc_loop_spec) : rv_val_regs :=
  List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf)
    (ml_regs ls) (rv_cut_base_vrf ls).

Definition rv_skel_vrf (ls : mc_loop_spec) : rv_val_regs :=
  List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf)
    (ml_regs ls) (rv_cut_base_vrf ls).

Definition a64_cut_base_vrf (ls : mc_loop_spec) : a64_val_regs :=
  fun r =>
    if N.leb 31%N r then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if a64_is_callee_saved r && negb (slot_has_saved_reg (ml_slots ls) r) then MSV_SavedReg r
    else MSV_Undef.

Definition a64_cut_vrf (ls : mc_loop_spec) : a64_val_regs :=
  List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf)
    (ml_regs ls) (a64_cut_base_vrf ls).

Definition a64_skel_vrf (ls : mc_loop_spec) : a64_val_regs :=
  List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf)
    (ml_regs ls) (a64_cut_base_vrf ls).

Definition mc_preserved_regs (arch : elf_arch) : list N :=
  match arch with
  | EA_Riscv64 => rv_preserved_non_sp_regs
  | EA_AArch64 => a64_callee_saved_list
  end.

Definition mc_unspilled_preserved (arch : elf_arch) (ls : mc_loop_spec) : list N :=
  List.filter (fun r =>
    negb (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) &&
    negb (slot_has_saved_reg (ml_slots ls) r))
    (mc_preserved_regs arch).

Fixpoint mc_skel_tree_ok (arch : elf_arch) (ls : mc_loop_spec) (t : mc_seg_tree) {struct t} : bool :=
  match t with
  | MST_Cut sp' rr' astk' =>
      Z.eqb sp' (ml_sp_off ls) &&
      forallb (fun r => match rr' r with MSV_SavedReg r0 => N.eqb r0 r | _ => false end)
        (mc_unspilled_preserved arch ls) &&
      forallb (fun sb =>
        match sb with
        | MLS_Expr _ _ _ => true
        | MLS_SavedReg off r =>
            match mc_sym_stk_load off MS_8 false astk' with
            | Some (MSV_SavedReg r0) => N.eqb r0 r
            | _ => false
            end
        end) (ml_slots ls)
  | MST_Ret _ => true
  | MST_Branch _ dt df => mc_skel_tree_ok arch ls dt && mc_skel_tree_ok arch ls df
  end.

Definition expr_has_var (nm : string) (e : cert_expr) : bool :=
  existsb (fun '(x, _) => String.eqb x nm) (collect_free_vars [] e).

Definition is_exact_cut_var (k : nat) (w : positive) (e : cert_expr) : bool :=
  match e with
  | CE_Var nm w' => String.eqb nm (mc_cut_var_name k) && Pos.eqb w w'
  | _ => false
  end.

Definition reg_slot_uses_cut_var_ok (k : nat) (w : positive) (e : cert_expr) : bool :=
  negb (expr_has_var (mc_cut_var_name k) e) || is_exact_cut_var k w e.

Definition cut_var_bind_count (k : nat) (rbs : list mc_loop_reg_bind) (sbs : list mc_loop_slot_bind) : nat :=
  List.length (List.filter (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) rbs) +
  List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) sbs).

Definition cut_var_ptol (ls : mc_loop_spec) (k : nat) (w : positive) : bool :=
  match ml_inv ls with
  | None => true
  | Some inv_e => negb (expr_has_var (mc_cut_var_name k) inv_e)
  end &&
  Nat.leb (cut_var_bind_count k (ml_regs ls) (ml_slots ls)) 1 &&
  forallb (fun rb => reg_slot_uses_cut_var_ok k w (mlr_expr rb)) (ml_regs ls) &&
  forallb (fun sb => match sb with MLS_Expr _ _ e => reg_slot_uses_cut_var_ok k w e | MLS_SavedReg _ _ => true end) (ml_slots ls).

Fixpoint expr_is_ptol_var_at (ls : mc_loop_spec) (idx : nat) (hdr_ws : list positive) (e : cert_expr) {struct hdr_ws} : bool :=
  match hdr_ws with
  | [] => false
  | w :: rest =>
      (is_exact_cut_var idx w e && cut_var_ptol ls idx w) ||
      expr_is_ptol_var_at ls (S idx) rest e
  end.

Definition expr_is_ptol_var (ls : mc_loop_spec) (hdr_ws : list positive) (e : cert_expr) : bool :=
  expr_is_ptol_var_at ls 0%nat hdr_ws e.

Fixpoint build_phi_subst (idx : nat) (phis : list (positive * cert_expr)) {struct phis}
  : list (string * positive * cert_expr) :=
  match phis with
  | [] => []
  | (w, ce) :: rest => (mc_cut_var_name idx, w, ce) :: build_phi_subst (S idx) rest
  end.

Fixpoint collect_phi_def_obls
  (ls : mc_loop_spec) (is_body : bool) (path : list (bool * cert_expr))
  (idx : nat) (phis : list (positive * cert_expr)) {struct phis} : list mc_loop_obl :=
  match phis with
  | [] => []
  | (w, ce) :: rest =>
      (if cut_var_ptol ls idx w then [] else [MLO_Defined is_body path w ce]) ++
      collect_phi_def_obls ls is_body path (S idx) rest
  end.

Definition trunc_mc_expr_to (w : positive) (e64 : cert_expr) : cert_expr :=
  if Pos.eqb w 64%positive then e64
  else CE_Cast CCK_Trunc 64%positive w no_cast_flags e64.

Definition trunc_mc_slot_expr (sz : mc_mem_size) (e64 : cert_expr) : cert_expr :=
  match sz with
  | MS_8 => e64
  | _ => CE_Cast CCK_Trunc 64%positive (mc_mem_bits sz) no_cast_flags e64
  end.

Fixpoint collect_reg_cut_obls
  (ls : mc_loop_spec) (hdr_ws : list positive) (is_body : bool) (path : list (bool * cert_expr))
  (sub : list (string * positive * cert_expr)) (rr' : N -> mc_sym_val) (rbs : list mc_loop_reg_bind)
  {struct rbs} : option (list mc_loop_obl) :=
  match rbs with
  | [] => Some []
  | rb :: rest =>
      match rr' (mlr_reg rb) with
      | MSV_Expr e_mc64 =>
          match collect_reg_cut_obls ls hdr_ws is_body path sub rr' rest with
          | None => None
          | Some obls_r =>
              let e_src := subst_cert_expr sub (mlr_expr rb) in
              let e_tgt := trunc_mc_expr_to (mlr_width rb) e_mc64 in
              let def_l := if expr_is_ptol_var ls hdr_ws (mlr_expr rb) then [] else [MLO_Defined is_body path (mlr_width rb) e_src] in
              Some (def_l ++ [MLO_Refine is_body path (mlr_width rb) e_src e_tgt] ++ obls_r)
          end
      | _ => None
      end
  end.

Fixpoint collect_slot_cut_obls
  (ls : mc_loop_spec) (hdr_ws : list positive) (is_body : bool) (path : list (bool * cert_expr))
  (sub : list (string * positive * cert_expr)) (astk' : mc_sym_stack) (sbs : list mc_loop_slot_bind)
  {struct sbs} : option (list mc_loop_obl) :=
  match sbs with
  | [] => Some []
  | MLS_SavedReg off r :: rest =>
      match mc_sym_stk_load off MS_8 false astk' with
      | Some (MSV_SavedReg r0) =>
          if N.eqb r0 r then collect_slot_cut_obls ls hdr_ws is_body path sub astk' rest else None
      | _ => None
      end
  | MLS_Expr off sz e_s :: rest =>
      match mc_sym_stk_load off sz false astk' with
      | Some (MSV_Expr e_mc64) =>
          match collect_slot_cut_obls ls hdr_ws is_body path sub astk' rest with
          | None => None
          | Some obls_r =>
              let w := mc_mem_bits sz in
              let e_src := subst_cert_expr sub e_s in
              let e_tgt := trunc_mc_slot_expr sz e_mc64 in
              let def_l := if expr_is_ptol_var ls hdr_ws e_s then [] else [MLO_Defined is_body path w e_src] in
              Some (def_l ++ [MLO_Refine is_body path w e_src e_tgt] ++ obls_r)
          end
      | _ => None
      end
  end.

Definition imposs_obl (is_body : bool) (path : list (bool * cert_expr)) : list mc_loop_obl :=
  [MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (CE_BvConst 1%positive 0%N)].

Fixpoint check_widths_match (ws : list positive) (phis : list (positive * cert_expr)) {struct ws} : bool :=
  match ws, phis with
  | [], [] => true
  | w :: rw, (wp, _) :: rp => Pos.eqb w wp && check_widths_match rw rp
  | _, _ => false
  end.

Fixpoint collect_mc_ir_obls
  (arch : elf_arch) (ls : mc_loop_spec) (ret_w : positive) (hdr_ws : list positive)
  (is_body : bool) (path : list (bool * cert_expr)) (t_ir : ir_seg_tree) (t_mc : mc_seg_tree)
  {struct t_ir} : list mc_loop_obl :=
  match t_ir with
  | IST_UB => []
  | IST_Branch cond dt_ir df_ir =>
      collect_mc_ir_obls arch ls ret_w hdr_ws is_body (path ++ [(true, cond)]) dt_ir t_mc ++
      collect_mc_ir_obls arch ls ret_w hdr_ws is_body (path ++ [(false, cond)]) df_ir t_mc
  | IST_Ret rw ret_ir =>
      (fix go_mc (u : mc_seg_tree) (p : list (bool * cert_expr)) {struct u} : list mc_loop_obl :=
        match u with
        | MST_Branch cond_mc dt_mc df_mc =>
            go_mc dt_mc (p ++ [(true, cond_mc)]) ++ go_mc df_mc (p ++ [(false, cond_mc)])
        | MST_Ret ret_mc =>
            if Pos.eqb rw ret_w then [MLO_Refine is_body p rw ret_ir ret_mc] else imposs_obl is_body p
        | MST_Cut _ _ _ => imposs_obl is_body p
        end) t_mc path
  | IST_Cut _ phis_ir =>
      (fix go_mc (u : mc_seg_tree) (p : list (bool * cert_expr)) {struct u} : list mc_loop_obl :=
        match u with
        | MST_Branch cond_mc dt_mc df_mc =>
            go_mc dt_mc (p ++ [(true, cond_mc)]) ++ go_mc df_mc (p ++ [(false, cond_mc)])
        | MST_Ret _ => imposs_obl is_body p
        | MST_Cut sp' rr' astk' =>
            let pres_ok :=
              Z.eqb sp' (ml_sp_off ls) &&
              forallb (fun r => match rr' r with MSV_SavedReg r0 => N.eqb r0 r | _ => false end)
                (mc_unspilled_preserved arch ls) &&
              check_widths_match hdr_ws phis_ir
            in
            if negb pres_ok then imposs_obl is_body p
            else
              let sub := build_phi_subst 0%nat phis_ir in
              match collect_reg_cut_obls ls hdr_ws is_body p sub rr' (ml_regs ls),
                    collect_slot_cut_obls ls hdr_ws is_body p sub astk' (ml_slots ls) with
              | Some robls, Some sobls =>
                  let iobls :=
                    match ml_inv ls with
                    | None => []
                    | Some inv_e => [MLO_Refine is_body p 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr sub inv_e)]
                    end in
                  collect_phi_def_obls ls is_body p 0%nat phis_ir ++ robls ++ sobls ++ iobls
              | _, _ => imposs_obl is_body p
              end
        end) t_mc path
  end.

Lemma cut_slot_expr_wf : forall allowed off sz e,
  mc_slot_in_frame 0%Z off sz = true ->
  wt_cert_expr [] e = true ->
  cert_expr_bit_width e = mc_mem_bits sz ->
  is_let_free_expr e = true ->
  vars_subset_b (collect_free_vars [] e) allowed = true ->
  mc_sym_val_wf allowed (MSV_Expr (cut_slot_expr sz e)).
Proof.
  intros allowed off sz e _ Hwt Hbw Hlf Hsub.
  destruct sz; unfold cut_slot_expr, mc_sym_val_wf;
    [apply wf_sym_cast; [reflexivity |]
    | apply wf_sym_cast; [reflexivity |]
    | apply wf_sym_cast; [reflexivity |]
    |];
    unfold wf_sym_expr; cbn [mc_mem_bits]; rewrite Hwt, Hbw, Hlf; repeat split; try reflexivity; exact Hsub.
Qed.

Lemma mc_stk_load_expr_agrees {Pa : Params} :
  forall penv foracle off sz (mstk : mc_stack_mem) (e : cert_expr),
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz)
      (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))) ->
    exists v64 : @Integers.bit_int 64%positive,
      eval_closed_cert_expr penv foracle (cut_slot_expr sz e) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) /\
      mc_stk_load mstk off sz false =
        (match sz with
         | MS_8 => v64
         | _ =>
             let w := mc_mem_bits sz in
             @Integers.repr 64%positive (@Integers.unsigned w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
         end) /\
      mc_stk_load mstk off sz true =
        (match sz with
         | MS_8 => v64
         | _ =>
             let w := mc_mem_bits sz in
             @Integers.repr 64%positive (@Integers.signed w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
         end).
Proof.
  intros penv foracle off sz mstk e He.
  destruct sz; unfold cut_slot_expr.
  - (* MS_1: 8-bit *)
    pose proof (eval_ce_zext penv foracle 8%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 1%N) with 1%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 1%nat) as Hb.
    change (N.pow 256%N (N.of_nat 1%nat)) with 256%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 256%N) with 256%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 1%nat)) as Hnn.
    assert (Hu8 : @Integers.unsigned 8%positive (@Integers.repr 8%positive (Z.of_N (mc_stk_read_bytes mstk off 1%nat))) = Z.of_N (mc_stk_read_bytes mstk off 1%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 8%positive) with 255%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 1%nat))) = Z.of_N (mc_stk_read_bytes mstk off 1%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu8 | rewrite Hu64]); split; reflexivity.
  - (* MS_2: 16-bit *)
    pose proof (eval_ce_zext penv foracle 16%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 2%N) with 2%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 2%nat) as Hb.
    change (N.pow 256%N (N.of_nat 2%nat)) with 65536%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 65536%N) with 65536%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 2%nat)) as Hnn.
    assert (Hu16 : @Integers.unsigned 16%positive (@Integers.repr 16%positive (Z.of_N (mc_stk_read_bytes mstk off 2%nat))) = Z.of_N (mc_stk_read_bytes mstk off 2%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 16%positive) with 65535%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 2%nat))) = Z.of_N (mc_stk_read_bytes mstk off 2%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu16 | rewrite Hu64]); split; reflexivity.
  - (* MS_4: 32-bit *)
    pose proof (eval_ce_zext penv foracle 32%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 4%N) with 4%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 4%nat) as Hb.
    change (N.pow 256%N (N.of_nat 4%nat)) with 4294967296%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 4294967296%N) with 4294967296%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 4%nat)) as Hnn.
    assert (Hu32 : @Integers.unsigned 32%positive (@Integers.repr 32%positive (Z.of_N (mc_stk_read_bytes mstk off 4%nat))) = Z.of_N (mc_stk_read_bytes mstk off 4%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 32%positive) with 4294967295%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 4%nat))) = Z.of_N (mc_stk_read_bytes mstk off 4%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu32 | rewrite Hu64]); split; reflexivity.
  - (* MS_8: 64-bit *)
    cbn [mc_mem_bits] in He; rewrite (@Integers.repr_unsigned 64%positive) in He.
    exists (mc_stk_load mstk off MS_8 false); split; [exact He |].
    unfold mc_stk_load; cbn; split; reflexivity.
Qed.

Lemma build_cut_astk_agrees {Pa : Params} :
  forall penv foracle read_init sp0 slots mstk,
    (forall off sz e, In (MLS_Expr off sz e) slots ->
       eval_closed_cert_expr penv foracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz)
           (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))) ->
    (forall off r, In (MLS_SavedReg off r) slots ->
       mc_stk_load mstk off MS_8 false = read_init r) ->
    mc_sym_stack_agrees penv foracle read_init sp0 (build_cut_astk slots) mstk.
Proof.
  intros penv foracle read_init sp0 slots mstk Hexpr Hsav.
  unfold build_cut_astk, mc_sym_stack_agrees; apply Forall_forall.
  intros [[off sz] sv] Hin; apply in_map_iff in Hin as [sb [Heq Hsb]].
  destruct sb as [o s e | o r]; inversion Heq; subst; clear Heq.
  - exact (mc_stk_load_expr_agrees penv foracle off sz mstk e (Hexpr off sz e Hsb)).
  - split; [reflexivity | exact (Hsav off r Hsb)].
Qed.

Lemma build_skel_astk_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 idx slots mstk,
    (forall i o s e, nth_error slots i = Some (MLS_Expr o s e) ->
       penv (mc_skel_slot_name (idx + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))) ->
    (forall o r, In (MLS_SavedReg o r) slots -> mc_stk_load mstk o MS_8 false = read_init r) ->
    mc_sym_stack_agrees penv foracle read_init sp0 (build_skel_astk idx slots) mstk.
Proof.
  intros penv foracle read_init sp0 idx slots; revert idx;
    induction slots as [| sb rest IH]; intros idx mstk Hp Hsav;
    cbn [build_skel_astk]; [constructor |].
  assert (Hp_rest : forall i o s e, nth_error rest i = Some (MLS_Expr o s e) ->
    penv (mc_skel_slot_name (S idx + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; replace (S idx + i)%nat with (idx + S i)%nat by lia; exact (Hp (S i) o s e Hnth). }
  destruct sb as [o s e | o r]; constructor.
  - pose proof (Hp 0%nat o s e eq_refl) as H0; rewrite Nat.add_0_r in H0.
    exists (mc_stk_load mstk o s false); split.
    + unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite H0; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + destruct s; unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *.
      * change (N.to_nat 1%N) with 1%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 1%nat) as Hb;
          change (N.pow 256%N (N.of_nat 1%nat)) with 256%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 256%N) with 256%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 1%nat)) as Hnn;
          assert (Hu8 : @Integers.unsigned 8%positive (@Integers.repr 8%positive (Z.of_N (mc_stk_read_bytes mstk o 1%nat))) = Z.of_N (mc_stk_read_bytes mstk o 1%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 8%positive) with 255%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 1%nat))) = Z.of_N (mc_stk_read_bytes mstk o 1%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu8 | rewrite Hu64]); split; reflexivity.
      * change (N.to_nat 2%N) with 2%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 2%nat) as Hb;
          change (N.pow 256%N (N.of_nat 2%nat)) with 65536%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 65536%N) with 65536%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 2%nat)) as Hnn;
          assert (Hu16 : @Integers.unsigned 16%positive (@Integers.repr 16%positive (Z.of_N (mc_stk_read_bytes mstk o 2%nat))) = Z.of_N (mc_stk_read_bytes mstk o 2%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 16%positive) with 65535%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 2%nat))) = Z.of_N (mc_stk_read_bytes mstk o 2%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu16 | rewrite Hu64]); split; reflexivity.
      * change (N.to_nat 4%N) with 4%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 4%nat) as Hb;
          change (N.pow 256%N (N.of_nat 4%nat)) with 4294967296%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 4294967296%N) with 4294967296%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 4%nat)) as Hnn;
          assert (Hu32 : @Integers.unsigned 32%positive (@Integers.repr 32%positive (Z.of_N (mc_stk_read_bytes mstk o 4%nat))) = Z.of_N (mc_stk_read_bytes mstk o 4%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 32%positive) with 4294967295%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 4%nat))) = Z.of_N (mc_stk_read_bytes mstk o 4%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu32 | rewrite Hu64]); split; reflexivity.
      * split; reflexivity.
  - exact (IH (S idx) mstk Hp_rest (fun o0 r0 H => Hsav o0 r0 (or_intror H))).
  - split; [reflexivity | exact (Hsav o r (or_introl eq_refl))].
  - exact (IH (S idx) mstk Hp_rest (fun o0 r0 H => Hsav o0 r0 (or_intror H))).
Qed.

Lemma rv_val_write_eq : forall r sv vrf,
  r <> 0%N -> rv_val_read r (rv_val_write r sv vrf) = sv.
Proof.
  intros r sv vrf Hne; unfold rv_val_read, rv_val_write.
  destruct (N.eqb r 0%N) eqn:Er0; [apply N.eqb_eq in Er0; contradiction |].
  rewrite N.eqb_refl; reflexivity.
Qed.

Lemma rv_val_write_neq : forall r r' sv vrf,
  r' <> r -> rv_val_read r' (rv_val_write r sv vrf) = rv_val_read r' vrf.
Proof.
  intros r r' sv vrf Hne; unfold rv_val_read, rv_val_write.
  destruct (N.eqb r' 0%N) eqn:Er0'; [reflexivity |].
  destruct (N.eqb r 0%N); [reflexivity |].
  destruct (N.eqb r' r) eqn:Eeq; [apply N.eqb_eq in Eeq; contradiction | reflexivity].
Qed.

Lemma a64_val_write_eq : forall r sv vrf,
  (r < 31)%N -> a64_val_read r (a64_val_write r sv vrf) = sv.
Proof.
  intros r sv vrf Hlt; unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r) eqn:Er31; [apply N.leb_le in Er31; lia |].
  rewrite N.eqb_refl; reflexivity.
Qed.

Lemma a64_val_write_neq : forall r r' sv vrf,
  r' <> r -> a64_val_read r' (a64_val_write r sv vrf) = a64_val_read r' vrf.
Proof.
  intros r r' sv vrf Hne; unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r') eqn:Er31'; [reflexivity |].
  destruct (N.leb 31%N r); [reflexivity |].
  destruct (N.eqb r' r) eqn:Eeq; [apply N.eqb_eq in Eeq; contradiction | reflexivity].
Qed.

Lemma no_dup_N_to_NoDup : forall xs,
  no_dup_N xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intro H; cbn [no_dup_N] in H; [constructor |].
  apply andb_true_iff in H as [Hnin Hrest]; constructor; [| exact (IH Hrest)].
  intro Hin; apply negb_true_iff in Hnin.
  assert (Hex : n_in_list_bool x rest = true)
    by (unfold n_in_list_bool; apply existsb_exists; exists x; split; [exact Hin | apply N.eqb_refl]).
  rewrite Hex in Hnin; discriminate Hnin.
Qed.

Lemma n_in_list_In : forall x xs,
  n_in_list x xs = true -> In x xs.
Proof.
  intros x; induction xs as [| y ys IH]; intro H; cbn in H; [discriminate |].
  apply orb_true_iff in H as [Heq | Hr]; [apply N.eqb_eq in Heq; left; congruence | right; exact (IH Hr)].
Qed.

Lemma rv_cut_base_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf r,
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    ~ In r (List.map mlr_reg (ml_regs ls)) ->
    (forall r0, In r0 (mc_unspilled_preserved EA_Riscv64 ls) -> rf r0 = rf0 r0) ->
    mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0)
      (rv_val_read r (rv_cut_base_vrf ls)) (rv_read_reg r rf).
Proof.
  intros penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp.
  unfold rv_val_read, rv_cut_base_vrf.
  destruct (N.eqb r 0%N) eqn:E0.
  - cbn [mc_sym_val_agrees]; unfold rv_read_reg; rewrite E0, eval_ce_const, repr_zero_N; reflexivity.
  - destruct (N.eqb r 2%N) eqn:E2.
    + apply N.eqb_eq in E2; subst r; cbn [mc_sym_val_agrees]; unfold rv_read_reg; cbn [N.eqb]; split; assumption.
    + destruct (n_in_list r rv_preserved_non_sp_regs && negb (slot_has_saved_reg (ml_slots ls) r)) eqn:Ep.
      * apply andb_true_iff in Ep as [Hpres Hnsav].
        cbn [mc_sym_val_agrees]; unfold rv_read_reg; rewrite E0; apply Hunsp.
        unfold mc_unspilled_preserved; apply filter_In; split; [exact (n_in_list_In r rv_preserved_non_sp_regs Hpres) |].
        apply andb_true_iff; split; [| exact Hnsav].
        apply negb_true_iff; destruct (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) eqn:Ex; [| reflexivity].
        apply existsb_exists in Ex as [rb [Hrb Heqr]]; apply N.eqb_eq in Heqr; subst r.
        exfalso; apply Hnin, in_map_iff; exists rb; split; [reflexivity | exact Hrb].
      * cbn [mc_sym_val_agrees]; trivial.
Qed.

Lemma rv_fold_write_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle (f_expr : mc_loop_reg_bind -> cert_expr) rf0 rf rbs base r,
    NoDup (List.map mlr_reg rbs) ->
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    (~ In r (List.map mlr_reg rbs) ->
       mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0) (rv_val_read r base) (rv_read_reg r rf)) ->
    (forall rb, In rb rbs ->
       eval_closed_cert_expr penv foracle (f_expr rb) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))) ->
    mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0)
      (rv_val_read r (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (f_expr rb)) vrf) rbs base))
      (rv_read_reg r rf).
Proof.
  intros penv foracle f_expr rf0 rf rbs; induction rbs as [| rb rest IH];
    intros base r Hnd Hall Hbase Hfe; cbn [List.fold_left List.map] in *.
  - apply Hbase; intros [].
  - inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; try assumption; [| intros rb0 H0; apply Hfe; right; exact H0].
    intro Hninr; destruct (N.eq_dec r (mlr_reg rb)) as [-> | Hneq].
    + unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
      cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [[H1 _] _].
      rewrite rv_val_write_eq by (apply N.leb_le in H1; lia).
      exact (Hfe rb (or_introl eq_refl)).
    + rewrite rv_val_write_neq by exact Hneq; apply Hbase; intros [Heq | Hin]; [apply Hneq; symmetry; exact Heq | exact (Hninr Hin)].
Qed.

Lemma rv_cut_vrf_sp : forall ls,
  forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true ->
  rv_val_read 2%N (rv_cut_vrf ls) = MSV_StackPtr (ml_sp_off ls).
Proof.
  intros ls Hwf; unfold rv_cut_vrf.
  assert (Hgen : forall rbs base,
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    rv_val_read 2%N base = MSV_StackPtr (ml_sp_off ls) ->
    rv_val_read 2%N (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf) rbs base) =
      MSV_StackPtr (ml_sp_off ls)).
  { intros rbs; induction rbs as [| rb rest IH]; intros base Hall Hb; cbn [List.fold_left]; [exact Hb |].
    cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; [exact Hall' |].
    unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
    cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [_ Hn2]; apply negb_true_iff, N.eqb_neq in Hn2.
    rewrite rv_val_write_neq; [exact Hb | intro Heq; apply Hn2; symmetry; exact Heq]. }
  apply Hgen; [exact Hwf | reflexivity].
Qed.

Lemma rv_skel_vrf_sp : forall ls,
  forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true ->
  rv_val_read 2%N (rv_skel_vrf ls) = MSV_StackPtr (ml_sp_off ls).
Proof.
  intros ls Hwf; unfold rv_skel_vrf.
  assert (Hgen : forall rbs base,
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    rv_val_read 2%N base = MSV_StackPtr (ml_sp_off ls) ->
    rv_val_read 2%N (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf) rbs base) =
      MSV_StackPtr (ml_sp_off ls)).
  { intros rbs; induction rbs as [| rb rest IH]; intros base Hall Hb; cbn [List.fold_left]; [exact Hb |].
    cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; [exact Hall' |].
    unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
    cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [_ Hn2]; apply negb_true_iff, N.eqb_neq in Hn2.
    rewrite rv_val_write_neq; [exact Hb | intro Heq; apply Hn2; symmetry; exact Heq]. }
  apply Hgen; [exact Hwf | reflexivity].
Qed.

Lemma rv_cut_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) ->
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv foracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf))))) ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) (rv_cut_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _).
  apply rv_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (rv_cut_base_vrf_agrees penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp).
  - intros rb Hrb; destruct (Hregs rb Hrb) as [Hev Hhi].
    rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
    unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb; destruct Hwrb as (((((_ & Hw) & _) & _) & _) & _).
    unfold cut_reg_expr; apply orb_true_iff in Hw as [Hw32 | Hw64].
    + apply Pos.eqb_eq in Hw32; rewrite Hw32 in *; cbn [Pos.eqb].
      eapply combine_hi32_expr_sound; [| exact Hev | reflexivity].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hhi eq_refl); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + apply Pos.eqb_eq in Hw64; rewrite Hw64 in *; rewrite Pos.eqb_refl; rewrite (@Integers.repr_unsigned 64%positive) in Hev; exact Hev.
Qed.

Lemma rv_skel_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) ->
    (forall rb, In rb (ml_regs ls) ->
       penv (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))) ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) (rv_skel_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _).
  apply rv_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (rv_cut_base_vrf_agrees penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp).
  - intros rb Hrb; unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hregs rb Hrb); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma a64_cut_base_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf r,
    ~ In r (List.map mlr_reg (ml_regs ls)) ->
    (forall r0, In r0 (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r0 rf = a64_read_reg r0 rf0) ->
    mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0
      (a64_val_read r (a64_cut_base_vrf ls)) (a64_read_reg r rf).
Proof.
  intros penv foracle ls rf0 sp0 rf r Hnin Hunsp.
  unfold a64_val_read, a64_cut_base_vrf.
  destruct (N.leb 31%N r) eqn:E31.
  - cbn [mc_sym_val_agrees]; unfold a64_read_reg; rewrite E31, eval_ce_const, repr_zero_N; reflexivity.
  - destruct (a64_is_callee_saved r && negb (slot_has_saved_reg (ml_slots ls) r)) eqn:Ep.
    + apply andb_true_iff in Ep as [Hcs Hnsav].
      cbn [mc_sym_val_agrees]; apply Hunsp.
      unfold mc_unspilled_preserved; apply filter_In; split.
      * unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [H19 H30]; apply N.leb_le in H19; apply N.leb_le in H30.
        cbn [mc_preserved_regs]; unfold a64_callee_saved_list.
        assert (Hr_eq : r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/ r = 23%N \/ r = 24%N \/ r = 25%N \/ r = 26%N \/ r = 27%N \/ r = 28%N \/ r = 29%N \/ r = 30%N) by lia.
        repeat destruct Hr_eq as [-> | Hr_eq]; cbn; auto 15.
      * apply andb_true_iff; split; [| exact Hnsav].
        apply negb_true_iff; destruct (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) eqn:Ex; [| reflexivity].
        apply existsb_exists in Ex as [rb [Hrb Heqr]]; apply N.eqb_eq in Heqr; subst r.
        exfalso; apply Hnin, in_map_iff; exists rb; split; [reflexivity | exact Hrb].
    + cbn [mc_sym_val_agrees]; trivial.
Qed.

Lemma a64_fold_write_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle (f_expr : mc_loop_reg_bind -> cert_expr) rf0 sp0 rf rbs base r,
    NoDup (List.map mlr_reg rbs) ->
    forallb (wf_mc_loop_reg_bind EA_AArch64) rbs = true ->
    (~ In r (List.map mlr_reg rbs) ->
       mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0 (a64_val_read r base) (a64_read_reg r rf)) ->
    (forall rb, In rb rbs ->
       eval_closed_cert_expr penv foracle (f_expr rb) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))) ->
    mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0
      (a64_val_read r (List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (f_expr rb)) vrf) rbs base))
      (a64_read_reg r rf).
Proof.
  intros penv foracle f_expr rf0 sp0 rf rbs; induction rbs as [| rb rest IH];
    intros base r Hnd Hall Hbase Hfe; cbn [List.fold_left List.map] in *.
  - apply Hbase; intros [].
  - inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; try assumption; [| intros rb0 H0; apply Hfe; right; exact H0].
    intro Hninr; destruct (N.eq_dec r (mlr_reg rb)) as [-> | Hneq].
    + unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
      cbn [mc_loop_reg_valid] in Hv; apply N.leb_le in Hv.
      rewrite a64_val_write_eq by lia.
      exact (Hfe rb (or_introl eq_refl)).
    + rewrite a64_val_write_neq by exact Hneq; apply Hbase; intros [Heq | Hin]; [apply Hneq; symmetry; exact Heq | exact (Hninr Hin)].
Qed.

Lemma a64_cut_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) ->
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv foracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf))))) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_cut_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 sp0 rf Hwf Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _).
  apply a64_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (a64_cut_base_vrf_agrees penv foracle ls rf0 sp0 rf r Hnin Hunsp).
  - intros rb Hrb; destruct (Hregs rb Hrb) as [Hev Hhi].
    rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
    unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb; destruct Hwrb as (((((_ & Hw) & _) & _) & _) & _).
    unfold cut_reg_expr; apply orb_true_iff in Hw as [Hw32 | Hw64].
    + apply Pos.eqb_eq in Hw32; rewrite Hw32 in *; cbn [Pos.eqb].
      eapply combine_hi32_expr_sound; [| exact Hev | reflexivity].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hhi eq_refl); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + apply Pos.eqb_eq in Hw64; rewrite Hw64 in *; rewrite Pos.eqb_refl; rewrite (@Integers.repr_unsigned 64%positive) in Hev; exact Hev.
Qed.

Lemma a64_skel_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) ->
    (forall rb, In rb (ml_regs ls) ->
       penv (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_skel_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 sp0 rf Hwf Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _).
  apply a64_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (a64_cut_base_vrf_agrees penv foracle ls rf0 sp0 rf r Hnin Hunsp).
  - intros rb Hrb; unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hregs rb Hrb); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma mc_skel_tree_ok_extract {Pa : Params} :
  forall arch ls (penv : param_env Pa) foracle P_cut P_ret t,
    mc_skel_tree_ok arch ls t = true ->
    mc_seg_holds penv foracle P_cut P_ret t ->
    (exists sp' rr' astk',
       sp' = ml_sp_off ls /\
       (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
       (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
          mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
       P_cut sp' rr' astk') \/
    (exists ret_e, P_ret ret_e).
Proof.
  intros arch ls penv foracle P_cut P_ret t.
  induction t as [sp' rr' astk' | ret_e | cond dt IHt df IHf];
    intros Hok Hh; cbn [mc_skel_tree_ok mc_seg_holds] in *.
  - rewrite !andb_true_iff in Hok; destruct Hok as [[Hsp Hunsp] Hsav].
    apply Z.eqb_eq in Hsp.
    left; exists sp', rr', astk'; repeat split; try assumption.
    + intros r Hr; rewrite forallb_forall in Hunsp; pose proof (Hunsp r Hr) as Hr0.
      destruct (rr' r) as [| | r0 |]; try discriminate Hr0; apply N.eqb_eq in Hr0; subst r0; reflexivity.
    + intros off r Hr; rewrite forallb_forall in Hsav; pose proof (Hsav (MLS_SavedReg off r) Hr) as Hr0.
      cbn in Hr0; destruct (mc_sym_stk_load off MS_8 false astk') as [sv |] eqn:Eld;
        [destruct sv as [| | r0 |] |]; try discriminate Hr0;
        apply N.eqb_eq in Hr0; subst r0; reflexivity.
  - right; exists ret_e; exact Hh.
  - apply andb_true_iff in Hok as [Ht Hf]; destruct Hh as [b [_ Hsub]].
    destruct b; [exact (IHt Ht Hsub) | exact (IHf Hf Hsub)].
Qed.

Fixpoint overlay_penv {Pa : Params} (binds : list (string * @dvalue Pa)) (base : param_env Pa)
  : param_env Pa :=
  fun nm =>
    match binds with
    | [] => base nm
    | (x, dv) :: rest => if String.eqb nm x then Some dv else overlay_penv rest base nm
    end.

Lemma overlay_penv_lookup_in {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) x dv,
    NoDup (List.map fst binds) ->
    In (x, dv) binds ->
    overlay_penv binds base x = Some dv.
Proof.
  induction binds as [| [y v] rest IH]; intros base x dv Hnd Hin; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [overlay_penv List.map] in *.
  destruct Hin as [Heq | Hinr].
  - inversion Heq; subst; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb x y) eqn:Exy; [| exact (IH base x dv Hnd' Hinr)].
    apply String.eqb_eq in Exy; subst y; exfalso; apply Hnin, in_map_iff; exists (x, dv); split; [reflexivity | exact Hinr].
Qed.

Lemma overlay_penv_not_in {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    ~ In nm (List.map fst binds) ->
    overlay_penv binds base nm = base nm.
Proof.
  induction binds as [| [y v] rest IH]; intros base nm Hnin; cbn [overlay_penv List.map] in *; [reflexivity |].
  destruct (String.eqb nm y) eqn:Eny.
  - apply String.eqb_eq in Eny; subst y; exfalso; apply Hnin; left; reflexivity.
  - apply IH; intro H; apply Hnin; right; exact H.
Qed.

Lemma overlay_penv_non_bang {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    (forall y, In y (List.map fst binds) -> mc_starts_with_bang y = true) ->
    mc_starts_with_bang nm = false ->
    overlay_penv binds base nm = base nm.
Proof.
  intros binds base nm Hbang Hnb; apply overlay_penv_not_in.
  intro Hin; rewrite (Hbang nm Hin) in Hnb; discriminate Hnb.
Qed.

Definition mc_cut_obl_inv_holds {Pa : Params}
  (ls : mc_loop_spec) (penv : param_env Pa) (foracle : freeze_oracle) : Prop :=
  match ml_inv ls with
  | None => True
  | Some inv_e =>
      eval_closed_cert_expr penv foracle inv_e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
  end.

Definition expr_cut_vars_ok (ls : mc_loop_spec) (e : cert_expr) : Prop :=
  forall nm w, In (nm, w) (collect_free_vars [] e) -> mc_starts_with_bang nm = false \/ exists k, nm = mc_cut_var_name k.

Lemma expr_has_var_false_not_in : forall nm e,
  expr_has_var nm e = false -> forall w, ~ In (nm, w) (collect_free_vars [] e).
Proof.
  intros nm e Hfv w Hin; unfold expr_has_var in Hfv.
  assert (Htru : existsb (fun '(x, _) => String.eqb x nm) (collect_free_vars [] e) = true)
    by (apply existsb_exists; exists (nm, w); split; [exact Hin | apply String.eqb_refl]).
  rewrite Htru in Hfv; discriminate Hfv.
Qed.

Lemma eval_cert_expr_penv_eq_if_vars {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) -> penv1 nm = penv2 nm) ->
    eval_closed_cert_expr penv1 foracle e = eval_closed_cert_expr penv2 foracle e.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hag; unfold eval_closed_cert_expr in *;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *;
    try reflexivity; try discriminate Hlf.
  - rewrite (Hag nm w (or_introl eq_refl)); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr];
      rewrite (IHl Hl (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHr Hr (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror H)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr];
      rewrite (IHl Hl (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHr Hr (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror H)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hc Ht] Hf];
      rewrite (IHc Hc (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHt Ht (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H)))))),
              (IHf Hf (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror H)))))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
Qed.

Lemma check_widths_match_spec : forall ws phis,
  check_widths_match ws phis = true ->
  Forall2 (fun w '(wp, _) => w = wp) ws phis.
Proof.
  induction ws as [| w rw IH]; intros [| [wp ce] rp] H; cbn in H; try discriminate H; [constructor |].
  apply andb_true_iff in H as [Hw Hr]; apply Pos.eqb_eq in Hw; constructor; [exact Hw | exact (IH rp Hr)].
Qed.

Definition is_ptol_for_spec (ls : mc_loop_spec) (hdr_ws : list positive) (idx : nat) (w : positive) : bool :=
  match nth_error hdr_ws idx with
  | Some w' => Pos.eqb w w' && cut_var_ptol ls idx w
  | None => false
  end.

Lemma expr_is_ptol_var_at_spec : forall ls hdr_ws idx e,
  expr_is_ptol_var_at ls idx hdr_ws e = true ->
  exists k w,
    (idx <= k)%nat /\
    nth_error hdr_ws (k - idx)%nat = Some w /\
    e = CE_Var (mc_cut_var_name k) w /\
    cut_var_ptol ls k w = true.
Proof.
  intros ls hdr_ws; induction hdr_ws as [| w_h rest IH]; intros idx e H; cbn in H; [discriminate H |].
  apply orb_true_iff in H as [Hhere | Hlater].
  - apply andb_true_iff in Hhere as [He Hpt].
    destruct e as [| | nm bw | | | | | |]; try discriminate He; cbn in He; apply andb_true_iff in He as [Hnm Hw].
    apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw; rewrite Hnm, <- Hw.
    exists idx, w_h; rewrite Nat.sub_diag; repeat split; try lia; try reflexivity; exact Hpt.
  - destruct (IH (S idx) e Hlater) as (k & wk & Hle & Hnth & He & Hpt).
    exists k, wk; repeat split; try lia; try assumption.
    replace (k - idx)%nat with (S (k - S idx))%nat by lia; exact Hnth.
Qed.

Lemma expr_not_ptol_var_avoids_ptol : forall ls hdr_ws e k w,
  expr_is_ptol_var ls hdr_ws e = false ->
  nth_error hdr_ws k = Some w ->
  cut_var_ptol ls k w = true ->
  reg_slot_uses_cut_var_ok k w e = true ->
  forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] e).
Proof.
  intros ls hdr_ws e k w Hno Hnth Hpt Hok w0 Hin.
  unfold reg_slot_uses_cut_var_ok in Hok; apply orb_true_iff in Hok as [Hneg | His].
  - apply negb_true_iff in Hneg; exact (expr_has_var_false_not_in _ _ Hneg w0 Hin).
  - destruct e as [| | nm bw | | | | | |]; try discriminate His; cbn in His; apply andb_true_iff in His as [Hnm Hw].
    apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw; subst nm bw.
    assert (Hyes : expr_is_ptol_var ls hdr_ws (CE_Var (mc_cut_var_name k) w) = true).
    { unfold expr_is_ptol_var; clear -Hnth Hpt.
      assert (Hgen : forall idx xs, nth_error xs (k - idx)%nat = Some w -> (idx <= k)%nat ->
        expr_is_ptol_var_at ls idx xs (CE_Var (mc_cut_var_name k) w) = true).
      { intros idx xs; revert idx; induction xs as [| x rx IH]; intros idx Hn Hle; cbn in *.
        - destruct (k - idx)%nat; discriminate Hn.
        - destruct (Nat.eq_dec idx k) as [-> | Hneq].
          + rewrite Nat.sub_diag in Hn; inversion Hn; subst x.
            rewrite String.eqb_refl, Pos.eqb_refl, Hpt; reflexivity.
          + replace (k - idx)%nat with (S (k - S idx))%nat in Hn by lia.
            rewrite (IH (S idx) Hn ltac:(lia)), orb_true_r; reflexivity. }
      exact (Hgen 0%nat hdr_ws ltac:(rewrite Nat.sub_0_r; exact Hnth) ltac:(lia)). }
    rewrite Hyes in Hno; discriminate Hno.
Qed.

Lemma build_phi_subst_in : forall idx phis nm w ce,
  In (nm, w, ce) (build_phi_subst idx phis) ->
  exists j, nm = mc_cut_var_name (idx + j) /\ nth_error phis j = Some (w, ce).
Proof.
  intros idx phis; revert idx; induction phis as [| [w0 ce0] rest IH];
    intros idx nm w ce Hin; cbn [build_phi_subst] in Hin; [contradiction |].
  destruct Hin as [Heq | Hinr].
  - inversion Heq; subst; exists 0%nat; rewrite Nat.add_0_r; split; reflexivity.
  - destruct (IH (S idx) nm w ce Hinr) as [j [Hnm Hnth]].
    exists (S j); split; [rewrite Hnm; f_equal; lia | exact Hnth].
Qed.

Lemma build_phi_subst_nodup : forall idx phis,
  NoDup (List.map (fun '(x, _, _) => x) (build_phi_subst idx phis)).
Proof.
  intros idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intro idx; cbn [build_phi_subst List.map]; constructor; [| exact (IH (S idx))].
  intro Hin; apply in_map_iff in Hin as [[[nm w0] ce0] [Hnm Hrest]].
  subst nm; destruct (build_phi_subst_in _ _ _ _ _ Hrest) as [j [Heq _]].
  apply mc_cut_var_name_inj in Heq; lia.
Qed.

Lemma lookup_phi_subst_some : forall idx phis j w ce,
  nth_error phis j = Some (w, ce) ->
  lookup_subst (mc_cut_var_name (idx + j)) (build_phi_subst idx phis) = Some (w, ce).
Proof.
  intros idx phis; revert idx; induction phis as [| [w0 ce0] rest IH];
    intros idx j w ce Hnth; cbn [build_phi_subst lookup_subst]; [destruct j; discriminate Hnth |].
  destruct j as [| j']; cbn in Hnth.
  - inversion Hnth; subst w0 ce0; rewrite Nat.add_0_r, String.eqb_refl; reflexivity.
  - destruct (String.eqb (mc_cut_var_name (idx + S j')) (mc_cut_var_name idx)) eqn:Eeq.
    + apply String.eqb_eq, mc_cut_var_name_inj in Eeq; lia.
    + replace (idx + S j')%nat with (S idx + j')%nat by lia; exact (IH (S idx) j' w ce Hnth).
Qed.

Lemma lookup_phi_subst_none_non_bang : forall idx phis nm,
  mc_starts_with_bang nm = false ->
  lookup_subst nm (build_phi_subst idx phis) = None.
Proof.
  intros idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intros idx nm Hnb; cbn [build_phi_subst lookup_subst]; [reflexivity |].
  destruct (String.eqb nm (mc_cut_var_name idx)) eqn:Eeq.
  - apply String.eqb_eq in Eeq; subst nm; cbn in Hnb; discriminate Hnb.
  - exact (IH (S idx) nm Hnb).
Qed.

Lemma build_phi_subst_wf : forall allowed_ir idx phis,
  Forall (fun '(wp, ce) =>
    wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
    is_let_free_expr ce = true /\ ub_free_expr ce = true /\ incl (collect_free_vars [] ce) allowed_ir) phis ->
  Forall (subst_entry_wf allowed_ir) (build_phi_subst idx phis).
Proof.
  intros allowed_ir idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intros idx Hfa; cbn [build_phi_subst]; [constructor |].
  inversion Hfa as [| ? ? Hw Hrest]; subst; constructor; [exact Hw | exact (IH (S idx) Hrest)].
Qed.

Lemma imposs_obl_absurd {Pa : Params} :
  forall (penv : param_env Pa) foracle opt_inv (is_body : bool) (path : list (bool * cert_expr)),
    (is_body = true -> match opt_inv with None => True | Some inv_e => eval_closed_cert_expr penv foracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))) end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv foracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv foracle opt_inv is_body) (imposs_obl is_body path) ->
    False.
Proof.
  intros penv foracle opt_inv is_body path Hinv Hpath Hfa.
  inversion Hfa as [| ? ? H0 _]; subst.
  pose proof (H0 eq_refl Hinv Hpath) as Href.
  cbn [eval_closed_cert_expr eval_cert_expr refine_eou_dvalue] in Href.
  rewrite repr_one_N, repr_zero_N in Href.
  destruct Href as [Hbad | Hbad]; [inversion Hbad |].
  pose proof (f_equal dvalue_int_unsigned Hbad) as Hu.
  cbn in Hu; rewrite (@Integers.unsigned_one 1%positive), (@Integers.unsigned_zero 1%positive) in Hu; discriminate Hu.
Qed.

(** Leaf-pair soundness for [collect_mc_ir_obls] against generic [ir_seg_eval_spec]
    and [mc_seg_holds]. *)
Theorem collect_mc_ir_obls_sound {Pa : Params} :
  forall arch ls ret_w hdr_ws allowed_ir (is_body : bool)
         (penv_ir penv_mc : param_env Pa)
         bmap hdr_id hdr_phis wr_keep env0 bid_from cur_bid t_ir
         P_cut P_ret t_mc opt_inv (path : list (bool * cert_expr)),
    extract_hdr_phi_widths hdr_phis = hdr_ws ->
    ir_seg_wf allowed_ir hdr_ws t_ir ->
    ir_seg_freeze_free t_ir = true ->
    (forall nm w, In (nm, w) allowed_ir ->
       exists d1 d2 : @dvalue Pa,
         penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv_ir env0 bid_from cur_bid t_ir ->
    mc_seg_holds penv_mc dummy_freeze_oracle P_cut P_ret t_mc ->
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv_mc dummy_freeze_oracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body)
      (collect_mc_ir_obls arch ls ret_w hdr_ws is_body path t_ir t_mc) ->
    (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
    (exists env_out dv_ir ret_mc dv_mc,
       pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
       P_ret ret_mc /\
       eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
       dvalue_refines dv_ir dv_mc) \/
    (exists env_c bid_c b_hdr dvs lmap_cut phis_ir sp' rr' astk',
       ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
        pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
          env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
       RM.find hdr_id bmap = Some b_hdr /\
       In lmap_cut (collect_entry_cut_lmaps t_ir) /\
       lmap_matches_env penv_ir lmap_cut env_c /\
       (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
       pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
       Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
       Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir /\
       Forall (fun '(wp, ce) =>
         wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
         is_let_free_expr ce = true /\ ub_free_expr ce = true /\
         expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir /\
       Forall2 (fun '(wp, ce) '(_, dv) =>
         eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
         wf_scalar_dvalue wp dv) phis_ir dvs /\
       sp' = ml_sp_off ls /\
       P_cut sp' rr' astk' /\
       (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
       (forall k w ce,
          nth_error phis_ir k = Some (w, ce) ->
          cut_var_ptol ls k w = false ->
          exists vi,
            eval_closed_cert_expr penv_mc dummy_freeze_oracle ce =
            raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
       (forall rb, In rb (ml_regs ls) ->
          exists e_mc64,
            rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
              (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) /\
       (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
          mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
       (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) ->
          exists e_mc64,
            mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
              (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws e_s = false ->
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) /\
       match ml_inv ls with
       | None => True
       | Some inv_e =>
           mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
             (MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
       end).
Proof.
  intros arch ls ret_w hdr_ws allowed_ir is_body penv_ir penv_mc bmap hdr_id hdr_phis wr_keep.
  intros env0 bid_from cur_bid t_ir P_cut P_ret t_mc opt_inv path Hhdr Hwf_ir Hfrz_ir Href.
  revert env0 bid_from cur_bid path Hwf_ir Hfrz_ir.
  induction t_ir as [lmap_cut phis_ir | rw ret_ir | | cond dt_ir IHt df_ir IHf];
    intros env0 bid_from cur_bid path Hwf_ir Hfrz_ir Hir Hmc Hinv Hpath Hobls.
  - (* IST_Cut *)
    destruct Hwf_ir as [_ Hwf_phis]; cbn [ir_seg_freeze_free ir_seg_exprs_freeze_free_cut] in Hfrz_ir.
    assert (Hphis_wf : Forall (fun '(wp, ce) =>
      wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
      is_let_free_expr ce = true /\ ub_free_expr ce = true /\
      expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir).
    { clear -Hwf_phis Hfrz_ir.
      induction Hwf_phis as [| w [wp ce] rw rp (_ & Hwt & Hbw & Hlf & Hub & Hfv) _ IH];
        cbn [forallb] in *; [constructor |].
      apply andb_true_iff in Hfrz_ir as [Hnfrz Hfrz_r]; apply negb_true_iff in Hnfrz.
      constructor; [repeat split; assumption | exact (IH Hfrz_r)]. }
    clear Hhdr; induction t_mc as [sp' rr' astk' | ret_mc | cond_mc dt_mc IHtm df_mc IHfm] in path, Hmc, Hpath, Hobls |- *;
      cbn [collect_mc_ir_obls mc_seg_holds] in Hobls, Hmc.
    + destruct (Z.eqb sp' (ml_sp_off ls) &&
                forallb (fun r => match rr' r with MSV_SavedReg r0 => N.eqb r0 r | _ => false end) (mc_unspilled_preserved arch ls) &&
                check_widths_match hdr_ws phis_ir) eqn:Epres; cbn [negb] in Hobls;
        [| exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls)].
      destruct (collect_reg_cut_obls ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) rr' (ml_regs ls)) as [robls |] eqn:Ero;
        [| exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls)].
      destruct (collect_slot_cut_obls ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) astk' (ml_slots ls)) as [sobls |] eqn:Eso;
        [| exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls)].
      destruct Hir as [Hub | (env_c & bid_c & b_hdr & dvs & Htau & Ebh & Hlm & Hkp & Hph & Hids & Hstp)]; [left; exact Hub |].
      right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut, phis_ir, sp', rr', astk'.
      rewrite !andb_true_iff in Epres; destruct Epres as [[Hsp Hunsp] Hwm].
      apply Z.eqb_eq in Hsp.
      rewrite !Forall_app in Hobls; destruct Hobls as [Hob_phi [Hob_reg [Hob_slot Hob_inv]]].
      cbn [collect_entry_cut_lmaps].
      repeat split; try assumption.
      * left; reflexivity.
      * exact (check_widths_match_spec _ _ Hwm).
      * intros r Hr; rewrite forallb_forall in Hunsp; pose proof (Hunsp r Hr) as Hrr.
        destruct (rr' r) as [| | r0 |]; try discriminate Hrr; apply N.eqb_eq in Hrr; subst r0; reflexivity.
      * intros k w ce Hnth Hpt.
        clear -Hob_phi Hnth Hpt Hinv Hpath.
        assert (Hgen : forall idx phis,
          nth_error phis (k - idx)%nat = Some (w, ce) ->
          (idx <= k)%nat ->
          Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) (collect_phi_def_obls ls is_body path idx phis) ->
          cut_var_ptol ls k w = false ->
          exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))).
        { intros idx phis; revert idx; induction phis as [| [w0 ce0] rp IHp]; intros idx Hn Hle Hfa Hpt0;
            cbn in Hfa; [destruct (k - idx)%nat; discriminate Hn |].
          rewrite Forall_app in Hfa; destruct Hfa as [H0 Hrest].
          destruct (Nat.eq_dec idx k) as [-> | Hneq].
          - rewrite Nat.sub_diag in Hn; inversion Hn; subst w0 ce0.
            rewrite Hpt0 in H0; inversion H0 as [| ? ? Hd _]; exact (Hd eq_refl Hinv Hpath).
          - replace (k - idx)%nat with (S (k - S idx))%nat in Hn by lia; exact (IHp (S idx) Hn ltac:(lia) Hrest Hpt0). }
        exact (Hgen 0%nat phis_ir ltac:(rewrite Nat.sub_0_r; exact Hnth) ltac:(lia) Hob_phi Hpt).
      * intros rb Hrb.
        clear -Ero Hob_reg Hrb; revert Hrb robls Hob_reg Ero.
        induction (ml_regs ls) as [| rb0 rest IHr]; intros Hrb robls Hob_reg Ero; cbn in *; [contradiction |].
        destruct (rr' (mlr_reg rb0)) as [| e_mc64 | |] eqn:Err; try discriminate Ero.
        destruct (collect_reg_cut_obls ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) rr' rest) as [or_r |] eqn:Erest;
          [| discriminate Ero]; inversion Ero; subst robls; clear Ero.
        rewrite !Forall_app in Hob_reg; destruct Hob_reg as [Hdef Hcons].
        inversion Hcons as [| ? ? Ho_ref Hrest]; subst.
        destruct Hrb as [<- | Hinr].
        -- exists e_mc64; split; [exact Err | split; [exact Ho_ref |]].
           intro Hno; rewrite Hno in Hdef; inversion Hdef as [| ? ? Ho_def _]; exact Ho_def.
        -- exact (IHr Hinr or_r Hrest eq_refl).
      * intros off r Hs; clear -Eso Hs; revert Hs sobls Eso.
        induction (ml_slots ls) as [| [o s e | o r0] rest IHs]; intros Hs sobls Eso; cbn in *; [contradiction | |].
        -- destruct (mc_sym_stk_load o s false astk') as [[| em | |] |]; try discriminate Eso.
           destruct (collect_slot_cut_obls ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) astk' rest) as [os_r |] eqn:Erest;
             [| discriminate Eso]; inversion Eso; destruct Hs as [Hc | Hr]; [discriminate Hc | exact (IHs Hr os_r eq_refl)].
        -- destruct (mc_sym_stk_load o MS_8 false astk') as [[| | r1 |] |] eqn:Eld; try discriminate Eso.
           destruct (N.eqb r1 r0) eqn:Er; [| discriminate Eso]; apply N.eqb_eq in Er; subst r1.
           destruct Hs as [Heq | Hr]; [inversion Heq; subst; exact Eld | exact (IHs Hr sobls Eso)].
      * intros off sz e_s Hs; clear -Eso Hob_slot Hs; revert Hs sobls Hob_slot Eso.
        induction (ml_slots ls) as [| [o s e | o r0] rest IHs]; intros Hs sobls Hob_slot Eso; cbn in *; [contradiction | |].
        -- destruct (mc_sym_stk_load o s false astk') as [[| em | |] |] eqn:Eld; try discriminate Eso.
           destruct (collect_slot_cut_obls ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) astk' rest) as [os_r |] eqn:Erest;
             [| discriminate Eso]; inversion Eso; subst sobls; clear Eso.
           rewrite !Forall_app in Hob_slot; destruct Hob_slot as [Hdef Hcons].
           inversion Hcons as [| ? ? Ho_ref Hrest]; subst.
           destruct Hs as [Heq | Hr].
           ++ inversion Heq; subst; exists em; split; [exact Eld | split; [exact Ho_ref |]].
              intro Hno; rewrite Hno in Hdef; inversion Hdef as [| ? ? Ho_def _]; exact Ho_def.
           ++ exact (IHs Hr os_r Hrest eq_refl).
        -- destruct (mc_sym_stk_load o MS_8 false astk') as [[| | r1 |] |]; try discriminate Eso.
           destruct (N.eqb r1 r0); [| discriminate Eso].
           destruct Hs as [Hc | Hr]; [discriminate Hc | exact (IHs Hr sobls Hob_slot Eso)].
      * destruct (ml_inv ls); [inversion Hob_inv; assumption | exact I].
    + exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls).
    + rewrite Forall_app in Hobls; destruct Hobls as [Hbt Hbf].
      destruct Hmc as [b [Hbc Hsub]].
      assert (Hpath' : forall (b0 : bool) (c0 : cert_expr), In (b0, c0) (path ++ [(b, cond_mc)]) ->
        eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 Hin; apply in_app_iff in Hin as [Hin | [Heq | []]]; [exact (Hpath b0 c0 Hin) | inversion Heq; subst; exact Hbc]. }
      assert (Hsub_mc :
        (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
        (exists env_out dv_ir ret_mc dv_mc,
           pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
           P_ret ret_mc /\
           eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
           dvalue_refines dv_ir dv_mc) \/
        (exists env_c bid_c b_hdr dvs lmap_cut0 phis_ir0 sp' rr' astk',
           ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
            pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
              env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
           RM.find hdr_id bmap = Some b_hdr /\
           In lmap_cut0 (collect_entry_cut_lmaps (IST_Cut lmap_cut phis_ir)) /\
           lmap_matches_env penv_ir lmap_cut0 env_c /\
           (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
           pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
           Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
           Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir0 /\
           Forall (fun '(wp, ce) =>
             wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
             is_let_free_expr ce = true /\ ub_free_expr ce = true /\
             expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir0 /\
           Forall2 (fun '(wp, ce) '(_, dv) =>
             eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
             wf_scalar_dvalue wp dv) phis_ir0 dvs /\
           sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
           (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
           (forall k w ce, nth_error phis_ir0 k = Some (w, ce) -> cut_var_ptol ls k w = false ->
              exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
           (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
              (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond_mc)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb))))) /\
           (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
           (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
              (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond_mc)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s)))) /\
           match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) inv_e)) end)).
      { destruct b; [exact (IHtm (path ++ [(true, cond_mc)]) Hsub Hpath' Hbt)
                   | exact (IHfm (path ++ [(false, cond_mc)]) Hsub Hpath' Hbf)]. }
      destruct Hsub_mc as [Hub_m | [Hret_m | (env_c & bid_c & b_hdr & dvs & lmap_cut0 & phis_ir0 & sp' & rr' & astk' & Htau_m & Ebh_m & Hin_m & Hlm_m & Hkp_m & Hstp_m & Hids_m & Hws_m & Hpwf_m & Hph_m & Hsp_m & Hpc_m & Hunsp_m & Hphi_m & Hregs_m & Hsav_m & Hslts_m & Hmi_m)]];
        [left; exact Hub_m | right; left; exact Hret_m |].
      right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut0, phis_ir0, sp', rr', astk'.
      repeat split; try assumption.
      * intros rb Hrb; destruct (Hregs_m rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d); exists e_mc64; split; [exact Err | split].
        -- intros Hbm Hinv0 Hpath0; exact (Ho_r Hbm Hinv0 Hpath').
        -- intros Hnpt Hbm Hinv0 Hpath0; exact (Ho_d Hnpt Hbm Hinv0 Hpath').
      * intros off sz e_s Hsl; destruct (Hslts_m off sz e_s Hsl) as (e_mc64 & Eld & Ho_r & Ho_d); exists e_mc64; split; [exact Eld | split].
        -- intros Hbm Hinv0 Hpath0; exact (Ho_r Hbm Hinv0 Hpath').
        -- intros Hnpt Hbm Hinv0 Hpath0; exact (Ho_d Hnpt Hbm Hinv0 Hpath').
      * destruct (ml_inv ls); [| exact I]; intros Hbm Hinv0 Hpath0; exact (Hmi_m Hbm Hinv0 Hpath').
  - (* IST_Ret *)
    destruct Hwf_ir as (_ & Hsup & Hwt_r & Hbw_r & Hlf_r & Hub_r & Hfv_r).
    cbn [ir_seg_freeze_free] in Hfrz_ir; apply negb_true_iff in Hfrz_ir.
    induction t_mc as [sp' rr' astk' | ret_mc | cond_mc dt_mc IHtm df_mc IHfm] in path, Hmc, Hpath, Hobls |- *;
      cbn [collect_mc_ir_obls mc_seg_holds] in Hobls, Hmc.
    + exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls).
    + destruct (Pos.eqb rw ret_w) eqn:Erw;
        [| exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath Hobls)].
      destruct Hir as [Hub | (env_out & dv_ir & Hst & Hev_ir)]; [left; exact Hub |].
      inversion Hobls as [| ? ? Ho_r _]; subst; clear Hobls.
      pose proof (Ho_r eq_refl Hinv Hpath) as Href_e.
      destruct (eval_cert_expr_refine_mono penv_ir penv_mc dummy_freeze_oracle ret_ir Hwt_r Hlf_r Hub_r Hfrz_ir
                  (fun x wx Hx => Href x wx (Hfv_r (x, wx) Hx)))
        as (v1 & v2 & Ev1 & Ev2 & _ & _ & R12).
      rewrite Hev_ir in Ev1; inversion Ev1; subst v1.
      cbn [refine_eou_dvalue] in Href_e; rewrite Ev2 in Href_e; destruct (eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc) as [| | | dv_mc] eqn:Evmc;
        try contradiction.
      right; left; exists env_out, dv_ir, ret_mc, dv_mc; repeat split; try assumption.
      exact (dvalue_refines_trans _ _ _ R12 Href_e).
    + rewrite Forall_app in Hobls; destruct Hobls as [Hbt Hbf].
      destruct Hmc as [b [Hbc Hsub]].
      assert (Hpath' : forall (b0 : bool) (c0 : cert_expr), In (b0, c0) (path ++ [(b, cond_mc)]) ->
        eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 Hin; apply in_app_iff in Hin as [Hin | [Heq | []]]; [exact (Hpath b0 c0 Hin) | inversion Heq; subst; exact Hbc]. }
      assert (Hsub_mc :
        (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
        (exists env_out dv_ir ret_mc dv_mc,
           pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
           P_ret ret_mc /\
           eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
           dvalue_refines dv_ir dv_mc) \/
        (exists env_c bid_c b_hdr dvs lmap_cut0 phis_ir0 sp' rr' astk',
           ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
            pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
              env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
           RM.find hdr_id bmap = Some b_hdr /\
           In lmap_cut0 (collect_entry_cut_lmaps (IST_Ret rw ret_ir)) /\
           lmap_matches_env penv_ir lmap_cut0 env_c /\
           (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
           pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
           Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
           Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir0 /\
           Forall (fun '(wp, ce) =>
             wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
             is_let_free_expr ce = true /\ ub_free_expr ce = true /\
             expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir0 /\
           Forall2 (fun '(wp, ce) '(_, dv) =>
             eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
             wf_scalar_dvalue wp dv) phis_ir0 dvs /\
           sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
           (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
           (forall k w ce, nth_error phis_ir0 k = Some (w, ce) -> cut_var_ptol ls k w = false ->
              exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
           (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
              (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond_mc)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb))))) /\
           (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
           (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
              (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond_mc)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s)))) /\
           match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond_mc)]) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) inv_e)) end)).
      { destruct b; [exact (IHtm (path ++ [(true, cond_mc)]) Hsub Hpath' Hbt)
                   | exact (IHfm (path ++ [(false, cond_mc)]) Hsub Hpath' Hbf)]. }
      destruct Hsub_mc as [Hub_m | [Hret_m | (? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & Hin_m & _)]];
        [left; exact Hub_m | right; left; exact Hret_m | exfalso; exact Hin_m].
  - (* IST_UB *)
    left; exact Hir.
  - (* IST_Branch *)
    cbn [collect_mc_ir_obls] in Hobls; rewrite Forall_app in Hobls; destruct Hobls as [Hob_t Hob_f].
    destruct Hwf_ir as [Hlms (Hwt_c & Hbw_c & Hlf_c & Hub_c & Hfv_c & Hwf_t & Hwf_f)].
    assert (Hlms_t : forall lm, In lm (collect_entry_cut_lmaps dt_ir) -> wf_pure_lmap allowed_ir lm)
      by (intros lm Hin; exact (Hlms lm (in_or_app _ _ _ (or_introl Hin)))).
    assert (Hlms_f : forall lm, In lm (collect_entry_cut_lmaps df_ir) -> wf_pure_lmap allowed_ir lm)
      by (intros lm Hin; exact (Hlms lm (in_or_app _ _ _ (or_intror Hin)))).
    cbn [ir_seg_freeze_free] in Hfrz_ir; rewrite !andb_true_iff in Hfrz_ir; destruct Hfrz_ir as [[Hnfrz_c Hnf_t] Hnf_f].
    apply negb_true_iff in Hnfrz_c.
    cbn [ir_seg_eval_spec] in Hir; destruct Hir as [Hub | (env_mid & bid_step & br_t & br_f & b & Htau & Hev_c & Hk2 & Hsub)];
      [left; exact Hub |].
    destruct (eval_cert_expr_refine_mono penv_ir penv_mc dummy_freeze_oracle cond Hwt_c Hlf_c Hub_c Hnfrz_c
                (fun x wx Hx => Href x wx (Hfv_c (x, wx) Hx)))
      as (vc1 & vc2 & Evc1 & Evc2 & _ & _ & Rc).
    rewrite Hev_c in Evc1; inversion Evc1; subst vc1.
    assert (Hvc2 : vc2 = DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))).
    { destruct Rc as [Hbad | <-]; [discriminate Hbad | reflexivity]. }
    subst vc2.
    assert (Hpath' : forall b0 c0, In (b0, c0) (path ++ [(b, cond)]) ->
      eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { intros b0 c0 Hin; apply in_app_iff in Hin as [Hin | [Heq | []]]; [exact (Hpath b0 c0 Hin) | inversion Heq; subst; exact Evc2]. }
    assert (Hsub_res :
      (forall sigma, cfg_steps_to_ub sigma env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f))) \/
      (exists env_out dv_ir ret_mc dv_mc,
         pure_cfg_steps env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f)) env_out dv_ir /\
         P_ret ret_mc /\
         eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
         dvalue_refines dv_ir dv_mc) \/
      (exists env_c bid_c b_hdr dvs lmap_cut phis_ir sp' rr' astk',
         ((env_c = env_mid /\ bid_c = bid_step /\ (if b then br_t else br_f) = hdr_id) \/
          pure_cfg_steps_to_tau env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f))
            env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
         RM.find hdr_id bmap = Some b_hdr /\
         In lmap_cut (collect_entry_cut_lmaps (if b then dt_ir else df_ir)) /\
         lmap_matches_env penv_ir lmap_cut env_c /\
         (forall r, In r wr_keep -> RM.find r env_c = RM.find r env_mid) /\
         pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
         Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
         Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir /\
         Forall (fun '(wp, ce) =>
           wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
           is_let_free_expr ce = true /\ ub_free_expr ce = true /\
           expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir /\
         Forall2 (fun '(wp, ce) '(_, dv) =>
           eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
           wf_scalar_dvalue wp dv) phis_ir dvs /\
         sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
         (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
         (forall k w ce, nth_error phis_ir k = Some (w, ce) -> cut_var_ptol ls k w = false ->
            exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
         (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond)]) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) /\
         (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
         (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body (path ++ [(b, cond)]) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) /\
         match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body (path ++ [(b, cond)]) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e)) end)).
    { destruct b; [exact (IHt _ _ _ (path ++ [(true, cond)]) (conj Hlms_t Hwf_t) Hnf_t Hsub Hmc Hinv Hpath' Hob_t)
                 | exact (IHf _ _ _ (path ++ [(false, cond)]) (conj Hlms_f Hwf_f) Hnf_f Hsub Hmc Hinv Hpath' Hob_f)]. }
    destruct Hsub_res as [Hub_sub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & Hpr & Hevmc & Href_d)
                                  | (env_c & bid_c & b_hdr & dvs & lmap_cut & phis_ir & sp' & rr' & astk' &
                                     Htau2 & Ebh & Hin_lm & Hlm_m & Hkp2 & Hstp & Hids & Hws & Hpwf & Hph & Hsp & Hpc & Hunsp & Hphi_d & Hregs & Hsav & Hslts & Hmi)]].
    + left; intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hub_sub sigma)).
    + right; left; exists env_out, dv_ir, ret_mc, dv_mc; repeat split; try assumption.
      exact (pure_cfg_steps_to_tau_then_ret _ _ _ _ _ _ Htau Hst).
    + right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut, phis_ir, sp', rr', astk'.
      cbn [collect_entry_cut_lmaps].
      repeat split; try assumption.
      * right; destruct Htau2 as [[-> [-> Eeq]] | Htau2]; [rewrite <- Eeq; exact Htau | exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau Htau2)].
      * apply in_app_iff; destruct b; [left | right]; exact Hin_lm.
      * intros r Hr; rewrite (Hkp2 r Hr), (Hk2 r Hr); reflexivity.
      * intros rb Hrb; destruct (Hregs rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d); exists e_mc64; split; [exact Err | split].
        -- intros Hbm Hinv0 Hpath0; apply Ho_r; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
        -- intros Hnpt Hbm Hinv0 Hpath0; apply Ho_d; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
      * intros off sz e_s Hsl; destruct (Hslts off sz e_s Hsl) as (e_mc64 & Eld & Ho_r & Ho_d); exists e_mc64; split; [exact Eld | split].
        -- intros Hbm Hinv0 Hpath0; apply Ho_r; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
        -- intros Hnpt Hbm Hinv0 Hpath0; apply Ho_d; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
      * destruct (ml_inv ls); [| exact I]; intros Hbm Hinv0 Hpath0; apply Hmi; try assumption.
Qed.

Lemma reify_ir_seg_req_step_bid_from_irrel :
  forall fuel bmap hdr_id hdr_phis visited bid1 bid2 cur_bid lmap,
    reify_ir_seg fuel bmap hdr_id hdr_phis true visited bid1 cur_bid lmap =
    reify_ir_seg fuel bmap hdr_id hdr_phis true visited bid2 cur_bid lmap.
Proof. destruct fuel; reflexivity. Qed.

(** ** 5. End-to-End Loop Validators & CNF Emitters ([validate_mc_loop_rv64], [validate_mc_loop_a64]) *)

Record mc_loop_ir_prep : Type := mk_mc_loop_ir_prep {
  mlip_hdr_id : block_id;
  mlip_b_hdr : block dtyp;
  mlip_hdr_phis : list (raw_id * positive);
  mlip_lmap_base : rmap (positive * cert_expr);
  mlip_wr_entry : list raw_id;
  mlip_wr_body : list raw_id;
  mlip_t_ir_entry : ir_seg_tree;
  mlip_t_ir_body : ir_seg_tree
}.

Definition check_ls_exprs_vars (allowed : list (string * positive)) (ls : mc_loop_spec) : bool :=
  forallb (fun rb => AlgRules.vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed) (ml_regs ls) &&
  forallb (fun sb => match sb with MLS_Expr _ _ e => AlgRules.vars_subset_b (collect_free_vars [] e) allowed | MLS_SavedReg _ _ => true end) (ml_slots ls) &&
  match ml_inv ls with
  | None => true
  | Some inv => AlgRules.vars_subset_b (collect_free_vars [] inv) allowed
  end.

Definition find_hdr_block_id (hdr_name : string) (blks : list (block dtyp)) : option block_id :=
  match List.find (fun b => String.eqb (cert_raw_id_bare (blk_id b)) hdr_name) blks with
  | Some b => Some (blk_id b)
  | None => None
  end.

Definition prepare_mc_loop_ir
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (ls : mc_loop_spec)
  : option mc_loop_ir_prep :=
  if negb (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) then None
  else
    let bmap := ocfg_map (blks ir_cfg) in
    match find_hdr_block_id (ml_ir_header ls) (blks ir_cfg) with
    | None => None
    | Some hdr_id =>
    match RM.find hdr_id bmap with
    | None => None
    | Some b_hdr =>
        match extract_hdr_phis (blk_phis b_hdr) with
        | None => None
        | Some hdr_phis =>
            if negb (no_dup_raw_ids (List.map fst hdr_phis)) then None
            else
              let ir_pnames := List.map cert_reg_name (args ir_cfg) in
              let lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg) in
              let ir_fuel := S (List.length (blks ir_cfg) + 1) in
              match ir_seg_written_ids ir_fuel bmap hdr_id false [] (init ir_cfg),
                    reify_ir_seg ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init with
              | Some wr_entry, Some t_ir_entry =>
                  let lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_entry) in
                  let lmap_cut := wrap_cut_mc lmap_base hdr_phis in
                  match ir_seg_written_ids ir_fuel bmap hdr_id true [] hdr_id,
                        reify_ir_seg ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut with
                  | Some wr_body, Some t_ir_body =>
                      if disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body) &&
                         ir_seg_freeze_free t_ir_entry &&
                         ir_seg_freeze_free t_ir_body &&
                         check_ls_exprs_vars (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls
                      then
                        Some (mk_mc_loop_ir_prep hdr_id b_hdr hdr_phis lmap_base wr_entry wr_body t_ir_entry t_ir_body)
                      else None
                  | _, _ => None
                  end
              | _, _ => None
              end
        end
    end
    end.

Record mc_loop_cnf_bundle : Type := mk_mc_loop_cnf_bundle {
  mlcb_prep : mc_loop_ir_prep;
  mlcb_ctx : ub_ctx;
  mlcb_known : list (string * positive);
  mlcb_obls : list mc_loop_obl
}.

Definition build_mc_loop_bundle_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + (mc_loop_cnf_bundle * rv_seg_tree * rv_seg_tree * rv_seg_tree) :=
  if negb (wf_mc_loop_spec EA_Riscv64 ls) then inl "malformed RV64 mc_loop_spec"
  else if negb (rv_supported_arg_width ret_w) then inl "unsupported return width for RV64 loop"
  else if negb (forallb inst_no_word_mulh insts) then inl "unsupported RV64 mulhw instruction in loop"
  else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb rv_valid_arg_spec arg_specs) then
    inl "invalid RV64 argument specs for loop"
  else
    match prepare_mc_loop_ir ir_cfg allowed0 ls with
    | None => inl "IR loop preparation/reification failed"
    | Some prep =>
        let mc_fuel := S (2 * List.length insts) in
        let hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep) in
        match summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                (rv_build_init_val_regs 10%N arg_specs) [] ret_w,
              summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w,
              summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w with
        | Some seg_ent, Some seg_body, Some seg_skel =>
            if negb (mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_ent) &&
                     mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel)) then
              inl "RV64 loop skeleton callee-saved/stack check failed"
            else
              let obls :=
                collect_mc_ir_obls EA_Riscv64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (rv_seg_to_mc_seg seg_ent) ++
                collect_mc_ir_obls EA_Riscv64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (rv_seg_to_mc_seg seg_body) in
              let ghost_vars := cut_vars_from 0%nat (mlip_hdr_phis prep) ++ hi32_vars ls in
              let known_vars := allowed0 ++ ghost_vars in
              let loop_ctx := mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost_vars in
              inr (mk_mc_loop_cnf_bundle prep loop_ctx known_vars obls, seg_ent, seg_body, seg_skel)
        | _, _, _ => inl "RV64 loop symbolic segment summarization failed"
        end
    end.

Definition validate_mc_loop_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_loop_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      if check_mc_loop_obls (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) opt_pf
      then inr tt
      else inl "RV64 loop SAT/LRAT obligation check failed"
  end.

Definition emit_mc_loop_cnf_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + option (positive * cnf) :=
  match build_mc_loop_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      match emit_mc_loop_cnf (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) with
      | None => inl "RV64 loop CNF emission failed"
      | Some nf => inr nf
      end
  end.

Definition build_mc_loop_bundle_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + (mc_loop_cnf_bundle * a64_seg_tree * a64_seg_tree * a64_seg_tree) :=
  if negb (wf_mc_loop_spec EA_AArch64 ls) then inl "malformed AArch64 mc_loop_spec"
  else if negb (rv_supported_arg_width ret_w) then inl "unsupported return width for AArch64 loop"
  else if negb (forallb a64_inst_valid insts) then inl "invalid AArch64 instruction in loop"
  else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb a64_valid_arg_spec arg_specs) then
    inl "invalid AArch64 argument specs for loop"
  else
    match prepare_mc_loop_ir ir_cfg allowed0 ls with
    | None => inl "IR loop preparation/reification failed"
    | Some prep =>
        let mc_fuel := S (2 * List.length insts) in
        let hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep) in
        match summarize_a64_seg mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w,
              summarize_a64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w,
              summarize_a64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w with
        | Some seg_ent, Some seg_body, Some seg_skel =>
            if negb (mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_ent) &&
                     mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel)) then
              inl "AArch64 loop skeleton callee-saved/stack check failed"
            else
              let obls :=
                collect_mc_ir_obls EA_AArch64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (a64_seg_to_mc_seg seg_ent) ++
                collect_mc_ir_obls EA_AArch64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (a64_seg_to_mc_seg seg_body) in
              let ghost_vars := cut_vars_from 0%nat (mlip_hdr_phis prep) ++ hi32_vars ls in
              let known_vars := allowed0 ++ ghost_vars in
              let loop_ctx := mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost_vars in
              inr (mk_mc_loop_cnf_bundle prep loop_ctx known_vars obls, seg_ent, seg_body, seg_skel)
        | _, _, _ => inl "AArch64 loop symbolic segment summarization failed"
        end
    end.

Definition validate_mc_loop_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_loop_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      if check_mc_loop_obls (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) opt_pf
      then inr tt
      else inl "AArch64 loop SAT/LRAT obligation check failed"
  end.

Definition emit_mc_loop_cnf_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + option (positive * cnf) :=
  match build_mc_loop_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      match emit_mc_loop_cnf (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) with
      | None => inl "AArch64 loop CNF emission failed"
      | Some nf => inr nf
      end
  end.




(** ** 6. Backward Partial Correctness & Arbitrary-Depth Forward Progress Proofs *)

Lemma dummy_freeze_oracle_const : forall w x y,
  dummy_freeze_oracle w x = dummy_freeze_oracle w y.
Proof. intros w x y; reflexivity. Qed.

Lemma mc_sp_aligned16_bounds : forall sp_off,
  mc_sp_aligned16 sp_off = true -> (- mc_frame_cap <= sp_off <= 0)%Z.
Proof.
  intros sp_off H; unfold mc_sp_aligned16 in H; rewrite !andb_true_iff in H; destruct H as [[Hlo Hhi] _].
  split; apply Z.leb_le; assumption.
Qed.

Lemma wf_mc_loop_spec_sp_bounds : forall arch ls,
  wf_mc_loop_spec arch ls = true -> (- mc_frame_cap <= ml_sp_off ls <= 0)%Z.
Proof.
  intros arch ls Hwf; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & Hsp) & _) & _) & _) & _) & _) & _).
  exact (mc_sp_aligned16_bounds _ Hsp).
Qed.

Lemma NoDup_app_intro : forall {A : Type} (xs ys : list A),
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros A xs; induction xs as [| x rx IH]; intros ys Hxs Hys Hdisj; cbn [app]; [exact Hys |].
  inversion Hxs as [| ? ? Hnin Hrx]; subst; constructor.
  - intro Hin; apply in_app_iff in Hin as [Hx | Hy]; [exact (Hnin Hx) | exact (Hdisj x (or_introl eq_refl) Hy)].
  - exact (IH ys Hrx Hys (fun y Hy => Hdisj y (or_intror Hy))).
Qed.

Lemma mc_skel_reg_slot_disjoint : forall r i,
  mc_skel_reg_name r <> mc_skel_slot_name i.
Proof.
  intros r i Heq; unfold mc_skel_reg_name, mc_skel_slot_name in Heq; discriminate Heq.
Qed.

Lemma mc_cut_hi_disjoint : forall k r,
  mc_cut_var_name k <> mc_hi_var_name r.
Proof.
  intros k r Heq; unfold mc_cut_var_name, mc_hi_var_name in Heq; discriminate Heq.
Qed.

Lemma mc_skel_reg_bang : forall r, mc_starts_with_bang (mc_skel_reg_name r) = true.
Proof. intro r; reflexivity. Qed.

Lemma mc_skel_slot_bang : forall i, mc_starts_with_bang (mc_skel_slot_name i) = true.
Proof. intro i; reflexivity. Qed.

Lemma mc_cut_var_bang : forall k, mc_starts_with_bang (mc_cut_var_name k) = true.
Proof. intro k; reflexivity. Qed.

Lemma mc_hi_var_bang : forall r, mc_starts_with_bang (mc_hi_var_name r) = true.
Proof. intro r; reflexivity. Qed.

Lemma rv_unspilled_preserved_nonzero : forall ls r,
  In r (mc_unspilled_preserved EA_Riscv64 ls) -> r <> 0%N.
Proof.
  intros ls r Hin; unfold mc_unspilled_preserved, mc_preserved_regs in Hin.
  apply filter_In in Hin as [Hrv _].
  cbn [rv_preserved_non_sp_regs In] in Hrv; repeat destruct Hrv as [<- | Hrv]; try lia; contradiction.
Qed.

Lemma a64_unspilled_preserved_lt31 : forall ls r,
  In r (mc_unspilled_preserved EA_AArch64 ls) -> (N.leb 31%N r = false).
Proof.
  intros ls r Hin; unfold mc_unspilled_preserved, mc_preserved_regs, a64_callee_saved_list in Hin.
  apply filter_In in Hin as [Ha64 _].
  cbn [In] in Ha64; repeat destruct Ha64 as [<- | Ha64]; try reflexivity; contradiction.
Qed.

Definition skel_reg_binds {Pa : Params}
  (read_reg : N -> @Integers.bit_int 64%positive) (rbs : list mc_loop_reg_bind)
  : list (string * @dvalue Pa) :=
  List.map (fun rb => (mc_skel_reg_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))) rbs.

Fixpoint skel_slot_binds {Pa : Params}
  (mstk : mc_stack_mem) (idx : nat) (sbs : list mc_loop_slot_bind)
  {struct sbs} : list (string * @dvalue Pa) :=
  match sbs with
  | [] => []
  | MLS_Expr o s _ :: rest =>
      (mc_skel_slot_name idx, DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false))) ::
      skel_slot_binds mstk (S idx) rest
  | MLS_SavedReg _ _ :: rest =>
      skel_slot_binds mstk (S idx) rest
  end.

Lemma skel_slot_binds_ge {Pa : Params} :
  forall mstk idx sbs nm,
    In nm (List.map fst (@skel_slot_binds Pa mstk idx sbs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_skel_slot_name j.
Proof.
  intros mstk idx sbs; revert idx; induction sbs as [| [o s e | o r] rest IH]; intros idx nm Hin;
    cbn [skel_slot_binds List.map fst] in Hin; [contradiction | |].
  - destruct Hin as [Heq | Hr].
    + exists idx; split; [lia | symmetry; exact Heq].
    + destruct (IH (S idx) nm Hr) as [j [Hle Hnm]]; exists j; split; [lia | exact Hnm].
  - destruct (IH (S idx) nm Hin) as [j [Hle Hnm]]; exists j; split; [lia | exact Hnm].
Qed.

Lemma skel_binds_nodup {Pa : Params} :
  forall (read_reg : N -> @Integers.bit_int 64%positive) mstk ls,
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@skel_reg_binds Pa read_reg (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls))).
Proof.
  intros read_reg mstk ls Hnd; rewrite List.map_app; apply NoDup_app_intro.
  - clear mstk; induction (ml_regs ls) as [| rb rest IH]; cbn in *; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnr]; subst; constructor; [| exact (IH Hnr)].
    intro Hin; apply in_map_iff in Hin as [[x dv] [Hfx Hin]].
    cbn in Hfx; subst x; apply in_map_iff in Hin as [rb0 [Heq0 Hrb0]].
    apply (f_equal fst) in Heq0; cbn in Heq0; apply mc_skel_reg_name_inj in Heq0.
    apply Hnin; rewrite <- Heq0; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
  - clear read_reg Hnd; generalize 0%nat as idx; induction (ml_slots ls) as [| [o s e | o r] rest IH];
      intro idx; cbn [skel_slot_binds List.map]; [constructor | | exact (IH (S idx))].
    constructor; [| exact (IH (S idx))].
    intro Hin; apply skel_slot_binds_ge in Hin as [j [Hle Heq]]; apply mc_skel_slot_name_inj in Heq; lia.
  - intros x Hxr Hxs.
    apply in_map_iff in Hxr as [[x0 dv] [Hfx Hinr]]; cbn in Hfx; subst x0.
    apply in_map_iff in Hinr as [rb [Heq0 _]]; inversion Heq0 as [Hxr]; clear Heq0.
    apply skel_slot_binds_ge in Hxs as [j [_ Hxs]]; rewrite <- Hxr in Hxs.
    exact (mc_skel_reg_slot_disjoint (mlr_reg rb) j Hxs).
Qed.

Lemma skel_slot_binds_nth {Pa : Params} :
  forall mstk idx sbs i o s e,
    nth_error sbs i = Some (MLS_Expr o s e) ->
    In (mc_skel_slot_name (idx + i), DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))
       (skel_slot_binds mstk idx sbs).
Proof.
  intros mstk idx sbs; revert idx; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH];
    intros idx i o s e Hnth; [destruct i; discriminate Hnth | |].
  - destruct i as [| i']; cbn in Hnth.
    + inversion Hnth; subst; rewrite Nat.add_0_r; left; reflexivity.
    + right; replace (idx + S i')%nat with (S idx + i')%nat by lia; exact (IH (S idx) i' o s e Hnth).
  - destruct i as [| i']; cbn in Hnth; [discriminate Hnth |].
    replace (idx + S i')%nat with (S idx + i')%nat by lia; exact (IH (S idx) i' o s e Hnth).
Qed.

Definition rv_at_cut (ls : mc_loop_spec) (rf0 rf : rv_regfile) (mstk : mc_stack_mem) : Prop :=
  rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) /\
  (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) /\
  (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
     mc_stk_load mstk off MS_8 false = rv_read_reg r rf0).

Definition a64_at_cut (ls : mc_loop_spec) (sp0 : @Integers.bit_int 64%positive)
  (rf0 rf : a64_regfile) (sp : @Integers.bit_int 64%positive) (mstk : mc_stack_mem) : Prop :=
  sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive (ml_sp_off ls)) /\
  (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) /\
  (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
     mc_stk_load mstk off MS_8 false = a64_read_reg r rf0).

Lemma rv_skel_step {Pa : Params} :
  forall insts ret_w ls seg_skel rf0 rf mstk,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    summarize_rv64_seg (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w = Some seg_skel ->
    mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel) = true ->
    rv_at_cut ls rf0 rf mstk ->
    (exists fuel_end rf_end mstk_end,
       rv_exec_mem fuel_end insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N) \/
    (exists n rf' mstk',
       (1 <= n)%nat /\
       rv_exec_steps n insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk = Some (ml_mc_pc ls, rf', mstk') /\
       rv_at_cut ls rf0 rf' mstk').
Proof.
  intros insts ret_w ls seg_skel rf0 rf mstk Hwf Hrw Hnmul Hsp0 Hsum Hok [Hsp [Hunsp Hsav]].
  pose proof (wf_mc_loop_spec_sp_bounds _ _ Hwf) as Hrng.
  assert (Hnd : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); exact (no_dup_N_to_NoDup _ Hnd_b). }
  set (binds := @skel_reg_binds Pa (fun r => rv_read_reg r rf) (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls)).
  set (penv_s := overlay_penv binds (fun _ => None)).
  assert (Hnd_b : NoDup (List.map fst binds)) by exact (skel_binds_nodup _ mstk ls Hnd).
  assert (Hregs : forall rb, In rb (ml_regs ls) ->
    penv_s (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))).
  { intros rb Hrb; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; left; unfold skel_reg_binds; apply in_map_iff; exists rb; split; [reflexivity | exact Hrb]. }
  assert (Hslots : forall i o s e, nth_error (ml_slots ls) i = Some (MLS_Expr o s e) ->
    penv_s (mc_skel_slot_name (0%nat + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; right; exact (skel_slot_binds_nth mstk 0%nat (ml_slots ls) i o s e Hnth). }
  pose proof (rv_skel_vrf_agrees penv_s dummy_freeze_oracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs) as Hag.
  pose proof (build_skel_astk_agrees penv_s dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) 0%nat (ml_slots ls) mstk Hslots Hsav) as Hastk.
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  pose proof (summarize_rv64_seg_sound _ insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w seg_skel
                penv_s dummy_freeze_oracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng (rv_skel_vrf_sp ls Hwfb) Hag Hastk Hsum) as Hexec.
  apply rv_seg_exec_to_mc in Hexec.
  destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_s dummy_freeze_oracle _ _ _ Hok Hexec)
    as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & Hn & Hsteps & _ & Hsp2' & Hag' & Hastk'))
       | (ret_e & (fuel_end & rf_end & mstk_end & Hmem & Hcs & Hra & _))].
  - right; exists n, rf', mstk'; split; [exact (Hn eq_refl) | split; [exact Hsteps |]].
    repeat split.
    + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
    + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
      pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
      unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
    + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_s dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                  off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
      cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
  - left; exists fuel_end, rf_end, mstk_end; repeat split; assumption.
Qed.

Lemma rv_skel_backward_sound {Pa : Params} :
  forall insts ret_w ls seg_skel rf0 n_max fuel rf mstk rf_end mstk_end,
    (fuel <= n_max)%nat ->
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    summarize_rv64_seg (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w = Some seg_skel ->
    mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel) = true ->
    rv_at_cut ls rf0 rf mstk ->
    rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N.
Proof.
  intros insts ret_w ls seg_skel rf0 n_max; induction n_max as [| n_max' IH];
    intros fuel rf mstk rf_end mstk_end Hle Hwf Hrw Hnmul Hsp0 Hsum Hok Hat Hmem.
  - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [rv_exec_mem] in Hmem; discriminate Hmem.
  - destruct (@rv_skel_step Pa insts ret_w ls seg_skel rf0 rf mstk Hwf Hrw Hnmul Hsp0 Hsum Hok Hat)
      as [(fuel_e & rf_e & mstk_e & Hme & Hcs & Hra) | (n1 & rf1 & mstk1 & Hn1 & Hst1 & Hat1)].
    + pose proof (rv_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk _ _ Hmem Hme) as Heq.
      inversion Heq; subst rf_e mstk_e; split; assumption.
    + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk
                  (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
      exact (IH (fuel - n1)%nat rf1 mstk1 rf_end mstk_end ltac:(lia) Hwf Hrw Hnmul Hsp0 Hsum Hok Hat1 Hrem).
Qed.

Lemma a64_skel_step {Pa : Params} :
  forall insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    summarize_a64_seg (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w = Some seg_skel ->
    mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel) = true ->
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    (exists fuel_end rf_end fl_end mstk_end,
       a64_exec_mem fuel_end insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end) \/
    (exists n rf' sp' fl' mstk',
       (1 <= n)%nat /\
       a64_exec_steps n insts sp0 (ml_mc_pc ls) rf sp fl mstk = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\
       a64_at_cut ls sp0 rf0 rf' sp' mstk').
Proof.
  intros insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk Hwf Hrw Hval Hsp0 Hsum Hok [Hsp [Hunsp Hsav]].
  pose proof (wf_mc_loop_spec_sp_bounds _ _ Hwf) as Hrng.
  assert (Hnd : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); exact (no_dup_N_to_NoDup _ Hnd_b). }
  set (binds := @skel_reg_binds Pa (fun r => a64_read_reg r rf) (ml_regs ls) ++ skel_slot_binds mstk 0%nat (ml_slots ls)).
  set (penv_s := overlay_penv binds (fun _ => None)).
  assert (Hnd_b : NoDup (List.map fst binds)) by exact (skel_binds_nodup _ mstk ls Hnd).
  assert (Hregs : forall rb, In rb (ml_regs ls) ->
    penv_s (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))).
  { intros rb Hrb; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; left; unfold skel_reg_binds; apply in_map_iff; exists rb; split; [reflexivity | exact Hrb]. }
  assert (Hslots : forall i o s e, nth_error (ml_slots ls) i = Some (MLS_Expr o s e) ->
    penv_s (mc_skel_slot_name (0%nat + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; unfold penv_s; apply overlay_penv_lookup_in; [exact Hnd_b |].
    unfold binds; apply in_or_app; right; exact (skel_slot_binds_nth mstk 0%nat (ml_slots ls) i o s e Hnth). }
  pose proof (a64_skel_vrf_agrees penv_s dummy_freeze_oracle ls rf0 sp0 rf Hwf Hunsp Hregs) as Hag.
  pose proof (build_skel_astk_agrees penv_s dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0 0%nat (ml_slots ls) mstk Hslots Hsav) as Hastk.
  pose proof (summarize_a64_seg_sound _ insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w seg_skel
                penv_s dummy_freeze_oracle rf0 sp0 rf sp fl mstk Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun C => ltac:(discriminate C)) Hsum) as Hexec.
  apply a64_seg_exec_to_mc in Hexec.
  destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_s dummy_freeze_oracle _ _ _ Hok Hexec)
    as [(sp_off' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp' & fl' & mstk' & Hn & Hsteps & _ & Hsp' & Hag' & Hastk'))
       | (ret_e & (fuel_end & rf_end & fl_end & mstk_end & Hmem & Hcs & _))].
  - right; exists n, rf', sp', fl', mstk'; split; [exact (Hn eq_refl) | split; [exact Hsteps |]].
    repeat split; try assumption.
    + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
    + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_s dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                  off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
      cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
  - left; exists fuel_end, rf_end, fl_end, mstk_end; split; assumption.
Qed.

Lemma a64_skel_backward_sound {Pa : Params} :
  forall insts ret_w ls seg_skel rf0 sp0 n_max fuel rf sp fl mstk rf_end sp_end fl_end mstk_end,
    (fuel <= n_max)%nat ->
    wf_mc_loop_spec EA_AArch64 ls = true ->
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    summarize_a64_seg (S (2 * List.length insts)) insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
      (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w = Some seg_skel ->
    mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel) = true ->
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end.
Proof.
  intros insts ret_w ls seg_skel rf0 sp0 n_max; induction n_max as [| n_max' IH];
    intros fuel rf sp fl mstk rf_end sp_end fl_end mstk_end Hle Hwf Hrw Hval Hsp0 Hsum Hok Hat Hmem.
  - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [a64_exec_mem] in Hmem; discriminate Hmem.
  - destruct (@a64_skel_step Pa insts ret_w ls seg_skel rf0 sp0 rf sp fl mstk Hwf Hrw Hval Hsp0 Hsum Hok Hat)
      as [(fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs) | (n1 & rf1 & sp1 & fl1 & mstk1 & Hn1 & Hst1 & Hat1)].
    + pose proof (a64_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) sp0 rf sp fl mstk _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | exact Hcs].
    + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 (ml_mc_pc ls) rf sp fl mstk
                  (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
      exact (IH (fuel - n1)%nat rf1 sp1 fl1 mstk1 rf_end sp_end fl_end mstk_end ltac:(lia) Hwf Hrw Hval Hsp0 Hsum Hok Hat1 Hrem).
Qed.

(** Helpers for [ir_at_cut] and [lmap_base] *)

Definition ir_at_cut {Pa : Params}
  (bmap : rmap (block dtyp)) (init_id hdr_id : block_id)
  (env0 env_c : rmap (@dvalue Pa)) (bid_c : block_id) : Prop :=
  (env_c = env0 /\ bid_c = init_id /\ init_id = hdr_id) \/
  pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (init_id, init_id))
    env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)).

Lemma ir_at_cut_ub {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c (sigma : @draw_strat Pa),
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    cfg_steps_to_ub sigma env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)) ->
    cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (init_id, init_id)).
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c sigma Hcut Hub.
  destruct Hcut as [[-> [-> ->]] | Htau]; [exact Hub | exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau Hub)].
Qed.

Lemma ir_at_cut_ret {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c env_out (dv : @dvalue Pa),
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    pure_cfg_steps env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id)) env_out dv ->
    pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (init_id, init_id)) env_out dv.
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c env_out dv Hcut Hst.
  destruct Hcut as [[-> [-> ->]] | Htau]; [exact Hst | exact (pure_cfg_steps_to_tau_then_ret _ _ _ _ _ _ Htau Hst)].
Qed.

Lemma ir_at_cut_step {Pa : Params} :
  forall bmap init_id hdr_id env0 env_c bid_c env_c' bid_c',
    ir_at_cut bmap init_id hdr_id env0 env_c bid_c ->
    ((env_c' = env_c /\ bid_c' = bid_c /\ hdr_id = hdr_id) \/
     pure_cfg_steps_to_tau env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))
       env_c' (@denote_cfg_from Pa bmap None (bid_c', hdr_id))) ->
    ir_at_cut bmap init_id hdr_id env0 env_c' bid_c'.
Proof.
  intros bmap init_id hdr_id env0 env_c bid_c env_c' bid_c' Hcut Hstep.
  destruct Hstep as [[-> [-> _]] | Htau2]; [exact Hcut |].
  right; destruct Hcut as [[-> [-> ->]] | Htau1];
    [exact Htau2 | exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau1 Htau2)].
Qed.

Lemma common_cut_lmap_wf : forall allowed base lms,
  wf_pure_lmap allowed base ->
  (forall lm, In lm lms -> wf_pure_lmap allowed lm) ->
  wf_pure_lmap allowed (common_cut_lmap base lms).
Proof.
  intros allowed base lms Hbase Hlms; destruct lms as [| lm0 rest]; cbn [common_cut_lmap]; [exact Hbase |].
  intros r w ce Hf.
  pose proof (common_cut_lmap_in base (lm0 :: rest) lm0 (or_introl eq_refl) r w ce Hf) as Hf0.
  exact (Hlms lm0 (or_introl eq_refl) r w ce Hf0).
Qed.

Lemma lmap_matches_env_penv_agree {Pa : Params} :
  forall allowed (penv1 penv2 : param_env Pa) lm env,
    wf_pure_lmap allowed lm ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    lmap_matches_env penv1 lm env ->
    lmap_matches_env penv2 lm env.
Proof.
  intros allowed penv1 penv2 lm env Hwf Hag Hlm r w ce Hf.
  destruct (Hlm r w ce Hf) as (dv & Hev & Hsc & Hrm).
  destruct (Hwf r w ce Hf) as (_ & _ & Hlf & Hfv).
  exists dv; repeat split; try assumption.
  rewrite <- Hsc; symmetry; apply eval_cert_expr_penv_eq_if_vars; [exact Hlf |].
  intros nm wn Hin; exact (Hag nm wn (Hfv _ Hin)).
Qed.

Lemma wrap_cut_mc_at_matches {Pa : Params} :
  forall (penv : param_env Pa) lmap_base idx hspecs dvs env,
    lmap_matches_env penv lmap_base env ->
    NoDup (List.map fst hspecs) ->
    Forall2 (fun '(id, _) '(id', _) => id' = id) hspecs dvs ->
    (forall r, In r (lmap_keys lmap_base) -> ~ In r (List.map fst hspecs)) ->
    (forall j id w dv,
       nth_error hspecs j = Some (id, w) ->
       nth_error dvs j = Some (id, dv) ->
       penv (mc_cut_var_name (idx + j)) = Some dv /\ wf_scalar_dvalue w dv) ->
    lmap_matches_env penv (wrap_cut_mc_at idx lmap_base hspecs) (apply_phi_env env dvs).
Proof.
  intros penv lmap_base idx hspecs; revert idx;
    induction hspecs as [| [id w] rest IH]; intros idx [| [id' dv'] rdvs] env Hlm Hnd Hids Hdisj Hp;
    try (inversion Hids; fail); cbn [wrap_cut_mc_at apply_phi_env].
  - exact Hlm.
  - cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin_rest Hnd_rest]; subst.
    assert (Hids_rest : Forall2 (fun '(id0, _) '(id'0, _) => id'0 = id0) rest rdvs)
      by (inversion Hids; assumption).
    assert (Hid : id' = id) by (inversion Hids; assumption).
    subst id'.
    intros r wr cer Hf.
    destruct (RawIDOrd.eq_dec id r) as [Heqr | Hneqr].
    + subst r; rewrite RMF.F.add_eq_o in Hf by reflexivity; inversion Hf; subst wr cer.
      destruct (Hp 0%nat id w dv' eq_refl eq_refl) as [Hpv Hsc].
      rewrite Nat.add_0_r in Hpv; exists dv'; repeat split; try assumption.
      * rewrite apply_phi_env_preserves_not_in;
          [rewrite RMF.F.add_eq_o by reflexivity; reflexivity
          | intro Hin; apply Hnin_rest; clear -Hids_rest Hin;
            revert rdvs Hids_rest Hin; induction rest as [| [i0 w0] rr IHr]; intros rdvs H2 Hin;
            destruct rdvs as [| [i1 d1] r2]; try inversion H2; cbn in Hin; [contradiction |];
            subst; destruct Hin as [Heq | Hr]; [cbn in *; left; congruence | right; exact (IHr _ H5 Hr)]].
      * unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv.
        destruct Hsc as [-> | [v ->]]; cbn [check_scalar_width]; [reflexivity | rewrite Pos.eqb_refl; reflexivity].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneqr.
      assert (Hlm_add : lmap_matches_env penv lmap_base (RM.add id dv' env)).
      { intros r0 w0 ce0 Hf0; destruct (Hlm r0 w0 ce0 Hf0) as (d0 & He0 & Hs0 & Hr0).
        exists d0; repeat split; try assumption.
        rewrite RMF.F.add_neq_o; [exact He0 | intro Heq; subst r0; apply (Hdisj id (proj2 (in_lmap_keys_iff lmap_base id) (ex_intro _ _ Hf0))); left; reflexivity]. }
      assert (Hp_sub : forall j0 id0 w0 dv0,
        nth_error rest j0 = Some (id0, w0) ->
        nth_error rdvs j0 = Some (id0, dv0) ->
        penv (mc_cut_var_name (S idx + j0)) = Some dv0 /\ wf_scalar_dvalue w0 dv0).
      { intros j0 id0 w0 dv0 Hn1 Hn2; replace (S idx + j0)%nat with (idx + S j0)%nat by lia; exact (Hp (S j0) id0 w0 dv0 Hn1 Hn2). }
      exact (IH (S idx) rdvs (RM.add id dv' env) Hlm_add Hnd_rest Hids_rest
               (fun r0 Hr0 Hin => Hdisj r0 Hr0 (or_intror Hin)) Hp_sub r wr cer Hf).
Qed.

(** Constructive Cutpoint [penv] Construction *)

Lemma is_exact_cut_var_has_var : forall k w e,
  is_exact_cut_var k w e = true -> expr_has_var (mc_cut_var_name k) e = true.
Proof.
  intros k w e H; destruct e; cbn in H; try discriminate H; apply andb_true_iff in H as [Hnm _].
  unfold expr_has_var; cbn; rewrite Hnm; reflexivity.
Qed.

Lemma is_exact_cut_var_inj_k : forall k1 w1 k2 w2 e,
  is_exact_cut_var k1 w1 e = true ->
  is_exact_cut_var k2 w2 e = true ->
  k1 = k2 /\ w1 = w2.
Proof.
  intros k1 w1 k2 w2 e H1 H2; destruct e; cbn in H1, H2; try discriminate H1.
  apply andb_true_iff in H1 as [Hn1 Hw1]; apply andb_true_iff in H2 as [Hn2 Hw2].
  apply String.eqb_eq in Hn1; apply String.eqb_eq in Hn2; apply Pos.eqb_eq in Hw1; apply Pos.eqb_eq in Hw2.
  subst; split; [apply mc_cut_var_name_inj; exact Hn2 | reflexivity].
Qed.

Lemma length_filter_ge1 : forall {A : Type} (f : A -> bool) (xs : list A) (x : A),
  f x = true -> In x xs -> (1 <= List.length (List.filter f xs))%nat.
Proof.
  intros A f xs; induction xs as [| y rest IH]; intros x Hfx Hin; cbn in Hin; [contradiction |].
  cbn [List.filter]; destruct Hin as [-> | Hr].
  - rewrite Hfx; cbn [List.length]; lia.
  - destruct (f y); cbn [List.length]; pose proof (IH x Hfx Hr); lia.
Qed.

Fixpoint find_ptol_reg (k : nat) (w : positive) (rbs : list mc_loop_reg_bind) {struct rbs} : option N :=
  match rbs with
  | [] => None
  | rb :: rest => if is_exact_cut_var k w (mlr_expr rb) then Some (mlr_reg rb) else find_ptol_reg k w rest
  end.

Fixpoint find_ptol_slot (k : nat) (w : positive) (sbs : list mc_loop_slot_bind) {struct sbs} : option (Z * mc_mem_size) :=
  match sbs with
  | [] => None
  | MLS_Expr off sz e :: rest =>
      if is_exact_cut_var k w e then Some (off, sz) else find_ptol_slot k w rest
  | MLS_SavedReg _ _ :: rest =>
      find_ptol_slot k w rest
  end.

Lemma find_ptol_reg_spec : forall k w rbs rb,
  (List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rbs) <= 1)%nat ->
  In rb rbs ->
  is_exact_cut_var k w (mlr_expr rb) = true ->
  find_ptol_reg k w rbs = Some (mlr_reg rb).
Proof.
  intros k w rbs; induction rbs as [| rb0 rest IH]; intros rb Hle Hin Hex; cbn in *; [contradiction |].
  pose proof (is_exact_cut_var_has_var k w (mlr_expr rb) Hex) as Hhv.
  destruct (is_exact_cut_var k w (mlr_expr rb0)) eqn:Ex0.
  - rewrite (is_exact_cut_var_has_var k w _ Ex0) in Hle; cbn [List.length] in Hle.
    destruct Hin as [<- | Hinr]; [reflexivity |].
    pose proof (length_filter_ge1 (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rest rb Hhv Hinr); lia.
  - destruct (expr_has_var (mc_cut_var_name k) (mlr_expr rb0)) in Hle; cbn [List.length] in Hle;
      destruct Hin as [-> | Hinr]; [rewrite Ex0 in Hex; discriminate Hex | apply (IH rb ltac:(lia) Hinr Hex) | rewrite Ex0 in Hex; discriminate Hex | apply (IH rb ltac:(lia) Hinr Hex)].
Qed.

Lemma find_ptol_reg_none_when_zero : forall k w rbs,
  List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) rbs) = 0%nat ->
  find_ptol_reg k w rbs = None.
Proof.
  intros k w rbs; induction rbs as [| rb0 rest IH]; intro Hz; cbn in *; [reflexivity |].
  destruct (is_exact_cut_var k w (mlr_expr rb0)) eqn:Ex0.
  - rewrite (is_exact_cut_var_has_var k w _ Ex0) in Hz; cbn [List.length] in Hz; discriminate Hz.
  - destruct (expr_has_var (mc_cut_var_name k) (mlr_expr rb0)) in Hz; cbn [List.length] in Hz; [discriminate Hz | exact (IH Hz)].
Qed.

Lemma find_ptol_slot_spec : forall k w sbs off sz e,
  (List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) sbs) <= 1)%nat ->
  In (MLS_Expr off sz e) sbs ->
  is_exact_cut_var k w e = true ->
  find_ptol_slot k w sbs = Some (off, sz).
Proof.
  intros k w sbs; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH];
    intros off sz e Hle Hin Hex; cbn in *; [contradiction | |].
  - pose proof (is_exact_cut_var_has_var k w e Hex) as Hhv.
    destruct (is_exact_cut_var k w e0) eqn:Ex0.
    + rewrite (is_exact_cut_var_has_var k w e0 Ex0) in Hle; cbn [List.length] in Hle.
      destruct Hin as [Heq | Hinr]; [inversion Heq; reflexivity |].
      pose proof (length_filter_ge1 (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) rest (MLS_Expr off sz e) Hhv Hinr); lia.
    + destruct (expr_has_var (mc_cut_var_name k) e0) in Hle; cbn [List.length] in Hle;
        destruct Hin as [Heq | Hinr]; try (inversion Heq; subst; rewrite Ex0 in Hex; discriminate Hex);
        apply (IH off sz e ltac:(lia) Hinr Hex).
  - destruct Hin as [Hc | Hinr]; [discriminate Hc | exact (IH off sz e Hle Hinr Hex)].
Qed.

Lemma cut_var_ptol_count_split : forall ls k w,
  cut_var_ptol ls k w = true ->
  (List.length (List.filter (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) (ml_regs ls)) +
   List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) (ml_slots ls)) <= 1)%nat.
Proof.
  intros ls k w H; unfold cut_var_ptol in H; rewrite !andb_true_iff in H.
  destruct H as [[[_ Hcnt] _] _]; apply Nat.leb_le in Hcnt; exact Hcnt.
Qed.

Lemma cut_var_ptol_inv_not_in : forall ls k w inv_e,
  cut_var_ptol ls k w = true ->
  ml_inv ls = Some inv_e ->
  forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] inv_e).
Proof.
  intros ls k w inv_e Hpt Hmi w0.
  unfold cut_var_ptol in Hpt; rewrite Hmi, !andb_true_iff in Hpt.
  destruct Hpt as [[[Hneg _] _] _]; apply negb_true_iff in Hneg; exact (expr_has_var_false_not_in _ _ Hneg w0).
Qed.

Lemma cut_var_ptol_reg_uses : forall ls k w rb,
  cut_var_ptol ls k w = true -> In rb (ml_regs ls) -> reg_slot_uses_cut_var_ok k w (mlr_expr rb) = true.
Proof.
  intros ls k w rb Hpt Hrb; unfold cut_var_ptol in Hpt; rewrite !andb_true_iff in Hpt.
  destruct Hpt as [[[_ _] Hregs] _]; rewrite forallb_forall in Hregs; exact (Hregs rb Hrb).
Qed.

Lemma cut_var_ptol_slot_uses : forall ls k w off sz e,
  cut_var_ptol ls k w = true -> In (MLS_Expr off sz e) (ml_slots ls) -> reg_slot_uses_cut_var_ok k w e = true.
Proof.
  intros ls k w off sz e Hpt Hs; unfold cut_var_ptol in Hpt; rewrite !andb_true_iff in Hpt.
  destruct Hpt as [_ Hslts]; rewrite forallb_forall in Hslts; exact (Hslts (MLS_Expr off sz e) Hs).
Qed.

Fixpoint build_cut_ir_binds {Pa : Params}
  (idx : nat) (hdr_ws : list positive) (dvs : list (raw_id * @dvalue Pa))
  {struct hdr_ws} : list (string * @dvalue Pa) :=
  match hdr_ws, dvs with
  | _ :: rw, (_, dv) :: rd => (mc_cut_var_name idx, dv) :: build_cut_ir_binds (S idx) rw rd
  | _, _ => []
  end.

Fixpoint build_cut_mc_binds {Pa : Params}
  (ls : mc_loop_spec) (penv_mc_prev : param_env Pa)
  (read_reg : N -> @Integers.bit_int 64%positive) (mstk : mc_stack_mem)
  (idx : nat) (hdr_ws : list positive) (phis_ir : list (positive * cert_expr))
  (dvs : list (raw_id * @dvalue Pa)) {struct hdr_ws} : list (string * @dvalue Pa) :=
  match hdr_ws, phis_ir, dvs with
  | w :: rw, (_, ce) :: rp, (_, dv) :: rd =>
      let dv_bind :=
        if cut_var_ptol ls idx w then
          match find_ptol_reg idx w (ml_regs ls) with
          | Some r =>
              DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (read_reg r))))
          | None =>
              match find_ptol_slot idx w (ml_slots ls) with
              | Some (off, sz) =>
                  DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))
              | None =>
                  match dv with
                  | DVALUE_Base (@DVALUE_I _ wp' vi) =>
                      if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
                      else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                  | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                  end
              end
          end
        else
          match eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce with
          | raise_ret (DVALUE_Base (@DVALUE_I _ wp' vi)) =>
              if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
              else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
          | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
          end
      in
      (mc_cut_var_name idx, dv_bind) :: build_cut_mc_binds ls penv_mc_prev read_reg mstk (S idx) rw rp rd
  | _, _, _ => []
  end.

Definition build_hi32_binds {Pa : Params}
  (read_reg : N -> @Integers.bit_int 64%positive) (rbs : list mc_loop_reg_bind)
  : list (string * @dvalue Pa) :=
  List.flat_map (fun rb =>
    if Pos.eqb (mlr_width rb) 32%positive then
      [(mc_hi_var_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))]
    else []) rbs.

Lemma build_cut_ir_binds_ge {Pa : Params} :
  forall idx hdr_ws dvs nm,
    In nm (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_cut_var_name j.
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w rw IH]; intros idx [| [id dv] rd] nm Hin;
    cbn in Hin; try contradiction.
  destruct Hin as [<- | Hr]; [exists idx; split; [lia | reflexivity] |].
  destruct (IH (S idx) rd nm Hr) as [j [Hle ->]]; exists j; split; [lia | reflexivity].
Qed.

Lemma build_cut_ir_binds_nodup {Pa : Params} :
  forall idx hdr_ws dvs, NoDup (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)).
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w rw IH]; intros idx [| [id dv] rd]; cbn; [constructor | constructor | constructor |].
  constructor; [| exact (IH (S idx) rd)].
  intro Hin; apply build_cut_ir_binds_ge in Hin as [j [Hle Heq]]; apply mc_cut_var_name_inj in Heq; lia.
Qed.

Lemma build_cut_ir_binds_bang {Pa : Params} :
  forall idx hdr_ws dvs nm,
    In nm (List.map fst (@build_cut_ir_binds Pa idx hdr_ws dvs)) -> mc_starts_with_bang nm = true.
Proof.
  intros idx hdr_ws dvs nm Hin; apply build_cut_ir_binds_ge in Hin as [j [_ ->]]; apply mc_cut_var_bang.
Qed.

Lemma build_cut_mc_binds_ge {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm,
    In nm (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs)) ->
    exists j, (idx <= j)%nat /\ nm = mc_cut_var_name j.
Proof.
  intros ls penv_prev rr mstk idx hdr_ws; revert idx;
    induction hdr_ws as [| w rw IH]; intros idx [| [wp ce] rp] [| [id dv] rd] nm Hin;
    cbn [build_cut_mc_binds List.map fst] in Hin; try contradiction.
  destruct Hin as [<- | Hr]; [exists idx; split; [lia | reflexivity] |].
  destruct (IH (S idx) rp rd nm Hr) as [j [Hle ->]]; exists j; split; [lia | reflexivity].
Qed.

Lemma build_hi32_binds_nodup {Pa : Params} :
  forall rr rbs,
    NoDup (List.map mlr_reg rbs) ->
    NoDup (List.map fst (@build_hi32_binds Pa rr rbs)).
Proof.
  intros rr rbs; induction rbs as [| rb rest IH]; intro Hnd; cbn in *; [constructor |].
  inversion Hnd as [| ? ? Hnin Hnr]; subst.
  destruct (Pos.eqb (mlr_width rb) 32%positive); cbn [app List.map]; [| exact (IH Hnr)].
  constructor; [| exact (IH Hnr)].
  intro Hin; apply in_map_iff in Hin as [[nm dv] [Hfx Hfl]]; cbn in Hfx; subst nm.
  unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb0 [Hrb0 Hin0]].
  destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hin0; [| contradiction].
  destruct Hin0 as [Heq | []]; apply (f_equal fst) in Heq; cbn in Heq; apply mc_hi_var_name_inj in Heq.
  apply Hnin; rewrite <- Heq; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
Qed.

Lemma build_cut_mc_hi_nodup {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs,
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs ++ build_hi32_binds rr (ml_regs ls))).
Proof.
  intros ls penv_prev rr mstk idx hdr_ws phis_ir dvs Hnd; rewrite List.map_app; apply NoDup_app_intro.
  - clear -idx; revert idx phis_ir dvs; induction hdr_ws as [| w rw IH]; intros idx [| [wp ce] rp] [| [id dv] rd]; cbn;
      try (constructor; fail).
    constructor; [| exact (IH (S idx) rp rd)].
    intro Hin; apply build_cut_mc_binds_ge in Hin as [j [Hle Heq]]; apply mc_cut_var_name_inj in Heq; lia.
  - exact (build_hi32_binds_nodup rr (ml_regs ls) Hnd).
  - intros x Hxc Hxh; apply build_cut_mc_binds_ge in Hxc as [j [_ ->]].
    apply in_map_iff in Hxh as [[nm dv] [Hfx Hfl]]; cbn in Hfx; subst nm.
    unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb0 [_ Hin0]].
    destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hin0; [| contradiction].
    destruct Hin0 as [Heq | []]; inversion Heq as [Hnm]; exact (mc_cut_hi_disjoint j (mlr_reg rb0) Hnm).
Qed.

Lemma build_cut_mc_hi_bang {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm,
    In nm (List.map fst (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs ++ build_hi32_binds rr (ml_regs ls))) ->
    mc_starts_with_bang nm = true.
Proof.
  intros ls penv_prev rr mstk idx hdr_ws phis_ir dvs nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hc | Hh].
  - apply build_cut_mc_binds_ge in Hc as [j [_ ->]]; apply mc_cut_var_bang.
  - apply in_map_iff in Hh as [[x dv] [<- Hfl]]; unfold build_hi32_binds in Hfl; apply in_flat_map in Hfl as [rb [_ Hr]].
    destruct (Pos.eqb (mlr_width rb) 32%positive); cbn in Hr; [| contradiction]; destruct Hr as [Heq | []]; inversion Heq; reflexivity.
Qed.

Fixpoint cut_vars_from_ws (idx : nat) (ws : list positive) {struct ws}
  : list (string * positive) :=
  match ws with
  | [] => []
  | w :: rest => (mc_cut_var_name idx, w) :: cut_vars_from_ws (S idx) rest
  end.

Lemma cut_vars_from_eq_ws : forall idx hspecs,
  cut_vars_from idx hspecs = cut_vars_from_ws idx (extract_hdr_phi_widths hspecs).
Proof.
  intros idx hspecs; revert idx; induction hspecs as [| [id w] rest IH];
    intro idx; cbn; [reflexivity | f_equal; exact (IH (S idx))].
Qed.

Lemma Forall2_nth_error_l_ex : forall {A B : Type} (R : A -> B -> Prop) xs ys k x,
  Forall2 R xs ys ->
  nth_error xs k = Some x ->
  exists y, nth_error ys k = Some y /\ R x y.
Proof.
  intros A B R xs ys k x Hfa; revert k; induction Hfa as [| x0 y0 rx ry Hxy Hrest IH];
    intros [| k'] Hnth; cbn in Hnth; try discriminate Hnth.
  - inversion Hnth; subst x0; exists y0; split; [reflexivity | exact Hxy].
  - exact (IH k' Hnth).
Qed.

Lemma Forall2_nth_error_r : forall {A B : Type} (R : A -> B -> Prop) xs ys k y,
  Forall2 R xs ys ->
  nth_error ys k = Some y ->
  exists x, nth_error xs k = Some x /\ R x y.
Proof.
  intros A B R xs ys k y Hfa; revert k; induction Hfa as [| x0 y0 rx ry Hxy Hrest IH];
    intros [| k'] Hnth; cbn in Hnth; try discriminate Hnth.
  - inversion Hnth; subst y0; exists x0; split; [reflexivity | exact Hxy].
  - exact (IH k' Hnth).
Qed.

Lemma build_cut_ir_binds_nth {Pa : Params} :
  forall idx hdr_ws dvs k w id dv,
    nth_error hdr_ws k = Some w ->
    nth_error dvs k = Some (id, dv) ->
    In (mc_cut_var_name (idx + k), dv) (@build_cut_ir_binds Pa idx hdr_ws dvs).
Proof.
  intros idx hdr_ws; revert idx; induction hdr_ws as [| w0 rw IH];
    intros idx [| [id0 dv0] rd] [| k'] w id dv Hnw Hndv; cbn in Hnw, Hndv;
    try discriminate Hnw; try discriminate Hndv; cbn [build_cut_ir_binds].
  - inversion Hndv; subst; rewrite Nat.add_0_r; left; reflexivity.
  - right; replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH (S idx) rd k' w id dv Hnw Hndv).
Qed.

Lemma build_cut_mc_binds_nth {Pa : Params} :
  forall ls penv_prev rr mstk idx hdr_ws phis_ir dvs k w wp ce id dv,
    nth_error hdr_ws k = Some w ->
    nth_error phis_ir k = Some (wp, ce) ->
    nth_error dvs k = Some (id, dv) ->
    let dv_bind :=
      if cut_var_ptol ls (idx + k) w then
        match find_ptol_reg (idx + k) w (ml_regs ls) with
        | Some r =>
            DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (rr r))))
        | None =>
            match find_ptol_slot (idx + k) w (ml_slots ls) with
            | Some (off, sz) =>
                DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))
            | None =>
                match dv with
                | DVALUE_Base (@DVALUE_I _ wp' vi) =>
                    if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
                    else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
                end
            end
        end
      else
        match eval_closed_cert_expr penv_prev dummy_freeze_oracle ce with
        | raise_ret (DVALUE_Base (@DVALUE_I _ wp' vi)) =>
            if Pos.eqb wp' w then DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned wp' vi)))
            else DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
        | _ => DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))
        end in
    In (mc_cut_var_name (idx + k), dv_bind)
       (@build_cut_mc_binds Pa ls penv_prev rr mstk idx hdr_ws phis_ir dvs).
Proof.
  intros ls penv_prev rr mstk idx hdr_ws; revert idx;
    induction hdr_ws as [| w0 rw IH];
    intros idx [| [wp0 ce0] rp] [| [id0 dv0] rd] [| k'] w wp ce id dv Hnw Hnp Hndv;
    cbn in Hnw, Hnp, Hndv; try discriminate Hnw; try discriminate Hnp; try discriminate Hndv;
    cbn [build_cut_mc_binds].
  - inversion Hnw; inversion Hnp; inversion Hndv; subst; rewrite Nat.add_0_r; left; reflexivity.
  - right; replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH (S idx) rp rd k' w wp ce id dv Hnw Hnp Hndv).
Qed.

Lemma build_hi32_binds_in {Pa : Params} :
  forall (rr : N -> @Integers.bit_int 64%positive) rbs rb,
    In rb rbs ->
    mlr_width rb = 32%positive ->
    In (mc_hi_var_name (mlr_reg rb), DVALUE_Base (@DVALUE_I Pa 64%positive (rr (mlr_reg rb))))
       (build_hi32_binds rr rbs).
Proof.
  intros rr rbs rb Hin Hw32; unfold build_hi32_binds; apply in_flat_map; exists rb; split; [exact Hin |].
  rewrite Hw32, Pos.eqb_refl; left; reflexivity.
Qed.

Lemma find_ptol_reg_In : forall k w rbs r,
  find_ptol_reg k w rbs = Some r ->
  exists rb, In rb rbs /\ mlr_reg rb = r /\ is_exact_cut_var k w (mlr_expr rb) = true.
Proof.
  intros k w rbs; induction rbs as [| rb rest IH]; intros r H; cbn in H; [discriminate H |].
  destruct (is_exact_cut_var k w (mlr_expr rb)) eqn:Ex.
  - inversion H; subst; exists rb; repeat split; [left; reflexivity | exact Ex].
  - destruct (IH r H) as (rb0 & Hin & Heqr & Ex0); exists rb0; repeat split; [right; exact Hin | exact Heqr | exact Ex0].
Qed.

Lemma find_ptol_slot_In : forall k w sbs off sz,
  find_ptol_slot k w sbs = Some (off, sz) ->
  exists e, In (MLS_Expr off sz e) sbs /\ is_exact_cut_var k w e = true.
Proof.
  intros k w sbs; induction sbs as [| [o0 s0 e0 | o0 r0] rest IH]; intros off sz H; cbn in H; [discriminate H | |].
  - destruct (is_exact_cut_var k w e0) eqn:Ex.
    + inversion H; subst; exists e0; split; [left; reflexivity | exact Ex].
    + destruct (IH off sz H) as [e [Hin Ex0]]; exists e; split; [right; exact Hin | exact Ex0].
  - destruct (IH off sz H) as [e [Hin Ex0]]; exists e; split; [right; exact Hin | exact Ex0].
Qed.

Lemma trunc_mc_expr_to_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle w e64 (v64 : @Integers.bit_int 64%positive),
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (trunc_mc_expr_to w e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.unsigned 64%positive v64)))).
Proof.
  intros penv foracle w e64 v64 [-> | ->] He; unfold trunc_mc_expr_to; cbn [Pos.eqb].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - rewrite (@Integers.repr_unsigned 64%positive); exact He.
Qed.

Lemma trunc_mc_slot_expr_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle sz e64 (v64 : @Integers.bit_int 64%positive),
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (trunc_mc_slot_expr sz e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive v64)))).
Proof.
  intros penv foracle sz e64 v64 He; destruct sz; unfold trunc_mc_slot_expr; cbn [mc_mem_bits].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - apply eval_ce_trunc; [reflexivity | exact He].
  - rewrite (@Integers.repr_unsigned 64%positive); exact He.
Qed.

Lemma cut_vars_from_ws_In : forall idx ws nm w,
  In (nm, w) (cut_vars_from_ws idx ws) ->
  exists k, nm = mc_cut_var_name (idx + k) /\ nth_error ws k = Some w.
Proof.
  intros idx ws; revert idx; induction ws as [| w0 rest IH]; intros idx nm w Hin;
    cbn [cut_vars_from_ws] in Hin; [contradiction |].
  destruct Hin as [Heq | Hr].
  - inversion Heq; subst; exists 0%nat; rewrite Nat.add_0_r; split; reflexivity.
  - destruct (IH (S idx) nm w Hr) as [k [Hnm Hnth]]; exists (S k);
      split; [rewrite Hnm; f_equal; lia | exact Hnth].
Qed.

Lemma hi32_vars_In : forall ls nm w,
  In (nm, w) (hi32_vars ls) ->
  exists rb, In rb (ml_regs ls) /\ mlr_width rb = 32%positive /\ nm = mc_hi_var_name (mlr_reg rb) /\ w = 64%positive.
Proof.
  intros ls nm w Hin; unfold hi32_vars in Hin; apply in_flat_map in Hin as [rb [Hrb Hhere]].
  destruct (Pos.eqb (mlr_width rb) 32%positive) eqn:Ew; cbn in Hhere; [| contradiction].
  destruct Hhere as [Heq | []]; inversion Heq; subst; apply Pos.eqb_eq in Ew.
  exists rb; repeat split; assumption.
Qed.

Lemma wf_mc_loop_reg_bind_props : forall arch ls rb,
  wf_mc_loop_spec arch ls = true -> In rb (ml_regs ls) ->
  (mlr_width rb = 32%positive \/ mlr_width rb = 64%positive) /\
  wt_cert_expr [] (mlr_expr rb) = true /\
  cert_expr_bit_width (mlr_expr rb) = mlr_width rb /\
  is_let_free_expr (mlr_expr rb) = true /\
  ub_free_expr (mlr_expr rb) = true.
Proof.
  intros arch ls rb Hwf Hrb; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _).
  rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
  unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb.
  destruct Hwrb as (((((_ & Hw) & Hwt) & Hbw) & Hlf) & Hub).
  apply orb_true_iff in Hw; apply Pos.eqb_eq in Hbw.
  split; [destruct Hw as [H32 | H64]; [left; apply Pos.eqb_eq; exact H32 | right; apply Pos.eqb_eq; exact H64] |].
  repeat split; assumption.
Qed.

Lemma wf_mc_loop_slot_bind_props : forall arch ls off sz e,
  wf_mc_loop_spec arch ls = true -> In (MLS_Expr off sz e) (ml_slots ls) ->
  wt_cert_expr [] e = true /\
  cert_expr_bit_width e = mc_mem_bits sz /\
  is_let_free_expr e = true /\
  ub_free_expr e = true.
Proof.
  intros arch ls off sz e Hwf Hs; unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & _) & _) & Hwbs) & _) & _).
  rewrite forallb_forall in Hwbs; pose proof (Hwbs (MLS_Expr off sz e) Hs) as Hwsb.
  unfold wf_mc_loop_slot_bind in Hwsb; rewrite !andb_true_iff in Hwsb.
  destruct Hwsb as ((((_ & Hwt) & Hbw) & Hlf) & Hub); apply Pos.eqb_eq in Hbw.
  repeat split; assumption.
Qed.

Lemma alg_vars_subset_b_incl : forall sub sup,
  AlgRules.vars_subset_b sub sup = true -> incl sub sup.
Proof.
  induction sub as [| [nm w] rest IH]; intros sup H [x wx] Hin; cbn in Hin; [contradiction |].
  cbn [AlgRules.vars_subset_b] in H; apply andb_true_iff in H as [Hhd Htl].
  destruct Hin as [Heq | Hr]; [| exact (IH sup Htl (x, wx) Hr)].
  inversion Heq; subst x wx; apply existsb_exists in Hhd as [[nm' w'] [Hin_s Heqb]].
  apply andb_true_iff in Heqb as [Hsn Hsw]; apply String.eqb_eq in Hsn; apply Pos.eqb_eq in Hsw; subst; exact Hin_s.
Qed.

Lemma build_next_cut_penvs_sound {Pa : Params} :
  forall arch ls allowed0 mc_init_ctx (penv0 penv_ir_prev penv_mc_prev : param_env Pa)
         hdr_ws phis_ir dvs (read_reg : N -> @Integers.bit_int 64%positive) mstk opt_inv is_body path,
    wf_mc_loop_spec arch ls = true ->
    (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall nm, mc_starts_with_bang nm = false -> penv_ir_prev nm = penv0 nm /\ penv_mc_prev nm = penv0 nm) ->
    AlgRules.vars_subset_b (collect_free_vars [] (match ml_inv ls with None => CE_BvConst 1%positive 1%N | Some inv => inv end)) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true ->
    (forall rb, In rb (ml_regs ls) -> AlgRules.vars_subset_b (collect_free_vars [] (mlr_expr rb)) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true) ->
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) -> AlgRules.vars_subset_b (collect_free_vars [] e) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true) ->
    Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir ->
    Forall2 (fun '(wp, ce) '(_, dv) =>
      eval_closed_cert_expr penv_ir_prev dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue wp dv) phis_ir dvs ->
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e => eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle inv_e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (fun '(wp, ce) =>
      wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
      is_let_free_expr ce = true /\ ub_free_expr ce = true /\
      expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else []))) phis_ir ->
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else [])) ->
       exists d1 d2 : @dvalue Pa, penv_ir_prev nm = Some d1 /\ penv_mc_prev nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) ->
    (forall k w ce,
       nth_error phis_ir k = Some (w, ce) ->
       cut_var_ptol ls k w = false ->
       exists vi, eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) ->
    (forall rb, In rb (ml_regs ls) ->
       exists e_mc64,
         eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))) /\
         mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
          mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) ->
    (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) ->
       exists e_mc64,
         eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk off sz false))) /\
         mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws e_s = false ->
          mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) ->
    match ml_inv ls with
    | None => True
    | Some inv_e =>
        mc_obl_holds penv_mc_prev dummy_freeze_oracle opt_inv is_body
          (MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
    end ->
    let ir_binds := build_cut_ir_binds 0%nat hdr_ws dvs in
    let mc_binds := build_cut_mc_binds ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds read_reg (ml_regs ls) in
    let penv_ir_next := overlay_penv ir_binds penv0 in
    let penv_mc_next := overlay_penv mc_binds penv0 in
    (forall nm, mc_starts_with_bang nm = false -> penv_ir_next nm = penv0 nm /\ penv_mc_next nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc_next /\
    ub_ctx_holds penv_mc_next dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir_next nm = Some d1 /\ penv_mc_next nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    (forall k id w dv,
       nth_error hdr_ws k = Some w ->
       nth_error dvs k = Some (id, dv) ->
       penv_ir_next (mc_cut_var_name k) = Some dv /\ wf_scalar_dvalue w dv) /\
    mc_cut_obl_inv_holds ls penv_mc_next dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc_next dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb)))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
Proof.
  intros arch ls allowed0 mc_init_ctx penv0 penv_ir_prev penv_mc_prev hdr_ws phis_ir dvs read_reg mstk opt_inv is_body path.
  intros Hwf Hnb_al Hpenv0 Hctx0 Hprev Hinv_sub Hreg_sub Hslt_sub Hws Hph Hinv_p Hpath_p Hph_wf Href_p Hphi_d Hregs Hslts Hmi.
  intros ir_binds mc_binds penv_ir_next penv_mc_next.
  assert (Hnd_r : NoDup (List.map mlr_reg (ml_regs ls))).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); exact (no_dup_N_to_NoDup _ Hnd_b). }
  assert (Hnd_ir : NoDup (List.map fst ir_binds)) by exact (build_cut_ir_binds_nodup 0%nat hdr_ws dvs).
  assert (Hnd_mc : NoDup (List.map fst mc_binds)) by exact (build_cut_mc_hi_nodup ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs Hnd_r).
  assert (Hnb_next : forall nm, mc_starts_with_bang nm = false -> penv_ir_next nm = penv0 nm /\ penv_mc_next nm = penv0 nm).
  { intros nm Hnb; split.
    - apply overlay_penv_non_bang; [| exact Hnb]; intros y Hy; exact (build_cut_ir_binds_bang _ _ _ _ Hy).
    - apply overlay_penv_non_bang; [| exact Hnb]; intros y Hy; exact (build_cut_mc_hi_bang _ _ _ _ _ _ _ _ _ Hy). }
  assert (Hcut_facts : forall k w, nth_error hdr_ws k = Some w ->
    exists id dv_ir ce vi_mc,
      nth_error phis_ir k = Some (w, ce) /\
      nth_error dvs k = Some (id, dv_ir) /\
      penv_ir_next (mc_cut_var_name k) = Some dv_ir /\
      wf_scalar_dvalue w dv_ir /\
      penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa w vi_mc)) /\
      dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa w vi_mc)) /\
      (cut_var_ptol ls k w = false ->
       eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi_mc)))).
  { intros k w Hnw.
    destruct (Forall2_nth_error_l_ex _ _ _ k w Hws Hnw) as [[wp ce] [Hnp Hweq]]; subst wp.
    destruct (Forall2_nth_error_l_ex _ _ _ k (w, ce) Hph Hnp) as [[id dv_ir] [Hndv [Hev_ir Hsc_ir]]].
    assert (Hir_k : penv_ir_next (mc_cut_var_name k) = Some dv_ir).
    { unfold penv_ir_next; apply overlay_penv_lookup_in; [exact Hnd_ir |].
      unfold ir_binds; replace k with (0%nat + k)%nat by lia; exact (build_cut_ir_binds_nth 0%nat hdr_ws dvs k w id dv_ir Hnw Hndv). }
    pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k w w ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
    rewrite Nat.add_0_l in Hin_mc; set (dv_b := if cut_var_ptol ls k w then _ else _) in Hin_mc.
    assert (Hmc_k : penv_mc_next (mc_cut_var_name k) = Some dv_b).
    { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
    assert (Hce_wf : wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = w /\ is_let_free_expr ce = true /\
      ub_free_expr ce = true /\ expr_has_freeze ce = false /\
      incl (collect_free_vars [] ce) (allowed0 ++ cut_vars_from_ws 0%nat (if is_body then hdr_ws else []))).
    { rewrite Forall_forall in Hph_wf; exact (Hph_wf (w, ce) (nth_error_In _ k Hnp)). }
    destruct Hce_wf as (Hwt_c & Hbw_c & Hlf_c & Hub_c & Hnf_c & Hfv_c).
    destruct (eval_cert_expr_refine_mono penv_ir_prev penv_mc_prev dummy_freeze_oracle ce Hwt_c Hlf_c Hub_c Hnf_c
                (fun x wx Hx => Href_p x wx (Hfv_c (x, wx) Hx)))
      as (v1 & v2 & Ev1 & Ev2 & _ & W2 & R12).
    rewrite Hev_ir in Ev1; inversion Ev1; subst v1; rewrite Hbw_c in W2.
    unfold dv_b in Hmc_k; destruct (cut_var_ptol ls k w) eqn:Ept.
    - destruct (find_ptol_reg k w (ml_regs ls)) as [r |] eqn:Epr.
      + apply find_ptol_reg_In in Epr as [rb [Hrb [<- Hex_rb]]].
        destruct rb as [r0 w0 e0]; cbn in Hex_rb; destruct e0 as [| | nm_rb w_rb | | | | | |]; try discriminate Hex_rb.
        cbn in Hex_rb; apply andb_true_iff in Hex_rb as [Hnm Hw0]; apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw0.
        destruct (wf_mc_loop_reg_bind_props arch ls _ Hwf Hrb) as (Hw32_64 & _ & Hbw_rb & _ & _); cbn in Hbw_rb.
        rewrite Hbw_rb in Hw0; subst w0; cbn [mlr_width mlr_expr mlr_reg] in *.
        eexists id, dv_ir, ce, (@Integers.repr w (@Integers.unsigned 64%positive (read_reg r0))).
        repeat split; try assumption; [| intro C; discriminate C].
        destruct Hsc_ir as [-> | [vi_ir ->]]; [apply dvalue_refines_poison_l |].
        assert (Hv2_eq : v2 = DVALUE_Base (@DVALUE_I Pa w vi_ir)).
        { destruct R12 as [Hc | ->]; [discriminate Hc | reflexivity]. }
        subst v2; destruct (Hregs _ Hrb) as (e_mc64 & Ev_mc & Ho_r & _).
        pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o; cbn [mlr_width mlr_expr mlr_reg] in *.
        assert (Hsub_ce : subst_cert_expr (build_phi_subst 0%nat phis_ir) (CE_Var nm_rb w_rb) = ce).
        { cbn [subst_cert_expr]; rewrite Hnm, Hbw_rb.
          replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k w ce Hnp), Pos.eqb_refl; reflexivity. }
        cbn [refine_eou_dvalue] in Href_o; rewrite Hsub_ce, Ev2, (trunc_mc_expr_to_sound _ _ w e_mc64 _ Hw32_64 Ev_mc) in Href_o.
        destruct Href_o as [Hc | Href_o]; [discriminate Hc | right; exact Href_o].
      + destruct (find_ptol_slot k w (ml_slots ls)) as [[off sz] |] eqn:Eps.
        * apply find_ptol_slot_In in Eps as [e0 [Hs0 Hex_s]].
          destruct e0 as [| | nm_s w_s | | | | | |]; try discriminate Hex_s; cbn in Hex_s; apply andb_true_iff in Hex_s as [Hnm Hw0].
          apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw0.
          destruct (wf_mc_loop_slot_bind_props arch ls off sz _ Hwf Hs0) as (_ & Hbw_s & _ & _); cbn in Hbw_s.
          rewrite Hbw_s in Hw0; subst w.
          eexists id, dv_ir, ce, (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))).
          repeat split; try assumption; [| intro C; discriminate C].
          destruct Hsc_ir as [-> | [vi_ir ->]]; [apply dvalue_refines_poison_l |].
          assert (Hv2_eq : v2 = DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) vi_ir)).
          { destruct R12 as [Hc | ->]; [discriminate Hc | reflexivity]. }
          subst v2; destruct (Hslts off sz _ Hs0) as (e_mc64 & Ev_mc & Ho_r & _).
          assert (Hsub_ce : subst_cert_expr (build_phi_subst 0%nat phis_ir) (CE_Var nm_s w_s) = ce).
          { cbn [subst_cert_expr]; rewrite Hnm, Hbw_s.
            replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k (mc_mem_bits sz) ce Hnp), Pos.eqb_refl; reflexivity. }
          cbn [refine_eou_dvalue] in Ho_r; pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
          rewrite Hsub_ce, Ev2, (trunc_mc_slot_expr_sound _ _ sz e_mc64 _ Ev_mc) in Href_o.
          destruct Href_o as [Hc | Href_o]; [discriminate Hc | right; exact Href_o].
        * destruct Hsc_ir as [-> | [vi_ir ->]].
          -- eexists id, (DVALUE_Base DVALUE_Poison), ce, (@Integers.zero w); repeat split; try assumption;
               [left; reflexivity | apply dvalue_refines_poison_l | intro C; discriminate C].
          -- rewrite Pos.eqb_refl, (@Integers.repr_unsigned w vi_ir) in Hmc_k; eexists id, (DVALUE_Base (@DVALUE_I Pa w vi_ir)), ce, vi_ir;
               repeat split; try assumption; [right; exists vi_ir; reflexivity | apply dvalue_refines_refl | intro C; discriminate C].
    - destruct (Hphi_d k w ce Hnp Ept) as [vi_d Hev_d].
      rewrite Hev_d in Hmc_k, Ev2; inversion Ev2; subst v2; rewrite Pos.eqb_refl, (@Integers.repr_unsigned w vi_d) in Hmc_k.
      eexists id, dv_ir, ce, vi_d; repeat split; try assumption; intros _; exact Hev_d. }
  assert (Hcut_ref : forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
    exists d1 d2 : @dvalue Pa, penv_ir_next nm = Some d1 /\ penv_mc_next nm = Some d2 /\
      wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; apply in_app_iff in Hin as [Hal | Hcut].
    - destruct (Hpenv0 nm w Hal) as [d0 [Hp0 Hwf0]].
      destruct (Hnb_next nm (Hnb_al nm w Hal)) as [-> ->].
      exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl.
    - apply cut_vars_from_ws_In in Hcut as [k [-> Hnw]].
      destruct (Hcut_facts k w Hnw) as (id & dv_ir & ce & vi_mc & _ & _ & Hir_k & Hsc_ir & Hmc_k & Href_k & _).
      rewrite Nat.add_0_l; exists dv_ir, (DVALUE_Base (@DVALUE_I Pa w vi_mc)); repeat split; try assumption.
      right; exists vi_mc; reflexivity. }
  assert (Hhi_lookup : forall rb, In rb (ml_regs ls) -> mlr_width rb = 32%positive ->
    penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb))))).
  { intros rb Hrb Hw32; unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc |].
    unfold mc_binds; apply in_or_app; right; exact (build_hi32_binds_in read_reg (ml_regs ls) rb Hrb Hw32). }
  assert (Hmc_wf : wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc_next).
  { intros nm w Hin; apply in_app_iff in Hin as [Hal | Hgh].
    - destruct (Hcut_ref nm w (in_or_app _ _ _ (or_introl Hal))) as (_ & d2 & _ & Hmc_n & _ & Hw2 & _); exists d2; split; assumption.
    - apply in_app_iff in Hgh as [Hcut | Hhi].
      + destruct (Hcut_ref nm w (in_or_app _ _ _ (or_intror Hcut))) as (_ & d2 & _ & Hmc_n & _ & Hw2 & _); exists d2; split; assumption.
      + apply hi32_vars_In in Hhi as (rb & Hrb & Hw32 & -> & ->).
        eexists; split; [exact (Hhi_lookup rb Hrb Hw32) | right; eexists; reflexivity]. }
  assert (Hctx_next : ub_ctx_holds penv_mc_next dummy_freeze_oracle
    (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls))).
  { apply Forall_app; split; [apply Hctx0; intros nm Hnb; exact (proj2 (Hnb_next nm Hnb)) |].
    apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hgh]].
    apply in_app_iff in Hgh as [Hcut | Hhi].
    - apply cut_vars_from_ws_In in Hcut as [k [-> Hnw]]; rewrite Nat.add_0_l.
      destruct (Hcut_facts k w Hnw) as (_ & _ & _ & vi_mc & _ & _ & _ & _ & Hmc_k & _).
      cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hmc_k in Hdv; inversion Hdv; discriminate.
    - apply hi32_vars_In in Hhi as (rb & Hrb & Hw32 & -> & ->).
      cbn [ub_assumption_holds]; intros dv Hdv; rewrite (Hhi_lookup rb Hrb Hw32) in Hdv; inversion Hdv; discriminate. }
  assert (Hsubst_non_ptol : forall e,
    is_let_free_expr e = true ->
    AlgRules.vars_subset_b (collect_free_vars [] e) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) = true ->
    (forall k w, nth_error hdr_ws k = Some w -> cut_var_ptol ls k w = true ->
       forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] e)) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
    eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle (subst_cert_expr (build_phi_subst 0%nat phis_ir) e)).
  { intros e Hlf Hsub Hav; apply subst_cert_expr_eval; [exact dummy_freeze_oracle_const | exact Hlf |].
    intros nm wn Hfn.
    pose proof (alg_vars_subset_b_incl _ _ Hsub _ Hfn) as Hin_all.
    apply in_app_iff in Hin_all as [Hal | Hcut].
    - pose proof (Hnb_al nm wn Hal) as Hnb.
      rewrite (lookup_phi_subst_none_non_bang 0%nat phis_ir nm Hnb).
      rewrite (proj2 (Hnb_next nm Hnb)), (proj2 (Hprev nm Hnb)); reflexivity.
    - apply cut_vars_from_ws_In in Hcut as [k [Heqn Hnw]]; rewrite Nat.add_0_l in Heqn; subst nm.
      destruct (Hcut_facts k wn Hnw) as (_ & _ & ce & vi_mc & Hnp & _ & _ & _ & Hmc_k & _ & Hprev_k).
      replace k with (0%nat + k)%nat by lia; rewrite (lookup_phi_subst_some 0%nat phis_ir k wn ce Hnp).
      destruct (cut_var_ptol ls k wn) eqn:Ept; [exfalso; exact (Hav k wn Hnw Ept wn Hfn) |].
      split; [reflexivity | exists (DVALUE_Base (@DVALUE_I Pa wn vi_mc)); split; [exact Hmc_k | split; [right; eexists; reflexivity | exact (Hprev_k eq_refl)]]]. }
  assert (Hinv_next : mc_cut_obl_inv_holds ls penv_mc_next dummy_freeze_oracle).
  { unfold mc_cut_obl_inv_holds; destruct (ml_inv ls) as [inv_e |] eqn:Emi; [| exact I].
    unfold wf_mc_loop_spec in Hwf; rewrite Emi, !andb_true_iff in Hwf.
    destruct Hwf as (((((((_ & _) & _) & _) & _) & _) & _) & ((_ & _) & Hlf_i) & _).
    rewrite (Hsubst_non_ptol inv_e Hlf_i Hinv_sub (fun k w _ Hpt => cut_var_ptol_inv_not_in ls k w inv_e Hpt Emi)).
    pose proof (Hmi eq_refl Hinv_p Hpath_p) as Href_i.
    cbn [refine_eou_dvalue eval_closed_cert_expr eval_cert_expr] in Href_i; rewrite repr_one_N in Href_i.
    destruct (eval_closed_cert_expr penv_mc_prev dummy_freeze_oracle (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
      as [| | | dv_i] eqn:Evi; try contradiction.
    destruct Href_i as [Hc | <-]; [discriminate Hc | reflexivity]. }
  assert (Hregs_next : forall rb, In rb (ml_regs ls) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle (mlr_expr rb) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb)))))) /\
    (mlr_width rb = 32%positive ->
       penv_mc_next (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (read_reg (mlr_reg rb)))))).
  { intros rb Hrb; split; [| exact (Hhi_lookup rb Hrb)].
    destruct (wf_mc_loop_reg_bind_props arch ls rb Hwf Hrb) as (Hw32_64 & _ & Hbw_rb & Hlf_rb & _).
    destruct (expr_is_ptol_var ls hdr_ws (mlr_expr rb)) eqn:Eptv.
    - apply expr_is_ptol_var_at_spec in Eptv as (k & w & _ & Hnw & He_eq & Hpt).
      rewrite Nat.sub_0_r in Hnw; rewrite He_eq in Hbw_rb |- *; cbn [cert_expr_bit_width] in Hbw_rb; subst w.
      pose proof (cut_var_ptol_count_split ls k (mlr_width rb) Hpt) as Hcnt.
      assert (Hle1 : (List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) (ml_regs ls)) <= 1)%nat) by lia.
      pose proof (find_ptol_reg_spec k (mlr_width rb) (ml_regs ls) rb Hle1 Hrb ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl, Pos.eqb_refl; reflexivity)) as Efnd.
      destruct (Forall2_nth_error_l_ex _ _ _ k (mlr_width rb) Hws Hnw) as [[wp ce] [Hnp <-]].
      destruct (Forall2_nth_error_l_ex _ _ _ k (mlr_width rb, ce) Hph Hnp) as [[id dv_ir] [Hndv _]].
      pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k (mlr_width rb) (mlr_width rb) ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
      rewrite Nat.add_0_l, Hpt, Efnd in Hin_mc.
      assert (Hpv : penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (read_reg (mlr_reg rb))))))).
      { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    - rewrite (Hsubst_non_ptol (mlr_expr rb) Hlf_rb (Hreg_sub rb Hrb)
                 (fun k w Hnw Hpt => expr_not_ptol_var_avoids_ptol ls hdr_ws (mlr_expr rb) k w Eptv Hnw Hpt (cut_var_ptol_reg_uses ls k w rb Hpt Hrb))).
      destruct (Hregs rb Hrb) as (e_mc64 & Ev_mc & Ho_r & Ho_d).
      destruct (Ho_d Eptv eq_refl Hinv_p Hpath_p) as [v_def Ev_def].
      pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
      cbn [refine_eou_dvalue] in Href_o; rewrite Ev_def, (trunc_mc_expr_to_sound _ _ (mlr_width rb) e_mc64 _ Hw32_64 Ev_mc) in Href_o.
      destruct Href_o as [Hpois | Heqv]; [discriminate Hpois | rewrite Heqv; exact Ev_def]. }
  assert (Hslts_next : forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
    eval_closed_cert_expr penv_mc_next dummy_freeze_oracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
  { intros off sz e Hs; destruct (wf_mc_loop_slot_bind_props arch ls off sz e Hwf Hs) as (_ & Hbw_s & Hlf_s & _).
    destruct (expr_is_ptol_var ls hdr_ws e) eqn:Eptv.
    - apply expr_is_ptol_var_at_spec in Eptv as (k & w & _ & Hnw & He_eq & Hpt).
      rewrite Nat.sub_0_r in Hnw; rewrite He_eq in Hbw_s |- *; cbn [cert_expr_bit_width] in Hbw_s; subst w.
      pose proof (cut_var_ptol_count_split ls k (mc_mem_bits sz) Hpt) as Hcnt.
      assert (Hreg0 : List.length (List.filter (fun r => expr_has_var (mc_cut_var_name k) (mlr_expr r)) (ml_regs ls)) = 0%nat).
      { pose proof (length_filter_ge1 (fun sb : mc_loop_slot_bind => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) (ml_slots ls) (MLS_Expr off sz e)
                      ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl; reflexivity) Hs) as Hgt; lia. }
      assert (Hle1 : (List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e0 => expr_has_var (mc_cut_var_name k) e0 | MLS_SavedReg _ _ => false end) (ml_slots ls)) <= 1)%nat) by lia.
      pose proof (find_ptol_reg_none_when_zero k (mc_mem_bits sz) (ml_regs ls) Hreg0) as Enr.
      pose proof (find_ptol_slot_spec k (mc_mem_bits sz) (ml_slots ls) off sz e Hle1 Hs
                    ltac:(rewrite He_eq; cbn; rewrite String.eqb_refl, Pos.eqb_refl; reflexivity)) as Efs.
      destruct (Forall2_nth_error_l_ex _ _ _ k (mc_mem_bits sz) Hws Hnw) as [[wp ce] [Hnp <-]].
      destruct (Forall2_nth_error_l_ex _ _ _ k (mc_mem_bits sz, ce) Hph Hnp) as [[id dv_ir] [Hndv _]].
      pose proof (build_cut_mc_binds_nth ls penv_mc_prev read_reg mstk 0%nat hdr_ws phis_ir dvs k (mc_mem_bits sz) (mc_mem_bits sz) ce id dv_ir Hnw Hnp Hndv) as Hin_mc.
      rewrite Nat.add_0_l, Hpt, Enr, Efs in Hin_mc.
      assert (Hpv : penv_mc_next (mc_cut_var_name k) = Some (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))).
      { unfold penv_mc_next; apply overlay_penv_lookup_in; [exact Hnd_mc | unfold mc_binds; apply in_or_app; left; exact Hin_mc]. }
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hpv; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    - rewrite (Hsubst_non_ptol e Hlf_s (Hslt_sub off sz e Hs)
                 (fun k w Hnw Hpt => expr_not_ptol_var_avoids_ptol ls hdr_ws e k w Eptv Hnw Hpt (cut_var_ptol_slot_uses ls k w off sz e Hpt Hs))).
      destruct (Hslts off sz e Hs) as (e_mc64 & Ev_mc & Ho_r & Ho_d).
      destruct (Ho_d Eptv eq_refl Hinv_p Hpath_p) as [v_def Ev_def].
      pose proof (Ho_r eq_refl Hinv_p Hpath_p) as Href_o.
      cbn [refine_eou_dvalue] in Href_o; rewrite Ev_def, (trunc_mc_slot_expr_sound _ _ sz e_mc64 _ Ev_mc) in Href_o.
      destruct Href_o as [Hpois | Heqv]; [discriminate Hpois | rewrite Heqv; exact Ev_def]. }
  split; [exact Hnb_next |].
  split; [exact Hmc_wf |].
  split; [exact Hctx_next |].
  split; [exact Hcut_ref |].
  split.
  { intros k id w dv Hnw Hndv; destruct (Hcut_facts k w Hnw) as (id0 & dv0 & _ & _ & _ & Hndv0 & Hir_k & Hsc_k & _).
    rewrite Hndv in Hndv0; inversion Hndv0; subst; split; assumption. }
  split; [exact Hinv_next |].
  split; [exact Hregs_next | exact Hslts_next].
Qed.

Lemma lmap_base_matches_next {Pa : Params} :
  forall allowed0 (penv0 penv_ir_prev penv_ir_next : param_env Pa)
         lmap_base lmap_cut dvs env_c hdr_phis wr_body,
    wf_pure_lmap allowed0 lmap_base ->
    (forall r w ce, RM.find r lmap_base = Some (w, ce) -> RM.find r lmap_cut = Some (w, ce)) ->
    lmap_matches_env penv_ir_prev lmap_cut env_c ->
    (forall nm w, In (nm, w) allowed0 -> penv_ir_next nm = penv_ir_prev nm) ->
    NoDup (List.map fst hdr_phis) ->
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs ->
    disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body) = true ->
    (forall k id w dv,
       nth_error hdr_phis k = Some (id, w) ->
       nth_error dvs k = Some (id, dv) ->
       penv_ir_next (mc_cut_var_name k) = Some dv /\ wf_scalar_dvalue w dv) ->
    lmap_matches_env penv_ir_next (wrap_cut_mc lmap_base hdr_phis) (apply_phi_env env_c dvs).
Proof.
  intros allowed0 penv0 penv_ir_prev penv_ir_next lmap_base lmap_cut dvs env_c hdr_phis wr_body
         Hwf_b Hsub Hlm Hagree Hnd_h Hids Hdisj Hphi.
  assert (Hlm_b : lmap_matches_env penv_ir_next lmap_base env_c).
  { apply (lmap_matches_env_penv_agree allowed0 penv_ir_prev penv_ir_next lmap_base env_c Hwf_b (fun nm w H => Logic.eq_sym (Hagree nm w H))).
    intros r w ce Hf; exact (Hlm r w ce (Hsub r w ce Hf)). }
  assert (Hdisj_h : forall r, In r (lmap_keys lmap_base) -> ~ In r (List.map fst hdr_phis)).
  { intros r Hr Hin; pose proof (disjoint_raw_ids_spec _ _ r Hdisj Hr) as Hn; apply Hn, in_or_app; left; exact Hin. }
  exact (wrap_cut_mc_at_matches penv_ir_next lmap_base 0%nat hdr_phis dvs env_c Hlm_b Hnd_h Hids Hdisj_h Hphi).
Qed.

(** Zero-ghost-var initialization helper for initial Entry obligations *)

Definition zero_ghost_binds {Pa : Params} (vs : list (string * positive))
  : list (string * @dvalue Pa) :=
  List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))) vs.

Lemma zero_ghost_binds_nodup {Pa : Params} :
  forall (ls : mc_loop_spec) (ws : list positive),
    NoDup (List.map mlr_reg (ml_regs ls)) ->
    NoDup (List.map fst (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat ws ++ hi32_vars ls))).
Proof.
  intros ls ws Hnd; unfold zero_ghost_binds.
  replace (List.map fst (List.map (fun '(nm, w) => (nm, DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))) (cut_vars_from_ws 0%nat ws ++ hi32_vars ls)))
    with (List.map fst (cut_vars_from_ws 0%nat ws ++ hi32_vars ls))
    by (clear; induction (cut_vars_from_ws 0%nat ws ++ hi32_vars ls) as [| [nm w] rest IH]; cbn; [reflexivity | f_equal; exact IH]).
  rewrite List.map_app; apply NoDup_app_intro.
  - clear; generalize 0%nat as idx; induction ws as [| w rw IH]; intro idx; cbn; [constructor |].
    constructor; [| exact (IH (S idx))].
    intro Hin; apply in_map_iff in Hin as [[nm w0] [Hfx Hc]]; cbn in Hfx; subst nm.
    apply cut_vars_from_ws_In in Hc as [k [Heq _]]; apply mc_cut_var_name_inj in Heq; lia.
  - clear ws; unfold hi32_vars in *; generalize dependent (ml_regs ls); intros rbs Hnd.
    induction rbs as [| rb rest IH]; cbn in *; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnr]; subst; destruct (Pos.eqb (mlr_width rb) 32%positive); cbn [app List.map]; [| exact (IH Hnr)].
    constructor; [| exact (IH Hnr)].
    intro Hin; cbn [fst] in Hin; apply in_map_iff in Hin as [[nm w0] [Hfx Hfl]]; cbn [fst] in Hfx; subst nm.
    apply in_flat_map in Hfl as [rb0 [Hrb0 Hhere]].
    destruct (Pos.eqb (mlr_width rb0) 32%positive); cbn in Hhere; [| contradiction].
    destruct Hhere as [Heq | []]; apply (f_equal fst) in Heq; cbn in Heq; apply mc_hi_var_name_inj in Heq.
    apply Hnin; rewrite <- Heq; apply in_map_iff; exists rb0; split; [reflexivity | exact Hrb0].
  - intros x Hxc Hxh.
    apply in_map_iff in Hxc as [[nm w] [Hfx Hc]]; cbn [fst] in Hfx; subst x.
    apply cut_vars_from_ws_In in Hc as [k [Heqc _]]; cbn [Nat.add] in Heqc; subst nm.
    apply in_map_iff in Hxh as [[nm0 w0] [Heq Hh]]; cbn [fst] in Heq; subst nm0.
    apply hi32_vars_In in Hh as [rb [_ [_ [Hdisj _]]]]; exact (mc_cut_hi_disjoint k (mlr_reg rb) Hdisj).
Qed.

Lemma zero_ghost_binds_bang {Pa : Params} :
  forall vs nm,
    In nm (List.map fst (@zero_ghost_binds Pa vs)) ->
    (forall x w, In (x, w) vs -> mc_starts_with_bang x = true) ->
    mc_starts_with_bang nm = true.
Proof.
  intros vs nm Hin Hvs; apply in_map_iff in Hin as [[x dv] [<- Hzm]].
  unfold zero_ghost_binds in Hzm; apply in_map_iff in Hzm as [[x0 w0] [Heq Hxin]]; inversion Heq; subst; exact (Hvs _ _ Hxin).
Qed.

Lemma zero_ghost_binds_wf_ctx {Pa : Params} :
  forall ls ws (penv0 : param_env Pa) allowed0 mc_init_ctx,
    wf_mc_loop_spec EA_Riscv64 ls = true \/ wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    let ghost := cut_vars_from_ws 0%nat ws ++ hi32_vars ls in
    let penv_ext := overlay_penv (@zero_ghost_binds Pa ghost) penv0 in
    (forall nm, mc_starts_with_bang nm = false -> penv_ext nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ ghost) penv_ext /\
    ub_ctx_holds penv_ext dummy_freeze_oracle (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost).
Proof.
  intros ls ws penv0 allowed0 mc_init_ctx Hwf Hnb Hpenv0 Hctx0 ghost penv_ext.
  assert (Hnd_r : NoDup (List.map mlr_reg (ml_regs ls))).
  { destruct Hwf as [Hw | Hw]; unfold wf_mc_loop_spec in Hw; rewrite !andb_true_iff in Hw;
      destruct Hw as (((((((_ & _) & _) & Hnd_b) & _) & _) & _) & _); exact (no_dup_N_to_NoDup _ Hnd_b). }
  assert (Hnd_g : NoDup (List.map fst (@zero_ghost_binds Pa ghost))) by exact (zero_ghost_binds_nodup ls ws Hnd_r).
  assert (Hgb : forall nm w, In (nm, w) ghost -> mc_starts_with_bang nm = true).
  { intros nm w Hg; unfold ghost in Hg; apply in_app_iff in Hg as [Hc | Hh].
    - apply cut_vars_from_ws_In in Hc as [k [-> _]]; reflexivity.
    - apply hi32_vars_In in Hh as (rb & _ & _ & -> & _); reflexivity. }
  assert (Hnb_ext : forall nm, mc_starts_with_bang nm = false -> penv_ext nm = penv0 nm).
  { intros nm Hnbm; apply overlay_penv_non_bang; [| exact Hnbm]; intros y Hy; exact (zero_ghost_binds_bang ghost y Hy Hgb). }
  assert (Hg_lk : forall nm w, In (nm, w) ghost -> penv_ext nm = Some (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w)))).
  { intros nm w Hg; unfold penv_ext; apply overlay_penv_lookup_in; [exact Hnd_g |].
    unfold zero_ghost_binds; apply in_map_iff; exists (nm, w); split; [reflexivity | exact Hg]. }
  repeat split; [exact Hnb_ext | |].
  - intros nm w Hin; apply in_app_iff in Hin as [Hal | Hg].
    + rewrite (Hnb_ext nm (Hnb nm w Hal)); exact (Hpenv0 nm w Hal).
    + exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))); split; [exact (Hg_lk nm w Hg) | right; eexists; reflexivity].
  - apply Forall_app; split; [exact (Hctx0 penv_ext Hnb_ext) |].
    apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hg]].
    cbn [ub_assumption_holds]; intros dv Hdv; rewrite (Hg_lk nm w Hg) in Hdv; inversion Hdv; discriminate.
Qed.

(** Common Loop Invariant Helper Checks on [prepare_mc_loop_ir] & [check_ls_exprs_vars] *)

Lemma check_ls_exprs_vars_split : forall allowed ls,
  check_ls_exprs_vars allowed ls = true ->
  AlgRules.vars_subset_b (collect_free_vars [] (match ml_inv ls with None => CE_BvConst 1%positive 1%N | Some inv => inv end)) allowed = true /\
  (forall rb, In rb (ml_regs ls) -> AlgRules.vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed = true) /\
  (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) -> AlgRules.vars_subset_b (collect_free_vars [] e) allowed = true).
Proof.
  intros allowed ls H; unfold check_ls_exprs_vars in H; rewrite !andb_true_iff in H; destruct H as [[Hr Hs] Hi].
  repeat split.
  - destruct (ml_inv ls); [exact Hi | reflexivity].
  - intros rb Hrb; rewrite forallb_forall in Hr; exact (Hr rb Hrb).
  - intros off sz e Hsl; rewrite forallb_forall in Hs; exact (Hs (MLS_Expr off sz e) Hsl).
Qed.

Definition rv_loop_sound_spec {Pa : Params}
  (ir_cfg : CFG.cfg dtyp) (insts : list decoded_rv_inst) (ret_w : positive)
  (ls : mc_loop_spec) (vs : list (@dvalue Pa)) (rf0 : rv_regfile) (mstk0 : mc_stack_mem) : Prop :=
  (forall fuel rf_end mstk_end,
     rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) ->
     rv_callee_saved_preserved rf0 rf_end /\
     rf_end 1%N = rf0 1%N /\
     exists sigma_ir,
       wf_draw_strat sigma_ir /\
       (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
        exists sigma_ir' env_out dv_ir,
          cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
            sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))) /\
  (forall k : nat,
     (exists fuel rf_end mstk_end,
        rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
     (exists n rf_k mstk_k,
        (k <= n)%nat /\
        rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf_k, mstk_k) /\
        rv_at_cut ls rf0 rf_k mstk_k)).

Definition a64_loop_sound_spec {Pa : Params}
  (ir_cfg : CFG.cfg dtyp) (insts : list decoded_a64_inst) (ret_w : positive)
  (ls : mc_loop_spec) (vs : list (@dvalue Pa))
  (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive) (fl0 : a64_flags) (mstk0 : mc_stack_mem) : Prop :=
  (forall fuel rf_end sp_end fl_end mstk_end,
     a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end) ->
     sp_end = sp0 /\
     a64_callee_saved_preserved rf0 rf_end /\
     exists sigma_ir,
       wf_draw_strat sigma_ir /\
       (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
        exists sigma_ir' env_out dv_ir,
          cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
            sigma_ir' env_out dv_ir /\
          dvalue_refines dv_ir
            (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))) /\
  (forall k : nat,
     (exists fuel rf_end sp_end fl_end mstk_end,
        a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
     (exists n rf_k sp_k fl_k mstk_k,
        (k <= n)%nat /\
        a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf_k, sp_k, fl_k, mstk_k) /\
        a64_at_cut ls sp0 rf0 rf_k sp_k mstk_k)).

Lemma init_param_lmap_dom : forall params pnames uses r w ce,
  RM.find r (init_param_lmap params pnames uses) = Some (w, ce) ->
  exists pnm, ce = CE_Var pnm w /\ In pnm pnames.
Proof.
  intros params pnames uses; induction uses as [| [idx dt] rest IH]; intros r w ce Hf.
  - cbn [init_param_lmap] in Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - destruct dt as [[w0 | | | | | | | | | |] | |]; cbn [init_param_lmap] in Hf;
      try exact (IH r w ce Hf).
    destruct (is_supported_bit_width w0); [| exact (IH r w ce Hf)].
    destruct (nth_error params idx) as [r0 |]; [| exact (IH r w ce Hf)].
    destruct (nth_error pnames idx) as [pnm |] eqn:Hpnm; [| exact (IH r w ce Hf)].
    destruct (starts_with_dollar pnm); [exact (IH r w ce Hf) |].
    destruct (RawIDOrd.eq_dec r0 r) as [<- | Hneq].
    + rewrite RMF.F.add_eq_o in Hf by reflexivity; inversion Hf; subst w0 ce.
      exists pnm; split; [reflexivity | exact (nth_error_In pnames idx Hpnm)].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (IH r w ce Hf).
Qed.

Theorem validate_mc_loop_rv64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (ls : mc_loop_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 mstk0,
    validate_mc_loop_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf = inr tt ->
    forallb inst_no_word_mulh insts = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv0 arg_specs rf0 ->
    rv_loop_sound_spec ir_cfg insts ret_w ls vs rf0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf arg_dtys vs penv0 rf0 mstk0
         Hval Hnmul Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hpu Hpenv_eq Hpenv0 Hctx0 Hargs_al Hsp0 Hm.
  unfold validate_mc_loop_rv64, build_mc_loop_bundle_rv64 in Hval.
  destruct (wf_mc_loop_spec EA_Riscv64 ls) eqn:Hwf; cbn [negb] in Hval; [| discriminate Hval].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  rewrite Hnmul in Hval; cbn [negb] in Hval.
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_args; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (prepare_mc_loop_ir ir_cfg allowed0 ls) as [prep |] eqn:Eprep; [| discriminate Hval].
  set (mc_fuel := S (2 * List.length insts)) in *.
  set (hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep)) in *.
  destruct (summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z (rv_build_init_val_regs 10%N arg_specs) [] ret_w)
    as [seg_ent |] eqn:Es_ent; [| discriminate Hval].
  destruct (summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w)
    as [seg_body |] eqn:Es_body; [| discriminate Hval].
  destruct (summarize_rv64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w)
    as [seg_skel |] eqn:Es_skel; [| discriminate Hval].
  destruct (mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_ent) &&
            mc_skel_tree_ok EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel)) eqn:Hok_both;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Hok_both as [Hok_ent Hok_skel].
  destruct (check_mc_loop_obls _ _ _ _ opt_pf) eqn:Hchk; [| discriminate Hval].
  clear Hval.
  (* Unpack prepare_mc_loop_ir *)
  unfold prepare_mc_loop_ir in Eprep.
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  set (bmap := ocfg_map (blks ir_cfg)) in *.
  destruct (find_hdr_block_id (ml_ir_header ls) (blks ir_cfg)) as [hdr_id |] eqn:Ehid; [| discriminate Eprep].
  destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Eprep].
  destruct (extract_hdr_phis (blk_phis b_hdr)) as [hdr_phis |] eqn:Ehp; [| discriminate Eprep].
  destruct (no_dup_raw_ids (List.map fst hdr_phis)) eqn:Hnd_hp_b; cbn [negb] in Eprep; [| discriminate Eprep].
  apply no_dup_raw_ids_spec in Hnd_hp_b.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg)) in *.
  set (ir_fuel := S (List.length (blks ir_cfg) + 1)) in *.
  destruct (ir_seg_written_ids ir_fuel bmap hdr_id false [] (init ir_cfg)) as [wr_ent |] eqn:Ewre; [| discriminate Eprep].
  destruct (reify_ir_seg ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init)
    as [t_ir_ent |] eqn:Ere_ent; [| discriminate Eprep].
  set (lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_ent)) in *.
  set (lmap_cut := wrap_cut_mc lmap_base hdr_phis) in *.
  destruct (ir_seg_written_ids ir_fuel bmap hdr_id true [] hdr_id) as [wr_body |] eqn:Ewrb; [| discriminate Eprep].
  destruct (reify_ir_seg ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut)
    as [t_ir_body |] eqn:Ere_body; [| discriminate Eprep].
  destruct (disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body) &&
            ir_seg_freeze_free t_ir_ent &&
            ir_seg_freeze_free t_ir_body &&
            check_ls_exprs_vars (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls) eqn:Echk_ir; [| discriminate Eprep].
  inversion Eprep; subst prep; clear Eprep; cbn [mlip_hdr_phis mlip_t_ir_entry mlip_t_ir_body] in *.
  rewrite !andb_true_iff in Echk_ir; destruct Echk_ir as (((Hdisj_b & Hnf_ent) & Hnf_bdy) & Hls_vars).
  rewrite cut_vars_from_eq_ws in Hls_vars; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hls_vars.
  destruct (check_ls_exprs_vars_split _ _ Hls_vars) as (Hinv_sub & Hreg_sub & Hslt_sub).
  (* Typing & agreement for lmap_init and lmap_base *)
  assert (Hwf_li : wf_pure_lmap allowed0 lmap_init) by exact (init_param_lmap_typing _ _ _ _ Hpu).
  assert (Hwf_te : ir_seg_wf allowed0 hdr_ws t_ir_ent) by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ Hwf_li Ere_ent).
  assert (Hwf_lb : wf_pure_lmap allowed0 lmap_base) by exact (common_cut_lmap_wf _ _ _ Hwf_li (proj1 Hwf_te)).
  assert (Hwf_lc : wf_pure_lmap (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) lmap_cut).
  { change hdr_ws with (extract_hdr_phi_widths hdr_phis); rewrite <- (cut_vars_from_eq_ws 0%nat hdr_phis); exact (wrap_cut_mc_at_wf 0%nat allowed0 lmap_base hdr_phis Hwf_lb). }
  assert (Hwf_tb : ir_seg_wf (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) hdr_ws t_ir_body)
    by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ Hwf_lc Ere_body).
  (* Initial entry ghost extension & obligations *)
  destruct (zero_ghost_binds_wf_ctx ls hdr_ws penv0 allowed0 mc_init_ctx (or_introl Hwf) Hnb_al Hpenv0 Hctx0)
    as (Hnb_ext & Hpenv_ext & Hctx_ext).
  set (penv_ext := overlay_penv (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) penv0) in *.
  cbn [mlcb_ctx mlcb_known mlcb_obls] in Hchk; rewrite cut_vars_from_eq_ws in Hchk; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hchk.
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ penv_ext dummy_freeze_oracle false Hchk Hpenv_ext Hctx_ext) as Hobls_all_ent.
  rewrite Forall_app in Hobls_all_ent; destruct Hobls_all_ent as [Hobls_ent _].
  assert (Hpenv_ext_ref : forall nm w, In (nm, w) allowed0 ->
    exists d1 d2 : @dvalue Pa, penv_ext nm = Some d1 /\ penv_ext nm = Some d2 /\ wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; destruct (Hpenv0 nm w Hin) as [d0 [Hp0 Hw0]]; rewrite (Hnb_ext nm (Hnb_al nm w Hin)).
    exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl. }
  assert (Hinit_len : List.length (args ir_cfg) = List.length vs).
  { pose proof (Forall2_length Hty); lia. }
  assert (Hcomp_n : forall idx dt, In (idx, dt) (param_idx_uses_cfg ir_cfg) -> nth_error arg_dtys idx = Some dt)
    by (intros idx dt Hin; exact (cfg_param_dtyp_compatible_nth _ _ idx dt Hcomp Hin)).
  assert (Hlm_init_dom : forall r w ce, RM.find r lmap_init = Some (w, ce) ->
    exists pnm, ce = CE_Var pnm w /\ In pnm ir_pnames)
    by (intros r w ce Hf; exact (init_param_lmap_dom _ _ _ _ _ _ Hf)).
  assert (Hlm_init_ext : lmap_matches_env penv_ext lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (param_idx_uses_cfg ir_cfg) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnd_a Hnd_s Hinit_len (eq_trans Hlen_s Hinit_len) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (Hlm_init_dom r w ce Hf) as [pnm [-> Hinp]].
    destruct (Hwf_li r w (CE_Var pnm w) Hf) as (_ & _ & _ & Hfv).
    pose proof (Hfv (pnm, w) (or_introl eq_refl)) as Hal.
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *.
    rewrite (Hnb_ext pnm (Hnb_al pnm w Hal)), (Hpenv_eq pnm Hinp); exact Hsc. }
  assert (Hm_ext : rv_rf_matches_args penv_ext arg_specs rf0).
  { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
    pose proof (Hargs_al sp (nth_error_In arg_specs k Hnth)) as Hal_sp.
    exists v; split; [rewrite (Hnb_ext _ (Hnb_al _ _ Hal_sp)); exact Hp | exact Hmt]. }
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  assert (Hrng : (- mc_frame_cap <= ml_sp_off ls <= 0)%Z) by exact (wf_mc_loop_spec_sp_bounds _ _ Hwf).
  assert (Hdisj_b_wr : disjoint_raw_ids (lmap_keys lmap_base) wr_body = true).
  { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
    pose proof (Hdisj_b x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
    destruct (raw_id_in_list x wr_body) eqn:Exb; [| reflexivity].
    rewrite raw_id_in_list_spec in Exb.
    assert (Htru : raw_id_in_list x (List.map fst hdr_phis ++ wr_body) = true)
      by (apply raw_id_in_list_spec, in_or_app; right; exact Exb).
    rewrite Htru in Hnx; discriminate Hnx. }
  assert (Hdisj_e_nil : disjoint_raw_ids (@nil raw_id) wr_ent = true) by reflexivity.
  assert (Hsp2_init : rv_val_read 2%N (rv_build_init_val_regs 10%N arg_specs) = MSV_StackPtr 0%Z).
  { unfold rv_val_read; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  assert (Hskel_bwd : forall fuel rf mstk rf_end mstk_end,
    rv_at_cut ls rf0 rf mstk ->
    rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N).
  { intros fuel rf mstk rf_end mstk_end Hat Hmem.
    exact (@rv_skel_backward_sound Pa insts ret_w ls seg_skel rf0 fuel fuel rf mstk rf_end mstk_end
             (Nat.le_refl fuel) Hwf Hrw Hnmul Hsp0 Es_skel Hok_skel Hat Hmem). }
  assert (Hentry_skel_bwd : forall fuel rf_end mstk_end,
    rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) ->
    rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N).
  { intros fuel rf_end mstk_end Hmem.
    pose proof (summarize_rv64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hs_ent.
    apply rv_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & _ & Hsteps & _ & Hsp2' & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & mstk_e & Hme & Hcs & Hra & _))].
    - destruct (rv_exec_mem_split_steps n fuel insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0
                  (ml_mc_pc ls) rf' mstk' (rf_end, mstk_end) Hmem Hsteps) as [_ Hrem].
      apply (Hskel_bwd (fuel - n)%nat rf' mstk' rf_end mstk_end); [| exact Hrem].
      repeat split.
      + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
        unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - pose proof (rv_exec_mem_det fuel fuel_end insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; assumption. }
  assert (Hentry_skel_fwd :
    (exists fuel rf_end mstk_end, rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
    (exists n rf' mstk', rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf', mstk') /\ rv_at_cut ls rf0 rf' mstk')).
  { pose proof (summarize_rv64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hs_ent.
    apply rv_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_Riscv64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & mstk' & _ & Hsteps & _ & Hsp2' & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & mstk_e & Hme & _))].
    - right; exists n, rf', mstk'; split; [exact Hsteps | repeat split].
      + specialize (Hag' 2%N); rewrite Hsp2' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
        unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - left; exists fuel_end, rf_e, mstk_e; exact Hme. }
  set (rv_cut_inv := fun (env_c : rmap (@dvalue Pa)) (bid_c : block_id) (dvs : list (raw_id * @dvalue Pa))
                         (penv_ir penv_mc : param_env Pa) (rf : rv_regfile) (mstk : mc_stack_mem) =>
    ir_at_cut bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c /\
    pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
    lmap_matches_env penv_ir lmap_cut (apply_phi_env env_c dvs) /\
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
    rv_at_cut ls rf0 rf mstk /\
    (forall nm, mc_starts_with_bang nm = false -> penv_ir nm = penv0 nm /\ penv_mc nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc /\
    ub_ctx_holds penv_mc dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    mc_cut_obl_inv_holds ls penv_mc dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))))).
  assert (Hentry_step :
    cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
    (exists fuel_end rf_end mstk_end env_out dv_ir,
       rv_exec_mem fuel_end insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end))))) \/
    (exists n rf1 mstk1 env_c bid_c dvs penv_ir1 penv_mc1,
       rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf1, mstk1) /\
       rv_cut_inv env_c bid_c dvs penv_ir1 penv_mc1 rf1 mstk1)).
  { pose proof (reify_ir_seg_sound ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init
                  [] wr_ent penv_ext (init_cfg_locals (args ir_cfg) vs) (init_cfg_locals (args ir_cfg) vs)
                  t_ir_ent Ewre Hdisj_e_nil (conj eq_refl Hlm_init_ext) Ere_ent) as Hir_ent.
    pose proof (summarize_rv64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (rv_build_init_val_regs 10%N arg_specs) [] ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 rf0 mstk0 Hrw Hnmul Hsp0 ltac:(unfold mc_frame_cap; lia)
                  Hsp2_init (rv_init_val_regs_agrees penv_ext dummy_freeze_oracle arg_specs rf0 Hws Hm_ext)
                  (mc_sym_stack_agrees_empty _ _ _ _ _) Es_ent) as Hmc_ent.
    apply rv_seg_exec_to_mc in Hmc_ent.
    destruct (collect_mc_ir_obls_sound EA_Riscv64 ls ret_w hdr_ws allowed0 false penv_ext penv_ext
                bmap hdr_id hdr_phis [] (init_cfg_locals (args ir_cfg) vs) (init ir_cfg) (init ir_cfg) t_ir_ent
                _ _ (rv_seg_to_mc_seg seg_ent) (ml_inv ls) [] eq_refl Hwf_te Hnf_ent Hpenv_ext_ref
                Hir_ent Hmc_ent (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ent)
      as [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & mstk_e & Hme & Hcs & Hra & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c & bid_c & b_hdr0 & dvs & lmap_cut0 & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & Hin_lm & Hlm_m & _ & Hstp & Hids & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf1 & mstk1 & _ & Hst_mc & _ & Hsp2' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact (Hub default_draw_strat).
    - right; left; exists fuel_e, rf_e, mstk_e, env_out, dv_ir.
      split; [exact Hme | split; [exact Hcs | split; [exact Hra | split]]].
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact Hst.
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat1 : rv_at_cut ls rf0 rf1 mstk1).
      { repeat split.
        - specialize (Hag' 2%N); rewrite Hsp2', Hsp' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
          pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
          unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                      off MS_8 false astk' mstk1 (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf1))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk1 off sz false))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                      off sz false astk' mstk1 (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_Riscv64 ls allowed0 mc_init_ctx penv0 penv_ext penv_ext
                  hdr_ws phis_ir dvs (fun r => rv_read_reg r rf1) mstk1 (ml_inv ls) false []
                  Hwf Hnb_al Hpenv0 Hctx0 (fun nm Hnb => conj (Hnb_ext nm Hnb) (Hnb_ext nm Hnb))
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin))
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpwf_m)
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpenv_ext_ref) Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb_1 & Hwf_mc1 & Hctx1 & Href1 & Hphi1 & Hmi1 & Hregs1 & Hslts1).
      set (penv_ir1 := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs) penv0) in *.
      set (penv_mc1 := overlay_penv (build_cut_mc_binds ls penv_ext (fun r => rv_read_reg r rf1) mstk1 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds (fun r => rv_read_reg r rf1) (ml_regs ls)) penv0) in *.
      assert (Hlm_next1 : lmap_matches_env penv_ir1 lmap_cut (apply_phi_env env_c dvs)).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ext penv_ir1 lmap_base lmap_cut0 dvs env_c hdr_phis wr_body
                 Hwf_lb (fun r w ce Hf => common_cut_lmap_in lmap_init (collect_entry_cut_lmaps t_ir_ent) lmap_cut0 Hin_lm r w ce Hf)
                 Hlm_m (fun nm w Hal => eq_trans (proj1 (Hnb_1 nm (Hnb_al nm w Hal))) (Logic.eq_sym (Hnb_ext nm (Hnb_al nm w Hal))))
                 Hnd_hp_b Hids Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi1 k id w dv Hnw Hndv). }
      right; right; exists n, rf1, mstk1, env_c, bid_c, dvs, penv_ir1, penv_mc1.
      split; [exact Hst_mc |].
      unfold rv_cut_inv.
      split; [destruct Htau as [[-> [-> ->]] | Htau]; [left; repeat split; reflexivity | right; exact Htau] |].
      split; [exact Hstp | split; [exact Hlm_next1 | split; [exact Hids | split; [exact Hat1 |]]]].
      split; [exact Hnb_1 | split; [exact Hwf_mc1 | split; [exact Hctx1 | split; [exact Href1 | split; [exact Hmi1 | split; [exact Hregs1 | exact Hslts1]]]]]]. }
  assert (Hbody_step : forall env_c bid_c dvs penv_ir penv_mc rf mstk,
    rv_cut_inv env_c bid_c dvs penv_ir penv_mc rf mstk ->
    (cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)) \/
    (exists fuel_end rf_end mstk_end env_out dv_ir,
       rv_exec_mem fuel_end insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
       rv_callee_saved_preserved rf0 rf_end /\
       rf_end 1%N = rf0 1%N /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end))))) \/
    (exists n rf' mstk' env_c' bid_c' dvs' penv_ir' penv_mc',
       (1 <= n)%nat /\
       rv_exec_steps n insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk = Some (ml_mc_pc ls, rf', mstk') /\
       rv_cut_inv env_c' bid_c' dvs' penv_ir' penv_mc' rf' mstk')).
  { intros env_c bid_c dvs penv_ir penv_mc rf mstk
           (Hcut & Hstp_p & Hlm_c & Hids & Hat & Hnb_c & Hwf_mc & Hctx_c & Href_c & Hmi_c & Hregs_c & Hslts_c).
    assert (Hpres_phi : forall r, In r (lmap_keys lmap_base) -> RM.find r (apply_phi_env env_c dvs) = RM.find r env_c).
    { intros r Hr; apply apply_phi_env_preserves_not_in.
      intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr), in_or_app; left.
      clear -Hids Hin; revert dvs Hids Hin; induction hdr_phis as [| [i0 w0] rp IH];
        intros [| [i1 d1] rd] H2 Hin; cbn in *; try inversion H2; [contradiction |].
      destruct Hin as [Heq | Hr]; [left; subst; congruence | right; exact (IH rd H5 Hr)]. }
    assert (Hre_body_c : reify_ir_seg ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut = Some t_ir_body)
      by (rewrite (reify_ir_seg_req_step_bid_from_irrel ir_fuel bmap hdr_id hdr_phis [] bid_c hdr_id hdr_id lmap_cut); exact Ere_body).
    pose proof (reify_ir_seg_sound ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut
                  (lmap_keys lmap_base) wr_body penv_ir env_c (apply_phi_env env_c dvs) t_ir_body
                  Ewrb Hdisj_b_wr (ex_intro _ b_hdr (conj Ebh (conj Hstp_p (conj Hpres_phi Hlm_c)))) Hre_body_c) as Hir_body.
    destruct Hat as [Hsp_r [Hunsp_r Hsav_r]].
    pose proof (summarize_rv64_seg_sound mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                  (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w seg_body
                  penv_mc dummy_freeze_oracle rf0 rf mstk Hrw Hnmul Hsp0 Hrng (rv_cut_vrf_sp ls Hwfb)
                  (rv_cut_vrf_agrees penv_mc dummy_freeze_oracle ls rf0 rf Hwf Hsp_r Hrng Hunsp_r Hregs_c)
                  (build_cut_astk_agrees penv_mc dummy_freeze_oracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0) (ml_slots ls) mstk Hslts_c Hsav_r)
                  Es_body) as Hmc_body.
    apply rv_seg_exec_to_mc in Hmc_body.
    pose proof (check_mc_loop_obls_sound _ _ _ _ _ penv_mc dummy_freeze_oracle true Hchk Hwf_mc Hctx_c) as Hobls_all_b.
    rewrite Forall_app in Hobls_all_b; destruct Hobls_all_b as [_ Hobls_b].
    destruct (collect_mc_ir_obls_sound EA_Riscv64 ls ret_w hdr_ws (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) true penv_ir penv_mc
                bmap hdr_id hdr_phis (lmap_keys lmap_base) env_c bid_c hdr_id t_ir_body
                _ _ (rv_seg_to_mc_seg seg_body) (ml_inv ls) [] eq_refl Hwf_tb Hnf_bdy Href_c
                Hir_body Hmc_body (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_b)
      as [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & mstk_e & Hme & Hcs & Hra & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c' & bid_c' & b_hdr0 & dvs' & lmap_cut' & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & _ & Hlm_m & Hkp_lb & Hstp & Hids' & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf' & mstk' & Hn & Hst_mc & _ & Hsp2' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
      exact (ir_at_cut_ub bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c default_draw_strat Hcut (Hub default_draw_strat)).
    - right; left; exists fuel_e, rf_e, mstk_e, env_out, dv_ir; repeat split; try assumption.
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
        exact (ir_at_cut_ret bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_out dv_ir Hcut Hst).
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat' : rv_at_cut ls rf0 rf' mstk').
      { repeat split.
        - specialize (Hag' 2%N); rewrite Hsp2', Hsp' in Hag'; cbn [mc_sym_val_agrees] in Hag'; exact (proj2 Hag').
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr.
          pose proof (rv_unspilled_preserved_nonzero ls r Hr) as Hnz.
          unfold rv_read_reg in Hagr; destruct (N.eqb r 0%N) eqn:E0; [apply N.eqb_eq in E0; contradiction | exact Hagr].
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                                      off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf'))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk' off sz false))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                      off sz false astk' mstk' (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_Riscv64 ls allowed0 mc_init_ctx penv0 penv_ir penv_mc
                  hdr_ws phis_ir dvs' (fun r => rv_read_reg r rf') mstk' (ml_inv ls) true []
                  Hwf Hnb_al Hpenv0 Hctx0 Hnb_c
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin))
                  Hpwf_m Href_c Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb' & Hwf_mc' & Hctx' & Href' & Hphi' & Hmi' & Hregs' & Hslts').
      set (penv_ir' := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs') penv0) in *.
      set (penv_mc' := overlay_penv (build_cut_mc_binds ls penv_mc (fun r => rv_read_reg r rf') mstk' 0%nat hdr_ws phis_ir dvs' ++ build_hi32_binds (fun r => rv_read_reg r rf') (ml_regs ls)) penv0) in *.
      assert (Hlm_env_c' : lmap_matches_env penv_ir lmap_base env_c').
      { intros r w ce Hf; assert (Hr_k : In r (lmap_keys lmap_base)) by (apply in_lmap_keys_iff; eexists; exact Hf).
        assert (Hnf_h : ~ In r (List.map fst hdr_phis)) by (intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr_k), in_or_app; left; exact Hin).
        assert (Hf_cut : RM.find r lmap_cut = Some (w, ce)) by (unfold lmap_cut, wrap_cut_mc; rewrite wrap_cut_mc_at_preserves by exact Hnf_h; exact Hf).
        destruct (Hlm_c r w ce Hf_cut) as (dv0 & He0 & Hs0 & Hrm0); exists dv0; repeat split; try assumption.
        rewrite (Hkp_lb r Hr_k), <- Hpres_phi by exact Hr_k; exact He0. }
      assert (Hlm_next' : lmap_matches_env penv_ir' lmap_cut (apply_phi_env env_c' dvs')).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ir penv_ir' lmap_base lmap_base dvs' env_c' hdr_phis wr_body
                 Hwf_lb (fun r w ce H => H) Hlm_env_c'
                 (fun nm w Hal => eq_trans (proj1 (Hnb' nm (Hnb_al nm w Hal))) (Logic.eq_sym (proj1 (Hnb_c nm (Hnb_al nm w Hal)))))
                 Hnd_hp_b Hids' Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi' k id w dv Hnw Hndv). }
      right; right; exists n, rf', mstk', env_c', bid_c', dvs', penv_ir', penv_mc'.
      split; [exact (Hn eq_refl) | split; [exact Hst_mc |]].
      unfold rv_cut_inv.
      split; [exact (ir_at_cut_step bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_c' bid_c' Hcut Htau) |].
      split; [exact Hstp | split; [exact Hlm_next' | split; [exact Hids' | split; [exact Hat' |]]]].
      split; [exact Hnb' | split; [exact Hwf_mc' | split; [exact Hctx' | split; [exact Href' | split; [exact Hmi' | split; [exact Hregs' | exact Hslts']]]]]]. }
  split.
  - (* Part 1: Backward partial correctness *)
    assert (Hbwd_cut : forall n_max fuel rf mstk env_c bid_c dvs penv_ir penv_mc rf_end mstk_end,
      (fuel <= n_max)%nat ->
      rv_cut_inv env_c bid_c dvs penv_ir penv_mc rf mstk ->
      rv_exec_mem fuel insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) ->
      rv_callee_saved_preserved rf0 rf_end /\ rf_end 1%N = rf0 1%N /\
      exists sigma_ir,
        wf_draw_strat sigma_ir /\
        (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
         exists sigma_ir' env_out dv_ir,
           cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
             sigma_ir' env_out dv_ir /\
           dvalue_refines dv_ir
             (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))))).
    { intros n_max; induction n_max as [| n_max' IH];
        intros fuel rf mstk env_c bid_c dvs penv_ir penv_mc rf_end mstk_end Hle Hinv Hmem.
      - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [rv_exec_mem] in Hmem; discriminate Hmem.
      - destruct (Hbody_step env_c bid_c dvs penv_ir penv_mc rf mstk Hinv)
          as [Hub | [(fuel_e & rf_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hra & Hst & Href)
                    | (n1 & rf1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hn1 & Hst1 & Hinv1)]].
        + destruct (Hskel_bwd fuel rf mstk rf_end mstk_end (proj1 (proj2 (proj2 (proj2 (proj2 Hinv))))) Hmem) as [Hcs Hra].
          split; [exact Hcs | split; [exact Hra | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
        + pose proof (rv_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) (rv_read_reg 2%N rf0) rf mstk _ _ Hmem Hme) as Heq.
          inversion Heq; subst rf_e mstk_e.
          split; [exact Hcs | split; [exact Hra | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
        + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) (ml_mc_pc ls) rf mstk
                      (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
          exact (IH (fuel - n1)%nat rf1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end mstk_end ltac:(lia) Hinv1 Hrem). }
    intros fuel rf_end mstk_end Hmem.
    destruct (Hentry_skel_bwd fuel rf_end mstk_end Hmem) as [Hcs0 Hra0].
    destruct Hentry_step as [Hub | [(fuel_e & rf_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hra & Hst & Href)
                                  | (n1 & rf1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hst1 & Hinv1)]].
    + split; [exact Hcs0 | split; [exact Hra0 | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
    + pose proof (rv_exec_mem_det fuel fuel_e insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst rf_e mstk_e.
      split; [exact Hcs0 | split; [exact Hra0 | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
    + destruct (rv_exec_mem_split_steps n1 fuel insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0
                  (ml_mc_pc ls) rf1 mstk1 (rf_end, mstk_end) Hmem Hst1) as [_ Hrem].
      exact (Hbwd_cut (fuel - n1)%nat (fuel - n1)%nat rf1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end mstk_end (Nat.le_refl _) Hinv1 Hrem).
  - (* Part 2: Arbitrary-depth forward progress *)
    assert (Hfwd_aux : forall k : nat,
      (exists fuel rf_end mstk_end, rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end)) \/
      (exists n rf_k mstk_k, (k <= n)%nat /\ rv_exec_steps n insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 = Some (ml_mc_pc ls, rf_k, mstk_k) /\ rv_at_cut ls rf0 rf_k mstk_k)).
    { induction k as [| k' IH].
      - destruct Hentry_skel_fwd as [(f0 & rfe & me & Hmem) | (n0 & rf1 & mstk1 & Hst1 & Hat1)].
        + left; exists f0, rfe, me; exact Hmem.
        + right; exists n0, rf1, mstk1; split; [lia | split; assumption].
      - destruct IH as [(f0 & rfe & me & Hmem) | (n0 & rfk & mstkk & Hle & Hst0 & Hatk)];
          [left; exists f0, rfe, me; exact Hmem |].
        destruct (@rv_skel_step Pa insts ret_w ls seg_skel rf0 rfk mstkk Hwf Hrw Hnmul Hsp0 Es_skel Hok_skel Hatk)
          as [(fe & rfe & me & Hme & _ & _) | (n1 & rf1 & mstk1 & Hn1 & Hst1 & Hat1)].
        + left; exists (n0 + fe)%nat, rfe, me; exact (rv_exec_steps_to_exec_mem n0 fe insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 (ml_mc_pc ls) rfk mstkk (rfe, me) Hst0 Hme).
        + right; exists (n0 + n1)%nat, rf1, mstk1; split; [lia | split; [exact (rv_exec_steps_trans n0 n1 insts (rv_read_reg 2%N rf0) 0%N rf0 mstk0 (ml_mc_pc ls) rfk mstkk (ml_mc_pc ls, rf1, mstk1) Hst0 Hst1) | exact Hat1]]. }
    exact Hfwd_aux.
Qed.

Lemma a64_init_arg_expr_vars : forall sp,
  is_let_free_expr (a64_init_arg_expr sp) = true /\
  (forall nm w,
     In (nm, w) (collect_free_vars [] (a64_init_arg_expr sp)) ->
     (nm = ras_name sp /\ w = ras_width sp) \/
     ((ras_width sp =? 64)%positive = false /\ nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive)).
Proof.
  intros sp; unfold a64_init_arg_expr.
  destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64.
  - cbn [is_let_free_expr collect_free_vars]; split; [reflexivity |].
    intros nm w [Heq | []]; inversion Heq; left; split; reflexivity.
  - destruct (Pos.eqb (ras_width sp) 32%positive) eqn:E32.
    + cbn [is_let_free_expr collect_free_vars]; split; [reflexivity |].
      intros nm w [Heq | [Heq | []]]; inversion Heq;
        [left; split; reflexivity | right; repeat split; try assumption; reflexivity].
    + destruct (ras_ext sp); cbn [is_let_free_expr collect_free_vars]; split; try reflexivity;
        intros nm w [Heq | [Heq | []]]; inversion Heq;
        [left; split; reflexivity | right; repeat split; try assumption; reflexivity
        | left; split; reflexivity | right; repeat split; try assumption; reflexivity
        | left; split; reflexivity | right; repeat split; try assumption; reflexivity].
Qed.

Lemma a64_build_init_val_regs_vars : forall idx specs r e,
  a64_val_read r (a64_build_init_val_regs idx specs) = MSV_Expr e ->
  is_let_free_expr e = true /\
  (forall nm w,
     In (nm, w) (collect_free_vars [] e) ->
     exists sp,
       In sp specs /\
       ((nm = ras_name sp /\ w = ras_width sp) \/
        ((ras_width sp =? 64)%positive = false /\ nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive))).
Proof.
  intros idx specs; revert idx; induction specs as [| sp rest IH];
    intros idx r e Hrd; unfold a64_val_read in Hrd;
    destruct (N.leb 31%N r) eqn:Er31.
  - inversion Hrd; subst; split; [reflexivity | intros nm w []].
  - cbn [a64_build_init_val_regs] in Hrd; unfold a64_empty_val_regs in Hrd; rewrite Er31 in Hrd.
    destruct (a64_is_callee_saved r); discriminate Hrd.
  - inversion Hrd; subst; split; [reflexivity | intros nm w []].
  - cbn [a64_build_init_val_regs] in Hrd; destruct (N.eqb r idx) eqn:Eeq.
    + inversion Hrd; subst e; destruct (a64_init_arg_expr_vars sp) as [Hlf Hfv].
      split; [exact Hlf | intros nm w Hin; exists sp; split; [left; reflexivity | exact (Hfv nm w Hin)]].
    + assert (Hrd' : a64_val_read r (a64_build_init_val_regs (N.succ idx) rest) = MSV_Expr e)
        by (unfold a64_val_read; rewrite Er31; exact Hrd).
      destruct (IH (N.succ idx) r e Hrd') as [Hlf Hfv].
      split; [exact Hlf | intros nm w Hin; destruct (Hfv nm w Hin) as [sp0 [Hin0 Hcase]]; exists sp0; split; [right; exact Hin0 | exact Hcase]].
Qed.

Theorem validate_mc_loop_a64_sound {Pa : Params} :
  forall (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
         (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
         (ls : mc_loop_spec) (opt_pf : option (list lrat_step))
         arg_dtys vs (penv0 : param_env Pa) rf0 sp0 fl0 mstk0,
    validate_mc_loop_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf = inr tt ->
    forallb a64_inst_valid insts = true ->
    NoDup (args ir_cfg) ->
    NoDup (List.map cert_reg_name (args ir_cfg)) ->
    List.length (List.map cert_reg_name (args ir_cfg)) = List.length (args ir_cfg) ->
    List.length arg_dtys = List.length (args ir_cfg) ->
    cfg_param_dtyp_compatible ir_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
       In (idx, DTYPE_Base (DTYPE_I w)) (param_idx_uses_cfg ir_cfg) ->
       nth_error (List.map cert_reg_name (args ir_cfg)) idx = Some pnm ->
       In (pnm, w) allowed0) ->
    (forall nm, In nm (List.map cert_reg_name (args ir_cfg)) ->
       penv0 nm = build_param_env (List.map cert_reg_name (args ir_cfg)) vs nm) ->
    (forall sp, In sp arg_specs ->
       penv0 (a64_hi_var_name (ras_name sp)) =
       a64_extend_penv_with_hi (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 (a64_hi_var_name (ras_name sp))) ->
    wf_param_env_for allowed0 penv0 ->
    (forall penv' : param_env Pa,
       (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv0 nm) ->
       ub_ctx_holds penv' dummy_freeze_oracle mc_init_ctx) ->
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed0) ->
    (forall nv, In nv (a64_hi_vars arg_specs) -> In nv allowed0) ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    (forall sp, In sp arg_specs -> penv0 (ras_name sp) = build_param_env (List.map cert_reg_name (args ir_cfg)) vs (ras_name sp)) ->
    mc_valid_sp0 sp0 ->
    a64_rf_matches_args (build_param_env (List.map cert_reg_name (args ir_cfg)) vs) arg_specs rf0 ->
    a64_loop_sound_spec ir_cfg insts ret_w ls vs rf0 sp0 fl0 mstk0.
Proof.
  intros ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls opt_pf arg_dtys vs penv0 rf0 sp0 fl0 mstk0
         Hval Hval_a64 Hnd_a Hnd_s Hlen_s Hlen_ad Hcomp Hty Hpu Hpenv_eq Hhi_eq Hpenv0 Hctx0 Hargs_al Hhi_al Hnd_mc Hdis_args Hnames_p Hsp0 Hm.
  unfold validate_mc_loop_a64, build_mc_loop_bundle_a64 in Hval.
  destruct (wf_mc_loop_spec EA_AArch64 ls) eqn:Hwf; cbn [negb] in Hval; [| discriminate Hval].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hval; [| discriminate Hval].
  rewrite Hval_a64 in Hval; cbn [negb] in Hval.
  destruct (Nat.leb (List.length arg_specs) 8) eqn:Hlen_args; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb orb] in Hval; [| discriminate Hval].
  destruct (prepare_mc_loop_ir ir_cfg allowed0 ls) as [prep |] eqn:Eprep; [| discriminate Hval].
  set (mc_fuel := S (2 * List.length insts)) in *.
  set (hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep)) in *.
  destruct (summarize_a64_seg mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w)
    as [seg_ent |] eqn:Es_ent; [| discriminate Hval].
  destruct (summarize_a64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w)
    as [seg_body |] eqn:Es_body; [| discriminate Hval].
  destruct (summarize_a64_seg mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls) (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w)
    as [seg_skel |] eqn:Es_skel; [| discriminate Hval].
  destruct (mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_ent) &&
            mc_skel_tree_ok EA_AArch64 ls (a64_seg_to_mc_seg seg_skel)) eqn:Hok_both;
    cbn [negb] in Hval; [| discriminate Hval].
  apply andb_true_iff in Hok_both as [Hok_ent Hok_skel].
  destruct (check_mc_loop_obls _ _ _ _ opt_pf) eqn:Hchk; [| discriminate Hval].
  clear Hval.
  unfold prepare_mc_loop_ir in Eprep.
  destruct (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) eqn:Hnb_al_b;
    cbn [negb] in Eprep; [| discriminate Eprep].
  assert (Hnb_al : forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false).
  { intros nm w Hin; rewrite forallb_forall in Hnb_al_b; pose proof (Hnb_al_b (nm, w) Hin) as Hn; apply negb_true_iff in Hn; exact Hn. }
  set (bmap := ocfg_map (blks ir_cfg)) in *.
  destruct (find_hdr_block_id (ml_ir_header ls) (blks ir_cfg)) as [hdr_id |] eqn:Ehid; [| discriminate Eprep].
  destruct (RM.find hdr_id bmap) as [b_hdr |] eqn:Ebh; [| discriminate Eprep].
  destruct (extract_hdr_phis (blk_phis b_hdr)) as [hdr_phis |] eqn:Ehp; [| discriminate Eprep].
  destruct (no_dup_raw_ids (List.map fst hdr_phis)) eqn:Hnd_hp_b; cbn [negb] in Eprep; [| discriminate Eprep].
  apply no_dup_raw_ids_spec in Hnd_hp_b.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg)) in *.
  set (ir_fuel := S (List.length (blks ir_cfg) + 1)) in *.
  destruct (ir_seg_written_ids ir_fuel bmap hdr_id false [] (init ir_cfg)) as [wr_ent |] eqn:Ewre; [| discriminate Eprep].
  destruct (reify_ir_seg ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init)
    as [t_ir_ent |] eqn:Ere_ent; [| discriminate Eprep].
  set (lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_ent)) in *.
  set (lmap_cut := wrap_cut_mc lmap_base hdr_phis) in *.
  destruct (ir_seg_written_ids ir_fuel bmap hdr_id true [] hdr_id) as [wr_body |] eqn:Ewrb; [| discriminate Eprep].
  destruct (reify_ir_seg ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut)
    as [t_ir_body |] eqn:Ere_body; [| discriminate Eprep].
  destruct (disjoint_raw_ids (lmap_keys lmap_base) (List.map fst hdr_phis ++ wr_body) &&
            ir_seg_freeze_free t_ir_ent &&
            ir_seg_freeze_free t_ir_body &&
            check_ls_exprs_vars (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls) eqn:Echk_ir; [| discriminate Eprep].
  inversion Eprep; subst prep; clear Eprep; cbn [mlip_hdr_phis mlip_t_ir_entry mlip_t_ir_body] in *.
  rewrite !andb_true_iff in Echk_ir; destruct Echk_ir as (((Hdisj_b & Hnf_ent) & Hnf_bdy) & Hls_vars).
  rewrite cut_vars_from_eq_ws in Hls_vars; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hls_vars.
  destruct (check_ls_exprs_vars_split _ _ Hls_vars) as (Hinv_sub & Hreg_sub & Hslt_sub).
  assert (Hwf_li : wf_pure_lmap allowed0 lmap_init) by exact (init_param_lmap_typing _ _ _ _ Hpu).
  assert (Hwf_te : ir_seg_wf allowed0 hdr_ws t_ir_ent) by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ Hwf_li Ere_ent).
  assert (Hwf_lb : wf_pure_lmap allowed0 lmap_base) by exact (common_cut_lmap_wf _ _ _ Hwf_li (proj1 Hwf_te)).
  assert (Hwf_lc : wf_pure_lmap (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) lmap_cut).
  { change hdr_ws with (extract_hdr_phi_widths hdr_phis); rewrite <- (cut_vars_from_eq_ws 0%nat hdr_phis); exact (wrap_cut_mc_at_wf 0%nat allowed0 lmap_base hdr_phis Hwf_lb). }
  assert (Hwf_tb : ir_seg_wf (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) hdr_ws t_ir_body)
    by exact (reify_ir_seg_wf _ _ _ _ _ _ _ _ _ _ _ Hwf_lc Ere_body).
  destruct (zero_ghost_binds_wf_ctx ls hdr_ws penv0 allowed0 mc_init_ctx (or_intror Hwf) Hnb_al Hpenv0 Hctx0)
    as (Hnb_ext & Hpenv_ext & Hctx_ext).
  set (penv_ext := overlay_penv (@zero_ghost_binds Pa (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) penv0) in *.
  cbn [mlcb_ctx mlcb_known mlcb_obls] in Hchk; rewrite cut_vars_from_eq_ws in Hchk; change (extract_hdr_phi_widths hdr_phis) with hdr_ws in Hchk.
  pose proof (check_mc_loop_obls_sound _ _ _ _ _ penv_ext dummy_freeze_oracle false Hchk Hpenv_ext Hctx_ext) as Hobls_all_ent.
  rewrite Forall_app in Hobls_all_ent; destruct Hobls_all_ent as [Hobls_ent _].
  assert (Hpenv_ext_ref : forall nm w, In (nm, w) allowed0 ->
    exists d1 d2 : @dvalue Pa, penv_ext nm = Some d1 /\ penv_ext nm = Some d2 /\ wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2).
  { intros nm w Hin; destruct (Hpenv0 nm w Hin) as [d0 [Hp0 Hw0]]; rewrite (Hnb_ext nm (Hnb_al nm w Hin)).
    exists d0, d0; repeat split; try assumption; apply dvalue_refines_refl. }
  assert (Hinit_len : List.length (args ir_cfg) = List.length vs) by (pose proof (Forall2_length Hty); lia).
  assert (Hcomp_n : forall idx dt, In (idx, dt) (param_idx_uses_cfg ir_cfg) -> nth_error arg_dtys idx = Some dt)
    by (intros idx dt Hin; exact (cfg_param_dtyp_compatible_nth _ _ idx dt Hcomp Hin)).
  assert (Hlm_init_dom : forall r w ce, RM.find r lmap_init = Some (w, ce) -> exists pnm, ce = CE_Var pnm w /\ In pnm ir_pnames)
    by (intros r w ce Hf; exact (init_param_lmap_dom _ _ _ _ _ _ Hf)).
  assert (Hlm_init_ext : lmap_matches_env penv_ext lmap_init (init_cfg_locals (args ir_cfg) vs)).
  { pose proof (init_param_lmap_matches (param_idx_uses_cfg ir_cfg) (args ir_cfg) ir_pnames arg_dtys vs
                  Hnd_a Hnd_s Hinit_len (eq_trans Hlen_s Hinit_len) Hty Hcomp_n) as Hbase.
    intros r w ce Hf; destruct (Hbase r w ce Hf) as (dv & Hev & Hsc & Hrm).
    destruct (Hlm_init_dom r w ce Hf) as [pnm [-> Hinp]].
    destruct (Hwf_li r w (CE_Var pnm w) Hf) as (_ & _ & _ & Hfv).
    pose proof (Hfv (pnm, w) (or_introl eq_refl)) as Hal.
    exists dv; repeat split; try assumption.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val] in *.
    rewrite (Hnb_ext pnm (Hnb_al pnm w Hal)), (Hpenv_eq pnm Hinp); exact Hsc. }
  assert (Ha64_init_agrees :
    a64_val_regs_agrees penv_ext dummy_freeze_oracle rf0 sp0 (a64_build_init_val_regs 0%N arg_specs) rf0).
  { set (penv_hi := a64_extend_penv_with_hi (build_param_env ir_pnames vs) arg_specs rf0).
    pose proof (a64_init_val_regs_agrees (build_param_env ir_pnames vs) dummy_freeze_oracle arg_specs rf0 sp0 Hws Hnd_mc Hdis_args Hm) as Hbase.
    fold penv_hi in Hbase.
    intro r; pose proof (Hbase r) as Hr; destruct (a64_val_read r (a64_build_init_val_regs 0%N arg_specs)) as [| e_arg | |] eqn:Erd;
      try exact Hr.
    cbn [mc_sym_val_agrees] in Hr |- *.
    rewrite <- Hr; symmetry; apply eval_cert_expr_penv_eq_if_vars;
      destruct (a64_build_init_val_regs_vars 0%N arg_specs r e_arg Erd) as [Hlf Hfv]; [exact Hlf |].
    intros nm wn Hfn.
    destruct (Hfv nm wn Hfn) as [sp [Hin [[-> ->] | [Hw64 [-> ->]]]]].
    - pose proof (Hargs_al sp Hin) as Hal.
      rewrite (Hnb_ext _ (Hnb_al _ _ Hal)), (Hnames_p sp Hin).
      unfold penv_hi, a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
      intros sp1 Hin1 Heq; apply (Hdis_args sp1 Hin1); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hin].
    - assert (Hhi_in : In (a64_hi_var_name (ras_name sp), 64%positive) (a64_hi_vars arg_specs))
        by (unfold a64_hi_vars; apply in_flat_map; exists sp; split; [exact Hin | rewrite Hw64; left; reflexivity]).
      pose proof (Hhi_al _ Hhi_in) as Hal.
      rewrite (Hnb_ext _ (Hnb_al _ _ Hal)), (Hhi_eq sp Hin); reflexivity. }
  assert (Hsp0_eq : sp0 = @Integers.add 64%positive sp0 (@Integers.repr 64%positive 0%Z))
    by (change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive); rewrite Integers.add_zero; reflexivity).
  assert (Hwfb : forallb (wf_mc_loop_reg_bind EA_AArch64) (ml_regs ls) = true).
  { unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf; destruct Hwf as (((((((_ & _) & _) & _) & Hwbr) & _) & _) & _); exact Hwbr. }
  assert (Hrng : (- mc_frame_cap <= ml_sp_off ls <= 0)%Z) by exact (wf_mc_loop_spec_sp_bounds _ _ Hwf).
  assert (Hdisj_b_wr : disjoint_raw_ids (lmap_keys lmap_base) wr_body = true).
  { unfold disjoint_raw_ids in *; rewrite forallb_forall in *; intros x Hx.
    pose proof (Hdisj_b x Hx) as Hnx; apply negb_true_iff in Hnx; apply negb_true_iff.
    destruct (raw_id_in_list x wr_body) eqn:Exb; [| reflexivity].
    rewrite raw_id_in_list_spec in Exb.
    assert (Htru : raw_id_in_list x (List.map fst hdr_phis ++ wr_body) = true)
      by (apply raw_id_in_list_spec, in_or_app; right; exact Exb).
    rewrite Htru in Hnx; discriminate Hnx. }
  assert (Hdisj_e_nil : disjoint_raw_ids (@nil raw_id) wr_ent = true) by reflexivity.
  assert (Hskel_bwd : forall fuel rf sp fl mstk rf_end sp_end fl_end mstk_end,
    a64_at_cut ls sp0 rf0 rf sp mstk ->
    a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end).
  { intros fuel rf sp fl mstk rf_end sp_end fl_end mstk_end Hat Hmem.
    exact (@a64_skel_backward_sound Pa insts ret_w ls seg_skel rf0 sp0 fuel fuel rf sp fl mstk rf_end sp_end fl_end mstk_end
             (Nat.le_refl fuel) Hwf Hrw Hval_a64 Hsp0 Es_skel Hok_skel Hat Hmem). }
  assert (Hentry_skel_bwd : forall fuel rf_end sp_end fl_end mstk_end,
    a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end) ->
    sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end).
  { intros fuel rf_end sp_end fl_end mstk_end Hmem.
    pose proof (summarize_a64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hs_ent.
    apply a64_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp_c & fl_c & mstk' & _ & Hsteps & _ & Hsp_c & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & fl_e & mstk_e & Hme & Hcs & _))].
    - destruct (a64_exec_mem_split_steps n fuel insts sp0 0%N rf0 sp0 fl0 mstk0
                  (ml_mc_pc ls) rf' sp_c fl_c mstk' (rf_end, sp_end, fl_end, mstk_end) Hmem Hsteps) as [_ Hrem].
      apply (Hskel_bwd (fuel - n)%nat rf' sp_c fl_c mstk' rf_end sp_end fl_end mstk_end); [| exact Hrem].
      repeat split; [exact Hsp_c | |].
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - pose proof (a64_exec_mem_det fuel fuel_end insts 0%N sp0 rf0 sp0 fl0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | exact Hcs]. }
  assert (Hentry_skel_fwd :
    (exists fuel rf_end sp_end fl_end mstk_end, a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
    (exists n rf' sp' fl' mstk', a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\ a64_at_cut ls sp0 rf0 rf' sp' mstk')).
  { pose proof (summarize_a64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hs_ent.
    apply a64_seg_exec_to_mc in Hs_ent.
    destruct (mc_skel_tree_ok_extract EA_AArch64 ls penv_ext dummy_freeze_oracle _ _ _ Hok_ent Hs_ent)
      as [(sp' & rr' & astk' & -> & Hrr' & Hstk' & (n & rf' & sp_c & fl_c & mstk' & _ & Hsteps & _ & Hsp_c & Hag' & Hastk'))
         | (ret_e & (fuel_end & rf_e & fl_e & mstk_e & Hme & _))].
    - right; exists n, rf', sp_c, fl_c, mstk'; split; [exact Hsteps | repeat split; try assumption].
      + intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hrr' r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
      + intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                    off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hstk' off r Hr)) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exact Hsld.
    - left; exists fuel_end, rf_e, sp0, fl_e, mstk_e; exact Hme. }
  set (a64_cut_inv := fun (env_c : rmap (@dvalue Pa)) (bid_c : block_id) (dvs : list (raw_id * @dvalue Pa))
                          (penv_ir penv_mc : param_env Pa) (rf : a64_regfile) (sp : @Integers.bit_int 64%positive) (mstk : mc_stack_mem) =>
    ir_at_cut bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c /\
    pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
    lmap_matches_env penv_ir lmap_cut (apply_phi_env env_c dvs) /\
    Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
    a64_at_cut ls sp0 rf0 rf sp mstk /\
    (forall nm, mc_starts_with_bang nm = false -> penv_ir nm = penv0 nm /\ penv_mc nm = penv0 nm) /\
    wf_param_env_for (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls) penv_mc /\
    ub_ctx_holds penv_mc dummy_freeze_oracle
      (mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) (cut_vars_from_ws 0%nat hdr_ws ++ hi32_vars ls)) /\
    (forall nm w, In (nm, w) (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) ->
       exists d1 d2 : @dvalue Pa, penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) /\
    mc_cut_obl_inv_holds ls penv_mc dummy_freeze_oracle /\
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv_mc (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
    (forall off sz e, In (MLS_Expr off sz e) (ml_slots ls) ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz) (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))))).
  assert (Hentry_step :
    cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
    (exists fuel_end rf_end fl_end mstk_end env_out dv_ir,
       a64_exec_mem fuel_end insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end))))) \/
    (exists n rf1 sp1 fl1 mstk1 env_c bid_c dvs penv_ir1 penv_mc1,
       a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf1, sp1, fl1, mstk1) /\
       a64_cut_inv env_c bid_c dvs penv_ir1 penv_mc1 rf1 sp1 mstk1)).
  { pose proof (reify_ir_seg_sound ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init
                  [] wr_ent penv_ext (init_cfg_locals (args ir_cfg) vs) (init_cfg_locals (args ir_cfg) vs)
                  t_ir_ent Ewre Hdisj_e_nil (conj eq_refl Hlm_init_ext) Ere_ent) as Hir_ent.
    pose proof (summarize_a64_seg_sound mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                  (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w seg_ent
                  penv_ext dummy_freeze_oracle rf0 sp0 rf0 sp0 fl0 mstk0 Hrw Hval_a64 Hsp0
                  ltac:(unfold mc_frame_cap; lia) Hsp0_eq Ha64_init_agrees (mc_sym_stack_agrees_empty _ _ _ _ _)
                  (fun C => ltac:(discriminate C)) Es_ent) as Hmc_ent.
    apply a64_seg_exec_to_mc in Hmc_ent.
    destruct (collect_mc_ir_obls_sound EA_AArch64 ls ret_w hdr_ws allowed0 false penv_ext penv_ext
                bmap hdr_id hdr_phis [] (init_cfg_locals (args ir_cfg) vs) (init ir_cfg) (init ir_cfg) t_ir_ent
                _ _ (a64_seg_to_mc_seg seg_ent) (ml_inv ls) [] eq_refl Hwf_te Hnf_ent Hpenv_ext_ref
                Hir_ent Hmc_ent (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_ent)
      as [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c & bid_c & b_hdr0 & dvs & lmap_cut0 & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & Hin_lm & Hlm_m & _ & Hstp & Hids & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf1 & sp1 & fl1 & mstk1 & _ & Hst_mc & _ & Hsp_c & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact (Hub default_draw_strat).
    - right; left; exists fuel_e, rf_e, fl_e, mstk_e, env_out, dv_ir.
      split; [exact Hme | split; [exact Hcs | split]].
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)); exact Hst.
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat1 : a64_at_cut ls sp0 rf0 rf1 sp1 mstk1).
      { repeat split.
        - rewrite Hsp_c, Hsp'; reflexivity.
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                      off MS_8 false astk' mstk1 (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf1))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_ext dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk1 off sz false))) /\
        mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Refine false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_ext dummy_freeze_oracle (ml_inv ls) false (MLO_Defined false [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_ext dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                      off sz false astk' mstk1 (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_AArch64 ls allowed0 mc_init_ctx penv0 penv_ext penv_ext
                  hdr_ws phis_ir dvs (fun r => a64_read_reg r rf1) mstk1 (ml_inv ls) false []
                  Hwf Hnb_al Hpenv0 Hctx0 (fun nm Hnb => conj (Hnb_ext nm Hnb) (Hnb_ext nm Hnb))
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun C => ltac:(discriminate C)) (fun _ _ Hin => ltac:(contradiction Hin))
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpwf_m)
                  ltac:(cbn [cut_vars_from_ws]; rewrite app_nil_r; exact Hpenv_ext_ref) Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb_1 & Hwf_mc1 & Hctx1 & Href1 & Hphi1 & Hmi1 & Hregs1 & Hslts1).
      set (penv_ir1 := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs) penv0) in *.
      set (penv_mc1 := overlay_penv (build_cut_mc_binds ls penv_ext (fun r => a64_read_reg r rf1) mstk1 0%nat hdr_ws phis_ir dvs ++ build_hi32_binds (fun r => a64_read_reg r rf1) (ml_regs ls)) penv0) in *.
      assert (Hlm_next1 : lmap_matches_env penv_ir1 lmap_cut (apply_phi_env env_c dvs)).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ext penv_ir1 lmap_base lmap_cut0 dvs env_c hdr_phis wr_body
                 Hwf_lb (fun r w ce Hf => common_cut_lmap_in lmap_init (collect_entry_cut_lmaps t_ir_ent) lmap_cut0 Hin_lm r w ce Hf)
                 Hlm_m (fun nm w Hal => eq_trans (proj1 (Hnb_1 nm (Hnb_al nm w Hal))) (Logic.eq_sym (Hnb_ext nm (Hnb_al nm w Hal))))
                 Hnd_hp_b Hids Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi1 k id w dv Hnw Hndv). }
      right; right; exists n, rf1, sp1, fl1, mstk1, env_c, bid_c, dvs, penv_ir1, penv_mc1.
      split; [exact Hst_mc |].
      unfold a64_cut_inv.
      split; [destruct Htau as [[-> [-> ->]] | Htau]; [left; repeat split; reflexivity | right; exact Htau] |].
      split; [exact Hstp | split; [exact Hlm_next1 | split; [exact Hids | split; [exact Hat1 |]]]].
      split; [exact Hnb_1 | split; [exact Hwf_mc1 | split; [exact Hctx1 | split; [exact Href1 | split; [exact Hmi1 | split; [exact Hregs1 | exact Hslts1]]]]]]. }
  assert (Hbody_step : forall env_c bid_c dvs penv_ir penv_mc rf sp fl mstk,
    a64_cut_inv env_c bid_c dvs penv_ir penv_mc rf sp mstk ->
    (cfg_steps_to_ub default_draw_strat (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)) \/
    (exists fuel_end rf_end fl_end mstk_end env_out dv_ir,
       a64_exec_mem fuel_end insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
       a64_callee_saved_preserved rf0 rf_end /\
       pure_cfg_steps (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) env_out dv_ir /\
       dvalue_refines dv_ir (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end))))) \/
    (exists n rf' sp' fl' mstk' env_c' bid_c' dvs' penv_ir' penv_mc',
       (1 <= n)%nat /\
       a64_exec_steps n insts sp0 (ml_mc_pc ls) rf sp fl mstk = Some (ml_mc_pc ls, rf', sp', fl', mstk') /\
       a64_cut_inv env_c' bid_c' dvs' penv_ir' penv_mc' rf' sp' mstk')).
  { intros env_c bid_c dvs penv_ir penv_mc rf sp fl mstk
           (Hcut & Hstp_p & Hlm_c & Hids & Hat & Hnb_c & Hwf_mc & Hctx_c & Href_c & Hmi_c & Hregs_c & Hslts_c).
    assert (Hpres_phi : forall r, In r (lmap_keys lmap_base) -> RM.find r (apply_phi_env env_c dvs) = RM.find r env_c).
    { intros r Hr; apply apply_phi_env_preserves_not_in.
      intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr), in_or_app; left.
      clear -Hids Hin; revert dvs Hids Hin; induction hdr_phis as [| [i0 w0] rp IH];
        intros [| [i1 d1] rd] H2 Hin; cbn in *; try inversion H2; [contradiction |].
      destruct Hin as [Heq | Hr]; [left; subst; congruence | right; exact (IH rd H5 Hr)]. }
    assert (Hre_body_c : reify_ir_seg ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut = Some t_ir_body)
      by (rewrite (reify_ir_seg_req_step_bid_from_irrel ir_fuel bmap hdr_id hdr_phis [] bid_c hdr_id hdr_id lmap_cut); exact Ere_body).
    pose proof (reify_ir_seg_sound ir_fuel bmap hdr_id hdr_phis true [] bid_c hdr_id lmap_cut
                  (lmap_keys lmap_base) wr_body penv_ir env_c (apply_phi_env env_c dvs) t_ir_body
                  Ewrb Hdisj_b_wr (ex_intro _ b_hdr (conj Ebh (conj Hstp_p (conj Hpres_phi Hlm_c)))) Hre_body_c) as Hir_body.
    destruct Hat as [Hsp_r [Hunsp_r Hsav_r]].
    pose proof (summarize_a64_seg_sound mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                  (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w seg_body
                  penv_mc dummy_freeze_oracle rf0 sp0 rf sp fl mstk Hrw Hval_a64 Hsp0 Hrng Hsp_r
                  (a64_cut_vrf_agrees penv_mc dummy_freeze_oracle ls rf0 sp0 rf Hwf Hunsp_r Hregs_c)
                  (build_cut_astk_agrees penv_mc dummy_freeze_oracle (fun k => a64_read_reg k rf0) sp0 (ml_slots ls) mstk Hslts_c Hsav_r)
                  (fun C => ltac:(discriminate C)) Es_body) as Hmc_body.
    apply a64_seg_exec_to_mc in Hmc_body.
    pose proof (check_mc_loop_obls_sound _ _ _ _ _ penv_mc dummy_freeze_oracle true Hchk Hwf_mc Hctx_c) as Hobls_all_b.
    rewrite Forall_app in Hobls_all_b; destruct Hobls_all_b as [_ Hobls_b].
    destruct (collect_mc_ir_obls_sound EA_AArch64 ls ret_w hdr_ws (allowed0 ++ cut_vars_from_ws 0%nat hdr_ws) true penv_ir penv_mc
                bmap hdr_id hdr_phis (lmap_keys lmap_base) env_c bid_c hdr_id t_ir_body
                _ _ (a64_seg_to_mc_seg seg_body) (ml_inv ls) [] eq_refl Hwf_tb Hnf_bdy Href_c
                Hir_body Hmc_body (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin)) Hobls_b)
      as [Hub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & (fuel_e & rf_e & fl_e & mstk_e & Hme & Hcs & Hev_mc) & Hev_mc2 & Href_d)
                | (env_c' & bid_c' & b_hdr0 & dvs' & lmap_cut' & phis_ir & sp' & rr' & astk' &
                   Htau & Ebh0 & _ & Hlm_m & Hkp_lb & Hstp & Hids' & Hws_m & Hpwf_m & Hph_m & Hsp' &
                   (n & rf' & sp_c' & fl_c' & mstk' & Hn & Hst_mc & _ & Hsp_c' & Hag' & Hastk') &
                   Hunsp & Hphi_d & Hregs_o & Hsav & Hslts_o & Hmi_o)]].
    - left; change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
      exact (ir_at_cut_ub bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c default_draw_strat Hcut (Hub default_draw_strat)).
    - right; left; exists fuel_e, rf_e, fl_e, mstk_e, env_out, dv_ir; repeat split; try assumption.
      + change (denote_cfg ir_cfg None) with (denote_cfg_from bmap None (init ir_cfg, init ir_cfg)).
        exact (ir_at_cut_ret bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_out dv_ir Hcut Hst).
      + rewrite Hev_mc in Hev_mc2; inversion Hev_mc2; subst dv_mc; exact Href_d.
    - rewrite Ebh in Ebh0; inversion Ebh0; subst b_hdr0.
      assert (Hat' : a64_at_cut ls sp0 rf0 rf' sp_c' mstk').
      { repeat split.
        - rewrite Hsp_c', Hsp'; reflexivity.
        - intros r Hr; pose proof (Hag' r) as Hagr; rewrite (Hunsp r Hr) in Hagr; cbn [mc_sym_val_agrees] in Hagr; exact Hagr.
        - intros off r Hr; pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                                      off MS_8 false astk' mstk' (MSV_SavedReg r) Hastk' (Hsav off r Hr)) as Hsld.
          cbn [mc_sym_val_agrees] in Hsld; exact Hsld. }
      assert (Hregs_ev : forall rb, In rb (ml_regs ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf'))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))).
      { intros rb Hrb; destruct (Hregs_o rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d).
        pose proof (Hag' (mlr_reg rb)) as Hagr; rewrite Err in Hagr; cbn [mc_sym_val_agrees] in Hagr.
        exists e_mc64; split; [exact Hagr | split; assumption]. }
      assert (Hslts_ev : forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64,
        eval_closed_cert_expr penv_mc dummy_freeze_oracle e_mc64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk' off sz false))) /\
        mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Refine true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
        (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle (ml_inv ls) true (MLO_Defined true [] (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))).
      { intros off sz e_s Hs; destruct (Hslts_o off sz e_s Hs) as (e_mc64 & Eld & Ho_r & Ho_d).
        pose proof (mc_sym_stk_load_sound penv_mc dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0
                      off sz false astk' mstk' (MSV_Expr e_mc64) Hastk' Eld) as Hsld.
        cbn [mc_sym_val_agrees] in Hsld; exists e_mc64; split; [exact Hsld | split; assumption]. }
      destruct (@build_next_cut_penvs_sound Pa EA_AArch64 ls allowed0 mc_init_ctx penv0 penv_ir penv_mc
                  hdr_ws phis_ir dvs' (fun r => a64_read_reg r rf') mstk' (ml_inv ls) true []
                  Hwf Hnb_al Hpenv0 Hctx0 Hnb_c
                  Hinv_sub Hreg_sub Hslt_sub Hws_m Hph_m (fun _ => Hmi_c) (fun _ _ Hin => ltac:(contradiction Hin))
                  Hpwf_m Href_c Hphi_d Hregs_ev Hslts_ev Hmi_o)
        as (Hnb' & Hwf_mc' & Hctx' & Href' & Hphi' & Hmi' & Hregs' & Hslts').
      set (penv_ir' := overlay_penv (build_cut_ir_binds 0%nat hdr_ws dvs') penv0) in *.
      set (penv_mc' := overlay_penv (build_cut_mc_binds ls penv_mc (fun r => a64_read_reg r rf') mstk' 0%nat hdr_ws phis_ir dvs' ++ build_hi32_binds (fun r => a64_read_reg r rf') (ml_regs ls)) penv0) in *.
      assert (Hlm_env_c' : lmap_matches_env penv_ir lmap_base env_c').
      { intros r w ce Hf; assert (Hr_k : In r (lmap_keys lmap_base)) by (apply in_lmap_keys_iff; eexists; exact Hf).
        assert (Hnf_h : ~ In r (List.map fst hdr_phis)) by (intro Hin; apply (disjoint_raw_ids_spec _ _ r Hdisj_b Hr_k), in_or_app; left; exact Hin).
        assert (Hf_cut : RM.find r lmap_cut = Some (w, ce)) by (unfold lmap_cut, wrap_cut_mc; rewrite wrap_cut_mc_at_preserves by exact Hnf_h; exact Hf).
        destruct (Hlm_c r w ce Hf_cut) as (dv0 & He0 & Hs0 & Hrm0); exists dv0; repeat split; try assumption.
        rewrite (Hkp_lb r Hr_k), <- Hpres_phi by exact Hr_k; exact He0. }
      assert (Hlm_next' : lmap_matches_env penv_ir' lmap_cut (apply_phi_env env_c' dvs')).
      { apply (lmap_base_matches_next allowed0 penv0 penv_ir penv_ir' lmap_base lmap_base dvs' env_c' hdr_phis wr_body
                 Hwf_lb (fun r w ce H => H) Hlm_env_c'
                 (fun nm w Hal => eq_trans (proj1 (Hnb' nm (Hnb_al nm w Hal))) (Logic.eq_sym (proj1 (Hnb_c nm (Hnb_al nm w Hal)))))
                 Hnd_hp_b Hids' Hdisj_b).
        intros k id w dv Hnh Hndv; assert (Hnw : nth_error hdr_ws k = Some w) by (unfold hdr_ws, extract_hdr_phi_widths; rewrite nth_error_map, Hnh; reflexivity); exact (Hphi' k id w dv Hnw Hndv). }
      right; right; exists n, rf', sp_c', fl_c', mstk', env_c', bid_c', dvs', penv_ir', penv_mc'.
      split; [exact (Hn eq_refl) | split; [exact Hst_mc |]].
      unfold a64_cut_inv.
      split; [exact (ir_at_cut_step bmap (init ir_cfg) hdr_id (init_cfg_locals (args ir_cfg) vs) env_c bid_c env_c' bid_c' Hcut Htau) |].
      split; [exact Hstp | split; [exact Hlm_next' | split; [exact Hids' | split; [exact Hat' |]]]].
      split; [exact Hnb' | split; [exact Hwf_mc' | split; [exact Hctx' | split; [exact Href' | split; [exact Hmi' | split; [exact Hregs' | exact Hslts']]]]]]. }
  split.
  - assert (Hbwd_cut : forall n_max fuel rf sp fl mstk env_c bid_c dvs penv_ir penv_mc rf_end sp_end fl_end mstk_end,
      (fuel <= n_max)%nat ->
      a64_cut_inv env_c bid_c dvs penv_ir penv_mc rf sp mstk ->
      a64_exec_mem fuel insts (ml_mc_pc ls) sp0 rf sp fl mstk = Some (rf_end, sp_end, fl_end, mstk_end) ->
      sp_end = sp0 /\ a64_callee_saved_preserved rf0 rf_end /\
      exists sigma_ir,
        wf_draw_strat sigma_ir /\
        (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
         exists sigma_ir' env_out dv_ir,
           cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
             sigma_ir' env_out dv_ir /\
           dvalue_refines dv_ir
             (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))).
    { intros n_max; induction n_max as [| n_max' IH];
        intros fuel rf sp fl mstk env_c bid_c dvs penv_ir penv_mc rf_end sp_end fl_end mstk_end Hle Hinv Hmem.
      - assert (Hf0 : fuel = 0%nat) by lia; subst fuel; cbn [a64_exec_mem] in Hmem; discriminate Hmem.
      - destruct (Hbody_step env_c bid_c dvs penv_ir penv_mc rf sp fl mstk Hinv)
          as [Hub | [(fuel_e & rf_e & fl_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hst & Href)
                    | (n1 & rf1 & sp1 & fl1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hn1 & Hst1 & Hinv1)]].
        + destruct (Hskel_bwd fuel rf sp fl mstk rf_end sp_end fl_end mstk_end (proj1 (proj2 (proj2 (proj2 (proj2 Hinv))))) Hmem) as [Hspe Hcs].
          split; [exact Hspe | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
        + pose proof (a64_exec_mem_det fuel fuel_e insts (ml_mc_pc ls) sp0 rf sp fl mstk _ _ Hmem Hme) as Heq.
          inversion Heq; subst; split; [reflexivity | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
        + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 (ml_mc_pc ls) rf sp fl mstk
                      (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [Hlt Hrem].
          exact (IH (fuel - n1)%nat rf1 sp1 fl1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end sp_end fl_end mstk_end ltac:(lia) Hinv1 Hrem). }
    intros fuel rf_end sp_end fl_end mstk_end Hmem.
    destruct (Hentry_skel_bwd fuel rf_end sp_end fl_end mstk_end Hmem) as [Hspe0 Hcs0].
    destruct Hentry_step as [Hub | [(fuel_e & rf_e & fl_e & mstk_e & env_out & dv_ir & Hme & Hcs & Hst & Href)
                                  | (n1 & rf1 & sp1 & fl1 & mstk1 & env_c1 & bid_c1 & dvs1 & penv_ir1 & penv_mc1 & Hst1 & Hinv1)]].
    + split; [exact Hspe0 | split; [exact Hcs0 | exists default_draw_strat; split; [exact default_draw_strat_wf | left; exact Hub]]].
    + pose proof (a64_exec_mem_det fuel fuel_e insts 0%N sp0 rf0 sp0 fl0 mstk0 _ _ Hmem Hme) as Heq.
      inversion Heq; subst; split; [reflexivity | split; [exact Hcs | exists default_draw_strat; split; [exact default_draw_strat_wf | right; exists default_draw_strat, env_out, dv_ir; split; [apply pure_cfg_to_cfg_ret; exact Hst | exact Href]]]].
    + destruct (a64_exec_mem_split_steps n1 fuel insts sp0 0%N rf0 sp0 fl0 mstk0
                  (ml_mc_pc ls) rf1 sp1 fl1 mstk1 (rf_end, sp_end, fl_end, mstk_end) Hmem Hst1) as [_ Hrem].
      exact (Hbwd_cut (fuel - n1)%nat (fuel - n1)%nat rf1 sp1 fl1 mstk1 env_c1 bid_c1 dvs1 penv_ir1 penv_mc1 rf_end sp_end fl_end mstk_end (Nat.le_refl _) Hinv1 Hrem).
  - assert (Hfwd_aux : forall k : nat,
      (exists fuel rf_end sp_end fl_end mstk_end, a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp_end, fl_end, mstk_end)) \/
      (exists n rf_k sp_k fl_k mstk_k, (k <= n)%nat /\ a64_exec_steps n insts sp0 0%N rf0 sp0 fl0 mstk0 = Some (ml_mc_pc ls, rf_k, sp_k, fl_k, mstk_k) /\ a64_at_cut ls sp0 rf0 rf_k sp_k mstk_k)).
    { induction k as [| k' IH].
      - destruct Hentry_skel_fwd as [(f0 & rfe & spe & fle & me & Hmem) | (n0 & rf1 & sp1 & fl1 & mstk1 & Hst1 & Hat1)].
        + left; exists f0, rfe, spe, fle, me; exact Hmem.
        + right; exists n0, rf1, sp1, fl1, mstk1; split; [lia | split; assumption].
      - destruct IH as [(f0 & rfe & spe & fle & me & Hmem) | (n0 & rfk & spk & flk & mstkk & Hle & Hst0 & Hatk)];
          [left; exists f0, rfe, spe, fle, me; exact Hmem |].
        destruct (@a64_skel_step Pa insts ret_w ls seg_skel rf0 sp0 rfk spk flk mstkk Hwf Hrw Hval_a64 Hsp0 Es_skel Hok_skel Hatk)
          as [(fe & rfe & fle & me & Hme & _) | (n1 & rf1 & sp1 & fl1 & mstk1 & Hn1 & Hst1 & Hat1)].
        + left; exists (n0 + fe)%nat, rfe, sp0, fle, me; exact (a64_exec_steps_to_exec_mem n0 fe insts sp0 0%N rf0 sp0 fl0 mstk0 (ml_mc_pc ls) rfk spk flk mstkk (rfe, sp0, fle, me) Hst0 Hme).
        + right; exists (n0 + n1)%nat, rf1, sp1, fl1, mstk1; split; [lia | split; [exact (a64_exec_steps_trans n0 n1 insts sp0 0%N rf0 sp0 fl0 mstk0 (ml_mc_pc ls) rfk spk flk mstkk (ml_mc_pc ls, rf1, sp1, fl1, mstk1) Hst0 Hst1) | exact Hat1]]. }
    exact Hfwd_aux.
Qed.


