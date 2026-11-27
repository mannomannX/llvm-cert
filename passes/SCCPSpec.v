(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Sparse Conditional Constant Propagation Specification ([CertPasses.SCCPSpec])

    Purpose:
      Defines the constant domain and lattice ([const_val], [lat_val]),
      bit-vector constant evaluators, SCCP dataflow solver ([sccp_solve]),
      must-definedness analysis, certificate checker ([check_sccp_valid]), and
      CFG/MCFG rewriting ([sccp_mcfg], [sccp_mcfg_typ]).

    Trust Contract & Fail-Closed Boundary:
      Extracted to OCaml ([Extract.v]: [sccp_mcfg], [sccp_mcfg_typ]).
      [sccp_cfg] validates [sccp_check_guards] and [check_sccp_valid] on the
      pruned constant certificate, falling back to the identity CFG [c] if
      either check fails.

    Assumptions:
      Depends on Stdlib, Vellvm, and [CertPasses.PassCommon]; zero custom axioms
      (decidable equality and Hedberg UIP on [positive] proved in vanilla CIC).

    Section Outline:
      (1) Decidable equality, bit-vector, & edge helpers; (2) Constant domain,
      lattice, & evaluators; (3) Solver, must-definedness, [check_sccp_valid],
      & CFG/MCFG rewriting. *)

From Stdlib Require Import
  ZArith
  PArith
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  Semantics.Interfaces.Params.

From CertPasses Require Import PassCommon.
Import Logic.

Set Default Goal Selector "!".
#[local] Unset Implicit Arguments.

(** * 1. Decidable Equality, Bit-Vector, and Graph Helpers *)

Lemma sccp_eq_trans_sym_l {A : Type} {x y : A} (p : x = y) :
  Logic.eq_trans (Logic.eq_sym p) p = Logic.eq_refl.
Proof.
  destruct p; reflexivity.
Qed.

Lemma sccp_eq_sym_involutive {A : Type} {x y : A} (p : x = y) :
  Logic.eq_sym (Logic.eq_sym p) = p.
Proof.
  destruct p; reflexivity.
Qed.

Definition sccp_pos_nu {x y : positive} (p : x = y) : x = y :=
  match Pos.eq_dec x y with
  | left q => q
  | right Hne => False_rect (x = y) (Hne p)
  end.

Lemma sccp_pos_nu_const {x y : positive} (p q : x = y) :
  sccp_pos_nu p = sccp_pos_nu q.
Proof.
  unfold sccp_pos_nu.
  destruct (Pos.eq_dec x y) as [Heq | Hne]; [reflexivity | contradiction (Hne p)].
Qed.

Lemma sccp_pos_nu_left_inv {x y : positive} (p : x = y) :
  Logic.eq_trans (Logic.eq_sym (sccp_pos_nu Logic.eq_refl)) (sccp_pos_nu p) = p.
Proof.
  destruct p; apply sccp_eq_trans_sym_l.
Qed.

Lemma sccp_pos_uip_refl (x : positive) (p : x = x) :
  p = Logic.eq_refl.
Proof.
  rewrite <- (sccp_pos_nu_left_inv p), (sccp_pos_nu_const p Logic.eq_refl);
    apply sccp_pos_nu_left_inv.
Qed.

Lemma sccp_pos_eq_dec_refl (sz : positive) :
  Pos.eq_dec sz sz = left Logic.eq_refl.
Proof.
  destruct (Pos.eq_dec sz sz) as [Heq | Hne].
  - f_equal; apply sccp_pos_uip_refl.
  - contradiction (Hne Logic.eq_refl).
Qed.

Lemma sccp_bit_int_unsigned_inj (sz : positive) (x y : @bit_int sz) :
  @Integers.unsigned sz x = @Integers.unsigned sz y -> x = y.
Proof.
  intros H.
  rewrite <- (@Integers.repr_unsigned sz x), <- (@Integers.repr_unsigned sz y), H.
  reflexivity.
Qed.

Lemma sccp_bit_int_1_cases (val : @bit_int 1) :
  if (@Integers.unsigned 1 val =? 1)%Z
  then val = @Integers.one 1
  else val = @Integers.zero 1.
Proof.
  pose proof (@Integers.unsigned_range 1 val) as Hrng.
  change (@Integers.modulus 1) with 2%Z in Hrng.
  destruct (@Integers.unsigned 1 val =? 1)%Z eqn:E.
  - apply Z.eqb_eq in E.
    apply sccp_bit_int_unsigned_inj.
    rewrite E, (@Integers.unsigned_one 1); reflexivity.
  - apply Z.eqb_neq in E.
    apply sccp_bit_int_unsigned_inj.
    rewrite (@Integers.unsigned_zero 1); lia.
Qed.

Definition sccp_z_to_lit_checked (z : Z) : option int_syntax :=
  let lit := BinIntDef.Z.to_num_int z in
  if Z.eqb (denote_int_syntax lit) z then Some lit else None.

Lemma sccp_z_to_lit_checked_sound (z : Z) (lit : int_syntax) :
  sccp_z_to_lit_checked z = Some lit ->
  denote_int_syntax lit = z.
Proof.
  unfold sccp_z_to_lit_checked; cbn zeta.
  destruct (Z.eqb (denote_int_syntax (BinIntDef.Z.to_num_int z)) z) eqn:E; [| discriminate].
  intros H; inversion H; subst lit.
  apply Z.eqb_eq, E.
Qed.

Fixpoint sccp_nodup_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && sccp_nodup_ids rest
  end.

Definition sccp_incl_ids (xs ys : list raw_id) : bool :=
  forallb (fun x => in_raw_ids x ys) xs.

Lemma sccp_incl_ids_spec (xs ys : list raw_id) :
  sccp_incl_ids xs ys = true ->
  forall x, In x xs -> In x ys.
Proof.
  unfold sccp_incl_ids; rewrite forallb_forall; intros H x Hx.
  apply in_raw_ids_spec, H, Hx.
Qed.

Fixpoint sccp_dedup_ids (xs : list raw_id) : list raw_id :=
  match xs with
  | [] => []
  | x :: rest =>
      let rest' := sccp_dedup_ids rest in
      if in_raw_ids x rest' then rest' else x :: rest'
  end.

Definition sccp_inter_ids (xs ys : list raw_id) : list raw_id :=
  List.filter (fun x => in_raw_ids x ys) xs.

Definition sccp_id_list_eqb (xs ys : list raw_id) : bool :=
  sccp_incl_ids xs ys && sccp_incl_ids ys xs.

Definition cfg_edge : Type := (block_id * block_id)%type.

Definition sccp_edge_eqb (e1 e2 : cfg_edge) : bool :=
  raw_id_eqb (fst e1) (fst e2) && raw_id_eqb (snd e1) (snd e2).

Lemma sccp_edge_eqb_spec (e1 e2 : cfg_edge) :
  sccp_edge_eqb e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1 as [a1 b1], e2 as [a2 b2]; unfold sccp_edge_eqb; cbn [fst snd].
  rewrite Bool.andb_true_iff, !raw_id_eqb_spec.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; split; reflexivity].
Qed.

Definition sccp_in_edges (e : cfg_edge) (es : list cfg_edge) : bool :=
  existsb (sccp_edge_eqb e) es.

Lemma sccp_in_edges_spec (e : cfg_edge) (es : list cfg_edge) :
  sccp_in_edges e es = true <-> In e es.
Proof.
  unfold sccp_in_edges; rewrite existsb_exists.
  split.
  - intros [e' [Hin Heq]]; apply sccp_edge_eqb_spec in Heq; subst; exact Hin.
  - intros Hin; exists e; split; [exact Hin | apply sccp_edge_eqb_spec; reflexivity].
Qed.

Definition sccp_add_edge (e : cfg_edge) (es : list cfg_edge) : list cfg_edge * bool :=
  if sccp_in_edges e es then (es, false) else (e :: es, true).

Fixpoint sccp_add_edges (new_es es : list cfg_edge) : list cfg_edge * bool :=
  match new_es with
  | [] => (es, false)
  | e :: rest =>
      let '(es1, ch1) := sccp_add_edge e es in
      let '(es2, ch2) := sccp_add_edges rest es1 in
      (es2, ch1 || ch2)
  end.

Definition sccp_is_reachable_blk (exec_edges : list cfg_edge) (bid : block_id) : bool :=
  existsb (fun '(_, dst) => raw_id_eqb dst bid) exec_edges.

Definition sccp_check_guards (fargs : list local_id) (c : CFG.cfg dtyp) : bool :=
  cfg_no_block_addresses c
  && sccp_nodup_ids (List.map blk_id (blks c))
  && sccp_nodup_ids (fargs ++ flat_map full_block_defs (blks c)).

(** * 2. Constant Domain, Value Lattice, and Poison/UB-Free Evaluators *)

Inductive const_val : Type :=
| CInt (sz : positive) (val : @bit_int sz).

Definition const_val_eqb (c1 c2 : const_val) : bool :=
  match c1, c2 with
  | CInt sz1 v1, CInt sz2 v2 =>
      Pos.eqb sz1 sz2 && Z.eqb (@Integers.unsigned sz1 v1) (@Integers.unsigned sz2 v2)
  end.

Lemma const_val_eqb_refl (c : const_val) :
  const_val_eqb c c = true.
Proof.
  destruct c as [sz v]; cbn [const_val_eqb].
  rewrite Pos.eqb_refl, Z.eqb_refl; reflexivity.
Qed.

Lemma const_val_eqb_spec (c1 c2 : const_val) :
  const_val_eqb c1 c2 = true <-> c1 = c2.
Proof.
  split.
  - destruct c1 as [sz1 v1], c2 as [sz2 v2]; cbn [const_val_eqb].
    rewrite Bool.andb_true_iff, Pos.eqb_eq, Z.eqb_eq.
    intros [<- Hu]; f_equal; apply sccp_bit_int_unsigned_inj, Hu.
  - intros <-; apply const_val_eqb_refl.
Qed.

Definition const_to_dvalue {Pa : Params} (cv : const_val) : @dvalue Pa :=
  match cv with
  | CInt sz val => DVALUE_Base (DVALUE_I sz val)
  end.

Definition const_to_lit_exp (cv : const_val) : option (dtyp * exp dtyp) :=
  match cv with
  | CInt sz val =>
      match Pos.eq_dec sz 1%positive with
      | left Heq =>
          let v1 : @bit_int 1 := eq_rect sz (fun s => @bit_int s) val 1%positive Heq in
          Some (DTYPE_Base (DTYPE_I 1), EXP_Bool ((@Integers.unsigned 1 v1 =? 1)%Z))
      | right _ =>
          match sccp_z_to_lit_checked (@Integers.unsigned sz val) with
          | Some lit => Some (DTYPE_Base (DTYPE_I sz), EXP_Integer lit)
          | None => None
          end
      end
  end.

Definition const_to_exp_at (cv : const_val) (top : option dtyp) : option (exp dtyp) :=
  match const_to_lit_exp cv with
  | None => None
  | Some (dt_cv, e_lit) =>
      match top with
      | Some dt => if dtyp_eqb dt dt_cv then Some e_lit else None
      | None => Some (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt_cv e_lit)
      end
  end.

Definition eval_const_iop_same (sz : positive) (iop : ibinop)
  (x y : @bit_int sz) : option (@bit_int sz) :=
  match iop with
  | Add nuw nsw =>
      if orb (andb nuw (@Integers.eq sz (@Integers.add_carry sz x y (@Integers.zero sz)) (@Integers.one sz)))
             (andb nsw (@Integers.eq sz (@Integers.add_overflow sz x y (@Integers.zero sz)) (@Integers.one sz)))
      then None
      else Some (@Integers.add sz x y)
  | Sub nuw nsw =>
      if orb (andb nuw (@Integers.eq sz (@Integers.sub_borrow sz x y (@Integers.zero sz)) (@Integers.one sz)))
             (andb nsw (@Integers.eq sz (@Integers.sub_overflow sz x y (@Integers.zero sz)) (@Integers.one sz)))
      then None
      else Some (@Integers.sub sz x y)
  | Mul nuw nsw =>
      if Pos.eqb sz 1 then Some (@Integers.mul sz x y)
      else
        let res := @Integers.mul sz x y in
        let res_u' := (@Integers.unsigned sz x * @Integers.unsigned sz y)%Z in
        let res_s' := (@Integers.signed sz x * @Integers.signed sz y)%Z in
        if orb (andb nuw (res_u' >? @Integers.unsigned sz res)%Z)
               (andb nsw (orb (@Integers.min_signed sz >? res_s')%Z
                              (res_s' >? @Integers.max_signed sz)%Z))
        then None
        else Some res
  | Shl nuw nsw =>
      if (@Integers.unsigned sz y >=? Z.pos sz)%Z then None
      else
        let res := @Integers.shl sz x y in
        let res_u := @Integers.unsigned sz res in
        let res_u' := Z.shiftl (@Integers.unsigned sz x) (@Integers.unsigned sz y) in
        if andb nuw (res_u' >? res_u)%Z then None
        else if nsw then
          let nres := @Integers.negative sz res in
          if negb (Z.shiftr (@Integers.unsigned sz x) (Z.pos sz - @Integers.unsigned sz y)
                   =? @Integers.unsigned sz nres * (Z.pow 2 (@Integers.unsigned sz y) - 1))%Z
          then None
          else Some res
        else Some res
  | UDiv ex =>
      if (@Integers.unsigned sz y =? 0)%Z then None
      else if andb ex (negb ((@Integers.unsigned sz x) mod (@Integers.unsigned sz y) =? 0)%Z)
      then None
      else Some (@Integers.divu sz x y)
  | SDiv ex =>
      if (@Integers.signed sz y =? 0)%Z then None
      else if ((@Integers.min_signed sz =? @Integers.signed sz x)%Z
               && (@Integers.signed sz y =? -1)%Z)%bool
      then None
      else if andb ex (negb ((@Integers.signed sz x) mod (@Integers.signed sz y) =? 0)%Z)
      then None
      else Some (@Integers.divs sz x y)
  | LShr ex =>
      if (@Integers.unsigned sz y >=? Z.pos sz)%Z then None
      else if andb ex (negb ((@Integers.unsigned sz x)
                               mod (Z.pow 2 (@Integers.unsigned sz y)) =? 0)%Z)
      then None
      else Some (@Integers.shru sz x y)
  | AShr ex =>
      if (@Integers.unsigned sz y >=? Z.pos sz)%Z then None
      else if andb ex (negb ((@Integers.unsigned sz x)
                               mod (Z.pow 2 (@Integers.unsigned sz y)) =? 0)%Z)
      then None
      else Some (@Integers.shr sz x y)
  | URem =>
      if (@Integers.unsigned sz y =? 0)%Z then None
      else Some (@Integers.modu sz x y)
  | SRem =>
      if (@Integers.signed sz y =? 0)%Z then None
      else if ((@Integers.min_signed sz =? @Integers.signed sz x)%Z
               && (@Integers.signed sz y =? -1)%Z)%bool
      then None
      else Some (@Integers.mods sz x y)
  | And => Some (@Integers.and sz x y)
  | Or b =>
      if b then
        if @Integers.eq sz (@Integers.or sz x y) (@Integers.xor sz x y)
        then Some (@Integers.or sz x y)
        else None
      else Some (@Integers.or sz x y)
  | Xor => Some (@Integers.xor sz x y)
  end.

Definition eval_const_iop (iop : ibinop) (c1 c2 : const_val) : option const_val :=
  match c1, c2 with
  | CInt sz1 x, CInt sz2 y =>
      match Pos.eq_dec sz2 sz1 with
      | left Heq =>
          let y' : @bit_int sz1 := eq_rect sz2 (fun s => @bit_int s) y sz1 Heq in
          option_map (CInt sz1) (eval_const_iop_same sz1 iop x y')
      | right _ => None
      end
  end.

Definition eval_const_icmp_same (sz : positive) (samesign_f : bool) (cmp_op : icmp)
  (x y : @bit_int sz) : option const_val :=
  if (samesign_f && negb (@VellvmIntegers.samesign (@bit_int sz) (VellvmIntegers.VInt_Bounded sz) x y))%bool
  then None
  else
    let bit :=
      match cmp_op with
      | Eq  => @Integers.cmpu sz Ceq x y
      | Ne  => @Integers.cmpu sz Cne x y
      | Ugt => @Integers.cmpu sz Cgt x y
      | Uge => @Integers.cmpu sz Cge x y
      | Ult => @Integers.cmpu sz Clt x y
      | Ule => @Integers.cmpu sz Cle x y
      | Sgt => @Integers.cmp sz Cgt x y
      | Sge => @Integers.cmp sz Cge x y
      | Slt => @Integers.cmp sz Clt x y
      | Sle => @Integers.cmp sz Cle x y
      end
    in
    Some (CInt 1 (if bit then @Integers.one 1 else @Integers.zero 1)).

Definition eval_const_icmp (samesign_f : bool) (cmp_op : icmp)
  (c1 c2 : const_val) : option const_val :=
  match c1, c2 with
  | CInt sz1 x, CInt sz2 y =>
      match Pos.eq_dec sz2 sz1 with
      | left Heq =>
          let y' : @bit_int sz1 := eq_rect sz2 (fun s => @bit_int s) y sz1 Heq in
          eval_const_icmp_same sz1 samesign_f cmp_op x y'
      | right _ => None
      end
  end.

Definition eval_const_pconv (pconv : pure_conversion) (dt_from : dtyp)
  (c1 : const_val) (dt_to : dtyp) : option const_val :=
  match c1, dt_from, dt_to with
  | CInt sz_from i1, DTYPE_Base (DTYPE_I sz_t), DTYPE_Base (DTYPE_I sz_to) =>
      match pconv with
      | Trunc nuw nsw =>
          if (Pos.eqb sz_t sz_from && (sz_to <? sz_from)%positive)%bool then
            let res : @bit_int sz_to := @Integers.repr sz_to (@Integers.unsigned sz_from i1) in
            let nuw_v := (nuw && negb (Z.eqb (@Integers.unsigned sz_to res) (@Integers.unsigned sz_from i1)))%bool in
            let nsw_v := (nsw && negb (Z.eqb (@Integers.signed sz_to res) (@Integers.signed sz_from i1)))%bool in
            if (nuw_v || nsw_v)%bool then None else Some (CInt sz_to res)
          else None
      | Zext nneg =>
          if (Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive)%bool then
            if (nneg && (@Integers.signed sz_from i1 <? 0)%Z)%bool then None
            else Some (CInt sz_to (@Integers.repr sz_to (@Integers.unsigned sz_from i1)))
          else None
      | Sext =>
          if (Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive)%bool then
            Some (CInt sz_to (@Integers.repr sz_to (@Integers.signed sz_from i1)))
          else None
      | _ => None
      end
  | _, _, _ => None
  end.

Inductive lat_val : Type :=
| LTop
| LConst (cv : const_val)
| LBot.

Definition lat_eqb (l1 l2 : lat_val) : bool :=
  match l1, l2 with
  | LTop, LTop => true
  | LConst c1, LConst c2 => const_val_eqb c1 c2
  | LBot, LBot => true
  | _, _ => false
  end.

Definition lat_meet (l1 l2 : lat_val) : lat_val :=
  match l1, l2 with
  | LTop, l => l
  | l, LTop => l
  | LConst c1, LConst c2 => if const_val_eqb c1 c2 then LConst c1 else LBot
  | _, _ => LBot
  end.

Definition sccp_lookup_lat (x : local_id) (lm : rmap lat_val) : lat_val :=
  match RM.find x lm with
  | Some lv => lv
  | None => LTop
  end.

Definition sccp_update_lat (x : local_id) (lv : lat_val) (lm : rmap lat_val)
  : rmap lat_val * bool :=
  let old := sccp_lookup_lat x lm in
  let merged := lat_meet old lv in
  if lat_eqb old merged then (lm, false) else (RM.add x merged lm, true).

(** * 3. Solver, Must-Definedness, Validator, and CFG Rewriting *)

Definition sccp_term_succs (tm : terminator dtyp) : list block_id :=
  match tm with
  | TERM_Ret _ | TERM_Ret_void | TERM_Resume _ | TERM_Unreachable => []
  | TERM_Br_1 br => [br]
  | TERM_Br _ br1 br2 => [br1; br2]
  | TERM_Switch _ def_br dests => def_br :: List.map snd dests
  | TERM_IndirectBr _ brs _ => brs
  | TERM_Invoke _ _ to_lbl unwind_lbl _ _ => [to_lbl; unwind_lbl]
  end.

Fixpoint sccp_abs_eval_exp (lm : rmap lat_val) (top : option dtyp) (e : exp dtyp)
  {struct e} : lat_val :=
  match e with
  | EXP_Ident (ID_Local y) => sccp_lookup_lat y lm
  | EXP_Bool b => LConst (CInt 1 (if b then @Integers.one 1 else @Integers.zero 1))
  | EXP_Integer lit =>
      match top with
      | Some (DTYPE_Base (DTYPE_I sz)) =>
          LConst (CInt sz (@Integers.repr sz (denote_int_syntax lit)))
      | _ => LBot
      end
  | OP_IBinop iop dt e1 e2 =>
      match sccp_abs_eval_exp lm (Some dt) e1, sccp_abs_eval_exp lm (Some dt) e2 with
      | LBot, _ | _, LBot => LBot
      | LTop, _ | _, LTop => LTop
      | LConst c1, LConst c2 =>
          match eval_const_iop iop c1 c2 with
          | Some cr => LConst cr
          | None => LBot
          end
      end
  | OP_ICmp samesign_f cmp_op dt e1 e2 =>
      match sccp_abs_eval_exp lm (Some dt) e1, sccp_abs_eval_exp lm (Some dt) e2 with
      | LBot, _ | _, LBot => LBot
      | LTop, _ | _, LTop => LTop
      | LConst c1, LConst c2 =>
          match eval_const_icmp samesign_f cmp_op c1 c2 with
          | Some cr => LConst cr
          | None => LBot
          end
      end
  | OP_Conversion ct dt_from e1 dt_to =>
      match sccp_abs_eval_exp lm (Some dt_from) e1 with
      | LBot => LBot
      | LTop => LTop
      | LConst c1 =>
          match ct with
          | CONV_Bitcast => if dtyp_eqb dt_from dt_to then LConst c1 else LBot
          | CONV_Pure pconv =>
              match eval_const_pconv pconv dt_from c1 dt_to with
              | Some cr => LConst cr
              | None => LBot
              end
          | CONV_Impure _ => LBot
          end
      end
  | OP_Select _ (dt_c, cnd) (dt1, op1) (dt2, op2) =>
      match sccp_abs_eval_exp lm (Some dt_c) cnd with
      | LTop => LTop
      | LBot => LBot
      | LConst (CInt sz_c vc) =>
          match Pos.eq_dec sz_c 1%positive with
          | left Heq =>
              let vc1 : @bit_int 1 := eq_rect sz_c (fun s => @bit_int s) vc 1%positive Heq in
              if (@Integers.unsigned 1 vc1 =? 1)%Z
              then sccp_abs_eval_exp lm (Some dt1) op1
              else sccp_abs_eval_exp lm (Some dt2) op2
          | right _ => LBot
          end
      end
  | EXP_Metadata md =>
      match md with
      | METADATA_Const (dt, ex) => sccp_abs_eval_exp lm (Some dt) ex
      | _ => LBot
      end
  | _ => LBot
  end.

Definition sccp_step_phi (incoming : list cfg_edge) (lm : rmap lat_val)
  (p : local_id * phi dtyp * list (metadata dtyp)) : rmap lat_val * bool :=
  let '(x, Phi _ dt args, _) := p in
  let lv :=
    List.fold_left
      (fun acc '(pred, _) =>
         let v_in :=
           match assoc pred args with
           | Some op => sccp_abs_eval_exp lm (Some dt) op
           | None => LBot
           end
         in
         lat_meet acc v_in)
      incoming LTop
  in
  sccp_update_lat x lv lm.

Definition sccp_step_block (exec_edges : list cfg_edge) (lm : rmap lat_val)
  (b : block dtyp) : list cfg_edge * rmap lat_val * bool :=
  let bid := blk_id b in
  let incoming := List.filter (fun '(_, dst) => raw_id_eqb dst bid) exec_edges in
  match incoming with
  | [] => (exec_edges, lm, false)
  | _ :: _ =>
      let '(lm1, ch1) :=
        List.fold_left
          (fun '(cur_lm, cur_ch) p =>
             let '(lm', ch') := sccp_step_phi incoming cur_lm p in
             (lm', cur_ch || ch'))
          (blk_phis b) (lm, false)
      in
      let '(lm2, ch2) :=
        List.fold_left
          (fun '(cur_lm, cur_ch) '(iid, ins, _) =>
             match iid, ins with
             | IId x, INSTR_Op op =>
                 let '(lm', ch') := sccp_update_lat x (sccp_abs_eval_exp cur_lm None op) cur_lm in
                 (lm', cur_ch || ch')
             | IId x, _ =>
                 let '(lm', ch') := sccp_update_lat x LBot cur_lm in
                 (lm', cur_ch || ch')
             | IVoid _, _ => (cur_lm, cur_ch)
             end)
          (blk_code b) (lm1, ch1)
      in
      let '(tiid, tm, _) := blk_term b in
      let '(lm3, ch3) :=
        match tiid with
        | IId tx =>
            let '(lm', ch') := sccp_update_lat tx LBot lm2 in
            (lm', ch2 || ch')
        | IVoid _ => (lm2, ch2)
        end
      in
      let new_edges :=
        match tm with
        | TERM_Br (dt, op) br1 br2 =>
            match sccp_abs_eval_exp lm3 (Some dt) op with
            | LTop => []
            | LConst (CInt sz vc) =>
                match Pos.eq_dec sz 1%positive with
                | left Heq =>
                    let vc1 : @bit_int 1 := eq_rect sz (fun s => @bit_int s) vc 1%positive Heq in
                    [(bid, if @Integers.eq 1 vc1 (@Integers.one 1) then br1 else br2)]
                | right _ => [(bid, br1); (bid, br2)]
                end
            | LBot => [(bid, br1); (bid, br2)]
            end
        | _ => List.map (fun succ => (bid, succ)) (sccp_term_succs tm)
        end
      in
      let '(es', ch_e) := sccp_add_edges new_edges exec_edges in
      (es', lm3, ch3 || ch_e)
  end.

Fixpoint sccp_solve_loop (fuel : nat) (bks : ocfg dtyp)
  (exec_edges : list cfg_edge) (lm : rmap lat_val)
  : list cfg_edge * rmap lat_val :=
  match fuel with
  | O => (exec_edges, lm)
  | S fuel' =>
      let '(es', lm', ch) :=
        List.fold_left
          (fun '(cur_es, cur_lm, cur_ch) b =>
             let '(es1, lm1, ch1) := sccp_step_block cur_es cur_lm b in
             (es1, lm1, cur_ch || ch1))
          bks (exec_edges, lm, false)
      in
      if ch then sccp_solve_loop fuel' bks es' lm' else (es', lm')
  end.

Definition sccp_solve (fargs : list local_id) (c : CFG.cfg dtyp)
  : list cfg_edge * rmap lat_val :=
  let init_lm := List.fold_left (fun acc x => RM.add x LBot acc) fargs (RM.empty lat_val) in
  let init_edges := [(init c, init c)] in
  let num_blks := List.length (blks c) in
  let num_defs := List.length (flat_map full_block_defs (blks c)) in
  let fuel := (2 * num_blks + 2 * num_defs + 4)%nat in
  sccp_solve_loop fuel (blks c) init_edges init_lm.

(** Must-definedness tracking (excludes [INSTR_Fence], which performs no [lwrite]). *)
Definition sccp_instr_defs (ii : instr_id * instr dtyp * list (metadata dtyp))
  : list raw_id :=
  match ii with
  | (IId id, INSTR_Fence _ _, _) => []
  | (IId id, _, _) => [id]
  | (IVoid _, _, _) => []
  end.

Fixpoint sccp_phis_defs_end (cur_defs : list raw_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp))) : list raw_id :=
  match phis with
  | [] => cur_defs
  | (x, _, _) :: rest => sccp_phis_defs_end (x :: cur_defs) rest
  end.

Fixpoint sccp_code_defs_end (cur_defs : list raw_id) (cd : code dtyp) : list raw_id :=
  match cd with
  | [] => cur_defs
  | ii :: rest => sccp_code_defs_end (sccp_instr_defs ii ++ cur_defs) rest
  end.

Definition sccp_block_defs_end (defs_in : list raw_id) (b : block dtyp) : list raw_id :=
  sccp_code_defs_end (sccp_phis_defs_end defs_in (blk_phis b)) (blk_code b).

Definition sccp_lookup_defs (bid : block_id) (md_in : rmap (list raw_id)) : list raw_id :=
  match RM.find bid md_in with
  | Some ds => ds
  | None => []
  end.

Definition sccp_edge_defs (fargs : list local_id) (c : CFG.cfg dtyp)
  (md_in : rmap (list raw_id)) (bid_from bid_src : block_id) : list raw_id :=
  if raw_id_eqb bid_from (init c) && raw_id_eqb bid_src (init c) then
    fargs
  else
    match find_block (blks c) bid_from with
    | Some b_pred => sccp_block_defs_end (sccp_lookup_defs bid_from md_in) b_pred
    | None => []
    end.

Fixpoint sccp_must_def_loop (fuel : nat) (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (all_defs : list raw_id) (md_in : rmap (list raw_id))
  : rmap (list raw_id) :=
  match fuel with
  | O => md_in
  | S fuel' =>
      let '(md_next, ch) :=
        List.fold_left
          (fun '(cur_md, cur_ch) b =>
             let bid := blk_id b in
             let incoming := List.filter (fun '(_, dst) => raw_id_eqb dst bid) exec_edges in
             match incoming with
             | [] => (cur_md, cur_ch)
             | _ :: _ =>
                 let new_ds :=
                   List.fold_left
                     (fun acc '(pred, _) =>
                        sccp_inter_ids acc (sccp_edge_defs fargs c cur_md pred bid))
                     incoming all_defs
                 in
                 let old_ds := sccp_lookup_defs bid cur_md in
                 if sccp_id_list_eqb old_ds new_ds
                 then (cur_md, cur_ch)
                 else (RM.add bid new_ds cur_md, true)
             end)
          (blks c) (md_in, false)
      in
      if ch then sccp_must_def_loop fuel' fargs c exec_edges all_defs md_next else md_next
  end.

Definition sccp_compute_must_def (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) : rmap (list raw_id) :=
  let all_defs := sccp_dedup_ids (fargs ++ flat_map full_block_defs (blks c)) in
  let md0 :=
    List.fold_left
      (fun acc b =>
         if sccp_is_reachable_blk exec_edges (blk_id b)
         then RM.add (blk_id b) all_defs acc
         else acc)
      (blks c) (RM.empty (list raw_id))
  in
  let md1 :=
    if sccp_in_edges (init c, init c) exec_edges
    then RM.add (init c) fargs md0
    else md0
  in
  sccp_must_def_loop (S (List.length (blks c))) fargs c exec_edges all_defs md1.

(** Certificate evaluator and [PS-10] boolean validator. *)
Definition sccp_safe_atom (defs : list raw_id) (dt : dtyp) (e : exp dtyp) : bool :=
  match e with
  | EXP_Bool _ | EXP_Null | EXP_Undef | EXP_Poison => true
  | EXP_Integer _ =>
      match dt with
      | DTYPE_Base (DTYPE_I _) => true
      | _ => false
      end
  | EXP_Ident (ID_Local y) => in_raw_ids y defs
  | _ => false
  end.

Fixpoint eval_cert_exp (cm : rmap const_val) (defs : list raw_id)
  (top : option dtyp) (e : exp dtyp) {struct e} : option const_val :=
  match e with
  | EXP_Ident (ID_Local y) =>
      if in_raw_ids y defs then RM.find y cm else None
  | EXP_Bool b =>
      Some (CInt 1 (if b then @Integers.one 1 else @Integers.zero 1))
  | EXP_Integer lit =>
      match top with
      | Some (DTYPE_Base (DTYPE_I sz)) =>
          Some (CInt sz (@Integers.repr sz (denote_int_syntax lit)))
      | _ => None
      end
  | OP_IBinop iop dt e1 e2 =>
      match eval_cert_exp cm defs (Some dt) e1, eval_cert_exp cm defs (Some dt) e2 with
      | Some c1, Some c2 => eval_const_iop iop c1 c2
      | _, _ => None
      end
  | OP_ICmp samesign_f cmp_op dt e1 e2 =>
      match eval_cert_exp cm defs (Some dt) e1, eval_cert_exp cm defs (Some dt) e2 with
      | Some c1, Some c2 => eval_const_icmp samesign_f cmp_op c1 c2
      | _, _ => None
      end
  | OP_Conversion ct dt_from e1 dt_to =>
      match eval_cert_exp cm defs (Some dt_from) e1 with
      | Some c1 =>
          match ct with
          | CONV_Bitcast => if dtyp_eqb dt_from dt_to then Some c1 else None
          | CONV_Pure pconv => eval_const_pconv pconv dt_from c1 dt_to
          | CONV_Impure _ => None
          end
      | None => None
      end
  | OP_Select _ (dt_c, cnd) (dt1, op1) (dt2, op2) =>
      match eval_cert_exp cm defs (Some dt_c) cnd with
      | Some (CInt sz_c vc) =>
          match Pos.eq_dec sz_c 1%positive with
          | left Heq =>
              let vc1 : @bit_int 1 := eq_rect sz_c (fun s => @bit_int s) vc 1%positive Heq in
              let r1 := eval_cert_exp cm defs (Some dt1) op1 in
              let r2 := eval_cert_exp cm defs (Some dt2) op2 in
              let ok1 := match r1 with Some _ => true | None => sccp_safe_atom defs dt1 op1 end in
              let ok2 := match r2 with Some _ => true | None => sccp_safe_atom defs dt2 op2 end in
              if (@Integers.unsigned 1 vc1 =? 1)%Z then
                if ok2 then r1 else None
              else
                if ok1 then r2 else None
          | right _ => None
          end
      | None => None
      end
  | EXP_Metadata md =>
      match md with
      | METADATA_Const (dt, ex) => eval_cert_exp cm defs (Some dt) ex
      | _ => None
      end
  | _ => None
  end.

Definition sccp_branch_target (cm : rmap const_val) (defs : list raw_id)
  (dt : dtyp) (op : exp dtyp) (br1 br2 : block_id) : option block_id :=
  match eval_cert_exp cm defs (Some dt) op with
  | Some (CInt sz vc) =>
      match Pos.eq_dec sz 1%positive with
      | left Heq =>
          let vc1 : @bit_int 1 := eq_rect sz (fun s => @bit_int s) vc 1%positive Heq in
          Some (if @Integers.eq 1 vc1 (@Integers.one 1) then br1 else br2)
      | right _ => None
      end
  | None => None
  end.

Definition check_sccp_phi (cm : rmap const_val) (edge_d : list raw_id)
  (bid_from : block_id) (p : local_id * phi dtyp * list (metadata dtyp)) : bool :=
  let '(x, Phi _ dt args, _) := p in
  match RM.find x cm with
  | None => true
  | Some cv =>
      match assoc bid_from args with
      | None => false
      | Some op =>
          match eval_cert_exp cm edge_d (Some dt) op with
          | Some cv' => const_val_eqb cv cv'
          | None => false
          end
      end
  end.

Definition check_sccp_instr (cm : rmap const_val) (cur_defs : list raw_id)
  (ii : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  match ii with
  | (IId x, INSTR_Op op, _) =>
      match RM.find x cm with
      | None => true
      | Some cv =>
          match eval_cert_exp cm cur_defs None op with
          | Some cv' => const_val_eqb cv cv'
          | None => false
          end
      end
  | (IId x, _, _) =>
      match RM.find x cm with
      | None => true
      | Some _ => false
      end
  | (IVoid _, _, _) => true
  end.

Fixpoint check_sccp_code (cm : rmap const_val) (cur_defs : list raw_id)
  (cd : code dtyp) : bool :=
  match cd with
  | [] => true
  | ii :: rest =>
      check_sccp_instr cm cur_defs ii
      && check_sccp_code cm (sccp_instr_defs ii ++ cur_defs) rest
  end.

Definition check_sccp_term (exec_edges : list cfg_edge) (cm : rmap const_val)
  (defs_end : list raw_id) (bid_src : block_id)
  (trm : instr_id * terminator dtyp * list (metadata dtyp)) : bool :=
  let '(tiid, tm, _) := trm in
  let tid_ok :=
    match tiid with
    | IId tx => match RM.find tx cm with None => true | Some _ => false end
    | IVoid _ => true
    end
  in
  let succ_ok :=
    match tm with
    | TERM_Br (dt, op) br1 br2 =>
        match sccp_branch_target cm defs_end dt op br1 br2 with
        | Some taken => sccp_in_edges (bid_src, taken) exec_edges
        | None =>
            sccp_in_edges (bid_src, br1) exec_edges
            && sccp_in_edges (bid_src, br2) exec_edges
        end
    | _ =>
        forallb (fun succ => sccp_in_edges (bid_src, succ) exec_edges)
                (sccp_term_succs tm)
    end
  in
  tid_ok && succ_ok.

Definition check_sccp_edge (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (e : cfg_edge) : bool :=
  let '(bid_from, bid_src) := e in
  match find_block (blks c) bid_src with
  | None => true
  | Some b =>
      let edge_d := sccp_edge_defs fargs c md_in bid_from bid_src in
      let defs_in := sccp_lookup_defs bid_src md_in in
      sccp_incl_ids defs_in edge_d
      && forallb (check_sccp_phi cm edge_d bid_from) (blk_phis b)
      && check_sccp_code cm (sccp_phis_defs_end defs_in (blk_phis b)) (blk_code b)
      && check_sccp_term exec_edges cm (sccp_block_defs_end defs_in b) bid_src (blk_term b)
  end.

Definition check_sccp_valid (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id))
  (cm : rmap const_val) : bool :=
  sccp_in_edges (init c, init c) exec_edges
  && forallb (fun x => match RM.find x cm with None => true | Some _ => false end) fargs
  && forallb (check_sccp_edge fargs c exec_edges md_in cm) exec_edges.

(** Prune any constant entry whose [eval_cert_exp] check fails under [md_in]. *)
Fixpoint sccp_prune_code_cert (cm : rmap const_val) (cur_defs : list raw_id)
  (cd : code dtyp) : rmap const_val * bool :=
  match cd with
  | [] => (cm, false)
  | ii :: rest =>
      let '(cm1, ch1) :=
        match ii with
        | (IId x, _, _) =>
            if check_sccp_instr cm cur_defs ii then (cm, false)
            else (RM.remove x cm, true)
        | (IVoid _, _, _) => (cm, false)
        end
      in
      let '(cm2, ch2) := sccp_prune_code_cert cm1 (sccp_instr_defs ii ++ cur_defs) rest in
      (cm2, ch1 || ch2)
  end.

Fixpoint sccp_prune_cert_loop (fuel : nat) (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  : rmap const_val :=
  match fuel with
  | O => cm
  | S fuel' =>
      let '(cm_next, ch) :=
        List.fold_left
          (fun '(cur_cm, cur_ch) '(bid_from, bid_src) =>
             match find_block (blks c) bid_src with
             | None => (cur_cm, cur_ch)
             | Some b =>
                 let edge_d := sccp_edge_defs fargs c md_in bid_from bid_src in
                 let defs_in := sccp_lookup_defs bid_src md_in in
                 let '(cm1, ch1) :=
                   List.fold_left
                     (fun '(c_cm, c_ch) p =>
                        let '(x, _, _) := p in
                        if check_sccp_phi c_cm edge_d bid_from p
                        then (c_cm, c_ch)
                        else (RM.remove x c_cm, true))
                     (blk_phis b) (cur_cm, cur_ch)
                 in
                 let '(cm2, ch2) :=
                   sccp_prune_code_cert cm1 (sccp_phis_defs_end defs_in (blk_phis b)) (blk_code b)
                 in
                 let '(tiid, _, _) := blk_term b in
                 let '(cm3, ch3) :=
                   match tiid with
                   | IId tx =>
                       match RM.find tx cm2 with
                       | Some _ => (RM.remove tx cm2, true)
                       | None => (cm2, false)
                       end
                   | IVoid _ => (cm2, false)
                   end
                 in
                 (cm3, ch1 || ch2 || ch3)
             end)
          exec_edges (cm, false)
      in
      if ch then sccp_prune_cert_loop fuel' fargs c exec_edges md_in cm_next else cm_next
  end.

Definition sccp_build_cert (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (lm : rmap lat_val)
  : rmap const_val :=
  let cand_defs := flat_map full_block_defs (blks c) in
  let cm0 :=
    List.fold_left
      (fun acc x =>
         if in_raw_ids x fargs then acc
         else
           match sccp_lookup_lat x lm with
           | LConst cv =>
               match const_to_lit_exp cv with
               | Some _ => RM.add x cv acc
               | None => acc
               end
           | _ => acc
           end)
      cand_defs (RM.empty const_val)
  in
  sccp_prune_cert_loop (S (List.length cand_defs)) fargs c exec_edges md_in cm0.

(** Syntactic expression, instruction, terminator, and block rewriting. *)
Fixpoint subst_exp_at (cm : rmap const_val) (defs : list raw_id)
  (top : option dtyp) (e : exp dtyp) {struct e} : exp dtyp :=
  let map_texps :=
    fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
      match l with
      | [] => []
      | (dt, ex) :: rest => (dt, subst_exp_at cm defs (Some dt) ex) :: go rest
      end
  in
  match e with
  | EXP_Ident (ID_Local y) =>
      if in_raw_ids y defs then
        match RM.find y cm with
        | Some cv =>
            match const_to_exp_at cv top with
            | Some ec => ec
            | None => e
            end
        | None => e
        end
      else e
  | EXP_Ident (ID_Global _)
  | EXP_Integer _ | EXP_Float _ | EXP_Bool _ | EXP_Null
  | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_Asm _ _ _ _ _ _ | EXP_BlockAddress _ _ => e
  | EXP_Cstring es => EXP_Cstring (map_texps es)
  | EXP_Struct es => EXP_Struct (map_texps es)
  | EXP_Packed_struct es => EXP_Packed_struct (map_texps es)
  | EXP_Array es => EXP_Array (map_texps es)
  | EXP_Vector es => EXP_Vector (map_texps es)
  | OP_IBinop iop dt e1 e2 =>
      OP_IBinop iop dt (subst_exp_at cm defs (Some dt) e1) (subst_exp_at cm defs (Some dt) e2)
  | OP_ICmp samesign_f cmp_op dt e1 e2 =>
      OP_ICmp samesign_f cmp_op dt
        (subst_exp_at cm defs (Some dt) e1)
        (subst_exp_at cm defs (Some dt) e2)
  | OP_FBinop fop fm dt e1 e2 =>
      OP_FBinop fop fm dt
        (subst_exp_at cm defs (Some dt) e1)
        (subst_exp_at cm defs (Some dt) e2)
  | OP_FCmp fcmp_op fm dt e1 e2 =>
      OP_FCmp fcmp_op fm dt
        (subst_exp_at cm defs (Some dt) e1)
        (subst_exp_at cm defs (Some dt) e2)
  | OP_Fneg fm (dt, e1) =>
      OP_Fneg fm (dt, subst_exp_at cm defs (Some dt) e1)
  | OP_Conversion ct dt_from e1 dt_to =>
      OP_Conversion ct dt_from (subst_exp_at cm defs (Some dt_from) e1) dt_to
  | OP_GetElementPtr flags dt1 (dt2, ep) idxs =>
      OP_GetElementPtr flags dt1 (dt2, subst_exp_at cm defs (Some dt2) ep) (map_texps idxs)
  | OP_ExtractElement (dt_v, ev) (dt_i, ei) =>
      OP_ExtractElement
        (dt_v, subst_exp_at cm defs (Some dt_v) ev)
        (dt_i, subst_exp_at cm defs (Some dt_i) ei)
  | OP_InsertElement (dt_v, ev) (dt_e, ee) (dt_i, ei) =>
      OP_InsertElement
        (dt_v, subst_exp_at cm defs (Some dt_v) ev)
        (dt_e, subst_exp_at cm defs (Some dt_e) ee)
        (dt_i, subst_exp_at cm defs (Some dt_i) ei)
  | OP_ShuffleVector (dt1, e1) (dt2, e2) (dt3, e3) =>
      OP_ShuffleVector
        (dt1, subst_exp_at cm defs (Some dt1) e1)
        (dt2, subst_exp_at cm defs (Some dt2) e2)
        (dt3, subst_exp_at cm defs (Some dt3) e3)
  | OP_ExtractValue (dt_s, es) idxs =>
      OP_ExtractValue (dt_s, subst_exp_at cm defs (Some dt_s) es) idxs
  | OP_InsertValue (dt_s, es) (dt_e, ee) idxs =>
      OP_InsertValue
        (dt_s, subst_exp_at cm defs (Some dt_s) es)
        (dt_e, subst_exp_at cm defs (Some dt_e) ee)
        idxs
  | OP_Select fm (dt_c, ec) (dt1, e1) (dt2, e2) =>
      OP_Select fm
        (dt_c, subst_exp_at cm defs (Some dt_c) ec)
        (dt1, subst_exp_at cm defs (Some dt1) e1)
        (dt2, subst_exp_at cm defs (Some dt2) e2)
  | OP_Freeze (dt, e1) =>
      OP_Freeze (dt, subst_exp_at cm defs (Some dt) e1)
  | EXP_Splat (dt, e1) =>
      EXP_Splat (dt, subst_exp_at cm defs (Some dt) e1)
  | EXP_Metadata md =>
      match md with
      | METADATA_Const (dt, ex) =>
          EXP_Metadata (METADATA_Const (dt, subst_exp_at cm defs (Some dt) ex))
      | _ => e
      end
  end.

Definition sccp_rewrite_call_args (cm : rmap const_val) (defs : list raw_id)
  (args : list (texp dtyp * list param_attr)) : list (texp dtyp * list param_attr) :=
  List.map (fun '((t, op), attrs) => ((t, subst_exp_at cm defs (Some t) op), attrs)) args.

Definition sccp_rewrite_ob (cm : rmap const_val) (defs : list raw_id)
  (ob : @operand_bundle dtyp) : @operand_bundle dtyp :=
  {| ob_tag := ob_tag ob;
     ob_ops :=
       List.map
         (fun o =>
            match o with
            | SSA_value (t, ex) => SSA_value (t, subst_exp_at cm defs (Some t) ex)
            | Metadata_string md => Metadata_string md
            end)
         (ob_ops ob) |}.

Definition sccp_rewrite_instr (cm : rmap const_val) (defs : list raw_id)
  (ins : instr dtyp) : instr dtyp :=
  match ins with
  | INSTR_Comment msg => INSTR_Comment msg
  | INSTR_Op op => INSTR_Op (subst_exp_at cm defs None op)
  | INSTR_Call fn args anns obs =>
      INSTR_Call fn
        (sccp_rewrite_call_args cm defs args)
        anns
        (List.map (sccp_rewrite_ob cm defs) obs)
  | INSTR_Alloca dt anns => INSTR_Alloca dt anns
  | INSTR_Load dt (du, ptr) anns =>
      INSTR_Load dt (du, subst_exp_at cm defs (Some du) ptr) anns
  | INSTR_Store (dt, val) (du, ptr) anns =>
      INSTR_Store
        (dt, subst_exp_at cm defs (Some dt) val)
        (du, subst_exp_at cm defs (Some du) ptr)
        anns
  | INSTR_Fence sc ord => INSTR_Fence sc ord
  | INSTR_AtomicCmpXchg cpx =>
      let '(ptr_ty, ptr_val) := c_ptr cpx in
      let '(cmp_ty, cmp_val) := c_cmp cpx in
      let '(new_ty, new_val) := c_new cpx in
      INSTR_AtomicCmpXchg
        {| c_weak := c_weak cpx;
           c_volatile := c_volatile cpx;
           c_ptr := (ptr_ty, subst_exp_at cm defs (Some ptr_ty) ptr_val);
           c_cmp := (cmp_ty, subst_exp_at cm defs (Some cmp_ty) cmp_val);
           c_new := (new_ty, subst_exp_at cm defs (Some new_ty) new_val);
           c_syncscope := c_syncscope cpx;
           c_success_ordering := c_success_ordering cpx;
           c_failure_ordering := c_failure_ordering cpx;
           c_align := c_align cpx |}
  | INSTR_AtomicRMW armw =>
      let '(ptr_ty, ptr_val) := a_ptr armw in
      let '(a_ty, a_val_e) := a_val armw in
      INSTR_AtomicRMW
        {| a_volatile := a_volatile armw;
           a_operation := a_operation armw;
           a_ptr := (ptr_ty, subst_exp_at cm defs (Some ptr_ty) ptr_val);
           a_val := (a_ty, subst_exp_at cm defs (Some a_ty) a_val_e);
           a_syncscope := a_syncscope armw;
           a_ordering := a_ordering armw;
           a_align := a_align armw |}
  | INSTR_VAArg (t, ptr_exp) argty =>
      INSTR_VAArg (t, subst_exp_at cm defs (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp) argty
  | INSTR_LandingPad rty cl cs => INSTR_LandingPad rty cl cs
  end.

Fixpoint sccp_rewrite_code (cm : rmap const_val) (cur_defs : list raw_id)
  (cd : code dtyp) : code dtyp :=
  match cd with
  | [] => []
  | ii :: rest =>
      let '(iid, ins, md) := ii in
      (iid, sccp_rewrite_instr cm cur_defs ins, md)
      :: sccp_rewrite_code cm (sccp_instr_defs ii ++ cur_defs) rest
  end.

Definition sccp_rewrite_term (allow_fold : bool) (cm : rmap const_val)
  (defs_end : list raw_id) (tm : terminator dtyp) : terminator dtyp :=
  match tm with
  | TERM_Ret (dt, op) => TERM_Ret (dt, subst_exp_at cm defs_end (Some dt) op)
  | TERM_Ret_void => TERM_Ret_void
  | TERM_Br (dt, op) br1 br2 =>
      if allow_fold then
        match sccp_branch_target cm defs_end dt op br1 br2 with
        | Some taken => TERM_Br_1 taken
        | None => TERM_Br (dt, subst_exp_at cm defs_end (Some dt) op) br1 br2
        end
      else TERM_Br (dt, subst_exp_at cm defs_end (Some dt) op) br1 br2
  | TERM_Br_1 br => TERM_Br_1 br
  | TERM_Switch (dt, ex) def_br dests =>
      TERM_Switch (dt, subst_exp_at cm defs_end (Some dt) ex) def_br dests
  | TERM_IndirectBr (dt, ex) brs fn =>
      TERM_IndirectBr (dt, subst_exp_at cm defs_end (Some dt) ex) brs fn
  | TERM_Resume (dt, ex) =>
      TERM_Resume (dt, subst_exp_at cm defs_end (Some dt) ex)
  | TERM_Invoke fn args to_lbl unwind_lbl anns obs =>
      TERM_Invoke fn
        (sccp_rewrite_call_args cm defs_end args)
        to_lbl unwind_lbl anns
        (List.map (sccp_rewrite_ob cm defs_end) obs)
  | TERM_Unreachable => TERM_Unreachable
  end.

Definition sccp_rewrite_phi_args (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (bid_src : block_id) (dt : dtyp)
  (args : list (block_id * exp dtyp)) : list (block_id * exp dtyp) :=
  List.map
    (fun '(pred, op) =>
       if sccp_in_edges (pred, bid_src) exec_edges
       then (pred, subst_exp_at cm (sccp_edge_defs fargs c md_in pred bid_src) (Some dt) op)
       else (pred, op))
    args.

Definition sccp_rewrite_phis (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (bid_src : block_id)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  : list (local_id * phi dtyp * list (metadata dtyp)) :=
  List.map
    (fun '(x, Phi fm dt args, md) =>
       (x, Phi fm dt (sccp_rewrite_phi_args fargs c exec_edges md_in cm bid_src dt args), md))
    phis.

Definition sccp_rewrite_block (fargs : list local_id) (c : CFG.cfg dtyp)
  (exec_edges : list cfg_edge) (md_in : rmap (list raw_id)) (cm : rmap const_val)
  (b : block dtyp) : block dtyp :=
  let bid := blk_id b in
  if sccp_is_reachable_blk exec_edges bid then
    let defs_in := sccp_lookup_defs bid md_in in
    let defs_phis := sccp_phis_defs_end defs_in (blk_phis b) in
    let defs_end := sccp_block_defs_end defs_in b in
    let '(tiid, tm, tmd) := blk_term b in
    {| blk_id := bid;
       blk_phis := sccp_rewrite_phis fargs c exec_edges md_in cm bid (blk_phis b);
       blk_code := sccp_rewrite_code cm defs_phis (blk_code b);
       blk_term := (tiid, sccp_rewrite_term true cm defs_end tm, tmd);
       blk_comments := blk_comments b |}
  else b.

Definition sccp_cfg (fargs : list local_id) (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  if sccp_check_guards fargs c then
    let '(exec_edges, lm) := sccp_solve fargs c in
    let md_in := sccp_compute_must_def fargs c exec_edges in
    let cm := sccp_build_cert fargs c exec_edges md_in lm in
    if check_sccp_valid fargs c exec_edges md_in cm then
      {| init := init c;
         blks := List.map (sccp_rewrite_block fargs c exec_edges md_in cm) (blks c);
         args := args c |}
    else c
  else c.

Definition sccp_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_with_args sccp_cfg M.

Definition sccp_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  sccp_mcfg (convert_types M).

