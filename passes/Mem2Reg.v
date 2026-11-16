(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Stack-Slot to SSA Register Promotion ([CertPasses.Mem2Reg])

    Promotes non-escaping scalar [alloca] stack slots in function entry blocks
    to SSA registers and block-entry [Phi] nodes (Stage 1), followed by
    reverse-order dead scalar [alloca] elimination in leaf functions (Stage 2)
    so inlinable callees become [alloca]-free before [CertPasses.Inline].
    Composed across bounded rounds via [prog_refines_trans]. *)

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
  Utils.rutt_cutoff
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Sizeof
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 1. Computable Syntax Inspectors & CFG Transformation *)

Definition m2r_is_empty {A : Type} (xs : list A) : bool :=
  match xs with
  | [] => true
  | _ :: _ => false
  end.

Lemma m2r_is_empty_spec {A : Type} (xs : list A) :
  m2r_is_empty xs = true <-> xs = [].
Proof using.
  destruct xs; cbn; split; intros H; congruence.
Qed.

Fixpoint m2r_nodup_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (in_raw_ids x xs') && m2r_nodup_ids xs'
  end.

Lemma m2r_nodup_ids_spec (xs : list raw_id) :
  m2r_nodup_ids xs = true <-> NoDup xs.
Proof using.
  induction xs as [| x xs' IH]; cbn [m2r_nodup_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, in_raw_ids_false, IH.
    split.
    + intros [Hnin Hnd]; constructor; assumption.
    + intros Hnd; inversion Hnd; subst; split; assumption.
Qed.

Fixpoint m2r_count_id (x : raw_id) (xs : list raw_id) : nat :=
  match xs with
  | [] => O
  | y :: ys =>
      (if raw_id_eqb x y then 1%nat else 0%nat) + m2r_count_id x ys
  end.

Lemma m2r_count_id_app (x : raw_id) (l1 l2 : list raw_id) :
  m2r_count_id x (l1 ++ l2) = (m2r_count_id x l1 + m2r_count_id x l2)%nat.
Proof using.
  induction l1 as [| y l1' IH]; cbn; [reflexivity | rewrite IH; lia].
Qed.

Lemma m2r_count_id_zero (x : raw_id) (xs : list raw_id) :
  m2r_count_id x xs = O <-> ~ In x xs.
Proof using.
  induction xs as [| y ys IH]; cbn.
  - split; [intros _ [] | intros _; reflexivity].
  - destruct (raw_id_eqb_spec x y) as [-> | Hne]; cbn.
    + split; [lia | intros H; exfalso; apply H; left; reflexivity].
    + rewrite IH; split; intros H.
      * intros [Heq | Hin]; [exact (Hne ( eq_sym Heq)) | exact (H Hin)].
      * intros Hin; apply H; right; exact Hin.
Qed.

Definition m2r_term_succs {T : Set} (tm : terminator T) : list block_id :=
  match tm with
  | TERM_Br _ b1 b2 => [b1; b2]
  | TERM_Br_1 b => [b]
  | TERM_Switch _ d brs => d :: List.map snd brs
  | TERM_IndirectBr _ brs _ => brs
  | TERM_Invoke _ _ b1 b2 _ _ => [b1; b2]
  | TERM_Ret _ | TERM_Ret_void | TERM_Resume _ | TERM_Unreachable => []
  end.

Definition m2r_block_succs {T : Set} (bk : block T) : list block_id :=
  let '(_, tm, _) := blk_term bk in
  m2r_term_succs tm.

Definition m2r_all_succs {T : Set} (c : CFG.cfg T) : list block_id :=
  flat_map m2r_block_succs (blks c).

Fixpoint is_only_align_anns {T : Set} (anns : list (annotation T)) : bool :=
  match anns with
  | [] => true
  | ANN_align _ :: rest => is_only_align_anns rest
  | _ => false
  end.

Lemma is_only_align_anns_num_elts {T : Set} (anns : list (annotation T)) :
  is_only_align_anns anns = true ->
  find_option ann_num_elements anns = None /\
  flat_map full_ann_uses anns = [].
Proof using.
  induction anns as [| a rest IH]; cbn; [tauto |].
  destruct a; try (intros H; discriminate H).
  intros H; apply IH in H; exact H.
Qed.

Fixpoint is_debug_or_file_md {T : Set} (mds : list (metadata T)) : bool :=
  match mds with
  | [] => true
  | METADATA_Debug _ _ :: rest => is_debug_or_file_md rest
  | METADATA_File_info _ :: rest => is_debug_or_file_md rest
  | _ => false
  end.

Lemma is_debug_or_file_md_props (mds : list (metadata dtyp)) :
  is_debug_or_file_md mds = true ->
  load_metadata_attrs mds = [] /\
  metadata_range mds = None /\
  load_metadata_dereferenceable mds = None /\
  flat_map full_metadata_uses mds = [].
Proof using.
  induction mds as [| md rest IH]; cbn.
  - intros _; repeat split; reflexivity.
  - destruct md; try (intros H; discriminate H);
      intros H; apply IH in H as (H1 & H2 & H3 & H4);
      cbn; repeat split; assumption.
Qed.

Definition m2r_code_entry_uses {T : Set}
  (im : instr_id * instr T * list (metadata T)) : list raw_id :=
  let '(_, ins, md) := im in
  full_instr_uses ins ++ flat_map full_metadata_uses md.

Definition m2r_phi_entry_uses {T : Set}
  (pe : local_id * phi T * list (metadata T)) : list raw_id :=
  let '(_, ph, md) := pe in
  full_phi_uses ph ++ flat_map full_metadata_uses md.

Definition m2r_term_entry_uses {T : Set}
  (te : instr_id * terminator T * list (metadata T)) : list raw_id :=
  let '(_, tm, md) := te in
  full_term_uses tm ++ flat_map full_metadata_uses md.

(** Collect local IDs defined uniquely across [fargs ++ all_block_defs]
    by a single [INSTR_Alloca] instruction in [bks]. *)
Definition m2r_collect_unique_allocas
  (all_defs : list raw_id) (bks : ocfg dtyp) : list local_id :=
  flat_map
    (fun bk =>
       flat_map
         (fun im =>
            match im with
            | (IId q, INSTR_Alloca _ _, _) =>
                if Nat.eqb (m2r_count_id q all_defs) 1%nat then [q] else []
            | _ => []
            end)
         (blk_code bk))
    bks.

(** Pointer expressions guaranteed never to evaluate to [wildcard_prov] ([None])
    or to a provenance outside [U ++ safe_locals]. *)
Fixpoint m2r_safe_ptr_exp (safe_locals : list local_id) (e : exp dtyp) : bool :=
  match e with
  | EXP_Null | EXP_Poison => true
  | EXP_Ident (ID_Global _) => true
  | EXP_Ident (ID_Local q) => in_raw_ids q safe_locals
  | OP_GetElementPtr _ _ (_, base_e) _ => m2r_safe_ptr_exp safe_locals base_e
  | OP_Select _ _ (_, e1) (_, e2) =>
      m2r_safe_ptr_exp safe_locals e1 && m2r_safe_ptr_exp safe_locals e2
  | _ => false
  end.

Definition m2r_non_invoke_term {T : Set} (tm : terminator T) : bool :=
  match tm with
  | TERM_Invoke _ _ _ _ _ _ => false
  | _ => true
  end.

(** Module-level interprocedural safety check allowing [Stage 1] to promote
    slots in non-leaf and recursive functions when no function in [M] calls
    [puts], memory intrinsics, or dereferences unknown pointers. *)
Definition m2r_safe_mem_instr_any
  (safe_locals : list local_id)
  (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  let '(iid, ins, _) := im in
  match iid, ins with
  | IId _, INSTR_Op _ => true
  | IId _, INSTR_Alloca _ _ => true
  | IId _, INSTR_Load _ (_, ptr_e) _ => m2r_safe_ptr_exp safe_locals ptr_e
  | IVoid _, INSTR_Store _ (_, ptr_e) _ => m2r_safe_ptr_exp safe_locals ptr_e
  | _, INSTR_Call (_, fn_e) _ _ obs =>
      m2r_is_empty obs &&
      match intrinsic_exp fn_e with
      | None => true
      | Some _ => false
      end
  | IVoid _, INSTR_Comment _ => true
  | _, INSTR_Fence _ _ => true
  | _, _ => false
  end.

Definition m2r_defn_mem_safe (df : definition dtyp (CFG.cfg dtyp)) : bool :=
  let c := df_instrs df in
  let all_defs := df_args df ++ flat_map full_block_defs (blks c) in
  let safe_locals := m2r_collect_unique_allocas all_defs (blks c) in
  m2r_nodup_ids (List.map blk_id (blks c)) &&
  forallb
    (fun bk =>
       forallb (m2r_safe_mem_instr_any safe_locals) (blk_code bk) &&
       m2r_non_invoke_term (snd (fst (blk_term bk))))
    (blks c).

Definition m2r_module_interproc_safe (M : CFG.mcfg dtyp) : bool :=
  mcfg_no_inttoptr M &&
  match m_declarations M with
  | [] => true
  | _ => false
  end &&
  negb (in_raw_ids (Name "puts"%string) (List.map dc_name (m_declarations M))) &&
  forallb m2r_defn_mem_safe (m_definitions M).

(** ** Stage 1: Single-Slot SSA Promotion *)

(** Exact SSA replacement expressions for promoted [Store] and [Load] sites:
    - [mk_store_val_exp] evaluates [val_exp] at [Some dt] and checks base-value
      well-formedness via [dvalue_to_dvalue_base] (matching [Store]'s [FailureE]
      behavior on aggregate values without prematurely deserializing dead stores).
    - [mk_load_val_exp] serializes the current SSA register at [dt] and runs
      [memory_bytes_to_dvalue] at [dt], matching [Load] byte-for-byte across all
      scalar integer, pointer, and floating-point types. *)
Definition mk_store_val_exp (dt : dtyp) (val_exp : exp dtyp) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  let i1_ty := DTYPE_Base (DTYPE_I 1) in
  OP_ExtractElement
    (vec_ty,
     OP_InsertElement (vec_ty, EXP_Poison) (dt, val_exp) (i1_ty, EXP_Bool false))
    (i1_ty, EXP_Bool false).

Definition mk_load_val_exp (dt : dtyp) (cur_reg : local_id) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  OP_Conversion CONV_Bitcast vec_ty
    (EXP_Vector [(dt, EXP_Ident (ID_Local cur_reg))]) dt.

Fixpoint is_non_volatile_non_atomic_anns {T : Set} (anns : list (annotation T)) : bool :=
  match anns with
  | [] => true
  | ANN_volatile :: _ => false
  | ANN_atomic :: _ => false
  | ANN_ordering _ :: _ => false
  | ANN_syncscope _ :: _ => false
  | _ :: rest => is_non_volatile_non_atomic_anns rest
  end.

Definition is_promotable_load_of
  (p : local_id) (dt : dtyp)
  (im : instr_id * instr dtyp * list (metadata dtyp))
  : option local_id :=
  match im with
  | (IId dst, INSTR_Load dt_ld (du_ld, EXP_Ident (ID_Local q)) anns_ld, md) =>
      if raw_id_eqb q p
         && negb (raw_id_eqb dst p)
         && dtyp_eqb dt_ld dt
         && dtyp_eqb du_ld (DTYPE_Base DTYPE_Pointer)
         && m2r_is_empty (flat_map full_ann_uses anns_ld)
         && is_non_volatile_non_atomic_anns anns_ld
         && is_debug_or_file_md md
      then Some dst
      else None
  | _ => None
  end.

Definition is_promotable_store_of
  (p : local_id) (dt : dtyp)
  (im : instr_id * instr dtyp * list (metadata dtyp))
  : option (exp dtyp) :=
  match im with
  | (IVoid _, INSTR_Store (dt_st, val_exp) (du_st, EXP_Ident (ID_Local q)) anns_st, md) =>
      if raw_id_eqb q p
         && dtyp_eqb dt_st dt
         && dtyp_eqb du_st (DTYPE_Base DTYPE_Pointer)
         && negb (in_raw_ids p (full_exp_uses val_exp))
         && m2r_is_empty (flat_map full_ann_uses anns_st)
         && is_non_volatile_non_atomic_anns anns_st
         && is_debug_or_file_md md
      then Some val_exp
      else None
  | _ => None
  end.

Definition check_other_instr_for_slot
  (allow_calls : bool) (safe_locals_no_p : list local_id) (p : local_id)
  (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  negb (in_raw_ids p (m2r_code_entry_uses im)) &&
  let '(iid, ins, _) := im in
  match iid, ins with
  | IId _, INSTR_Op _ => true
  | IId _, INSTR_Alloca _ _ => true
  | IId _, INSTR_Load _ (_, ptr_e) _ => m2r_safe_ptr_exp safe_locals_no_p ptr_e
  | IVoid _, INSTR_Store _ (_, ptr_e) _ => m2r_safe_ptr_exp safe_locals_no_p ptr_e
  | _, INSTR_Call (_, fn_e) _ _ obs =>
      allow_calls && m2r_is_empty obs &&
      match intrinsic_exp fn_e with
      | None => true
      | Some _ => false
      end
  | IVoid _, INSTR_Comment _ => true
  | _, INSTR_Fence _ _ => true
  | _, _ => false
  end.

Definition check_code_entry_for_slot
  (allow_calls : bool) (safe_locals_no_p : list local_id)
  (p : local_id) (dt : dtyp)
  (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  match is_promotable_load_of p dt im with
  | Some _ => true
  | None =>
      match is_promotable_store_of p dt im with
      | Some _ => true
      | None => check_other_instr_for_slot allow_calls safe_locals_no_p p im
      end
  end.

Definition check_block_non_entry_for_slot
  (allow_calls : bool) (safe_locals_no_p : list local_id)
  (p : local_id) (dt : dtyp) (bk : block dtyp) : bool :=
  negb (in_raw_ids p (flat_map m2r_phi_entry_uses (blk_phis bk))) &&
  forallb (check_code_entry_for_slot allow_calls safe_locals_no_p p dt) (blk_code bk) &&
  negb (in_raw_ids p (m2r_term_entry_uses (blk_term bk))) &&
  m2r_non_invoke_term (snd (fst (blk_term bk))).

Fixpoint rewrite_code_for_slot
  (p : local_id) (dt : dtyp) (cur_reg : local_id) (avoid : list raw_id)
  (cd : code dtyp)
  : code dtyp * local_id * list raw_id :=
  match cd with
  | [] => ([], cur_reg, avoid)
  | im :: rest =>
      match is_promotable_load_of p dt im with
      | Some dst =>
          let '(rest', end_reg, avoid') :=
            rewrite_code_for_slot p dt cur_reg avoid rest in
          ((IId dst, INSTR_Op (mk_load_val_exp dt cur_reg), []) :: rest',
           end_reg, avoid')
      | None =>
          match is_promotable_store_of p dt im with
          | Some val_exp =>
              let st_reg := fresh_name "m2r_st" avoid in
              let '(rest', end_reg, avoid') :=
                rewrite_code_for_slot p dt st_reg (st_reg :: avoid) rest in
              ((IId st_reg, INSTR_Op (mk_store_val_exp dt val_exp), []) :: rest',
               end_reg, avoid')
          | None =>
              let '(rest', end_reg, avoid') :=
                rewrite_code_for_slot p dt cur_reg avoid rest in
              (im :: rest', end_reg, avoid')
          end
      end
  end.

Fixpoint rewrite_non_entry_blocks_pass1
  (init_bid : block_id) (p : local_id) (dt : dtyp)
  (init_end_reg : local_id) (init_code' : code dtyp)
  (avoid : list raw_id)
  (bk_phis : list (block dtyp * local_id))
  : list (block dtyp * local_id * code dtyp * local_id) * list raw_id :=
  match bk_phis with
  | [] => ([], avoid)
  | (bk, phi_reg) :: rest =>
      if raw_id_eqb (blk_id bk) init_bid then
        let '(rest_out, avoid') :=
          rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid rest in
        ((bk, phi_reg, init_code', init_end_reg) :: rest_out, avoid')
      else
        let '(cd', end_reg, avoid1) :=
          rewrite_code_for_slot p dt phi_reg avoid (blk_code bk) in
        let '(rest_out, avoid2) :=
          rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid1 rest in
        ((bk, phi_reg, cd', end_reg) :: rest_out, avoid2)
  end.

Fixpoint lookup_end_reg
  (end_map : list (block_id * local_id)) (bid : block_id) (default_reg : local_id)
  : local_id :=
  match end_map with
  | [] => default_reg
  | (b, r) :: rest =>
      if raw_id_eqb b bid then r else lookup_end_reg rest bid default_reg
  end.

Definition build_promoted_blocks
  (init_bid : block_id) (dt : dtyp) (init_reg : local_id)
  (all_bks : ocfg dtyp)
  (pass1_out : list (block dtyp * local_id * code dtyp * local_id))
  : ocfg dtyp :=
  let end_map :=
    List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out in
  List.map
    (fun '(bk, phi_reg, cd', _) =>
       if raw_id_eqb (blk_id bk) init_bid then
         {| blk_id       := blk_id bk;
            blk_phis     := blk_phis bk;
            blk_code     := cd';
            blk_term     := blk_term bk;
            blk_comments := blk_comments bk |}
       else
         let preds :=
           List.filter
             (fun b_pred => in_raw_ids (blk_id bk) (m2r_block_succs b_pred))
             all_bks in
         let incoming :=
           List.map
             (fun b_pred =>
                (blk_id b_pred,
                 EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_pred) init_reg))))
             preds in
         {| blk_id       := blk_id bk;
            blk_phis     := (phi_reg, Phi [] dt incoming, []) :: blk_phis bk;
            blk_code     := cd';
            blk_term     := blk_term bk;
            blk_comments := blk_comments bk |})
    pass1_out.

Definition promote_slot_in_cfg
  (fargs : list local_id) (c : CFG.cfg dtyp) (b_init : block dtyp)
  (pre_al : code dtyp)
  (al_ins : instr_id * instr dtyp * list (metadata dtyp))
  (post_al : code dtyp)
  (p : local_id) (dt : dtyp) : CFG.cfg dtyp :=
  let avoid0 := fargs ++ cfg_all_ids c in
  let init_reg := fresh_name "m2r_init" avoid0 in
  let avoid1 := init_reg :: avoid0 in
  let phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1 in
  let avoid2 := phi_regs ++ avoid1 in
  let '(post_al', init_end_reg, avoid3) :=
    rewrite_code_for_slot p dt init_reg avoid2 post_al in
  let init_op :=
    (IId init_reg,
     INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
     []) in
  let init_code' := pre_al ++ al_ins :: init_op :: post_al' in
  let bk_phis := List.combine (blks c) phi_regs in
  let '(pass1_out, _) :=
    rewrite_non_entry_blocks_pass1
      (init c) p dt init_end_reg init_code' avoid3 bk_phis in
  {| init := init c;
     blks := build_promoted_blocks (init c) dt init_reg (blks c) pass1_out;
     args := args c |}.

Fixpoint find_promotable_in_init_code
  (allow_calls : bool) (all_defs : list raw_id) (all_uses : list raw_id)
  (safe_locals : list local_id) (init_bid : block_id) (bks : ocfg dtyp)
  (b_init : block dtyp)
  (acc_pre : code dtyp) (rem : code dtyp)
  : option (code dtyp * (instr_id * instr dtyp * list (metadata dtyp)) *
            code dtyp * local_id * dtyp) :=
  match rem with
  | [] => None
  | im :: post_al =>
      let pre_al := List.rev acc_pre in
      let cand :=
        match im with
        | (IId p, INSTR_Alloca dt anns_al, md_al) =>
            let safe_no_p :=
              List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
            if is_scalar_dtyp dt
               && is_only_align_anns anns_al
               && is_debug_or_file_md md_al
               && Nat.eqb (m2r_count_id p all_defs) 1%nat
               && in_raw_ids p all_uses
               && forallb (check_other_instr_for_slot allow_calls safe_no_p p) pre_al
               && forallb (check_code_entry_for_slot allow_calls safe_no_p p dt) post_al
               && negb (in_raw_ids p (m2r_term_entry_uses (blk_term b_init)))
               && m2r_non_invoke_term (snd (fst (blk_term b_init)))
               && forallb
                    (fun bk =>
                       if raw_id_eqb (blk_id bk) init_bid then true
                       else check_block_non_entry_for_slot allow_calls safe_no_p p dt bk)
                    bks
            then Some (pre_al, im, post_al, p, dt)
            else None
        | _ => None
        end
      in
      match cand with
      | Some res => Some res
      | None =>
          find_promotable_in_init_code
            allow_calls all_defs all_uses safe_locals init_bid bks b_init
            (im :: acc_pre) post_al
      end
  end.

Definition try_promote_slot_in_defn
  (interproc_safe : bool)
  (df : definition dtyp (CFG.cfg dtyp))
  : option (definition dtyp (CFG.cfg dtyp)) :=
  let fargs := df_args df in
  let c := df_instrs df in
  if m2r_nodup_ids (List.map blk_id (blks c))
     && negb (in_raw_ids (init c) (m2r_all_succs c))
     && cfg_no_block_addresses c
  then
    match find_block (blks c) (init c) with
    | Some b_init =>
        if m2r_is_empty (blk_phis b_init) then
          let all_defs := fargs ++ flat_map full_block_defs (blks c) in
          let all_uses := flat_map full_block_uses (blks c) in
          let safe_locals := m2r_collect_unique_allocas all_defs (blks c) in
          match find_promotable_in_init_code
                  interproc_safe all_defs all_uses safe_locals
                  (init c) (blks c) b_init [] (blk_code b_init) with
          | Some (pre_al, al_ins, post_al, p, dt) =>
              Some {| df_prototype := df_prototype df;
                      df_args      := df_args df;
                      df_instrs    := promote_slot_in_cfg
                                        fargs c b_init pre_al al_ins post_al p dt |}
          | None => None
          end
        else None
    | None => None
    end
  else None.

Fixpoint promote_first_in_defs
  (interproc_safe : bool)
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  : option (list (definition dtyp (CFG.cfg dtyp))) :=
  match defs with
  | [] => None
  | df :: rest =>
      match try_promote_slot_in_defn interproc_safe df with
      | Some df' => Some (df' :: rest)
      | None => option_map (cons df) (promote_first_in_defs interproc_safe rest)
      end
  end.

Definition promote_slot_step_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  if mcfg_no_inttoptr M then
    let interproc_safe := m2r_module_interproc_safe M in
    match promote_first_in_defs interproc_safe (m_definitions M) with
    | None => M
    | Some defs' =>
        {| m_name         := m_name M;
           m_target       := m_target M;
           m_datalayout   := m_datalayout M;
           m_type_defs    := m_type_defs M;
           m_globals      := m_globals M;
           m_declarations := m_declarations M;
           m_definitions  := defs' |}
    end
  else M.

Fixpoint promote_slot_iter (fuel : nat) (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  match fuel with
  | O => M
  | S fuel' => promote_slot_iter fuel' (promote_slot_step_mcfg M)
  end.

(** ** Stage 2: Reverse-Order Dead Scalar Alloca Elimination *)

Definition check_no_alloca_or_call_instr
  (safe_locals_no_p : list local_id)
  (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
  let '(iid, ins, md) := im in
  match iid, ins with
  | IId _, INSTR_Op _ => true
  | IId _, INSTR_Load _ (_, ptr_e) _ =>
      m2r_safe_ptr_exp safe_locals_no_p ptr_e &&
      match load_metadata_dereferenceable md with
      | None => true
      | Some _ => false
      end
  | IVoid _, INSTR_Store _ (_, ptr_e) _ => m2r_safe_ptr_exp safe_locals_no_p ptr_e
  | IVoid _, INSTR_Comment _ => true
  | _, INSTR_Fence _ _ => true
  | _, _ => false
  end.

(** Scan [rem] and pick a dead scalar [Alloca] after which NO [Alloca] or
    [Call] occurs in [post_al] (automatically picking the last dead [Alloca]
    when multiple dead [Alloca]s exist in [b_init]!). *)
Fixpoint find_trailing_dead_alloca_in_code
  (all_defs : list raw_id) (all_uses : list raw_id)
  (safe_locals : list local_id)
  (acc_pre : code dtyp) (rem : code dtyp)
  : option (code dtyp * (instr_id * instr dtyp * list (metadata dtyp)) *
            code dtyp * local_id * dtyp) :=
  match rem with
  | [] => None
  | im :: post_al =>
      match find_trailing_dead_alloca_in_code
              all_defs all_uses safe_locals (im :: acc_pre) post_al with
      | Some later => Some later
      | None =>
          let pre_al := List.rev acc_pre in
          match im with
          | (IId p, INSTR_Alloca dt anns_al, md_al) =>
              let safe_no_p :=
                List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
              if is_scalar_dtyp dt
                 && is_only_align_anns anns_al
                 && is_debug_or_file_md md_al
                 && Nat.eqb (m2r_count_id p all_defs) 1%nat
                 && negb (in_raw_ids p all_uses)
                 && forallb (check_other_instr_for_slot false safe_no_p p) pre_al
                 && forallb (check_no_alloca_or_call_instr safe_no_p) post_al
              then Some (pre_al, im, post_al, p, dt)
              else None
          | _ => None
          end
      end
  end.

Definition try_elim_dead_alloca_in_defn
  (df : definition dtyp (CFG.cfg dtyp))
  : option (definition dtyp (CFG.cfg dtyp)) :=
  let fargs := df_args df in
  let c := df_instrs df in
  if m2r_nodup_ids (List.map blk_id (blks c))
     && negb (in_raw_ids (init c) (m2r_all_succs c))
     && cfg_no_block_addresses c
  then
    match find_block (blks c) (init c) with
    | Some b_init =>
        if m2r_is_empty (blk_phis b_init)
           && m2r_non_invoke_term (snd (fst (blk_term b_init)))
        then
          let all_defs := fargs ++ flat_map full_block_defs (blks c) in
          let all_uses := flat_map full_block_uses (blks c) in
          let safe_locals := m2r_collect_unique_allocas all_defs (blks c) in
          match find_trailing_dead_alloca_in_code
                  all_defs all_uses safe_locals [] (blk_code b_init) with
          | Some (pre_al, _, post_al, p, _) =>
              let safe_no_p :=
                List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
              if forallb
                   (fun bk =>
                      if raw_id_eqb (blk_id bk) (init c) then true
                      else
                        forallb (check_no_alloca_or_call_instr safe_no_p) (blk_code bk) &&
                        m2r_non_invoke_term (snd (fst (blk_term bk))))
                   (blks c)
              then
                let new_blks :=
                  List.map
                    (fun bk =>
                       if raw_id_eqb (blk_id bk) (init c) then
                         {| blk_id       := blk_id bk;
                            blk_phis     := blk_phis bk;
                            blk_code     := pre_al ++ post_al;
                            blk_term     := blk_term bk;
                            blk_comments := blk_comments bk |}
                       else bk)
                    (blks c) in
                Some {| df_prototype := df_prototype df;
                        df_args      := df_args df;
                        df_instrs    := {| init := init c;
                                           blks := new_blks;
                                           args := args c |} |}
              else None
          | None => None
          end
        else None
    | None => None
    end
  else None.

Fixpoint elim_first_dead_alloca_in_defs
  (defs : list (definition dtyp (CFG.cfg dtyp)))
  : option (list (definition dtyp (CFG.cfg dtyp))) :=
  match defs with
  | [] => None
  | df :: rest =>
      match try_elim_dead_alloca_in_defn df with
      | Some df' => Some (df' :: rest)
      | None => option_map (cons df) (elim_first_dead_alloca_in_defs rest)
      end
  end.

Definition elim_dead_alloca_step_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  if mcfg_no_inttoptr M then
    match elim_first_dead_alloca_in_defs (m_definitions M) with
    | None => M
    | Some defs' =>
        {| m_name         := m_name M;
           m_target       := m_target M;
           m_datalayout   := m_datalayout M;
           m_type_defs    := m_type_defs M;
           m_globals      := m_globals M;
           m_declarations := m_declarations M;
           m_definitions  := defs' |}
    end
  else M.

Fixpoint elim_dead_alloca_iter (fuel : nat) (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  match fuel with
  | O => M
  | S fuel' => elim_dead_alloca_iter fuel' (elim_dead_alloca_step_mcfg M)
  end.

(** ** Top-Level Pass Entry Points *)

Definition mem2reg_default_fuel : nat := 32%nat.

Definition mem2reg_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  elim_dead_alloca_iter mem2reg_default_fuel
    (promote_slot_iter mem2reg_default_fuel M).

Definition mem2reg_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  mem2reg_mcfg (convert_types M).


(** * 2. Provenance-Model & Interpreter Combinators *)

Section BindCompat.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  Lemma m2r_refine_prov_bind {R1 R2 S1 S2}
    (RR : list N -> R1 -> R2 -> Prop) (RS : list N -> S1 -> S2 -> Prop)
    (U : list N)
    (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (k1 : R1 -> itree ProvBotE S1) (k2 : R2 -> itree ProvBotE S2)
    (Ht : refine_prov RR U t1 t2)
    (Hk : forall U' r1 r2, RR U' r1 r2 -> refine_prov RS U' (k1 r1) (k2 r2)) :
    refine_prov RS U (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    eapply PassCommon.refine_prov_bind; [exact Ht |].
    intros U' r1 r2 _ HR; exact (Hk U' r1 r2 HR).
  Qed.
End BindCompat.

#[local] Notation refine_prov_bind := m2r_refine_prov_bind (only parsing).

#[local] Definition mrec_ctx {IP : IPtr} {IPT : @IPtrTheory IP}
  (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
  : @CallE (@ParamsV IP IPT) ~> @CFGtop (@ParamsV IP IPT) :=
  fun T call_ev =>
    match call_ev with
    | Call dt cc fv args =>
        @Monads.bind (@CFGtop (@ParamsV IP IPT)) _ _ _
          (EOU_to_itree (check_callee fv))
          (fun _ =>
             match lookup_defn fv fundefs with
             | Some f_den => f_den cc args
             | None => Functor.fmap inr (external_call dt fv args)
             end)
    end.

Section ModelCombinators.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.

  (** ** Strong Bisimulation Equations for [interp_mrec], [interp_mcfg_model], [interp_cfg_model] *)

  Lemma interp_mrec_ret {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R} (x : R) :
    interp_mrec ctx (Ret x) ≅ Ret x.
  Proof using.
    rewrite unfold_interp_mrec; reflexivity.
  Qed.

  Lemma interp_mrec_tau {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R}
    (t : itree (D +' E) R) :
    interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
  Proof using.
    rewrite unfold_interp_mrec; reflexivity.
  Qed.

  Lemma interp_mrec_proper_eq {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R} :
    forall (t1 t2 : itree (D +' E) R),
      t1 ≅ t2 ->
      interp_mrec ctx t1 ≅ interp_mrec ctx t2.
  Proof using.
    ginit; gcofix CIH; intros t1 t2 Heq.
    rewrite (unfold_interp_mrec ctx t1), (unfold_interp_mrec ctx t2).
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X [d | e] k1 k2 Hk]; pclearbot.
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, Hm.
    - gstep; constructor; gfinal; left; apply CIH.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x _ <-; apply Hk.
    - gstep; constructor; intros x; gstep; constructor; gfinal; left; apply CIH, Hk.
  Qed.

  Lemma interp_mrec_bind_eq {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R S} :
    forall (t : itree (D +' E) R) (k : R -> itree (D +' E) S),
      interp_mrec ctx (ITree.bind t k) ≅
      ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
  Proof using.
    ginit; gcofix CIH; intros t k.
    rewrite (unfold_interp_mrec ctx t).
    destruct (observe t) as [r | m | X [d | e] h] eqn:Hot; cbn [_interp_mrec].
    - assert (Htk : ITree.bind t k ≅ k r).
      { rewrite (itree_eta t), Hot, Eqit.bind_ret_l; reflexivity. }
      rewrite (interp_mrec_proper_eq ctx _ _ Htk), Eqit.bind_ret_l.
      gfinal; right; eapply paco2_mon; [reflexivity | intros ? ? []].
    - rewrite (unfold_interp_mrec ctx (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
    - rewrite (unfold_interp_mrec ctx (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_tau.
      gstep; constructor.
      rewrite (interp_mrec_proper_eq ctx _ _ (Eqit.bind_bind (ctx X d) h k)).
      gfinal; left; apply CIH.
    - rewrite (unfold_interp_mrec ctx (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_vis.
      gstep; constructor; intros x.
      rewrite Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
  Qed.

  Lemma interp_mcfg_model_ret {R} (x : R) (s : FusedS) :
    interp_mcfg_model (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_mcfg_model_tau {R} (t : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_mcfg_model (Tau t) s ≅ Tau (interp_mcfg_model t s).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_tau, interp_state_tau; reflexivity.
  Qed.

  Lemma interp_mcfg_model_bind {R S}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (k : R -> @MCFGtop (@ParamsV IP IPT) S) (s : FusedS) :
    interp_mcfg_model (ITree.bind t k) s ≅
    ITree.bind (interp_mcfg_model t s) (fun '(s', x) => interp_mcfg_model (k x) s').
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_bind, interp_state_bind; reflexivity.
  Qed.

  Lemma interp_mcfg_model_obs_eq {R}
    (t1 t2 : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_mcfg_model t1 s ≅ interp_mcfg_model t2 s.
  Proof using.
    intros Heq; unfold interp_mcfg_model, interp_intrinsics.
    rewrite Heq; reflexivity.
  Qed.

  Definition interp_cfg_model {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res R) :=
    interp_mcfg_model (interp_mrec (mrec_ctx ctx) t) s.

  Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
    (args : list (@dvalue (@ParamsV IP IPT))) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (mrec_ctx fundefs) (mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  Lemma interp_cfg_model_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    interp_cfg_model ctx (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_ret (mrec_ctx ctx) x)).
    apply interp_mcfg_model_ret.
  Qed.

  Lemma interp_cfg_model_tau {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_cfg_model ctx (Tau t) s ≅ Tau (interp_cfg_model ctx t s).
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_tau (mrec_ctx ctx) t)).
    apply interp_mcfg_model_tau.
  Qed.

  Lemma interp_cfg_model_bind {R S}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R)
    (k : R -> @CFGtop (@ParamsV IP IPT) S) (s : FusedS) :
    interp_cfg_model ctx (ITree.bind t k) s ≅
    ITree.bind (interp_cfg_model ctx t s) (fun '(s', x) => interp_cfg_model ctx (k x) s').
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_bind_eq (mrec_ctx ctx) t k)).
    apply interp_mcfg_model_bind.
  Qed.

  Lemma interp_cfg_model_obs_eq {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t1 t2 : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_cfg_model ctx t1 s ≅ interp_cfg_model ctx t2 s.
  Proof using.
    intros Heq; unfold interp_cfg_model.
    apply interp_mcfg_model_obs_eq, interp_mrec_proper_eq, Heq.
  Qed.

  (** ** [refine_prov] Combinators & Finite-Tau Closure ([tau_star]) *)

  Lemma refine_prov_ret {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (r1 : R1) (r2 : R2) :
    RR U r1 r2 ->
    refine_prov RR U (Ret r1) (Ret r2).
  Proof using.
    intros H; pstep; apply RP_Step; cbn; exact H.
  Qed.

  Lemma refine_prov_tau_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (m1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U m1 t2 ->
    refine_prov RR U (Tau m1) t2.
  Proof using.
    intros H; punfold H; pstep.
    eapply RP_TauL; [reflexivity | eapply refine_prov__mon; [exact H | auto]].
  Qed.

  Lemma refine_prov_tau_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (m2 : itree ProvBotE R2) :
    refine_prov RR U t1 m2 ->
    refine_prov RR U t1 (Tau m2).
  Proof using.
    intros H; punfold H; pstep.
    eapply RP_TauR; [reflexivity | eapply refine_prov__mon; [exact H | auto]].
  Qed.

  Lemma refine_prov_tau_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (m1 : itree ProvBotE R1) (m2 : itree ProvBotE R2) :
    refine_prov RR U m1 m2 ->
    refine_prov RR U (Tau m1) (Tau m2).
  Proof using.
    intros H; pstep; apply RP_Step; cbn; left; exact H.
  Qed.

  Lemma refine_prov_ub_vis_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) {X} (e : ProvBotE X) (k1 : X -> itree ProvBotE R1)
    (t2 : itree ProvBotE R2) :
    is_ub_prov e = true ->
    refine_prov RR U (Vis e k1) t2.
  Proof using.
    intros Hub; pstep; apply RP_Step; cbn; left; exact Hub.
  Qed.

  Lemma refine_prov_fresh_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (k2 : N -> itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) (k2 p)) ->
    refine_prov RR U (Vis (inl1 FreshProv) k1) (Vis (inl1 FreshProv) k2).
  Proof using.
    intros Hk; pstep; apply RP_Step; cbn.
    right; right; intros p Hp; left; apply Hk, Hp.
  Qed.

  Lemma refine_prov_fresh_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) t2) ->
    refine_prov RR U (Vis (inl1 FreshProv) k1) t2.
  Proof using.
    intros Hk; pstep; apply RP_Step; cbn.
    right; left; intros p Hp; left; apply Hk, Hp.
  Qed.

  Lemma refine_prov_incl {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall (U0 U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2),
      incl U0 U ->
      refine_prov RR U t1 t2 ->
      refine_prov (fun U' r1 r2 => incl U0 U' /\ RR U' r1 r2) U t1 t2.
  Proof using.
    intros U0; pcofix CIH.
    intros U t1 t2 Hincl Hrel; pstep; punfold Hrel.
    revert U0 Hincl;
      induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros U0 Hincl.
    - apply RP_Step; unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; split; assumption.
      + destruct (observe t2); try contradiction; pclearbot; right; eapply CIH; eassumption.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot; right; eapply CIH; [| exact Hleft].
          intros z Hz; right; apply Hincl, Hz.
        * right; right; destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot; right; eapply CIH; [| exact Hboth].
             intros z Hz; right; apply Hincl, Hz.
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; eapply CIH; [| exact HA].
             intros z Hz; apply in_app_iff; right; apply Hincl, Hz.
    - eapply RP_TauL; [exact Ht1 | apply IH, Hincl].
    - eapply RP_TauR; [exact Ht2 | apply IH, Hincl].
  Qed.

  Lemma refine_prov_weaken_incl {R1 R2}
    (RR RR' : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (Hrel : refine_prov RR U t1 t2)
    (Himp : forall U' r1 r2, incl U U' -> RR U' r1 r2 -> RR' U' r1 r2) :
    refine_prov RR' U t1 t2.
  Proof using.
    eapply refine_prov_obs_eq;
      [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply PassCommon.refine_prov_bind; [exact Hrel |].
    intros U' r1 r2 Hincl Hr; apply refine_prov_ret; exact (Himp U' r1 r2 Hincl Hr).
  Qed.

  Lemma refine_prov_weaken {R1 R2}
    (RR RR' : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (Hrel : refine_prov RR U t1 t2)
    (Himp : forall U' r1 r2, RR U' r1 r2 -> RR' U' r1 r2) :
    refine_prov RR' U t1 t2.
  Proof using.
    eapply refine_prov_weaken_incl; [exact Hrel |].
    intros U' r1 r2 _ Hr; exact (Himp U' r1 r2 Hr).
  Qed.

  Lemma refine_prov_iter {I1 I2 R1 R2}
    (RI : list N -> I1 -> I2 -> Prop)
    (RR : list N -> R1 -> R2 -> Prop)
    (b1 : I1 -> itree ProvBotE (I1 + R1))
    (b2 : I2 -> itree ProvBotE (I2 + R2))
    (U0 : list N)
    (Hbody : forall U i1 i2,
               incl U0 U ->
               RI U i1 i2 ->
               refine_prov
                 (fun U' lr1 lr2 =>
                    match lr1, lr2 with
                    | inl j1, inl j2 => RI U' j1 j2
                    | inr r1, inr r2 => RR U' r1 r2
                    | _, _ => False
                    end)
                 U (b1 i1) (b2 i2)) :
    forall i1 i2,
      RI U0 i1 i2 ->
      refine_prov RR U0 (ITree.iter b1 i1) (ITree.iter b2 i2).
  Proof using.
    set (RBody := fun U' (lr1 : I1 + R1) (lr2 : I2 + R2) =>
                    incl U0 U' /\
                    match lr1, lr2 with
                    | inl j1, inl j2 => RI U' j1 j2
                    | inr r1, inr r2 => RR U' r1 r2
                    | _, _ => False
                    end).
    set (k1 := fun lr : I1 + R1 =>
                 match lr with
                 | inl j => Tau (ITree.iter b1 j)
                 | inr r => Ret r
                 end).
    set (k2 := fun lr : I2 + R2 =>
                 match lr with
                 | inl j => Tau (ITree.iter b2 j)
                 | inr r => Ret r
                 end).
    set (r_it := fun U (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) =>
                   exists u1 u2,
                     ITree.bind u1 k1 ≅ t1 /\
                     ITree.bind u2 k2 ≅ t2 /\
                     refine_prov RBody U u1 u2).
    assert (Hr_eq : forall U a1 a1' a2 a2',
                      a1 ≅ a1' -> a2 ≅ a2' -> r_it U a1 a2 -> r_it U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 (u1 & u2 & Eu1 & Eu2 & Hu).
      exists u1, u2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hu]]. }
    assert (Hcore : forall U t1 t2, r_it U t1 t2 -> refine_prov RR U t1 t2).
    { pcofix CIH.
      intros U t1 t2 (u1 & u2 & Eu1 & Eu2 & Hu); pstep.
      eapply refine_prov__mon with (r := r_it);
        [| intros U' a1 a2 Hr; right; apply CIH, Hr].
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Eu1 | exact Eu2 |].
      punfold Hu; clear t1 t2 Eu1 Eu2.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [lr1 | m1 | X1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          destruct Hstep as [Hincl Hlr].
          destruct lr1 as [j1 | r1], lr2 as [j2 | r2]; try contradiction.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn.
            exists (b1 j1), (b2 j2).
            split; [symmetry; apply unfold_iter |].
            split; [symmetry; apply unfold_iter |].
            apply refine_prov_incl; [exact Hincl | apply Hbody; assumption].
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn; exact Hlr.
        + destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2.
          exists m1, m2; repeat split; try reflexivity; exact Hstep.
        + apply RP_Step; unfold rp_step_body; rewrite (observe_bind u1 k1), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            exists (h1 p), u2; repeat split; try reflexivity; exact Hleft.
          * right; right; destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 k2), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               exists (h1 p), (h2 p); repeat split; try reflexivity; exact Hboth.
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               exists (h1 a1), (h2 a2); repeat split; try reflexivity; exact HA.
      - eapply RP_TauL; [rewrite (observe_bind u1 k1), Hu1; reflexivity | exact IH].
      - eapply RP_TauR; [rewrite (observe_bind u2 k2), Hu2; reflexivity | exact IH]. }
    intros i1 i2 Hinit; apply Hcore.
    exists (b1 i1), (b2 i2).
    split; [symmetry; apply unfold_iter |].
    split; [symmetry; apply unfold_iter |].
    apply refine_prov_incl; [apply incl_refl | apply Hbody; [apply incl_refl | exact Hinit]].
  Qed.

  Lemma refine_mcfg_model_bind {A1 A2 B1 B2}
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @MCFGtop (@ParamsV IP IPT) A1) (t2 : @MCFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @MCFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @MCFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov RA U (interp_mcfg_model t1 s1) (interp_mcfg_model t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       refine_prov RB U' (interp_mcfg_model (k1 a1) s1') (interp_mcfg_model (k2 a2) s2')) ->
    refine_prov RB U
      (interp_mcfg_model (ITree.bind t1 k1) s1)
      (interp_mcfg_model (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind | symmetry; apply interp_mcfg_model_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl RA U U _ _ (incl_refl U) Ht).
    - intros U' [s1' a1] [s2' a2] [Hincl Ha]; eapply Hk; eassumption.
  Qed.

  Lemma refine_cfg_model_bind {A1 A2 B1 B2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       refine_prov RB U' (interp_cfg_model ctx1 (k1 a1) s1') (interp_cfg_model ctx2 (k2 a2) s2')) ->
    refine_prov RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl RA U U _ _ (incl_refl U) Ht).
    - intros U' [s1' a1] [s2' a2] [Hincl Ha]; eapply Hk; eassumption.
  Qed.

  Inductive tau_star {R} : itree ProvBotE R -> itree ProvBotE R -> Prop :=
  | TS_Refl t : tau_star t t
  | TS_Eq t1 t2 t3 : t1 ≅ t2 -> tau_star t2 t3 -> tau_star t1 t3
  | TS_Tau m t' : tau_star m t' -> tau_star (Tau m) t'.

  Lemma tau_star_trans {R} (t1 t2 t3 : itree ProvBotE R) :
    tau_star t1 t2 ->
    tau_star t2 t3 ->
    tau_star t1 t3.
  Proof using.
    intros H12; revert t3;
      induction H12 as [t | a b c Heq _ IH | m b _ IH]; intros t3 H23.
    - exact H23.
    - eapply TS_Eq; [exact Heq | apply IH, H23].
    - apply TS_Tau, IH, H23.
  Qed.

  Lemma tau_star_bind {A B}
    (u u' : itree ProvBotE A) (k : A -> itree ProvBotE B) :
    tau_star u u' ->
    tau_star (ITree.bind u k) (ITree.bind u' k).
  Proof using.
    intros Hts; induction Hts as [t | t1 t2 t3 Heq _ IH | m t' _ IH].
    - apply TS_Refl.
    - eapply TS_Eq; [rewrite Heq; reflexivity | exact IH].
    - eapply TS_Eq; [apply Eqit.bind_tau | apply TS_Tau, IH].
  Qed.

  Lemma refine_prov_tau_star_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    tau_star t1 t1' ->
    refine_prov RR U t1' t2 ->
    refine_prov RR U t1 t2.
  Proof using.
    intros Hts; revert t2;
      induction Hts as [t | a b c Heq _ IH | m b _ IH]; intros t2 Hrel.
    - exact Hrel.
    - eapply refine_prov_obs_eq; [symmetry; exact Heq | reflexivity | apply IH, Hrel].
    - apply refine_prov_tau_l, IH, Hrel.
  Qed.

  Lemma refine_prov_tau_star_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_star t2 t2' ->
    refine_prov RR U t1 t2' ->
    refine_prov RR U t1 t2.
  Proof using.
    intros Hts; revert t1;
      induction Hts as [t | a b c Heq _ IH | m b _ IH]; intros t1 Hrel.
    - exact Hrel.
    - eapply refine_prov_obs_eq; [reflexivity | symmetry; exact Heq | apply IH, Hrel].
    - apply refine_prov_tau_r, IH, Hrel.
  Qed.

  (** ** Primitive Event Reductions under [interp_mcfg_model] & [interp_cfg_model] *)

  Lemma interp_cfg_model_call
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT))) (s : FusedS) :
    interp_cfg_model ctx (call dt cc fv vs) s ≅
    Tau (interp_cfg_model ctx (mrec_ctx ctx _ (Call dt cc fv vs)) s).
  Proof using.
    unfold call, trigger, ITree.trigger, interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
    cbn [_interp_mrec subevent resum ReSum_inl ReSum_id id_ Id_IFun inl1 observe].
    rewrite interp_mcfg_model_tau.
    rewrite (interp_mcfg_model_obs_eq _ _ s
               (interp_mrec_proper_eq (mrec_ctx ctx) _ _ (Eqit.bind_ret_r _))).
    reflexivity.
  Qed.

  Lemma interp_mcfg_model_non_intr {X}
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_mcfg_model (ITree.trigger me) s ≅
    ITree.bind (interp_vellvm_prov_h me s)
      (fun '(s', x) => Tau (Tau (Ret (s', x)))).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics, ITree.trigger.
    rewrite unfold_interp; cbn [_interp observe]; rewrite Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, interp_tau, interp_ret, interp_state_tau, interp_state_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_model_non_intr {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_cfg_model ctx (ITree.trigger (inr1 me)) s ≅
    ITree.bind (interp_vellvm_prov_h me s)
      (fun '(s', x) => Tau (Tau (Tau (Ret (s', x))))).
  Proof using.
    unfold interp_cfg_model, ITree.trigger.
    rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
    cbn [_interp_mrec observe].
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite unfold_interp; cbn [_interp observe]; rewrite Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, interp_tau, interp_state_tau.
    change (interp_state interp_vellvm_prov_h
              (interp interp_intrinsics_h (interp_mrec (mrec_ctx ctx) (Ret x))) s')
      with (interp_cfg_model ctx (Ret x) s').
    rewrite interp_cfg_model_ret; reflexivity.
  Qed.

  Lemma tau_star_mcfg_det {X}
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s s' : FusedS) (v : X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hstep : interp_vellvm_prov_h me s ≅ Ret (s', v)) :
    tau_star (interp_mcfg_model (ITree.trigger me) s) (Ret (s', v)).
  Proof using.
    eapply TS_Eq; [apply interp_mcfg_model_non_intr, Hni |].
    eapply TS_Eq; [rewrite Hstep, Eqit.bind_ret_l; reflexivity |].
    apply TS_Tau, TS_Tau, TS_Refl.
  Qed.

  Lemma tau_star_cfg_det {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s s' : FusedS) (v : X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hstep : interp_vellvm_prov_h me s ≅ Ret (s', v)) :
    tau_star (interp_cfg_model ctx (ITree.trigger (inr1 me)) s) (Ret (s', v)).
  Proof using.
    eapply TS_Eq; [apply interp_cfg_model_non_intr, Hni |].
    eapply TS_Eq; [rewrite Hstep, Eqit.bind_ret_l; reflexivity |].
    apply TS_Tau, TS_Tau, TS_Tau, TS_Refl.
  Qed.

  Lemma refine_mcfg_raiseUB_l {X R2}
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_mcfg_model (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr _ s1 Logic.eq_refl); reflexivity | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_mcfg_raiseOOM_l {X R2}
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_mcfg_model (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr _ s1 Logic.eq_refl); reflexivity | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_mcfg_raise_both {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_mcfg_model (raise msg1) s1)
      (interp_mcfg_model (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind | symmetry; apply interp_mcfg_model_bind |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr _ s1 Logic.eq_refl); reflexivity
      | symmetry; rewrite (interp_mcfg_model_non_intr _ s2 Logic.eq_refl); reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
      | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_cfg_raiseUB_l {X R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_model ctx1 (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_cfg_model_non_intr ctx1 _ s1 Logic.eq_refl); reflexivity | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_cfg_raiseOOM_l {X R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_model ctx1 (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_cfg_model_non_intr ctx1 _ s1 Logic.eq_refl); reflexivity | reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_cfg_raise_both {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_cfg_model ctx1 (raise msg1) s1)
      (interp_cfg_model ctx2 (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_cfg_model_non_intr ctx1 _ s1 Logic.eq_refl); reflexivity
      | symmetry; rewrite (interp_cfg_model_non_intr ctx2 _ s2 Logic.eq_refl); reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
      | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_EOU {A1 A2}
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> Res A1 -> Res A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (s1, a1) (s2, a2)) :
    refine_prov RR U
      (interp_mcfg_model (EOU_to_itree m1) s1)
      (interp_mcfg_model (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret, Hret, Ha.
    - apply refine_mcfg_raise_both.
    - apply refine_mcfg_raiseOOM_l.
    - apply refine_mcfg_raiseUB_l.
  Qed.

  Lemma refine_cfg_EOU {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> Res A1 -> Res A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (s1, a1) (s2, a2)) :
    refine_prov RR U
      (interp_cfg_model ctx1 (EOU_to_itree m1) s1)
      (interp_cfg_model ctx2 (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret, Hret, Ha.
    - apply refine_cfg_raise_both.
    - apply refine_cfg_raiseOOM_l.
    - apply refine_cfg_raiseUB_l.
  Qed.

  (** Lift [memM_interp_prov] refinement to any [MemoryE] trigger in [CFGtop] or [MCFGtop]. *)
  Lemma refine_mcfg_memory_event {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RR U' ((σ1', rest1), x1) ((σ2', rest2), x2))
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov RR U
      (interp_mcfg_model (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_mcfg_model (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] [σ2' x2] HRR.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret, HRR.
  Qed.

  Lemma refine_cfg_memory_event {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> Res X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RR U' ((σ1', rest1), x1) ((σ2', rest2), x2))
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov RR U
      (interp_cfg_model ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_cfg_model ctx2 (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_non_intr; reflexivity
      | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] [σ2' x2] HRR.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret, HRR.
  Qed.

  (** One-sided left [MemoryE] step against an arbitrary right-hand model tree [t2]. *)
  Lemma refine_cfg_memory_event_l {X1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> R2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (U : list N) (σ1 : state)
    (rest1 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (t2 : itree ProvBotE R2) :
    refine_prov
      (fun U' '(σ1', x1) r2 => RR U' ((σ1', rest1), x1) r2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      t2 ->
    refine_prov RR U
      (interp_cfg_model ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      t2.
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_non_intr; reflexivity | symmetry; apply Eqit.bind_ret_r |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] r2 HRR.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    apply refine_prov_tau_l, refine_prov_tau_l, refine_prov_tau_l, refine_prov_ret, HRR.
  Qed.

  (** ** Exception-Reifying Interpreter ([interp_cfg_exc]) for [run_exc] *)

  Lemma run_exc_ret_eq {A} (a : A) :
    @run_exc (@ParamsV IP IPT) A (Ret a) ≅ Ret (inr a).
  Proof using.
    rewrite unfold_run_exc_obs; reflexivity.
  Qed.

  Lemma run_exc_tau_eq {A} (t : @CFGtop (@ParamsV IP IPT) A) :
    run_exc (Tau t) ≅ Tau (run_exc t).
  Proof using.
    rewrite unfold_run_exc_obs; reflexivity.
  Qed.

  Lemma run_exc_proper_eq {A} :
    forall (t1 t2 : @CFGtop (@ParamsV IP IPT) A),
      t1 ≅ t2 ->
      run_exc t1 ≅ run_exc t2.
  Proof using.
    ginit; gcofix CIH; intros t1 t2 Heq.
    rewrite (unfold_run_exc_obs t1), (unfold_run_exc_obs t2).
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X e k1 k2 Hk]; pclearbot.
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, Hm.
    - destruct (exc_of_event e) as [x |].
      + gstep; constructor; reflexivity.
      + gstep; constructor; intros y; gstep; constructor; gfinal; left; apply CIH, Hk.
  Qed.

  Lemma run_exc_bind_eq {A B} :
    forall (t : @CFGtop (@ParamsV IP IPT) A)
           (k : A -> @CFGtop (@ParamsV IP IPT) B),
      run_exc (ITree.bind t k) ≅
      ITree.bind (run_exc t)
        (fun res =>
           match res with
           | inl x => Ret (inl x)
           | inr a => run_exc (k a)
           end).
  Proof using.
    ginit; gcofix CIH; intros t k.
    rewrite (unfold_run_exc_obs t).
    destruct (observe t) as [a | m | X e h] eqn:Hot.
    - assert (Htk : ITree.bind t k ≅ k a).
      { rewrite (itree_eta t), Hot, Eqit.bind_ret_l; reflexivity. }
      rewrite (run_exc_proper_eq _ _ Htk), Eqit.bind_ret_l.
      gfinal; right; eapply paco2_mon; [reflexivity | intros ? ? []].
    - rewrite (unfold_run_exc_obs (ITree.bind t k)), observe_bind, Hot, Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
    - rewrite (unfold_run_exc_obs (ITree.bind t k)), observe_bind, Hot.
      destruct (exc_of_event e) as [x |].
      + rewrite Eqit.bind_ret_l; gstep; constructor; reflexivity.
      + rewrite Eqit.bind_vis; gstep; constructor; intros y.
        rewrite Eqit.bind_tau; gstep; constructor; gfinal; left; apply CIH.
  Qed.

  Lemma run_exc_raiseLLVM_eq {A} (x : @exc (@ParamsV IP IPT)) :
    @run_exc (@ParamsV IP IPT) A (raiseLLVM x) ≅ Ret (inl x).
  Proof using.
    unfold raiseLLVM, trigger_cast, ITree.trigger.
    rewrite unfold_run_exc_obs, observe_bind.
    cbn [observe exc_of_event subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    reflexivity.
  Qed.

  Lemma run_exc_trigger_non_exc {X}
    (e : @CFGEtop (@ParamsV IP IPT) X)
    (Hne : exc_of_event e = None) :
    run_exc (ITree.trigger e) ≅
    ITree.bind (ITree.trigger e) (fun y => Tau (Ret (inr y))).
  Proof using.
    unfold ITree.trigger.
    rewrite unfold_run_exc_obs; cbn [observe]; rewrite Hne, Eqit.bind_vis.
    apply eqit_Vis; intros y; rewrite run_exc_ret_eq; reflexivity.
  Qed.

  Definition interp_cfg_exc {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R)) :=
    interp_cfg_model ctx (run_exc t) s.

  Lemma interp_cfg_exc_obs_eq {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t1 t2 : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_cfg_exc ctx t1 s ≅ interp_cfg_exc ctx t2 s.
  Proof using.
    intros Heq; unfold interp_cfg_exc.
    apply interp_cfg_model_obs_eq, run_exc_proper_eq, Heq.
  Qed.

  Lemma interp_cfg_exc_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (a : R) (s : FusedS) :
    interp_cfg_exc ctx (Ret a) s ≅ Ret (s, inr a).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_ret_eq a)).
    apply interp_cfg_model_ret.
  Qed.

  Lemma interp_cfg_exc_tau {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_cfg_exc ctx (Tau t) s ≅ Tau (interp_cfg_exc ctx t s).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_tau_eq t)).
    apply interp_cfg_model_tau.
  Qed.

  Lemma interp_cfg_exc_raiseLLVM {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : @exc (@ParamsV IP IPT)) (s : FusedS) :
    @interp_cfg_exc R ctx (raiseLLVM x) s ≅ Ret (s, inl x).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_raiseLLVM_eq x)).
    apply interp_cfg_model_ret.
  Qed.

  Lemma interp_cfg_exc_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) A)
    (k : A -> @CFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    interp_cfg_exc ctx (ITree.bind t k) s ≅
    ITree.bind (interp_cfg_exc ctx t s)
      (fun '(s', res) =>
         match res with
         | inl x => Ret (s', inl x)
         | inr a => interp_cfg_exc ctx (k a) s'
         end).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_bind_eq t k)).
    rewrite interp_cfg_model_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' [x | a]] _ <-.
    - apply interp_cfg_model_ret.
    - reflexivity.
  Qed.

  Lemma interp_cfg_exc_trigger_non_exc {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (e : @CFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hne : exc_of_event e = None) :
    interp_cfg_exc ctx (ITree.trigger e) s ≅
    ITree.bind (interp_cfg_model ctx (ITree.trigger e) s)
      (fun '(s', y) => Tau (Ret (s', inr y))).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_trigger_non_exc e Hne)).
    rewrite interp_cfg_model_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' y] _ <-.
    rewrite interp_cfg_model_tau, interp_cfg_model_ret; reflexivity.
  Qed.

  Definition exc_post {A1 A2}
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N)
    (r1 : Res (@exc (@ParamsV IP IPT) + A1))
    (r2 : Res (@exc (@ParamsV IP IPT) + A2)) : Prop :=
    let '(s1, v1) := r1 in
    let '(s2, v2) := r2 in
    match v1, v2 with
    | inl x1, inl x2 => RExc U s1 s2 x1 x2
    | inr a1, inr a2 => RA U s1 s2 a1 a2
    | _, _ => False
    end.

  Lemma refine_cfg_exc_ret {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) (s1 s2 : FusedS) :
    RA U s1 s2 a1 a2 ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (Ret a1) s1)
      (interp_cfg_exc ctx2 (Ret a2) s2).
  Proof using.
    intros Hra.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_ret | symmetry; apply interp_cfg_exc_ret |].
    apply refine_prov_ret; exact Hra.
  Qed.

  Lemma refine_cfg_exc_bind {A1 A2 B1 B2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1)
      (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       refine_prov (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    refine_prov (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl (exc_post RExc RA) U U _ _ (incl_refl U) Ht).
    - intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] [Hincl Hres]; try contradiction.
      + apply refine_prov_ret; exact Hres.
      + eapply Hk; eassumption.
  Qed.

  Lemma refine_cfg_exc_trigger {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> X1 -> X2 -> Prop)
    (e1 : @CFGEtop (@ParamsV IP IPT) X1)
    (e2 : @CFGEtop (@ParamsV IP IPT) X2)
    (U : list N) (s1 s2 : FusedS)
    (Hne1 : exc_of_event e1 = None)
    (Hne2 : exc_of_event e2 = None) :
    refine_prov (fun U' '(s1', y1) '(s2', y2) => RA U' s1' s2' y1 y2) U
      (interp_cfg_model ctx1 (ITree.trigger e1) s1)
      (interp_cfg_model ctx2 (ITree.trigger e2) s2) ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (ITree.trigger e1) s1)
      (interp_cfg_exc ctx2 (ITree.trigger e2) s2).
  Proof using.
    intros Htr.
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_exc_trigger_non_exc ctx1 e1 s1 Hne1)
      | symmetry; apply (interp_cfg_exc_trigger_non_exc ctx2 e2 s2 Hne2) |].
    eapply refine_prov_bind; [exact Htr |].
    intros U' [s1' y1] [s2' y2] Hra.
    apply refine_prov_tau_both, refine_prov_ret; exact Hra.
  Qed.

  Lemma refine_cfg_exc_EOU {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RVal : A1 -> A2 -> Prop)
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RA U s1 s2 a1 a2) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (EOU_to_itree m1) s1)
      (interp_cfg_exc ctx2 (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - apply refine_cfg_exc_ret, Hret, Ha.
    - unfold raise, trigger_cast; eapply refine_cfg_exc_bind.
      + eapply refine_cfg_exc_trigger with (RA := fun _ _ _ (v1 : void) (_ : void) => match v1 with end);
          [reflexivity | reflexivity |].
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_trigger_prov, ITree.trigger.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + intros _ _ [] _ _ _ _.
    - unfold raiseOOM, trigger_cast, interp_cfg_exc.
      eapply refine_prov_obs_eq;
        [symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ s1 (run_exc_bind_eq _ _)),
                           (interp_cfg_model_obs_eq ctx1 _ _ s1
                              (eq_itree_clo_bind _ _ _ _ Logic.eq
                                 (run_exc_trigger_non_exc _ Logic.eq_refl)
                                 (fun _ _ _ => Logic.eq_refl))),
                           !Eqit.bind_bind, !interp_cfg_model_bind; reflexivity
        | reflexivity |].
      eapply refine_prov_obs_eq;
        [symmetry; rewrite (interp_cfg_model_non_intr ctx1 _ s1 Logic.eq_refl); reflexivity | reflexivity |].
      cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_trigger_prov, ITree.trigger.
      eapply refine_prov_obs_eq;
        [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - unfold raiseUB, trigger_cast, interp_cfg_exc.
      eapply refine_prov_obs_eq;
        [symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ s1 (run_exc_bind_eq _ _)),
                           (interp_cfg_model_obs_eq ctx1 _ _ s1
                              (eq_itree_clo_bind _ _ _ _ Logic.eq
                                 (run_exc_trigger_non_exc _ Logic.eq_refl)
                                 (fun _ _ _ => Logic.eq_refl))),
                           !Eqit.bind_bind, !interp_cfg_model_bind; reflexivity
        | reflexivity |].
      eapply refine_prov_obs_eq;
        [symmetry; rewrite (interp_cfg_model_non_intr ctx1 _ s1 Logic.eq_refl); reflexivity | reflexivity |].
      cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_trigger_prov, ITree.trigger.
      eapply refine_prov_obs_eq;
        [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_cfg_exc_raiseUB_l {A1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + A1) -> R2 -> Prop)
    (U : list N) (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_exc ctx1 (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, interp_cfg_exc.
    assert (Hub : run_exc (ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg))))
                             (fun v : void => match v with end))
                  ≅ ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg))))
                      (fun v : void => match v with end)).
    { rewrite run_exc_bind_eq, (run_exc_trigger_non_exc _ Logic.eq_refl), Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hub) | reflexivity |].
    apply (refine_cfg_raiseUB_l ctx1 RR U msg s1 t2).
  Qed.

  Lemma refine_cfg_exc_iter {I1 I2 R1 R2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RI   : list N -> FusedS -> FusedS -> I1 -> I2 -> Prop)
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RRet : list N -> FusedS -> FusedS -> R1 -> R2 -> Prop)
    (b1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1))
    (b2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2))
    (U0 : list N)
    (Hbody : forall U s1 s2 i1 i2,
               incl U0 U ->
               RI U s1 s2 i1 i2 ->
               refine_prov
                 (exc_post RExc
                    (fun U' s1' s2' lr1 lr2 =>
                       match lr1, lr2 with
                       | inl j1, inl j2 => RI U' s1' s2' j1 j2
                       | inr r1, inr r2 => RRet U' s1' s2' r1 r2
                       | _, _ => False
                       end))
                 U
                 (interp_cfg_exc ctx1 (b1 i1) s1)
                 (interp_cfg_exc ctx2 (b2 i2) s2)) :
    forall s1 s2 i1 i2,
      RI U0 s1 s2 i1 i2 ->
      refine_prov (exc_post RExc RRet) U0
        (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1)
        (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2).
  Proof using.
    set (RStep := fun U' (x1 : Res (@exc (@ParamsV IP IPT) + (I1 + R1)))
                         (x2 : Res (@exc (@ParamsV IP IPT) + (I2 + R2))) =>
                    incl U0 U' /\
                    exc_post RExc
                      (fun U'' s1' s2' lr1 lr2 =>
                         match lr1, lr2 with
                         | inl j1, inl j2 => RI U'' s1' s2' j1 j2
                         | inr r1, inr r2 => RRet U'' s1' s2' r1 r2
                         | _, _ => False
                         end) U' x1 x2).
    set (k1 := fun '(s', res) =>
                 match res with
                 | inl x => Ret (s', inl x)
                 | inr (inl j) => Tau (interp_cfg_exc ctx1 (ITree.iter b1 j) s')
                 | inr (inr r) => Ret (s', inr r)
                 end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1))).
    set (k2 := fun '(s', res) =>
                 match res with
                 | inl x => Ret (s', inl x)
                 | inr (inl j) => Tau (interp_cfg_exc ctx2 (ITree.iter b2 j) s')
                 | inr (inr r) => Ret (s', inr r)
                 end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R2))).
    assert (Hunf1 : forall s i,
              interp_cfg_exc ctx1 (ITree.iter b1 i) s ≅
              ITree.bind (interp_cfg_exc ctx1 (b1 i) s) k1).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx1 _ _ s (unfold_iter b1 i)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | r]]] _ <-; cbn [k1].
      - reflexivity.
      - apply interp_cfg_exc_tau.
      - apply interp_cfg_exc_ret. }
    assert (Hunf2 : forall s i,
              interp_cfg_exc ctx2 (ITree.iter b2 i) s ≅
              ITree.bind (interp_cfg_exc ctx2 (b2 i) s) k2).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ s (unfold_iter b2 i)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | r]]] _ <-; cbn [k2].
      - reflexivity.
      - apply interp_cfg_exc_tau.
      - apply interp_cfg_exc_ret. }
    set (r_it := fun U t1 t2 =>
                   exists u1 u2,
                     ITree.bind u1 k1 ≅ t1 /\
                     ITree.bind u2 k2 ≅ t2 /\
                     refine_prov RStep U u1 u2).
    assert (Hr_eq : forall U a1 a1' a2 a2',
                      a1 ≅ a1' -> a2 ≅ a2' -> r_it U a1 a2 -> r_it U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 (u1 & u2 & Eu1 & Eu2 & Hu).
      exists u1, u2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hu]]. }
    assert (Hcore : forall U t1 t2, r_it U t1 t2 -> refine_prov (exc_post RExc RRet) U t1 t2).
    { pcofix CIH.
      intros U t1 t2 (u1 & u2 & Eu1 & Eu2 & Hu); pstep.
      eapply refine_prov__mon with (r := r_it);
        [| intros U' a1 a2 Hr; right; apply CIH, Hr].
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Eu1 | exact Eu2 |].
      punfold Hu; clear t1 t2 Eu1 Eu2.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[s1' res1] | m1 | X1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[s2' res2] | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          destruct Hstep as [Hincl Hres].
          destruct res1 as [x1 | [j1 | r1]], res2 as [x2 | [j2 | r2]]; cbn in Hres; try contradiction.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn; exact Hres.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn.
            exists (interp_cfg_exc ctx1 (b1 j1) s1'), (interp_cfg_exc ctx2 (b2 j2) s2').
            split; [symmetry; apply Hunf1 |].
            split; [symmetry; apply Hunf2 |].
            apply refine_prov_incl; [exact Hincl | eapply Hbody; eassumption].
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn; exact Hres.
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2.
          exists m1, m2; repeat split; try reflexivity; exact Hstep.
        + apply RP_Step; unfold rp_step_body; rewrite (observe_bind u1 k1), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            exists (h1 p), u2; repeat split; try reflexivity; exact Hleft.
          * right; right; destruct (observe u2) as [? | ? | X2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 k2), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               exists (h1 p), (h2 p); repeat split; try reflexivity; exact Hboth.
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               exists (h1 a1), (h2 a2); repeat split; try reflexivity; exact HA.
      - eapply RP_TauL; [rewrite (observe_bind u1 k1), Hu1; reflexivity | exact IH].
      - eapply RP_TauR; [rewrite (observe_bind u2 k2), Hu2; reflexivity | exact IH]. }
    intros s1 s2 i1 i2 Hinit; apply Hcore.
    exists (interp_cfg_exc ctx1 (b1 i1) s1), (interp_cfg_exc ctx2 (b2 i2) s2).
    split; [symmetry; apply Hunf1 |].
    split; [symmetry; apply Hunf2 |].
    apply refine_prov_incl; [apply incl_refl | apply Hbody; [apply incl_refl | exact Hinit]].
  Qed.

End ModelCombinators.


(** * 3. Memory Model, Byte Serialization & Ghost-Slot Simulation *)

Section MemoryAndSerialization.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.

  (** ** 3A. [memM_interp_prov] Monadic Laws & [mem_stack_equal] Synchronization *)

  Lemma memM_interp_prov_ret {A} (x : A) (σ : state) :
    memM_interp_prov (Monads.ret x) σ = Ret (σ, x).
  Proof using.
    reflexivity.
  Qed.

  Lemma memM_interp_prov_bind {A B}
    (m : @memM (@ParamsV IP IPT) _ A)
    (k : A -> @memM (@ParamsV IP IPT) _ B)
    (σ : state) :
    memM_interp_prov (Monads.bind m k) σ ≅
    ITree.bind (memM_interp_prov m σ) (fun '(σ', x) => memM_interp_prov (k x) σ').
  Proof using.
    revert σ; induction m as [x | s | s | s | g IH | σ' g IH | c g IH]; intros σ;
      cbn [Monads.bind memS_mon memS_bind memM_interp_prov].
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
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros p _ <-; apply IH.
      + apply IH.
  Qed.

  Lemma memM_interp_prov_map_monad_acc {A B}
    (f : A -> @memM (@ParamsV IP IPT) _ B) (l : list A) (σ : state) :
    memM_interp_prov (map_monad_acc f l) σ ≅
    memM_interp_prov (map_monad f l) σ.
  Proof using.
    unfold map_monad_acc.
    set (go := fix loop (acc : list B) (xs : list A) : @memM (@ParamsV IP IPT) _ (list B) :=
                 match xs with
                 | [] => Monads.ret (rev_append acc [])
                 | a :: xs' => Monads.bind (f a) (fun b => loop (b :: acc) xs')
                 end).
    change (memM_interp_prov (go [] l) σ ≅ memM_interp_prov (map_monad f l) σ).
    assert (Hgo : forall xs acc σ0,
              memM_interp_prov (go acc xs) σ0 ≅
              memM_interp_prov (Monads.bind (map_monad f xs) (fun bs => Monads.ret (rev_append acc bs))) σ0).
    { induction xs as [| a xs' IH]; intros acc σ0; cbn [go map_monad].
      - rewrite memM_interp_prov_bind, memM_interp_prov_ret, Eqit.bind_ret_l; reflexivity.
      - rewrite !memM_interp_prov_bind, !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [σ1 b] _ <-.
        rewrite IH, !memM_interp_prov_bind, !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [σ2 bs] _ <-.
        rewrite !memM_interp_prov_ret, !Eqit.bind_ret_l, !memM_interp_prov_ret.
        cbn [rev_append]; reflexivity. }
    rewrite Hgo, memM_interp_prov_bind; cbn [rev_append].
    rewrite <- (Eqit.bind_ret_r (memM_interp_prov (map_monad f l) σ)) at 2.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [σ' bs] _ <-; reflexivity.
  Qed.

  Lemma memM_interp_prov_raiseUB_l {A R2}
    (RR : list N -> (state * A) -> R2 -> Prop)
    (U : list N) (msg : string) (σ1 : state) (t2 : itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Mub state (@ptr ProvenanceV (@PointerV IP)) provenance A msg) σ1)
      t2.
  Proof using.
    cbn [memM_interp_prov]; unfold raiseUB, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_vis | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_raiseOOM_l {A R2}
    (RR : list N -> (state * A) -> R2 -> Prop)
    (U : list N) (msg : string) (σ1 : state) (t2 : itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Moom state (@ptr ProvenanceV (@PointerV IP)) provenance A msg) σ1)
      t2.
  Proof using.
    cbn [memM_interp_prov]; unfold raiseOOM, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_vis | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_raise_both {A1 A2}
    (RR : list N -> (state * A1) -> (state * A2) -> Prop)
    (U : list N) (msg1 msg2 : string) (σ1 σ2 : state) :
    refine_prov RR U
      (memM_interp_prov (@Merr state (@ptr ProvenanceV (@PointerV IP)) provenance A1 msg1) σ1)
      (memM_interp_prov (@Merr state (@ptr ProvenanceV (@PointerV IP)) provenance A2 msg2) σ2).
  Proof using.
    cbn [memM_interp_prov]; unfold raise, trigger_cast, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_EOU_refl {A} (e : EOU A) :
    refine_EOU Logic.eq e e.
  Proof using.
    destruct e; constructor; reflexivity.
  Qed.

  Lemma memM_interp_prov_lift_EOU {A1 A2}
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> (state * A1) -> (state * A2) -> Prop)
    (U : list N) (e1 : EOU A1) (e2 : EOU A2) (σ1 σ2 : state)
    (He : refine_EOU RVal e1 e2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (σ1, a1) (σ2, a2)) :
    refine_prov RR U
      (memM_interp_prov (Interfaces.Memory.lift e1) σ1)
      (memM_interp_prov (Interfaces.Memory.lift e2) σ2).
  Proof using.
    destruct He as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 e2'];
      cbn [Interfaces.Memory.lift].
    - cbn [memM_interp_prov]; apply refine_prov_ret, Hret, Ha.
    - apply memM_interp_prov_raise_both.
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
  Qed.

  Lemma lookup_delete_eq {A} (k : Z) (m : IntMap A) :
    IntMaps.lookup k (IntMaps.delete k m) = None.
  Proof using.
    unfold IntMaps.lookup, IntMaps.delete.
    apply IntMaps.IP.F.remove_eq_o; reflexivity.
  Qed.

  Lemma lookup_delete_neq {A} (z k : Z) (m : IntMap A) :
    z <> k ->
    IntMaps.lookup z (IntMaps.delete k m) = IntMaps.lookup z m.
  Proof using.
    intros Hne; unfold IntMaps.lookup, IntMaps.delete.
    apply IntMaps.IP.F.remove_neq_o; lia.
  Qed.

  Lemma Equal_add {A} (k : Z) (v : A) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add k v m1) (IntMaps.add k v m2).
  Proof using.
    intros Heq z.
    destruct (Z.eq_dec z k) as [-> | Hne].
    - rewrite !IntMaps.lookup_add_eq; reflexivity.
    - rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Heq.
  Qed.

  Lemma Equal_delete {A} (k : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.delete k m1) (IntMaps.delete k m2).
  Proof using.
    intros Heq z.
    destruct (Z.eq_dec z k) as [-> | Hne].
    - rewrite !lookup_delete_eq; reflexivity.
    - rewrite !lookup_delete_neq by exact Hne; apply Heq.
  Qed.

  Lemma Equal_member_iff {A} (m1 m2 : IntMap A) (k : Z) :
    IntMaps.Equal m1 m2 ->
    (IntMaps.member k m1 <-> IntMaps.member k m2).
  Proof using.
    intros Heq; split; intros Hm.
    - apply IntMaps.member_lookup in Hm as [v Hv].
      rewrite Heq in Hv; eapply IntMaps.lookup_member; exact Hv.
    - apply IntMaps.member_lookup in Hm as [v Hv].
      rewrite <- Heq in Hv; eapply IntMaps.lookup_member; exact Hv.
  Qed.

  Lemma Equal_IM_greatest_key {A} (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IM_greatest_key m1 = IM_greatest_key m2.
  Proof using.
    intros Heq; apply IM_greatest_key_morph.
    intros k; apply Equal_member_iff, Heq.
  Qed.

  Lemma Equal_next_key_with_alignment {A} (m1 m2 : IntMap A) (align : N) :
    IntMaps.Equal m1 m2 ->
    next_key_with_alignment m1 align = next_key_with_alignment m2 align.
  Proof using.
    intros Heq; unfold next_key_with_alignment.
    rewrite (Equal_IM_greatest_key m1 m2 Heq); reflexivity.
  Qed.

  Lemma Equal_add_all_index {A} (vs : list A) (base : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add_all_index vs base m1) (IntMaps.add_all_index vs base m2).
  Proof using.
    revert base m1 m2; induction vs as [| v vs' IH]; intros base m1 m2 Heq;
      cbn [IntMaps.add_all_index]; [exact Heq |].
    apply Equal_add, IH, Heq.
  Qed.

  Lemma Equal_add_all_index_acc {A} (vs : list A) (base : Z) (m1 m2 : IntMap A) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (IntMaps.add_all_index_acc vs base m1) (IntMaps.add_all_index_acc vs base m2).
  Proof using.
    intros Heq z.
    pose proof (IntMaps.add_all_index_acc_eq vs base m1 z) as H1.
    pose proof (IntMaps.add_all_index_acc_eq vs base m2 z) as H2.
    rewrite H1, H2; apply Equal_add_all_index, Heq.
  Qed.

  Lemma Equal_free_frame_memory
    (f : @Frame (@ParamsV IP IPT))
    (m1 m2 : @memory (@ParamsV IP IPT)) :
    IntMaps.Equal m1 m2 ->
    IntMaps.Equal (free_frame_memory f m1) (free_frame_memory f m2).
  Proof using.
    revert m1 m2; induction f as [| k f' IH]; intros m1 m2 Heq;
      cbn [free_frame_memory fold_left]; [exact Heq |].
    apply IH; unfold free_byte; apply Equal_delete, Heq.
  Qed.

  Definition mem_stack_equal (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    IntMaps.Equal (Memory_stack_memory ms1) (Memory_stack_memory ms2) /\
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 /\
    Memory_stack_heap ms1 = Memory_stack_heap ms2.

  Lemma mem_stack_equal_refl (ms : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms ms.
  Proof using.
    repeat split; reflexivity.
  Qed.

  Lemma mem_stack_equal_sym (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal ms2 ms1.
  Proof using.
    intros (Hm & Hfs & Hh); repeat split; symmetry; assumption.
  Qed.

  Lemma mem_stack_equal_trans (ms1 ms2 ms3 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal ms2 ms3 ->
    mem_stack_equal ms1 ms3.
  Proof using.
    intros (Hm12 & Hfs12 & Hh12) (Hm23 & Hfs23 & Hh23).
    repeat split; etransitivity; eassumption.
  Qed.

  Definition eq_sync_post {R : Type} (U0 : list N)
    (U' : list N) (sr1 sr2 : state * R) : Prop :=
    let '(σ1', r1) := sr1 in
    let '(σ2', r2) := sr2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
    r1 = r2.

  Lemma Read_byte_equal_sync (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Read_byte p) σ1)
      (memM_interp_prov (Read_byte p) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2))).
    rewrite (Hmem (ptr_to_int p)).
    destruct (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      as [[b aid] |].
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      destruct (access_allowed (ptr_provenance p) aid).
      + apply refine_prov_ret; repeat split; [apply incl_refl | exact Hmem | exact Hfs | exact Hh | reflexivity].
      + apply memM_interp_prov_raiseUB_l.
    - cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma Write_byte_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Write_byte p mb) σ1)
      (memM_interp_prov (Write_byte p mb) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2))).
    rewrite (Hmem (ptr_to_int p)).
    destruct (IntMaps.lookup (ptr_to_int p) (Memory_stack_memory (state_memory_stack σ2)))
      as [[b0 aid] |].
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      destruct (access_allowed (ptr_provenance p) aid).
      + unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
          cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
        apply refine_prov_ret; repeat split; cbn;
          [apply incl_refl
          | apply Equal_add, Hmem
          | exact Hfs
          | exact Hh
          | reflexivity].
      + apply memM_interp_prov_raiseUB_l.
    - cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma map_monad_Read_byte_equal_sync
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction ptrs as [| p ptrs' IH]; intros U σ1 σ2 Heq;
      cbn [map_monad].
    - apply refine_prov_ret; repeat split; [apply incl_refl | apply Heq | apply Heq | apply Heq | reflexivity].
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply Read_byte_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply IH, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      apply refine_prov_ret; split; [eapply incl_tran; eassumption | split; [exact Heq2 | reflexivity]].
  Qed.

  Lemma read_bytes_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (sz : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (read_bytes p sz) σ1)
      (memM_interp_prov (read_bytes p sz) σ2).
  Proof using.
    unfold read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros ptrs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' ptrs1] [σ2' ptrs2] (Hinc1 & Heq1 & <-).
      cbn [read_byte MemoryModelPrimitivesV].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_map_monad_acc
        | symmetry; apply memM_interp_prov_map_monad_acc |].
      eapply refine_prov_weaken; [apply map_monad_Read_byte_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma loop_Write_byte_equal_sync
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction pbs as [| [pt mb] pbs' IH]; intros U σ1 σ2 Heq;
      cbn [loop_monad].
    - apply refine_prov_ret; repeat split; [apply incl_refl | apply Heq | apply Heq | apply Heq | reflexivity].
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply Write_byte_equal_sync, Heq |].
      intros U1 [σ1' []] [σ2' []] (Hinc1 & Heq1 & _).
      eapply refine_prov_weaken; [apply IH, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma write_bytes_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (bs : list (@memory_byte (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (write_bytes p bs) σ1)
      (memM_interp_prov (write_bytes p bs) σ2).
  Proof using.
    unfold write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros ptrs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' ptrs1] [σ2' ptrs2] (Hinc1 & Heq1 & <-).
      cbn [write_byte MemoryModelPrimitivesV].
      eapply refine_prov_weaken; [apply loop_Write_byte_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma read_dvalue_equal_sync (dt : dtyp) (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (read_dvalue dt p) σ1)
      (memM_interp_prov (read_dvalue dt p) σ2).
  Proof using.
    unfold read_dvalue.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq |].
    intros U1 [σ1' bs1] [σ2' bs2] (Hinc1 & Heq1 & <-).
    eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
    intros dv _ <-; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
  Qed.

  Lemma write_dvalue_equal_sync
    (p : @ptr ProvenanceV (@PointerV IP)) (dt : dtyp) (v : @dvalue (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (write_dvalue p dt v) σ1)
      (memM_interp_prov (write_dvalue p dt v) σ2).
  Proof using.
    unfold write_dvalue.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros bs _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' bs1] [σ2' bs2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq1 |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)].
  Qed.

  Lemma get_free_block_equal_sync (sz align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (get_free_block sz align pr) σ1)
      (memM_interp_prov (get_free_block sz align pr) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold get_free_block, next_key, Mnext_key;
      cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    rewrite (Equal_next_key_with_alignment _ _ align Hmem).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) align).
    destruct (int_to_ptr addr (allocation_id_to_prov (provenance_to_allocation_id pr)))
      as [s | s | s | pt];
      cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret].
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
    - apply memM_interp_prov_raise_both.
    - destruct (get_consecutive_ptrs pt sz) as [s | s | s | ptrs];
        cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret].
      + apply memM_interp_prov_raiseOOM_l.
      + apply memM_interp_prov_raiseUB_l.
      + apply memM_interp_prov_raise_both.
      + apply refine_prov_ret; exact (conj (incl_refl U) (conj (conj Hmem (conj Hfs Hh)) Logic.eq_refl)).
  Qed.

  Lemma add_all_to_frame_equal
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal (add_all_to_frame ks ms1) (add_all_to_frame ks ms2).
  Proof using.
    revert ms1 ms2; induction ks as [| k ks' IH]; intros [m1 s1 h1] [m2 s2 h2] (Hm & Hfs & Hh);
      cbn [add_all_to_frame fold_left Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap] in *.
    - exact (conj Hm (conj Hfs Hh)).
    - subst s2 h2; destruct s1; apply IH; repeat split; try exact Hm; reflexivity.
  Qed.

  Lemma add_all_to_heap_equal
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    mem_stack_equal ms1 ms2 ->
    mem_stack_equal (add_all_to_heap ks ms1) (add_all_to_heap ks ms2).
  Proof using.
    destruct ks as [| root ks']; [intros H; exact H |].
    unfold add_all_to_heap; set (all_ks := root :: ks'); clearbody all_ks.
    revert ms1 ms2; induction all_ks as [| k rest IH]; intros [m1 s1 h1] [m2 s2 h2] (Hm & Hfs & Hh);
      cbn [add_all_to_heap' fold_left add_to_heap Memory_stack_memory Memory_stack_frame_stack Memory_stack_heap] in *.
    - exact (conj Hm (conj Hfs Hh)).
    - subst s2 h2; apply IH; repeat split; [exact Hm | reflexivity | reflexivity].
  Qed.

  Lemma Allocate_bytes_with_pr_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Allocate_bytes_with_pr bs align pr) σ1)
      (memM_interp_prov (Allocate_bytes_with_pr bs align pr) σ2).
  Proof using.
    unfold Allocate_bytes_with_pr.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply get_free_block_equal_sync, Heq |].
    intros U1 [σ1' [pt1 ptrs1]] [σ2' [pt2 ptrs2]] (Hinc1 & Heq1 & Hpair).
    inversion Hpair; subst pt2 ptrs2; clear Hpair.
    unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    destruct Heq1 as (Hm1 & Hfs1 & Hh1).
    apply refine_prov_ret; split; [exact Hinc1 | split; [| reflexivity]].
    apply add_all_to_frame_equal; repeat split; cbn;
      [apply Equal_add_all_index_acc, Hm1 | exact Hfs1 | exact Hh1].
  Qed.

  Lemma Malloc_bytes_with_pr_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N) (pr : provenance)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Malloc_bytes_with_pr bs align pr) σ1)
      (memM_interp_prov (Malloc_bytes_with_pr bs align pr) σ2).
  Proof using.
    unfold Malloc_bytes_with_pr.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind; [apply get_free_block_equal_sync, Heq |].
    intros U1 [σ1' [pt1 ptrs1]] [σ2' [pt2 ptrs2]] (Hinc1 & Heq1 & Hpair).
    inversion Hpair; subst pt2 ptrs2; clear Hpair.
    unfold add_block_to_heap, add_block, add_ptrs_to_heap, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    destruct Heq1 as (Hm1 & Hfs1 & Hh1).
    apply refine_prov_ret; split; [exact Hinc1 | split; [| reflexivity]].
    apply add_all_to_heap_equal; repeat split; cbn;
      [apply Equal_add_all_index_acc, Hm1 | exact Hfs1 | exact Hh1].
  Qed.

  Lemma refine_prov_trigger_fresh_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (k2 : N -> itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) (k2 p)) ->
    refine_prov RR U
      (ITree.bind (ITree.trigger FreshProv) k1)
      (ITree.bind (ITree.trigger FreshProv) k2).
  Proof using.
    intros Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply bind_trigger | symmetry; apply bind_trigger |].
    apply refine_prov_fresh_both, Hk.
  Qed.

  Lemma refine_prov_trigger_fresh_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) t2) ->
    refine_prov RR U (ITree.bind (ITree.trigger FreshProv) k1) t2.
  Proof using.
    intros Hk.
    eapply refine_prov_obs_eq; [symmetry; apply bind_trigger | reflexivity |].
    apply refine_prov_fresh_l, Hk.
  Qed.

  Lemma allocate_bytes_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (allocate_bytes bs align) σ1)
      (memM_interp_prov (allocate_bytes bs align) σ2).
  Proof using.
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply refine_prov_trigger_fresh_both; intros p Hp.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    eapply refine_prov_weaken; [apply Allocate_bytes_with_pr_equal_sync; cbn; exact Heq |].
    intros U' [s1 r1] [s2 r2] (Hinc & Heq' & Hr).
    split; [intros z Hz; apply Hinc; right; exact Hz | exact (conj Heq' Hr)].
  Qed.

  Lemma malloc_bytes_equal_sync
    (bs : list (@memory_byte (@ParamsV IP IPT))) (align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (malloc_bytes bs align) σ1)
      (memM_interp_prov (malloc_bytes bs align) σ2).
  Proof using.
    unfold malloc_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.ret memS_mon memM_interp_prov malloc_bytes_with_pr MemoryModelPrimitivesV].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply refine_prov_trigger_fresh_both; intros p Hp.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    eapply refine_prov_weaken; [apply Malloc_bytes_with_pr_equal_sync; cbn; exact Heq |].
    intros U' [s1 r1] [s2 r2] (Hinc & Heq' & Hr).
    split; [intros z Hz; apply Hinc; right; exact Hz | exact (conj Heq' Hr)].
  Qed.

  Lemma allocate_dtyp_equal_sync (dt : dtyp) (num align : N)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (allocate_dtyp dt num align) σ1)
      (memM_interp_prov (allocate_dtyp dt num align) σ2).
  Proof using.
    unfold allocate_dtyp.
    destruct (dtyp_eqb dt DTYPE_Void).
    - apply memM_interp_prov_raiseUB_l.
    - apply allocate_bytes_equal_sync, Heq.
  Qed.

  Lemma Mempush_equal_sync (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov Mempush σ1)
      (memM_interp_prov Mempush σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Mempush, app_frame_stack, get, put;
      cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn;
      [apply incl_refl | exact Hmem | unfold push_frame_stack; congruence | exact Hh | reflexivity].
  Qed.

  Lemma Mempop_equal_sync (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov Mempop σ1)
      (memM_interp_prov Mempop σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs.
    destruct (Memory_stack_frame_stack (state_memory_stack σ2)) as [f | s f].
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      cbn [pop_frame_stack Interfaces.Memory.lift Monads.bind memS_mon memS_bind].
      apply memM_interp_prov_raise_both.
    - eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      cbn [pop_frame_stack Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
      apply refine_prov_ret; repeat split; cbn;
        [apply incl_refl | apply Equal_free_frame_memory, Hmem | reflexivity | exact Hh | reflexivity].
  Qed.

  Lemma Free_equal_sync (p : @ptr ProvenanceV (@PointerV IP))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (Free p) σ1)
      (memM_interp_prov (Free p) σ2).
  Proof using.
    destruct Heq as (Hmem & Hfs & Hh).
    unfold Free, get_heap, app_mem, upd_heap, app_heap, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hh.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    destruct (IntMaps.lookup (ptr_to_int p) (Memory_stack_heap (state_memory_stack σ2))) as [blk |].
    - cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
      apply refine_prov_ret; repeat split; cbn;
        [apply incl_refl | apply Equal_free_frame_memory, Hmem | exact Hfs | reflexivity | reflexivity].
    - apply memM_interp_prov_raiseUB_l.
  Qed.

  Lemma convert_impure_base_equal_sync
    (ct : impure_conversion) (t1 : dtyp_base) (dv : @dvalue_base (@ParamsV IP IPT)) (t2 : dtyp_base)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ1)
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ2).
  Proof using.
    unfold convert_impure_base, assert_inttoptr_types_ok.
    destruct ct.
    - destruct t1; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        cbn [Monads.bind memS_mon memS_bind Monads.ret];
        (destruct dv;
         eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        (eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        (eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl))).
    - apply memM_interp_prov_raise_both.
  Qed.

  Lemma map_monad_convert_impure_base_equal_sync
    (ct : impure_conversion) (t1 t2 : dtyp_base) (elts : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ1)
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ2).
  Proof using.
    revert U σ1 σ2 Heq; induction elts as [| v vs IH]; intros U σ1 σ2 Heq; cbn [map_monad].
    - apply refine_prov_ret; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply IH, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      apply refine_prov_ret; split; [eapply incl_tran; eassumption | exact (conj Heq2 Logic.eq_refl)].
  Qed.

  Lemma convert_impure_equal_sync
    (ct : impure_conversion) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ1)
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ2).
  Proof using.
    unfold convert_impure.
    destruct dv as [db | | vec elts].
    - destruct (get_base_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      unfold Functor.fmap, Functor_Monad.
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_equal_sync, Heq |].
      intros U1 [σ1' b1] [σ2' b2] (Hinc1 & Heq1 & <-).
      apply refine_prov_ret; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
    - apply memM_interp_prov_raise_both.
    - destruct vec; [| apply memM_interp_prov_raise_both].
      destruct (get_vector_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind.
      + eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
        intros elts' _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
      + intros U1 [σ1' elts1'] [σ2' elts2'] (Hinc1 & Heq1 & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply map_monad_convert_impure_base_equal_sync, Heq1 |].
        intros U2 [σ1'' vs1] [σ2'' vs2] (Hinc2 & Heq2 & <-).
        apply refine_prov_ret; split; [eapply incl_tran; eassumption | exact (conj Heq2 Logic.eq_refl)].
  Qed.

  Lemma handle_memoryM_equal_sync {X} (me : @MemoryE (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_memoryM me) σ1)
      (memM_interp_prov (handle_memoryM me) σ2).
  Proof using.
    destruct me as [| | dt num al | dt a | dt a v | ct t1 v t2];
      cbn [handle_memoryM mempush mempop MemoryModelPrimitivesV].
    - apply Mempush_equal_sync, Heq.
    - apply Mempop_equal_sync, Heq.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply allocate_dtyp_equal_sync, Heq |].
      intros U1 [σ1' pt1] [σ2' pt2] (Hinc1 & Heq1 & <-).
      apply refine_prov_ret; exact (conj Hinc1 (conj Heq1 Logic.eq_refl)).
    - destruct a as [[pt | | | | | | |] | |];
        try apply memM_interp_prov_raiseUB_l.
      apply read_dvalue_equal_sync, Heq.
    - destruct a as [[pt | | | | | | |] | |];
        try apply memM_interp_prov_raiseUB_l.
      apply write_dvalue_equal_sync, Heq.
    - apply convert_impure_equal_sync, Heq.
  Qed.

  Lemma handle_memtransfer_equal_sync (ov : bool) (args : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_memtransfer ov args) σ1)
      (memM_interp_prov (handle_memtransfer ov args) σ2).
  Proof using.
    unfold handle_memtransfer.
    destruct args as [| dst [| src [| len [| vlt [| ? ?]]]]];
      try apply memM_interp_prov_raise_both.
    destruct vlt; try apply memM_interp_prov_raise_both.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    assert (Hlen : refine_prov (eq_sync_post U) U
                     (memM_interp_prov
                        (match len with
                         | DVALUE_I _ sz => Monads.ret (Z.to_N (unsigned sz))
                         | DVALUE_Iptr sz => Monads.ret (Z.to_N (to_Z sz))
                         | DVALUE_Poison => mub ((if ov then "memmove" else "memcpy") ++ " with poison length.")%string
                         | _ => merr ("Unsupported arguments to " ++ (if ov then "memmove" else "memcpy") ++ ".")%string
                         end) σ1)
                     (memM_interp_prov
                        (match len with
                         | DVALUE_I _ sz => Monads.ret (Z.to_N (unsigned sz))
                         | DVALUE_Iptr sz => Monads.ret (Z.to_N (to_Z sz))
                         | DVALUE_Poison => mub ((if ov then "memmove" else "memcpy") ++ " with poison length.")%string
                         | _ => merr ("Unsupported arguments to " ++ (if ov then "memmove" else "memcpy") ++ ".")%string
                         end) σ2)).
    { destruct len;
        try apply memM_interp_prov_raise_both;
        try apply memM_interp_prov_raiseUB_l;
        apply refine_prov_ret; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)). }
    eapply refine_prov_bind; [exact Hlen |].
    intros U1 [σ1' sz1] [σ2' sz2] (Hinc1 & Heq1 & <-).
    assert (Hbody : forall (m : @memM (@ParamsV IP IPT) _ unit),
              refine_prov (eq_sync_post U1) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2') ->
              refine_prov (eq_sync_post U) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2')).
    { intros m Hm; eapply refine_prov_weaken; [exact Hm |].
      intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)]. }
    apply Hbody.
    destruct dst, src;
      try apply memM_interp_prov_raise_both;
      try (destruct (sz1 =? 0)%N;
           [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
           | apply memM_interp_prov_raiseUB_l]).
    destruct ov; unfold memmove, memcpy.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq2 |].
      intros U3 [s1 r1] [s2 r2] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
    - destruct (orb (no_overlap p sz1 p0 sz1) (Z.eqb (ptr_to_int p0) (ptr_to_int p)));
        [| apply memM_interp_prov_raiseUB_l].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply read_bytes_equal_sync, Heq1 |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (Hinc2 & Heq2 & <-).
      eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq2 |].
      intros U3 [s1 r1] [s2 r2] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
  Qed.

  Lemma handle_intrinsicM_equal_sync {X} (ie : @IntrinsicE (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (eq_sync_post U) U
      (memM_interp_prov (handle_intrinsicM ie) σ1)
      (memM_interp_prov (handle_intrinsicM ie) σ2).
  Proof using.
    destruct ie as [dt name args va]; unfold handle_intrinsicM.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    eapply refine_prov_bind.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros args' _ <-; exact (conj (incl_refl U) (conj Heq Logic.eq_refl)).
    - intros U1 [σ1' args1'] [σ2' args2'] (Hinc1 & Heq1 & <-).
      assert (Hwk : forall R (m : @memM (@ParamsV IP IPT) _ R),
                refine_prov (eq_sync_post U1) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2') ->
                refine_prov (eq_sync_post U) U1 (memM_interp_prov m σ1') (memM_interp_prov m σ2')).
      { intros R m Hm; eapply refine_prov_weaken; [exact Hm |].
        intros U2 [s1 r1] [s2 r2] (Hinc2 & Heq2 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq2 Hr)]. }
      apply Hwk.
      destruct (is_memcpy_name name).
      + eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply handle_memtransfer_equal_sync, Heq1 |].
        intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
      + destruct (is_memmove_name name).
        * eapply refine_prov_obs_eq;
            [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
          eapply refine_prov_bind; [apply handle_memtransfer_equal_sync, Heq1 |].
          intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
        * destruct (is_memset_name name).
          -- eapply refine_prov_obs_eq;
               [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
             eapply refine_prov_bind.
             ++ unfold handle_memset.
                destruct args1' as [| dst [| val [| len [| vlt [| ? ?]]]]];
                  try apply memM_interp_prov_raise_both.
                destruct vlt; try apply memM_interp_prov_raise_both.
                eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                assert (Hval : refine_prov (eq_sync_post U1) U1
                                 (memM_interp_prov
                                    (match val with
                                     | DVALUE_I sz v => if Pos.eqb sz 8 then Monads.ret (BYTE_I (repr (unsigned v) : int8)) else merr "Unsupported arguments to memset."%string
                                     | DVALUE_Poison => Monads.ret poison_memory_byte
                                     | _ => merr "Unsupported arguments to memset."%string
                                     end) σ1')
                                 (memM_interp_prov
                                    (match val with
                                     | DVALUE_I sz v => if Pos.eqb sz 8 then Monads.ret (BYTE_I (repr (unsigned v) : int8)) else merr "Unsupported arguments to memset."%string
                                     | DVALUE_Poison => Monads.ret poison_memory_byte
                                     | _ => merr "Unsupported arguments to memset."%string
                                     end) σ2')).
                { destruct val; try apply memM_interp_prov_raise_both.
                  - destruct (Pos.eqb sz 8);
                      [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
                      | apply memM_interp_prov_raise_both].
                  - apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl)). }
                eapply refine_prov_bind; [exact Hval |].
                intros U2 [s1 mb1] [s2 mb2] (Hinc2 & Heq2 & <-).
                eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                assert (Hsz : refine_prov (eq_sync_post U2) U2
                                (memM_interp_prov
                                   (match len with
                                    | DVALUE_I _ l => Monads.ret (Z.to_N (unsigned l))
                                    | DVALUE_Poison => mub "memset with poison length."%string
                                    | _ => merr "Unsupported arguments to memset."%string
                                    end) s1)
                                (memM_interp_prov
                                   (match len with
                                    | DVALUE_I _ l => Monads.ret (Z.to_N (unsigned l))
                                    | DVALUE_Poison => mub "memset with poison length."%string
                                    | _ => merr "Unsupported arguments to memset."%string
                                    end) s2)).
                { destruct len;
                    try apply memM_interp_prov_raise_both;
                    try apply memM_interp_prov_raiseUB_l;
                    apply refine_prov_ret; exact (conj (incl_refl U2) (conj Heq2 Logic.eq_refl)). }
                eapply refine_prov_bind.
                ** eapply refine_prov_weaken; [exact Hsz |].
                   intros U3 [sa ra] [sb rb] (Hinc3 & Heq3 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq3 Hr)].
                ** intros U3 [sa sz1] [sb sz2] (Hinc3 & Heq3 & <-).
                   destruct dst;
                     try apply memM_interp_prov_raise_both.
                   --- unfold memset; eapply refine_prov_weaken; [apply write_bytes_equal_sync, Heq3 |].
                       intros U4 [x1 y1] [x2 y2] (Hinc4 & Heq4 & Hr); split; [eapply incl_tran; eassumption | exact (conj Heq4 Hr)].
                   --- destruct (sz1 =? 0)%N;
                         [apply refine_prov_ret; exact (conj Hinc3 (conj Heq3 Logic.eq_refl))
                         | apply memM_interp_prov_raiseUB_l].
             ++ intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _); apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
          -- destruct (Rocqlib.proj_sumbool (string_dec name "malloc"%string)).
             ++ eapply refine_prov_obs_eq;
                  [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                eapply refine_prov_bind.
                ** unfold handle_malloc.
                   destruct args1' as [| a0 [| ? ?]]; try apply memM_interp_prov_raise_both.
                   destruct a0; try apply memM_interp_prov_raise_both;
                     apply malloc_bytes_equal_sync, Heq1.
                ** intros U2 [s1 pt1] [s2 pt2] (Hinc2 & Heq2 & <-).
                   apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
             ++ destruct (Rocqlib.proj_sumbool (string_dec name "free"%string)).
                ** eapply refine_prov_obs_eq;
                     [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
                   eapply refine_prov_bind.
                   --- unfold handle_free.
                       destruct args1' as [| a0 [| ? ?]]; try apply memM_interp_prov_raise_both.
                       destruct a0; try apply memM_interp_prov_raise_both.
                       +++ destruct (ptr_to_int p =? ptr_to_int null)%Z;
                             [apply refine_prov_ret; exact (conj (incl_refl U1) (conj Heq1 Logic.eq_refl))
                             | apply Free_equal_sync, Heq1].
                       +++ apply memM_interp_prov_raiseUB_l.
                   --- intros U2 [s1 []] [s2 []] (Hinc2 & Heq2 & _).
                       apply refine_prov_ret; exact (conj Hinc2 (conj Heq2 Logic.eq_refl)).
                ** apply memM_interp_prov_raise_both.
  Qed.

  (** ** 3B. Scalar Types & Byte Serialization Identities *)

  Lemma is_scalar_dtyp_inv (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    exists dtb,
      dt = DTYPE_Base dtb /\
      ((exists sz, dtb = DTYPE_I sz) \/
       dtb = DTYPE_Pointer \/
       dtb = DTYPE_FP FP_float \/
       dtb = DTYPE_FP FP_double).
  Proof using.
    intros Hsc; destruct dt as [dtb | |]; try discriminate Hsc.
    exists dtb; split; [reflexivity |].
    cbn [is_scalar_dtyp is_scalar_dtyp_base] in Hsc.
    destruct dtb as [sz | | | | fp | | | | | |]; try discriminate Hsc.
    - left; exists sz; reflexivity.
    - right; left; reflexivity.
    - destruct fp; try discriminate Hsc;
        [right; right; left; reflexivity | right; right; right; reflexivity].
  Qed.

  Lemma scalar_dtyp_not_void (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    dtyp_eqb dt DTYPE_Void = false.
  Proof using.
    intros Hsc; apply is_scalar_dtyp_inv in Hsc as (dtb & -> & Hdtb).
    unfold dtyp_eqb; destruct (dtyp_eq_dec (DTYPE_Base dtb) (DTYPE_Base DTYPE_Void)) as [Heq | _];
      [| reflexivity].
    inversion Heq; subst dtb.
    destruct Hdtb as [[sz H] | [H | [H | H]]]; discriminate H.
  Qed.

  Lemma scalar_store_size_pos (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    (1 <= @store_size_dtyp SizeofV dt)%N.
  Proof using.
    intros Hsc; apply is_scalar_dtyp_inv in Hsc as (dtb & -> & Hdtb).
    destruct Hdtb as [[sz ->] | [-> | [-> | ->]]];
      cbn [store_size_dtyp SizeofV Store_size_dtyp Sizeof_dtyp_base ptr_size byte_sizeof_floating_point_variant];
      try lia.
    rewrite round_up_to_eight_div by lia.
    apply N.div_le_lower_bound; lia.
  Qed.

  Lemma bit_sizeof_vec1_eq (dt : dtyp) :
    (@bit_sizeof_dtyp SizeofV (DTYPE_Array true 1%N dt) =? @bit_sizeof_dtyp SizeofV dt)%N = true.
  Proof using.
    cbn [bit_sizeof_dtyp SizeofV Bit_sizeof_dtyp].
    rewrite N.mul_1_l; apply N.eqb_refl.
  Qed.

  Lemma vec1_neq_base (dt : dtyp) (dtb : dtyp_base) :
    dtyp_eqb (DTYPE_Array true 1%N dt) (DTYPE_Base dtb) = false.
  Proof using.
    unfold dtyp_eqb.
    destruct (dtyp_eq_dec (DTYPE_Array true 1%N dt) (DTYPE_Base dtb)) as [Heq | _];
      [discriminate Heq | reflexivity].
  Qed.

  Lemma N_length_h_eq {A} (l : list A) (acc : N) :
    ListUtil.N.length_h l acc = (N.of_nat (List.length l) + acc)%N.
  Proof using.
    revert acc; induction l as [| x xs IH]; intros acc;
      cbn [ListUtil.N.length_h List.length]; [lia |].
    rewrite IH; lia.
  Qed.

  Lemma N_length_eq {A} (l : list A) :
    ListUtil.N.length l = N.of_nat (List.length l).
  Proof using.
    unfold ListUtil.N.length; rewrite N_length_h_eq; lia.
  Qed.

  Lemma dvalue_to_memory_bytes_base_ok
    (dtb : dtyp_base) (db : @dvalue_base (@ParamsV IP IPT)) :
    exists bs : list (@memory_byte (@ParamsV IP IPT)),
      dvalue_to_memory_bytes (DTYPE_Base dtb) (DVALUE_Base db) None = raise_ret bs /\
      List.length bs = N.to_nat (@store_size_dtyp SizeofV (DTYPE_Base dtb)).
  Proof using.
    unfold dvalue_to_memory_bytes, acc_dvalue_to_memory_bytes_h,
           acc_memory_bytes_of_dvalue_base, accumulate_padding.
    eexists; split; [reflexivity |].
    rewrite rev_append_rev, app_nil_r, rev_length, rev_loop_acc_length.
    cbn [List.length]; lia.
  Qed.

  Lemma dvalue_to_memory_bytes_base_err
    (dtb : dtyp_base) (v : @dvalue (@ParamsV IP IPT))
    (Hnot_base : forall db, v <> DVALUE_Base db) :
    exists msg : string,
      dvalue_to_memory_bytes (DTYPE_Base dtb) v None = raise_error msg.
  Proof using.
    destruct v as [db | |]; [exfalso; exact (Hnot_base db Logic.eq_refl) | |];
      eexists; reflexivity.
  Qed.

  Lemma dvalue_to_memory_bytes_vec1_eq
    (dtb : dtyp_base) (db : @dvalue_base (@ParamsV IP IPT)) :
    dvalue_to_memory_bytes (DTYPE_Array true 1%N (DTYPE_Base dtb))
      (DVALUE_Array true [DVALUE_Base db]) None =
    dvalue_to_memory_bytes (DTYPE_Base dtb) (DVALUE_Base db) None.
  Proof using.
    unfold dvalue_to_memory_bytes.
    cbn -[acc_memory_bytes_of_dvalue_base].
    destruct (acc_memory_bytes_of_dvalue_base dtb db 0%N []) as [off bs].
    cbn; reflexivity.
  Qed.

  Lemma alloc_poison_bytes_eq (dt : dtyp) :
    concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt)) =
    List.repeat (@poison_memory_byte (@ParamsV IP IPT))
      (N.to_nat (@store_size_dtyp SizeofV dt)).
  Proof using.
    rewrite concat_acc_eq.
    change (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))
      with [@generate_poison_bytes (@ParamsV IP IPT) dt].
    cbn [List.concat]; rewrite app_nil_r.
    unfold generate_poison_bytes, generate_num_poison_bytes, generate_num_poison_bytes_h.
    rewrite N_to_nat_safe_eq, seq_map_acc_eq, map_const_Nseq; reflexivity.
  Qed.

  Lemma dvalue_to_memory_bytes_poison_base (dtb : dtyp_base) :
    @dvalue_to_memory_bytes (@ParamsV IP IPT) (DTYPE_Base dtb) (DVALUE_Base DVALUE_Poison) None =
    raise_ret (List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                 (N.to_nat (@store_size_dtyp SizeofV (DTYPE_Base dtb)))).
  Proof using.
    unfold dvalue_to_memory_bytes, acc_dvalue_to_memory_bytes_h,
           acc_memory_bytes_of_dvalue_base, accumulate_padding.
    cbn -[ListUtil.N.rev_loop_acc store_size_dtyp poison_memory_byte].
    rewrite rev_loop_acc_const, app_nil_r, rev_append_rev, app_nil_r, rev_repeat.
    reflexivity.
  Qed.

  Lemma memory_bytes_to_dvalue_b8_total
    (dbs : list (@memory_byte (@ParamsV IP IPT))) :
    exists dv : @dvalue (@ParamsV IP IPT),
      memory_bytes_to_dvalue dbs (DTYPE_Base (DTYPE_B 8)) = raise_ret dv.
  Proof using.
    cbn [memory_bytes_to_dvalue memory_bytes_to_dvalue_base].
    set (td := take (@store_size_dtyp SizeofV (DTYPE_Base (DTYPE_B 8))) dbs).
    destruct (all_poison_bytes td); [eexists; reflexivity |].
    assert (Hbv : exists bv, memory_bytes_to_byte_value 8 td = raise_ret bv).
    { unfold memory_bytes_to_byte_value.
      destruct (memory_bytes_to_pointer_slice td) as [[p k] |];
        [destruct (pointer_chunk_aligned 8 k); eexists; reflexivity | eexists; reflexivity]. }
    destruct Hbv as [bv Hbv]; rewrite Hbv; cbn.
    destruct (dvalue_bv_all_poison bv); eexists; reflexivity.
  Qed.

  Lemma memory_bytes_to_dvalue_b8_array_total
    (dbs : list (@memory_byte (@ParamsV IP IPT))) (n : N) :
    exists dv : @dvalue (@ParamsV IP IPT),
      memory_bytes_to_dvalue dbs (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) = raise_ret dv.
  Proof using.
    cbn [memory_bytes_to_dvalue].
    destruct (poison_split dbs) as [np rest].
    destruct rest as [| b0 rest']; [eexists; reflexivity |].
    set (stride := @alloc_size_dtyp SizeofV (DTYPE_Base (DTYPE_B 8))).
    set (ssz := @store_size_dtyp SizeofV (DTYPE_Base (DTYPE_B 8))).
    set (go := fix loop (cnt : nat) (off : N) (bs : list (@memory_byte (@ParamsV IP IPT)))
                 : EOU (list (@dvalue (@ParamsV IP IPT))) :=
                 match cnt with
                 | O => Monads.ret []
                 | S cnt' =>
                     Monads.bind
                       (if N.leb (off + ssz) np
                        then Monads.ret (DVALUE_Base DVALUE_Poison)
                        else memory_bytes_to_dvalue (take ssz bs) (DTYPE_Base (DTYPE_B 8)))
                       (fun e =>
                          Monads.bind (loop cnt' (off + stride)%N (drop stride bs))
                            (fun es => Monads.ret (e :: es)))
                 end).
    assert (Hgo : forall cnt off bs, exists elts, go cnt off bs = raise_ret elts).
    { induction cnt as [| cnt' IH]; intros off bs; cbn [go]; [eexists; reflexivity |].
      assert (He : exists e,
                 (if N.leb (off + ssz) np
                  then Monads.ret (DVALUE_Base DVALUE_Poison)
                  else memory_bytes_to_dvalue (take ssz bs) (DTYPE_Base (DTYPE_B 8))) = raise_ret e).
      { destruct (N.leb (off + ssz) np); [eexists; reflexivity | apply memory_bytes_to_dvalue_b8_total]. }
      destruct He as [e ->]; cbn.
      destruct (IH (off + stride)%N (drop stride bs)) as [elts ->]; cbn.
      eexists; reflexivity. }
    destruct (Hgo (N.to_nat n) 0%N (b0 :: rest')) as [elts Helts].
    change (Monads.bind (go (N.to_nat n) 0%N (b0 :: rest'))
              (fun es => Monads.ret (canonicalize_agg (DVALUE_Array false) es)))
      with (elts0 <- go (N.to_nat n) 0%N (b0 :: rest');;
            Monads.ret (canonicalize_agg (DVALUE_Array false) elts0)).
    rewrite Helts; cbn; eexists; reflexivity.
  Qed.

  (** ** 3C. Allocation Keys, Consecutive Pointers, Frame Memory & Safe Provenance *)

  Lemma next_key_le_aligned {A} (m : IntMap A) (align : N) :
    (IntMaps.next_key m <= next_key_with_alignment m align)%Z.
  Proof using.
    unfold IntMaps.next_key, next_key_with_alignment, Handlers.Memory.pad_to.
    destruct (IM_greatest_key m) as [gk |]; lia.
  Qed.

  Lemma next_key_with_alignment_pos {A} (m : IntMap A) (align : N) :
    (1 <= next_key_with_alignment m align)%Z.
  Proof using.
    unfold next_key_with_alignment, Handlers.Memory.pad_to.
    destruct (IM_greatest_key m); lia.
  Qed.

  Lemma next_key_with_alignment_fresh {A} (m : IntMap A) (align : N) (z : Z) :
    (next_key_with_alignment m align <= z)%Z ->
    IntMaps.lookup z m = None.
  Proof using.
    intros Hz.
    destruct (IntMaps.lookup z m) as [v |] eqn:Efind; [| reflexivity].
    exfalso.
    assert (Hin : IM.In z m).
    { exists v; apply IM.find_2, Efind. }
    pose proof (IntMaps.next_key_correct m z Hin) as Hlt.
    pose proof (next_key_le_aligned m align) as Hle.
    lia.
  Qed.

  Lemma map_monad_acc_EOU_eq {A B} (f : A -> EOU B) (l : list A) :
    map_monad_acc f l = map_monad f l.
  Proof using.
    unfold map_monad_acc.
    set (go := fix loop (acc : list B) (xs : list A) : EOU (list B) :=
                 match xs with
                 | [] => Monads.ret (rev_append acc [])
                 | a :: xs' => Monads.bind (f a) (fun b => loop (b :: acc) xs')
                 end).
    change (go [] l = map_monad f l).
    assert (Hgo : forall xs acc,
              go acc xs = Monads.bind (map_monad f xs) (fun bs => Monads.ret (rev_append acc bs))).
    { induction xs as [| a xs' IH]; intros acc; cbn [go map_monad]; [reflexivity |].
      destruct (f a) eqn:Efa; cbn; try reflexivity.
      rewrite IH; destruct (map_monad f xs'); reflexivity. }
    rewrite Hgo; destruct (map_monad f l); reflexivity.
  Qed.

  Lemma ptr_byte_offset_spec (p q : @ptr ProvenanceV (@PointerV IP)) (ix : iptr) :
    ptr_byte_offset p ix = raise_ret q ->
    ptr_to_int q = (ptr_to_int p + to_Z ix)%Z /\
    ptr_provenance q = ptr_provenance p.
  Proof using.
    unfold ptr_byte_offset.
    change (@alloc_size_dtyp (@ParamsV IP IPT) (DTYPE_Base (DTYPE_B 8))) with 1%N.
    cbn [int_to_ptr PIV ptr_to_int ptr_provenance PointerV fst snd].
    destruct (from_Z (to_Z (fst p) + 1 * to_Z ix)%Z) as [| | | ip] eqn:Efz;
      cbn; try discriminate.
    intros Hq; inversion Hq; subst q; cbn.
    apply from_Z_to_Z in Efz.
    split; [lia | reflexivity].
  Qed.

  Lemma get_consecutive_ptrs_seq_spec
    (p : @ptr ProvenanceV (@PointerV IP))
    (n : nat) (start : N) (ixs : list iptr)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) :
    map_monad (fun k : N => from_Z (Z.of_N k)) (Nseq start n) = raise_ret ixs ->
    map_monad (ptr_byte_offset p) ixs = raise_ret ptrs ->
    List.length ptrs = n /\
    (forall k q,
       nth_error ptrs k = Some q ->
       (k < n)%nat /\
       ptr_to_int q = (ptr_to_int p + Z.of_N start + Z.of_nat k)%Z /\
       ptr_provenance q = ptr_provenance p) /\
    (forall k,
       (k < n)%nat ->
       exists q,
         nth_error ptrs k = Some q /\
         ptr_to_int q = (ptr_to_int p + Z.of_N start + Z.of_nat k)%Z /\
         ptr_provenance q = ptr_provenance p).
  Proof using.
    revert start ixs ptrs; induction n as [| n' IH]; intros start ixs ptrs Hixs Hptrs;
      cbn [Nseq map_monad] in Hixs.
    - inversion Hixs; subst ixs; cbn [map_monad] in Hptrs; inversion Hptrs; subst ptrs.
      split; [reflexivity | split].
      + intros [| k] q Hk; discriminate Hk.
      + intros k Hk; lia.
    - apply EOU_bind_ret_inv in Hixs as (ix0 & Hfz0 & Hixs').
      apply EOU_bind_ret_inv in Hixs' as (ixs_tl & Hmap_ix & Heq_ixs).
      inversion Heq_ixs; subst ixs; clear Heq_ixs.
      cbn [map_monad] in Hptrs.
      apply EOU_bind_ret_inv in Hptrs as (q0 & Hq0 & Hptrs').
      apply EOU_bind_ret_inv in Hptrs' as (ptrs_tl & Hmap_tl & Heq_ptrs).
      inversion Heq_ptrs; subst ptrs; clear Heq_ptrs.
      apply from_Z_to_Z in Hfz0.
      apply ptr_byte_offset_spec in Hq0 as [Hq0_int Hq0_pr].
      destruct (IH (N.succ start) ixs_tl ptrs_tl Hmap_ix Hmap_tl) as (Hlen & Hnth_inv & Hnth_ex).
      split; [cbn [List.length]; lia | split].
      + intros [| k] q Hnth; cbn [nth_error] in Hnth.
        * inversion Hnth; subst q.
          split; [lia | split; [lia | exact Hq0_pr]].
        * destruct (Hnth_inv k q Hnth) as (Hk & Hq_int & Hq_pr).
          split; [lia | split; [lia | exact Hq_pr]].
      + intros [| k] Hk; cbn [nth_error].
        * exists q0; split; [reflexivity | split; [lia | exact Hq0_pr]].
        * assert (Hk' : (k < n')%nat) by lia.
          destruct (Hnth_ex k Hk') as (q & Hnth & Hq_int & Hq_pr).
          exists q; split; [exact Hnth | split; [lia | exact Hq_pr]].
  Qed.

  Lemma get_consecutive_ptrs_spec
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) :
    get_consecutive_ptrs p size = raise_ret ptrs ->
    List.length ptrs = N.to_nat size /\
    (forall k q,
       nth_error ptrs k = Some q ->
       (k < N.to_nat size)%nat /\
       ptr_to_int q = (ptr_to_int p + Z.of_nat k)%Z /\
       ptr_provenance q = ptr_provenance p) /\
    (forall k,
       (k < N.to_nat size)%nat ->
       exists q,
         nth_error ptrs k = Some q /\
         ptr_to_int q = (ptr_to_int p + Z.of_nat k)%Z /\
         ptr_provenance q = ptr_provenance p).
  Proof using.
    unfold get_consecutive_ptrs, intptr_seq.
    rewrite N_to_nat_safe_eq, seq_map_monad_acc_eq.
    intros H; apply EOU_bind_ret_inv in H as (ixs & Hixs & Hptrs).
    rewrite map_monad_acc_EOU_eq in Hptrs.
    destruct (get_consecutive_ptrs_seq_spec p (N.to_nat size) 0%N ixs ptrs Hixs Hptrs)
      as (Hlen & Hinv & Hex).
    split; [exact Hlen | split].
    - intros k q Hnth; destruct (Hinv k q Hnth) as (Hk & Hq_int & Hq_pr).
      split; [exact Hk | split; [lia | exact Hq_pr]].
    - intros k Hk; destruct (Hex k Hk) as (q & Hnth & Hq_int & Hq_pr).
      exists q; split; [exact Hnth | split; [lia | exact Hq_pr]].
  Qed.

  Lemma get_consecutive_ptrs_in_addrs
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP))) (z : Z)
    (Hptrs : get_consecutive_ptrs p size = raise_ret ptrs) :
    In z (List.map ptr_to_int ptrs) <->
    (ptr_to_int p <= z < ptr_to_int p + Z.of_nat (N.to_nat size))%Z.
  Proof using.
    destruct (get_consecutive_ptrs_spec p size ptrs Hptrs) as (Hlen & Hinv & Hex).
    split.
    - intros Hin; apply in_map_iff in Hin as (q & <- & Hin_q).
      apply In_nth_error in Hin_q as [k Hnth].
      destruct (Hinv k q Hnth) as (Hk & Hq_int & _); lia.
    - intros Hz.
      set (k := Z.to_nat (z - ptr_to_int p)).
      assert (Hk : (k < N.to_nat size)%nat) by lia.
      destruct (Hex k Hk) as (q & Hnth & Hq_int & _).
      replace z with (ptr_to_int q) by lia.
      apply in_map, (nth_error_In ptrs k Hnth).
  Qed.

  Lemma get_consecutive_ptrs_well_behaved {IPWB : IPtrWellBehaved IP}
    (p : @ptr ProvenanceV (@PointerV IP)) (size : N) :
    (exists ptrs, get_consecutive_ptrs p size = raise_ret ptrs) \/
    (exists msg, get_consecutive_ptrs p size = raise_oom msg).
  Proof using.
    unfold get_consecutive_ptrs, intptr_seq.
    rewrite N_to_nat_safe_eq, seq_map_monad_acc_eq.
    assert (Hix : forall n start,
              (exists ixs, map_monad (fun k : N => from_Z (Z.of_N k)) (Nseq start n) = raise_ret ixs) \/
              (exists msg, map_monad (fun k : N => from_Z (Z.of_N k)) (Nseq start n) = raise_oom msg)).
    { induction n as [| n' IH]; intros start; cbn [Nseq map_monad]; [left; exists []; reflexivity |].
      destruct (from_Z_ret_or_oom (Z.of_N start)) as [[ix ->] | [msg ->]]; cbn; [| right; exists msg; reflexivity].
      destruct (IH (N.succ start)) as [[ixs ->] | [msg ->]]; cbn;
        [left; exists (ix :: ixs); reflexivity | right; exists msg; reflexivity]. }
    destruct (Hix (N.to_nat size) 0%N) as [[ixs Hixs] | [msg Hmsg]].
    - change (Basics.compose from_Z Z.of_N) with (fun k : N => from_Z (Z.of_N k)).
      rewrite Hixs; cbn; rewrite map_monad_acc_EOU_eq.
      induction ixs as [| ix ixs' IH]; cbn [map_monad]; [left; exists []; reflexivity |].
      unfold ptr_byte_offset, int_to_ptr, PIV; cbn [Monads.bind Monad_either].
      destruct (from_Z_ret_or_oom (ptr_to_int p + Z.of_N (alloc_size_dtyp (DTYPE_Base (DTYPE_B 8))) * to_Z ix)%Z)
        as [[i ->] | [msg ->]]; cbn; [| right; exists msg; reflexivity].
      destruct IH as [[ptrs ->] | [msg ->]]; cbn;
        [left; exists ((i, ptr_provenance p) :: ptrs); reflexivity | right; exists msg; reflexivity].
    - change (Basics.compose from_Z Z.of_N) with (fun k : N => from_Z (Z.of_N k)).
      rewrite Hmsg; right; exists msg; reflexivity.
  Qed.

  Lemma lookup_add_all_index_in {A} (vs : list A) (base : Z) (m : IntMap A)
    (k : nat) (v : A) (z : Z) :
    nth_error vs k = Some v ->
    z = (base + Z.of_nat k)%Z ->
    IntMaps.lookup z (IntMaps.add_all_index vs base m) = Some v.
  Proof using.
    revert base k z; induction vs as [| v0 vs' IH]; intros base [| k] z Hnth ->;
      cbn [nth_error] in Hnth; try discriminate Hnth.
    - inversion Hnth; subst v0.
      replace (base + Z.of_nat 0)%Z with base by lia.
      cbn [IntMaps.add_all_index]; apply IntMaps.lookup_add_eq.
    - cbn [IntMaps.add_all_index].
      rewrite IntMaps.lookup_add_ineq by lia.
      apply (IH (base + 1)%Z k); [exact Hnth | lia].
  Qed.

  Lemma lookup_add_all_index_out {A} (vs : list A) (base : Z) (m : IntMap A) (z : Z) :
    ~ (base <= z < base + Z.of_nat (List.length vs))%Z ->
    IntMaps.lookup z (IntMaps.add_all_index vs base m) = IntMaps.lookup z m.
  Proof using.
    revert base; induction vs as [| v0 vs' IH]; intros base Hout;
      cbn [IntMaps.add_all_index List.length] in *; [reflexivity |].
    rewrite IntMaps.lookup_add_ineq by lia.
    apply IH; lia.
  Qed.

  Lemma lookup_add_all_index_acc_in {A} (vs : list A) (base : Z) (m : IntMap A)
    (k : nat) (v : A) (z : Z) :
    nth_error vs k = Some v ->
    z = (base + Z.of_nat k)%Z ->
    IntMaps.lookup z (IntMaps.add_all_index_acc vs base m) = Some v.
  Proof using.
    intros Hnth Hz.
    pose proof (IntMaps.add_all_index_acc_eq vs base m z) as Heq.
    rewrite Heq; eapply lookup_add_all_index_in; eassumption.
  Qed.

  Lemma lookup_add_all_index_acc_out {A} (vs : list A) (base : Z) (m : IntMap A) (z : Z) :
    ~ (base <= z < base + Z.of_nat (List.length vs))%Z ->
    IntMaps.lookup z (IntMaps.add_all_index_acc vs base m) = IntMaps.lookup z m.
  Proof using.
    intros Hout.
    pose proof (IntMaps.add_all_index_acc_eq vs base m z) as Heq.
    rewrite Heq; apply lookup_add_all_index_out, Hout.
  Qed.

  Lemma add_all_to_frame_Singleton
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (mem : @memory (@ParamsV IP IPT))
    (f : @Frame (@ParamsV IP IPT))
    (h : @Heap (@ParamsV IP IPT)) :
    add_all_to_frame ks (mkMemoryStack mem (Singleton f) h) =
    mkMemoryStack mem (Singleton (rev ks ++ f)) h.
  Proof using.
    revert f; induction ks as [| k ks' IH]; intros f;
      cbn [add_all_to_frame fold_left add_to_frame rev app]; [reflexivity |].
    rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma add_all_to_frame_Snoc
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (mem : @memory (@ParamsV IP IPT))
    (s : @Framestack (@ParamsV IP IPT))
    (f : @Frame (@ParamsV IP IPT))
    (h : @Heap (@ParamsV IP IPT)) :
    add_all_to_frame ks (mkMemoryStack mem (Snoc s f) h) =
    mkMemoryStack mem (Snoc s (rev ks ++ f)) h.
  Proof using.
    revert f; induction ks as [| k ks' IH]; intros f;
      cbn [add_all_to_frame fold_left add_to_frame rev app]; [reflexivity |].
    rewrite IH, <- app_assoc; reflexivity.
  Qed.

  Lemma in_map_rev_app_iff {A B} (g : A -> B) (xs ys : list A) (y : B) :
    In y (List.map g (rev xs ++ ys)) <->
    In y (List.map g xs) \/ In y (List.map g ys).
  Proof using.
    rewrite map_app, map_rev, in_app_iff, <- in_rev; reflexivity.
  Qed.

  Lemma lookup_free_frame_memory_out
    (f : @Frame (@ParamsV IP IPT))
    (m : @memory (@ParamsV IP IPT)) (z : Z) :
    ~ In z (List.map ptr_to_int f) ->
    IntMaps.lookup z (free_frame_memory f m) = IntMaps.lookup z m.
  Proof using.
    revert m; induction f as [| k0 f' IH]; intros m Hnin;
      cbn [free_frame_memory fold_left List.map] in *; [reflexivity |].
    rewrite IH by (intros Hx; apply Hnin; right; exact Hx).
    unfold free_byte; apply lookup_delete_neq.
    intros ->; apply Hnin; left; reflexivity.
  Qed.

  Lemma lookup_free_frame_memory_in
    (f : @Frame (@ParamsV IP IPT))
    (m : @memory (@ParamsV IP IPT)) (z : Z) :
    In z (List.map ptr_to_int f) ->
    IntMaps.lookup z (free_frame_memory f m) = None.
  Proof using.
    revert m; induction f as [| k0 f' IH]; intros m Hin;
      cbn [free_frame_memory fold_left List.map] in *; [contradiction |].
    destruct (in_dec Z.eq_dec z (List.map ptr_to_int f')) as [Hin' | Hnin'].
    - apply IH, Hin'.
    - destruct Hin as [<- | Hin]; [| contradiction].
      rewrite lookup_free_frame_memory_out by exact Hnin'.
      unfold free_byte; apply lookup_delete_eq.
  Qed.

  Definition safe_prov (P_unprom : list N) (pr : @prov ProvenanceV) : Prop :=
    match pr with
    | None => False
    | Some ps => incl ps P_unprom
    end.

  Definition is_safe_ptr_dvalue (P_unprom : list N) (v : @dvalue (@ParamsV IP IPT)) : Prop :=
    forall pt, v = DVALUE_Base (DVALUE_Pointer pt) -> safe_prov P_unprom (ptr_provenance pt).

  Definition genv_safe (P_unprom : list N) (g : @global_env (@ParamsV IP IPT)) : Prop :=
    forall gid v, Maps.lookup gid g = Some v -> is_safe_ptr_dvalue P_unprom v.

  Lemma safe_prov_incl (P1 P2 : list N) (pr : @prov ProvenanceV) :
    incl P1 P2 ->
    safe_prov P1 pr ->
    safe_prov P2 pr.
  Proof using.
    intros Hinc Hpr; destruct pr as [ps |]; [eapply incl_tran; eassumption | exact Hpr].
  Qed.

  Lemma is_safe_ptr_dvalue_incl (P1 P2 : list N) (v : @dvalue (@ParamsV IP IPT)) :
    incl P1 P2 ->
    is_safe_ptr_dvalue P1 v ->
    is_safe_ptr_dvalue P2 v.
  Proof using.
    intros Hinc Hv pt Hpt; eapply safe_prov_incl; [exact Hinc | apply Hv, Hpt].
  Qed.

  Lemma genv_safe_incl (P1 P2 : list N) (g : @global_env (@ParamsV IP IPT)) :
    incl P1 P2 ->
    genv_safe P1 g ->
    genv_safe P2 g.
  Proof using.
    intros Hinc Hg gid v Hlk; eapply is_safe_ptr_dvalue_incl; [exact Hinc | eapply Hg, Hlk].
  Qed.

  Lemma null_safe_ptr_dvalue (P_unprom : list N) :
    is_safe_ptr_dvalue P_unprom (DVALUE_Base (DVALUE_Pointer null)).
  Proof using.
    intros pt Hpt; inversion Hpt; subst pt; cbn; intros x [].
  Qed.

  Lemma poison_safe_ptr_dvalue (P_unprom : list N) :
    is_safe_ptr_dvalue P_unprom (DVALUE_Base DVALUE_Poison).
  Proof using.
    intros pt Hpt; discriminate Hpt.
  Qed.

  Lemma fresh_ptr_safe_dvalue (P_unprom : list N) (pt : @ptr ProvenanceV (@PointerV IP)) (pr : N) :
    ptr_provenance pt = Some [pr] ->
    is_safe_ptr_dvalue (pr :: P_unprom) (DVALUE_Base (DVALUE_Pointer pt)).
  Proof using.
    intros Hpr pt' Hpt'; inversion Hpt'; subst pt'.
    unfold safe_prov; rewrite Hpr; intros z [<- | []]; left; reflexivity.
  Qed.

  Lemma safe_prov_access_disjoint (P_unprom : list N) (pr : @prov ProvenanceV) (pr_prom : N) :
    safe_prov P_unprom pr ->
    ~ In pr_prom P_unprom ->
    @access_allowed ProvenanceV pr (Some pr_prom) = false.
  Proof using.
    intros Hsafe Hnin.
    destruct pr as [ps |]; [| contradiction Hsafe].
    cbn [access_allowed ProvenanceV].
    destruct (existsb (N.eqb pr_prom) ps) eqn:Eex; [| reflexivity].
    exfalso; apply existsb_exists in Eex as (x & Hx & Heqb).
    apply N.eqb_eq in Heqb; subst x.
    apply Hnin, Hsafe, Hx.
  Qed.

  Lemma eval_gep_safe_ptr (P_unprom : list N) (flags : gep_flags) (dt : dtyp)
    (dv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT)))
    (res : @dvalue (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_unprom dv ->
    eval_gep flags dt dv vs = raise_ret res ->
    is_safe_ptr_dvalue P_unprom res.
  Proof using.
    intros Hdv Hgep.
    unfold eval_gep in Hgep.
    destruct dv as [[pt | | | | | | |] | |]; try discriminate Hgep.
    - unfold catch_pois, Functor.fmap, Functor_Monad in Hgep.
      destruct (handle_gep_ptr flags dt pt vs) as [| | | [| pt']] eqn:Eh;
        cbn in Hgep; try discriminate Hgep; inversion Hgep; subst res.
      + apply poison_safe_ptr_dvalue.
      + intros pt0 Hpt0; inversion Hpt0; subst pt0.
        pose proof (handle_gep_ptr_preserves_provenance flags dt vs pt pt' Eh) as Hpr.
        rewrite <- Hpr; apply (Hdv pt Logic.eq_refl).
    - inversion Hgep; subst res; apply poison_safe_ptr_dvalue.
  Qed.

  Lemma eval_select_safe_ptr (P_unprom : list N)
    (cnd : @dvalue (@ParamsV IP IPT)) (vt : dtyp)
    (v1 v2 res : @dvalue (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_unprom v1 ->
    is_safe_ptr_dvalue P_unprom v2 ->
    eval_select cnd vt v1 v2 = raise_ret res ->
    is_safe_ptr_dvalue P_unprom res.
  Proof using.
    intros Hv1 Hv2 Hsel; unfold eval_select in Hsel.
    destruct cnd as [cb | | vec conds]; try discriminate Hsel.
    - unfold eval_select_base_dvalue in Hsel.
      destruct cb; try discriminate Hsel.
      + destruct sz; try discriminate Hsel.
        destruct (@Integers.unsigned 1 i =? 1)%Z; inversion Hsel; subst res; assumption.
      + inversion Hsel; subst res; apply poison_safe_ptr_dvalue.
    - destruct vec; [| discriminate Hsel].
      destruct vt as [| | vec_t sz_t elt_t]; try discriminate Hsel.
      destruct vec_t; [| discriminate Hsel].
      destruct (map_monad dvalue_to_dvalue_base conds) as [| | | conds'];
        cbn in Hsel; try discriminate Hsel.
      destruct v1 as [[| | | | | | |] | | [|] elts1],
               v2 as [[| | | | | | |] | | [|] elts2];
        cbn in Hsel; try discriminate Hsel;
        try (inversion Hsel; subst res; apply poison_safe_ptr_dvalue);
        unfold Functor.fmap, Functor_Monad in Hsel;
        destruct (vec_loop _ _) as [| | | out]; cbn in Hsel; try discriminate Hsel;
        inversion Hsel; subst res; unfold canonicalize_vector in *;
        destruct (forallb dvalue_is_poison out);
        [apply poison_safe_ptr_dvalue | intros pt Hpt; discriminate Hpt].
  Qed.

  (** ** 3D. Stage 1 Ghost-Slot Memory Invariant & Primitive Simulation *)

  Record ghost_slot : Type := mkGhostSlot {
    gs_pt    : @ptr ProvenanceV (@PointerV IP);
    gs_ptrs  : list (@ptr ProvenanceV (@PointerV IP));
    gs_pr    : N;
    gs_dt    : dtyp;
    gs_db    : @dvalue_base (@ParamsV IP IPT);
    gs_bytes : list (@memory_byte (@ParamsV IP IPT))
  }.

  Definition gs_len (gs : ghost_slot) : nat :=
    N.to_nat (@store_size_dtyp SizeofV (gs_dt gs)).

  Definition gs_addr (gs : ghost_slot) : Z :=
    ptr_to_int (gs_pt gs).

  Definition gs_in_range (gs : ghost_slot) (z : Z) : Prop :=
    (gs_addr gs <= z < gs_addr gs + Z.of_nat (gs_len gs))%Z.

  Definition gs_wf (gs : ghost_slot) : Prop :=
    is_scalar_dtyp (gs_dt gs) = true /\
    ptr_provenance (gs_pt gs) = Some [gs_pr gs] /\
    get_consecutive_ptrs (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) = raise_ret (gs_ptrs gs) /\
    dvalue_to_memory_bytes (gs_dt gs) (DVALUE_Base (gs_db gs)) None = raise_ret (gs_bytes gs) /\
    List.length (gs_bytes gs) = gs_len gs /\
    (1 <= gs_addr gs)%Z.

  Definition gs_disjoint (gs1 gs2 : ghost_slot) : Prop :=
    forall z, gs_in_range gs1 z -> ~ gs_in_range gs2 z.

  Fixpoint ghost_list_disjoint (G : list ghost_slot) : Prop :=
    match G with
    | [] => True
    | gs :: G' => (forall gs', In gs' G' -> gs_disjoint gs gs') /\ ghost_list_disjoint G'
    end.

  Lemma ghost_list_disjoint_sym_neq (G : list ghost_slot) :
    ghost_list_disjoint G ->
    forall gs1 gs2 z,
      In gs1 G ->
      In gs2 G ->
      gs_in_range gs1 z ->
      gs_in_range gs2 z ->
      gs1 = gs2.
  Proof using.
    induction G as [| gs0 G' IH]; intros Hdisj gs1 gs2 z Hin1 Hin2 Hr1 Hr2;
      [contradiction |].
    destruct Hdisj as [Hhd Htl].
    destruct Hin1 as [<- | Hin1], Hin2 as [<- | Hin2].
    - reflexivity.
    - exfalso; eapply (Hhd gs2 Hin2 z Hr1 Hr2).
    - exfalso; eapply (Hhd gs1 Hin1 z Hr2 Hr1).
    - eapply IH; eassumption.
  Qed.

  Lemma gs_in_range_dec (gs : ghost_slot) (z : Z) :
    {gs_in_range gs z} + {~ gs_in_range gs z}.
  Proof using.
    unfold gs_in_range.
    destruct (Z_le_gt_dec (gs_addr gs) z) as [Hle | Hgt].
    - destruct (Z_lt_ge_dec z (gs_addr gs + Z.of_nat (gs_len gs))) as [Hlt | Hge].
      + left; lia.
      + right; lia.
    - right; lia.
  Qed.

  Lemma stage1_find_gs_at (G : list ghost_slot) (z : Z) :
    {gs : ghost_slot | In gs G /\ gs_in_range gs z} +
    {forall gs, In gs G -> ~ gs_in_range gs z}.
  Proof using.
    induction G as [| gs0 G' IH].
    - right; intros gs [].
    - destruct (gs_in_range_dec gs0 z) as [Hin0 | Hout0].
      + left; exists gs0; split; [left; reflexivity | exact Hin0].
      + destruct IH as [[gs [Hgs Hr]] | Hall].
        * left; exists gs; split; [right; exact Hgs | exact Hr].
        * right; intros gs [<- | Hgs]; [exact Hout0 | apply Hall, Hgs].
  Qed.

  Inductive framestack_ghost_wf
    : list ghost_slot -> @Framestack (@ParamsV IP IPT) -> Prop :=
  | FGW_Base fs :
      framestack_ghost_wf [] fs
  | FGW_Snoc_Unprom G fs f :
      framestack_ghost_wf G fs ->
      (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
      framestack_ghost_wf G (Snoc fs f)
  | FGW_Snoc_Prom gs G fs f :
      framestack_ghost_wf G fs ->
      (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) ->
      (forall z, In z (List.map ptr_to_int f) -> forall gs', In gs' G -> ~ gs_in_range gs' z) ->
      framestack_ghost_wf (gs :: G) (Snoc fs f).

  Definition stage1_mem_inv (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) : Prop :=
    incl P_unprom U /\
    NoDup (List.map gs_pr G) /\
    Forall (fun gs => gs_wf gs /\ In (gs_pr gs) U /\ ~ In (gs_pr gs) P_unprom) G /\
    ghost_list_disjoint G /\
    framestack_ghost_wf G (Memory_stack_frame_stack (state_memory_stack σ2)) /\
    Memory_stack_frame_stack (state_memory_stack σ1) = Memory_stack_frame_stack (state_memory_stack σ2) /\
    Memory_stack_heap (state_memory_stack σ1) = Memory_stack_heap (state_memory_stack σ2) /\
    (forall z,
       (forall gs, In gs G -> ~ gs_in_range gs z) ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2))) /\
    (forall gs k mb,
       In gs G ->
       nth_error (gs_bytes gs) k = Some mb ->
       IntMaps.lookup (gs_addr gs + Z.of_nat k)%Z (Memory_stack_memory (state_memory_stack σ1)) =
         Some (mb, Some (gs_pr gs)) /\
       IntMaps.lookup (gs_addr gs + Z.of_nat k)%Z (Memory_stack_memory (state_memory_stack σ2)) =
         Some (poison_memory_byte, Some (gs_pr gs))).

  Lemma stage1_mem_inv_incl_U (U U' P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    incl U U' ->
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    stage1_mem_inv U' P_unprom G σ1 σ2.
  Proof using.
    intros Hinc (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    split; [eapply incl_tran; eassumption |].
    split; [exact Hnd |].
    split.
    - eapply Forall_impl; [| exact Hall].
      intros gs (Hwf & HinU & HninP); repeat split; [exact Hwf | apply Hinc, HinU | exact HninP].
    - exact (conj Hdisj (conj Hfgw (conj Hfs (conj Hh (conj Hout Hgs))))).
  Qed.

  Lemma stage1_mem_nil_is_equal (U P_unprom : list N) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom [] σ1 σ2 ->
    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2).
  Proof using.
    intros (_ & _ & _ & _ & _ & Hfs & Hh & Hout & _).
    repeat split; [| exact Hfs | exact Hh].
    intros z; apply Hout; intros gs [].
  Qed.

  Lemma stage1_equal_to_mem_inv (U P_unprom : list N) (σ1 σ2 : state) :
    incl P_unprom U ->
    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
    stage1_mem_inv U P_unprom [] σ1 σ2.
  Proof using.
    intros Hpu (Hm & Hfs & Hh).
    split; [exact Hpu |].
    split; [constructor |].
    split; [constructor |].
    split; [exact I |].
    split; [apply FGW_Base |].
    split; [exact Hfs |].
    split; [exact Hh |].
    split; [intros z _; apply Hm | intros gs _ _ []].
  Qed.

  Lemma stage1_gs_lookup_range (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (gs : ghost_slot) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    gs_in_range gs z ->
    exists mb,
      nth_error (gs_bytes gs) (Z.to_nat (z - gs_addr gs)) = Some mb /\
      IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) = Some (mb, Some (gs_pr gs)) /\
      IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2)) = Some (poison_memory_byte, Some (gs_pr gs)).
  Proof using.
    intros (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs) Hin Hr.
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [Hwf _].
    destruct Hwf as (_ & _ & _ & _ & Hlen & _).
    unfold gs_in_range in Hr.
    set (k := Z.to_nat (z - gs_addr gs)).
    assert (Hk : (k < List.length (gs_bytes gs))%nat) by lia.
    destruct (nth_error_Some (gs_bytes gs) k) as [_ Hsome].
    destruct (nth_error (gs_bytes gs) k) as [mb |] eqn:Enth;
      [| exfalso; apply Hsome; [exact Hk | reflexivity]].
    destruct (Hgs gs k mb Hin Enth) as [Hlk1 Hlk2].
    replace z with (gs_addr gs + Z.of_nat k)%Z by lia.
    exists mb; repeat split; [exact Enth | exact Hlk1 | exact Hlk2].
  Qed.

  Lemma stage1_mem_member_iff (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    (IntMaps.member z (Memory_stack_memory (state_memory_stack σ1)) <->
     IntMaps.member z (Memory_stack_memory (state_memory_stack σ2))).
  Proof using.
    intros Hinv.
    destruct (stage1_find_gs_at G z) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs z Hinv Hin Hr)
        as (mb & _ & Hlk1 & Hlk2).
      split; intros _.
      + eapply IntMaps.lookup_member; exact Hlk2.
      + eapply IntMaps.lookup_member; exact Hlk1.
    - destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      pose proof (Hout z Hout_z) as Heq.
      split; intros Hm; apply IntMaps.member_lookup in Hm as [v Hv];
        [rewrite Heq in Hv | rewrite <- Heq in Hv];
        eapply IntMaps.lookup_member; exact Hv.
  Qed.

  Lemma stage1_mem_next_key_eq (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (align : N) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) align =
    next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) align.
  Proof using.
    intros Hinv; unfold next_key_with_alignment.
    erewrite IM_greatest_key_morph; [reflexivity |].
    intros k; eapply stage1_mem_member_iff; exact Hinv.
  Qed.

  Lemma stage1_gs_fresh_above_next_key (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state) (align : N) (z : Z) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    (next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) align <= z)%Z ->
    forall gs, In gs G -> ~ gs_in_range gs z.
  Proof using.
    intros Hinv Hge gs Hin Hr.
    destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs z Hinv Hin Hr)
      as (mb & _ & Hlk1 & _).
    rewrite (next_key_with_alignment_fresh _ align z Hge) in Hlk1.
    discriminate Hlk1.
  Qed.

  Lemma int_to_ptr_spec (addr : Z) (pr_opt : @prov ProvenanceV)
    (pt : @ptr ProvenanceV (@PointerV IP)) :
    int_to_ptr addr pr_opt = raise_ret pt ->
    ptr_to_int pt = addr /\ ptr_provenance pt = pr_opt.
  Proof using.
    cbn [int_to_ptr PIV ptr_to_int ptr_provenance PointerV fst snd].
    destruct (from_Z addr) as [| | | ip] eqn:Efz; cbn; try discriminate.
    intros H; inversion H; subst pt; cbn.
    apply from_Z_to_Z in Efz; split; [exact Efz | reflexivity].
  Qed.

  Lemma memory_bytes_to_bytes_eq (aid : @allocationId ProvenanceV)
    (bs : list (@memory_byte (@ParamsV IP IPT))) :
    memory_bytes_to_bytes aid bs = List.map (fun b => (b, aid)) bs.
  Proof using.
    unfold memory_bytes_to_bytes; apply map_acc_eq.
  Qed.

  Lemma convert_impure_base_id_sync
    (ct : impure_conversion) (t1 : dtyp_base) (dv : @dvalue_base (@ParamsV IP IPT)) (t2 : dtyp_base)
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ1)
      (memM_interp_prov (convert_impure_base ct t1 dv t2) σ2).
  Proof using.
    unfold convert_impure_base, assert_inttoptr_types_ok.
    destruct ct.
    - destruct t1; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        cbn [Monads.bind memS_mon memS_bind Monads.ret];
        (destruct dv;
         eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; repeat split; reflexivity).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        (eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; repeat split; reflexivity).
    - destruct dv; try apply memM_interp_prov_raiseUB_l;
        destruct t2; try apply memM_interp_prov_raiseUB_l;
        (eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |];
         intros r _ <-; repeat split; reflexivity).
    - apply memM_interp_prov_raise_both.
  Qed.

  Lemma map_monad_convert_impure_base_id_sync
    (ct : impure_conversion) (t1 t2 : dtyp_base) (elts : list (@dvalue_base (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ1)
      (memM_interp_prov (map_monad (fun v => convert_impure_base ct t1 v t2) elts) σ2).
  Proof using.
    induction elts as [| v vs IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_id_sync |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma convert_impure_id_sync
    (ct : impure_conversion) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (σ1 σ2 : state) :
    refine_prov (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2) U
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ1)
      (memM_interp_prov (convert_impure ct t_from dv t_to) σ2).
  Proof using.
    unfold convert_impure.
    destruct dv as [db | | vec elts].
    - destruct (get_base_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      unfold Functor.fmap, Functor_Monad.
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply convert_impure_base_id_sync |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
    - apply memM_interp_prov_raise_both.
    - destruct vec; [| apply memM_interp_prov_raise_both].
      destruct (get_vector_conversion_type t_from t_to) as [[t1 t2] |];
        [| apply memM_interp_prov_raise_both].
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind.
      + eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
        intros elts' _ <-; repeat split; reflexivity.
      + intros U1 [σ1' elts1'] [σ2' elts2'] (-> & -> & -> & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
        eapply refine_prov_bind; [apply map_monad_convert_impure_base_id_sync |].
        intros U2 [σ1'' vs1] [σ2'' vs2] (-> & -> & -> & <-).
        apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  (** Updating a single ghost slot [gs] in [G] (uniquely identified by [gs_pr]). *)
  Definition gs_set_val (gs : ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) : ghost_slot :=
    {| gs_pt    := gs_pt gs;
       gs_ptrs  := gs_ptrs gs;
       gs_pr    := gs_pr gs;
       gs_dt    := gs_dt gs;
       gs_db    := db';
       gs_bytes := bs' |}.

  Fixpoint update_ghost_slot (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) : list ghost_slot :=
    match G with
    | [] => []
    | gs :: G' =>
        if N.eqb (gs_pr gs) pr then gs_set_val gs db' bs' :: G'
        else gs :: update_ghost_slot G' pr db' bs'
    end.

  Lemma map_gs_pr_update_ghost_slot (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    List.map gs_pr (update_ghost_slot G pr db' bs') = List.map gs_pr G.
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot List.map]; [reflexivity |].
    destruct (N.eqb (gs_pr gs) pr); cbn [List.map gs_set_val gs_pr]; [reflexivity | f_equal; exact IH].
  Qed.

  Lemma update_ghost_slot_in_range_iff (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) (z : Z) :
    (exists g', In g' (update_ghost_slot G pr db' bs') /\ gs_in_range g' z) <->
    (exists g, In g G /\ gs_in_range g z).
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot In]; [firstorder |].
    destruct (N.eqb (gs_pr gs) pr); cbn [In].
    - split.
      + intros [g' [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * exists g'; split; [right; exact Hin | exact Hr].
      + intros [g [[<- | Hin] Hr]].
        * exists (gs_set_val gs db' bs'); split; [left; reflexivity | exact Hr].
        * exists g; split; [right; exact Hin | exact Hr].
    - split.
      + intros [g' [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * destruct (proj1 IH (ex_intro _ g' (conj Hin Hr))) as [g [Hg Hrg]].
          exists g; split; [right; exact Hg | exact Hrg].
      + intros [g [[<- | Hin] Hr]].
        * exists gs; split; [left; reflexivity | exact Hr].
        * destruct (proj2 IH (ex_intro _ g (conj Hin Hr))) as [g' [Hg' Hrg']].
          exists g'; split; [right; exact Hg' | exact Hrg'].
  Qed.

  Lemma ghost_list_disjoint_update (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    ghost_list_disjoint G ->
    ghost_list_disjoint (update_ghost_slot G pr db' bs').
  Proof using.
    induction G as [| gs G' IH]; cbn [update_ghost_slot ghost_list_disjoint]; [tauto |].
    intros [Hhd Htl].
    destruct (N.eqb (gs_pr gs) pr); cbn [ghost_list_disjoint].
    - split; [intros gs' Hin z Hr; apply (Hhd gs' Hin z Hr) | exact Htl].
    - split; [| apply IH, Htl].
      intros g' Hin z Hr Hrg'.
      destruct (proj1 (update_ghost_slot_in_range_iff G' pr db' bs' z)
                  (ex_intro _ g' (conj Hin Hrg'))) as [g [Hg Hrg]].
      exact (Hhd g Hg z Hr Hrg).
  Qed.

  Lemma framestack_ghost_wf_update (G : list ghost_slot) (pr : N)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT)))
    (fs : @Framestack (@ParamsV IP IPT)) :
    framestack_ghost_wf G fs ->
    framestack_ghost_wf (update_ghost_slot G pr db' bs') fs.
  Proof using.
    intros Hfgw; induction Hfgw as [fs0 | G0 fs0 f Hsub IH Hout | gs G0 fs0 f Hsub IH Hin Hout].
    - cbn [update_ghost_slot]; apply FGW_Base.
    - apply FGW_Snoc_Unprom; [exact IH |].
      intros z Hz g' Hg' Hrg'.
      destruct (proj1 (update_ghost_slot_in_range_iff G0 pr db' bs' z)
                  (ex_intro _ g' (conj Hg' Hrg'))) as [g [Hg Hrg]].
      exact (Hout z Hz g Hg Hrg).
    - cbn [update_ghost_slot].
      destruct (N.eqb (gs_pr gs) pr).
      + apply FGW_Snoc_Prom; [exact Hsub | exact Hin | exact Hout].
      + apply FGW_Snoc_Prom; [exact IH | exact Hin |].
        intros z Hz g' Hg' Hrg'.
        destruct (proj1 (update_ghost_slot_in_range_iff G0 pr db' bs' z)
                    (ex_intro _ g' (conj Hg' Hrg'))) as [g [Hg Hrg]].
        exact (Hout z Hz g Hg Hrg).
  Qed.

  Lemma in_update_ghost_slot_nodup (G : list ghost_slot) (gs : ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT))) :
    NoDup (List.map gs_pr G) ->
    In gs G ->
    In (gs_set_val gs db' bs') (update_ghost_slot G (gs_pr gs) db' bs') /\
    (forall g',
       In g' (update_ghost_slot G (gs_pr gs) db' bs') ->
       g' = gs_set_val gs db' bs' \/ (In g' G /\ gs_pr g' <> gs_pr gs)).
  Proof using.
    induction G as [| gs0 G' IH]; intros Hnd Hin; [contradiction |].
    inversion Hnd as [| ? ? Hnin_pr Hnd']; subst.
    cbn [update_ghost_slot].
    destruct Hin as [-> | Hin].
    - rewrite N.eqb_refl; split; [left; reflexivity |].
      intros g' [<- | Hg']; [left; reflexivity | right].
      split; [right; exact Hg' |].
      intros Heq; apply Hnin_pr; rewrite <- Heq; apply in_map, Hg'.
    - assert (Hne : gs_pr gs0 <> gs_pr gs).
      { intros Heq; apply Hnin_pr; rewrite Heq; apply in_map, Hin. }
      destruct (N.eqb_spec (gs_pr gs0) (gs_pr gs)) as [Heq | _]; [contradiction |].
      destruct (IH Hnd' Hin) as [Hin_set Hinv].
      split; [right; exact Hin_set |].
      intros g' [<- | Hg'].
      + right; split; [left; reflexivity | exact Hne].
      + destruct (Hinv g' Hg') as [-> | [Hg0 Hne_g']].
        * left; reflexivity.
        * right; split; [right; exact Hg0 | exact Hne_g'].
  Qed.

  Lemma framestack_ghost_wf_add_ptrs (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    framestack_ghost_wf G (Memory_stack_frame_stack ms) ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    framestack_ghost_wf G (Memory_stack_frame_stack (add_all_to_frame ptrs ms)).
  Proof using.
    destruct ms as [mem fs h]; cbn [Memory_stack_frame_stack].
    intros Hfgw Hdisj.
    inversion Hfgw as [fs0 HeqG Heqfs | G0 fs0 f Hsub Hout HeqG Heqfs | gs G0 fs0 f Hsub Hin Hout HeqG Heqfs]; subst.
    - apply FGW_Base.
    - rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
      apply FGW_Snoc_Unprom; [exact Hsub |].
      intros z Hz gs Hgs; apply in_map_rev_app_iff in Hz as [Hz | Hz].
      + exact (Hdisj z Hz gs Hgs).
      + exact (Hout z Hz gs Hgs).
    - rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
      apply FGW_Snoc_Prom; [exact Hsub | |].
      + intros z Hr; apply in_map_rev_app_iff; right; apply Hin, Hr.
      + intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
        * exact (Hdisj z Hz gs' (or_intror Hgs')).
        * exact (Hout z Hz gs' Hgs').
  Qed.

  Lemma zip_combine_eq {X Y} (xs : list X) (ys : list Y) :
    zip_acc xs ys = List.combine xs ys.
  Proof using.
    rewrite zip_acc_eq.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'];
      cbn [zip zipWith List.combine]; try reflexivity.
    f_equal; apply IH.
  Qed.

  Lemma add_all_to_frame_fs_eq
    (ks : list (@ptr ProvenanceV (@PointerV IP)))
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    Memory_stack_frame_stack (add_all_to_frame ks ms1) =
    Memory_stack_frame_stack (add_all_to_frame ks ms2).
  Proof using.
    destruct ms1 as [m1 fs1 h1], ms2 as [m2 fs2 h2]; cbn [Memory_stack_frame_stack].
    intros ->; destruct fs2 as [f | s f].
    - rewrite !add_all_to_frame_Singleton; reflexivity.
    - rewrite !add_all_to_frame_Snoc; reflexivity.
  Qed.

  Lemma framestack_ghost_wf_unprom_inv (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f : @Frame (@ParamsV IP IPT)) :
    Forall (fun gs => gs_wf gs) G ->
    framestack_ghost_wf G (Snoc fs0 f) ->
    (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    framestack_ghost_wf G fs0.
  Proof using.
    intros Hall Hfgw Hout.
    inversion Hfgw as [fs1 HeqG HeqS | G0 fs1 f1 Hsub _ HeqG HeqS | gs G0 fs1 f1 Hsub Hin _ HeqG HeqS]; subst.
    - apply FGW_Base.
    - exact Hsub.
    - exfalso; inversion Hall as [| ? ? Hwf _]; subst.
      destruct Hwf as (Hsc & _).
      pose proof (scalar_store_size_pos (gs_dt gs) Hsc) as Hpos.
      assert (Hr : gs_in_range gs (gs_addr gs)) by (unfold gs_in_range, gs_len; lia).
      exact (Hout (gs_addr gs) (Hin (gs_addr gs) Hr) gs (or_introl Logic.eq_refl) Hr).
  Qed.

  Lemma framestack_ghost_wf_prom_inv (gs : ghost_slot) (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f : @Frame (@ParamsV IP IPT)) :
    gs_wf gs ->
    framestack_ghost_wf (gs :: G) (Snoc fs0 f) ->
    (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) ->
    framestack_ghost_wf G fs0.
  Proof using.
    intros Hwf Hfgw Hin.
    inversion Hfgw as [| G0 fs1 f1 Hsub Hout HeqG HeqS | gs' G0 fs1 f1 Hsub _ _ HeqG HeqS]; subst.
    - exfalso; destruct Hwf as (Hsc & _).
      pose proof (scalar_store_size_pos (gs_dt gs) Hsc) as Hpos.
      assert (Hr : gs_in_range gs (gs_addr gs)) by (unfold gs_in_range, gs_len; lia).
      exact (Hout (gs_addr gs) (Hin (gs_addr gs) Hr) gs (or_introl Logic.eq_refl) Hr).
    - exact Hsub.
  Qed.

  Definition top_frame_unprom_from
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ms : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    exists f,
      Memory_stack_frame_stack ms = Snoc fs0 f /\
      (forall z, In z (List.map ptr_to_int f) -> forall gs, In gs G -> ~ gs_in_range gs z).

  Definition top_frame_prom_from
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ms : @Memory_stack (@ParamsV IP IPT)) : Prop :=
    exists f,
      Memory_stack_frame_stack ms = Snoc fs0 f /\
      (forall z, gs_in_range gs z -> In z (List.map ptr_to_int f)) /\
      (forall z, In z (List.map ptr_to_int f) -> forall gs', In gs' G -> ~ gs_in_range gs' z).

  Lemma top_frame_prom_set_val
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (db' : @dvalue_base (@ParamsV IP IPT))
    (bs' : list (@memory_byte (@ParamsV IP IPT)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_prom_from fs0 gs G ms ->
    top_frame_prom_from fs0 (gs_set_val gs db' bs') G ms.
  Proof using.
    intros (f & Hfs & Hin & Hout).
    exists f; split; [exact Hfs | split; [exact Hin | exact Hout]].
  Qed.

  Lemma top_frame_unprom_add_ptrs
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_unprom_from fs0 G ms ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) ->
    top_frame_unprom_from fs0 G (add_all_to_frame ptrs ms).
  Proof using.
    destruct ms as [mem fs h]; cbn [Memory_stack_frame_stack].
    intros (f & -> & Hout) Hdisj.
    rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
    exists (rev ptrs ++ f); split; [reflexivity |].
    intros z Hz gs Hgs; apply in_map_rev_app_iff in Hz as [Hz | Hz].
    - exact (Hdisj z Hz gs Hgs).
    - exact (Hout z Hz gs Hgs).
  Qed.

  Lemma top_frame_prom_add_ptrs
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (ms : @Memory_stack (@ParamsV IP IPT)) :
    top_frame_prom_from fs0 gs G ms ->
    (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 (gs :: G) -> ~ gs_in_range gs0 z) ->
    top_frame_prom_from fs0 gs G (add_all_to_frame ptrs ms).
  Proof using.
    destruct ms as [mem fs h]; cbn [Memory_stack_frame_stack].
    intros (f & -> & Hin & Hout) Hdisj.
    rewrite add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
    exists (rev ptrs ++ f); split; [reflexivity | split].
    - intros z Hr; apply in_map_rev_app_iff; right; apply Hin, Hr.
    - intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
      + exact (Hdisj z Hz gs' (or_intror Hgs')).
      + exact (Hout z Hz gs' Hgs').
  Qed.

  Lemma stage1_mempush (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         top_frame_unprom_from (Memory_stack_frame_stack (state_memory_stack σ2)) G (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM MemPush) σ1)
      (memM_interp_prov (handle_memoryM MemPush) σ2).
  Proof using.
    intros (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    cbn [handle_memoryM mempush MemoryModelPrimitivesV].
    unfold Mempush, app_frame_stack, get, put, push_frame_stack, initial_frame;
      cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn.
    - exact Hpu.
    - exact Hnd.
    - exact Hall.
    - exact Hdisj.
    - apply FGW_Snoc_Unprom; [exact Hfgw | intros z []].
    - congruence.
    - exact Hh.
    - exact Hout.
    - exact Hgs.
    - exists []; split; [reflexivity | intros z []].
  Qed.

  Lemma stage1_alloca_unprom (dt : dtyp) (num : N) (align : option N)
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists pr ptrs,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = r2 /\
           is_safe_ptr_dvalue (pr :: P_unprom) r2 /\
           stage1_mem_inv (pr :: U) (pr :: P_unprom) G σ1' σ2' /\
           (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
           Memory_stack_frame_stack (state_memory_stack σ2') =
             Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack σ2)))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ2).
  Proof using.
    intros Hinv.
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    unfold allocate_dtyp.
    destruct (dtyp_eqb dt DTYPE_Void).
    { eapply refine_prov_obs_eq;
        [symmetry; unfold mub; cbn [MemoryModelStateV]; reflexivity | reflexivity |].
      unfold Mub; cbn [memM_interp_prov].
      eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity. }
    set (bs := concat_acc (repeatN num (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind; cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind; cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
        rewrite !Eqit.bind_bind; reflexivity |].
    apply refine_prov_trigger_fresh_both; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind;
        cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov];
        rewrite !Eqit.bind_bind; reflexivity |].
    rewrite (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) al).
    set (sz := ListUtil.N.length bs).
    destruct (int_to_ptr addr (allocation_id_to_prov (provenance_to_allocation_id pr)))
      as [s | s | s | pt] eqn:Ept;
      cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - destruct (get_consecutive_ptrs pt sz) as [s | s | s | ptrs] eqn:Eptrs;
        cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l;
            cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV];
            rewrite !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret.
        destruct (int_to_ptr_spec addr (Some [pr]) pt Ept) as [Hpt_int Hpt_pr].
        pose proof (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv) as Hnk_eq.
        assert (Hsz_nat : N.to_nat sz = List.length bs).
        { unfold sz; rewrite N_length_eq, Nat2N.id; reflexivity. }
        assert (Hptrs_disj : forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z).
        { intros z Hz gs Hgs.
          apply (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs) in Hz.
          rewrite Hpt_int in Hz.
          eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al z Hinv); [| exact Hgs].
          rewrite Hnk_eq; fold addr; lia. }
        pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
        exists pr, ptrs.
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [apply fresh_ptr_safe_dvalue, Hpt_pr |].
        set (mbs := memory_bytes_to_bytes (provenance_to_allocation_id pr) bs).
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        split.
        * split.
          { intros x [<- | Hx]; [left; reflexivity | right; apply Hpu, Hx]. }
          split; [exact Hnd |].
          split.
          { eapply Forall_impl; [| exact Hall].
            intros gs (Hwf & HinU & HninP).
            split; [exact Hwf | split; [right; exact HinU |]].
            intros [Heq | HinP]; [subst pr; exact (Hpr HinU) | exact (HninP HinP)]. }
          split; [exact Hdisj |].
          split.
          { cbn [state_memory_stack].
            set (ms2_mid := {| Memory_stack_memory := IntMaps.add_all_index_acc mbs (ptr_to_int pt)
                                                        (Memory_stack_memory (state_memory_stack σ2));
                               Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ2);
                               Memory_stack_heap := Memory_stack_heap (state_memory_stack σ2) |}).
            apply (framestack_ghost_wf_add_ptrs G ptrs ms2_mid);
              [cbn; exact Hfgw | exact Hptrs_disj]. }
          split.
          { cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; cbn; exact Hfs. }
          split.
          { cbn [state_memory_stack].
            assert (Hheap : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                      Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
            { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
              destruct fss; apply IH. }
            rewrite !Hheap; cbn; exact Hh. }
          assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                    Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
          { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
            destruct fss; apply IH. }
          split.
          { intros z Hz_out; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            destruct (Z_le_gt_dec (ptr_to_int pt) z) as [Hlo | Hgt].
            - destruct (Z_lt_ge_dec z (ptr_to_int pt + Z.of_nat (List.length mbs))) as [Hhi | Hge].
              + set (k := Z.to_nat (z - ptr_to_int pt)).
                assert (Hk : (k < List.length mbs)%nat) by lia.
                destruct (nth_error_Some mbs k) as [_ Hsome].
                destruct (nth_error mbs k) as [v |] eqn:Enth;
                  [| exfalso; apply Hsome; [exact Hk | reflexivity]].
                erewrite !lookup_add_all_index_acc_in; try exact Enth; try lia; reflexivity.
              + rewrite !lookup_add_all_index_acc_out by lia; apply Hout, Hz_out.
            - rewrite !lookup_add_all_index_acc_out by lia; apply Hout, Hz_out. }
          { intros gs k mb Hin_gs Enth; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            pose proof Hall as Hall'.
            rewrite Forall_forall in Hall'.
            destruct (Hall' gs Hin_gs) as [(Hsc & _ & _ & _ & Hlen_gs & _) _].
            pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
            assert (Hk : (k < List.length (gs_bytes gs))%nat).
            { apply Hsome; rewrite Enth; discriminate. }
            assert (Hr_z : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z).
            { unfold gs_in_range; lia. }
            assert (Hlt_addr : (gs_addr gs + Z.of_nat k < ptr_to_int pt)%Z).
            { destruct (Z_lt_ge_dec (gs_addr gs + Z.of_nat k) (ptr_to_int pt)) as [Hlt | Hge]; [exact Hlt |].
              exfalso; eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al _ Hinv);
                [rewrite Hnk_eq; fold addr; lia | exact Hin_gs | exact Hr_z]. }
            rewrite !lookup_add_all_index_acc_out by lia.
            apply (Hgs gs k mb Hin_gs Enth). }
        * split; [exact Hptrs_disj |].
          cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; reflexivity.
  Qed.

  Lemma stage1_alloca_prom (dt : dtyp) (align : option N)
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    is_scalar_dtyp dt = true ->
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    top_frame_unprom_from fs0 G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists gs0,
           ~ In (gs_pr gs0) U /\
           U' = gs_pr gs0 :: U /\
           gs_dt gs0 = dt /\
           gs_db gs0 = DVALUE_Poison /\
           r1 = DVALUE_Base (DVALUE_Pointer (gs_pt gs0)) /\
           r2 = DVALUE_Base (DVALUE_Pointer (gs_pt gs0)) /\
           stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
           top_frame_prom_from fs0 gs0 G (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ2).
  Proof using.
    intros Hsc Hinv Htop.
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    unfold allocate_dtyp.
    rewrite (scalar_dtyp_not_void dt Hsc).
    set (bs := concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind; cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite memM_interp_prov_bind; cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
        rewrite !Eqit.bind_bind; reflexivity |].
    apply refine_prov_trigger_fresh_both; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov];
       rewrite !Eqit.bind_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind;
        cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov];
        rewrite !Eqit.bind_bind; reflexivity |].
    rewrite (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv).
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ2)) al).
    set (sz := ListUtil.N.length bs).
    destruct (int_to_ptr addr (allocation_id_to_prov (provenance_to_allocation_id pr)))
      as [s | s | s | pt] eqn:Ept;
      cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - destruct (get_consecutive_ptrs pt sz) as [s | s | s | ptrs] eqn:Eptrs;
        cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l;
            cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV];
            rewrite !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret.
        destruct (int_to_ptr_spec addr (Some [pr]) pt Ept) as [Hpt_int Hpt_pr].
        pose proof (stage1_mem_next_key_eq U P_unprom G σ1 σ2 al Hinv) as Hnk_eq.
        assert (Hbs_eq : bs = List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                                (N.to_nat (@store_size_dtyp SizeofV dt))).
        { unfold bs; apply alloc_poison_bytes_eq. }
        assert (Hbs_len : List.length bs = N.to_nat (@store_size_dtyp SizeofV dt)).
        { rewrite Hbs_eq, repeat_length; reflexivity. }
        assert (Hsz_eq : sz = @store_size_dtyp SizeofV dt).
        { unfold sz; rewrite N_length_eq, Hbs_len, N2Nat.id; reflexivity. }
        destruct (is_scalar_dtyp_inv dt Hsc) as [dtb Hdt_eq].
        set (gs0 := {| gs_pt := pt;
                       gs_ptrs := ptrs;
                       gs_pr := pr;
                       gs_dt := dt;
                       gs_db := DVALUE_Poison;
                       gs_bytes := bs |}).
        assert (Hwf0 : gs_wf gs0).
        { repeat split; cbn [gs_pt gs_ptrs gs_pr gs_dt gs_db gs_bytes].
          - exact Hsc.
          - exact Hpt_pr.
          - rewrite <- Hsz_eq; exact Eptrs.
          - rewrite Hdt_eq, dvalue_to_memory_bytes_poison_base, <- Hdt_eq, <- Hbs_eq; reflexivity.
          - unfold gs_len; cbn [gs_dt]; exact Hbs_len.
          - unfold gs_addr; cbn [gs_pt]; rewrite Hpt_int; unfold addr; apply next_key_with_alignment_pos. }
        pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
        destruct Htop as (f & Hfs_top & Hout_f).
        assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
        { eapply (framestack_ghost_wf_unprom_inv G fs0 f);
            [eapply Forall_impl; [intros g [Hw _]; exact Hw | exact Hall]
            | rewrite <- Hfs_top; exact Hfgw
            | exact Hout_f]. }
        assert (Hptrs_in : forall z, In z (List.map ptr_to_int ptrs) <-> gs_in_range gs0 z).
        { intros z; rewrite (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs).
          unfold gs_in_range, gs_addr, gs_len; cbn [gs_pt gs_dt]; rewrite Hsz_eq; reflexivity. }
        assert (Hgs0_disj : forall gs', In gs' G -> gs_disjoint gs0 gs').
        { intros gs' Hgs' z Hr0.
          unfold gs_in_range, gs_addr in Hr0; cbn [gs_pt] in Hr0.
          eapply (stage1_gs_fresh_above_next_key U P_unprom G σ1 σ2 al z Hinv); [| exact Hgs'].
          rewrite Hnk_eq; fold addr; lia. }
        set (mbs := memory_bytes_to_bytes (provenance_to_allocation_id pr) bs).
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        exists gs0; cbn [gs_pr gs_dt gs_db gs_pt].
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split.
        * split; [intros x Hx; right; apply Hpu, Hx |].
          split.
          { cbn [List.map]; constructor; [| exact Hnd].
            intros Hin_map; apply in_map_iff in Hin_map as (gs' & Heq_pr & Hin_gs').
            rewrite Forall_forall in Hall.
            destruct (Hall gs' Hin_gs') as (_ & HinU & _).
            rewrite Heq_pr in HinU; exact (Hpr HinU). }
          split.
          { constructor.
            - split; [exact Hwf0 | split; [left; reflexivity | intros Hp; exact (Hpr (Hpu pr Hp))]].
            - eapply Forall_impl; [| exact Hall].
              intros gs' (Hw & Hu & Hnp); exact (conj Hw (conj (or_intror Hu) Hnp)). }
          split; [split; [exact Hgs0_disj | exact Hdisj] |].
          split.
          { cbn [state_memory_stack]; rewrite Hfs_top, add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
            apply FGW_Snoc_Prom; [exact Hfgw_fs0 | |].
            - intros z Hr; apply in_map_rev_app_iff; left; apply Hptrs_in, Hr.
            - intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
              + apply Hptrs_in in Hz; exact (Hgs0_disj gs' Hgs' z Hz).
              + exact (Hout_f z Hz gs' Hgs'). }
          split.
          { cbn [state_memory_stack]; apply add_all_to_frame_fs_eq; cbn; exact Hfs. }
          split.
          { cbn [state_memory_stack].
            assert (Hheap : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                      Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
            { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
              destruct fss; apply IH. }
            rewrite !Hheap; cbn; exact Hh. }
          split.
          { intros z Hz_out; cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            assert (Hout0 : ~ gs_in_range gs0 z) by (apply Hz_out; left; reflexivity).
            unfold gs_in_range, gs_addr, gs_len in Hout0; cbn [gs_pt gs_dt] in Hout0.
            rewrite !lookup_add_all_index_acc_out by lia.
            apply Hout; intros gs' Hgs'; apply Hz_out; right; exact Hgs'. }
          { intros gs' k mb [<- | Hin_gs'] Enth;
              cbn [state_memory_stack]; rewrite !Hmem_frame; cbn [Memory_stack_memory].
            - cbn [gs_bytes] in Enth.
              pose proof (nth_error_In bs k Enth) as Hin_bs.
              rewrite Hbs_eq in Hin_bs; apply repeat_spec in Hin_bs; subst mb.
              assert (Enth_mbs : nth_error mbs k = Some (poison_memory_byte, Some pr)).
              { unfold mbs; rewrite memory_bytes_to_bytes_eq, nth_error_map, Enth; reflexivity. }
              split; eapply lookup_add_all_index_acc_in; try exact Enth_mbs; reflexivity.
            - pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
              destruct (Hall' gs' Hin_gs') as [(_ & _ & _ & _ & Hlen_gs' & _) _].
              pose proof (nth_error_Some (gs_bytes gs') k) as [Hsome _].
              assert (Hk : (k < List.length (gs_bytes gs'))%nat) by (apply Hsome; rewrite Enth; discriminate).
              assert (Hr_gs' : gs_in_range gs' (gs_addr gs' + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
              assert (Hn0 : ~ gs_in_range gs0 (gs_addr gs' + Z.of_nat k)%Z).
              { intros Hr0; exact (Hgs0_disj gs' Hin_gs' _ Hr0 Hr_gs'). }
              unfold gs_in_range, gs_addr, gs_len in Hn0; cbn [gs_pt gs_dt] in Hn0.
              rewrite !lookup_add_all_index_acc_out by lia.
              apply (Hgs gs' k mb Hin_gs' Enth). }
        * cbn [state_memory_stack]; rewrite Hfs_top, add_all_to_frame_Snoc; cbn [Memory_stack_frame_stack].
          exists (rev ptrs ++ f); split; [reflexivity | split].
          -- intros z Hr; apply in_map_rev_app_iff; left; apply Hptrs_in, Hr.
          -- intros z Hz gs' Hgs'; apply in_map_rev_app_iff in Hz as [Hz | Hz].
             ++ apply Hptrs_in in Hz; exact (Hgs0_disj gs' Hgs' z Hz).
             ++ exact (Hout_f z Hz gs' Hgs').
  Qed.

  Lemma Read_byte_hit_eq (q : @ptr ProvenanceV (@PointerV IP))
    (mb : @memory_byte (@ParamsV IP IPT)) (pr : N) (σ : state)
    (Hpr : ptr_provenance q = Some [pr])
    (Hlk : IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)) = Some (mb, Some pr)) :
    memM_interp_prov (Read_byte q) σ ≅ Ret (σ, mb).
  Proof using.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    rewrite memM_interp_prov_bind.
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ))).
    rewrite Hlk, Eqit.bind_ret_l, Hpr.
    cbn [access_allowed ProvenanceV existsb]; rewrite N.eqb_refl; cbn; reflexivity.
  Qed.

  Lemma map_monad_Read_gs_bytes_eq
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (base : Z) (j : nat) (pr : N) (σ : state)
    (Hlen : List.length ptrs = List.length bs)
    (Hptrs : forall i q,
               nth_error ptrs i = Some q ->
               ptr_to_int q = (base + Z.of_nat (j + i))%Z /\
               ptr_provenance q = Some [pr])
    (Hmem : forall i mb,
              nth_error bs i = Some mb ->
              IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ)) =
                Some (mb, Some pr)) :
    memM_interp_prov (map_monad Read_byte ptrs) σ ≅ Ret (σ, bs).
  Proof using.
    revert bs j Hlen Hptrs Hmem; induction ptrs as [| q ptrs' IH]; intros [| mb bs'] j Hlen Hptrs Hmem;
      cbn [List.length map_monad] in *; try lia.
    - reflexivity.
    - destruct (Hptrs 0%nat q Logic.eq_refl) as [Hq_int Hq_pr].
      pose proof (Hmem 0%nat mb Logic.eq_refl) as Hlk0.
      replace (j + 0)%nat with j in Hq_int, Hlk0 by lia.
      rewrite <- Hq_int in Hlk0.
      rewrite memM_interp_prov_bind, (Read_byte_hit_eq q mb pr σ Hq_pr Hlk0), Eqit.bind_ret_l.
      rewrite memM_interp_prov_bind.
      rewrite (IH bs' (S j) ltac:(lia)); [rewrite Eqit.bind_ret_l; reflexivity | |].
      + intros i q' Hnth; destruct (Hptrs (S i) q' Hnth) as [Hi Hpr']; split; [lia | exact Hpr'].
      + intros i mb' Hnth; pose proof (Hmem (S i) mb' Hnth) as Hlk';
          replace (j + S i)%nat with (S j + i)%nat in Hlk' by lia; exact Hlk'.
  Qed.

  Lemma stage1_load_prom (U P_unprom : list N) (G : list ghost_slot)
    (gs : ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))) σ1)
      (memM_interp_prov (Interfaces.Memory.lift (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))) σ2).
  Proof using.
    intros Hinv Hin.
    pose proof Hinv as (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs).
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [(_ & Hpr & Eptrs & _ & Hlen_bs & _) _].
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (Hlen_ptrs & Hinv_ptrs & _).
    cbn [handle_memoryM]; unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq.
    - symmetry.
      rewrite memM_interp_prov_bind, memM_interp_prov_bind, Eptrs.
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov read_byte MemoryModelPrimitivesV].
      rewrite Eqit.bind_ret_l, memM_interp_prov_map_monad_acc.
      rewrite (map_monad_Read_gs_bytes_eq (gs_ptrs gs) (gs_bytes gs) (gs_addr gs) 0%nat (gs_pr gs) σ1).
      + rewrite Eqit.bind_ret_l; reflexivity.
      + unfold gs_len in Hlen_bs; lia.
      + intros i q Hnth; destruct (Hinv_ptrs i q Hnth) as (_ & Hqi & Hqpr).
        rewrite Hpr in Hqpr; unfold gs_addr; split; [lia | exact Hqpr].
      + intros i mb Hnth; destruct (Hgs gs i mb Hin Hnth) as [Hlk1 _]; exact Hlk1.
    - reflexivity.
    - eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma Write_byte_hit_eq (q : @ptr ProvenanceV (@PointerV IP))
    (mb0 mb : @memory_byte (@ParamsV IP IPT)) (pr : N) (σ : state)
    (Hpr : ptr_provenance q = Some [pr])
    (Hlk : IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)) = Some (mb0, Some pr)) :
    memM_interp_prov (Write_byte q mb) σ ≅
    Ret ({| state_memory_stack :=
              {| Memory_stack_memory :=
                   IntMaps.add (ptr_to_int q) (mb, Some pr) (Memory_stack_memory (state_memory_stack σ));
                 Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ);
                 Memory_stack_heap := Memory_stack_heap (state_memory_stack σ) |};
            state_provenance := state_provenance σ |}, tt).
  Proof using.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    rewrite memM_interp_prov_bind.
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ))).
    rewrite Hlk, Eqit.bind_ret_l, Hpr.
    cbn [access_allowed ProvenanceV existsb]; rewrite N.eqb_refl; cbn [orb].
    unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
      cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    reflexivity.
  Qed.

  Lemma loop_Write_gs_bytes_spec
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (base : Z) (j : nat) (pr : N) (σ : state)
    (Hlen : List.length ptrs = List.length bs)
    (Hptrs : forall i q,
               nth_error ptrs i = Some q ->
               ptr_to_int q = (base + Z.of_nat (j + i))%Z /\
               ptr_provenance q = Some [pr])
    (Hmem : forall i,
              (i < List.length bs)%nat ->
              exists mb0,
                IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ)) =
                  Some (mb0, Some pr)) :
    exists σ',
      memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) (List.combine ptrs bs)) σ ≅
        Ret (σ', tt) /\
      Memory_stack_frame_stack (state_memory_stack σ') = Memory_stack_frame_stack (state_memory_stack σ) /\
      Memory_stack_heap (state_memory_stack σ') = Memory_stack_heap (state_memory_stack σ) /\
      (forall i mb,
         nth_error bs i = Some mb ->
         IntMaps.lookup (base + Z.of_nat (j + i))%Z (Memory_stack_memory (state_memory_stack σ')) =
           Some (mb, Some pr)) /\
      (forall z,
         ~ (base + Z.of_nat j <= z < base + Z.of_nat (j + List.length bs))%Z ->
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ')) =
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ))).
  Proof using.
    revert bs j σ Hlen Hptrs Hmem;
      induction ptrs as [| q ptrs' IH];
      intros [| mb bs'] j σ Hlen Hptrs Hmem;
      cbn [List.length List.combine loop_monad] in *; try lia.
    - exists σ; repeat split; try reflexivity.
      intros [| i] mb Hnth; discriminate Hnth.
    - destruct (Hptrs 0%nat q Logic.eq_refl) as [Hq_int Hq_pr].
      destruct (Hmem 0%nat ltac:(lia)) as [mb0 Hlk0].
      replace (j + 0)%nat with j in Hq_int, Hlk0 by lia.
      rewrite <- Hq_int in Hlk0.
      set (σ_mid := {| state_memory_stack :=
                         {| Memory_stack_memory :=
                              IntMaps.add (ptr_to_int q) (mb, Some pr) (Memory_stack_memory (state_memory_stack σ));
                            Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ);
                            Memory_stack_heap := Memory_stack_heap (state_memory_stack σ) |};
                       state_provenance := state_provenance σ |}).
      assert (Hptrs' : forall i q',
                 nth_error ptrs' i = Some q' ->
                 ptr_to_int q' = (base + Z.of_nat (S j + i))%Z /\
                 ptr_provenance q' = Some [pr]).
      { intros i q' Hnth; destruct (Hptrs (S i) q' Hnth) as [Hi Hpr']; split; [lia | exact Hpr']. }
      assert (Hmem' : forall i,
                 (i < List.length bs')%nat ->
                 exists mb1,
                   IntMaps.lookup (base + Z.of_nat (S j + i))%Z (Memory_stack_memory (state_memory_stack σ_mid)) =
                     Some (mb1, Some pr)).
      { intros i Hi; cbn [state_memory_stack Memory_stack_memory σ_mid].
        rewrite IntMaps.lookup_add_ineq by lia.
        destruct (Hmem (S i) ltac:(lia)) as [mb1 Hlk1].
        replace (j + S i)%nat with (S j + i)%nat in Hlk1 by lia; exists mb1; exact Hlk1. }
      destruct (IH bs' (S j) σ_mid ltac:(lia) Hptrs' Hmem')
        as (σ' & Heq_tl & Hfs' & Hh' & Hin' & Hout').
      exists σ'; split.
      + rewrite memM_interp_prov_bind, (Write_byte_hit_eq q mb0 mb pr σ Hq_pr Hlk0), Eqit.bind_ret_l.
        exact Heq_tl.
      + split; [exact Hfs' | split; [exact Hh' | split]].
        * intros [| i] mb1 Hnth; cbn [nth_error] in Hnth.
          -- inversion Hnth; subst mb1.
             replace (j + 0)%nat with j by lia.
             rewrite (Hout' (base + Z.of_nat j)%Z ltac:(lia)).
             cbn [state_memory_stack Memory_stack_memory σ_mid].
             rewrite Hq_int; apply IntMaps.lookup_add_eq.
          -- replace (j + S i)%nat with (S j + i)%nat by lia.
             apply (Hin' i mb1 Hnth).
        * intros z Hz.
          rewrite (Hout' z ltac:(lia)).
          cbn [state_memory_stack Memory_stack_memory σ_mid].
          apply IntMaps.lookup_add_ineq; lia.
  Qed.

  Lemma stage1_store_prom_base (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (fs0 : @Framestack (@ParamsV IP IPT))
    (db' : @dvalue_base (@ParamsV IP IPT)) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom (gs :: G) σ1 σ2 ->
    top_frame_prom_from fs0 gs G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists bs',
           U' = U /\ r1 = tt /\ r2 = tt /\
           dvalue_to_memory_bytes (gs_dt gs) (DVALUE_Base db') None = raise_ret bs' /\
           stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
           top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2))
      U
      (memM_interp_prov (handle_memoryM (Store (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) (DVALUE_Base db'))) σ1)
      (Ret (σ2, tt)).
  Proof using.
    intros Hinv Htop.
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    inversion Hall as [| ? ? (Hwf & HinU & HninP) Hall_tl]; subst.
    destruct Hwf as (Hsc & Hpr & Eptrs & _ & Hlen_old & Hpos_addr).
    destruct (is_scalar_dtyp_inv (gs_dt gs) Hsc) as [dtb Hdt_eq].
    destruct (dvalue_to_memory_bytes_base_ok dtb db') as (bs' & Hser & Hlen_bs').
    rewrite <- Hdt_eq in Hser, Hlen_bs'.
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (Hlen_ptrs & Hinv_ptrs & _).
    assert (Hsz_bs' : ListUtil.N.length bs' = @store_size_dtyp SizeofV (gs_dt gs)).
    { rewrite N_length_eq, Hlen_bs', N2Nat.id; reflexivity. }
    assert (Hmem_pre : forall i,
               (i < List.length bs')%nat ->
               exists mb0,
                 IntMaps.lookup (gs_addr gs + Z.of_nat (0 + i))%Z (Memory_stack_memory (state_memory_stack σ1)) =
                   Some (mb0, Some (gs_pr gs))).
    { intros i Hi.
      assert (Hi_old : (i < List.length (gs_bytes gs))%nat) by (unfold gs_len in Hlen_old; lia).
      destruct (nth_error_Some (gs_bytes gs) i) as [_ Hsome].
      destruct (nth_error (gs_bytes gs) i) as [mb0 |] eqn:Enth0;
        [| exfalso; apply Hsome; [exact Hi_old | reflexivity]].
      destruct (Hgs gs i mb0 (or_introl Logic.eq_refl) Enth0) as [Hlk1 _].
      exists mb0; exact Hlk1. }
    destruct (loop_Write_gs_bytes_spec (gs_ptrs gs) bs' (gs_addr gs) 0%nat (gs_pr gs) σ1
                ltac:(lia)
                (fun i q Hnth =>
                   match Hinv_ptrs i q Hnth with
                   | conj _ (conj Hqi Hqp) => conj ltac:(unfold gs_addr; lia) ltac:(congruence)
                   end)
                Hmem_pre)
      as (σ1' & Hloop_eq & Hfs' & Hh' & Hin' & Hout').
    cbn [handle_memoryM]; unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq.
    - symmetry.
      rewrite memM_interp_prov_bind, Hser; cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
      rewrite Eqit.bind_ret_l, memM_interp_prov_bind, Hsz_bs', Eptrs.
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov write_byte MemoryModelPrimitivesV].
      rewrite Eqit.bind_ret_l, zip_combine_eq, Hloop_eq; reflexivity.
    - reflexivity.
    - apply refine_prov_ret.
      exists bs'; split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hser |]]]].
      destruct Hdisj as [Hdisj_hd Hdisj_tl].
      split; [| apply top_frame_prom_set_val, Htop].
      split; [exact Hpu |].
      split; [exact Hnd |].
      split.
      + constructor.
        * split; [| exact (conj HinU HninP)].
          repeat split; cbn [gs_set_val gs_dt gs_pt gs_pr gs_ptrs gs_db gs_bytes];
            try assumption; unfold gs_len; cbn [gs_dt]; exact Hlen_bs'.
        * exact Hall_tl.
      + split; [exact (conj Hdisj_hd Hdisj_tl) |].
        split.
        * inversion Hfgw as [| G0 fs1 f1 Hsub Hout_f HeqG HeqS | gs1 G0 fs1 f1 Hsub Hin_f Hout_f HeqG HeqS]; subst.
          -- apply FGW_Snoc_Unprom; [exact Hsub | exact Hout_f].
          -- apply FGW_Snoc_Prom; [exact Hsub | exact Hin_f | exact Hout_f].
        * split; [congruence | split; [congruence | split]].
          -- intros z Hz_out.
             assert (Hn0 : ~ gs_in_range gs z).
             { intros Hr; exact (Hz_out (gs_set_val gs db' bs') (or_introl Logic.eq_refl) Hr). }
             unfold gs_in_range, gs_len in Hn0.
             rewrite (Hout' z ltac:(lia)).
             apply Hout; intros g0 [<- | Hg0];
               [exact Hn0 | apply Hz_out; right; exact Hg0].
          -- intros g0 k mb [<- | Hg0] Enth.
             ++ cbn [gs_set_val gs_bytes gs_pr] in *.
                split; [exact (Hin' k mb Enth) |].
                pose proof (nth_error_Some bs' k) as [Hsome _].
                assert (Hk : (k < List.length bs')%nat) by (apply Hsome; rewrite Enth; discriminate).
                assert (Hk_old : (k < List.length (gs_bytes gs))%nat) by (unfold gs_len in Hlen_old; lia).
                destruct (nth_error_Some (gs_bytes gs) k) as [_ Hsome_old].
                destruct (nth_error (gs_bytes gs) k) as [mb_old |] eqn:Enth_old;
                  [| exfalso; apply Hsome_old; [exact Hk_old | reflexivity]].
                destruct (Hgs gs k mb_old (or_introl Logic.eq_refl) Enth_old) as [_ Hlk2].
                exact Hlk2.
             ++ pose proof Hall_tl as Hall_tl'; rewrite Forall_forall in Hall_tl'.
                destruct (Hall_tl' g0 Hg0) as [(_ & _ & _ & _ & Hlen_g0 & _) _].
                pose proof (nth_error_Some (gs_bytes g0) k) as [Hsome _].
                assert (Hk : (k < List.length (gs_bytes g0))%nat) by (apply Hsome; rewrite Enth; discriminate).
                assert (Hr_g0 : gs_in_range g0 (gs_addr g0 + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
                assert (Hn0 : ~ gs_in_range gs (gs_addr g0 + Z.of_nat k)%Z).
                { intros Hr0; exact (Hdisj_hd g0 Hg0 _ Hr0 Hr_g0). }
                unfold gs_in_range, gs_len in Hn0.
                rewrite (Hout' (gs_addr g0 + Z.of_nat k)%Z ltac:(lia)).
                exact (Hgs g0 k mb (or_intror Hg0) Enth).
  Qed.

  Lemma stage1_store_prom_err {R2}
    (RR : list N -> (state * unit) -> (state * R2) -> Prop)
    (U : list N) (gs : ghost_slot) (v : @dvalue (@ParamsV IP IPT))
    (msg2 : string) (σ1 σ2 : state) :
    is_scalar_dtyp (gs_dt gs) = true ->
    (forall db, v <> DVALUE_Base db) ->
    refine_prov RR U
      (memM_interp_prov (handle_memoryM (Store (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v)) σ1)
      (memM_interp_prov (Merr msg2) σ2).
  Proof using.
    intros Hsc Hnot_base.
    destruct (is_scalar_dtyp_inv (gs_dt gs) Hsc) as [dtb Hdt_eq].
    destruct (dvalue_to_memory_bytes_base_err dtb v Hnot_base) as [msg1 Hser].
    cbn [handle_memoryM]; unfold write_dvalue.
    rewrite Hdt_eq, Hser; cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind].
    apply memM_interp_prov_raise_both.
  Qed.

  Lemma stage1_Read_byte_unprom (q : @ptr ProvenanceV (@PointerV IP))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    safe_prov P_unprom (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros Hinv Hsafe.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb & _ & Hlk1 & _).
      pose proof Hinv as (_ & _ & Hall & _).
      rewrite Forall_forall in Hall.
      destruct (Hall gs Hin) as (_ & _ & HninP).
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      rewrite (safe_prov_access_disjoint P_unprom (ptr_provenance q) (gs_pr gs) Hsafe HninP).
      apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      rewrite (Hout (ptr_to_int q) Hout_z).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        destruct (access_allowed (ptr_provenance q) aid).
        * apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_map_monad_Read_byte_unprom
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    Forall (fun q => safe_prov P_unprom (ptr_provenance q)) ptrs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv Hall; induction Hall as [| q ptrs' Hq _ IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Read_byte_unprom q U P_unprom G σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_load_unprom (dt : dtyp) (a : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    is_safe_ptr_dvalue P_unprom a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load dt a)) σ1)
      (memM_interp_prov (handle_memoryM (Load dt a)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |];
      try apply memM_interp_prov_raiseUB_l.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    destruct (get_consecutive_ptrs pt (@store_size_dtyp SizeofV dt))
      as [s | s | s | ptrs] eqn:Eptrs;
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      assert (Hall_safe : Forall (fun q => safe_prov P_unprom (ptr_provenance q)) ptrs).
      { destruct (get_consecutive_ptrs_spec pt (@store_size_dtyp SizeofV dt) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros q Hin_q.
        apply In_nth_error in Hin_q as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q); rewrite Hpr_q; exact Hsafe. }
      eapply refine_prov_bind;
        [apply (stage1_map_monad_Read_byte_unprom ptrs U P_unprom G σ1 σ2 Hinv Hall_safe) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & -> & <-).
      eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma stage1_Write_byte_unprom
    (q : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    safe_prov P_unprom (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (Write_byte q mb) σ1)
      (memM_interp_prov (Write_byte q mb) σ2).
  Proof using.
    intros Hinv Hsafe.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb0 & _ & Hlk1 & _).
      pose proof Hinv as (_ & _ & Hall & _).
      rewrite Forall_forall in Hall.
      destruct (Hall gs Hin) as (_ & _ & HninP).
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      rewrite (safe_prov_access_disjoint P_unprom (ptr_provenance q) (gs_pr gs) Hsafe HninP).
      apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
      rewrite (Hout (ptr_to_int q) Hout_z).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b0 aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        destruct (access_allowed (ptr_provenance q) aid).
        * unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
            cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
          apply refine_prov_ret; repeat split; cbn;
            try exact Hpu; try exact Hnd; try exact Hall; try exact Hdisj;
            try exact Hfgw; try exact Hfs; try exact Hh.
          -- intros z Hz.
             destruct (Z.eq_dec (ptr_to_int q) z) as [<- | Hne].
             ++ rewrite !IntMaps.lookup_add_eq; reflexivity.
             ++ rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Hout, Hz.
          -- intros gs k mb1 Hin_gs Enth.
             pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
             destruct (Hall' gs Hin_gs) as [(_ & _ & _ & _ & Hlen_gs & _) _].
             pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
             assert (Hk : (k < List.length (gs_bytes gs))%nat) by (apply Hsome; rewrite Enth; discriminate).
             assert (Hr_gs : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
             assert (Hne : ptr_to_int q <> (gs_addr gs + Z.of_nat k)%Z).
             { intros Heq; rewrite Heq in Hout_z; exact (Hout_z gs Hin_gs Hr_gs). }
             rewrite !IntMaps.lookup_add_ineq by exact Hne.
             apply (Hgs gs k mb1 Hin_gs Enth).
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_loop_Write_byte_unprom
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    Forall (fun '(q, _) => safe_prov P_unprom (ptr_provenance q)) pbs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    intros Hinv Hall; revert σ1 σ2 Hinv;
      induction Hall as [| [q mb] pbs' Hq _ IH]; intros σ1 σ2 Hinv; cbn [loop_monad].
    - apply refine_prov_ret; repeat split; try exact Hinv; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Write_byte_unprom q mb U P_unprom G σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' []] [σ2' []] (-> & _ & _ & Hinv1 & Hfs1).
      eapply refine_prov_weaken; [apply IH, Hinv1 |].
      intros U2 [σ1'' r1] [σ2'' r2] (-> & -> & -> & Hinv2 & Hfs2).
      repeat split; [exact Hinv2 | congruence].
  Qed.

  Lemma stage1_store_unprom (dt : dtyp) (a v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    is_safe_ptr_dvalue P_unprom a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') =
           Memory_stack_frame_stack (state_memory_stack σ2))
      U
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ1)
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |];
      try apply memM_interp_prov_raiseUB_l.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    destruct (dvalue_to_memory_bytes dt v None) as [s | s | s | bs];
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
    - apply memM_interp_prov_raise_both.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity |].
      destruct (get_consecutive_ptrs pt (ListUtil.N.length bs)) as [s | s | s | ptrs] eqn:Eptrs;
        cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
      + apply memM_interp_prov_raiseOOM_l.
      + apply memM_interp_prov_raiseUB_l.
      + apply memM_interp_prov_raise_both.
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity
          | symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity |].
        cbn [write_byte MemoryModelPrimitivesV].
        apply stage1_loop_Write_byte_unprom; [exact Hinv |].
        destruct (get_consecutive_ptrs_spec pt (ListUtil.N.length bs) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros [q mb] Hin_c.
        apply in_combine_l in Hin_c.
        apply In_nth_error in Hin_c as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q); rewrite Hpr_q; exact Hsafe.
  Qed.

  Lemma stage1_Read_byte_any_ptr (q : @ptr ProvenanceV (@PointerV IP))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros Hinv.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage1_find_gs_at G (ptr_to_int q)) as [[gs [Hin Hr]] | Hout_z].
    - destruct (stage1_gs_lookup_range U P_unprom G σ1 σ2 gs (ptr_to_int q) Hinv Hin Hr)
        as (mb & _ & Hlk1 & Hlk2).
      rewrite Hlk1, Hlk2.
      eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      destruct (access_allowed (ptr_provenance q) (Some (gs_pr gs))).
      + apply refine_prov_ret; repeat split; reflexivity.
      + apply memM_interp_prov_raiseUB_l.
    - pose proof Hinv as (_ & _ & _ & _ & _ & _ & _ & Hout & _).
      rewrite (Hout (ptr_to_int q) Hout_z).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        destruct (access_allowed (ptr_provenance q) aid).
        * apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage1_map_monad_Read_byte_any_ptr
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv; induction ptrs as [| q ptrs' IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [apply (stage1_Read_byte_any_ptr q U P_unprom G σ1 σ2 Hinv) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & ->).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & ->).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_load_b8_array_any_ptr (n : N) (a : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', _) '(σ2', _) => U' = U /\ σ1' = σ1 /\ σ2' = σ2)
      U
      (memM_interp_prov (handle_memoryM (Load (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) a)) σ1)
      (memM_interp_prov (handle_memoryM (Load (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8))) a)) σ2).
  Proof using.
    intros Hinv; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |];
      try apply memM_interp_prov_raiseUB_l.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    destruct (get_consecutive_ptrs pt (@store_size_dtyp SizeofV (DTYPE_Array false n (DTYPE_Base (DTYPE_B 8)))))
      as [s | s | s | ptrs];
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      eapply refine_prov_bind;
        [apply (stage1_map_monad_Read_byte_any_ptr ptrs U P_unprom G σ1 σ2 Hinv) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & ->).
      destruct (memory_bytes_to_dvalue_b8_array_total bs1 n) as [dv1 ->].
      destruct (memory_bytes_to_dvalue_b8_array_total bs2 n) as [dv2 ->].
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage1_mempop_unprom (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    top_frame_unprom_from fs0 G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros Hinv (f & Hfs_top & Hout_f).
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
    { eapply (framestack_ghost_wf_unprom_inv G fs0 f);
        [eapply Forall_impl; [intros g [Hw _]; exact Hw | exact Hall]
        | rewrite <- Hfs_top; exact Hfgw
        | exact Hout_f]. }
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs, Hfs_top.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    cbn [pop_frame_stack Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn;
      try exact Hpu; try exact Hnd; try exact Hall; try exact Hdisj;
      try exact Hfgw_fs0; try exact Hh.
    - intros z Hz_out.
      destruct (in_dec Z.eq_dec z (List.map ptr_to_int f)) as [Hin_f | Hnin_f].
      + rewrite !lookup_free_frame_memory_in by exact Hin_f; reflexivity.
      + rewrite !lookup_free_frame_memory_out by exact Hnin_f; apply Hout, Hz_out.
    - intros gs k mb Hin_gs Enth.
      pose proof Hall as Hall'; rewrite Forall_forall in Hall'.
      destruct (Hall' gs Hin_gs) as [(_ & _ & _ & _ & Hlen_gs & _) _].
      pose proof (nth_error_Some (gs_bytes gs) k) as [Hsome _].
      assert (Hk : (k < List.length (gs_bytes gs))%nat) by (apply Hsome; rewrite Enth; discriminate).
      assert (Hr_gs : gs_in_range gs (gs_addr gs + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
      assert (Hnin_f : ~ In (gs_addr gs + Z.of_nat k)%Z (List.map ptr_to_int f)).
      { intros Hin_f; exact (Hout_f _ Hin_f gs Hin_gs Hr_gs). }
      rewrite !lookup_free_frame_memory_out by exact Hnin_f.
      apply (Hgs gs k mb Hin_gs Enth).
  Qed.

  Lemma stage1_mempop_prom (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom (gs :: G) σ1 σ2 ->
    top_frame_prom_from fs0 gs G (state_memory_stack σ2) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage1_mem_inv U P_unprom G σ1' σ2' /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros Hinv (f & Hfs_top & Hin_f & Hout_f).
    pose proof Hinv as (Hpu & Hnd & Hall & Hdisj & Hfgw & Hfs & Hh & Hout & Hgs).
    inversion Hnd as [| ? ? _ Hnd_tl]; subst.
    inversion Hall as [| ? ? (Hwf0 & _ & _) Hall_tl]; subst.
    destruct Hdisj as [_ Hdisj_tl].
    assert (Hfgw_fs0 : framestack_ghost_wf G fs0).
    { eapply (framestack_ghost_wf_prom_inv gs G fs0 f);
        [exact Hwf0 | rewrite <- Hfs_top; exact Hfgw | exact Hin_f]. }
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs, Hfs_top.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    cbn [pop_frame_stack Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn;
      try exact Hpu; try exact Hnd_tl; try exact Hall_tl; try exact Hdisj_tl;
      try exact Hfgw_fs0; try exact Hh.
    - intros z Hz_out.
      destruct (gs_in_range_dec gs z) as [Hr0 | Hnr0].
      + rewrite !lookup_free_frame_memory_in by (apply Hin_f, Hr0); reflexivity.
      + destruct (in_dec Z.eq_dec z (List.map ptr_to_int f)) as [Hzf | Hnzf].
        * rewrite !lookup_free_frame_memory_in by exact Hzf; reflexivity.
        * rewrite !lookup_free_frame_memory_out by exact Hnzf.
          apply Hout; intros g0 [<- | Hg0]; [exact Hnr0 | apply Hz_out, Hg0].
    - intros gs' k mb Hin_gs' Enth.
      pose proof Hall_tl as Hall_tl'; rewrite Forall_forall in Hall_tl'.
      destruct (Hall_tl' gs' Hin_gs') as [(_ & _ & _ & _ & Hlen_gs' & _) _].
      pose proof (nth_error_Some (gs_bytes gs') k) as [Hsome _].
      assert (Hk : (k < List.length (gs_bytes gs'))%nat) by (apply Hsome; rewrite Enth; discriminate).
      assert (Hr_gs' : gs_in_range gs' (gs_addr gs' + Z.of_nat k)%Z) by (unfold gs_in_range; lia).
      assert (Hnin_f : ~ In (gs_addr gs' + Z.of_nat k)%Z (List.map ptr_to_int f)).
      { intros Hzf; exact (Hout_f _ Hzf gs' Hin_gs' Hr_gs'). }
      rewrite !lookup_free_frame_memory_out by exact Hnin_f.
      apply (Hgs gs' k mb (or_intror Hin_gs') Enth).
  Qed.

  (** ** 3E. Stage 2 Dead-Alloca Memory Invariant & Primitive Simulation *)

  Definition stage2_in_range (base : Z) (sz : nat) (z : Z) : Prop :=
    (base <= z < base + Z.of_nat sz)%Z.

  Lemma stage2_in_range_dec (base : Z) (sz : nat) (z : Z) :
    {stage2_in_range base sz z} + {~ stage2_in_range base sz z}.
  Proof using.
    unfold stage2_in_range.
    destruct (Z_le_gt_dec base z) as [Hle | Hgt].
    - destruct (Z_lt_ge_dec z (base + Z.of_nat sz)) as [Hlt | Hge]; [left; lia | right; lia].
    - right; lia.
  Qed.

  Definition stage2_mem_inv (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) : Prop :=
    incl P_safe U /\
    In pr_dead U /\
    ~ In pr_dead P_safe /\
    Memory_stack_heap (state_memory_stack σ1) = Memory_stack_heap (state_memory_stack σ2) /\
    Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2 /\
    (exists ptrs_dead,
       (forall z, In z (List.map ptr_to_int ptrs_dead) <-> stage2_in_range base_dead sz_dead z) /\
       Memory_stack_frame_stack (state_memory_stack σ1) = Snoc fs0 (rev ptrs_dead ++ f2)) /\
    (forall z,
       stage2_in_range base_dead sz_dead z ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
         Some (poison_memory_byte, Some pr_dead) /\
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2)) = None) /\
    (forall z,
       ~ stage2_in_range base_dead sz_dead z ->
       IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ1)) =
         IntMaps.lookup z (Memory_stack_memory (state_memory_stack σ2))).

  Lemma stage2_mem_inv_incl_U (U U' P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat) (σ1 σ2 : state) :
    incl U U' ->
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    stage2_mem_inv U' P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2.
  Proof using.
    intros Hinc (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout).
    split; [eapply incl_tran; eassumption |].
    split; [apply Hinc, Hin |].
    exact (conj Hnin (conj Hh (conj Hfs2 (conj Hfs1 (conj Hrng Hout))))).
  Qed.

  Lemma stage2_alloca_dead_l {IPWB : IPtrWellBehaved IP}
    {R2} (r2 : R2)
    (dt : dtyp) (align : option N)
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (σ1 σ2 : state)
    (Hsc : is_scalar_dtyp dt = true)
    (Hpu : incl P_safe U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2))
    (Hfs2 : Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2) :
    refine_prov
      (fun U' '(σ1', r1) y2 =>
         exists pr pt,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = DVALUE_Base (DVALUE_Pointer pt) /\
           y2 = r2 /\
           stage2_mem_inv (pr :: U) P_safe fs0 f2 (ptr_to_int pt) pr
             (N.to_nat (@store_size_dtyp SizeofV dt)) σ1' σ2)
      U
      (memM_interp_prov (handle_memoryM (Alloca dt 1%N align)) σ1)
      (Ret r2).
  Proof using.
    destruct Heq as (Hm_eq & Hfs_eq & Hh_eq).
    cbn [handle_memoryM].
    set (al := match align with None => preferred_alignment (dtyp_alignment dt) | Some a => a end).
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | reflexivity |].
    unfold allocate_dtyp.
    rewrite (scalar_dtyp_not_void dt Hsc).
    set (bs := concat_acc (repeatN 1%N (@generate_poison_bytes (@ParamsV IP IPT) dt))).
    unfold allocate_bytes, fresh_prov, Mfresh_prov.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite memM_interp_prov_bind;
       cbn [Monads.ret memS_mon memM_interp_prov allocate_bytes_with_pr MemoryModelPrimitivesV];
       rewrite !Eqit.bind_bind; reflexivity
      | reflexivity |].
    apply refine_prov_trigger_fresh_l; intros pr Hpr.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity | reflexivity |].
    unfold Allocate_bytes_with_pr, get_free_block, next_key, Mnext_key.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind;
       cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov];
       rewrite !Eqit.bind_bind; reflexivity
      | reflexivity |].
    set (addr := next_key_with_alignment (Memory_stack_memory (state_memory_stack σ1)) al).
    set (sz := ListUtil.N.length bs).
    unfold int_to_ptr, PIV at 1.
    destruct (from_Z_ret_or_oom addr) as [[ip Hip] | [msg Hoom]].
    - rewrite Hip; cbn [Monads.bind Monad_either Monads.ret Interfaces.Memory.lift memS_mon memS_bind memM_interp_prov].
      set (pt := (ip, allocation_id_to_prov (provenance_to_allocation_id pr))
                 : @ptr ProvenanceV (@PointerV IP)).
      destruct (get_consecutive_ptrs_well_behaved pt sz) as [[ptrs Eptrs] | [msg Hoom]].
      + rewrite Eptrs; cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
        unfold add_block_to_stack, add_block, add_ptrs_to_frame, get_mem, upd_mem, app_mem, app_mem_stack, get, put.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l;
           cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV];
           rewrite !Eqit.bind_ret_l; reflexivity
          | reflexivity |].
        apply refine_prov_ret.
        pose proof (from_Z_to_Z addr ip Hip) as Hip_Z.
        assert (Hpt_int : ptr_to_int pt = addr) by (cbn; exact Hip_Z).
        assert (Hbs_eq : bs = List.repeat (@poison_memory_byte (@ParamsV IP IPT))
                                (N.to_nat (@store_size_dtyp SizeofV dt))).
        { unfold bs; apply alloc_poison_bytes_eq. }
        assert (Hbs_len : List.length bs = N.to_nat (@store_size_dtyp SizeofV dt)).
        { rewrite Hbs_eq, repeat_length; reflexivity. }
        assert (Hsz_eq : sz = @store_size_dtyp SizeofV dt).
        { unfold sz; rewrite N_length_eq, Hbs_len, N2Nat.id; reflexivity. }
        set (mbs := memory_bytes_to_bytes (provenance_to_allocation_id pr) bs).
        assert (Hmbs_len : List.length mbs = List.length bs).
        { unfold mbs; rewrite memory_bytes_to_bytes_eq, length_map; reflexivity. }
        assert (Hmem_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_memory (add_all_to_frame ks ms) = Memory_stack_memory ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        assert (Hheap_frame : forall ks (ms : @Memory_stack (@ParamsV IP IPT)),
                  Memory_stack_heap (add_all_to_frame ks ms) = Memory_stack_heap ms).
        { induction ks as [| k0 ks' IH]; intros [mm fss hh]; cbn; [reflexivity |].
          destruct fss; apply IH. }
        exists pr, pt.
        split; [exact Hpr |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [intros x Hx; right; apply Hpu, Hx |].
        split; [left; reflexivity |].
        split; [intros Hp; exact (Hpr (Hpu pr Hp)) |].
        split; [cbn [state_memory_stack]; rewrite Hheap_frame; cbn; exact Hh_eq |].
        split; [exact Hfs2 |].
        split.
        * exists ptrs; split.
          -- intros z; rewrite (get_consecutive_ptrs_in_addrs pt sz ptrs z Eptrs), Hsz_eq.
             unfold stage2_in_range; reflexivity.
          -- cbn [state_memory_stack].
             assert (Hfs1_top : Memory_stack_frame_stack (state_memory_stack σ1) = Snoc fs0 f2) by congruence.
             change (Memory_stack_frame_stack
                       (add_all_to_frame ptrs
                          {| Memory_stack_memory :=
                               IntMaps.add_all_index_acc mbs addr (Memory_stack_memory (state_memory_stack σ1));
                             Memory_stack_frame_stack := Memory_stack_frame_stack (state_memory_stack σ1);
                             Memory_stack_heap := Memory_stack_heap (state_memory_stack σ1) |}) =
                     Snoc fs0 (rev ptrs ++ f2)).
             rewrite Hfs1_top, add_all_to_frame_Snoc; reflexivity.
        * split.
          -- intros z Hz; unfold stage2_in_range in Hz.
             cbn [state_memory_stack]; rewrite Hmem_frame; cbn [Memory_stack_memory].
             set (k := Z.to_nat (z - addr)).
             assert (Hk_bs : (k < List.length bs)%nat) by lia.
             destruct (nth_error_Some bs k) as [_ Hsome].
             destruct (nth_error bs k) as [mb0 |] eqn:Enth_bs;
               [| exfalso; apply Hsome; [exact Hk_bs | reflexivity]].
             pose proof (nth_error_In bs k Enth_bs) as Hin_bs.
             rewrite Hbs_eq in Hin_bs; apply repeat_spec in Hin_bs; subst mb0.
             assert (Enth_mbs : nth_error mbs k = Some (poison_memory_byte, Some pr)).
             { unfold mbs; rewrite memory_bytes_to_bytes_eq, nth_error_map, Enth_bs; reflexivity. }
             split.
             ++ eapply lookup_add_all_index_acc_in; [exact Enth_mbs | lia].
             ++ rewrite <- (Hm_eq z).
                apply (next_key_with_alignment_fresh (Memory_stack_memory (state_memory_stack σ1)) al z).
                fold addr; lia.
          -- intros z Hz; unfold stage2_in_range in Hz.
             cbn [state_memory_stack]; rewrite Hmem_frame; cbn [Memory_stack_memory].
             rewrite lookup_add_all_index_acc_out by lia.
             apply Hm_eq.
      + rewrite Hoom; cbn [Interfaces.Memory.lift Monads.bind memS_mon memS_bind memM_interp_prov].
        eapply refine_prov_obs_eq;
          [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
    - rewrite Hoom; cbn [Monads.bind Monad_either Interfaces.Memory.lift memS_mon memS_bind memM_interp_prov].
      eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_Read_byte_safe (q : @ptr ProvenanceV (@PointerV IP))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    safe_prov P_safe (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (Read_byte q) σ1)
      (memM_interp_prov (Read_byte q) σ2).
  Proof using.
    intros (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout) Hsafe.
    unfold Read_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage2_in_range_dec base_dead sz_dead (ptr_to_int q)) as [Hr | Hnr].
    - destruct (Hrng (ptr_to_int q) Hr) as [Hlk1 _].
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      rewrite (safe_prov_access_disjoint P_safe (ptr_provenance q) pr_dead Hsafe Hnin).
      apply memM_interp_prov_raiseUB_l.
    - rewrite (Hout (ptr_to_int q) Hnr).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        destruct (access_allowed (ptr_provenance q) aid).
        * apply refine_prov_ret; repeat split; reflexivity.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_map_monad_Read_byte_safe
    (ptrs : list (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    Forall (fun q => safe_prov P_safe (ptr_provenance q)) ptrs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (map_monad Read_byte ptrs) σ1)
      (memM_interp_prov (map_monad Read_byte ptrs) σ2).
  Proof using.
    intros Hinv Hall; induction Hall as [| q ptrs' Hq _ IH]; cbn [map_monad].
    - apply refine_prov_ret; repeat split; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind;
        [apply (stage2_Read_byte_safe q U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' b1] [σ2' b2] (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind; [exact IH |].
      intros U2 [σ1'' bs1] [σ2'' bs2] (-> & -> & -> & <-).
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma stage2_load_safe (dt : dtyp) (a : @dvalue (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    is_safe_ptr_dvalue P_safe a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) => U' = U /\ σ1' = σ1 /\ σ2' = σ2 /\ r1 = r2)
      U
      (memM_interp_prov (handle_memoryM (Load dt a)) σ1)
      (memM_interp_prov (handle_memoryM (Load dt a)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |];
      try apply memM_interp_prov_raiseUB_l.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold read_dvalue, read_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !memM_interp_prov_bind; reflexivity
      | symmetry; rewrite !memM_interp_prov_bind; reflexivity |].
    destruct (get_consecutive_ptrs pt (@store_size_dtyp SizeofV dt))
      as [s | s | s | ptrs] eqn:Eptrs;
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseOOM, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | reflexivity |].
      apply refine_prov_ub_vis_l; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
        | symmetry; unfold raise, trigger_cast, ITree.trigger; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
         rewrite memM_interp_prov_map_monad_acc; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; cbn [read_byte MemoryModelPrimitivesV];
          rewrite memM_interp_prov_map_monad_acc; reflexivity |].
      assert (Hall_safe : Forall (fun q => safe_prov P_safe (ptr_provenance q)) ptrs).
      { destruct (get_consecutive_ptrs_spec pt (@store_size_dtyp SizeofV dt) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros q Hin_q.
        apply In_nth_error in Hin_q as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q); rewrite Hpr_q; exact Hsafe. }
      eapply refine_prov_bind;
        [apply (stage2_map_monad_Read_byte_safe ptrs U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hall_safe) |].
      intros U1 [σ1' bs1] [σ2' bs2] (-> & -> & -> & <-).
      eapply memM_interp_prov_lift_EOU; [apply refine_EOU_refl |].
      intros dv _ <-; repeat split; reflexivity.
  Qed.

  Lemma stage2_Write_byte_safe
    (q : @ptr ProvenanceV (@PointerV IP)) (mb : @memory_byte (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    safe_prov P_safe (ptr_provenance q) ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (Write_byte q mb) σ1)
      (memM_interp_prov (Write_byte q mb) σ2).
  Proof using.
    intros (Hpu & Hin & Hnin & Hh & Hfs2 & Hfs1 & Hrng & Hout) Hsafe.
    unfold Write_byte, read_byte_raw, read_byte_raw_mem.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [get Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ1))).
    change (IM.find (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
      with (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2))).
    destruct (stage2_in_range_dec base_dead sz_dead (ptr_to_int q)) as [Hr | Hnr].
    - destruct (Hrng (ptr_to_int q) Hr) as [Hlk1 _].
      rewrite Hlk1.
      eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
      rewrite (safe_prov_access_disjoint P_safe (ptr_provenance q) pr_dead Hsafe Hnin).
      apply memM_interp_prov_raiseUB_l.
    - rewrite (Hout (ptr_to_int q) Hnr).
      destruct (IntMaps.lookup (ptr_to_int q) (Memory_stack_memory (state_memory_stack σ2)))
        as [[b0 aid] |].
      + eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        destruct (access_allowed (ptr_provenance q) aid).
        * unfold set_byte_raw, get_mem, upd_mem, app_mem, set_byte_raw_mem, get, put;
            cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
          apply refine_prov_ret; repeat split; cbn;
            try exact Hpu; try exact Hin; try exact Hnin;
            try exact Hh; try exact Hfs2; try exact Hfs1.
          -- intros z Hz.
             assert (Hne : ptr_to_int q <> z) by (intros ->; exact (Hnr Hz)).
             rewrite !IntMaps.lookup_add_ineq by exact Hne.
             exact (proj1 (Hrng z Hz)).
          -- intros z Hz.
             assert (Hne : ptr_to_int q <> z) by (intros ->; exact (Hnr Hz)).
             rewrite !IntMaps.lookup_add_ineq by exact Hne.
             exact (proj2 (Hrng z Hz)).
          -- intros z Hz.
             destruct (Z.eq_dec (ptr_to_int q) z) as [<- | Hne].
             ++ rewrite !IntMaps.lookup_add_eq; reflexivity.
             ++ rewrite !IntMaps.lookup_add_ineq by exact Hne; apply Hout, Hz.
        * apply memM_interp_prov_raiseUB_l.
      + cbn [memM_interp_prov]; eapply refine_prov_obs_eq;
          [symmetry; unfold raiseUB, trigger_cast, ITree.trigger; rewrite Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | reflexivity |].
        apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma stage2_loop_Write_byte_safe
    (pbs : list (@ptr ProvenanceV (@PointerV IP) * @memory_byte (@ParamsV IP IPT)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    Forall (fun '(q, _) => safe_prov P_safe (ptr_provenance q)) pbs ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ1)
      (memM_interp_prov (loop_monad (fun '(pt, mb) => Write_byte pt mb) pbs) σ2).
  Proof using.
    intros Hinv Hall; revert σ1 σ2 Hinv;
      induction Hall as [| [q mb] pbs' Hq _ IH]; intros σ1 σ2 Hinv; cbn [loop_monad].
    - apply refine_prov_ret; repeat split; try exact Hinv; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
      eapply refine_prov_bind;
        [apply (stage2_Write_byte_safe q mb U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Hq) |].
      intros U1 [σ1' []] [σ2' []] (-> & _ & _ & Hinv1).
      apply IH, Hinv1.
  Qed.

  Lemma stage2_store_safe (dt : dtyp) (a v : @dvalue (@ParamsV IP IPT))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    is_safe_ptr_dvalue P_safe a ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2')
      U
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ1)
      (memM_interp_prov (handle_memoryM (Store dt a v)) σ2).
  Proof using.
    intros Hinv Ha; cbn [handle_memoryM].
    destruct a as [[pt | | | | | | |] | |];
      try apply memM_interp_prov_raiseUB_l.
    pose proof (Ha pt Logic.eq_refl) as Hsafe.
    unfold write_dvalue, write_bytes.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    destruct (dvalue_to_memory_bytes dt v None) as [s | s | s | bs];
      cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
    - apply memM_interp_prov_raiseOOM_l.
    - apply memM_interp_prov_raiseUB_l.
    - apply memM_interp_prov_raise_both.
    - eapply refine_prov_obs_eq;
        [symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity
        | symmetry; rewrite Eqit.bind_ret_l, memM_interp_prov_bind; reflexivity |].
      destruct (get_consecutive_ptrs pt (ListUtil.N.length bs)) as [s | s | s | ptrs] eqn:Eptrs;
        cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov].
      + apply memM_interp_prov_raiseOOM_l.
      + apply memM_interp_prov_raiseUB_l.
      + apply memM_interp_prov_raise_both.
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity
          | symmetry; rewrite Eqit.bind_ret_l, zip_combine_eq; reflexivity |].
        cbn [write_byte MemoryModelPrimitivesV].
        apply stage2_loop_Write_byte_safe; [exact Hinv |].
        destruct (get_consecutive_ptrs_spec pt (ListUtil.N.length bs) ptrs Eptrs) as (_ & Hinv_p & _).
        rewrite Forall_forall; intros [q mb] Hin_c.
        apply in_combine_l in Hin_c.
        apply In_nth_error in Hin_c as [k Hnth].
        destruct (Hinv_p k q Hnth) as (_ & _ & Hpr_q); rewrite Hpr_q; exact Hsafe.
  Qed.

  Lemma stage2_mempop_restore
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state) :
    stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 ->
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         U' = U /\ r1 = tt /\ r2 = tt /\
         mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
         Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (memM_interp_prov (handle_memoryM MemPop) σ1)
      (memM_interp_prov (handle_memoryM MemPop) σ2).
  Proof using.
    intros (_ & _ & _ & Hh & Hfs2 & (ptrs_dead & Hptrs & Hfs1) & Hrng & Hout).
    cbn [handle_memoryM mempop MemoryModelPrimitivesV].
    unfold Mempop, get_frame, get_frame_stack, app_frame_stack_eob, get_framestack,
           upd_frame_stack, app_frame_stack, app_mem, get, put.
    eapply refine_prov_obs_eq;
      [symmetry; apply memM_interp_prov_bind | symmetry; apply memM_interp_prov_bind |].
    cbn [Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov state_get_memory MemoryModelStateV].
    rewrite Hfs1, Hfs2.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    cbn [pop_frame_stack Interfaces.Memory.lift Monads.bind memS_mon memS_bind Monads.ret memM_interp_prov].
    apply refine_prov_ret; repeat split; cbn; try exact Hh.
    intros z.
    destruct (stage2_in_range_dec base_dead sz_dead z) as [Hr | Hnr].
    - assert (Hin1 : In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
      { apply in_map_rev_app_iff; left; apply Hptrs, Hr. }
      rewrite (lookup_free_frame_memory_in (rev ptrs_dead ++ f2) _ z Hin1).
      destruct (in_dec Z.eq_dec z (List.map ptr_to_int f2)) as [Hin2 | Hnin2].
      + rewrite (lookup_free_frame_memory_in f2 _ z Hin2); reflexivity.
      + rewrite (lookup_free_frame_memory_out f2 _ z Hnin2).
        symmetry; exact (proj2 (Hrng z Hr)).
    - destruct (in_dec Z.eq_dec z (List.map ptr_to_int f2)) as [Hin2 | Hnin2].
      + assert (Hin1 : In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
        { apply in_map_rev_app_iff; right; exact Hin2. }
        rewrite (lookup_free_frame_memory_in (rev ptrs_dead ++ f2) _ z Hin1),
                (lookup_free_frame_memory_in f2 _ z Hin2); reflexivity.
      + assert (Hnin1 : ~ In z (List.map ptr_to_int (rev ptrs_dead ++ f2))).
        { intros Hin1; apply in_map_rev_app_iff in Hin1 as [Hp | Hf];
            [apply Hptrs in Hp; exact (Hnr Hp) | exact (Hnin2 Hf)]. }
        rewrite (lookup_free_frame_memory_out (rev ptrs_dead ++ f2) _ z Hnin1),
                (lookup_free_frame_memory_out f2 _ z Hnin2).
        exact (Hout z Hnr).
  Qed.

  (** ** 3F. Syntactic Uniqueness, Environment & Interpreter Lifting Helpers *)

  Lemma m2r_flat_map_app {A B} (f : A -> list B) (l1 l2 : list A) :
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof using.
    induction l1 as [| a l1' IH]; cbn; [reflexivity | rewrite IH, app_assoc; reflexivity].
  Qed.

  Lemma m2r_in_raw_ids_dec (x : raw_id) (xs : list raw_id) :
    {In x xs} + {~ In x xs}.
  Proof using.
    induction xs as [| y ys IH].
    - right; intros [].
    - destruct (raw_id_eqb_spec x y) as [-> | Hne].
      + left; left; reflexivity.
      + destruct IH as [Hin | Hnin].
        * left; right; exact Hin.
        * right; intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnin Hin)].
  Qed.

  Lemma m2r_in_raw_ids_true (x : raw_id) (xs : list raw_id) :
    in_raw_ids x xs = true <-> In x xs.
  Proof using.
    destruct (in_raw_ids x xs) eqn:E.
    - destruct (m2r_in_raw_ids_dec x xs) as [Hin | Hnin];
        [tauto | apply in_raw_ids_false in Hnin; congruence].
    - apply in_raw_ids_false in E; split; [discriminate | intros H; contradiction (E H)].
  Qed.

  Lemma m2r_count_id_in_pos (x : raw_id) (xs : list raw_id) :
    In x xs ->
    (1 <= m2r_count_id x xs)%nat.
  Proof using.
    induction xs as [| y ys IH]; cbn [In m2r_count_id]; [intros [] |].
    intros [-> | Hin].
    - destruct (raw_id_eqb_spec x x) as [_ | Hne]; [lia | contradiction (Hne Logic.eq_refl)].
    - specialize (IH Hin); destruct (raw_id_eqb x y); lia.
  Qed.

  Lemma m2r_in_filter_no_p (p q : raw_id) (xs : list raw_id) :
    In q (List.filter (fun r => negb (raw_id_eqb r p)) xs) <->
    In q xs /\ q <> p.
  Proof using.
    rewrite filter_In, negb_true_iff.
    destruct (raw_id_eqb_spec q p) as [-> | Hne]; split; intros H;
      try tauto; destruct H as [_ H]; discriminate H.
  Qed.

  Lemma m2r_collect_unique_allocas_inv
    (all_defs : list raw_id) (bks : ocfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas all_defs bks) ->
    m2r_count_id q all_defs = 1%nat /\
    exists bk dt_q anns_q md_q,
      In bk bks /\
      In (IId q, INSTR_Alloca dt_q anns_q, md_q) (blk_code bk).
  Proof using.
    unfold m2r_collect_unique_allocas; rewrite in_flat_map.
    intros (bk & Hbk & Hin1).
    rewrite in_flat_map in Hin1.
    destruct Hin1 as ([[iid ins] md] & Him & Hin2).
    destruct iid as [id0 |]; [| contradiction Hin2].
    destruct ins; try contradiction Hin2.
    destruct (Nat.eqb_spec (m2r_count_id id0 all_defs) 1%nat) as [Hcnt | _];
      [| contradiction Hin2].
    destruct Hin2 as [<- | []].
    split; [exact Hcnt | eexists bk, _, _, md; split; eassumption].
  Qed.

  Lemma m2r_safe_ptr_exp_mono (s1 s2 : list local_id) (e : exp dtyp) :
    (forall q, In q s1 -> In q s2) ->
    m2r_safe_ptr_exp s1 e = true ->
    m2r_safe_ptr_exp s2 e = true.
  Proof using.
    intros Hsub; induction e; cbn [m2r_safe_ptr_exp]; try (intros H; exact H).
    - destruct id as [| q]; [intros H; exact H |].
      rewrite !m2r_in_raw_ids_true; apply Hsub.
    - destruct ptrval as [_ base_e]; apply IHe.
    - destruct cnd as [_ ec], v1 as [_ e1], v2 as [_ e2].
      rewrite !andb_true_iff; intros [H1 H2]; split; [apply IHe2, H1 | apply IHe3, H2].
  Qed.

  Lemma m2r_nodup_map_inv {A B} (f : A -> B) (xs : list A) :
    NoDup (List.map f xs) ->
    NoDup xs.
  Proof using.
    induction xs as [| x xs' IH]; cbn [List.map]; intros Hnd; [constructor |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    constructor; [intros Hx; exact (Hnin (in_map f xs' x Hx)) | apply IH, Hnd'].
  Qed.

  Lemma m2r_count_id_in_two_elems {A} (g : A -> list raw_id) (xs : list A)
    (a1 a2 : A) (q : raw_id) :
    NoDup xs ->
    In a1 xs ->
    In a2 xs ->
    a1 <> a2 ->
    In q (g a1) ->
    In q (g a2) ->
    (2 <= m2r_count_id q (flat_map g xs))%nat.
  Proof using.
    intros Hnd; induction Hnd as [| x xs' Hnin Hnd' IH]; cbn [In flat_map]; [intros [] |].
    intros [<- | Ha1] [<- | Ha2] Hne Hq1 Hq2; try contradiction.
    - rewrite m2r_count_id_app.
      pose proof (m2r_count_id_in_pos q (g a1) Hq1).
      assert (Hin2 : In q (flat_map g xs')) by (apply in_flat_map; exists a2; split; assumption).
      pose proof (m2r_count_id_in_pos q (flat_map g xs') Hin2); lia.
    - rewrite m2r_count_id_app.
      pose proof (m2r_count_id_in_pos q (g a2) Hq2).
      assert (Hin1 : In q (flat_map g xs')) by (apply in_flat_map; exists a1; split; assumption).
      pose proof (m2r_count_id_in_pos q (flat_map g xs') Hin1); lia.
    - rewrite m2r_count_id_app.
      pose proof (IH Ha1 Ha2 Hne Hq1 Hq2); lia.
  Qed.

  Lemma unique_alloca_not_in_fargs
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    ~ In q fargs.
  Proof using.
    intros Hq Hin_arg.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    pose proof (m2r_count_id_in_pos q fargs Hin_arg) as H1.
    assert (Hin_bks : In q (flat_map full_block_defs bks)).
    { apply in_flat_map; exists bk0; split; [exact Hbk0 |].
      unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
      apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
    pose proof (m2r_count_id_in_pos q _ Hin_bks) as H2; lia.
  Qed.

  Lemma unique_alloca_not_phi_def
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    NoDup (List.map blk_id bks) ->
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    forall bk x ph md,
      In bk bks ->
      In (x, ph, md) (blk_phis bk) ->
      x <> q.
  Proof using.
    intros Hnd_ids Hq bk x ph md Hbk Hphi ->.
    apply m2r_nodup_map_inv in Hnd_ids.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    assert (Hin_phi : In q (List.map (fun '(y, _, _) => y) (blk_phis bk))).
    { apply in_map_iff; exists (q, ph, md); split; [reflexivity | exact Hphi]. }
    assert (Hin_al : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk0))).
    { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
    destruct (raw_id_eqb_spec (blk_id bk) (blk_id bk0)) as [Heq_id | Hne_id].
    - assert (bk = bk0).
      { clear -Hnd_ids Hbk Hbk0 Heq_id.
        induction Hnd_ids as [| b bs Hnin Hnd IH]; [contradiction |].
        destruct Hbk as [<- | Hbk], Hbk0 as [<- | Hbk0]; [reflexivity | | | auto].
        - exfalso; apply Hnin; rewrite Heq_id; apply in_map, Hbk0.
        - exfalso; apply Hnin; rewrite <- Heq_id; apply in_map, Hbk. }
      subst bk0.
      assert (H2 : (2 <= m2r_count_id q (full_block_defs bk))%nat).
      { unfold full_block_defs; rewrite !m2r_count_id_app.
        pose proof (m2r_count_id_in_pos q _ Hin_phi).
        pose proof (m2r_count_id_in_pos q _ Hin_al); lia. }
      assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
      { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
        rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
      lia.
    - assert (Hne_bk : bk <> bk0) by (intros ->; exact (Hne_id Logic.eq_refl)).
      assert (Hdef1 : In q (full_block_defs bk)) by (unfold full_block_defs; apply in_app_iff; left; exact Hin_phi).
      assert (Hdef2 : In q (full_block_defs bk0))
        by (unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left; exact Hin_al).
      pose proof (m2r_count_id_in_two_elems full_block_defs bks bk bk0 q Hnd_ids Hbk Hbk0 Hne_bk Hdef1 Hdef2).
      lia.
  Qed.

  Lemma unique_alloca_code_def_is_alloca
    (fargs : list local_id) (bks : ocfg dtyp) (q : local_id) :
    NoDup (List.map blk_id bks) ->
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks) ->
    forall bk pre ins md post,
      In bk bks ->
      blk_code bk = pre ++ (IId q, ins, md) :: post ->
      exists dt0 anns0, ins = INSTR_Alloca dt0 anns0.
  Proof using.
    intros Hnd_ids Hq bk pre ins md post Hbk Hsplit.
    apply m2r_nodup_map_inv in Hnd_ids.
    apply m2r_collect_unique_allocas_inv in Hq as (Hcnt & bk0 & dt0 & anns0 & md0 & Hbk0 & Him0).
    rewrite m2r_count_id_app in Hcnt.
    destruct (raw_id_eqb_spec (blk_id bk) (blk_id bk0)) as [Heq_id | Hne_id].
    - assert (bk = bk0).
      { clear -Hnd_ids Hbk Hbk0 Heq_id.
        induction Hnd_ids as [| b bs Hnin Hnd IH]; [contradiction |].
        destruct Hbk as [<- | Hbk], Hbk0 as [<- | Hbk0]; [reflexivity | | | auto].
        - exfalso; apply Hnin; rewrite Heq_id; apply in_map, Hbk0.
        - exfalso; apply Hnin; rewrite <- Heq_id; apply in_map, Hbk. }
      subst bk0.
      rewrite Hsplit in Him0; apply in_app_iff in Him0 as [Hin_pre | [Heq_im | Hin_post]].
      + exfalso.
        assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
        { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
          rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
        unfold full_block_defs in Hge; rewrite Hsplit, m2r_flat_map_app in Hge; cbn [flat_map instr_id_defs] in Hge.
        rewrite !m2r_count_id_app in Hge; cbn [m2r_count_id] in Hge; rewrite raw_id_eqb_refl in Hge.
        assert (Hp1 : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre)).
        { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Hin_pre | left; reflexivity]. }
        pose proof (m2r_count_id_in_pos q _ Hp1); lia.
      + inversion Heq_im; exists dt0, anns0; reflexivity.
      + exfalso.
        assert (Hge : (m2r_count_id q (full_block_defs bk) <= m2r_count_id q (flat_map full_block_defs bks))%nat).
        { clear -Hbk; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
          rewrite m2r_count_id_app; destruct Hbk as [<- | Hbk]; [lia | specialize (IH Hbk); lia]. }
        unfold full_block_defs in Hge; rewrite Hsplit, m2r_flat_map_app in Hge; cbn [flat_map instr_id_defs] in Hge.
        rewrite !m2r_count_id_app in Hge; cbn [m2r_count_id] in Hge; rewrite raw_id_eqb_refl in Hge.
        assert (Hp2 : In q (flat_map (fun '(iid, _, _) => instr_id_defs iid) post)).
        { apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Hin_post | left; reflexivity]. }
        pose proof (m2r_count_id_in_pos q _ Hp2); lia.
    - exfalso.
      assert (Hne_bk : bk <> bk0) by (intros ->; exact (Hne_id Logic.eq_refl)).
      assert (Hdef1 : In q (full_block_defs bk)).
      { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
        rewrite Hsplit; apply in_flat_map; exists (IId q, ins, md);
          split; [apply in_app_iff; right; left; reflexivity | left; reflexivity]. }
      assert (Hdef2 : In q (full_block_defs bk0)).
      { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
        apply in_flat_map; exists (IId q, INSTR_Alloca dt0 anns0, md0); split; [exact Him0 | left; reflexivity]. }
      pose proof (m2r_count_id_in_two_elems full_block_defs bks bk bk0 q Hnd_ids Hbk Hbk0 Hne_bk Hdef1 Hdef2).
      lia.
  Qed.

  Definition safe_locals_env
    (P_unprom : list N) (safe_locals : list local_id)
    (env : @local_env (@ParamsV IP IPT)) : Prop :=
    forall q v,
      In q safe_locals ->
      Maps.lookup q env = Some v ->
      is_safe_ptr_dvalue P_unprom v.

  Lemma safe_locals_env_incl (P1 P2 : list N) (safe_locals : list local_id)
    (env : @local_env (@ParamsV IP IPT)) :
    incl P1 P2 ->
    safe_locals_env P1 safe_locals env ->
    safe_locals_env P2 safe_locals env.
  Proof using.
    intros Hinc Henv q v Hq Hlk.
    eapply is_safe_ptr_dvalue_incl; [exact Hinc | exact (Henv q v Hq Hlk)].
  Qed.

  Lemma select_switch_in
    (value : @dvalue (@ParamsV IP IPT)) (default_dest : block_id)
    (switches : list (@dvalue (@ParamsV IP IPT) * block_id)) (bid : block_id) :
    select_switch value default_dest switches = raise_ret bid ->
    bid = default_dest \/ In bid (List.map snd switches).
  Proof using.
    induction switches as [| [v id0] sw' IH]; cbn [select_switch List.map].
    - intros H; inversion H; left; reflexivity.
    - destruct value as [db1 | |]; try (intros H; discriminate H).
      destruct db1; try (intros H; discriminate H).
      destruct v as [db2 | |]; try (intros H; discriminate H).
      destruct db2; try (intros H; discriminate H).
      match goal with
      | |- context [Pos.eq_dec ?s1 ?s2] =>
          destruct (Pos.eq_dec s1 s2) as [? | _]; subst; [| intros H; discriminate H]
      end.
      cbn.
      match goal with
      | |- context [if ?c then _ else _] => destruct c
      end.
      + intros H; inversion H; right; left; reflexivity.
      + intros H; destruct (IH H) as [-> | Hin];
          [left; reflexivity | right; right; exact Hin].
  Qed.

  Lemma switch_dests_map_snd
    (dests : list (tint_literal * block_id))
    (switches : list (@dvalue (@ParamsV IP IPT) * block_id)) :
    map_monad
      (fun '((TInt_Literal sz x), id) =>
         Monads.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
           (fun s => Monads.ret (@DVALUE_Base (@ParamsV IP IPT) s, id)))
      dests = raise_ret switches ->
    List.map snd switches = List.map snd dests.
  Proof using.
    revert switches; induction dests as [| [[sz x] id0] dests' IH]; intros switches H;
      cbn [map_monad] in H.
    - inversion H; reflexivity.
    - apply EOU_bind_ret_inv in H as ([v0 bid0] & Hhd & Htl).
      apply EOU_bind_ret_inv in Hhd as (s & _ & Heq0); inversion Heq0; subst.
      apply EOU_bind_ret_inv in Htl as (sw_tl & Hmap & Heq_sw); inversion Heq_sw; subst.
      cbn [List.map snd]; f_equal; apply IH, Hmap.
  Qed.

  Inductive tau_expand_ {E : Type -> Type} {R : Type}
    (r : itree E R -> itree E R -> Prop) : itree E R -> itree E R -> Prop :=
  | TE_Eq t1 t1' t2 t2' :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      tau_expand_ r t1' t2' ->
      tau_expand_ r t1 t2
  | TE_Ret x :
      tau_expand_ r (Ret x) (Ret x)
  | TE_Tau m1 m2 :
      r m1 m2 ->
      tau_expand_ r (Tau m1) (Tau m2)
  | TE_Vis X (e : E X) k1 k2 :
      (forall x, r (k1 x) (k2 x)) ->
      tau_expand_ r (Vis e k1) (Vis e k2)
  | TE_TauL m1 t2 :
      tau_expand_ r m1 t2 ->
      tau_expand_ r (Tau m1) t2.

  Lemma tau_expand__mon {E : Type -> Type} {R : Type} :
    monotone2 (@tau_expand_ E R).
  Proof using.
    intros t1 t2 r r' IN LE.
    induction IN as [t1 t1' t2 t2' E1 E2 _ IH
                    | x
                    | m1 m2 Hr
                    | X e k1 k2 Hk
                    | m1 t2 _ IH].
    - eapply TE_Eq; [exact E1 | exact E2 | exact IH].
    - apply TE_Ret.
    - apply TE_Tau; apply LE, Hr.
    - apply TE_Vis; intros x; apply LE, Hk.
    - apply TE_TauL, IH.
  Qed.

  Definition tau_expand {E : Type -> Type} {R : Type}
    (t1 t2 : itree E R) : Prop :=
    paco2 (@tau_expand_ E R) bot2 t1 t2.

  Lemma tau_expand_obs_eq {E : Type -> Type} {R : Type}
    (t1 t1' t2 t2' : itree E R) :
    t1 ≅ t1' ->
    t2 ≅ t2' ->
    tau_expand t1 t2 ->
    tau_expand t1' t2'.
  Proof using.
    intros E1 E2 H; punfold H; pstep.
    eapply TE_Eq; [symmetry; exact E1 | symmetry; exact E2 |].
    eapply tau_expand__mon; [exact H | intros a b [Hab | []]; left; exact Hab].
  Qed.

  Lemma tau_expand_refl {E : Type -> Type} {R : Type} :
    forall (t : itree E R), tau_expand t t.
  Proof using.
    pcofix CIH; intros t; pstep.
    eapply TE_Eq; [apply itree_eta | apply itree_eta |].
    destruct (observe t) as [x | m | X e k].
    - apply TE_Ret.
    - apply TE_Tau; right; apply CIH.
    - apply TE_Vis; intros x; right; apply CIH.
  Qed.

  Lemma tau_expand_bind {E : Type -> Type} {A B : Type} :
    forall (u1 u2 : itree E A) (k1 k2 : A -> itree E B),
      tau_expand u1 u2 ->
      (forall a, tau_expand (k1 a) (k2 a)) ->
      tau_expand (ITree.bind u1 k1) (ITree.bind u2 k2).
  Proof using.
    pcofix CIH; intros u1 u2 k1 k2 Hu Hk; punfold Hu; pstep.
    induction Hu as [t1 t1' t2 t2' E1 E2 _ IH
                    | x
                    | m1 m2 Hm
                    | X e h1 h2 Hh
                    | m1 t2 _ IH].
    - eapply TE_Eq; [rewrite E1; reflexivity | rewrite E2; reflexivity | exact IH].
    - eapply TE_Eq; [apply Eqit.bind_ret_l | apply Eqit.bind_ret_l |].
      specialize (Hk x); punfold Hk.
      eapply tau_expand__mon; [exact Hk | intros a b [Hab | []]; left; exact Hab].
    - eapply TE_Eq; [apply Eqit.bind_tau | apply Eqit.bind_tau |].
      apply TE_Tau; pclearbot; right; apply CIH; [exact Hm | exact Hk].
    - eapply TE_Eq; [apply Eqit.bind_vis | apply Eqit.bind_vis |].
      apply TE_Vis; intros x; specialize (Hh x); pclearbot; right; apply CIH; [exact Hh | exact Hk].
    - eapply TE_Eq; [apply Eqit.bind_tau | reflexivity |].
      apply TE_TauL, IH.
  Qed.

  (** *** Lifting [tau_expand] to [refine_prov] without [Eqdep] *)

  Definition prov_te_vis_match {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    {X1} (e1 : ProvBotE X1) (k1 : X1 -> itree ProvBotE R)
    {X2} (e2 : ProvBotE X2) (k2 : X2 -> itree ProvBotE R) : Prop :=
    match e1 in (_ +' _) Y1 return (Y1 -> itree ProvBotE R) -> Prop with
    | inl1 p1 =>
        match p1 in ProvE Y1 return (Y1 -> itree ProvBotE R) -> Prop with
        | FreshProv => fun k1' =>
            match e2 in (_ +' _) Y2 return (Y2 -> itree ProvBotE R) -> Prop with
            | inl1 p2 =>
                match p2 in ProvE Y2 return (Y2 -> itree ProvBotE R) -> Prop with
                | FreshProv => fun k2' => forall p : N, r (k1' p) (k2' p)
                end k2
            | inr1 _ => fun _ => False
            end
        end
    | inr1 b1 => fun k1' =>
        match e2 in (_ +' _) Y2 return (Y2 -> itree ProvBotE R) -> Prop with
        | inl1 _ => fun _ => False
        | inr1 b2 => fun k2' =>
            EqE_bot _ _ b1 b2 /\
            EqE_bot _ _ b2 b1 /\
            (forall a1 a2, EqA_bot _ _ b1 a1 b2 a2 -> r (k1' a1) (k2' a2)) /\
            (forall a2 a1, EqA_bot _ _ b2 a2 b1 a1 -> r (k1' a1) (k2' a2))
        end k2
    end k1.

  Definition prov_te_step_body {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    (ot1 ot2 : itree' ProvBotE R) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => r1 = r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r m1 m2
        | _ => False
        end
    | VisF e1 k1 =>
        match ot2 with
        | VisF e2 k2 => prov_te_vis_match r e1 k1 e2 k2
        | _ => False
        end
    end.

  Inductive prov_te_ {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    : itree ProvBotE R -> itree ProvBotE R -> Prop :=
  | PTE_Step t1 t2 :
      prov_te_step_body r (observe t1) (observe t2) ->
      prov_te_ r t1 t2
  | PTE_TauL t1 m1 t2 :
      observe t1 = TauF m1 ->
      prov_te_ r m1 t2 ->
      prov_te_ r t1 t2.

  Lemma prov_te__mon {R : Type} :
    monotone2 (@prov_te_ R).
  Proof using.
    intros t1 t2 r r' IN LE.
    induction IN as [t1 t2 Hstep | t1 m1 t2 Ht1 _ IH].
    - apply PTE_Step; unfold prov_te_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1],
               (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
      + exact Hstep.
      + apply LE, Hstep.
      + destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
        * destruct p1, p2; intros p; apply LE, Hstep.
        * destruct Hstep as (HE1 & HE2 & HA1 & HA2).
          split; [exact HE1 | split; [exact HE2 | split]].
          -- intros a1 a2 Ha; apply LE, HA1, Ha.
          -- intros a2 a1 Ha; apply LE, HA2, Ha.
    - eapply PTE_TauL; [exact Ht1 | exact IH].
  Qed.

  Definition prov_te {R : Type} (t1 t2 : itree ProvBotE R) : Prop :=
    paco2 (@prov_te_ R) bot2 t1 t2.

  Lemma prov_te__obs_eq {R : Type}
    (r : itree ProvBotE R -> itree ProvBotE R -> Prop)
    (Hr_eq : forall a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r a1 a2 -> r a1' a2') :
    forall (t1 t1' t2 t2' : itree ProvBotE R),
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      prov_te_ r t1 t2 ->
      prov_te_ r t1' t2'.
  Proof using.
    intros t1 t1' t2 t2' E1 E2 Hrel.
    revert t1' t2' E1 E2;
      induction Hrel as [t1 t2 Hstep | t1 m1 t2 Ht1 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply PTE_Step; unfold prov_te_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1]; pclearbot.
      + destruct E2 as [r2 r2' <- | |]; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 |]; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct E2 as [| | X2 e2 k2 k2' Hk2]; try contradiction; pclearbot.
        destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
        * destruct p1, p2; intros p; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hstep].
        * destruct Hstep as (HE1 & HE2 & HA1 & HA2).
          split; [exact HE1 | split; [exact HE2 | split]].
          -- intros a1 a2 Ha; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA1 a1 a2 Ha)].
          -- intros a2 a1 Ha; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA2 a2 a1 Ha)].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        inversion E1 as [| m1_ m1' Hm1 E1a E1b |]; subst; pclearbot.
      eapply PTE_TauL; [symmetry; exact E1b | eapply IH; [exact Hm1 | exact E2]].
  Qed.

  Lemma tau_expand_step_prov_te {R : Type} (t1 t2 : itree ProvBotE R) :
    tau_expand_ (upaco2 (@tau_expand_ ProvBotE R) bot2) t1 t2 ->
    prov_te_ (@tau_expand ProvBotE R) t1 t2.
  Proof using.
    intros Hte.
    induction Hte as [t1 t1' t2 t2' E1 E2 _ IH
                     | x
                     | m1 m2 Hm
                     | X e k1 k2 Hk
                     | m1 t2 _ IH].
    - eapply prov_te__obs_eq; [exact (@tau_expand_obs_eq ProvBotE R) | | | exact IH];
        symmetry; assumption.
    - apply PTE_Step; cbn; reflexivity.
    - pclearbot; apply PTE_Step; cbn; exact Hm.
    - apply PTE_Step; cbn.
      destruct e as [p | b]; cbn.
      + destruct p; intros q; specialize (Hk q); pclearbot; exact Hk.
      + split; [apply EqE_bot_refl | split; [apply EqE_bot_refl | split]].
        * intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2;
            specialize (Hk a1); pclearbot; exact Hk.
        * intros a2 a1 Ha; apply EqA_bot_eq in Ha; subst a1;
            specialize (Hk a2); pclearbot; exact Hk.
    - eapply PTE_TauL; [reflexivity | exact IH].
  Qed.

  Lemma tau_expand_to_prov_te {R : Type} :
    forall (t1 t2 : itree ProvBotE R),
      tau_expand t1 t2 ->
      prov_te t1 t2.
  Proof using.
    pcofix CIH; intros t1 t2 Hte; pstep; punfold Hte.
    apply tau_expand_step_prov_te in Hte.
    eapply prov_te__mon; [exact Hte | intros a1 a2 Ha; right; apply CIH, Ha].
  Qed.

  Definition rel_te_l {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) : Prop :=
    exists t1, prov_te t1' t1 /\ refine_prov RR U t1 t2.

  Lemma refine_prov_prov_te_l_step {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U t1 t2 ->
    forall t1',
      prov_te t1' t1 ->
      refine_prov_ RR (upaco3 (refine_prov_ RR) (rel_te_l RR)) U t1' t2.
  Proof using.
    intros Hrp; punfold Hrp.
    induction Hrp as [U t1 t2 Hstep_rp | U t1 m1 t2 Ht1 _ IH_rp | U t1 t2 m2 Ht2 _ IH_rp];
      intros t1' Hte.
    - punfold Hte.
      induction Hte as [t1' t1_ Hstep_te | t1' n1' t1_ Hot1' _ IH_te].
      + apply RP_Step; unfold rp_step_body, prov_te_step_body in *.
        destruct (observe t1') as [x1' | m1' | X1' e1' k1'],
                 (observe t1_) as [x1 | m1 | X1 e1 k1]; try contradiction.
        * subst x1'; exact Hstep_rp.
        * destruct (observe t2) as [| m2 |]; try contradiction; pclearbot.
          right; exists m1; split; assumption.
        * destruct e1' as [p1' | b1'], e1 as [p1 | b1]; cbn in Hstep_te; try contradiction.
          -- destruct p1', p1.
             destruct Hstep_rp as [Hub | [Hleft | Hboth]]; [discriminate Hub | |].
             ++ right; left; intros p Hp.
                specialize (Hstep_te p); specialize (Hleft p Hp); pclearbot.
                right; exists (k1 p); split; assumption.
             ++ right; right.
                destruct (observe t2) as [| | X2 e2 k2]; try contradiction.
                destruct e2 as [p2 | b2]; cbn in *; try contradiction; destruct p2.
                intros p Hp; specialize (Hstep_te p); specialize (Hboth p Hp); pclearbot.
                right; exists (k1 p); split; assumption.
          -- destruct Hstep_te as (HE1' & _ & HA1' & _).
             destruct Hstep_rp as [Hub | [Hleft | Hboth]]; [| cbn in Hleft; contradiction |].
             ++ left; cbn in *; rewrite (EqE_bot_is_ub _ _ HE1'); exact Hub.
             ++ right; right.
                destruct (observe t2) as [| | X2 e2 k2]; try contradiction.
                destruct e2 as [p2 | b2]; cbn in *; try contradiction.
                destruct Hboth as [HE12 HA12].
                split; [eapply EqE_bot_trans; eassumption |].
                intros a1' a2 Ha1'2.
                destruct (EqA_bot_trans b1' b1 b2 a1' a2 HE1' HE12 Ha1'2) as [a1 [Ha1'1 Ha12]].
                specialize (HA1' a1' a1 Ha1'1); specialize (HA12 a1 a2 Ha12); pclearbot.
                rewrite (bot_ans_provs_eq b1' b1 a1' a1 HE1' Ha1'1).
                right; exists (k1 a1); split; assumption.
      + eapply RP_TauL; [exact Hot1' | exact IH_te].
    - punfold Hte; revert Ht1.
      induction Hte as [t1' t1_ Hstep_te | t1' n1' t1_ Hot1' _ IH_te]; intros Ht1.
      + unfold prov_te_step_body in Hstep_te; rewrite Ht1 in Hstep_te.
        destruct (observe t1') as [| m1' |] eqn:Hot1'; try contradiction; pclearbot.
        eapply RP_TauL; [exact Hot1' | apply (IH_rp m1' Hstep_te)].
      + eapply RP_TauL; [exact Hot1' | apply (IH_te Ht1)].
    - eapply RP_TauR; [exact Ht2 | apply (IH_rp t1' Hte)].
  Qed.

  Lemma refine_prov_tau_expand_l {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    tau_expand t1' t1 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1' t2.
  Proof using.
    intros Hte Hrp; apply tau_expand_to_prov_te in Hte.
    assert (Hmain : forall U0 a1' a2, rel_te_l RR U0 a1' a2 -> refine_prov RR U0 a1' a2).
    { pcofix CIH; intros U0 a1' a2 (a1 & Hae & Har); pstep.
      eapply refine_prov__mon; [exact (refine_prov_prov_te_l_step RR U0 a1 a2 Har a1' Hae) |].
      intros U1 b1' b2 [Hb | Hb]; [left; eapply paco3_mon; [exact Hb | intros ? ? ? []] | right; apply CIH, Hb]. }
    apply Hmain; exists t1; split; assumption.
  Qed.

  Definition rel_te_r {R1 R2 : Type} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2' : itree ProvBotE R2) : Prop :=
    exists t2, prov_te t2' t2 /\ refine_prov RR U t1 t2.

  Lemma refine_prov_prov_te_r_step {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U t1 t2 ->
    forall t2',
      prov_te t2' t2 ->
      refine_prov_ RR (upaco3 (refine_prov_ RR) (rel_te_r RR)) U t1 t2'.
  Proof using.
    intros Hrp; punfold Hrp.
    induction Hrp as [U t1 t2 Hstep_rp | U t1 m1 t2 Ht1 _ IH_rp | U t1 t2 m2 Ht2 _ IH_rp];
      intros t2' Hte.
    - unfold rp_step_body in Hstep_rp.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1] eqn:Hot1.
      + punfold Hte.
        induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te].
        * apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
          destruct (observe t2') as [x2' | |], (observe t2_) as [x2 | |]; try contradiction.
          subst x2'; exact Hstep_rp.
        * eapply RP_TauR; [exact Hot2' | exact IH_te].
      + punfold Hte.
        induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te].
        * apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
          destruct (observe t2') as [| m2' |], (observe t2_) as [| m2 |]; try contradiction.
          pclearbot; right; exists m2; split; assumption.
        * eapply RP_TauR; [exact Hot2' | exact IH_te].
      + destruct Hstep_rp as [Hub | [Hleft | Hboth]].
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; left; exact Hub.
        * apply RP_Step; unfold rp_step_body; rewrite Hot1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; exists t2; split; [exact Hte | exact Hleft].
        * punfold Hte.
          induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te].
          -- apply RP_Step; unfold rp_step_body, prov_te_step_body in *; rewrite Hot1.
             right; right.
             destruct (observe t2') as [| | X2' e2' k2'],
                      (observe t2_) as [| | X2 e2 k2]; try contradiction.
             destruct e1 as [p1 | b1], e2 as [p2 | b2], e2' as [p2' | b2'];
               cbn in *; try contradiction.
             ++ destruct p1, p2, p2'; intros p Hp.
                specialize (Hboth p Hp); specialize (Hstep_te p); pclearbot.
                right; exists (k2 p); split; assumption.
             ++ destruct Hboth as [HE12 HA12].
                destruct Hstep_te as (_ & HE22' & _ & HA22').
                split; [eapply EqE_bot_trans; eassumption |].
                intros a1 a2' Ha12'.
                destruct (EqA_bot_trans b1 b2 b2' a1 a2' HE12 HE22' Ha12') as [a2 [Ha12 Ha22']].
                specialize (HA12 a1 a2 Ha12); specialize (HA22' a2 a2' Ha22'); pclearbot.
                right; exists (k2 a2); split; assumption.
          -- eapply RP_TauR; [exact Hot2' | exact IH_te].
    - eapply RP_TauL; [exact Ht1 | apply (IH_rp t2' Hte)].
    - punfold Hte; revert Ht2.
      induction Hte as [t2' t2_ Hstep_te | t2' n2' t2_ Hot2' _ IH_te]; intros Ht2.
      + unfold prov_te_step_body in Hstep_te; rewrite Ht2 in Hstep_te.
        destruct (observe t2') as [| m2' |] eqn:Hot2'; try contradiction; pclearbot.
        eapply RP_TauR; [exact Hot2' | apply (IH_rp m2' Hstep_te)].
      + eapply RP_TauR; [exact Hot2' | apply (IH_te Ht2)].
  Qed.

  Lemma refine_prov_tau_expand_r {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_expand t2' t2 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1 t2'.
  Proof using.
    intros Hte Hrp; apply tau_expand_to_prov_te in Hte.
    assert (Hmain : forall U0 a1 a2', rel_te_r RR U0 a1 a2' -> refine_prov RR U0 a1 a2').
    { pcofix CIH; intros U0 a1 a2' (a2 & Hae & Har); pstep.
      eapply refine_prov__mon; [exact (refine_prov_prov_te_r_step RR U0 a1 a2 Har a2' Hae) |].
      intros U1 b1 b2' [Hb | Hb]; [left; eapply paco3_mon; [exact Hb | intros ? ? ? []] | right; apply CIH, Hb]. }
    apply Hmain; exists t2; split; assumption.
  Qed.

  Lemma refine_prov_tau_expand {R1 R2 : Type}
    (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_expand t1' t1 ->
    tau_expand t2' t2 ->
    refine_prov RR U t1 t2 ->
    refine_prov RR U t1' t2'.
  Proof using.
    intros H1 H2 Hrp.
    eapply refine_prov_tau_expand_l; [exact H1 |].
    eapply refine_prov_tau_expand_r; [exact H2 | exact Hrp].
  Qed.

  (** *** Syntactic & CFG Structural Lemmas for Stage 1 and Stage 2 *)

  Lemma in_defs_in_cfg_all_ids {T : Set} (c : CFG.cfg T) (bk : block T) (x : raw_id) :
    In bk (blks c) ->
    In x (full_block_defs bk) ->
    In x (cfg_all_ids c).
  Proof using.
    intros Hbk Hx; unfold cfg_all_ids; right.
    apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists bk; split; assumption.
  Qed.

  Lemma in_uses_in_cfg_all_ids {T : Set} (c : CFG.cfg T) (bk : block T) (x : raw_id) :
    In bk (blks c) ->
    In x (full_block_uses bk) ->
    In x (cfg_all_ids c).
  Proof using.
    intros Hbk Hx; unfold cfg_all_ids; right.
    apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right.
    apply in_flat_map; exists bk; split; assumption.
  Qed.

  Lemma m2r_phi_entry_uses_in_block {T : Set} (bk : block T)
    (pe : local_id * phi T * list (metadata T)) (x : raw_id) :
    In pe (blk_phis bk) ->
    In x (m2r_phi_entry_uses pe) ->
    In x (full_block_uses bk).
  Proof using.
    intros Hpe Hx; unfold full_block_uses; apply in_app_iff; left.
    apply in_flat_map; exists pe; split; [exact Hpe |].
    destruct pe as [[y ph] mds]; exact Hx.
  Qed.

  Lemma m2r_code_entry_uses_in_block {T : Set} (bk : block T)
    (im : instr_id * instr T * list (metadata T)) (x : raw_id) :
    In im (blk_code bk) ->
    In x (m2r_code_entry_uses im) ->
    In x (full_block_uses bk).
  Proof using.
    intros Him Hx; unfold full_block_uses; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists im; split; [exact Him |].
    destruct im as [[iid ins] mds]; exact Hx.
  Qed.

  Lemma m2r_term_entry_uses_in_block {T : Set} (bk : block T) (x : raw_id) :
    In x (m2r_term_entry_uses (blk_term bk)) ->
    In x (full_block_uses bk).
  Proof using.
    intros Hx; unfold full_block_uses; apply in_app_iff; right; apply in_app_iff; right.
    destruct (blk_term bk) as [[iid tm] mds]; exact Hx.
  Qed.

  Lemma find_promotable_in_init_code_inv
    (allow_calls : bool) (all_defs all_uses : list raw_id)
    (safe_locals : list local_id) (init_bid : block_id) (bks : ocfg dtyp)
    (b_init : block dtyp) (acc_pre rem : code dtyp)
    (pre_al : code dtyp) (al_ins : instr_id * instr dtyp * list (metadata dtyp))
    (post_al : code dtyp) (p : local_id) (dt : dtyp) :
    find_promotable_in_init_code allow_calls all_defs all_uses safe_locals
      init_bid bks b_init acc_pre rem = Some (pre_al, al_ins, post_al, p, dt) ->
    let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
    List.rev acc_pre ++ rem = pre_al ++ al_ins :: post_al /\
    (exists anns_al md_al,
       al_ins = (IId p, INSTR_Alloca dt anns_al, md_al) /\
       is_only_align_anns anns_al = true /\
       is_debug_or_file_md md_al = true) /\
    is_scalar_dtyp dt = true /\
    m2r_count_id p all_defs = 1%nat /\
    in_raw_ids p all_uses = true /\
    forallb (check_other_instr_for_slot allow_calls safe_no_p p) pre_al = true /\
    forallb (check_code_entry_for_slot allow_calls safe_no_p p dt) post_al = true /\
    in_raw_ids p (m2r_term_entry_uses (blk_term b_init)) = false /\
    m2r_non_invoke_term (snd (fst (blk_term b_init))) = true /\
    forallb (fun bk => if raw_id_eqb (blk_id bk) init_bid then true
                       else check_block_non_entry_for_slot allow_calls safe_no_p p dt bk) bks = true.
  Proof using.
    revert acc_pre; induction rem as [| im rem' IH]; intros acc_pre H;
      cbn [find_promotable_in_init_code] in H; [discriminate H |].
    match type of H with
    | context [match ?c with Some _ => _ | None => _ end] =>
        destruct c as [res |] eqn:Ecand
    end.
    - inversion H; subst; clear H.
      destruct im as [[iid ins] md_al]; destruct iid as [p0 |]; [| discriminate Ecand].
      destruct ins; try discriminate Ecand.
      match type of Ecand with
      | (if ?g then _ else _) = _ => destruct g eqn:Eg; [| discriminate Ecand]
      end.
      inversion Ecand; subst; clear Ecand.
      rewrite !andb_true_iff, !negb_true_iff, Nat.eqb_eq in Eg.
      destruct Eg as (((((((((Hsc & Hanns) & Hmd) & Hcnt) & Huse) & Hpre) & Hpost) & Hterm_p) & Hterm_ni) & Hbks).
      cbv zeta.
      split; [reflexivity |].
      split; [eexists _, _; split; [reflexivity | split; assumption] |].
      repeat split; assumption.
    - apply IH in H; cbv zeta in *.
      destruct H as (Hsplit & Hal & Hrest).
      split; [| split; [exact Hal | exact Hrest]].
      cbn [List.rev] in Hsplit; rewrite <- app_assoc in Hsplit; exact Hsplit.
  Qed.

  Lemma find_trailing_dead_alloca_in_code_inv
    (all_defs all_uses : list raw_id) (safe_locals : list local_id)
    (acc_pre rem : code dtyp)
    (pre_al : code dtyp) (al_ins : instr_id * instr dtyp * list (metadata dtyp))
    (post_al : code dtyp) (p : local_id) (dt : dtyp) :
    find_trailing_dead_alloca_in_code all_defs all_uses safe_locals acc_pre rem =
      Some (pre_al, al_ins, post_al, p, dt) ->
    let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
    List.rev acc_pre ++ rem = pre_al ++ al_ins :: post_al /\
    (exists anns_al md_al,
       al_ins = (IId p, INSTR_Alloca dt anns_al, md_al) /\
       is_only_align_anns anns_al = true /\
       is_debug_or_file_md md_al = true) /\
    is_scalar_dtyp dt = true /\
    m2r_count_id p all_defs = 1%nat /\
    in_raw_ids p all_uses = false /\
    forallb (check_other_instr_for_slot false safe_no_p p) pre_al = true /\
    forallb (check_no_alloca_or_call_instr safe_no_p) post_al = true.
  Proof using.
    revert acc_pre; induction rem as [| im rem' IH]; intros acc_pre H;
      cbn [find_trailing_dead_alloca_in_code] in H; [discriminate H |].
    destruct (find_trailing_dead_alloca_in_code all_defs all_uses safe_locals (im :: acc_pre) rem')
      as [later |] eqn:Elater.
    - inversion H; subst later; clear H.
      apply IH in Elater; cbv zeta in *.
      destruct Elater as (Hsplit & Hal & Hrest).
      split; [| split; [exact Hal | exact Hrest]].
      cbn [List.rev] in Hsplit; rewrite <- app_assoc in Hsplit; exact Hsplit.
    - destruct im as [[iid ins] md_al]; destruct iid as [p0 |]; [| discriminate H].
      destruct ins; try discriminate H.
      match type of H with
      | (if ?g then _ else _) = _ => destruct g eqn:Eg; [| discriminate H]
      end.
      inversion H; subst; clear H.
      rewrite !andb_true_iff, !negb_true_iff, Nat.eqb_eq in Eg.
      destruct Eg as ((((((Hsc & Hanns) & Hmd) & Hcnt) & Huse) & Hpre) & Hpost).
      cbv zeta.
      split; [reflexivity |].
      split; [eexists _, _; split; [reflexivity | split; assumption] |].
      repeat split; assumption.
  Qed.

  Lemma promote_first_in_defs_inv
    (interproc_safe : bool)
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    promote_first_in_defs interproc_safe defs = Some defs' ->
    exists pre df df' post,
      defs = pre ++ df :: post /\
      defs' = pre ++ df' :: post /\
      try_promote_slot_in_defn interproc_safe df = Some df'.
  Proof using.
    revert defs'; induction defs as [| d rest IH]; intros defs' H;
      cbn [promote_first_in_defs] in H; [discriminate H |].
    destruct (try_promote_slot_in_defn interproc_safe d) as [d' |] eqn:Ed.
    - inversion H; subst defs'; exists [], d, d', rest; repeat split; assumption.
    - destruct (promote_first_in_defs interproc_safe rest) as [rest' |] eqn:Erest;
        cbn in H; [| discriminate H].
      inversion H; subst defs'; clear H.
      destruct (IH rest' Logic.eq_refl) as (pre & df & df' & post & -> & -> & Htry).
      exists (d :: pre), df, df', post; repeat split; exact Htry.
  Qed.

  Lemma elim_first_dead_alloca_in_defs_inv
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    elim_first_dead_alloca_in_defs defs = Some defs' ->
    exists pre df df' post,
      defs = pre ++ df :: post /\
      defs' = pre ++ df' :: post /\
      try_elim_dead_alloca_in_defn df = Some df'.
  Proof using.
    revert defs'; induction defs as [| d rest IH]; intros defs' H;
      cbn [elim_first_dead_alloca_in_defs] in H; [discriminate H |].
    destruct (try_elim_dead_alloca_in_defn d) as [d' |] eqn:Ed.
    - inversion H; subst defs'; exists [], d, d', rest; repeat split; assumption.
    - destruct (elim_first_dead_alloca_in_defs rest) as [rest' |] eqn:Erest;
        cbn in H; [| discriminate H].
      inversion H; subst defs'; clear H.
      destruct (IH rest' Logic.eq_refl) as (pre & df & df' & post & -> & -> & Htry).
      exists (d :: pre), df, df', post; repeat split; exact Htry.
  Qed.

  Lemma rewrite_code_for_slot_fresh_inv
    (avoid0 : list raw_id) (p : local_id) (dt : dtyp)
    (cur_reg : local_id) (avoid : list raw_id) (cd : code dtyp)
    (cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id) :
    rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid') ->
    incl avoid0 avoid ->
    ~ In cur_reg avoid0 ->
    incl avoid avoid' /\ ~ In end_reg avoid0.
  Proof using.
    revert cur_reg avoid cd' end_reg avoid';
      induction cd as [| im rest IH];
      intros cur_reg avoid cd' end_reg avoid' Hrw Hinc Hcur;
      cbn [rewrite_code_for_slot] in Hrw.
    - inversion Hrw; subst; split; [apply incl_refl | exact Hcur].
    - destruct (is_promotable_load_of p dt im) as [dst |].
      + destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
        inversion Hrw; subst; eapply IH; eassumption.
      + destruct (is_promotable_store_of p dt im) as [val_exp |].
        * set (st_reg := fresh_name "m2r_st" avoid) in *.
          destruct (rewrite_code_for_slot p dt st_reg (st_reg :: avoid) rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst.
          assert (Hst : ~ In st_reg avoid0).
          { intros Hin0; exact (fresh_name_not_in "m2r_st" avoid (Hinc _ Hin0)). }
          assert (Hinc1 : incl avoid0 (st_reg :: avoid)) by (intros z Hz; right; apply Hinc, Hz).
          destruct (IH st_reg (st_reg :: avoid) rest' end_reg avoid' E Hinc1 Hst) as [Hav Her].
          split; [intros z Hz; apply Hav; right; exact Hz | exact Her].
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; eapply IH; eassumption.
  Qed.

  Lemma lookup_end_reg_in_nodup
    (end_map : list (block_id * local_id)) (bid : block_id) (r def_r : local_id) :
    NoDup (List.map fst end_map) ->
    In (bid, r) end_map ->
    lookup_end_reg end_map bid def_r = r.
  Proof using.
    induction end_map as [| [b0 r0] rest IH]; cbn [In List.map fst lookup_end_reg];
      [intros _ [] |].
    intros Hnd [Heq | Hin].
    - inversion Heq; subst b0 r0; rewrite raw_id_eqb_refl; reflexivity.
    - inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct (raw_id_eqb_spec b0 bid) as [-> | _].
      + exfalso; apply Hnin; apply in_map with (f := fst) in Hin; exact Hin.
      + apply IH; assumption.
  Qed.

  (** *** Expression & Dynamic-Value Size Measures and [withCall] Lifters *)

  Fixpoint m2r_exp_size {T : Set} (e : exp T) : nat :=
    let fix list_sz (l : list (T * exp T)) : nat :=
      match l with
      | [] => O
      | (_, ex) :: rest => S (m2r_exp_size ex + list_sz rest)
      end
    in
    match e with
    | EXP_Cstring elts | EXP_Struct elts | EXP_Packed_struct elts
    | EXP_Array elts | EXP_Vector elts => S (list_sz elts)
    | OP_IBinop _ _ e1 e2 | OP_ICmp _ _ _ e1 e2
    | OP_FBinop _ _ _ e1 e2 | OP_FCmp _ _ _ e1 e2 =>
        S (m2r_exp_size e1 + m2r_exp_size e2)
    | OP_Fneg _ (_, e1) | OP_Conversion _ _ e1 _
    | OP_ExtractValue (_, e1) _ | OP_Freeze (_, e1)
    | EXP_Splat (_, e1) => S (m2r_exp_size e1)
    | OP_GetElementPtr _ _ (_, ep) idxs =>
        S (m2r_exp_size ep + list_sz idxs)
    | OP_ExtractElement (_, e1) (_, e2)
    | OP_InsertValue (_, e1) (_, e2) _ =>
        S (m2r_exp_size e1 + m2r_exp_size e2)
    | OP_InsertElement (_, e1) (_, e2) (_, e3)
    | OP_ShuffleVector (_, e1) (_, e2) (_, e3)
    | OP_Select _ (_, e1) (_, e2) (_, e3) =>
        S (m2r_exp_size e1 + m2r_exp_size e2 + m2r_exp_size e3)
    | EXP_Metadata (METADATA_Const (_, ex)) => S (m2r_exp_size ex)
    | _ => 1%nat
    end.

  Lemma m2r_exp_size_pos {T : Set} (e : exp T) :
    (1 <= m2r_exp_size e)%nat.
  Proof using.
    destruct e; try (destruct m as [[] | | | | | |]); cbn; lia.
  Qed.

  Fixpoint m2r_dvalue_size (dv : @dvalue (@ParamsV IP IPT)) : nat :=
    let fix list_sz (l : list (@dvalue (@ParamsV IP IPT))) : nat :=
      match l with
      | [] => O
      | v :: rest => S (m2r_dvalue_size v + list_sz rest)
      end
    in
    match dv with
    | DVALUE_Base _ => 1%nat
    | DVALUE_Struct _ fields => S (list_sz fields)
    | DVALUE_Array _ elts => S (list_sz elts)
    end.

  Lemma m2r_dvalue_size_pos (dv : @dvalue (@ParamsV IP IPT)) :
    (1 <= m2r_dvalue_size dv)%nat.
  Proof using.
    destruct dv; cbn; lia.
  Qed.

  Lemma withCall_ret_eq {R} (x : R) :
    @withCall (@ParamsV IP IPT) R (Ret x) ≅ Ret x.
  Proof using.
    unfold withCall; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma withCall_bind_eq {A B}
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) :
    withCall (ITree.bind u k) ≅ ITree.bind (withCall u) (fun x => withCall (k x)).
  Proof using.
    unfold withCall; apply TranslateFacts.translate_bind.
  Qed.

  Lemma withCall_trigger_eq {X} (me : @MCFGEtop (@ParamsV IP IPT) X) :
    withCall (ITree.trigger me) ≅ ITree.trigger (inr1 me).
  Proof using.
    unfold withCall, ITree.trigger; rewrite unfold_translate; cbn.
    apply eqit_Vis; intros x; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma interp_mrec_trigger_inr1 {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) :
    interp_mrec (mrec_ctx ctx) (ITree.trigger (inr1 me)) ≅
    ITree.bind (ITree.trigger me) (fun x => Tau (Ret x)).
  Proof using.
    rewrite bind_trigger; unfold ITree.trigger.
    rewrite unfold_interp_mrec; cbn [_interp_mrec].
    apply eqit_Vis; intros x; rewrite interp_mrec_ret; reflexivity.
  Qed.

  Lemma tau_expand_cfg_withCall_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (Ret x)) s)
      (interp_mcfg_model (Ret x) s).
  Proof using.
    eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_ret_eq x)),
        interp_cfg_model_ret; reflexivity.
    - symmetry; apply interp_mcfg_model_ret.
    - apply tau_expand_refl.
  Qed.

  Lemma tau_expand_cfg_withCall_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    tau_expand (interp_cfg_model ctx (withCall u) s) (interp_mcfg_model u s) ->
    (forall s' a,
       tau_expand (interp_cfg_model ctx (withCall (k a)) s') (interp_mcfg_model (k a) s')) ->
    tau_expand
      (interp_cfg_model ctx (withCall (ITree.bind u k)) s)
      (interp_mcfg_model (ITree.bind u k) s).
  Proof using.
    intros Hu Hk; eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_bind_eq u k)),
        interp_cfg_model_bind; reflexivity.
    - symmetry; apply interp_mcfg_model_bind.
    - eapply tau_expand_bind; [exact Hu | intros [s' a]; apply Hk].
  Qed.

  Lemma tau_expand_cfg_withCall_trigger {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (ITree.trigger me)) s)
      (interp_mcfg_model (ITree.trigger me) s).
  Proof using.
    eapply tau_expand_obs_eq.
    - symmetry.
      rewrite (interp_cfg_model_obs_eq ctx _ _ s (withCall_trigger_eq me)).
      unfold interp_cfg_model.
      rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_trigger_inr1 ctx me)).
      apply interp_mcfg_model_bind.
    - rewrite <- (Eqit.bind_ret_r (interp_mcfg_model (ITree.trigger me) s)) at 1; reflexivity.
    - eapply tau_expand_bind; [apply tau_expand_refl |].
      intros [s' x]; eapply tau_expand_obs_eq.
      + symmetry; rewrite interp_mcfg_model_tau, interp_mcfg_model_ret; reflexivity.
      + reflexivity.
      + pstep; apply TE_TauL, TE_Ret.
  Qed.

  Lemma tau_expand_cfg_withCall_EOU {A}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (m : EOU A) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (EOU_to_itree m)) s)
      (interp_mcfg_model (EOU_to_itree m) s).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - unfold raiseOOM, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - unfold raiseUB, trigger_cast; eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_trigger | intros ? []].
    - apply tau_expand_cfg_withCall_ret.
  Qed.

  Lemma tau_expand_cfg_withCall_map_monad {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A)
    (Hf : forall a s0,
            In a xs ->
            tau_expand (interp_cfg_model ctx (withCall (f a)) s0) (interp_mcfg_model (f a) s0)) :
    forall s,
      tau_expand
        (interp_cfg_model ctx (withCall (map_monad f xs)) s)
        (interp_mcfg_model (map_monad f xs) s).
  Proof using.
    induction xs as [| a xs' IH]; intros s; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply tau_expand_cfg_withCall_ret.
    - eapply tau_expand_cfg_withCall_bind; [apply Hf; left; reflexivity |].
      intros s1 b; eapply tau_expand_cfg_withCall_bind.
      + apply IH; intros a' s0 Ha'; apply Hf; right; exact Ha'.
      + intros s2 bs; apply tau_expand_cfg_withCall_ret.
  Qed.

  Lemma tau_expand_cfg_withCall_convert
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (convert ct t_from dv t_to)) s)
      (interp_mcfg_model (convert ct t_from dv t_to) s).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply tau_expand_cfg_withCall_ret |].
      destruct (@bit_sizeof_dtyp SizeofV t_from =? @bit_sizeof_dtyp SizeofV t_to)%N.
      + apply tau_expand_cfg_withCall_EOU.
      + apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
    - apply tau_expand_cfg_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
  Qed.

  Lemma tau_expand_cfg_withCall_freeze_base
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (freeze_base dt db)) s)
      (interp_mcfg_model (freeze_base dt db) s).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | sz bv | |].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply tau_expand_cfg_withCall_bind;
          [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply tau_expand_cfg_withCall_bind;
          [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [Monads.bind Monads.ret Monad_itree].
        * eapply tau_expand_cfg_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
          -- intros s' x; apply tau_expand_cfg_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
            eapply tau_expand_cfg_withCall_bind;
            [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_cfg_withCall_bind;
        [apply tau_expand_cfg_withCall_ret | intros ? ?; apply tau_expand_cfg_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
  Qed.

  Lemma tau_expand_cfg_withCall_freeze
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (withCall (freeze dt dv)) s)
      (interp_mcfg_model (freeze dt dv) s).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt s Hle; induction sz as [| sz IH]; intros dv dt s Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply tau_expand_cfg_withCall_freeze_base.
      + destruct dt as [| | p' dts];
          try apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply tau_expand_cfg_withCall_bind; [| intros ? ?; apply tau_expand_cfg_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ( (fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert dts s Hfld; induction fields as [| v vs IHf]; intros [| t ts] s Hfld acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply tau_expand_cfg_withCall_ret.
        * apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        * apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        * eapply tau_expand_cfg_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHf; lia.
      + destruct dt as [| v' sz_n t |];
          try apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply tau_expand_cfg_withCall_bind; [| intros ? ?; apply tau_expand_cfg_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert s Helt; induction elts as [| v vs IHe]; intros s Helt acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply tau_expand_cfg_withCall_ret.
        * eapply tau_expand_cfg_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHe; lia.
  Qed.

  Lemma tau_expand_cfg_withCall_denote_exp
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (s : FusedS) :
    tau_expand
      (interp_cfg_model ctx (denote_exp' top e) s)
      (interp_mcfg_model (denote_exp top e) s).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e s Hle; induction sz as [| sz IH]; intros top e s Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)) s0,
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          tau_expand
            (interp_cfg_model ctx (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts)) s0)
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s0)).
      { intros elts s0 Helts; apply tau_expand_cfg_withCall_map_monad.
        intros [dt0 ex0] s1 Hin.
        apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [exact Hin | lia]]. }
      destruct e; cbn [denote_exp Monads.bind Monads.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_cfg_withCall_trigger.
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + destruct b; apply tau_expand_cfg_withCall_ret.
      + apply tau_expand_cfg_withCall_ret.
      + destruct top as [t |]; [apply tau_expand_cfg_withCall_EOU | apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _)].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + apply tau_expand_cfg_withCall_ret.
      + apply tau_expand_cfg_withCall_ret.
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist fields s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply tau_expand_cfg_withCall_EOU |].
        intros s1 []; eapply tau_expand_cfg_withCall_bind; [apply (Hlist fields s1 Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct op as [dt1 op1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + eapply tau_expand_cfg_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_cfg_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 vptr; eapply tau_expand_cfg_withCall_bind; [apply Hlist; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 v1; eapply tau_expand_cfg_withCall_bind.
        * eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
        * intros s2 elt_v; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 v2; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 vc; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 vv1; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_freeze].
      + apply (tau_expand_cfg_withCall_EOU ctx (raise_error _) _).
      + destruct md as [[dt1 ex1] | | | | | |];
          try apply tau_expand_cfg_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply tau_expand_cfg_withCall_bind; [apply tau_expand_cfg_withCall_EOU |].
        intros s1 [sz_v t_v]; eapply tau_expand_cfg_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_cfg_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast; apply tau_expand_cfg_withCall_trigger.
  Qed.

  Definition mcfg_inr_exc {R : Type}
    (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R)) :=
    ITree.bind (interp_mcfg_model u s) (fun '(s', r) => Ret (s', inr r)).

  Lemma tau_expand_exc_withCall_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (Ret x)) s)
      (mcfg_inr_exc (Ret x) s).
  Proof using.
    unfold mcfg_inr_exc; eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_ret_eq x)),
        interp_cfg_exc_ret; reflexivity.
    - symmetry; rewrite interp_mcfg_model_ret, Eqit.bind_ret_l; reflexivity.
    - apply tau_expand_refl.
  Qed.

  Lemma tau_expand_exc_withCall_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    tau_expand (interp_cfg_exc ctx (withCall u) s) (mcfg_inr_exc u s) ->
    (forall s' a,
       tau_expand (interp_cfg_exc ctx (withCall (k a)) s') (mcfg_inr_exc (k a) s')) ->
    tau_expand
      (interp_cfg_exc ctx (withCall (ITree.bind u k)) s)
      (mcfg_inr_exc (ITree.bind u k) s).
  Proof using.
    intros Hu Hk; unfold mcfg_inr_exc in *.
    eapply tau_expand_obs_eq.
    - symmetry; rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_bind_eq u k)),
        interp_cfg_exc_bind; reflexivity.
    - symmetry; rewrite interp_mcfg_model_bind, Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' a] ? <-; symmetry; rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind.
      eapply tau_expand_obs_eq.
      + reflexivity.
      + symmetry; rewrite Eqit.bind_bind; reflexivity.
      + eapply tau_expand_bind; [exact Hu |].
        intros [s' [ex | a]].
        * eapply tau_expand_obs_eq; [reflexivity | symmetry; apply Eqit.bind_ret_l | apply tau_expand_refl].
        * eapply tau_expand_obs_eq; [reflexivity | symmetry; apply Eqit.bind_ret_l | apply Hk].
  Qed.

  Lemma tau_expand_exc_withCall_trigger {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hne : exc_of_event (inr1 me) = None) :
    tau_expand
      (interp_cfg_exc ctx (withCall (ITree.trigger me)) s)
      (mcfg_inr_exc (ITree.trigger me) s).
  Proof using.
    unfold mcfg_inr_exc; eapply tau_expand_obs_eq.
    - symmetry.
      rewrite (interp_cfg_exc_obs_eq ctx _ _ s (withCall_trigger_eq me)).
      exact (interp_cfg_exc_trigger_non_exc ctx (inr1 me) s Hne).
    - reflexivity.
    - eapply tau_expand_bind.
      + eapply tau_expand_obs_eq;
          [apply (interp_cfg_model_obs_eq ctx _ _ s (withCall_trigger_eq me))
          | reflexivity
          | apply tau_expand_cfg_withCall_trigger].
      + intros [s' y]; pstep; apply TE_TauL, TE_Ret.
  Qed.

  Lemma tau_expand_exc_withCall_EOU {A}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (m : EOU A) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (EOU_to_itree m)) s)
      (mcfg_inr_exc (EOU_to_itree m) s).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - unfold raiseOOM, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - unfold raiseUB, trigger_cast; eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_trigger; reflexivity | intros ? []].
    - apply tau_expand_exc_withCall_ret.
  Qed.

  Lemma tau_expand_exc_withCall_map_monad {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A)
    (Hf : forall a s0,
            In a xs ->
            tau_expand (interp_cfg_exc ctx (withCall (f a)) s0) (mcfg_inr_exc (f a) s0)) :
    forall s,
      tau_expand
        (interp_cfg_exc ctx (withCall (map_monad f xs)) s)
        (mcfg_inr_exc (map_monad f xs) s).
  Proof using.
    induction xs as [| a xs' IH]; intros s; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply tau_expand_exc_withCall_ret.
    - eapply tau_expand_exc_withCall_bind; [apply Hf; left; reflexivity |].
      intros s1 b; eapply tau_expand_exc_withCall_bind.
      + apply IH; intros a' s0 Ha'; apply Hf; right; exact Ha'.
      + intros s2 bs; apply tau_expand_exc_withCall_ret.
  Qed.

  Lemma tau_expand_exc_withCall_convert
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (convert ct t_from dv t_to)) s)
      (mcfg_inr_exc (convert ct t_from dv t_to) s).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply tau_expand_exc_withCall_ret |].
      destruct (@bit_sizeof_dtyp SizeofV t_from =? @bit_sizeof_dtyp SizeofV t_to)%N.
      + apply tau_expand_exc_withCall_EOU.
      + apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
    - apply tau_expand_exc_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast;
        apply tau_expand_exc_withCall_trigger; reflexivity.
  Qed.

  Lemma tau_expand_exc_withCall_freeze_base
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (freeze_base dt db)) s)
      (mcfg_inr_exc (freeze_base dt db) s).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | sz bv | |].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply tau_expand_exc_withCall_bind;
          [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply tau_expand_exc_withCall_bind;
          [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [Monads.bind Monads.ret Monad_itree].
        * eapply tau_expand_exc_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast;
               apply tau_expand_exc_withCall_trigger; reflexivity.
          -- intros s' x; apply tau_expand_exc_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
            eapply tau_expand_exc_withCall_bind;
            [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply tau_expand_exc_withCall_bind;
        [apply tau_expand_exc_withCall_ret | intros ? ?; apply tau_expand_exc_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast;
        apply tau_expand_exc_withCall_trigger; reflexivity.
  Qed.

  Lemma tau_expand_exc_withCall_freeze
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (withCall (freeze dt dv)) s)
      (mcfg_inr_exc (freeze dt dv) s).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt s Hle; induction sz as [| sz IH]; intros dv dt s Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply tau_expand_exc_withCall_freeze_base.
      + destruct dt as [| | p' dts];
          try apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply tau_expand_exc_withCall_bind; [| intros ? ?; apply tau_expand_exc_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert dts s Hfld; induction fields as [| v vs IHf]; intros [| t ts] s Hfld acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply tau_expand_exc_withCall_ret.
        * apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        * apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        * eapply tau_expand_exc_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHf; lia.
      + destruct dt as [| v' sz_n t |];
          try apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply tau_expand_exc_withCall_bind; [| intros ? ?; apply tau_expand_exc_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert s Helt; induction elts as [| v vs IHe]; intros s Helt acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply tau_expand_exc_withCall_ret.
        * eapply tau_expand_exc_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros s1 v'; apply IHe; lia.
  Qed.

  Lemma tau_expand_exc_withCall_denote_exp
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (s : FusedS) :
    tau_expand
      (interp_cfg_exc ctx (denote_exp' top e) s)
      (mcfg_inr_exc (denote_exp top e) s).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e s Hle; induction sz as [| sz IH]; intros top e s Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)) s0,
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          tau_expand
            (interp_cfg_exc ctx (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts)) s0)
            (mcfg_inr_exc (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s0)).
      { intros elts s0 Helts; apply tau_expand_exc_withCall_map_monad.
        intros [dt0 ex0] s1 Hin.
        apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [exact Hin | lia]]. }
      destruct e; cbn [denote_exp Monads.bind Monads.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_exc_withCall_trigger; reflexivity.
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + destruct b; apply tau_expand_exc_withCall_ret.
      + apply tau_expand_exc_withCall_ret.
      + destruct top as [t |]; [apply tau_expand_exc_withCall_EOU | apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _)].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + apply tau_expand_exc_withCall_ret.
      + apply tau_expand_exc_withCall_ret.
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist fields s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply tau_expand_exc_withCall_EOU |].
        intros s1 []; eapply tau_expand_exc_withCall_bind; [apply (Hlist fields s1 Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply (Hlist elts s Hle) | intros ? ?; apply tau_expand_exc_withCall_ret].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct op as [dt1 op1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + eapply tau_expand_exc_withCall_bind; [apply IH; lia | intros ? ?; apply tau_expand_exc_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 vptr; eapply tau_expand_exc_withCall_bind; [apply Hlist; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros s1 v1; eapply tau_expand_exc_withCall_bind.
        * eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
        * intros s2 elt_v; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 v2; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 v1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s1 vc; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros s2 vv1; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_freeze].
      + apply (tau_expand_exc_withCall_EOU ctx (raise_error _) _).
      + destruct md as [[dt1 ex1] | | | | | |];
          try apply tau_expand_exc_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply tau_expand_exc_withCall_bind; [apply tau_expand_exc_withCall_EOU |].
        intros s1 [sz_v t_v]; eapply tau_expand_exc_withCall_bind; [apply IH; cbn in Hle; lia | intros ? ?; apply tau_expand_exc_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast;
          apply tau_expand_exc_withCall_trigger; reflexivity.
  Qed.

  (** *** Parametric Expression Simulation Across All Memory Invariants *)

  Lemma refine_mcfg_gread_same_g
    (gid : raw_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom, genv_safe P_unprom g -> is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_mcfg_model (gread gid) s1)
      (interp_mcfg_model (gread gid) s2).
  Proof using.
    cbv zeta; unfold gread, Subevent.trigger; try unfold trigger_cast.
    destruct (Maps.lookup gid g) as [v |] eqn:Elk.
    - assert (H1 : interp_vellvm_prov_h (subevent _ (GlobalRead gid)) (σ1, (ls1, g)) ≅ Ret ((σ1, (ls1, g)), v)).
      { unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
          cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
        rewrite Elk, !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity. }
      assert (H2 : interp_vellvm_prov_h (subevent _ (GlobalRead gid)) (σ2, (ls2, g)) ≅ Ret ((σ2, (ls2, g)), v)).
      { unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
          cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
        rewrite Elk, !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_tau_star_l; [eapply tau_star_mcfg_det; [reflexivity | exact H1] |].
      eapply refine_prov_tau_star_r; [eapply tau_star_mcfg_det; [reflexivity | exact H2] |].
      apply refine_prov_ret.
      repeat split; [intros P_unprom Hg; exact (Hg gid v Elk)].
    - eapply refine_prov_obs_eq.
      + symmetry; apply interp_mcfg_model_non_intr; reflexivity.
      + symmetry; apply interp_mcfg_model_non_intr; reflexivity.
      + unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, raise, trigger_cast, ITree.trigger, lift_bot_prov;
          cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
        rewrite Elk.
        pstep; apply RP_Step; unfold rp_step_body.
        rewrite !observe_bind, !unfold_translate; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_lread_same_opt
    (lid : local_id) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g1 g2 : @global_env (@ParamsV IP IPT))
    (Hlk_eq : Maps.lookup lid (stack_vars sf1) = Maps.lookup lid (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g1)) in
    let s2 := (σ2, ((sf2, fstk2), g2)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         Maps.lookup lid (stack_vars sf2) = Some v2)
      U
      (interp_mcfg_model (lread lid) s1)
      (interp_mcfg_model (lread lid) s2).
  Proof using.
    cbv zeta; unfold lread, Subevent.trigger; try unfold trigger_cast.
    destruct (Maps.lookup lid (stack_vars sf2)) as [v |] eqn:Elk2.
    - assert (Elk1 : Maps.lookup lid (stack_vars sf1) = Some v) by congruence.
      eapply refine_prov_tau_star_l.
      + eapply tau_star_mcfg_det; [reflexivity | apply (fused_local_prov_read_some lid v (σ1, ((sf1, fstk1), g1)) Elk1)].
      + eapply refine_prov_tau_star_r.
        * eapply tau_star_mcfg_det; [reflexivity | apply (fused_local_prov_read_some lid v (σ2, ((sf2, fstk2), g2)) Elk2)].
        * apply refine_prov_ret; repeat split; exact Elk2.
    - assert (Elk1 : Maps.lookup lid (stack_vars sf1) = None) by congruence.
      destruct (fused_local_prov_read_none lid (σ1, ((sf1, fstk1), g1)) Elk1) as (msg1 & k1 & H1).
      destruct (fused_local_prov_read_none lid (σ2, ((sf2, fstk2), g2)) Elk2) as (msg2 & k2 & H2).
      eapply refine_prov_obs_eq.
      + symmetry; rewrite interp_mcfg_model_non_intr by reflexivity.
        unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        rewrite H1, Eqit.bind_vis; reflexivity.
      + symmetry; rewrite interp_mcfg_model_non_intr by reflexivity.
        unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        rewrite H2, Eqit.bind_vis; reflexivity.
      + pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_draw_sync
    (dt : dtyp) (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (draw dt) s1)
      (interp_mcfg_model (draw dt) s2).
  Proof using.
    unfold draw, Subevent.trigger; try unfold trigger_cast.
    destruct (default_dvalue_of_dtyp dt) as [msg | msg | msg | dv] eqn:Edef.
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, !unfold_translate; cbn; left; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, !unfold_translate; cbn; left; reflexivity.
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_non_intr; reflexivity
        | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
      unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree].
      unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, !unfold_translate; cbn;
        right; right; split; [exact I | intros [] [] _].
    - assert (Hd1 : interp_vellvm_prov_h (subevent _ (Draw dt)) s1 ≅ Ret (s1, dv)).
      { unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree Monads.ret Monad_itree].
        rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
      assert (Hd2 : interp_vellvm_prov_h (subevent _ (Draw dt)) s2 ≅ Ret (s2, dv)).
      { unfold interp_vellvm_prov_h; cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_draw_prov, handle_draw; rewrite Edef; cbn [EOU_to_itree Monads.ret Monad_itree].
        rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_tau_star_l; [eapply tau_star_mcfg_det; [reflexivity | exact Hd1] |].
      eapply refine_prov_tau_star_r; [eapply tau_star_mcfg_det; [reflexivity | exact Hd2] |].
      apply refine_prov_ret; repeat split.
  Qed.

  Lemma refine_mcfg_convert_sync
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp)
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (convert ct t_from dv t_to) s1)
      (interp_mcfg_model (convert ct t_from dv t_to) s2).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to).
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split].
      + destruct (@bit_sizeof_dtyp SizeofV t_from =? @bit_sizeof_dtyp SizeofV t_to)%N.
        * eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split].
        * apply refine_mcfg_raise_both.
    - eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split].
    - destruct s1 as [σ1 rest1], s2 as [σ2 rest2].
      unfold conv, Subevent.trigger; try unfold trigger_cast.
      apply refine_mcfg_memory_event.
      cbn [handle_memoryM].
      eapply refine_prov_weaken; [apply convert_impure_id_sync |].
      intros U' [σ1' r1] [σ2' r2] (-> & -> & -> & ->); repeat split.
  Qed.

  Lemma refine_mcfg_freeze_sync
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT))
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2)
      U
      (interp_mcfg_model (freeze dt dv) s1)
      (interp_mcfg_model (freeze dt dv) s2).
  Proof using.
    assert (Hret_sync :
      forall A (x : A) U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (Ret x) a1) (interp_mcfg_model (Ret x) a2)).
    { intros A x U0 a1 a2; eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split]. }
    assert (Hfmap_ret :
      forall db0 U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (DVALUE_Base <$> Monads.ret db0) a1)
          (interp_mcfg_model (DVALUE_Base <$> Monads.ret db0) a2)).
    { intros db0 U0 a1 a2; unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree.
      eapply refine_mcfg_model_bind; [apply Hret_sync | intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync]. }
    assert (Hbase :
      forall dt0 db0 U0 a1 a2,
        refine_prov (fun U' '(s1', r1) '(s2', r2) => U' = U0 /\ s1' = a1 /\ s2' = a2 /\ r1 = r2) U0
          (interp_mcfg_model (freeze_base dt0 db0) a1)
          (interp_mcfg_model (freeze_base dt0 db0) a2)).
    { intros dt0 db0 U0 a1 a2; unfold freeze_base; destruct db0 as [| | | | | sz_b bv | |];
        try apply Hfmap_ret; [| apply refine_mcfg_draw_sync].
      destruct bv as [| | bits]; try apply Hfmap_ret.
      destruct (existsb is_poison_bit bits); [| apply Hfmap_ret].
      cbn [Monads.bind Monads.ret Monad_itree].
      eapply refine_mcfg_model_bind; [apply refine_mcfg_draw_sync | intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync]. }
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt U s1 s2 Hle; induction sz as [| sz IH]; intros dv dt U s1 s2 Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply Hbase.
      + destruct dt as [| | p' dts]; try apply refine_mcfg_raise_both.
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply refine_mcfg_model_bind; [| intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert dts U s1 s2 Hfld; induction fields as [| v vs IHf]; intros [| t ts] U s1 s2 Hfld acc;
          cbn [Monads.bind Monads.ret Monad_itree];
          try apply refine_mcfg_raise_both; [apply Hret_sync |].
        eapply refine_mcfg_model_bind.
        * fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
        * intros ? ? ? ? ? _ (-> & -> & -> & ->); apply IHf; lia.
      + destruct dt as [| v' sz_n t |]; try apply refine_mcfg_raise_both.
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply refine_mcfg_model_bind; [| intros ? ? ? ? ? _ (-> & -> & -> & ->); apply Hret_sync].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert U s1 s2 Helt; induction elts as [| v vs IHe]; intros U s1 s2 Helt acc;
          cbn [Monads.bind Monads.ret Monad_itree]; [apply Hret_sync |].
        eapply refine_mcfg_model_bind.
        * fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
        * intros ? ? ? ? ? _ (-> & -> & -> & ->); apply IHe; lia.
  Qed.

  Lemma denote_exp_mcfg_sim
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_mcfg_model (denote_exp top e) s1)
      (interp_mcfg_model (denote_exp top e) s2).
  Proof using.
    cbv zeta.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e U σ1 σ2 sf1 sf2 fstk1 fstk2 Hle Hvars;
      induction sz as [| sz IH];
      intros top e U σ1 σ2 sf1 sf2 fstk1 fstk2 Hle Hvars.
    - pose proof (m2r_exp_size_pos e); lia.
    - set (s1 := (σ1, ((sf1, fstk1), g))).
      set (s2 := (σ2, ((sf2, fstk2), g))).
      assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)),
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          (forall x,
             In x ((fix go l := match l with [] => [] | (_, ex) :: r => full_exp_uses ex ++ go r end) elts) ->
             Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) ->
          refine_prov
            (fun U' '(s1', vs1) '(s2', vs2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ vs1 = vs2)
            U
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s1)
            (interp_mcfg_model (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts) s2)).
      { induction elts as [| [dt0 ex0] rest IHr]; intros Hsz0 Hv0;
          cbn [map_monad Monads.bind Monads.ret Monad_itree].
        - eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split].
        - eapply refine_mcfg_model_bind.
          + apply IH; [lia | intros x Hx; apply Hv0, in_app_iff; left; exact Hx].
          + intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
            eapply refine_mcfg_model_bind.
            * apply IHr; [lia | intros x Hx; apply Hv0, in_app_iff; right; exact Hx].
            * intros ? ? ? ? ? _ (-> & -> & -> & <-).
              eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split]. }
      assert (Hnosafe :
        forall v : @dvalue (@ParamsV IP IPT),
          m2r_safe_ptr_exp = m2r_safe_ptr_exp ->
          (forall safe_locals, m2r_safe_ptr_exp safe_locals e = false) ->
          forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v).
      { intros v _ Hfalse ? safe_locals _ _ Htrue; rewrite (Hfalse safe_locals) in Htrue; discriminate Htrue. }
      destruct e; cbn [denote_exp Monads.bind Monads.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id].
        * eapply refine_prov_weaken; [apply refine_mcfg_gread_same_g |].
          intros U' [s1' v1] [s2' v2] (-> & -> & -> & -> & Hsafe).
          repeat split; intros P_unprom safe_locals Hg _ _; apply Hsafe, Hg.
        * eapply refine_prov_weaken.
          -- apply refine_mcfg_lread_same_opt; apply Hvars; left; reflexivity.
          -- intros U' [s1' v1] [s2' v2] (-> & -> & -> & -> & Hlk2).
             repeat split; intros P_unprom safe_locals _ Hloc Hsafe.
             cbn [m2r_safe_ptr_exp] in Hsafe; apply in_raw_ids_spec in Hsafe.
             exact (Hloc lid v2 Hsafe Hlk2).
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + destruct b; eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate.
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
        apply refine_prov_ret; repeat split; intros; apply null_safe_ptr_dvalue.
      + destruct top as [t |]; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate] | apply refine_mcfg_raise_both].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
        apply refine_prov_ret; repeat split; intros; apply poison_safe_ptr_dvalue.
      + eapply refine_mcfg_model_bind; [apply (Hlist fields Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros [] ? <-; exact Logic.eq_refl] |].
        intros ? ? [] ? [] _ <-.
        eapply refine_mcfg_model_bind; [apply (Hlist fields Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply (Hlist elts Hle Hvars) | intros ? ? ? ? ? _ (-> & -> & -> & <-); eapply refine_prov_obs_eq; try (symmetry; apply interp_mcfg_model_ret); apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct op as [dt1 op1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [lia | intros x Hx; apply Hvars, in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + eapply refine_mcfg_model_bind; [apply IH; [lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_weaken; [apply refine_mcfg_convert_sync | intros ? [? ?] [? ?] (-> & -> & -> & ->); repeat split; intros; discriminate].
      + destruct ptrval as [dt2 ptr_e].
        eapply refine_mcfg_model_bind.
        * apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx].
        * intros ? ? vptr ? ? _ (-> & -> & -> & <- & Hptr_safe).
          eapply refine_mcfg_model_bind.
          -- apply Hlist; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx].
          -- intros ? ? vs ? ? _ (-> & -> & -> & <-).
             destruct (eval_gep flags t vptr vs) as [msg | msg | msg | res] eqn:Egep; cbn [EOU_to_itree].
             ++ apply refine_mcfg_raise_both.
             ++ apply refine_mcfg_raiseOOM_l.
             ++ apply refine_mcfg_raiseUB_l.
             ++ eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
                apply refine_prov_ret; repeat split.
                intros P_unprom safe_locals Hg Hloc Hsafe; cbn [m2r_safe_ptr_exp] in Hsafe.
                eapply eval_gep_safe_ptr; [exact (Hptr_safe P_unprom safe_locals Hg Hloc Hsafe) | exact Egep].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind.
        * eapply refine_mcfg_model_bind;
            [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx]
            | intros ? ? ? ? ? _ (-> & -> & -> & <- & _); eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split]].
        * intros ? ? ? ? ? _ (-> & -> & -> & <-).
          eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
          intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
          eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; exact Hx] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; repeat split; intros; discriminate].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; left; exact Hx] |].
        intros ? ? vc ? ? _ (-> & -> & -> & <- & _).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; left; exact Hx] |].
        intros ? ? vv1 ? ? _ (-> & -> & -> & <- & Hs1).
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | intros x Hx; apply Hvars; cbn [full_exp_uses]; apply in_app_iff; right; apply in_app_iff; right; exact Hx] |].
        intros ? ? vv2 ? ? _ (-> & -> & -> & <- & Hs2).
        destruct (eval_select vc dt2 vv1 vv2) as [msg | msg | msg | res] eqn:Esel; cbn [EOU_to_itree].
        * apply refine_mcfg_raise_both.
        * apply refine_mcfg_raiseOOM_l.
        * apply refine_mcfg_raiseUB_l.
        * eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
          apply refine_prov_ret; repeat split.
          intros P_unprom safe_locals Hg Hloc Hsafe; cbn [m2r_safe_ptr_exp] in Hsafe.
          rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hs_e2 Hs_e3].
          eapply eval_select_safe_ptr;
            [exact (Hs1 P_unprom safe_locals Hg Hloc Hs_e2)
            | exact (Hs2 P_unprom safe_locals Hg Hloc Hs_e3)
            | exact Esel].
      + destruct v as [dt1 e1]; eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_weaken; [apply refine_mcfg_freeze_sync | intros ? [? ?] [? ?] (-> & -> & -> & ->); repeat split; intros; discriminate].
      + apply refine_mcfg_raise_both.
      + destruct md as [[dt1 ex1] | | | | | |];
          try (eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate]).
        eapply refine_prov_weaken; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? [? ?] [? ?] (-> & -> & -> & -> & _); repeat split; intros; discriminate.
      + destruct elt as [dt1 e1].
        eapply refine_mcfg_model_bind; [eapply refine_mcfg_EOU; [apply refine_EOU_refl | intros ? ? <-; exact Logic.eq_refl] |].
        intros ? ? [sz_v t_v] ? ? _ <-.
        eapply refine_mcfg_model_bind; [apply IH; [cbn in Hle; lia | exact Hvars] |].
        intros ? ? ? ? ? _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret | apply refine_prov_ret; repeat split; intros; discriminate].
      + eapply refine_prov_weaken; [apply refine_mcfg_gread_same_g |].
        intros ? [? ?] [? ?] (-> & -> & -> & -> & _); repeat split; intros; discriminate.
  Qed.

  Lemma denote_exp_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (fun U' '(s1', v1) '(s2', v2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
         (forall P_unprom safe_locals,
            genv_safe P_unprom g ->
            safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
            m2r_safe_ptr_exp safe_locals e = true ->
            is_safe_ptr_dvalue P_unprom v2))
      U
      (interp_cfg_model ctx1 (denote_exp' top e) s1)
      (interp_cfg_model ctx2 (denote_exp' top e) s2).
  Proof using.
    cbv zeta.
    eapply refine_prov_tau_expand;
      [apply tau_expand_cfg_withCall_denote_exp
      | apply tau_expand_cfg_withCall_denote_exp
      | apply denote_exp_mcfg_sim, Hvars].
  Qed.

  Lemma denote_exp_cfg_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (top : option dtyp) (e : exp dtyp) (U : list N)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (full_exp_uses e) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' v1 v2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2 /\
            (forall P_unprom safe_locals,
               genv_safe P_unprom g ->
               safe_locals_env P_unprom safe_locals (stack_vars sf2) ->
               m2r_safe_ptr_exp safe_locals e = true ->
               is_safe_ptr_dvalue P_unprom v2)))
      U
      (interp_cfg_exc ctx1 (denote_exp' top e) s1)
      (interp_cfg_exc ctx2 (denote_exp' top e) s2).
  Proof using.
    cbv zeta.
    eapply refine_prov_tau_expand;
      [apply tau_expand_exc_withCall_denote_exp
      | apply tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    eapply PassCommon.refine_prov_bind; [apply denote_exp_mcfg_sim, Hvars |].
    intros U' [s1' v1] [s2' v2] _ Hpost.
    apply refine_prov_ret; exact Hpost.
  Qed.


  (** ** 3G. Exception-Level Memory Lifters, Loop Splitting & Pass-1 Specs *)

  Lemma refine_cfg_exc_raise_both {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (raise msg1) s1)
      (interp_cfg_exc ctx2 (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast; eapply refine_cfg_exc_bind.
    - eapply refine_cfg_exc_trigger with (RA := fun _ _ _ (v1 : void) (_ : void) => match v1 with end);
        [reflexivity | reflexivity |].
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_non_intr; reflexivity
        | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
      cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_trigger_prov, ITree.trigger.
      eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
      pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
    - intros _ _ [] _ _ _ _.
  Qed.

  Lemma refine_cfg_exc_raiseOOM_l {A1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + A1) -> R2 -> Prop)
    (U : list N) (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_exc ctx1 (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, interp_cfg_exc.
    assert (Hoom : run_exc (ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg))))
                              (fun v : void => match v with end))
                    ≅ ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg))))
                        (fun v : void => match v with end)).
    { rewrite run_exc_bind_eq, (run_exc_trigger_non_exc _ Logic.eq_refl), Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hoom) | reflexivity |].
    apply (refine_cfg_raiseOOM_l ctx1 RR U msg s1 t2).
  Qed.

  Lemma refine_cfg_exc_raiseLLVM_both {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (x1 x2 : @exc (@ParamsV IP IPT)) (s1 s2 : FusedS) :
    RExc U s1 s2 x1 x2 ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (raiseLLVM x1) s1)
      (interp_cfg_exc ctx2 (raiseLLVM x2) s2).
  Proof using.
    intros Hx.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_raiseLLVM
      | symmetry; apply interp_cfg_exc_raiseLLVM |].
    apply refine_prov_ret; exact Hx.
  Qed.

  Lemma refine_cfg_exc_memory_event {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> X1 -> X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RA U' (σ1', rest1) (σ2', rest2) x1 x2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_cfg_exc ctx2 (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_cfg_exc_trigger; [reflexivity | reflexivity |].
    apply refine_cfg_memory_event, Hmem.
  Qed.

  Lemma refine_cfg_exc_memory_event_l {X1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + X1) -> R2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (U : list N) (σ1 : state)
    (rest1 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (t2 : itree ProvBotE R2) :
    refine_prov
      (fun U' '(σ1', x1) r2 => RR U' ((σ1', rest1), inr x1) r2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      t2 ->
    refine_prov RR U
      (interp_cfg_exc ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      t2.
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_exc_trigger_non_exc ctx1 (subevent _ me1) (σ1, rest1) Logic.eq_refl)
      | symmetry; apply Eqit.bind_ret_r |].
    eapply refine_prov_bind.
    - apply refine_cfg_memory_event_l, Hmem.
    - intros U' [s1' x1] r2 HRR.
      apply refine_prov_tau_l, refine_prov_ret, HRR.
  Qed.

  Lemma loop_monad_app_eq {E : Type -> Type} {A : Type}
    (f : A -> itree E unit) (l1 l2 : list A) :
    loop_monad f (l1 ++ l2) ≅
    ITree.bind (loop_monad f l1) (fun _ => loop_monad f l2).
  Proof using.
    induction l1 as [| a l1' IH]; cbn [List.app loop_monad Monads.bind Monads.ret Monad_itree].
    - symmetry; apply Eqit.bind_ret_l.
    - symmetry; rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; symmetry; exact IH.
  Qed.

  Lemma denote_code_app_eq
    (c1 c2 : code dtyp) (va : option (@ptr ProvenanceV (@PointerV IP))) :
    @denote_code (@ParamsV IP IPT) (c1 ++ c2) va ≅
    ITree.bind (denote_code c1 va) (fun _ => denote_code c2 va).
  Proof using.
    unfold denote_code; apply loop_monad_app_eq.
  Qed.

  Lemma rewrite_non_entry_blocks_pass1_spec
    (avoid0 : list raw_id)
    (init_bid : block_id) (p : local_id) (dt : dtyp)
    (init_end_reg : local_id) (init_code' : code dtyp)
    (avoid : list raw_id) (bk_phis : list (block dtyp * local_id))
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id))
    (avoid_out : list raw_id) :
    rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid bk_phis =
      (pass1_out, avoid_out) ->
    incl avoid0 avoid ->
    ~ In init_end_reg avoid0 ->
    (forall r, In r (List.map snd bk_phis) -> ~ In r avoid0) ->
    List.map (fun '(bk, _, _, _) => bk) pass1_out = List.map fst bk_phis /\
    List.map (fun '(_, phi_r, _, _) => phi_r) pass1_out = List.map snd bk_phis /\
    incl avoid avoid_out /\
    (forall bk phi_r cd' end_r,
       In (bk, phi_r, cd', end_r) pass1_out ->
       ~ In phi_r avoid0 /\
       ~ In end_r avoid0 /\
       (if raw_id_eqb (blk_id bk) init_bid then
          cd' = init_code' /\ end_r = init_end_reg
        else
          exists av_in av_out,
            incl avoid0 av_in /\
            rewrite_code_for_slot p dt phi_r av_in (blk_code bk) = (cd', end_r, av_out))).
  Proof using.
    revert avoid pass1_out avoid_out;
      induction bk_phis as [| [bk0 phi0] rest IH];
      intros avoid pass1_out avoid_out Hpass Hinc Hinit_er Hphis;
      cbn [rewrite_non_entry_blocks_pass1] in Hpass.
    - inversion Hpass; subst; repeat split; try apply incl_refl; intros ? ? ? ? [].
    - assert (Hphi0 : ~ In phi0 avoid0) by (apply Hphis; left; reflexivity).
      assert (Hphis_tl : forall r, In r (List.map snd rest) -> ~ In r avoid0)
        by (intros r Hr; apply Hphis; right; exact Hr).
      destruct (raw_id_eqb (blk_id bk0) init_bid) eqn:Einit.
      + destruct (rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid rest)
          as [rest_out av'] eqn:Erest.
        inversion Hpass; subst; clear Hpass.
        destruct (IH avoid rest_out avoid_out Logic.eq_refl Hinc Hinit_er Hphis_tl)
          as (Hbks & Hprs & Hav & Hall).
        cbn [List.map fst snd]; split; [f_equal; exact Hbks |].
        split; [f_equal; exact Hprs |].
        split; [exact Hav |].
        intros bk phi_r cd' end_r [Heq | Hin].
        * inversion Heq; subst; rewrite Einit; repeat split; assumption.
        * apply Hall, Hin.
      + destruct (rewrite_code_for_slot p dt phi0 avoid (blk_code bk0))
          as [[cd0 end0] av1] eqn:Erw.
        destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt phi0 avoid (blk_code bk0)
                    cd0 end0 av1 Erw Hinc Hphi0) as [Hav1 Hend0].
        assert (Hinc1 : incl avoid0 av1) by (eapply incl_tran; eassumption).
        destruct (rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' av1 rest)
          as [rest_out av2] eqn:Erest.
        inversion Hpass; subst; clear Hpass.
        destruct (IH av1 rest_out avoid_out Logic.eq_refl Hinc1 Hinit_er Hphis_tl)
          as (Hbks & Hprs & Hav2 & Hall).
        cbn [List.map fst snd]; split; [f_equal; exact Hbks |].
        split; [f_equal; exact Hprs |].
        split; [eapply incl_tran; eassumption |].
        intros bk phi_r cd' end_r [Heq | Hin].
        * inversion Heq; subst; rewrite Einit.
          split; [exact Hphi0 | split; [exact Hend0 | exists avoid, av1; split; assumption]].
        * apply Hall, Hin.
  Qed.

  Lemma build_promoted_blocks_map_blk_id
    (init_bid : block_id) (dt : dtyp) (init_reg : local_id)
    (all_bks : ocfg dtyp)
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id)) :
    List.map blk_id (build_promoted_blocks init_bid dt init_reg all_bks pass1_out) =
    List.map (fun '(bk, _, _, _) => blk_id bk) pass1_out.
  Proof using.
    unfold build_promoted_blocks.
    induction pass1_out as [| [[[bk phi_r] cd'] end_r] rest IH]; cbn [List.map]; [reflexivity |].
    destruct (raw_id_eqb (blk_id bk) init_bid); cbn [blk_id]; f_equal; exact IH.
  Qed.

  Lemma combine_fst_eq {A B} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    List.map fst (List.combine xs ys) = xs.
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen;
      cbn in *; try lia; [reflexivity | f_equal; apply IH; lia].
  Qed.

  Lemma combine_snd_eq {A B} (xs : list A) (ys : list B) :
    List.length xs = List.length ys ->
    List.map snd (List.combine xs ys) = ys.
  Proof using.
    revert ys; induction xs as [| x xs' IH]; intros [| y ys'] Hlen;
      cbn in *; try lia; [reflexivity | f_equal; apply IH; lia].
  Qed.


  Lemma m2r_dtyp_eqb_eq (t1 t2 : dtyp) :
    dtyp_eqb t1 t2 = true -> t1 = t2.
  Proof using.
    unfold dtyp_eqb; destruct (dtyp_eq_dec t1 t2) as [Heq | _];
      [intros _; exact Heq | intros H; discriminate H].
  Qed.

  Lemma is_promotable_load_of_inv
    (p : local_id) (dt : dtyp)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (dst : local_id) :
    is_promotable_load_of p dt im = Some dst ->
    dst <> p /\
    exists anns_ld md,
      im = (IId dst,
            INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld,
            md) /\
      flat_map full_ann_uses anns_ld = [] /\
      is_debug_or_file_md md = true.
  Proof using.
    destruct im as [[iid ins] md].
    destruct iid as [dst0 |]; [| intros H; discriminate H].
    destruct ins; try (intros H; discriminate H).
    destruct ptr as [du_ld ptr_e].
    destruct ptr_e; try (intros H; discriminate H).
    destruct id as [| q]; [intros H; discriminate H |].
    cbn [is_promotable_load_of].
    destruct (raw_id_eqb q p
              && negb (raw_id_eqb dst0 p)
              && dtyp_eqb t dt
              && dtyp_eqb du_ld (DTYPE_Base DTYPE_Pointer)
              && m2r_is_empty (flat_map full_ann_uses anns)
              && is_non_volatile_non_atomic_anns anns
              && is_debug_or_file_md md) eqn:Econd;
      [| intros H; discriminate H].
    intros Hsome; inversion Hsome; subst dst0; clear Hsome.
    rewrite !andb_true_iff, negb_true_iff in Econd.
    destruct Econd as ((((((Hq & Hdst) & Hdt) & Hdu) & Hanns) & _) & Hmd).
    destruct (raw_id_eqb_spec q p) as [-> | _]; [| discriminate Hq].
    destruct (raw_id_eqb_spec dst p) as [_ | Hne]; [discriminate Hdst |].
    apply m2r_dtyp_eqb_eq in Hdt; subst t.
    apply m2r_dtyp_eqb_eq in Hdu; subst du_ld.
    apply m2r_is_empty_spec in Hanns.
    split; [exact Hne | exists anns, md; repeat split; assumption].
  Qed.

  Lemma is_promotable_store_of_inv
    (p : local_id) (dt : dtyp)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (val_exp : exp dtyp) :
    is_promotable_store_of p dt im = Some val_exp ->
    ~ In p (full_exp_uses val_exp) /\
    exists vid anns_st md,
      im = (IVoid vid,
            INSTR_Store (dt, val_exp) (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_st,
            md) /\
      flat_map full_ann_uses anns_st = [] /\
      is_debug_or_file_md md = true.
  Proof using.
    destruct im as [[iid ins] md].
    destruct iid as [| vid]; [intros H; discriminate H |].
    destruct ins; try (intros H; discriminate H).
    destruct val as [dt_st v_e], ptr as [du_st ptr_e].
    destruct ptr_e; try (intros H; discriminate H).
    destruct id as [| q]; [intros H; discriminate H |].
    cbn [is_promotable_store_of].
    destruct (raw_id_eqb q p
              && dtyp_eqb dt_st dt
              && dtyp_eqb du_st (DTYPE_Base DTYPE_Pointer)
              && negb (in_raw_ids p (full_exp_uses v_e))
              && m2r_is_empty (flat_map full_ann_uses anns)
              && is_non_volatile_non_atomic_anns anns
              && is_debug_or_file_md md) eqn:Econd;
      [| intros H; discriminate H].
    intros Hsome; inversion Hsome; subst v_e; clear Hsome.
    rewrite !andb_true_iff, negb_true_iff in Econd.
    destruct Econd as ((((((Hq & Hdt) & Hdu) & Hnin) & Hanns) & _) & Hmd).
    destruct (raw_id_eqb_spec q p) as [-> | _]; [| discriminate Hq].
    apply m2r_dtyp_eqb_eq in Hdt; subst dt_st.
    apply m2r_dtyp_eqb_eq in Hdu; subst du_st.
    apply in_raw_ids_false in Hnin.
    apply m2r_is_empty_spec in Hanns.
    split; [exact Hnin | exists vid, anns, md; repeat split; assumption].
  Qed.

  Lemma check_other_instr_for_slot_inv
    (allow_calls : bool) (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    check_other_instr_for_slot allow_calls safe_no_p p im = true ->
    ~ In p (m2r_code_entry_uses im) /\
    m2r_safe_mem_instr_any safe_no_p im = true /\
    (allow_calls = false ->
     forall iid fn args anns obs md,
       im <> (iid, INSTR_Call fn args anns obs, md)).
  Proof using.
    destruct im as [[iid ins] md].
    unfold check_other_instr_for_slot.
    rewrite andb_true_iff, negb_true_iff, in_raw_ids_false.
    intros [Hnin Hrest].
    split; [exact Hnin |].
    destruct iid as [id0 | vid0], ins;
      try discriminate Hrest;
      try (split; [exact Hrest | intros _ ? ? ? ? ? ? H; discriminate H]).
    - destruct fn as [dt_fn fn_e].
      rewrite !andb_true_iff in Hrest; destruct Hrest as [[Hac Hobs] Hintr].
      split.
      + cbn [m2r_safe_mem_instr_any]; rewrite andb_true_iff; split; assumption.
      + intros Hfalse; rewrite Hfalse in Hac; discriminate Hac.
    - destruct fn as [dt_fn fn_e].
      rewrite !andb_true_iff in Hrest; destruct Hrest as [[Hac Hobs] Hintr].
      split.
      + cbn [m2r_safe_mem_instr_any]; rewrite andb_true_iff; split; assumption.
      + intros Hfalse; rewrite Hfalse in Hac; discriminate Hac.
  Qed.

  Lemma check_no_alloca_or_call_instr_inv
    (safe_no_p : list local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    check_no_alloca_or_call_instr safe_no_p im = true ->
    (exists id0 op md, im = (IId id0, INSTR_Op op, md)) \/
    (exists id0 dt du ptr_e anns md,
       im = (IId id0, INSTR_Load dt (du, ptr_e) anns, md) /\
       m2r_safe_ptr_exp safe_no_p ptr_e = true /\
       load_metadata_dereferenceable md = None) \/
    (exists vid0 dt val_e du ptr_e anns md,
       im = (IVoid vid0, INSTR_Store (dt, val_e) (du, ptr_e) anns, md) /\
       m2r_safe_ptr_exp safe_no_p ptr_e = true) \/
    (exists vid0 s md, im = (IVoid vid0, INSTR_Comment s, md)) \/
    (exists iid0 sync ord md, im = (iid0, INSTR_Fence sync ord, md)).
  Proof using.
    destruct im as [[iid ins] md]; cbn [check_no_alloca_or_call_instr].
    destruct iid as [id0 | vid0], ins; try (intros H; discriminate H).
    - intros _; left; exists id0, op, md; reflexivity.
    - destruct ptr as [du ptr_e]; rewrite andb_true_iff.
      intros [Hsafe Hderef].
      destruct (load_metadata_dereferenceable md) eqn:Ed; [discriminate Hderef |].
      right; left; exists id0, t, du, ptr_e, anns, md; repeat split; assumption.
    - intros _; right; right; right; right; exists (IId id0), syncscope, ordering, md; reflexivity.
    - destruct val as [dt val_e], ptr as [du ptr_e]; intros Hsafe.
      right; right; left; exists vid0, dt, val_e, du, ptr_e, anns, md; split; [reflexivity | exact Hsafe].
    - intros _; right; right; right; left; exists vid0, c, md; reflexivity.
    - intros _; right; right; right; right; exists (IVoid vid0), syncscope, ordering, md; reflexivity.
  Qed.

  (** ** 3H. Fused Environment Steps & Stage 1 Attribute / Call Helpers *)

  Lemma tau_star_cfg_lwrite
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx (lwrite x v) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (Maps.add x v (stack_vars sf)), fstk), g)), tt)).
  Proof using.
    unfold lwrite, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    apply fused_local_prov_write.
  Qed.

  Lemma tau_star_cfg_exc_lwrite
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_exc ctx (lwrite x v) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (Maps.add x v (stack_vars sf)), fstk), g)), inr tt)).
  Proof using.
    unfold lwrite, Subevent.trigger; try unfold trigger_cast.
    eapply TS_Eq; [apply interp_cfg_exc_trigger_non_exc; reflexivity |].
    eapply tau_star_trans.
    - apply tau_star_bind, (tau_star_cfg_lwrite ctx x v σ sf fstk g).
    - eapply TS_Eq; [apply Eqit.bind_ret_l | apply TS_Tau, TS_Refl].
  Qed.

  Lemma tau_star_cfg_lread_some
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_cfg_model ctx (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    exact (fused_local_prov_read_some x v (σ, ((sf, fstk), g)) Hlk).
  Qed.

  Lemma tau_star_cfg_exc_lread_some
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_cfg_exc ctx (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), inr v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply TS_Eq; [apply interp_cfg_exc_trigger_non_exc; reflexivity |].
    eapply tau_star_trans.
    - apply tau_star_bind, (tau_star_cfg_lread_some ctx x v σ sf fstk g Hlk).
    - eapply TS_Eq; [apply Eqit.bind_ret_l | apply TS_Tau, TS_Refl].
  Qed.

  Lemma tau_star_cfg_stack_push
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (bs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx (stack_push bs) (σ, ((sf, fstk), g)))
      (Ret ((σ, (({| stack_vars := init_local_env bs;
                     stack_exc  := None;
                     stack_loc  := Some ""%string |}, sf :: fstk), g)), tt)).
  Proof using.
    unfold stack_push, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_stack_prov, on_ls_prov, handle_stack;
      cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
    rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma tau_star_cfg_stack_pop
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (σ : state) (sf_cur sf_prev : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_model ctx stack_pop (σ, ((sf_cur, sf_prev :: fstk), g)))
      (Ret ((σ, ((sf_prev, fstk), g)), tt)).
  Proof using.
    unfold stack_pop, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_cfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_stack_prov, on_ls_prov, handle_stack;
      cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
    rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma tau_star_mcfg_gwrite
    (gid : raw_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env) :
    tau_star
      (interp_mcfg_model (gwrite gid v) (σ, (ls, g)))
      (Ret ((σ, (ls, Maps.add gid v g)), tt)).
  Proof using.
    unfold gwrite, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_mcfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref;
      cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
    rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma denote_operand_bundles_empty_eq
    (loc : string) (f : exp dtyp) :
    @denote_operand_bundles (@ParamsV IP IPT) loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma assert_dereferenceable_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt)
      U
      (interp_cfg_model ctx1 (assert_dereferenceable or_null n v msg1) (σ1, rest1))
      (interp_cfg_model ctx2 (assert_dereferenceable or_null n v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[pt | | | | | | |] | |];
      try apply refine_cfg_raise_both.
    - destruct ((or_null && (ptr_to_int pt =? ptr_to_int null)%Z) || (n =? 0)%N).
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
      + eapply refine_cfg_model_bind.
        * unfold load, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_memory_event.
          exact (stage1_load_b8_array_any_ptr n (DVALUE_Base (DVALUE_Pointer pt))
                   U P_unprom G σ1 σ2 Hinv).
        * intros U' s1' _ s2' _ _ (-> & -> & ->).
          eapply refine_prov_obs_eq;
            [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
          apply refine_prov_ret; repeat split; reflexivity.
    - apply refine_cfg_raiseUB_l.
  Qed.

  Lemma assert_dereferenceable_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt))
      U
      (interp_cfg_exc ctx1 (assert_dereferenceable or_null n v msg1) (σ1, rest1))
      (interp_cfg_exc ctx2 (assert_dereferenceable or_null n v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[pt | | | | | | |] | |];
      try apply refine_cfg_exc_raise_both.
    - destruct ((or_null && (ptr_to_int pt =? ptr_to_int null)%Z) || (n =? 0)%N).
      + apply refine_cfg_exc_ret; repeat split; reflexivity.
      + eapply refine_cfg_exc_bind.
        * unfold load, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_exc_memory_event.
          exact (stage1_load_b8_array_any_ptr n (DVALUE_Base (DVALUE_Pointer pt))
                   U P_unprom G σ1 σ2 Hinv).
        * intros U' s1' _ s2' _ _ (-> & -> & ->).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
    - apply refine_cfg_exc_raiseUB_l.
  Qed.

  Lemma assert_load_dereferenceable_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (md : list (metadata dtyp)) (v : @dvalue (@ParamsV IP IPT)) (msg1 msg2 : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = tt /\ r2 = tt))
      U
      (interp_cfg_exc ctx1 (assert_load_dereferenceable md v msg1) (σ1, rest1))
      (interp_cfg_exc ctx2 (assert_load_dereferenceable md v msg2) (σ2, rest2)).
  Proof using.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |].
    - exact (assert_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc or_null
               (Z.to_N (denote_int_syntax n)) v msg1 msg2 U P_unprom G σ1 σ2 rest1 rest2 Hinv).
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_attrs_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (apply_attrs attrs msg v) (σ1, rest1))
      (interp_cfg_model ctx2 (apply_attrs attrs msg v) (σ2, rest2)).
  Proof using.
    unfold apply_attrs.
    eapply refine_cfg_model_bind.
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros a1 a2 <-; exact (conj (Logic.eq_refl U) (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
    - intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <-).
      eapply refine_cfg_model_bind.
      + unfold assert_attrs_dereferenceable.
        destruct (find_option attr_dereferenceable attrs) as [[or_null n] |],
                 v1 as [[pt | | | | | | |] | |];
          try (eapply refine_prov_obs_eq;
               [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |];
               apply refine_prov_ret; exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))))).
        exact (assert_dereferenceable_stage1_cfg_sim ctx1 ctx2 or_null
                 (Z.to_N (denote_int_syntax n)) (DVALUE_Base (DVALUE_Pointer pt))
                 msg msg U P_unprom G σ1 σ2 rest1 rest2 Hinv).
      + intros U2 s1'' _ s2'' _ _ (-> & -> & -> & _ & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_attrs_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2))
      U
      (interp_cfg_exc ctx1 (apply_attrs attrs msg v) (σ1, rest1))
      (interp_cfg_exc ctx2 (apply_attrs attrs msg v) (σ2, rest2)).
  Proof using.
    unfold apply_attrs.
    eapply refine_cfg_exc_bind.
    - eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
      intros a1 a2 <-; repeat split; reflexivity.
    - intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <-).
      eapply refine_cfg_exc_bind.
      + unfold assert_attrs_dereferenceable.
        destruct (find_option attr_dereferenceable attrs) as [[or_null n] |],
                 v1 as [[pt | | | | | | |] | |];
          try (apply refine_cfg_exc_ret; exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))))).
        exact (assert_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc or_null
                 (Z.to_N (denote_int_syntax n)) (DVALUE_Base (DVALUE_Pointer pt))
                 msg msg U P_unprom G σ1 σ2 rest1 rest2 Hinv).
      + intros U2 s1'' _ s2'' _ _ (-> & -> & -> & _ & _).
        apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma apply_args_attrs_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (attrss : list (list param_attr)) (msg : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (apply_args_attrs attrss msg args) (σ1, rest1))
      (interp_cfg_model ctx2 (apply_args_attrs attrss msg args) (σ2, rest2)).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret; repeat split; reflexivity.
    - destruct attrss as [| a r];
        (eapply refine_cfg_model_bind;
         [exact (apply_attrs_stage1_cfg_sim ctx1 ctx2 _ msg v U P_unprom G σ1 σ2 rest1 rest2 Hinv) |];
         intros U1 s1' v' s2' v2' _ (-> & -> & -> & <-);
         eapply refine_cfg_model_bind; [apply IH |];
         intros U2 s1'' vs' s2'' vs2' _ (-> & -> & -> & <-);
         eapply refine_prov_obs_eq;
           [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |];
         apply refine_prov_ret; repeat split; reflexivity).
  Qed.

  Lemma check_call_return_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (rv : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (check_call_return fattrs ret_attrs ranges loc args rv) (σ1, rest1))
      (interp_cfg_model ctx2 (check_call_return fattrs ret_attrs ranges loc args rv) (σ2, rest2)).
  Proof using.
    unfold check_call_return.
    eapply refine_cfg_model_bind.
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1' _ s2' _ _ (-> & -> & ->).
      destruct rv as [ex | v].
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
      + eapply refine_cfg_model_bind.
        * exact (apply_attrs_stage1_cfg_sim ctx1 ctx2 ret_attrs
                   (loc ++ " return value violates noundef.")%string
                   (value_metadata_range ranges v) U P_unprom G σ1 σ2 rest1 rest2 Hinv).
        * intros U2 s1'' v' s2'' v2' _ (-> & -> & -> & <-).
          eapply refine_prov_obs_eq;
            [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
          apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  Lemma check_call_return_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (rv : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = (σ1, rest1) /\ s2' = (σ2, rest2) /\ r1 = r2))
      U
      (interp_cfg_exc ctx1 (check_call_return fattrs ret_attrs ranges loc args rv) (σ1, rest1))
      (interp_cfg_exc ctx2 (check_call_return fattrs ret_attrs ranges loc args rv) (σ2, rest2)).
  Proof using.
    unfold check_call_return.
    eapply refine_cfg_exc_bind.
    - eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1' _ s2' _ _ (-> & -> & ->).
      destruct rv as [ex | v].
      + apply refine_cfg_exc_ret; repeat split; reflexivity.
      + eapply refine_cfg_exc_bind.
        * exact (apply_attrs_stage1_exc_sim ctx1 ctx2 RExc ret_attrs
                   (loc ++ " return value violates noundef.")%string
                   (value_metadata_range ranges v) U P_unprom G σ1 σ2 rest1 rest2 Hinv).
        * intros U2 s1'' v' s2'' v2' _ (-> & -> & -> & <-).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma denote_call_args_stage1_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (args : list (texp dtyp * list param_attr)) (msg : string)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : global_env)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Hvars : forall x,
               In x (flat_map (fun '(te, _) => full_texp_uses te) args) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' vs1 vs2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ vs1 = vs2))
      U
      (interp_cfg_exc ctx1 (denote_call_args args msg) s1)
      (interp_cfg_exc ctx2 (denote_call_args args msg) s2).
  Proof using.
    cbv zeta; unfold denote_call_args.
    induction args as [| [[t op] attrs] rest IH]; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
    - eapply refine_cfg_exc_bind.
      + eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Hvars; cbn [flat_map full_texp_uses snd]; apply in_app_iff; left; exact Hx.
        * intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
          exact (apply_attrs_stage1_exc_sim ctx1 ctx2 RExc attrs msg v1
                   U P_unprom G σ1 σ2 ((sf1, fstk1), g) ((sf2, fstk2), g) Hinv).
      + intros U1 s1' v' s2' v2' _ (-> & -> & -> & <-).
        eapply refine_cfg_exc_bind.
        * apply IH; intros x Hx; apply Hvars; cbn [flat_map]; apply in_app_iff; right; exact Hx.
        * intros U2 s1'' vs' s2'' vs2' _ (-> & -> & -> & <-).
          apply refine_cfg_exc_ret; repeat split; reflexivity.
  Qed.

  Lemma putchar_denotation_stage1_cfg_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
    (U : list N) (s1 s2 : FusedS) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) => U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2)
      U
      (interp_cfg_model ctx1 (putchar_denotation cc args) s1)
      (interp_cfg_model ctx2 (putchar_denotation cc args) s2).
  Proof using.
    unfold putchar_denotation.
    destruct args as [| ch [| ? ?]];
      try apply refine_cfg_raise_both.
    cbn [Functor.fmap Functor_itree ITree.map].
    eapply refine_cfg_model_bind.
    - destruct ch as [[| sz x32 | | | | | |] | |];
        try apply refine_cfg_raiseUB_l.
      destruct (Pos.eq_dec 32 sz) as [<- | _];
        [| apply refine_cfg_raiseUB_l].
      eapply refine_cfg_model_bind.
      + unfold io_stdout, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_trigger_prov, ITree.trigger.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
        pstep; apply RP_Step; cbn; right; right; split; [reflexivity |].
        intros a1 a2 <-; left.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret.
        repeat split; reflexivity.
      + intros U1 s1' _ s2' _ _ (-> & -> & -> & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret; repeat split; reflexivity.
    - intros U1 s1' dv1 s2' dv2 _ (-> & -> & -> & <-).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret; repeat split; reflexivity.
  Qed.

  (** ** 3I. Attribute, Block-Lookup & Equal-Memory Synchronization Helpers *)

  Lemma apply_value_attrs_nil_eq (msg : string) (v : @dvalue (@ParamsV IP IPT)) :
    @apply_value_attrs (@ParamsV IP IPT) [] msg v = raise_ret v.
  Proof using.
    unfold apply_value_attrs, value_attrs_poison, value_attr_nofpclass,
           value_attr_range, value_attr_align, value_attr_nonnull.
    cbn [find_option existsb andb].
    destruct v as [db | |]; [destruct db | |]; reflexivity.
  Qed.

  Lemma assert_alignment_ret_or_ub
    (a : @dvalue (@ParamsV IP IPT)) (anns : list (annotation dtyp)) (msg : string) :
    @assert_alignment (@ParamsV IP IPT) a anns msg = raise_ret tt \/
    @assert_alignment (@ParamsV IP IPT) a anns msg = raise_ub msg.
  Proof using.
    unfold assert_alignment, assert_aligned_to.
    destruct a as [db | |]; [destruct db | |];
      destruct (find_option ann_align anns) as [al |];
      cbn; try (left; reflexivity).
    match goal with
    | |- context [if ?c then _ else _] =>
        destruct c; [left; reflexivity | right; reflexivity]
    end.
  Qed.

  Lemma m2r_find_block_some_inv {T : Set} (bks : ocfg T) (bid : block_id) (bk : block T) :
    find_block bks bid = Some bk ->
    In bk bks /\ blk_id bk = bid.
  Proof using.
    induction bks as [| b0 bs IH]; intros Hfind; [cbn in Hfind; discriminate Hfind |].
    destruct (raw_id_eqb_spec (blk_id b0) bid) as [Heq | Hne].
    - rewrite find_block_eq in Hfind by exact Heq.
      inversion Hfind; subst b0; split; [left; reflexivity | exact Heq].
    - rewrite find_block_ineq in Hfind by exact Hne.
      destruct (IH Hfind) as [Hin Hid]; split; [right; exact Hin | exact Hid].
  Qed.

  Lemma m2r_find_block_in_nodup {T : Set} (bks : ocfg T) (bk : block T) :
    NoDup (List.map blk_id bks) ->
    In bk bks ->
    find_block bks (blk_id bk) = Some bk.
  Proof using.
    induction bks as [| b0 bs IH]; intros Hnd Hin; [contradiction Hin |].
    cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
    destruct Hin as [<- | Hin].
    - apply find_block_eq; reflexivity.
    - destruct (raw_id_eqb_spec (blk_id b0) (blk_id bk)) as [Heq | Hne].
      + exfalso; apply Hnin; rewrite Heq; apply in_map, Hin.
      + rewrite find_block_ineq by exact Hne; apply IH; assumption.
  Qed.

  Lemma m2r_find_block_map_id_pres {T : Set}
    (f : block T -> block T) (bks : ocfg T) (bid : block_id)
    (Hid : forall bk, In bk bks -> blk_id (f bk) = blk_id bk) :
    find_block (List.map f bks) bid = option_map f (find_block bks bid).
  Proof using.
    induction bks as [| b0 bs IH]; cbn [List.map]; [reflexivity |].
    pose proof (Hid b0 (or_introl Logic.eq_refl)) as Hid0.
    destruct (raw_id_eqb_spec (blk_id b0) bid) as [Heq | Hne].
    - rewrite find_block_eq by exact Heq.
      rewrite find_block_eq by congruence.
      reflexivity.
    - rewrite find_block_ineq by exact Hne.
      rewrite find_block_ineq by congruence.
      apply IH; intros bk Hbk; apply Hid; right; exact Hbk.
  Qed.

  Lemma refine_prov_refl_incl {A : Type} (U0 : list N) (t : itree ProvBotE A) :
    refine_prov (fun U' a1 a2 => incl U0 U' /\ a1 = a2) U0 t t.
  Proof using.
    assert (Hgen : forall U (tr : itree ProvBotE A),
              incl U0 U ->
              refine_prov (fun U' a1 a2 => incl U0 U' /\ a1 = a2) U tr tr).
    { pcofix CIH; intros U tr Hinc; pstep.
      apply RP_Step; unfold rp_step_body.
      destruct (observe tr) as [a | m | X e k].
      - exact (conj Hinc Logic.eq_refl).
      - right; apply CIH, Hinc.
      - destruct e as [pe | be].
        + destruct pe; right; right; intros pr Hpr; right; apply CIH.
          intros z Hz; right; apply Hinc, Hz.
        + destruct (is_ub_bot be) eqn:Eub.
          * left; exact Eub.
          * right; right; split; [apply EqE_bot_refl |].
            intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2.
            right; apply CIH.
            intros z Hz; apply in_app_iff; right; apply Hinc, Hz. }
    apply Hgen, incl_refl.
  Qed.

  Lemma fused_non_mem_equal_sync {A R : Type}
    (t0 : itree ProvBotE A)
    (mk : state -> A -> Res R)
    (U : list N) (σ1 σ2 : state)
    (Hmk : forall a,
             mem_stack_equal (state_memory_stack (fst (mk σ1 a)))
                             (state_memory_stack (fst (mk σ2 a))) /\
             snd (fst (mk σ1 a)) = snd (fst (mk σ2 a)) /\
             snd (mk σ1 a) = snd (mk σ2 a)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         incl U U' /\
         mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
         snd s1' = snd s2' /\
         r1 = r2)
      U
      (ITree.bind t0 (fun a => Ret (mk σ1 a)))
      (ITree.bind t0 (fun a => Ret (mk σ2 a))).
  Proof using.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' a1 a2 _ [Hinc <-].
    apply refine_prov_ret.
    destruct (mk σ1 a1) as [[σ1' rest1'] r1] eqn:E1,
             (mk σ2 a1) as [[σ2' rest2'] r2] eqn:E2.
    pose proof (Hmk a1) as Hspec; rewrite E1, E2 in Hspec; cbn in Hspec.
    exact (conj Hinc Hspec).
  Qed.

  Lemma alloca_mem_equal_safe (dt : dtyp) (num : N) (align : option N)
    (U P0 : list N) (σ1 σ2 : state)
    (Hpu : incl P0 U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists pr,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = r2 /\
           is_safe_ptr_dvalue (pr :: P0) r2 /\
           mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ2).
  Proof using.
    pose proof (stage1_equal_to_mem_inv U P0 σ1 σ2 Hpu Heq) as Hinv.
    eapply refine_prov_weaken;
      [exact (stage1_alloca_unprom dt num align U P0 [] σ1 σ2 Hinv) |].
    intros U' [σ1' r1] [σ2' r2]
      (pr & ptrs & Hpr & -> & Hr & Hsafe & Hinv' & _ & _).
    exists pr.
    split; [exact Hpr |].
    split; [reflexivity |].
    split; [exact Hr |].
    split; [exact Hsafe |].
    exact (stage1_mem_nil_is_equal (pr :: U) (pr :: P0) σ1' σ2' Hinv').
  Qed.

  Definition mcfg_eq_post {R : Type} (U0 : list N)
    (U' : list N) (x1 x2 : Res R) : Prop :=
    let '(s1', r1) := x1 in
    let '(s2', r2) := x2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
    snd s1' = snd s2' /\
    r1 = r2.

  Lemma on_ls_prov_equal_sync {T : Type}
    (f : Monads.stateT (@stack_frame (@ParamsV IP IPT) * stack)
           (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_ls_prov f (σ1, (ls, g)))
      (on_ls_prov f (σ2, (ls, g))).
  Proof using.
    unfold on_ls_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [ls1' r1] [ls2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst ls2' r2.
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma on_genv_prov_equal_sync {T : Type}
    (f : Monads.stateT global_env (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_genv_prov f (σ1, (ls, g)))
      (on_genv_prov f (σ2, (ls, g))).
  Proof using.
    unfold on_genv_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [g1' r1] [g2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst g2' r2.
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma fused_trigger_prov_equal_sync {F : Type -> Type} `{F -< ProvBotE} {T : Type}
    (e : F T) (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (fused_trigger_prov T e (σ1, rest))
      (fused_trigger_prov T e (σ2, rest)).
  Proof using.
    unfold fused_trigger_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma fused_draw_prov_equal_sync {T : Type}
    (e : @DrawE (@ParamsV IP IPT) T) (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (fused_draw_prov T e (σ1, rest))
      (fused_draw_prov T e (σ2, rest)).
  Proof using.
    unfold fused_draw_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Section InterpStateEqualSync.
    Context {E : Type -> Type}
            (h : E ~> Monads.stateT FusedS (itree ProvBotE))
            (Hh : forall X (e : E X) U σ1 σ2 rest,
                    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
                    refine_prov (mcfg_eq_post U) U
                      (h X e (σ1, rest))
                      (h X e (σ2, rest))).

    Local Definition k_is_cont {X R : Type} (k : X -> itree E R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => Tau (interp_state h (k x) s').

    Inductive is_eq_rel {R : Type} (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | ISE_Tree U (t : itree E R) (σ1 σ2 : state) rest
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_state h t (σ1, rest) ≅ a1 ->
        interp_state h t (σ2, rest) ≅ a2 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        is_eq_rel U0 U a1 a2
    | ISE_Bind {X : Type} U (u1 u2 : itree ProvBotE (Res X)) (k : X -> itree E R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_is_cont k) ≅ a1 ->
        ITree.bind u2 (k_is_cont k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        is_eq_rel U0 U a1 a2.

    Local Lemma is_eq_rel_obs_eq {R : Type} (U0 U : list N)
      (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      is_eq_rel U0 U a1 a2 ->
      is_eq_rel U0 U a1' a2'.
    Proof using.
      intros E1 E2 Hst.
      destruct Hst as [U' t σ1 σ2 rest Et1 Et2 Hinc Heq
                      | X U' u1 u2 k Eu1 Eu2 Hu].
      - eapply ISE_Tree;
          [etransitivity; eassumption
          | etransitivity; eassumption
          | exact Hinc
          | exact Heq].
      - eapply ISE_Bind;
          [etransitivity; eassumption
          | etransitivity; eassumption
          | exact Hu].
    Qed.

    Local Lemma step_is_eq_bind {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X)) (k : X -> itree E R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@is_eq_rel R U0) U
        (ITree.bind u1 (k_is_cont k))
        (ITree.bind u2 (k_is_cont k)).
    Proof using.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply ISE_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply ISE_Bind; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_is_cont k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply ISE_Bind; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_is_cont k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply ISE_Bind; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply ISE_Bind; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_is_cont k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_is_cont k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma interp_state_equal_sync_gen {R : Type}
      (t : itree E R) (U0 : list N) (σ1 σ2 : state)
      (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_post U0) U0
        (interp_state h t (σ1, rest))
        (interp_state h t (σ2, rest)).
    Proof using Hh.
      assert (Hvis : forall X (e : E X) (k : X -> itree E R) (s : FusedS),
                ITree.bind (h X e s) (k_is_cont k) ≅ interp_state h (Vis e k) s).
      { intros X e k s; symmetry; rewrite interp_state_vis.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] _ <-; reflexivity. }
      assert (Hcore : forall U a1 a2,
                @is_eq_rel R U0 U a1 a2 ->
                refine_prov (mcfg_eq_post U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := @is_eq_rel R U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b rest0 E1 E2 Hinc Heq0
                        | X U u1 u2 k E1 E2 Hu].
        - eapply refine_prov__obs_eq;
            [exact (is_eq_rel_obs_eq U0) | exact E1 | exact E2 |].
          destruct (observe t0) as [rv | mt | X e k] eqn:Hot.
          + assert (Et1 : Ret ((s_a, rest0), rv) ≅ interp_state h t0 (s_a, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_ret. }
            assert (Et2 : Ret ((s_b, rest0), rv) ≅ interp_state h t0 (s_b, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_ret. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply RP_Step; cbn;
              exact (conj Hinc (conj Heq0 (conj Logic.eq_refl Logic.eq_refl))).
          + assert (Et1 : Tau (interp_state h mt (s_a, rest0)) ≅ interp_state h t0 (s_a, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_tau. }
            assert (Et2 : Tau (interp_state h mt (s_b, rest0)) ≅ interp_state h t0 (s_b, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_tau. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply RP_Step; cbn.
            eapply ISE_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq0].
          + assert (Et1 : ITree.bind (h X e (s_a, rest0)) (k_is_cont k) ≅
                          interp_state h t0 (s_a, rest0)).
            { etransitivity; [apply Hvis | symmetry; rewrite (itree_eta t0), Hot; reflexivity]. }
            assert (Et2 : ITree.bind (h X e (s_b, rest0)) (k_is_cont k) ≅
                          interp_state h t0 (s_b, rest0)).
            { etransitivity; [apply Hvis | symmetry; rewrite (itree_eta t0), Hot; reflexivity]. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply step_is_eq_bind.
            eapply refine_prov_weaken; [apply Hh, Heq0 |].
            intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
            exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
        - eapply refine_prov__obs_eq;
            [exact (is_eq_rel_obs_eq U0) | exact E1 | exact E2 |].
          exact (step_is_eq_bind U0 U u1 u2 k Hu). }
      apply Hcore.
      eapply ISE_Tree; [reflexivity | reflexivity | apply incl_refl | exact Heq].
    Qed.
  End InterpStateEqualSync.

  Section CfgEqualSync.
    Context (Hmcfg : forall R (t : @MCFGtop (@ParamsV IP IPT) R) U σ1 σ2 rest,
                       mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
                       refine_prov (mcfg_eq_post U) U
                         (interp_mcfg_model t (σ1, rest))
                         (interp_mcfg_model t (σ2, rest))).

    Definition ctx_eq_sim
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT))) : Prop :=
      forall X (ce : CallE X) U σ1 σ2 rest,
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        refine_prov (mcfg_eq_post U) U
          (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, rest))
          (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, rest)).

    Local Lemma cfg_vis_as_bind {X R : Type}
      (e : @CFGEtop (@ParamsV IP IPT) X) (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      Vis e k ≅ ITree.bind (ITree.trigger e) k.
    Proof using.
      unfold ITree.trigger; rewrite Eqit.bind_vis.
      apply eqit_Vis; intros x; symmetry; apply Eqit.bind_ret_l.
    Qed.

    Local Lemma interp_cfg_model_trigger_call {X : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (ce : CallE X) (s : FusedS) :
      interp_cfg_model ctx (ITree.trigger (inl1 ce)) s ≅
      Tau (interp_cfg_model ctx (mrec_ctx ctx X ce) s).
    Proof using.
      unfold interp_cfg_model, ITree.trigger.
      rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
      cbn [_interp_mrec observe].
      rewrite interp_mcfg_model_tau.
      rewrite (interp_mcfg_model_obs_eq _ _ s
                 (interp_mrec_proper_eq (mrec_ctx ctx) _ _ (Eqit.bind_ret_r _))).
      reflexivity.
    Qed.

    Local Lemma interp_cfg_model_trigger_mcfg {X : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS) :
      interp_cfg_model ctx (ITree.trigger (inr1 me)) s ≅
      ITree.bind (interp_mcfg_model (ITree.trigger me) s)
        (fun '(s', x) => Tau (Ret (s', x))).
    Proof using.
      unfold interp_cfg_model, ITree.trigger.
      rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
      cbn [_interp_mrec observe].
      assert (Hvis : Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x))) ≅
                     ITree.bind (Vis me (fun x => Ret x))
                       (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x)))).
      { rewrite Eqit.bind_vis; apply eqit_Vis; intros x; symmetry; apply Eqit.bind_ret_l. }
      rewrite (interp_mcfg_model_obs_eq _ _ s Hvis), interp_mcfg_model_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] _ <-.
      rewrite interp_mcfg_model_tau.
      rewrite (interp_mcfg_model_obs_eq _ _ s' (interp_mrec_ret (mrec_ctx ctx) x)).
      rewrite interp_mcfg_model_ret; reflexivity.
    Qed.

    Local Definition k_ces_mcfg {X R : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => Tau (interp_cfg_model ctx (k x) s').

    Local Definition k_ces_call {X R : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => interp_cfg_model ctx (k x) s'.

    Inductive ces_rel {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT))) (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | CES_Tree U (t : @CFGtop (@ParamsV IP IPT) R) (σ1 σ2 : state) rest
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_cfg_model ctx1 t (σ1, rest) ≅ a1 ->
        interp_cfg_model ctx2 t (σ2, rest) ≅ a2 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        ces_rel ctx1 ctx2 U0 U a1 a2
    | CES_BindMcfg {X : Type} U (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_ces_mcfg ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_ces_mcfg ctx2 k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        ces_rel ctx1 ctx2 U0 U a1 a2
    | CES_BindCall {X : Type} U (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_ces_call ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_ces_call ctx2 k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        ces_rel ctx1 ctx2 U0 U a1 a2.

    Local Lemma ces_rel_obs_eq {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (U0 U : list N) (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      @ces_rel R ctx1 ctx2 U0 U a1 a2 ->
      @ces_rel R ctx1 ctx2 U0 U a1' a2'.
    Proof using.
      intros E1 E2 Hc.
      destruct Hc as [U' t σ1 σ2 rest Et1 Et2 Hinc Heq
                     | X U' u1 u2 k Eu1 Eu2 Hu
                     | X U' u1 u2 k Eu1 Eu2 Hu].
      - eapply CES_Tree;
          [etransitivity; eassumption | etransitivity; eassumption | exact Hinc | exact Heq].
      - eapply CES_BindMcfg;
          [etransitivity; eassumption | etransitivity; eassumption | exact Hu].
      - eapply CES_BindCall;
          [etransitivity; eassumption | etransitivity; eassumption | exact Hu].
    Qed.

    Local Lemma step_ces_mcfg_bind {X R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (U0 U : list N) (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (ITree.bind u1 (k_ces_mcfg ctx1 k))
        (ITree.bind u2 (k_ces_mcfg ctx2 k)).
    Proof using.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply CES_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_ces_mcfg ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_ces_mcfg ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply CES_BindMcfg; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_ces_mcfg ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_ces_mcfg ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Local Lemma step_ces_tree {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (U0 U : list N) (t : @CFGtop (@ParamsV IP IPT) R)
      (σ1 σ2 : state) (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Hinc : incl U0 U)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (interp_cfg_model ctx1 t (σ1, rest))
        (interp_cfg_model ctx2 t (σ2, rest)).
    Proof using Hmcfg.
      destruct (observe t) as [rv | mt | X e k] eqn:Hot.
      - assert (Et1 : Ret ((σ1, rest), rv) ≅ interp_cfg_model ctx1 t (σ1, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 t (Ret rv) _
                               (eq_trans (itree_eta t) (eq_ind_r (fun o => go o ≅ Ret rv) (reflexivity _) Hot))).
          apply interp_cfg_model_ret. }
        assert (Et2 : Ret ((σ2, rest), rv) ≅ interp_cfg_model ctx2 t (σ2, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 t (Ret rv) _
                               (eq_trans (itree_eta t) (eq_ind_r (fun o => go o ≅ Ret rv) (reflexivity _) Hot))).
          apply interp_cfg_model_ret. }
        eapply refine_prov__obs_eq;
          [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
        apply RP_Step; cbn; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
      - assert (Heta : t ≅ Tau mt) by (rewrite (itree_eta t), Hot; reflexivity).
        assert (Et1 : Tau (interp_cfg_model ctx1 mt (σ1, rest)) ≅ interp_cfg_model ctx1 t (σ1, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta); apply interp_cfg_model_tau. }
        assert (Et2 : Tau (interp_cfg_model ctx2 mt (σ2, rest)) ≅ interp_cfg_model ctx2 t (σ2, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta); apply interp_cfg_model_tau. }
        eapply refine_prov__obs_eq;
          [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
        apply RP_Step; cbn; eapply CES_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
      - assert (Heta : t ≅ ITree.bind (ITree.trigger e) k).
        { rewrite (itree_eta t), Hot; apply cfg_vis_as_bind. }
        destruct e as [ce | me].
        + assert (Et1 : Tau (ITree.bind (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, rest))
                               (k_ces_call ctx1 k)) ≅
                        interp_cfg_model ctx1 t (σ1, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_call, Eqit.bind_tau; reflexivity. }
          assert (Et2 : Tau (ITree.bind (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, rest))
                               (k_ces_call ctx2 k)) ≅
                        interp_cfg_model ctx2 t (σ2, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_call, Eqit.bind_tau; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
          apply RP_Step; cbn.
          eapply CES_BindCall; [reflexivity | reflexivity |].
          eapply refine_prov_weaken; [apply Hctx, Heq |].
          intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
          exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
        + assert (Et1 : ITree.bind (interp_mcfg_model (ITree.trigger me) (σ1, rest))
                          (k_ces_mcfg ctx1 k) ≅
                        interp_cfg_model ctx1 t (σ1, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_mcfg, Eqit.bind_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
          assert (Et2 : ITree.bind (interp_mcfg_model (ITree.trigger me) (σ2, rest))
                          (k_ces_mcfg ctx2 k) ≅
                        interp_cfg_model ctx2 t (σ2, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_mcfg, Eqit.bind_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
          apply step_ces_mcfg_bind.
          eapply refine_prov_weaken; [apply Hmcfg, Heq |].
          intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
          exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
    Qed.

    Local Lemma step_ces_call_bind {X R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (U0 U : list N) (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (ITree.bind u1 (k_ces_call ctx1 k))
        (ITree.bind u2 (k_ces_call ctx2 k)).
    Proof using Hmcfg.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          assert (Eb1 : interp_cfg_model ctx1 (k x1) (σ1', rest1') ≅
                        ITree.bind u1 (k_ces_call ctx1 k)).
          { symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity. }
          assert (Eb2 : interp_cfg_model ctx2 (k x1) (σ2', rest1') ≅
                        ITree.bind u2 (k_ces_call ctx2 k)).
          { symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Eb1 | exact Eb2 |].
          exact (step_ces_tree ctx1 ctx2 Hctx U0 U (k x1) σ1' σ2' rest1' Hinc Heq).
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply CES_BindCall; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_ces_call ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply CES_BindCall; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_ces_call ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply CES_BindCall; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply CES_BindCall; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_ces_call ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_ces_call ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma cfg_equal_sync_gen {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (t : @CFGtop (@ParamsV IP IPT) R)
      (U0 : list N) (σ1 σ2 : state)
      (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_post U0) U0
        (interp_cfg_model ctx1 t (σ1, rest))
        (interp_cfg_model ctx2 t (σ2, rest)).
    Proof using Hmcfg.
      assert (Hcore : forall U a1 a2,
                @ces_rel R ctx1 ctx2 U0 U a1 a2 ->
                refine_prov (mcfg_eq_post U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := @ces_rel R ctx1 ctx2 U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b rest0 E1 E2 Hinc Heq0
                        | X U u1 u2 k E1 E2 Hu
                        | X U u1 u2 k E1 E2 Hu].
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_tree ctx1 ctx2 Hctx U0 U t0 s_a s_b rest0 Hinc Heq0).
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_mcfg_bind ctx1 ctx2 U0 U u1 u2 k Hu).
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_call_bind ctx1 ctx2 Hctx U0 U u1 u2 k Hu). }
      apply Hcore.
      eapply CES_Tree; [reflexivity | reflexivity | apply incl_refl | exact Heq].
    Qed.
  End CfgEqualSync.

  Lemma on_mem_prov_equal_sync {T : Type}
    (m : @memM (@ParamsV IP IPT) _ T)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hm : refine_prov (eq_sync_post U) U
            (memM_interp_prov m σ1)
            (memM_interp_prov m σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_mem_prov (memM_interp_prov m) (σ1, rest))
      (on_mem_prov (memM_interp_prov m) (σ2, rest)).
  Proof using.
    unfold on_mem_prov.
    eapply refine_prov_bind; [exact Hm |].
    intros U' [σ1' r1] [σ2' r2] (Hinc & Heq & <-).
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma interp_vellvm_prov_h_equal_sync {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_vellvm_prov_h e (σ1, rest))
      (interp_vellvm_prov_h e (σ2, rest)).
  Proof using.
    destruct rest as [ls g].
    unfold interp_vellvm_prov_h.
    destruct e as [e1 | [e2 | [e3 | [[e4a | e4b] | [e5 | [e6 | [e7 | [e8 | [e9 | [e10 | e11]]]]]]]]]];
      cbn [case_].
    - apply fused_trigger_prov_equal_sync, Heq.
    - unfold fused_intrinsic_prov, handle_intrinsic.
      apply on_mem_prov_equal_sync, handle_intrinsicM_equal_sync, Heq.
    - unfold fused_global_prov; apply on_genv_prov_equal_sync, Heq.
    - unfold fused_local_prov; apply on_ls_prov_equal_sync, Heq.
    - unfold fused_stack_prov; apply on_ls_prov_equal_sync, Heq.
    - unfold fused_memory_prov, handle_memory.
      apply on_mem_prov_equal_sync, handle_memoryM_equal_sync, Heq.
    - apply fused_draw_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
  Qed.

  Lemma mcfg_equal_sync {R : Type}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_mcfg_model t (σ1, rest))
      (interp_mcfg_model t (σ2, rest)).
  Proof using.
    unfold interp_mcfg_model.
    exact (interp_state_equal_sync_gen interp_vellvm_prov_h
             (@interp_vellvm_prov_h_equal_sync) (interp_intrinsics t) U σ1 σ2 rest Heq).
  Qed.

  Lemma cfg_equal_sync {R : Type}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : ctx_eq_sim ctx1 ctx2)
    (t : @CFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_cfg_model ctx1 t (σ1, rest))
      (interp_cfg_model ctx2 t (σ2, rest)).
  Proof using.
    exact (cfg_equal_sync_gen (@mcfg_equal_sync) ctx1 ctx2 Hctx t U σ1 σ2 rest Heq).
  Qed.

  Lemma cfg_exc_equal_sync {R : Type}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : ctx_eq_sim ctx1 ctx2)
    (t : @CFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov
      (exc_post
         (fun U' s1' s2' x1 x2 =>
            incl U U' /\
            mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
            snd s1' = snd s2' /\
            x1 = x2)
         (fun U' s1' s2' r1 r2 =>
            incl U U' /\
            mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
            snd s1' = snd s2' /\
            r1 = r2))
      U
      (interp_cfg_exc ctx1 t (σ1, rest))
      (interp_cfg_exc ctx2 t (σ2, rest)).
  Proof using.
    unfold interp_cfg_exc.
    eapply refine_prov_weaken;
      [exact (cfg_equal_sync ctx1 ctx2 Hctx (run_exc t) U σ1 σ2 rest Heq) |].
    intros U' [s1' [x1 | r1]] [s2' [x2 | r2]] (Hinc & Hm & Hs & Heq_res);
      inversion Heq_res; subst; exact (conj Hinc (conj Hm (conj Hs Logic.eq_refl))).
  Qed.

  (** ** 3J. Global Environment Initialization & Safe-Provenance Preservation *)

  Lemma genv_safe_empty (P0 : list N) :
    genv_safe P0 Maps.empty.
  Proof using.
    intros gid v Hlk; rewrite lookup_empty in Hlk; discriminate Hlk.
  Qed.

  Lemma genv_safe_add (P0 : list N) (gid : raw_id)
    (v : @dvalue (@ParamsV IP IPT)) (g : @global_env (@ParamsV IP IPT)) :
    genv_safe P0 g ->
    is_safe_ptr_dvalue P0 v ->
    genv_safe P0 (Maps.add gid v g).
  Proof using.
    intros Hg Hv gid' v' Hlk.
    destruct (RawIDOrd.eq_dec gid gid') as [<- | Hne].
    - rewrite lookup_add_eq in Hlk; inversion Hlk; subst v'; exact Hv.
    - rewrite lookup_add_neq in Hlk by exact Hne; exact (Hg gid' v' Hlk).
  Qed.

  Definition genv_init_post
    (P0 : list N) (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (U' : list N) (x1 x2 : Res unit) : Prop :=
    let '(s1', _) := x1 in
    let '(s2', _) := x2 in
    exists P1 g',
      incl P0 P1 /\
      incl P1 U' /\
      snd s1' = (ls, g') /\
      snd s2' = (ls, g') /\
      genv_safe P1 g' /\
      mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')).

  Lemma genv_init_seq
    (t1 t2 : @MCFGtop (@ParamsV IP IPT) unit)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Ht1 : refine_prov (genv_init_post P0 ls) U
             (interp_mcfg_model t1 (σ1, (ls, g)))
             (interp_mcfg_model t1 (σ2, (ls, g))))
    (Ht2 : forall U1 P1 σ1' σ2' g',
             incl P0 P1 ->
             incl P1 U1 ->
             genv_safe P1 g' ->
             mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') ->
             refine_prov (genv_init_post P1 ls) U1
               (interp_mcfg_model t2 (σ1', (ls, g')))
               (interp_mcfg_model t2 (σ2', (ls, g')))) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (ITree.bind t1 (fun _ => t2)) (σ1, (ls, g)))
      (interp_mcfg_model (ITree.bind t1 (fun _ => t2)) (σ2, (ls, g))).
  Proof using.
    eapply refine_mcfg_model_bind; [exact Ht1 |].
    intros U1 [σ1' rest1'] [] [σ2' rest2'] [] _
      (P1 & g1 & Hp01 & Hp1u & Hs1 & Hs2 & Hg1 & Heq1).
    cbn [fst snd] in Hs1, Hs2, Heq1; subst rest1' rest2'.
    eapply refine_prov_weaken; [exact (Ht2 U1 P1 σ1' σ2' g1 Hp01 Hp1u Hg1 Heq1) |].
    intros U2 [s1'' []] [s2'' []] (P2 & g2 & Hp12 & Hp2u & Hsa & Hsb & Hg2 & Heq2).
    exists P2, g2.
    exact (conj (incl_tran Hp01 Hp12)
             (conj Hp2u (conj Hsa (conj Hsb (conj Hg2 Heq2))))).
  Qed.

  Lemma genv_init_loop_monad {A : Type}
    (f : A -> @MCFGtop (@ParamsV IP IPT) unit)
    (xs : list A)
    (Hf : forall a U P0 σ1 σ2 ls g,
            In a xs ->
            incl P0 U ->
            genv_safe P0 g ->
            mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
            refine_prov (genv_init_post P0 ls) U
              (interp_mcfg_model (f a) (σ1, (ls, g)))
              (interp_mcfg_model (f a) (σ2, (ls, g)))) :
    forall U P0 σ1 σ2 ls g,
      incl P0 U ->
      genv_safe P0 g ->
      mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
      refine_prov (genv_init_post P0 ls) U
        (interp_mcfg_model (loop_monad f xs) (σ1, (ls, g)))
        (interp_mcfg_model (loop_monad f xs) (σ2, (ls, g))).
  Proof using.
    induction xs as [| a xs' IH]; intros U P0 σ1 σ2 ls g Hpu Hg Heq;
      cbn [loop_monad Monads.bind Monads.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - eapply genv_init_seq.
      + apply Hf; [left; reflexivity | exact Hpu | exact Hg | exact Heq].
      + intros U1 P1 σ1' σ2' g' _ Hp1u Hg1 Heq1.
        apply IH; [intros a' U' P' s1 s2 ls' g0 Ha'; apply Hf; right; exact Ha'
                  | exact Hp1u | exact Hg1 | exact Heq1].
  Qed.

  Lemma alloca_gwrite_safe_sim
    (dt : dtyp) (al : option N) (gid : raw_id)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model
         (ITree.bind (alloca dt 1%N al) (fun v => gwrite gid v))
         (σ1, (ls, g)))
      (interp_mcfg_model
         (ITree.bind (alloca dt 1%N al) (fun v => gwrite gid v))
         (σ2, (ls, g))).
  Proof using.
    eapply refine_mcfg_model_bind.
    - unfold alloca, Subevent.trigger; try unfold trigger_cast.
      apply refine_mcfg_memory_event.
      exact (alloca_mem_equal_safe dt 1%N al U P0 σ1 σ2 Hpu Heq).
    - intros U1 [σ1' rest1'] v1 [σ2' rest2'] v2 _
        (pr & Hpr & -> & <- & Hsafe & Heq').
      eapply refine_prov_tau_star_l; [apply tau_star_mcfg_gwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_mcfg_gwrite |].
      apply refine_prov_ret.
      exists (pr :: P0), (Maps.add gid v1 g).
      split; [intros z Hz; right; exact Hz |].
      split; [intros z [<- | Hz]; [left; reflexivity | right; apply Hpu, Hz] |].
      split; [reflexivity |].
      split; [reflexivity |].
      split; [apply genv_safe_add; [| exact Hsafe];
              eapply genv_safe_incl; [intros z Hz; right; exact Hz | exact Hg] |].
      exact Heq'.
  Qed.

  Lemma allocate_declaration_safe_sim (d : declaration dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_declaration d) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_declaration d) (σ2, (ls, g))).
  Proof using.
    unfold allocate_declaration.
    destruct (lookup_intrinsic_declaration (dc_name d)).
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - exact (alloca_gwrite_safe_sim (DTYPE_Base DTYPE_Pointer) None (dc_name d)
               U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma allocate_block_address_safe_sim (fb : function_id * block_id)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_block_address fb) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_block_address fb) (σ2, (ls, g))).
  Proof using.
    destruct fb as [f b]; unfold allocate_block_address.
    exact (alloca_gwrite_safe_sim (DTYPE_Base (DTYPE_I 8)) None (blockaddress_id f b)
             U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma allocate_global_safe_sim (gl : global dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_global gl) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_global gl) (σ2, (ls, g))).
  Proof using.
    unfold allocate_global.
    destruct (g_alias gl).
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - exact (alloca_gwrite_safe_sim (g_typ gl)
               (option_map (fun a => Z.to_N (denote_int_syntax a)) (g_align gl))
               (g_ident gl) U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma initialize_global_safe_sim (gl : global dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (initialize_global gl) (σ1, (ls, g)))
      (interp_mcfg_model (initialize_global gl) (σ2, (ls, g))).
  Proof using.
    destruct ls as [sf fstk]; unfold initialize_global.
    destruct (g_alias gl).
    - destruct (g_exp gl) as [e |]; [| apply refine_mcfg_raiseUB_l].
      destruct e; try apply refine_mcfg_raiseUB_l.
      destruct id as [g_source | lid]; [| apply refine_mcfg_raiseUB_l].
      eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
      intros U1 s1' p1 s2' p2 _ (-> & -> & -> & -> & Hsafe).
      eapply refine_prov_tau_star_l; [apply tau_star_mcfg_gwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_mcfg_gwrite |].
      apply refine_prov_ret.
      exists P0, (Maps.add (g_ident gl) p2 g).
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl
                  (conj Logic.eq_refl
                     (conj (genv_safe_add P0 (g_ident gl) p2 g Hg (Hsafe P0 Hg)) Heq))))).
    - eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
      intros U1 s1' a1 s2' a2 _ (-> & -> & -> & -> & _).
      eapply refine_mcfg_model_bind.
      + destruct (g_exp gl) as [e |].
        * eapply refine_prov_weaken;
            [exact (denote_exp_mcfg_sim (Some (g_typ gl)) e U σ1 σ2 sf sf fstk fstk g
                      (fun _ _ => Logic.eq_refl)) |].
          intros U' [sa va] [sb vb] (-> & -> & -> & -> & _).
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
        * eapply refine_prov_obs_eq;
            [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
          apply refine_prov_ret;
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U2 s1'' uv1 s2'' uv2 _ (-> & -> & -> & ->).
        unfold store, Subevent.trigger; try unfold trigger_cast.
        apply refine_mcfg_memory_event.
        eapply refine_prov_weaken;
          [exact (handle_memoryM_equal_sync (Store (g_typ gl) a2 uv2) U σ1 σ2 Heq) |].
        intros U' [σ1' []] [σ2' []] (Hinc & Heq' & _).
        exists P0, g.
        exact (conj (incl_refl P0)
                 (conj (incl_tran Hpu Hinc)
                    (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq'))))).
  Qed.

  Lemma build_global_environment_safe_sim (M : CFG.mcfg dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (build_global_environment M) (σ1, (ls, g)))
      (interp_mcfg_model (build_global_environment M) (σ2, (ls, g))).
  Proof using.
    unfold build_global_environment, allocate_declarations,
           allocate_block_addresses, allocate_globals, initialize_globals.
    eapply genv_init_seq.
    - apply genv_init_loop_monad;
        [intros d U' P' s1 s2 ls' g' _; apply allocate_declaration_safe_sim
        | exact Hpu | exact Hg | exact Heq].
    - intros U1 P1 σ1a σ2a g1 _ Hp1u Hg1 Heq1.
      eapply genv_init_seq.
      + apply genv_init_loop_monad;
          [intros fb U' P' s1 s2 ls' g' _; apply allocate_block_address_safe_sim
          | exact Hp1u | exact Hg1 | exact Heq1].
      + intros U2 P2 σ1b σ2b g2 _ Hp2u Hg2 Heq2.
        eapply genv_init_seq.
        * apply genv_init_loop_monad;
            [intros gl U' P' s1 s2 ls' g' _; apply allocate_global_safe_sim
            | exact Hp2u | exact Hg2 | exact Heq2].
        * intros U3 P3 σ1c σ2c g3 _ Hp3u Hg3 Heq3.
          apply genv_init_loop_monad;
            [intros gl U' P' s1 s2 ls' g' _; apply initialize_global_safe_sim
            | exact Hp3u | exact Hg3 | exact Heq3].
  Qed.

  Lemma address_one_function_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hname : dc_name (df_prototype df1) = dc_name (df_prototype df2))
    (Hfn : Rfn (denote_function df1) (denote_function df2)) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', (z1, f1)) '(s2', (z2, f2)) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ z1 = z2 /\ Rfn f1 f2)
      U
      (interp_mcfg_model (address_one_function df1) s1)
      (interp_mcfg_model (address_one_function df2) s2).
  Proof using.
    cbv zeta; destruct ls as [sf fstk]; unfold address_one_function.
    rewrite Hname.
    eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
    intros U1 s1' fv1 s2' fv2 _ (-> & -> & -> & -> & _).
    destruct fv2 as [[pt | | | | | | |] | |];
      try apply refine_mcfg_raise_both.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
    apply refine_prov_ret;
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hfn)))).
  Qed.

  Lemma address_one_library_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (lib : function_id * @function_denotation (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hfn : Rfn (snd lib) (snd lib)) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', (z1, f1)) '(s2', (z2, f2)) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ z1 = z2 /\ Rfn f1 f2)
      U
      (interp_mcfg_model (address_one_library_function lib) s1)
      (interp_mcfg_model (address_one_library_function lib) s2).
  Proof using.
    cbv zeta; destruct ls as [sf fstk], lib as [fid den]; cbn [snd] in Hfn.
    unfold address_one_library_function.
    eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
    intros U1 s1' fv1 s2' fv2 _ (-> & -> & -> & -> & _).
    destruct fv2 as [[pt | | | | | | |] | |];
      try apply refine_mcfg_raise_both.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
    apply refine_prov_ret;
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hfn)))).
  Qed.

  Lemma map_monad_address_one_function_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hrel : Forall2
              (fun d1 d2 =>
                 dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                 Rfn (denote_function d1) (denote_function d2))
              defs1 defs2) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', fns1) '(s2', fns2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\
         Forall2 (fun '(z1, f1) '(z2, f2) => z1 = z2 /\ Rfn f1 f2) fns1 fns2)
      U
      (interp_mcfg_model (map_monad address_one_function defs1) s1)
      (interp_mcfg_model (map_monad address_one_function defs2) s2).
  Proof using.
    cbv zeta; induction Hrel as [| d1 d2 ds1 ds2 [Hnm Hfn] _ IH];
      cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (Forall2_nil _)))).
    - eapply refine_mcfg_model_bind;
        [exact (address_one_function_pair_sim Rfn d1 d2 U σ1 σ2 ls g Hnm Hfn) |].
      intros U1 s1' [z1 f1] s2' [z2 f2] _ (-> & -> & -> & <- & Hf).
      eapply refine_mcfg_model_bind; [exact IH |].
      intros U2 s1'' fns1 s2'' fns2 _ (-> & -> & -> & Hfns).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl
                 (conj Logic.eq_refl
                    (conj Logic.eq_refl
                       (Forall2_cons _ _ (conj Logic.eq_refl Hf) Hfns)))).
  Qed.

  Lemma map_monad_address_one_library_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (libs : list (function_id * @function_denotation (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hrel : Forall (fun lib => Rfn (snd lib) (snd lib)) libs) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', fns1) '(s2', fns2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\
         Forall2 (fun '(z1, f1) '(z2, f2) => z1 = z2 /\ Rfn f1 f2) fns1 fns2)
      U
      (interp_mcfg_model (map_monad address_one_library_function libs) s1)
      (interp_mcfg_model (map_monad address_one_library_function libs) s2).
  Proof using.
    cbv zeta; induction Hrel as [| lib rest Hfn _ IH];
      cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (Forall2_nil _)))).
    - eapply refine_mcfg_model_bind;
        [exact (address_one_library_pair_sim Rfn lib U σ1 σ2 ls g Hfn) |].
      intros U1 s1' [z1 f1] s2' [z2 f2] _ (-> & -> & -> & <- & Hf).
      eapply refine_mcfg_model_bind; [exact IH |].
      intros U2 s1'' fns1 s2'' fns2 _ (-> & -> & -> & Hfns).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl
                 (conj Logic.eq_refl
                    (conj Logic.eq_refl
                       (Forall2_cons _ _ (conj Logic.eq_refl Hf) Hfns)))).
  Qed.

  Lemma convert_bitcast_vec1_scalar_eq
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (Hsc : is_scalar_dtyp dt = true)
    (Hser : dvalue_to_memory_bytes dt (DVALUE_Base db) None = raise_ret bs) :
    @convert (@ParamsV IP IPT) CONV_Bitcast (DTYPE_Array true 1%N dt)
      (DVALUE_Array true [DVALUE_Base db]) dt =
    EOU_to_itree (memory_bytes_to_dvalue bs dt).
  Proof using.
    destruct (is_scalar_dtyp_inv dt Hsc) as (dtb & -> & _).
    unfold convert.
    rewrite vec1_neq_base, bit_sizeof_vec1_eq, dvalue_to_memory_bytes_vec1_eq, Hser.
    cbn; reflexivity.
  Qed.

  (** ** 3K. Parameterized CPS Coinduction ([m2r_paco] & [m2r_cps]) *)

  Definition Ans : Type :=
    Res (@dvalue (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)).

  Definition top_ans_post : list N -> Ans -> Ans -> Prop :=
    fun _ '(_, r1) '(_, r2) => r1 = r2.

  Definition obs_clos
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (b1 b2 : itree ProvBotE Ans) : Prop :=
    exists a1 a2, a1 ≅ b1 /\ a2 ≅ b2 /\ r U a1 a2.

  Lemma obs_clos_eq
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (b1 b1' b2 b2' : itree ProvBotE Ans) :
    b1 ≅ b1' ->
    b2 ≅ b2' ->
    obs_clos r U b1 b2 ->
    obs_clos r U b1' b2'.
  Proof using.
    intros E1 E2 (a1 & a2 & Ea1 & Ea2 & Hr).
    exists a1, a2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hr]].
  Qed.

  Definition m2r_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
    exists R : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop,
      (forall U' a1 a1' a2 a2', a1 ≅ a1' -> a2 ≅ a2' -> R U' a1 a2 -> R U' a1' a2') /\
      (forall U' a1 a2,
         R U' a1 a2 ->
         refine_prov_ top_ans_post
           (fun U'' b1 b2 => R U'' b1 b2 \/ obs_clos r U'' b1 b2) U' a1 a2) /\
      R U t1 t2.

  Lemma m2r_paco_obs_eq
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t1' t2 t2' : itree ProvBotE Ans) :
    t1 ≅ t1' ->
    t2 ≅ t2' ->
    m2r_paco r U t1 t2 ->
    m2r_paco r U t1' t2'.
  Proof using.
    intros E1 E2 (R & Heq & Hst & HR).
    exists R; exact (conj Heq (conj Hst (Heq U t1 t1' t2 t2' E1 E2 HR))).
  Qed.

  Lemma m2r_paco_mon
    (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop) :
    (forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2) ->
    forall U t1 t2, m2r_paco r1 U t1 t2 -> m2r_paco r2 U t1 t2.
  Proof using.
    intros Hle U t1 t2 (R & Heq & Hst & HR).
    exists R; split; [exact Heq | split; [| exact HR]].
    intros U' a1 a2 Ha.
    eapply refine_prov__mon; [exact (Hst U' a1 a2 Ha) |].
    intros U'' b1 b2 [Hb | (c1 & c2 & Ec1 & Ec2 & Hc)]; [left; exact Hb |].
    right; exists c1, c2; exact (conj Ec1 (conj Ec2 (Hle U'' c1 c2 Hc))).
  Qed.

  Lemma m2r_paco_to_refine_prov (U0 : list N) (t1_0 t2_0 : itree ProvBotE Ans) :
    m2r_paco (fun _ _ _ => False) U0 t1_0 t2_0 ->
    refine_prov top_ans_post U0 t1_0 t2_0.
  Proof using.
    intros (R & _ & Hst & HR0).
    assert (Hcore : forall U t1 t2, R U t1 t2 -> refine_prov top_ans_post U t1 t2).
    { pcofix CIH; intros U t1 t2 HR; pstep.
      eapply refine_prov__mon; [exact (Hst U t1 t2 HR) |].
      intros U' b1 b2 [Hb | (_ & _ & _ & _ & [])].
      right; apply CIH, Hb. }
    exact (Hcore U0 t1_0 t2_0 HR0).
  Qed.

  Lemma m2r_paco_fold
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    refine_prov_ top_ans_post
      (fun U' b1 b2 => m2r_paco r U' b1 b2 \/ obs_clos r U' b1 b2) U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros H.
    set (R_fold := fun U' x1 x2 =>
                     m2r_paco r U' x1 x2 \/ (U' = U /\ t1 ≅ x1 /\ t2 ≅ x2)).
    exists R_fold; split; [| split].
    - intros U' a1 a1' a2 a2' E1 E2 [Ha | (-> & Et1 & Et2)].
      + left; exact (m2r_paco_obs_eq r U' a1 a1' a2 a2' E1 E2 Ha).
      + right; split; [reflexivity | split; etransitivity; eassumption].
    - intros U' a1 a2 [Ha | (-> & Et1 & Et2)].
      + destruct Ha as (R0 & Heq0 & Hst0 & HR0).
        eapply refine_prov__mon; [exact (Hst0 U' a1 a2 HR0) |].
        intros U'' b1 b2 [Hb | Hb];
          [left; left; exists R0; exact (conj Heq0 (conj Hst0 Hb)) | right; exact Hb].
      + eapply refine_prov__obs_eq; [| exact Et1 | exact Et2 |].
        * intros U'' x1 x1' x2 x2' Ex1 Ex2 [[Hx | (-> & E1 & E2)] | Hx].
          -- left; left; exact (m2r_paco_obs_eq r U'' x1 x1' x2 x2' Ex1 Ex2 Hx).
          -- left; right; split; [reflexivity | split; etransitivity; eassumption].
          -- right; exact (obs_clos_eq r U'' x1 x1' x2 x2' Ex1 Ex2 Hx).
        * eapply refine_prov__mon; [exact H |].
          intros U'' b1 b2 [Hb | Hb]; [left; left; exact Hb | right; exact Hb].
    - right; split; [reflexivity | split; reflexivity].
  Qed.

  Lemma m2r_paco_unfold
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    m2r_paco r U t1 t2 ->
    refine_prov_ top_ans_post
      (fun U' b1 b2 => m2r_paco r U' b1 b2 \/ obs_clos r U' b1 b2) U t1 t2.
  Proof using.
    intros (R & Heq & Hst & HR).
    eapply refine_prov__mon; [exact (Hst U t1 t2 HR) |].
    intros U' b1 b2 [Hb | Hb];
      [left; exists R; exact (conj Heq (conj Hst Hb)) | right; exact Hb].
  Qed.

  Lemma m2r_paco_acc
    (r0 l : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop) :
    (forall r,
       (forall U a1 a2, r0 U a1 a2 -> r U a1 a2) ->
       (forall U a1 a2, l U a1 a2 -> r U a1 a2) ->
       forall U a1 a2, l U a1 a2 -> m2r_paco r U a1 a2) ->
    forall U a1 a2, l U a1 a2 -> m2r_paco r0 U a1 a2.
  Proof using.
    intros HOBG.
    set (r_comb := fun U' y1 y2 => r0 U' y1 y2 \/ l U' y1 y2).
    pose proof (HOBG r_comb
                  (fun U' y1 y2 H => or_introl H)
                  (fun U' y1 y2 H => or_intror H)) as Hl_sub.
    set (R_union := m2r_paco r_comb).
    intros U a1 a2 Hl0.
    exists R_union; split; [exact (m2r_paco_obs_eq r_comb) | split; [| exact (Hl_sub U a1 a2 Hl0)]].
    intros U' x1 x2 (R & Heq & Hst & HR).
    eapply refine_prov__mon; [exact (Hst U' x1 x2 HR) |].
    intros U'' z1 z2 [HzR | (w1 & w2 & Ew1 & Ew2 & [Hzr0 | Hzl])].
    - left; exists R; exact (conj Heq (conj Hst HzR)).
    - right; exists w1, w2; exact (conj Ew1 (conj Ew2 Hzr0)).
    - left; exact (m2r_paco_obs_eq r_comb U'' w1 z1 w2 z2 Ew1 Ew2 (Hl_sub U'' w1 w2 Hzl)).
  Qed.

  Lemma m2r_paco_tau_both_r
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (m1 m2 t1 t2 : itree ProvBotE Ans) :
    Tau m1 ≅ t1 ->
    Tau m2 ≅ t2 ->
    r U m1 m2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros E1 E2 Hr.
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |].
    apply m2r_paco_fold, RP_Step; cbn.
    right; exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hr]].
  Qed.

  Definition m2r_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) : Prop :=
    forall (r' : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop),
      (forall U0 x1 x2, r U0 x1 x2 -> r' U0 x1 x2) ->
      forall (k1 : A1 -> itree ProvBotE Ans) (k2 : A2 -> itree ProvBotE Ans),
        (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> m2r_paco r' U' (k1 a1) (k2 a2)) ->
        m2r_paco r' U (ITree.bind u1 k1) (ITree.bind u2 k2).

  Lemma m2r_cps_mon {A1 A2 : Type}
    (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (Hle : forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    m2r_cps r1 RA U u1 u2 ->
    m2r_cps r2 RA U u1 u2.
  Proof using.
    intros Hcps r' Hr' k1 k2 Hk.
    exact (Hcps r' (fun U0 x1 x2 H => Hr' U0 x1 x2 (Hle U0 x1 x2 H)) k1 k2 Hk).
  Qed.

  Lemma m2r_cps_obs_eq {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 u1' : itree ProvBotE A1) (u2 u2' : itree ProvBotE A2) :
    u1 ≅ u1' ->
    u2 ≅ u2' ->
    m2r_cps r RA U u1 u2 ->
    m2r_cps r RA U u1' u2'.
  Proof using.
    intros E1 E2 Hcps r' Hr' k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E1 | intros ? ? <-; reflexivity]
      | eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E2 | intros ? ? <-; reflexivity]
      | exact (Hcps r' Hr' k1 k2 Hk)].
  Qed.

  Lemma m2r_cps_ret {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) :
    RA U a1 a2 ->
    m2r_cps r RA U (Ret a1) (Ret a2).
  Proof using.
    intros Hra r' _ k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_ret_l
      | symmetry; apply Eqit.bind_ret_l
      | exact (Hk U a1 a2 (incl_refl U) Hra)].
  Qed.

  Lemma m2r_cps_bind {A1 A2 B1 B2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (RB : list N -> B1 -> B2 -> Prop)
    (U : list N)
    (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2)
    (f1 : A1 -> itree ProvBotE B1) (f2 : A2 -> itree ProvBotE B2) :
    m2r_cps r RA U u1 u2 ->
    (forall U1 a1 a2, incl U U1 -> RA U1 a1 a2 -> m2r_cps r RB U1 (f1 a1) (f2 a2)) ->
    m2r_cps r RB U (ITree.bind u1 f1) (ITree.bind u2 f2).
  Proof using.
    intros Hu Hf r' Hr' k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply (Hu r' Hr'); intros U1 a1 a2 Hinc1 Ha.
    eapply (Hf U1 a1 a2 Hinc1 Ha r' Hr'); intros U2 b1 b2 Hinc2 Hb.
    exact (Hk U2 b1 b2 (incl_tran Hinc1 Hinc2) Hb).
  Qed.

  Lemma m2r_cps_weaken {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA RB : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    m2r_cps r RA U u1 u2 ->
    (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> RB U' a1 a2) ->
    m2r_cps r RB U u1 u2.
  Proof using.
    intros Hu Hw r' Hr' k1 k2 Hk.
    eapply (Hu r' Hr'); intros U' a1 a2 Hinc Ha.
    exact (Hk U' a1 a2 Hinc (Hw U' a1 a2 Hinc Ha)).
  Qed.

  Lemma m2r_cps_to_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    m2r_cps r top_ans_post U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros Hcps.
    eapply m2r_paco_obs_eq; [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply (Hcps r (fun _ _ _ H => H) (fun x => Ret x) (fun x => Ret x)).
    intros U' [s1 v1] [s2 v2] _ Heq.
    apply m2r_paco_fold, RP_Step; exact Heq.
  Qed.

  Lemma refine_prov_to_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U0 : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    refine_prov RA U0 u1 u2 ->
    m2r_cps r RA U0 u1 u2.
  Proof using.
    intros Hu0 r0 _ k1 k2 Hk0.
    set (l := fun U (t1 t2 : itree ProvBotE Ans) =>
                exists u1' u2',
                  ITree.bind u1' k1 ≅ t1 /\
                  ITree.bind u2' k2 ≅ t2 /\
                  incl U0 U /\
                  refine_prov RA U u1' u2').
    eapply (m2r_paco_acc r0 l);
      [| exists u1, u2; split; [reflexivity | split; [reflexivity | exact (conj (incl_refl U0) Hu0)]]].
    intros r' Hr0 Hl U t1 t2 (u1' & u2' & E1 & E2 & Hinc & Hu).
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
    punfold Hu; revert Hinc.
    induction Hu as [U u1' u2' Hstep | U u1' m1 u2' Hu1 _ IH | U u1' u2' m2 Hu2 _ IH];
      intros Hinc.
    - unfold rp_step_body in Hstep.
      destruct (observe u1') as [a1 | m1 | X1 e1 h1] eqn:Hou1.
      + destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
        eapply m2r_paco_obs_eq;
          [symmetry; rewrite (itree_eta u1'), Hou1, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite (itree_eta u2'), Hou2, Eqit.bind_ret_l; reflexivity
          | exact (m2r_paco_mon r0 r' Hr0 U (k1 a1) (k2 a2) (Hk0 U a1 a2 Hinc Hstep))].
      + destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
        pclearbot; apply m2r_paco_fold, RP_Step; unfold rp_step_body.
        rewrite (observe_bind u1' k1), Hou1, (observe_bind u2' k2), Hou2.
        right; exists (ITree.bind m1 k1), (ITree.bind m2 k2);
          split; [reflexivity | split; [reflexivity |]].
        apply Hl; exists m1, m2;
          split; [reflexivity | split; [reflexivity | exact (conj Hinc Hstep)]].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * apply m2r_paco_fold, RP_Step; unfold rp_step_body;
            rewrite (observe_bind u1' k1), Hou1; left; exact Hub.
        * apply m2r_paco_fold, RP_Step; unfold rp_step_body;
            rewrite (observe_bind u1' k1), Hou1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; exists (ITree.bind (h1 p) k1), (ITree.bind u2' k2);
            split; [reflexivity | split; [reflexivity |]].
          apply Hl; exists (h1 p), u2';
            split; [reflexivity | split; [reflexivity |]].
          split; [intros z Hz; right; apply Hinc, Hz | exact Hleft].
        * destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          apply m2r_paco_fold, RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1' k1), Hou1, (observe_bind u2' k2), Hou2; right; right.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             right; exists (ITree.bind (h1 p) k1), (ITree.bind (h2 p) k2);
               split; [reflexivity | split; [reflexivity |]].
             apply Hl; exists (h1 p), (h2 p);
               split; [reflexivity | split; [reflexivity |]].
             split; [intros z Hz; right; apply Hinc, Hz | exact Hboth].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             right; exists (ITree.bind (h1 a1) k1), (ITree.bind (h2 a2) k2);
               split; [reflexivity | split; [reflexivity |]].
             apply Hl; exists (h1 a1), (h2 a2);
               split; [reflexivity | split; [reflexivity |]].
             split; [intros z Hz; apply in_app_iff; right; apply Hinc, Hz | exact HA].
    - specialize (IH Hinc); apply m2r_paco_unfold in IH; apply m2r_paco_fold.
      eapply RP_TauL; [rewrite (observe_bind u1' k1), Hu1; reflexivity | exact IH].
    - specialize (IH Hinc); apply m2r_paco_unfold in IH; apply m2r_paco_fold.
      eapply RP_TauR; [rewrite (observe_bind u2' k2), Hu2; reflexivity | exact IH].
  Qed.

  Lemma m2r_cps_cfg_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    m2r_cps r RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       m2r_cps r RB U'
         (interp_cfg_model ctx1 (k1 a1) s1')
         (interp_cfg_model ctx2 (k2 a2) s2')) ->
    m2r_cps r RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply m2r_cps_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply m2r_cps_bind; [exact Ht |].
    intros U' [s1' a1] [s2' a2] Hinc Ha; exact (Hk U' s1' a1 s2' a2 Hinc Ha).
  Qed.

  Lemma m2r_cps_cfg_exc_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    m2r_cps r (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1) (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       m2r_cps r (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    m2r_cps r (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply m2r_cps_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply m2r_cps_bind; [exact Ht |].
    intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] Hinc Hres; try contradiction.
    - apply m2r_cps_ret; exact Hres.
    - exact (Hk U' s1' a1 s2' a2 Hinc Hres).
  Qed.

  Lemma m2r_cps_cfg_exc_iter {I1 I2 R1 R2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RI   : list N -> FusedS -> FusedS -> I1 -> I2 -> Prop)
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RRet : list N -> FusedS -> FusedS -> R1 -> R2 -> Prop)
    (b1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1))
    (b2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2))
    (U0 : list N)
    (Hbody : forall U s1 s2 i1 i2,
               incl U0 U ->
               RI U s1 s2 i1 i2 ->
               m2r_cps r
                 (exc_post RExc
                    (fun U' s1' s2' lr1 lr2 =>
                       match lr1, lr2 with
                       | inl j1, inl j2 => RI U' s1' s2' j1 j2
                       | inr v1, inr v2 => RRet U' s1' s2' v1 v2
                       | _, _ => False
                       end))
                 U
                 (interp_cfg_exc ctx1 (b1 i1) s1)
                 (interp_cfg_exc ctx2 (b2 i2) s2)) :
    forall s1 s2 i1 i2,
      RI U0 s1 s2 i1 i2 ->
      m2r_cps r (exc_post RExc RRet) U0
        (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1)
        (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2).
  Proof using.
    set (step_k1 := fun '(s', res) =>
                      match res with
                      | inl x => Ret (s', inl x)
                      | inr (inl j) => Tau (interp_cfg_exc ctx1 (ITree.iter b1 j) s')
                      | inr (inr v) => Ret (s', inr v)
                      end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1))).
    set (step_k2 := fun '(s', res) =>
                      match res with
                      | inl x => Ret (s', inl x)
                      | inr (inl j) => Tau (interp_cfg_exc ctx2 (ITree.iter b2 j) s')
                      | inr (inr v) => Ret (s', inr v)
                      end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R2))).
    assert (Hunf1 : forall s i,
              interp_cfg_exc ctx1 (ITree.iter b1 i) s ≅
              ITree.bind (interp_cfg_exc ctx1 (b1 i) s) step_k1).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx1 _ _ s (unfold_iter b1 i)), interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | v]]] _ <-; cbn [step_k1];
        [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
    assert (Hunf2 : forall s i,
              interp_cfg_exc ctx2 (ITree.iter b2 i) s ≅
              ITree.bind (interp_cfg_exc ctx2 (b2 i) s) step_k2).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ s (unfold_iter b2 i)), interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | v]]] _ <-; cbn [step_k2];
        [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
    intros s1_0 s2_0 i1_0 i2_0 Hinit r0 Hr k_out1 k_out2 Hk_out.
    set (l_it := fun U (t1 t2 : itree ProvBotE Ans) =>
                   exists s1 s2 i1 i2,
                     ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1) k_out1 ≅ t1 /\
                     ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2) k_out2 ≅ t2 /\
                     incl U0 U /\
                     RI U s1 s2 i1 i2).
    eapply (m2r_paco_acc r0 l_it);
      [| exists s1_0, s2_0, i1_0, i2_0;
         split; [reflexivity | split; [reflexivity | exact (conj (incl_refl U0) Hinit)]]].
    intros r' Hr0 Hl U t1 t2 (s1 & s2 & i1 & i2 & E1 & E2 & Hinc & Hri).
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
    assert (Eb1 : ITree.bind (interp_cfg_exc ctx1 (b1 i1) s1)
                    (fun x => ITree.bind (step_k1 x) k_out1) ≅
                  ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1) k_out1).
    { symmetry; rewrite <- Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf1 | intros ? ? <-; reflexivity]. }
    assert (Eb2 : ITree.bind (interp_cfg_exc ctx2 (b2 i2) s2)
                    (fun x => ITree.bind (step_k2 x) k_out2) ≅
                  ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2) k_out2).
    { symmetry; rewrite <- Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf2 | intros ? ? <-; reflexivity]. }
    eapply m2r_paco_obs_eq; [exact Eb1 | exact Eb2 |].
    eapply (Hbody U s1 s2 i1 i2 Hinc Hri r' (fun Ua x1 x2 H => Hr0 Ua x1 x2 (Hr Ua x1 x2 H))).
    intros U' [s1' res1] [s2' res2] Hinc' Hpost.
    destruct res1 as [x1 | [j1 | v1]], res2 as [x2 | [j2 | v2]]; cbn in Hpost; try contradiction.
    - eapply m2r_paco_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      exact (m2r_paco_mon r0 r' Hr0 U' _ _ (Hk_out U' (s1', inl x1) (s2', inl x2) (incl_tran Hinc Hinc') Hpost)).
    - eapply m2r_paco_tau_both_r;
        [symmetry; apply Eqit.bind_tau | symmetry; apply Eqit.bind_tau |].
      apply Hl; exists s1', s2', j1, j2;
        split; [reflexivity | split; [reflexivity | exact (conj (incl_tran Hinc Hinc') Hpost)]].
    - eapply m2r_paco_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      exact (m2r_paco_mon r0 r' Hr0 U' _ _ (Hk_out U' (s1', inr v1) (s2', inr v2) (incl_tran Hinc Hinc') Hpost)).
  Qed.

  Lemma of_list_lookup_pair
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2 (fun '(k1, f1) '(k2, f2) => k1 = k2 /\ Rfn f1 f2) l1 l2) :
    forall z,
      option_rel Rfn
        (lookup z (IntMaps.IP.of_list l1))
        (lookup z (IntMaps.IP.of_list l2)).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros z.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right fst snd]; unfold lookup.
      destruct (Z.eq_dec k1 z) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity; constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne; apply IH.
  Qed.

  Lemma interp_cfg_exc_call
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT))) (s : FusedS) :
    interp_cfg_exc ctx (call dt cc fv vs) s ≅
    Tau (ITree.bind
           (interp_cfg_model ctx (mrec_ctx ctx _ (Call dt cc fv vs)) s)
           (fun '(s', y) => Tau (Ret (s', inr y)))).
  Proof using.
    unfold call, Subevent.trigger.
    rewrite (interp_cfg_exc_trigger_non_exc ctx
               (subevent _ (Call dt cc fv vs)) s Logic.eq_refl).
    change (ITree.trigger (subevent _ (Call dt cc fv vs)))
      with (@call (@ParamsV IP IPT) dt cc fv vs).
    rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
               (interp_cfg_model_call ctx dt cc fv vs s)
               (fun _ _ <- => Logic.eq_refl)).
    apply Eqit.bind_tau.
  Qed.

  Lemma m2r_cps_call_exc
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT)))
    (U : list N) (s1 s2 : FusedS)
    (k_out1 k_out2 : Res (@exc (@ParamsV IP IPT) +
                          (@dvalue (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))) ->
                     itree ProvBotE Ans)
    (Hr_call :
       r U
         (ITree.bind
            (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) s1)
            (fun '(s1', y1) => Tau (k_out1 (s1', inr y1))))
         (ITree.bind
            (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) s2)
            (fun '(s2', y2) => Tau (k_out2 (s2', inr y2))))) :
    m2r_paco r U
      (ITree.bind (interp_cfg_exc ctx1 (call dt cc fv vs) s1) k_out1)
      (ITree.bind (interp_cfg_exc ctx2 (call dt cc fv vs) s2) k_out2).
  Proof using.
    assert (E1 :
      Tau (ITree.bind
             (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) s1)
             (fun '(s1', y1) => Tau (k_out1 (s1', inr y1)))) ≅
      ITree.bind (interp_cfg_exc ctx1 (call dt cc fv vs) s1) k_out1).
    { symmetry.
      rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
                 (interp_cfg_exc_call ctx1 dt cc fv vs s1)
                 (fun _ _ <- => Logic.eq_refl)).
      rewrite Eqit.bind_tau, Eqit.bind_bind.
      apply eqit_Tau.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s1' y1] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
    assert (E2 :
      Tau (ITree.bind
             (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) s2)
             (fun '(s2', y2) => Tau (k_out2 (s2', inr y2)))) ≅
      ITree.bind (interp_cfg_exc ctx2 (call dt cc fv vs) s2) k_out2).
    { symmetry.
      rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
                 (interp_cfg_exc_call ctx2 dt cc fv vs s2)
                 (fun _ _ <- => Logic.eq_refl)).
      rewrite Eqit.bind_tau, Eqit.bind_bind.
      apply eqit_Tau.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2' y2] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
    exact (m2r_paco_tau_both_r r U _ _ _ _ E1 E2 Hr_call).
  Qed.

  (** ** 3L. Call-Frame Helpers & Promoted SSA Instruction Simulations *)

  Lemma top_frame_unprom_frame_eq
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    top_frame_unprom_from fs0 G ms1 ->
    top_frame_unprom_from fs0 G ms2.
  Proof using.
    intros Heq (f & Hfs & Hout).
    exists f; split; [rewrite <- Heq; exact Hfs | exact Hout].
  Qed.

  Lemma top_frame_prom_frame_eq
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    top_frame_prom_from fs0 gs G ms1 ->
    top_frame_prom_from fs0 gs G ms2.
  Proof using.
    intros Heq (f & Hfs & Hin & Hout).
    exists f; split; [rewrite <- Heq; exact Hfs | split; [exact Hin | exact Hout]].
  Qed.

  Lemma m2r_combine_lists_varargs_fst_in {A B : Type}
    (xs : list A) (ys : list B) (bs : list (A * B)) (vs : list B) :
    combine_lists_varargs xs ys = raise_ret (bs, vs) ->
    forall x, In x (List.map fst bs) -> In x xs.
  Proof using.
    revert ys bs vs; induction xs as [| x0 xs' IH]; intros ys bs vs Hcomb x Hin;
      cbn [combine_lists_varargs] in Hcomb.
    - destruct ys; inversion Hcomb; subst; contradiction.
    - destruct ys as [| y0 ys']; [discriminate Hcomb |].
      apply EOU_bind_ret_inv in Hcomb as ([l vargs] & Hrec & Heq).
      inversion Heq; subst bs vs; clear Heq.
      cbn [List.map fst In] in Hin; destruct Hin as [<- | Hin].
      + left; reflexivity.
      + right; eapply IH; eassumption.
  Qed.

  Lemma init_local_env_lookup_none_not_in
    (bs : list (local_id * @dvalue (@ParamsV IP IPT))) (q : local_id) :
    ~ In q (List.map fst bs) ->
    Maps.lookup q (init_local_env bs) = None.
  Proof using.
    induction bs as [| [k dv] rest IH]; intros Hnin; cbn [init_local_env List.fold_right].
    - apply lookup_empty.
    - cbn [List.map fst In] in Hnin.
      destruct (RawIDOrd.eq_dec k q) as [-> | Hne].
      + exfalso; apply Hnin; left; reflexivity.
      + rewrite lookup_add_neq by exact Hne.
        apply IH; intros Hin; apply Hnin; right; exact Hin.
  Qed.

  Lemma safe_locals_env_init_args
    (P_safe : list N) (fargs : list local_id) (bks : ocfg dtyp)
    (safe_sub : list local_id)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (bs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (vs : list (@dvalue (@ParamsV IP IPT))) :
    combine_lists_varargs fargs args = raise_ret (bs, vs) ->
    (forall q,
       In q safe_sub ->
       In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks)) ->
    (forall q, In q safe_sub -> Maps.lookup q (init_local_env bs) = None) /\
    safe_locals_env P_safe safe_sub (init_local_env bs).
  Proof using.
    intros Hcomb Hsub.
    assert (Hnone : forall q, In q safe_sub -> Maps.lookup q (init_local_env bs) = None).
    { intros q Hq.
      apply init_local_env_lookup_none_not_in.
      intros Hin_bs.
      eapply (unique_alloca_not_in_fargs fargs bks q (Hsub q Hq)).
      eapply m2r_combine_lists_varargs_fst_in; eassumption. }
    split; [exact Hnone |].
    intros q v Hq Hlk; rewrite (Hnone q Hq) in Hlk; discriminate Hlk.
  Qed.

  Lemma safe_locals_env_add_other
    (P_safe : list N) (safe_sub : list local_id)
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (env : @local_env (@ParamsV IP IPT)) :
    ~ In x safe_sub ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (Maps.add x v env).
  Proof using.
    intros Hnin Henv q v0 Hq Hlk.
    destruct (RawIDOrd.eq_dec x q) as [-> | Hne]; [contradiction |].
    rewrite lookup_add_neq in Hlk by exact Hne.
    exact (Henv q v0 Hq Hlk).
  Qed.

  Lemma safe_locals_env_add_safe
    (P_safe : list N) (safe_sub : list local_id)
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (env : @local_env (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_safe v ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (Maps.add x v env).
  Proof using.
    intros Hv Henv q v0 Hq Hlk.
    destruct (RawIDOrd.eq_dec x q) as [<- | Hne].
    - rewrite lookup_add_eq in Hlk; inversion Hlk; subst v0; exact Hv.
    - rewrite lookup_add_neq in Hlk by exact Hne; exact (Henv q v0 Hq Hlk).
  Qed.

  Lemma push_call_frame_stage1_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (args : list (@dvalue (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hargs : df_args df1 = df_args df2)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', varg1) '(s2', varg2) =>
         exists pr_va bs vs σ1' σ2',
           ~ In pr_va U /\
           U' = pr_va :: U /\
           varg1 = varg2 /\
           combine_lists_varargs (df_args df1) args = raise_ret (bs, vs) /\
           s1' = (σ1', (({| stack_vars := init_local_env bs;
                            stack_exc  := None;
                            stack_loc  := Some ""%string |}, sf1 :: fstk1), g)) /\
           s2' = (σ2', (({| stack_vars := init_local_env bs;
                            stack_exc  := None;
                            stack_loc  := Some ""%string |}, sf2 :: fstk2), g)) /\
           stage1_mem_inv (pr_va :: U) (pr_va :: P_unprom) G σ1' σ2' /\
           top_frame_unprom_from
             (Memory_stack_frame_stack (state_memory_stack σ2)) G
             (state_memory_stack σ2'))
      U
      (interp_cfg_model ctx1 (push_call_frame df1 args) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_model ctx2 (push_call_frame df2 args) (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold push_call_frame; rewrite <- Hargs.
    destruct (combine_lists_varargs (df_args df1) args)
      as [msg | msg | msg | [bs vs]] eqn:Ecomb; cbn [EOU_to_itree].
    - eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
        [apply refine_cfg_raise_both | intros ? ? ? ? ? _ []].
    - eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
        [apply refine_cfg_raiseOOM_l | intros ? ? ? ? ? _ []].
    - eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
        [apply refine_cfg_raiseUB_l | intros ? ? ? ? ? _ []].
    - eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_model_obs_eq _ _ _ _ (Eqit.bind_ret_l _ _))
        | symmetry; apply (interp_cfg_model_obs_eq _ _ _ _ (Eqit.bind_ret_l _ _)) |].
      destruct (map_monad dtyp_of_dvalue vs) as [msg | msg | msg | dts] eqn:Edts;
        cbn [EOU_to_itree].
      + eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_raise_both | intros ? ? ? ? ? _ []].
      + eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_raiseOOM_l | intros ? ? ? ? ? _ []].
      + eapply refine_cfg_model_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_raiseUB_l | intros ? ? ? ? ? _ []].
      + eapply refine_prov_obs_eq;
          [symmetry; apply (interp_cfg_model_obs_eq _ _ _ _ (Eqit.bind_ret_l _ _))
          | symmetry; apply (interp_cfg_model_obs_eq _ _ _ _ (Eqit.bind_ret_l _ _)) |].
        eapply refine_cfg_model_bind.
        * unfold mem_push, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_memory_event, (stage1_mempush U P_unprom G σ1 σ2 Hinv).
        * intros U1 [σ1_mp rest1_mp] _ [σ2_mp rest2_mp] _ _
            ((<- & <-) & (-> & _ & _ & Hinv_mp & Htf_mp)).
          eapply refine_cfg_model_bind.
          -- eapply refine_prov_tau_star_l;
               [apply tau_star_cfg_stack_push |].
             eapply refine_prov_tau_star_r;
               [apply tau_star_cfg_stack_push |].
             apply refine_prov_ret;
               exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U2 s1_sp _ s2_sp _ _ (-> & -> & ->).
             eapply refine_cfg_model_bind.
             ++ unfold alloca, Subevent.trigger; try unfold trigger_cast.
                apply refine_cfg_memory_event.
                exact (stage1_alloca_unprom (DTYPE_Struct true dts) 1%N None
                         U P_unprom G σ1_mp σ2_mp Hinv_mp).
             ++ intros U3 [σ1_al rest1_al] va1 [σ2_al rest2_al] va2 _
                  ((<- & <-) &
                   (pr_va & ptrs_va & Hnin_va & -> & <- & Hsafe_va & Hinv_al & Hdisj_va & Hfs_al)).
                assert (Htf_al :
                          top_frame_unprom_from
                            (Memory_stack_frame_stack (state_memory_stack σ2)) G
                            (state_memory_stack σ2_al)).
                { eapply top_frame_unprom_frame_eq; [symmetry; exact Hfs_al |].
                  exact (top_frame_unprom_add_ptrs _ G ptrs_va _ Htf_mp Hdisj_va). }
                eapply refine_cfg_model_bind.
                ** unfold store, Subevent.trigger; try unfold trigger_cast.
                   apply refine_cfg_memory_event.
                   exact (stage1_store_unprom (DTYPE_Struct true dts) va1
                            (DVALUE_Struct true vs)
                            (pr_va :: U) (pr_va :: P_unprom) G σ1_al σ2_al Hinv_al Hsafe_va).
                ** intros U4 [σ1_st rest1_st] _ [σ2_st rest2_st] _ _
                     ((<- & <-) & (-> & _ & _ & Hinv_st & Hfs_st)).
                   assert (Htf_st :
                             top_frame_unprom_from
                               (Memory_stack_frame_stack (state_memory_stack σ2)) G
                               (state_memory_stack σ2_st)).
                   { eapply top_frame_unprom_frame_eq; [symmetry; exact Hfs_st | exact Htf_al]. }
                   destruct va1 as [[varg | | | | | | |] | |];
                     try apply refine_cfg_raise_both.
                   eapply refine_prov_obs_eq;
                     [symmetry; apply interp_cfg_model_ret
                     | symmetry; apply interp_cfg_model_ret |].
                   apply refine_prov_ret.
                   exists pr_va, bs, vs, σ1_st, σ2_st.
                   repeat split; assumption.
  Qed.

  Lemma pop_call_frame_stage1_unprom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf_cur1 sf_prev1 sf_cur2 sf_prev2 : @stack_frame (@ParamsV IP IPT))
    (fstk1 fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Htf : top_frame_unprom_from fs0 G (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev1, fstk1), g)) /\
           s2' = (σ2', ((sf_prev2, fstk2), g)) /\
           stage1_mem_inv U P_unprom G σ1' σ2' /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev1 :: fstk1), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev2 :: fstk2), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind.
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_weaken.
      + apply refine_cfg_memory_event.
        exact (stage1_mempop_unprom fs0 U P_unprom G σ1 σ2 Hinv Htf).
      + intros U' [[σ1' rest1'] r1] [[σ2' rest2'] r2]
          ((<- & <-) & (-> & -> & -> & Hinv' & Hfs')).
        exists σ1', σ2'; repeat split; assumption.
  Qed.

  Lemma pop_call_frame_stage1_prom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf_cur1 sf_prev1 sf_cur2 sf_prev2 : @stack_frame (@ParamsV IP IPT))
    (fstk1 fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev1, fstk1), g)) /\
           s2' = (σ2', ((sf_prev2, fstk2), g)) /\
           stage1_mem_inv U P_unprom G σ1' σ2' /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev1 :: fstk1), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev2 :: fstk2), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind.
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_weaken.
      + apply refine_cfg_memory_event.
        exact (stage1_mempop_prom fs0 U P_unprom gs G σ1 σ2 Hinv Htf).
      + intros U' [[σ1' rest1'] r1] [[σ2' rest2'] r2]
          ((<- & <-) & (-> & -> & -> & Hinv' & Hfs')).
        exists σ1', σ2'; repeat split; assumption.
  Qed.

  Lemma pop_call_frame_stage2_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf_cur1 sf_cur2 sf_prev : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev, fstk), g)) /\
           s2' = (σ2', ((sf_prev, fstk), g)) /\
           mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev :: fstk), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev :: fstk), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind.
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_weaken.
      + apply refine_cfg_memory_event.
        exact (stage2_mempop_restore U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv).
      + intros U' [[σ1' rest1'] r1] [[σ2' rest2'] r2]
          ((<- & <-) & (-> & -> & -> & Heq' & Hfs')).
        exists σ1', σ2'; repeat split; assumption.
  Qed.

  (** *** Promoted [init_op], [mk_store_val_exp], and [mk_load_val_exp] Simulations *)

  Lemma denote_init_copy_poison_exc_r {R1 : Type}
    (ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + R1) ->
          Res (@exc (@ParamsV IP IPT) + unit) -> Prop)
    (init_reg : local_id) (dt : dtyp)
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U : list N) (t1 : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1)))
    (σ2 : state) (sf2 : @stack_frame (@ParamsV IP IPT))
    (fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Href :
       refine_prov RR U t1
         (Ret ((σ2, ((upd_local_sf sf2 (Maps.add init_reg (DVALUE_Base DVALUE_Poison) (stack_vars sf2)),
                      fstk2), g)),
               inr tt))) :
    refine_prov RR U t1
      (interp_cfg_exc ctx2
         (denote_instr
            (IId init_reg,
             INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
             []) va)
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_refl
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (Eexp :
              interp_mcfg_model
                (denote_exp None (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison))
                (σ2, ((sf2, fstk2), g)) ≅
              Ret ((σ2, ((sf2, fstk2), g)), DVALUE_Base DVALUE_Poison)).
    { rewrite (interp_mcfg_model_obs_eq _ _ _
                 (denote_mk_copy_exp None (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison)).
      cbn [denote_exp]; apply interp_mcfg_model_ret. }
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry;
        rewrite Eqit.bind_bind,
          (eq_itree_clo_bind _ _ _ _ Logic.eq Eexp (fun _ _ <- => Logic.eq_refl)),
          !Eqit.bind_ret_l;
        apply interp_cfg_exc_bind
      |].
    eapply refine_prov_tau_star_r.
    - apply tau_star_bind, tau_star_cfg_exc_lwrite.
    - eapply refine_prov_obs_eq;
        [reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; apply interp_cfg_exc_ret
        | exact Href].
  Qed.

  Lemma tau_star_mcfg_lread_some
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_mcfg_model (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_mcfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    exact (fused_local_prov_read_some x v (σ, ((sf, fstk), g)) Hlk).
  Qed.

  Lemma raiseUB_bind_eq {E : Type -> Type} `{UBE -< E} {X Y : Type}
    (msg : string) (k : X -> itree E Y) :
    ITree.bind (raiseUB msg) k ≅ raiseUB msg.
  Proof using.
    unfold raiseUB, trigger_cast; rewrite Eqit.bind_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
  Qed.

  Lemma memM_Merr_mcfg_raise_bind_sim {A1 A2 R2 : Type}
    (RR : list N -> (state * A1) -> R2 -> Prop)
    (U : list N) (msg1 msg2 : string) (σ1 : state) (s2 : FusedS)
    (k2 : Res A2 -> itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Merr state (@ptr ProvenanceV (@PointerV IP)) provenance A1 msg1) σ1)
      (ITree.bind (interp_mcfg_model (raise msg2) s2) k2).
  Proof using.
    cbn [memM_interp_prov].
    assert (Er :
              ITree.bind (interp_mcfg_model (raise msg2) s2) k2 ≅
              ITree.bind (ITree.trigger (Throw (print_msg msg2)))
                (fun v : void => match v with end)).
    { unfold raise, trigger_cast.
      rewrite interp_mcfg_model_bind, Eqit.bind_bind.
      rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
                 (interp_mcfg_model_non_intr (subevent _ (Throw (print_msg msg2))) s2 Logic.eq_refl)
                 (fun _ _ <- => Logic.eq_refl)).
      cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
      unfold fused_trigger_prov, ITree.trigger.
      rewrite !Eqit.bind_bind, !Eqit.bind_vis.
      apply eqit_Vis; intros []. }
    unfold raise, trigger_cast, ITree.trigger at 1.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_vis
      | symmetry; rewrite Er; unfold ITree.trigger; apply Eqit.bind_vis |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma bind_unit_ret_r {E : Type -> Type} (t : itree E unit) :
    ITree.bind t (fun _ : unit => Ret tt) ≅ t.
  Proof using.
    rewrite <- (Eqit.bind_ret_r t) at 2.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _; reflexivity].
  Qed.

  Lemma memM_void_to_mcfg_raise_bind_eq {A2 R2 : Type}
    (msg : string) (σ2 : state) (s2 : FusedS)
    (k2 : Res A2 -> itree ProvBotE R2) :
    ITree.bind
      (memM_interp_prov (@Merr state (@ptr ProvenanceV (@PointerV IP)) provenance void msg) σ2)
      (fun '(_, v) => match v with end) ≅
    ITree.bind (interp_mcfg_model (raise msg) s2) k2.
  Proof using.
    cbn [memM_interp_prov].
    unfold raise, trigger_cast.
    rewrite interp_mcfg_model_bind, !Eqit.bind_bind.
    rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
               (interp_mcfg_model_non_intr (subevent _ (Throw (print_msg msg))) s2 Logic.eq_refl)
               (fun _ _ <- => Logic.eq_refl)).
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    rewrite !Eqit.bind_bind, !Eqit.bind_vis.
    apply eqit_Vis; intros [].
  Qed.

  Lemma denote_mk_store_val_exp_eq (dt : dtyp) (val_exp : exp dtyp) :
    @denote_exp (@ParamsV IP IPT) None (mk_store_val_exp dt val_exp) ≅
    ITree.bind (denote_exp (Some dt) val_exp)
      (fun v =>
         match v with
         | DVALUE_Base db => Ret (DVALUE_Base db)
         | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
         end).
  Proof using.
    unfold mk_store_val_exp; cbn [denote_exp].
    rewrite !Eqit.bind_ret_l, !Eqit.bind_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [db | pk flds | vec elts] _ <-.
    - cbn [dvalue_to_dvalue_base Monads.ret Monad_eitherT Monad_sum EOU_to_itree].
      rewrite !Eqit.bind_ret_l.
      unfold insert_element, extract_element, dvalue_to_Z, VellvmIntegers.signed, VellvmIntegers.zero;
        cbn; rewrite ?Eqit.bind_ret_l; reflexivity.
    - cbn [dvalue_to_dvalue_base EOU_to_itree].
      unfold raise, trigger_cast; rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - cbn [dvalue_to_dvalue_base EOU_to_itree].
      unfold raise, trigger_cast; rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
  Qed.

  Lemma denote_mk_load_val_exp_eq (dt : dtyp) (cur_reg : local_id) :
    @denote_exp (@ParamsV IP IPT) None (mk_load_val_exp dt cur_reg) ≅
    ITree.bind (lread cur_reg)
      (fun v => convert CONV_Bitcast (DTYPE_Array true 1%N dt) (DVALUE_Array true [v]) dt).
  Proof using.
    unfold mk_load_val_exp; cbn [denote_exp lookup_id map_monad Monads.bind Monads.ret Monad_itree].
    rewrite !Eqit.bind_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros v _ <-; rewrite !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma denote_mk_store_val_exp_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (vid : int) (p st_reg : local_id) (dt : dtyp) (val_exp : exp dtyp)
    (anns_st : list (annotation dtyp)) (md_st : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hsc : is_scalar_dtyp dt = true)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
    (Hvars : forall x,
               In x (full_exp_uses val_exp) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists db' bs' σ1',
              U' = U /\ r1 = tt /\ r2 = tt /\
              dvalue_to_memory_bytes dt (DVALUE_Base db') None = raise_ret bs' /\
              s1' = (σ1', ((sf1, fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)),
                           fstk2), g)) /\
              stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
              top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2)))
      U
      (interp_cfg_exc ctx1
         (denote_instr
            (IVoid vid,
             INSTR_Store (dt, val_exp) (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_st,
             md_st) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (denote_instr (IId st_reg, INSTR_Op (mk_store_val_exp dt val_exp), []) va2)
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (EexpR :
              interp_mcfg_model (denote_exp None (mk_store_val_exp dt val_exp))
                (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (denote_exp (Some dt) val_exp) (σ2, ((sf2, fstk2), g)))
                (fun '(s2', v) =>
                   interp_mcfg_model
                     (match v with
                      | DVALUE_Base db => Ret (DVALUE_Base db)
                      | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
                      end) s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_store_val_exp_eq dt val_exp)).
      apply interp_mcfg_model_bind. }
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind
      | symmetry;
        rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq EexpR (fun _ _ <- => Logic.eq_refl)),
          !Eqit.bind_bind;
        reflexivity
      |].
    eapply PassCommon.refine_prov_bind;
      [exact (denote_exp_mcfg_sim (Some dt) val_exp U σ1 σ2 sf1 sf2 fstk1 fstk2 g Hvars) |].
    intros U1 [s1_v v1] [s2_v v2] _ (-> & -> & -> & <- & _).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite Eqit.bind_ret_l; apply interp_cfg_exc_bind | reflexivity |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_refl |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply refine_prov_tau_star_l;
      [apply tau_star_bind, (tau_star_mcfg_lread_some p _ σ1 sf1 fstk1 g Hlk_p) |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity | reflexivity |].
    destruct (assert_alignment_ret_or_ub
                (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) anns_st
                (set_loc (get_file_info md_st) ++ location_error_string md_st ++
                 ": Store with overestimated alignment.")%string)
      as [Hal_ok | Hal_ub].
    - rewrite Hal_ok; cbn [EOU_to_itree].
      assert (Est_l :
                ITree.bind (Ret tt)
                  (fun _ : unit =>
                     ITree.bind (store dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v1)
                       (fun _ : unit => Ret tt)) ≅
                store dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v1).
      { rewrite Eqit.bind_ret_l; apply bind_unit_ret_r. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ Est_l) | reflexivity |];
        clear Est_l.
      assert (Hnonbase :
                forall v_bad : @dvalue (@ParamsV IP IPT),
                  (forall db, v_bad <> DVALUE_Base db) ->
                  refine_prov
                    (exc_post RExc
                       (fun U' s1' s2' r1 r2 =>
                          exists db' bs' σ1',
                            U' = U /\ r1 = tt /\ r2 = tt /\
                            dvalue_to_memory_bytes dt (DVALUE_Base db') None = raise_ret bs' /\
                            s1' = (σ1', ((sf1, fstk1), g)) /\
                            s2' = (σ2, ((upd_local_sf sf2 (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)),
                                         fstk2), g)) /\
                            stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
                            top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2)))
                    U
                    (interp_cfg_exc ctx1
                       (store dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v_bad)
                       (σ1, ((sf1, fstk1), g)))
                    (ITree.bind
                       (interp_mcfg_model (raise "dvalue_to_dvalue_base: non-base dvalue")
                          (σ2, ((sf2, fstk2), g)))
                       (fun '(s2', x) =>
                          ITree.bind (Ret (s2', inr x))
                            (fun '(s2'', res) =>
                               match res with
                               | inl ex => Ret (s2'', inl ex)
                               | inr uv =>
                                   interp_cfg_exc ctx2 (ITree.bind (lwrite st_reg uv) (fun _ => Ret tt)) s2''
                               end)))).
      { clear v1; intros v_bad Hnb; subst dt.
        unfold store, Subevent.trigger; try unfold trigger_cast.
        apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_r
          | symmetry; apply (memM_void_to_mcfg_raise_bind_eq
                               "dvalue_to_dvalue_base: non-base dvalue" σ2) |].
        eapply PassCommon.refine_prov_bind with
          (RPre := fun _ _ '(_, v : void) => match v with end).
        - exact (stage1_store_prom_err
                   (fun _ _ '(_, v : void) => match v with end)
                   U gs v_bad "dvalue_to_dvalue_base: non-base dvalue"%string σ1 σ2 Hsc Hnb).
        - intros _ _ [_ []] _ _. }
      destruct v1 as [db' | pk flds | vec elts].
      + clear Hnonbase.
        eapply refine_prov_obs_eq;
          [reflexivity
          | symmetry;
            rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
                       (interp_mcfg_model_ret _ _) (fun _ _ <- => Logic.eq_refl)),
              !Eqit.bind_ret_l;
            apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r (lwrite st_reg (DVALUE_Base db'))))
          |].
        eapply refine_prov_tau_star_r;
          [apply tau_star_cfg_exc_lwrite |].
        subst dt.
        unfold store, Subevent.trigger; try unfold trigger_cast.
        apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_r
          | symmetry;
            apply (Eqit.bind_ret_l (σ2, tt)
                     (fun _ =>
                        Ret ((σ2, ((upd_local_sf sf2 (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)),
                                    fstk2), g)),
                             inr tt))) |].
        eapply PassCommon.refine_prov_bind;
          [exact (stage1_store_prom_base U P_unprom gs G fs0 db' σ1 σ2 Hinv Htf) |].
        intros U2 [σ1' r1_st] _ _ (bs' & -> & -> & _ & Hser' & Hinv' & Htf').
        apply refine_prov_ret.
        exists db', bs', σ1'.
        repeat split; assumption.
      + apply Hnonbase; intros ? ?; discriminate.
      + apply Hnonbase; intros ? ?; discriminate.
    - rewrite Hal_ub; cbn [EOU_to_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
      apply refine_cfg_exc_raiseUB_l.
  Qed.

  Lemma stage1_load_prom_eq
    (U P_unprom : list N) (G : list ghost_slot)
    (gs : ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    memM_interp_prov
      (handle_memoryM (Load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))) σ1 ≅
    memM_interp_prov
      (Interfaces.Memory.lift (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))) σ1.
  Proof using.
    intros Hinv Hin.
    pose proof Hinv as (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs).
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [(_ & Hpr & Eptrs & _ & Hlen_bs & _) _].
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (_ & Hinv_ptrs & _).
    cbn [handle_memoryM]; unfold read_dvalue, read_bytes.
    rewrite memM_interp_prov_bind, memM_interp_prov_bind, Eptrs.
    cbn [Interfaces.Memory.lift Monads.ret memS_mon memM_interp_prov read_byte MemoryModelPrimitivesV].
    rewrite Eqit.bind_ret_l, memM_interp_prov_map_monad_acc.
    rewrite (map_monad_Read_gs_bytes_eq (gs_ptrs gs) (gs_bytes gs) (gs_addr gs) 0%nat (gs_pr gs) σ1).
    - rewrite Eqit.bind_ret_l; reflexivity.
    - unfold gs_len in Hlen_bs; lia.
    - intros i q Hnth; destruct (Hinv_ptrs i q Hnth) as (_ & Hqi & Hqpr).
      rewrite Hpr in Hqpr; unfold gs_addr; split; [lia | exact Hqpr].
    - intros i mb Hnth; destruct (Hgs gs i mb Hin Hnth) as [Hlk1 _]; exact Hlk1.
  Qed.

  Lemma denote_mk_load_val_exp_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (dst p cur_reg : local_id) (dt : dtyp)
    (anns_ld : list (annotation dtyp)) (md_ld : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hsc : is_scalar_dtyp dt = true)
    (Hmd : is_debug_or_file_md md_ld = true)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dv_ld,
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1, ((upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1
         (denote_instr
            (IId dst,
             INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld,
             md_ld) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (denote_instr (IId dst, INSTR_Op (mk_load_val_exp dt cur_reg), []) va2)
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (is_debug_or_file_md_props md_ld Hmd)
      as (Hlattrs & Hmrange & Hlderef & _).
    pose proof Hinv as (_ & _ & Hall & _).
    rewrite Forall_forall in Hall.
    destruct (Hall gs (or_introl Logic.eq_refl)) as [(_ & _ & _ & Hser & _) _].
    subst dt.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    assert (EexpR :
              interp_mcfg_model (denote_exp None (mk_load_val_exp (gs_dt gs) cur_reg))
                (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (lread cur_reg) (σ2, ((sf2, fstk2), g)))
                (fun '(s2', v) =>
                   interp_mcfg_model
                     (convert CONV_Bitcast (DTYPE_Array true 1%N (gs_dt gs))
                        (DVALUE_Array true [v]) (gs_dt gs)) s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_load_val_exp_eq (gs_dt gs) cur_reg)).
      apply interp_mcfg_model_bind. }
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind
      | symmetry;
        rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq EexpR (fun _ _ <- => Logic.eq_refl)),
          !Eqit.bind_bind;
        reflexivity
      |].
    eapply refine_prov_tau_star_l;
      [apply tau_star_bind, (tau_star_mcfg_lread_some p _ σ1 sf1 fstk1 g Hlk_p) |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some cur_reg _ σ2 sf2 fstk2 g Hlk_cur) |].
    rewrite (convert_bitcast_vec1_scalar_eq (gs_dt gs) (gs_db gs) (gs_bytes gs) Hsc Hser).
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_ret_l; reflexivity
      | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    destruct (assert_alignment_ret_or_ub
                (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) anns_ld
                (set_loc (get_file_info md_ld) ++ location_error_string md_ld ++
                 ": Load with overestimated alignment.")%string)
      as [Hal_ok | Hal_ub].
    - rewrite Hal_ok; cbn [EOU_to_itree].
      assert (Eld_l :
                ITree.bind (Ret tt)
                  (fun _ : unit =>
                     ITree.bind (load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
                       (fun v =>
                          ITree.bind
                            (EOU_to_itree
                               (apply_value_attrs (load_metadata_attrs md_ld)
                                  (set_loc (get_file_info md_ld) ++ location_error_string md_ld ++
                                   ": Loaded value violates !noundef.")%string
                                  (value_metadata_range (metadata_range md_ld) v)))
                            (fun v0 =>
                               ITree.bind
                                 (assert_load_dereferenceable md_ld v0
                                    (set_loc (get_file_info md_ld) ++ location_error_string md_ld ++
                                     ": Loaded value violates !dereferenceable.")%string)
                                 (fun _ => lwrite dst v0)))) ≅
                ITree.bind (load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
                  (fun v => lwrite dst v)).
      { rewrite Eqit.bind_ret_l, Hlattrs, Hmrange.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros v _ <-; cbn [value_metadata_range].
        rewrite apply_value_attrs_nil_eq; cbn [EOU_to_itree].
        rewrite Eqit.bind_ret_l.
        unfold assert_load_dereferenceable; rewrite Hlderef, Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_obs_eq;
        [symmetry;
         rewrite (interp_cfg_exc_obs_eq ctx1 _ _ _ Eld_l);
         apply interp_cfg_exc_bind
        | reflexivity |]; clear Eld_l.
      pose proof (stage1_load_prom_eq U P_unprom (gs :: G) gs σ1 σ2 Hinv (or_introl Logic.eq_refl))
        as Hld_eq.
      destruct (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))
        as [msg | msg | msg | dv_ld] eqn:Edeser; cbn [EOU_to_itree Interfaces.Memory.lift] in *.
      + unfold load, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [reflexivity
          | symmetry; apply (memM_void_to_mcfg_raise_bind_eq msg σ2) |].
        eapply PassCommon.refine_prov_bind with
          (RPre := fun _ _ '(_, v : void) => match v with end).
        * apply refine_cfg_exc_memory_event_l.
          eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
          apply memM_interp_prov_raise_both.
        * intros _ _ [_ []] _ _.
      + unfold load, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [reflexivity | symmetry; apply Eqit.bind_ret_r |].
        eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False).
        * apply refine_cfg_exc_memory_event_l.
          eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
          apply memM_interp_prov_raiseOOM_l.
        * intros _ _ _ _ [].
      + unfold load, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [reflexivity | symmetry; apply Eqit.bind_ret_r |].
        eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False).
        * apply refine_cfg_exc_memory_event_l.
          eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
          apply memM_interp_prov_raiseUB_l.
        * intros _ _ _ _ [].
      + unfold load, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [reflexivity
          | symmetry;
            rewrite (eq_itree_clo_bind _ _ _ _ Logic.eq
                       (interp_mcfg_model_ret _ _) (fun _ _ <- => Logic.eq_refl)),
              !Eqit.bind_ret_l;
            apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r (lwrite dst dv_ld)))
          |].
        eapply refine_prov_obs_eq;
          [reflexivity | symmetry; apply Eqit.bind_ret_r |].
        eapply PassCommon.refine_prov_bind with
          (RPre := fun U' '(s1_ld, res_ld) y2 =>
                     U' = U /\ s1_ld = (σ1, ((sf1, fstk1), g)) /\ res_ld = inr dv_ld /\
                     y2 = ((σ2, ((upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)), fstk2), g)),
                           inr tt)).
        * apply refine_cfg_exc_memory_event_l.
          eapply refine_prov_obs_eq;
            [symmetry; rewrite Hld_eq; reflexivity | reflexivity |].
          cbn [Monads.ret memS_mon memM_interp_prov].
          eapply refine_prov_tau_star_r;
            [apply tau_star_cfg_exc_lwrite |].
          apply refine_prov_ret; repeat split; reflexivity.
        * intros U2 [s1_ld res_ld] y2 _ (-> & -> & -> & ->).
          eapply refine_prov_tau_star_l;
            [apply tau_star_cfg_exc_lwrite |].
          apply refine_prov_ret; exists dv_ld; repeat split; reflexivity.
    - rewrite Hal_ub; cbn [EOU_to_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
      apply refine_cfg_exc_raiseUB_l.
  Qed.

  (** ** 3M. Global-Environment-Preserving Leaf Module Knot & Stage 2 Simulation *)

  Definition mcfg_eq_g_post {R : Type}
    (g0 : @global_env (@ParamsV IP IPT)) (U0 U' : list N)
    (x1 x2 : Res R) : Prop :=
    let '(s1', r1) := x1 in
    let '(s2', r2) := x2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
    snd s1' = snd s2' /\
    snd (snd s1') = g0 /\
    r1 = r2.

  Definition is_non_global_mcfg_ev {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
    | _ => true
    end.

  Definition is_non_global_cfg_ev {X : Type}
    (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => true
    | inr1 me => is_non_global_mcfg_ev me
    end.

  Lemma on_mem_prov_g_sync {T : Type}
    (m : @memM (@ParamsV IP IPT) _ T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Hm : refine_prov (eq_sync_post U) U
            (memM_interp_prov m σ1)
            (memM_interp_prov m σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (on_mem_prov (memM_interp_prov m) (σ1, (ls, g0)))
      (on_mem_prov (memM_interp_prov m) (σ2, (ls, g0))).
  Proof using.
    unfold on_mem_prov.
    eapply PassCommon.refine_prov_bind; [exact Hm |].
    intros U' [σ1' r1] [σ2' r2] _ (Hinc & Heq & <-).
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma on_ls_prov_g_sync {T : Type}
    (f : Monads.stateT (@stack_frame (@ParamsV IP IPT) * stack)
           (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (on_ls_prov f (σ1, (ls, g0)))
      (on_ls_prov f (σ2, (ls, g0))).
  Proof using.
    unfold on_ls_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [ls1' r1] [ls2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst ls2' r2.
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma fused_trigger_prov_g_sync {F : Type -> Type} `{F -< ProvBotE} {T : Type}
    (e : F T) (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (fused_trigger_prov T e (σ1, (ls, g0)))
      (fused_trigger_prov T e (σ2, (ls, g0))).
  Proof using.
    unfold fused_trigger_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma fused_draw_prov_g_sync {T : Type}
    (e : @DrawE (@ParamsV IP IPT) T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (fused_draw_prov T e (σ1, (ls, g0)))
      (fused_draw_prov T e (σ2, (ls, g0))).
  Proof using.
    unfold fused_draw_prov.
    eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma interp_vellvm_prov_h_non_global_g_sync {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X)
    (Hng : is_non_global_mcfg_ev e = true)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (interp_vellvm_prov_h e (σ1, (ls, g0)))
      (interp_vellvm_prov_h e (σ2, (ls, g0))).
  Proof using.
    unfold interp_vellvm_prov_h.
    destruct e as [e1 | [e2 | [e3 | [[e4a | e4b] | [e5 | [e6 | [e7 | [e8 | [e9 | [e10 | e11]]]]]]]]]];
      cbn [case_].
    - apply fused_trigger_prov_g_sync, Heq.
    - unfold fused_intrinsic_prov, handle_intrinsic.
      apply on_mem_prov_g_sync, handle_intrinsicM_equal_sync, Heq.
    - destruct e3 as [gid dv | gid]; [discriminate Hng |].
      unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
      destruct (Maps.lookup gid g0) as [v |];
        cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite !Eqit.bind_ret_l, lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret;
          exact (conj (incl_refl U) (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
      + unfold raise, trigger_cast, ITree.trigger, lift_bot_prov;
          cbn [Monads.bind Monads.ret Monad_stateT Monad_itree].
        pstep; apply RP_Step; unfold rp_step_body.
        rewrite !observe_bind, !unfold_translate; cbn; right; right; split; [exact I | intros [] [] _].
    - unfold fused_local_prov; apply on_ls_prov_g_sync, Heq.
    - unfold fused_stack_prov; apply on_ls_prov_g_sync, Heq.
    - unfold fused_memory_prov, handle_memory.
      apply on_mem_prov_g_sync, handle_memoryM_equal_sync, Heq.
    - apply fused_draw_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
  Qed.

  Inductive ev_ok_ {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (r : itree E R -> Prop) : itree E R -> Prop :=
  | EOK_Ret (x : R) (t : itree E R) :
      observe t = RetF x -> ev_ok_ ok_ev r t
  | EOK_Tau (m t : itree E R) :
      observe t = TauF m -> r m -> ev_ok_ ok_ev r t
  | EOK_Vis X (e : E X) (k : X -> itree E R) (t : itree E R) :
      observe t = VisF e k ->
      ok_ev X e = true ->
      (forall x, r (k x)) ->
      ev_ok_ ok_ev r t.

  Lemma ev_ok__mon {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) :
    monotone1 (@ev_ok_ E R ok_ev).
  Proof using.
    intros t r r' H Hle.
    destruct H as [x t Ho | m t Ho Hm | X e k t Ho Hok Hk].
    - exact (EOK_Ret ok_ev r' x t Ho).
    - exact (EOK_Tau ok_ev r' m t Ho (Hle _ Hm)).
    - exact (EOK_Vis ok_ev r' X e k t Ho Hok (fun x => Hle _ (Hk x))).
  Qed.
  #[local] Hint Resolve ev_ok__mon : paco.

  Definition ev_ok {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (t : itree E R) : Prop :=
    paco1 (ev_ok_ ok_ev) bot1 t.

  Lemma ev_ok_obs_eq {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (t1 t2 : itree E R) :
    t1 ≅ t2 ->
    ev_ok ok_ev t1 ->
    ev_ok ok_ev t2.
  Proof using.
    revert t1 t2; pcofix CIH; intros t1 t2 Heq Hok; pstep.
    punfold Hok; punfold Heq; red in Heq.
    destruct Hok as [x t1' Ho1 | m1 t1' Ho1 Hm1 | X e k1 t1' Ho1 He Hk1];
      rewrite Ho1 in Heq; inversion Heq; subst; pclearbot.
    - eapply EOK_Ret; symmetry; eassumption.
    - eapply EOK_Tau; [symmetry; eassumption | right; eapply CIH; eassumption].
    - match goal with
      | Hobs : VisF _ _ = observe t2 |- _ =>
          eapply EOK_Vis; [symmetry; exact Hobs | exact He |]
      end.
      intros x; right; eapply CIH; [| exact (Hk1 x)].
      match goal with Hrel : forall v, upaco2 _ _ _ _ |- _ => specialize (Hrel x); pclearbot; exact Hrel end.
  Qed.

  Lemma ev_ok_ret {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (x : R) :
    ev_ok ok_ev (Ret x).
  Proof using.
    pstep; exact (EOK_Ret ok_ev _ x (Ret x) Logic.eq_refl).
  Qed.

  Lemma ev_ok_trigger {E : Type -> Type} {X : Type}
    (ok_ev : forall Y, E Y -> bool) (e : E X) :
    ok_ev X e = true ->
    ev_ok ok_ev (ITree.trigger e).
  Proof using.
    intros Hok; pstep.
    refine (EOK_Vis ok_ev _ X e (fun x => Ret x) (ITree.trigger e) Logic.eq_refl Hok _).
    intros x; left; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_bind {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool)
    (t : itree E A) (k : A -> itree E B) :
    ev_ok ok_ev t ->
    (forall a, ev_ok ok_ev (k a)) ->
    ev_ok ok_ev (ITree.bind t k).
  Proof using.
    intros Ht Hk.
    assert (Hgen : forall b : itree E B,
              (exists t0, ITree.bind t0 k ≅ b /\ ev_ok ok_ev t0) ->
              ev_ok ok_ev b).
    { pcofix CIH; intros b (t0 & Eb & Ht0); punfold Ht0.
      destruct Ht0 as [a t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
      - assert (Eka : k a ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pose proof (ev_ok_obs_eq ok_ev (k a) b Eka (Hk a)) as Hb.
        punfold Hb; pstep; eapply ev_ok__mon; [exact Hb | intros ? []; contradiction].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        inversion Eb; subst; pclearbot.
        eapply EOK_Tau; [symmetry; eassumption |].
        right; apply CIH; exists m; split; [assumption | exact Hm].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        inversion Eb; subst; pclearbot.
        match goal with
        | Hobs : VisF _ _ = observe b |- _ =>
            eapply EOK_Vis; [symmetry; exact Hobs | exact Hok |]
        end.
        intros x; right; apply CIH; exists (h x); split; [| exact (Hh x)].
        match goal with Hrel : forall v, upaco2 _ _ _ _ |- _ => specialize (Hrel x); pclearbot; exact Hrel end. }
    apply Hgen; exists t; split; [reflexivity | exact Ht].
  Qed.

  Lemma ev_ok_EOU_mcfg {R : Type} (m : EOU R) :
    ev_ok (@is_non_global_mcfg_ev) (EOU_to_itree m).
  Proof using.
    destruct m as [msg | msg | msg | x]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - unfold raiseOOM, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - unfold raiseUB, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - apply ev_ok_ret.
  Qed.

  Lemma m2r_assoc_in {K V : Type} {Heq : RelDec (@Logic.eq K)} {Hcorr : RelDec_Correct Heq}
    (k : K) (l : list (K * V)) (v : V) :
    assoc k l = Some v ->
    exists k0, In (k0, v) l.
  Proof using.
    induction l as [| [k0 v0] rest IH]; cbn [assoc]; [intros H; discriminate H |].
    destruct (rel_dec k k0).
    - intros H; inversion H; subst v0; exists k0; left; reflexivity.
    - intros H; destruct (IH H) as [k1 Hin]; exists k1; right; exact Hin.
  Qed.

  Lemma defined_intrinsics_ev_ok :
    Forall
      (fun '(_, f) =>
         forall args va,
           ev_ok (@is_non_global_mcfg_ev) (f args va))
      (@defined_intrinsics (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _).
  Proof using.
    assert (Hpure : forall pf args va,
              ev_ok (@is_non_global_mcfg_ev)
                (@pure_to_semantic (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ pf args va)).
    { intros pf args va; unfold pure_to_semantic; apply ev_ok_EOU_mcfg. }
    assert (Hpbase : forall pbf args va,
              ev_ok (@is_non_global_mcfg_ev)
                (@pure_base_to_semantic (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ pbf args va)).
    { intros pbf args va; unfold pure_base_to_semantic; apply Hpure. }
    assert (Hmap_pb :
              forall {A} (xs : list A) d_fn f_fn,
                Forall
                  (fun '(_, f) => forall args va, ev_ok (@is_non_global_mcfg_ev) (f args va))
                  (List.map (fun x => (d_fn x, @pure_base_to_semantic (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ (f_fn x))) xs)).
    { intros A xs d_fn f_fn; induction xs as [| x xs' IH]; constructor; [apply Hpbase | exact IH]. }
    assert (Hmap_p :
              forall {A} (xs : list A) d_fn f_fn,
                Forall
                  (fun '(_, f) => forall args va, ev_ok (@is_non_global_mcfg_ev) (f args va))
                  (List.map (fun x => (d_fn x, @pure_to_semantic (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ (f_fn x))) xs)).
    { intros A xs d_fn f_fn; induction xs as [| x xs' IH]; constructor; [apply Hpure | exact IH]. }
    unfold defined_intrinsics, extra_fp_intrinsics, extra_int_intrinsics,
           mk_int_unop_defs, mk_int_unop_flag_defs, mk_int_binop_defs,
           mk_expect_int_defs, mk_int_ternop_defs, mk_int_ovf_binop_defs.
    repeat apply Forall_app; repeat split;
      try apply Hmap_pb; try apply Hmap_p.
    - repeat constructor; intros args va; apply Hpbase.
    - repeat constructor; intros args va; apply Hpbase.
    - constructor; [intros args va; apply Hpbase |].
      constructor; [intros args va; apply Hpbase |].
      constructor.
      + intros args va; unfold llvm_va_start.
        destruct args as [| a [| ? ?]], va as [vp |];
          try (unfold raise, trigger_cast; eapply ev_ok_bind; [apply ev_ok_trigger; reflexivity | intros []]).
        destruct a as [db | |].
        * destruct db;
            try (eapply ev_ok_bind;
                 [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
                 | intros _; apply ev_ok_ret]).
          unfold raiseUB, trigger_cast; eapply ev_ok_bind; [apply ev_ok_trigger; reflexivity | intros []].
        * eapply ev_ok_bind;
            [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
            | intros _; apply ev_ok_ret].
        * eapply ev_ok_bind;
            [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
            | intros _; apply ev_ok_ret].
      + constructor.
        * intros args va; unfold llvm_va_end; apply ev_ok_ret.
        * constructor; [| constructor].
          intros args va; unfold llvm_va_copy.
          destruct args as [| dest [| src [| ? ?]]];
            try (unfold raise, trigger_cast; eapply ev_ok_bind; [apply ev_ok_trigger; reflexivity | intros []]).
          eapply ev_ok_bind;
            [unfold load, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity |].
          intros vargs; eapply ev_ok_bind;
            [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity |].
          intros _; apply ev_ok_ret.
  Qed.

  Lemma interp_state_ev_ok_g_sync {R : Type}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (Hok : ev_ok (@is_non_global_mcfg_ev) t)
    (g0 : @global_env (@ParamsV IP IPT)) (U0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U0) U0
      (interp_state interp_vellvm_prov_h t (σ1, (ls, g0)))
      (interp_state interp_vellvm_prov_h t (σ2, (ls, g0))).
  Proof using.
    set (k_cont := fun {X : Type} (k : X -> @MCFGtop (@ParamsV IP IPT) R)
                       '(s', x) => Tau (interp_state interp_vellvm_prov_h (k x) s')).
    set (rel := fun (U : list N) (a1 a2 : itree ProvBotE (Res R)) =>
                  (exists t0 s_a s_b ls0,
                     interp_state interp_vellvm_prov_h t0 (s_a, (ls0, g0)) ≅ a1 /\
                     interp_state interp_vellvm_prov_h t0 (s_b, (ls0, g0)) ≅ a2 /\
                     ev_ok (@is_non_global_mcfg_ev) t0 /\
                     incl U0 U /\
                     mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) \/
                  (exists X (u1 u2 : itree ProvBotE (Res X)) (k : X -> @MCFGtop (@ParamsV IP IPT) R),
                     ITree.bind u1 (k_cont X k) ≅ a1 /\
                     ITree.bind u2 (k_cont X k) ≅ a2 /\
                     (forall x, ev_ok (@is_non_global_mcfg_ev) (k x)) /\
                     refine_prov (mcfg_eq_g_post g0 U0) U u1 u2)).
    assert (Hobs : forall U a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> rel U a1 a2 -> rel U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 [(t0 & s_a & s_b & ls0 & Ea & Eb & Ht0 & Hinc & Hm)
                                   | (X & u1 & u2 & k & Ea & Eb & Hk & Hu)].
      - left; exists t0, s_a, s_b, ls0;
          exact (conj (transitivity Ea E1) (conj (transitivity Eb E2) (conj Ht0 (conj Hinc Hm)))).
      - right; exists X, u1, u2, k;
          exact (conj (transitivity Ea E1) (conj (transitivity Eb E2) (conj Hk Hu))). }
    assert (Hbind_step :
              forall X U (u1 u2 : itree ProvBotE (Res X)) k,
                (forall x, ev_ok (@is_non_global_mcfg_ev) (k x)) ->
                refine_prov (mcfg_eq_g_post g0 U0) U u1 u2 ->
                refine_prov_ (mcfg_eq_g_post g0 U0) rel U
                  (ITree.bind u1 (k_cont X k))
                  (ITree.bind u2 (k_cont X k))).
    { intros X U u1 u2 k Hk Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          left; exists (k x1), s_a', s_b', ls1';
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj (Hk x1) (conj Hinc Hm)))).
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          right; exists X, m1, m2, k;
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hk Hstep))).
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_cont X k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            right; exists X, (h1 p), u2, k;
              exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hk Hleft))).
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_cont X k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               right; exists X, (h1 p), (h2 p), k;
                 exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hk Hboth))).
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               right; exists X, (h1 a1), (h2 a2), k;
                 exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hk HA))).
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_cont X k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_cont X k)), Hu2; reflexivity | exact IH]. }
    assert (Hcore : forall U a1 a2, rel U a1 a2 -> refine_prov (mcfg_eq_g_post g0 U0) U a1 a2).
    { pcofix CIH; intros U a1 a2 Hst; pstep.
      eapply refine_prov__mon with (r := rel); [| intros U' x1 x2 Hx; right; apply CIH, Hx].
      destruct Hst as [(t0 & s_a & s_b & ls0 & E1 & E2 & Ht0 & Hinc & Hm)
                      | (X & u1 & u2 & k & E1 & E2 & Hk & Hu)].
      - eapply refine_prov__obs_eq; [exact Hobs | exact E1 | exact E2 |].
        punfold Ht0; destruct Ht0 as [rv t0' Hot | mt t0' Hot Hmt | X e k t0' Hot He Hk]; pclearbot.
        + assert (Et1 : Ret ((s_a, (ls0, g0)), rv) ≅ interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_ret).
          assert (Et2 : Ret ((s_b, (ls0, g0)), rv) ≅ interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_ret).
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply RP_Step; cbn;
            exact (conj Hinc (conj Hm (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
        + assert (Et1 : Tau (interp_state interp_vellvm_prov_h mt (s_a, (ls0, g0))) ≅
                        interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_tau).
          assert (Et2 : Tau (interp_state interp_vellvm_prov_h mt (s_b, (ls0, g0))) ≅
                        interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_tau).
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply RP_Step; cbn; left; exists mt, s_a, s_b, ls0;
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hmt (conj Hinc Hm)))).
        + assert (Et1 : ITree.bind (interp_vellvm_prov_h X e (s_a, (ls0, g0))) (k_cont X k) ≅
                        interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0))).
          { symmetry; rewrite (itree_eta t0'), Hot, interp_state_vis.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [? ?] _ <-; reflexivity]. }
          assert (Et2 : ITree.bind (interp_vellvm_prov_h X e (s_b, (ls0, g0))) (k_cont X k) ≅
                        interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0))).
          { symmetry; rewrite (itree_eta t0'), Hot, interp_state_vis.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [? ?] _ <-; reflexivity]. }
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply Hbind_step; [exact Hk |].
          eapply refine_prov_weaken;
            [exact (interp_vellvm_prov_h_non_global_g_sync e He g0 U s_a s_b ls0 Hm) |].
          intros U' [s1' r1] [s2' r2] (Huu' & Hm' & Hrs & Hg' & Hr);
            exact (conj (incl_tran Hinc Huu') (conj Hm' (conj Hrs (conj Hg' Hr)))).
      - eapply refine_prov__obs_eq; [exact Hobs | exact E1 | exact E2 |].
        exact (Hbind_step X U u1 u2 k Hk Hu). }
    apply Hcore; left; exists t, σ1, σ2, ls;
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hok (conj (incl_refl U0) Heq)))).
  Qed.

  Lemma trigger_mcfg_non_global_g_sync {X : Type}
    (me : @MCFGEtop (@ParamsV IP IPT) X)
    (Hng : is_non_global_mcfg_ev me = true)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (interp_mcfg_model (ITree.trigger me) (σ1, (ls, g0)))
      (interp_mcfg_model (ITree.trigger me) (σ2, (ls, g0))).
  Proof using.
    unfold interp_mcfg_model.
    apply interp_state_ev_ok_g_sync; [| exact Heq].
    unfold interp_intrinsics.
    assert (Etr : interp interp_intrinsics_h (ITree.trigger me) ≅
                  ITree.bind (interp_intrinsics_h X me) (fun x => Tau (Ret x))).
    { unfold ITree.trigger; rewrite unfold_interp; cbn [_interp observe].
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x _ <-; rewrite interp_ret; reflexivity. }
    eapply ev_ok_obs_eq; [symmetry; exact Etr |].
    eapply ev_ok_bind; [| intros x; pstep; eapply EOK_Tau; [reflexivity | left; apply ev_ok_ret]].
    destruct me as [e1 | [ie | fe]].
    - cbn [interp_intrinsics_h case_ E_trigger Subevent.trigger]; apply ev_ok_trigger; reflexivity.
    - cbn [interp_intrinsics_h case_].
      unfold handle_intrinsics.
      destruct ie as [dt fname args va]; cbn.
      destruct (assoc fname defs_assoc) as [f |] eqn:Eassoc.
      + apply m2r_assoc_in in Eassoc as [k0 Hin].
        unfold defs_assoc in Hin; apply in_map_iff in Hin as ([decl f0] & Heq_p & Hin_def).
        inversion Heq_p; subst f0.
        pose proof defined_intrinsics_ev_ok as Hall; rewrite Forall_forall in Hall.
        exact (Hall (decl, f) Hin_def args va).
      + cbn; apply ev_ok_trigger; reflexivity.
    - cbn [interp_intrinsics_h case_ F_trigger Subevent.trigger].
      apply ev_ok_trigger, Hng.
  Qed.

  Lemma ev_ok_tau {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (m : itree E R) :
    ev_ok ok_ev m ->
    ev_ok ok_ev (Tau m).
  Proof using.
    intros Hm; pstep; exact (EOK_Tau ok_ev _ m (Tau m) Logic.eq_refl (or_introl Hm)).
  Qed.

  Lemma ev_ok_fmap {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool) (f : A -> B) (t : itree E A) :
    ev_ok ok_ev t ->
    ev_ok ok_ev (f <$> t).
  Proof using.
    intros Ht; unfold Functor.fmap, Functor_itree, ITree.map.
    eapply ev_ok_bind; [exact Ht | intros a; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_map_monad {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool)
    (f : A -> itree E B) (xs : list A) :
    (forall a, In a xs -> ev_ok ok_ev (f a)) ->
    ev_ok ok_ev (map_monad f xs).
  Proof using.
    intros Hf; induction xs as [| x xs' IH];
      cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply Hf; left; reflexivity |].
      intros b; eapply ev_ok_bind.
      + apply IH; intros a Ha; apply Hf; right; exact Ha.
      + intros bs; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_loop_monad {E : Type -> Type} {A : Type}
    (ok_ev : forall X, E X -> bool)
    (f : A -> itree E unit) (xs : list A) :
    (forall a, In a xs -> ev_ok ok_ev (f a)) ->
    ev_ok ok_ev (loop_monad f xs).
  Proof using.
    intros Hf; induction xs as [| x xs' IH];
      cbn [loop_monad Monads.bind Monads.ret Monad_itree].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply Hf; left; reflexivity |].
      intros []; apply IH; intros a Ha; apply Hf; right; exact Ha.
  Qed.

  Lemma ev_ok_iter {E : Type -> Type} {I R : Type}
    (ok_ev : forall X, E X -> bool)
    (body : I -> itree E (I + R)) (i0 : I) :
    (forall i, ev_ok ok_ev (body i)) ->
    ev_ok ok_ev (ITree.iter body i0).
  Proof using.
    intros Hbody.
    set (k_it := fun lr : I + R =>
                   match lr with
                   | inl j => Tau (ITree.iter body j)
                   | inr r => Ret r
                   end).
    assert (Hgen : forall b : itree E R,
              (exists t0, ITree.bind t0 k_it ≅ b /\ ev_ok ok_ev t0) ->
              ev_ok ok_ev b).
    { pcofix CIH; intros b (t0 & Eb & Ht0); punfold Ht0.
      destruct Ht0 as [[j | rv] t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
      - assert (Et : Tau (ITree.iter body j) ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pstep; punfold Et; red in Et; cbn in Et; inversion Et; subst; pclearbot.
        eapply EOK_Tau; [symmetry; eassumption |].
        right; apply CIH; exists (body j); split; [| exact (Hbody j)].
        etransitivity; [symmetry; apply unfold_iter | assumption].
      - assert (Er : Ret rv ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pstep; punfold Er; red in Er; cbn in Er; inversion Er; subst.
        eapply EOK_Ret; symmetry; eassumption.
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        inversion Eb; subst; pclearbot.
        eapply EOK_Tau; [symmetry; eassumption |].
        right; apply CIH; exists m; split; [assumption | exact Hm].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        inversion Eb; subst; pclearbot.
        match goal with
        | Hobs : VisF _ _ = observe b |- _ =>
            eapply EOK_Vis; [symmetry; exact Hobs | exact Hok |]
        end.
        intros x; right; apply CIH; exists (h x); split; [| exact (Hh x)].
        match goal with Hrel : forall v, upaco2 _ _ _ _ |- _ => specialize (Hrel x); pclearbot; exact Hrel end. }
    apply Hgen; exists (body i0); split; [symmetry; apply unfold_iter | exact (Hbody i0)].
  Qed.

  Lemma ev_ok_cfg_subevent {F : Type -> Type} `{F -< @CFGEtop (@ParamsV IP IPT)} {X : Type}
    (e : F X)
    (Hok : is_non_global_cfg_ev (subevent X e) = true) :
    ev_ok (@is_non_global_cfg_ev) (Subevent.trigger e).
  Proof using.
    unfold Subevent.trigger; apply ev_ok_trigger, Hok.
  Qed.

  Lemma ev_ok_cfg_raise {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raise (@CFGEtop (@ParamsV IP IPT)) A _ msg).
  Proof using.
    unfold raise, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseOOM {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raiseOOM (@CFGEtop (@ParamsV IP IPT)) _ A msg).
  Proof using.
    unfold raiseOOM, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseUB {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raiseUB (@CFGEtop (@ParamsV IP IPT)) _ A msg).
  Proof using.
    unfold raiseUB, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseLLVM {A : Type} (x : @exc (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@raiseLLVM (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) A _ x).
  Proof using.
    unfold raiseLLVM, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_EOU_cfg {R : Type} (m : EOU R) :
    ev_ok (@is_non_global_cfg_ev) (EOU_to_itree m).
  Proof using.
    destruct m as [msg | msg | msg | x]; cbn [EOU_to_itree].
    - apply ev_ok_cfg_raise.
    - apply ev_ok_cfg_raiseOOM.
    - apply ev_ok_cfg_raiseUB.
    - apply ev_ok_ret.
  Qed.

  Lemma ev_ok_withCall_ret {R : Type} (x : R) :
    ev_ok (@is_non_global_cfg_ev) (withCall (Ret x)).
  Proof using.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_ret_eq | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_withCall_bind {A B : Type}
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) :
    ev_ok (@is_non_global_cfg_ev) (withCall u) ->
    (forall a, ev_ok (@is_non_global_cfg_ev) (withCall (k a))) ->
    ev_ok (@is_non_global_cfg_ev) (withCall (ITree.bind u k)).
  Proof using.
    intros Hu Hk.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_bind_eq |].
    exact (ev_ok_bind (@is_non_global_cfg_ev) (withCall u) (fun x => withCall (k x)) Hu Hk).
  Qed.

  Lemma ev_ok_withCall_trigger {X : Type} (me : @MCFGEtop (@ParamsV IP IPT) X) :
    is_non_global_mcfg_ev me = true ->
    ev_ok (@is_non_global_cfg_ev) (withCall (ITree.trigger me)).
  Proof using.
    intros Hng.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_trigger_eq |].
    apply ev_ok_trigger, Hng.
  Qed.

  Lemma ev_ok_withCall_EOU {A : Type} (m : EOU A) :
    ev_ok (@is_non_global_cfg_ev) (withCall (EOU_to_itree m)).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - unfold raiseOOM, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - unfold raiseUB, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - apply ev_ok_withCall_ret.
  Qed.

  Lemma ev_ok_withCall_map_monad {A B : Type}
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A) :
    (forall a, In a xs -> ev_ok (@is_non_global_cfg_ev) (withCall (f a))) ->
    ev_ok (@is_non_global_cfg_ev) (withCall (map_monad f xs)).
  Proof using.
    intros Hf; induction xs as [| a xs' IH];
      cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply ev_ok_withCall_ret.
    - eapply ev_ok_withCall_bind; [apply Hf; left; reflexivity |].
      intros b; eapply ev_ok_withCall_bind.
      + apply IH; intros a' Ha'; apply Hf; right; exact Ha'.
      + intros bs; apply ev_ok_withCall_ret.
  Qed.

  Lemma ev_ok_withCall_convert
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp) :
    ev_ok (@is_non_global_cfg_ev) (withCall (convert ct t_from dv t_to)).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply ev_ok_withCall_ret |].
      destruct (@bit_sizeof_dtyp SizeofV t_from =? @bit_sizeof_dtyp SizeofV t_to)%N.
      + apply ev_ok_withCall_EOU.
      + apply (ev_ok_withCall_EOU (raise_error _)).
    - apply ev_ok_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast;
        apply ev_ok_withCall_trigger; reflexivity.
  Qed.

  Lemma ev_ok_withCall_freeze_base
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (withCall (freeze_base dt db)).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | sz bv | |].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
          eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [Monads.bind Monads.ret Monad_itree].
        * eapply ev_ok_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast;
               apply ev_ok_withCall_trigger; reflexivity.
          -- intros x; apply ev_ok_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
            eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, Monads.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros _; apply ev_ok_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast;
        apply ev_ok_withCall_trigger; reflexivity.
  Qed.

  Lemma ev_ok_withCall_freeze
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (withCall (freeze dt dv)).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt Hle; induction sz as [| sz IH]; intros dv dt Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply ev_ok_withCall_freeze_base.
      + destruct dt as [| | p' dts];
          try apply (ev_ok_withCall_EOU (raise_error _)).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply ev_ok_withCall_bind; [| intros _; apply ev_ok_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert dts Hfld; induction fields as [| v vs IHf]; intros [| t ts] Hfld acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply ev_ok_withCall_ret.
        * apply (ev_ok_withCall_EOU (raise_error _)).
        * apply (ev_ok_withCall_EOU (raise_error _)).
        * eapply ev_ok_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros v'; apply IHf; lia.
      + destruct dt as [| v' sz_n t |];
          try apply (ev_ok_withCall_EOU (raise_error _)).
        cbn [Monads.bind Monads.ret Monad_itree].
        eapply ev_ok_withCall_bind; [| intros _; apply ev_ok_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts <= sz)%nat) by lia.
        clear Hle; generalize (@nil (@dvalue (@ParamsV IP IPT))) as acc.
        revert Helt; induction elts as [| v vs IHe]; intros Helt acc;
          cbn [Monads.bind Monads.ret Monad_itree].
        * apply ev_ok_withCall_ret.
        * eapply ev_ok_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) _ _ _ _ t v); apply IH; lia.
          -- intros v'; apply IHe; lia.
  Qed.

  Lemma ev_ok_denote_exp' (top : option dtyp) (e : exp dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_exp' (@ParamsV IP IPT) top e).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e Hle; induction sz as [| sz IH]; intros top e Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)),
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S sz)%nat ->
          ev_ok (@is_non_global_cfg_ev)
            (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts))).
      { intros elts Helts; apply ev_ok_withCall_map_monad.
        intros [dt0 ex0] Hin; apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [exact Hin | lia]]. }
      destruct e; cbn [denote_exp Monads.bind Monads.ret Monad_itree]; cbn [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply ev_ok_withCall_trigger; reflexivity.
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + destruct b; apply ev_ok_withCall_ret.
      + apply ev_ok_withCall_ret.
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros _; apply ev_ok_withCall_ret].
      + apply ev_ok_withCall_ret.
      + apply ev_ok_withCall_ret.
      + eapply ev_ok_withCall_bind; [apply (Hlist fields Hle) | intros _; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply ev_ok_withCall_EOU |].
        intros []; eapply ev_ok_withCall_bind; [apply (Hlist fields Hle) | intros _; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros _; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros _; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; lia | intros _; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; lia | intros _; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; lia | intros _; apply ev_ok_withCall_EOU]].
      + destruct op as [dt1 op1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; lia | intros _; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros _; apply ev_ok_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros _; eapply ev_ok_withCall_bind; [apply Hlist; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros _; eapply ev_ok_withCall_bind.
        * eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU].
        * intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_freeze].
      + apply (ev_ok_withCall_EOU (raise_error _)).
      + destruct md as [[dt1 ex1] | | | | | |];
          try apply ev_ok_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_EOU |].
        intros [sz_v t_v]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros _; apply ev_ok_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast;
          apply ev_ok_withCall_trigger; reflexivity.
  Qed.

  Lemma ev_ok_run_exc {A : Type} (t : @CFGtop (@ParamsV IP IPT) A) :
    ev_ok (@is_non_global_cfg_ev) t ->
    ev_ok (@is_non_global_cfg_ev) (run_exc t).
  Proof using.
    intros Ht.
    assert (Hgen : forall b : @CFGtop (@ParamsV IP IPT) (@exc (@ParamsV IP IPT) + A),
              (exists t0, (run_exc t0 ≅ b \/ Tau (run_exc t0) ≅ b) /\
                          ev_ok (@is_non_global_cfg_ev) t0) ->
              ev_ok (@is_non_global_cfg_ev) b).
    { pcofix CIH; intros b (t0 & [Eb | Eb] & Ht0).
      - punfold Ht0.
        destruct Ht0 as [a t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
        + assert (Er : Ret (inr a) ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          pstep; punfold Er; red in Er; cbn in Er; inversion Er; subst.
          eapply EOK_Ret; symmetry; eassumption.
        + assert (Et : Tau (run_exc m) ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          pstep; punfold Et; red in Et; cbn in Et; inversion Et; subst; pclearbot.
          eapply EOK_Tau; [symmetry; eassumption |].
          right; apply CIH; exists m; split; [left; assumption | exact Hm].
        + assert (Ev : match exc_of_event e with
                       | Some x => Ret (inl x)
                       | None => Vis e (fun y => Tau (run_exc (h y)))
                       end ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          destruct (exc_of_event e) as [x |].
          * pstep; punfold Ev; red in Ev; cbn in Ev; inversion Ev; subst.
            eapply EOK_Ret; symmetry; eassumption.
          * pstep; punfold Ev; red in Ev; cbn in Ev; inversion Ev; subst; pclearbot.
            match goal with
            | Hobs : VisF _ _ = observe b |- _ =>
                eapply EOK_Vis; [symmetry; exact Hobs | exact Hok |]
            end.
            intros y; right; apply CIH; exists (h y); split; [| exact (Hh y)].
            right.
            match goal with Hrel : forall v, upaco2 _ _ _ _ |- _ => specialize (Hrel y); pclearbot; exact Hrel end.
      - pstep; punfold Eb; red in Eb; cbn in Eb; inversion Eb; subst; pclearbot.
        eapply EOK_Tau; [symmetry; eassumption |].
        right; apply CIH; exists t0; split; [left; assumption | exact Ht0]. }
    apply Hgen; exists t; split; [left; reflexivity | exact Ht].
  Qed.

  Lemma ev_ok_assert_dereferenceable
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@assert_dereferenceable (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ or_null n v msg).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [p | ? ? | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raise.
    - destruct ((or_null && (ptr_to_int p =? ptr_to_int null)%Z) || (n =? 0)%N).
      + apply ev_ok_ret.
      + eapply ev_ok_bind;
          [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_assert_attrs_dereferenceable
    (attrs : list param_attr) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@assert_attrs_dereferenceable (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ attrs v msg).
  Proof using.
    unfold assert_attrs_dereferenceable.
    destruct (find_option attr_dereferenceable attrs) as [[or_null n] |];
      [| apply ev_ok_ret].
    destruct v as [db | |]; [| apply ev_ok_ret | apply ev_ok_ret].
    destruct db; try apply ev_ok_ret; apply ev_ok_assert_dereferenceable.
  Qed.

  Lemma ev_ok_assert_load_dereferenceable
    (md : list (metadata dtyp)) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@assert_load_dereferenceable (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ md v msg).
  Proof using.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |];
      [apply ev_ok_assert_dereferenceable | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_apply_attrs
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@apply_attrs (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg |].
    intros v'; eapply ev_ok_bind;
      [apply ev_ok_assert_attrs_dereferenceable | intros _; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_apply_args_attrs
    (attrss : list (list param_attr)) (msg : string) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@apply_args_attrs (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ attrss msg args).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - apply ev_ok_ret.
    - destruct attrss as [| a r];
        eapply ev_ok_bind; [apply ev_ok_apply_attrs |];
        intros v'; eapply ev_ok_bind; [apply IH | intros vs'; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_check_call_return
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (res : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev)
      (@check_call_return (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _
         fattrs ret_attrs ranges loc args res).
  Proof using.
    unfold check_call_return.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg |].
    intros _; destruct res as [ex | v]; [apply ev_ok_ret |].
    eapply ev_ok_bind; [apply ev_ok_apply_attrs | intros v'; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_call_args
    (args : list (texp dtyp * list param_attr)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@denote_call_args (@ParamsV IP IPT) args msg).
  Proof using.
    unfold denote_call_args; apply ev_ok_map_monad.
    intros [[t op] attrs] _; eapply ev_ok_bind;
      [apply ev_ok_denote_exp' | intros v; apply ev_ok_apply_attrs].
  Qed.

  Lemma ev_ok_bundle_check
    (f : exp dtyp) (tag : string)
    (check : @assume_bundle_check (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _)
    (loc : string) (vs : list (@dvalue (@ParamsV IP IPT))) :
    bundle_check f tag = Some check ->
    ev_ok (@is_non_global_cfg_ev) (check loc vs).
  Proof using.
    unfold bundle_check; destruct (is_llvm_assume f); [| intros H; discriminate H].
    unfold assume_bundle_checks; cbn [List.find].
    repeat match goal with
           | |- context [if String.eqb ?a ?b then _ else _] => destruct (String.eqb a b)
           end;
      cbn [option_map snd]; intros H; try discriminate H; inversion H; subst check; clear H.
    - unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]]; try apply ev_ok_cfg_raise.
      destruct (dvalue_ptr_address p) as [a |]; [| apply ev_ok_cfg_raiseUB].
      destruct (a =? 0)%Z; [apply ev_ok_cfg_raiseUB | apply ev_ok_ret].
    - unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]]; try apply ev_ok_cfg_raise.
      destruct (dvalue_well_defined v); [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]]; try apply ev_ok_cfg_raise.
      destruct (dvalue_ptr_address p) as [a |]; [| apply ev_ok_cfg_raiseUB].
      destruct (bundle_uint al) as [n |]; [| apply ev_ok_cfg_raiseUB].
      destruct (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        [| apply ev_ok_cfg_raiseUB].
      destruct ((if is_power_of_two n then (a - o) mod n =? 0 else a =? 0)%Z);
        [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; try apply ev_ok_cfg_raise.
      destruct (dvalue_ptr_address p), (bundle_uint sz); try apply ev_ok_cfg_raiseUB.
      destruct (_ =? 0)%Z; [apply ev_ok_ret | apply ev_ok_assert_dereferenceable].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; try apply ev_ok_cfg_raise.
      destruct (dvalue_ptr_address p), (bundle_uint sz); try apply ev_ok_cfg_raiseUB.
      destruct (_ =? 0)%Z; [apply ev_ok_ret | apply ev_ok_assert_dereferenceable].
  Qed.

  Lemma ev_ok_denote_operand_bundles
    (loc : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_operand_bundles (@ParamsV IP IPT) loc f obs).
  Proof using.
    unfold denote_operand_bundles.
    eapply ev_ok_bind; [| intros _; apply ev_ok_ret].
    apply ev_ok_map_monad; intros ob _.
    eapply ev_ok_bind.
    - apply ev_ok_map_monad; intros [[t e] | s] _;
        [apply ev_ok_denote_exp' | apply ev_ok_ret].
    - intros vs; destruct (bundle_check f (ob_tag ob)) as [check |] eqn:Ebc;
        [eapply ev_ok_bundle_check; exact Ebc | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_cmpxchg (id : raw_id) (cpx : cmpxchg dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_cmpxchg (@ParamsV IP IPT) id cpx).
  Proof using.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val],
             (c_cmp cpx) as [cmp_ty cmp_val],
             (c_new cpx) as [new_ty new_val].
    destruct (dtyp_eq_dec cmp_ty new_ty); [| apply ev_ok_cfg_raise].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros cmp_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros new_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros _].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros loaded_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros dv].
    destruct dv as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [? | sz x | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raise.
    - destruct sz as [? | ? |]; [apply ev_ok_cfg_raise | apply ev_ok_cfg_raise |].
      destruct (equ x one).
      + eapply ev_ok_bind;
          [unfold store; apply ev_ok_cfg_subevent; reflexivity
          | intros _; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
      + unfold lwrite; apply ev_ok_cfg_subevent; reflexivity.
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_denote_atomic_rmw_operation
    (a_op : atomic_rmw_operation) (pv val : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_atomic_rmw_operation (@ParamsV IP IPT) a_op pv val).
  Proof using.
    unfold denote_atomic_rmw_operation.
    destruct a_op;
      try apply ev_ok_ret;
      try apply ev_ok_EOU_cfg;
      try apply ev_ok_cfg_raise.
    destruct val as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db; try apply ev_ok_cfg_raise; apply ev_ok_EOU_cfg.
  Qed.

  Lemma ev_ok_denote_atomicrmw (id : raw_id) (armw : atomicrmw dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_atomicrmw (@ParamsV IP IPT) id armw).
  Proof using.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val], (a_val armw) as [a_ty a_val].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros _].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros loaded_v].
    eapply ev_ok_bind; [apply ev_ok_denote_atomic_rmw_operation | intros stored_v].
    eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros _].
    eapply ev_ok_bind;
      [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_instr
    (i : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_instr (@ParamsV IP IPT) i va).
  Proof using.
    destruct i as [[iid ins] md]; cbn [denote_instr].
    destruct ins as [msg_c | op | [dt f] args anns obs | dt annotations
                    | dt [du ptr_e] anns | [dt val_e] [du ptr_e] anns
                    | sync ord | cpx | armw | [t ptr_e] argty | rty clp cs].
    - destruct iid; [apply ev_ok_cfg_raise | apply ev_ok_ret].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros uv].
      eapply ev_ok_bind;
        [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
    - eapply ev_ok_bind; [apply ev_ok_denote_call_args | intros vs].
      eapply ev_ok_bind; [apply ev_ok_denote_operand_bundles | intros _].
      eapply ev_ok_bind.
      + destruct (intrinsic_exp f) as [s |].
        * unfold intrinsic; apply ev_ok_cfg_subevent; reflexivity.
        * eapply ev_ok_bind;
            [apply ev_ok_denote_exp' | intros fv; unfold call; apply ev_ok_cfg_subevent; reflexivity].
      + intros res; eapply ev_ok_bind; [apply ev_ok_check_call_return | intros res'].
        eapply ev_ok_bind;
          [destruct res' as [ex | dv]; [apply ev_ok_cfg_raiseLLVM | apply ev_ok_ret] |].
        intros rv; destruct iid as [id |];
          [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_ret].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [| intros _; apply ev_ok_ret].
      destruct (find_option ann_num_elements annotations) as [[t num_exp] |].
      + eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros n].
        destruct (dvalue_is_poison n); [apply ev_ok_cfg_raiseUB |].
        eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros n'].
        eapply ev_ok_bind;
          [unfold alloca; apply ev_ok_cfg_subevent; reflexivity
          | intros v; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
      + eapply ev_ok_bind;
          [unfold alloca; apply ev_ok_cfg_subevent; reflexivity
          | intros v; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros _].
      eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros v].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros v'].
      eapply ev_ok_bind;
        [apply ev_ok_assert_load_dereferenceable
        | intros _; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
    - destruct iid; [apply ev_ok_cfg_raise |].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros v].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros _].
      eapply ev_ok_bind; [| intros _; apply ev_ok_ret].
      destruct a as [db | |];
        [destruct db; try (unfold store; apply ev_ok_cfg_subevent; reflexivity);
         apply ev_ok_cfg_raiseUB
        | unfold store; apply ev_ok_cfg_subevent; reflexivity
        | unfold store; apply ev_ok_cfg_subevent; reflexivity].
    - apply ev_ok_ret.
    - destruct iid as [id |]; [apply ev_ok_denote_cmpxchg | apply ev_ok_cfg_raise].
    - destruct iid as [id |]; [apply ev_ok_denote_atomicrmw | apply ev_ok_cfg_raise].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_to_args].
      eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros args].
      eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros retv].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros ix].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros args'].
      eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros _].
      destruct iid as [id |];
        [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_ret].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [unfold stack_get_exc; apply ev_ok_cfg_subevent; reflexivity |].
      intros [e |];
        [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_cfg_raise].
  Qed.

  Lemma ev_ok_denote_code
    (c : code dtyp) (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_code (@ParamsV IP IPT) c va).
  Proof using.
    unfold denote_code; apply ev_ok_loop_monad.
    intros i _; apply ev_ok_denote_instr.
  Qed.

  Lemma ev_ok_denote_phi
    (bid_from : block_id) (pe : local_id * phi dtyp * list (metadata dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_phi (@ParamsV IP IPT) bid_from pe).
  Proof using.
    destruct pe as [[id [anns dt args]] md]; cbn [denote_phi].
    destruct (assoc bid_from args) as [op |]; [| apply ev_ok_cfg_raise].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros uv; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_phis
    (bid_from : block_id) (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_phis (@ParamsV IP IPT) bid_from phis).
  Proof using.
    unfold denote_phis.
    eapply ev_ok_bind; [apply ev_ok_map_monad; intros pe _; apply ev_ok_denote_phi |].
    intros dvs; eapply ev_ok_bind.
    - apply ev_ok_map_monad; intros [id dv] _;
        unfold lwrite; apply ev_ok_cfg_subevent; reflexivity.
    - intros _; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_denote_terminator
    (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_terminator (@ParamsV IP IPT) trm).
  Proof using.
    destruct trm as [[iid tm] md]; cbn [denote_terminator].
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt e] default_br dests
                   | [t addr] brs fn | [t expr]
                   | [dt fnptrval] args to_label unwind_label anns obs |].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros dv; apply ev_ok_ret].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros v].
      destruct v as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
      destruct db as [? | sz x | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raise.
      + destruct sz as [? | ? |]; [apply ev_ok_cfg_raise | apply ev_ok_cfg_raise |].
        destruct (equ x one); apply ev_ok_ret.
      + apply ev_ok_cfg_raiseUB.
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros selector].
      destruct (dvalue_is_poison selector); [apply ev_ok_cfg_raiseUB |].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros bid; apply ev_ok_ret].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      destruct (dvalue_is_poison a); [apply ev_ok_cfg_raiseUB |].
      destruct fn as [f |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind.
      + apply ev_ok_map_monad; intros b _.
        eapply ev_ok_bind;
          [unfold gread; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
      + intros addrs; destruct (dvalue_ptr_address a) as [z |]; [| apply ev_ok_cfg_raise].
        destruct (indirectbr_target z (List.combine brs addrs)) as [b |];
          [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros exn; apply ev_ok_cfg_raiseLLVM].
    - eapply ev_ok_bind; [apply ev_ok_denote_call_args | intros uvs].
      eapply ev_ok_bind; [apply ev_ok_denote_operand_bundles | intros _].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros fv].
      eapply ev_ok_bind; [unfold call; apply ev_ok_cfg_subevent; reflexivity | intros rv].
      eapply ev_ok_bind; [apply ev_ok_check_call_return | intros [exn | retv]].
      + eapply ev_ok_bind;
          [unfold stack_raise; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
      + eapply ev_ok_bind;
          [destruct iid as [id |];
             [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_ret]
          | intros _; apply ev_ok_ret].
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_denote_block
    (b : block dtyp) (bid_from : block_id)
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_block (@ParamsV IP IPT) b bid_from va).
  Proof using.
    unfold denote_block.
    eapply ev_ok_bind; [apply ev_ok_denote_phis | intros _].
    eapply ev_ok_bind; [apply ev_ok_denote_code | intros _].
    apply ev_ok_denote_terminator.
  Qed.

  Lemma ev_ok_denote_ocfg_map
    (bmap : rmap (block dtyp)) (va : option (@ptr ProvenanceV (@PointerV IP)))
    (ids : block_id * block_id) :
    ev_ok (@is_non_global_cfg_ev) (@denote_ocfg_map (@ParamsV IP IPT) bmap va ids).
  Proof using.
    unfold denote_ocfg_map; apply ev_ok_iter.
    intros [bid_from bid_src].
    destruct (RM.find bid_src bmap) as [block_src |]; [| apply ev_ok_ret].
    eapply ev_ok_bind; [apply ev_ok_denote_block | intros [bid_target | dv]; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_cfg_map
    (bmap : rmap (block dtyp)) (f : CFG.cfg dtyp)
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_cfg_map (@ParamsV IP IPT) bmap f va).
  Proof using.
    unfold denote_cfg_map.
    eapply ev_ok_bind; [apply ev_ok_denote_ocfg_map | intros [bid | uv];
      [apply ev_ok_cfg_raise | apply ev_ok_ret]].
  Qed.

  Lemma ev_ok_push_call_frame
    (df : definition dtyp (CFG.cfg dtyp)) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@push_call_frame (@ParamsV IP IPT) df args).
  Proof using.
    unfold push_call_frame.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros [bs vs]].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros dts].
    eapply ev_ok_bind; [unfold mem_push; apply ev_ok_cfg_subevent; reflexivity | intros _].
    eapply ev_ok_bind; [unfold stack_push; apply ev_ok_cfg_subevent; reflexivity | intros _].
    eapply ev_ok_bind; [unfold alloca; apply ev_ok_cfg_subevent; reflexivity | intros varargs].
    eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros _].
    destruct varargs as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [varg | ? ? | ? | ? | ? | ? ? | |];
      try apply ev_ok_cfg_raise; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_pop_call_frame :
    ev_ok (@is_non_global_cfg_ev) (@pop_call_frame (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _).
  Proof using.
    unfold pop_call_frame.
    eapply ev_ok_bind;
      [unfold stack_pop; apply ev_ok_cfg_subevent; reflexivity
      | intros _; unfold mem_pop; apply ev_ok_cfg_subevent; reflexivity].
  Qed.

  Lemma ev_ok_denote_function
    (df : definition dtyp (CFG.cfg dtyp))
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_function (@ParamsV IP IPT) df cc args).
  Proof using.
    unfold denote_function.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros _].
    eapply ev_ok_bind; [apply ev_ok_apply_args_attrs | intros args'].
    eapply ev_ok_bind; [apply ev_ok_push_call_frame | intros varg].
    eapply ev_ok_bind; [apply ev_ok_run_exc, ev_ok_denote_cfg_map | intros rv].
    eapply ev_ok_bind; [apply ev_ok_pop_call_frame | intros _].
    apply ev_ok_check_call_return.
  Qed.

  Lemma ev_ok_i8_str_index
    (strptr : @ptr ProvenanceV (@PointerV IP)) (idx : Z) :
    ev_ok (@is_non_global_cfg_ev)
      (@i8_str_index (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ strptr idx).
  Proof using.
    unfold i8_str_index.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros i].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros addr].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros d_byte].
    destruct d_byte as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [? | sz b | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raise.
    destruct sz as [p | p |]; try apply ev_ok_cfg_raise;
      destruct p as [p | p |]; try apply ev_ok_cfg_raise;
      destruct p as [p | p |]; try apply ev_ok_cfg_raise;
      destruct p as [p | p |]; try apply ev_ok_cfg_raise.
    apply ev_ok_ret.
  Qed.

  Lemma ev_ok_putchar_denotation
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@putchar_denotation (@ParamsV IP IPT) cc args).
  Proof using.
    unfold putchar_denotation.
    destruct args as [| ch [| ? ?]]; try apply ev_ok_cfg_raise.
    apply ev_ok_fmap.
    destruct ch as [db | |]; [| apply ev_ok_cfg_raiseUB | apply ev_ok_cfg_raiseUB].
    destruct db as [? | sz x32 | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raiseUB.
    destruct (Pos.eq_dec 32 sz) as [<- | _]; [| apply ev_ok_cfg_raiseUB].
    eapply ev_ok_bind;
      [unfold io_stdout; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_puts_denotation
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@puts_denotation (@ParamsV IP IPT) cc args).
  Proof using.
    unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]]; try apply ev_ok_cfg_raise.
    apply ev_ok_fmap.
    destruct u_strptr as [db | |]; [| apply ev_ok_cfg_raiseUB | apply ev_ok_cfg_raiseUB].
    destruct db as [strptr | ? ? | ? | ? | ? | ? ? | |]; try apply ev_ok_cfg_raiseUB.
    eapply ev_ok_bind; [apply ev_ok_i8_str_index | intros ch].
    eapply ev_ok_bind.
    - apply ev_ok_iter.
      intros [[c bytes] offset].
      destruct (@Integers.eq 8 c (@Integers.zero 8)); [apply ev_ok_ret |].
      eapply ev_ok_bind; [apply ev_ok_i8_str_index | intros _; apply ev_ok_ret].
    - intros bytes; eapply ev_ok_bind;
        [unfold io_stdout; apply ev_ok_cfg_subevent; reflexivity | intros _; apply ev_ok_ret].
  Qed.

  Lemma library_functions_ev_ok (decls : list (declaration dtyp)) :
    Forall
      (fun lib =>
         forall cc args,
           ev_ok (@is_non_global_cfg_ev) (snd lib cc args))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    unfold library_functions, _LIBRARIES; cbn [List.filter].
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      repeat constructor; intros cc args; cbn [snd];
      first [apply ev_ok_puts_denotation | apply ev_ok_putchar_denotation].
  Qed.

  Lemma ev_ok_external_call_inr
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev)
      (@Functor.fmap (@CFGtop (@ParamsV IP IPT)) _ _ (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
         inr (external_call dt fv vs)).
  Proof using.
    apply ev_ok_fmap; unfold external_call; apply ev_ok_cfg_subevent; reflexivity.
  Qed.

  Definition leaf_ctx_fn_rel
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (f1 f2 : @function_denotation (@ParamsV IP IPT)) : Prop :=
    (f1 = f2 /\ forall cc args, ev_ok (@is_non_global_cfg_ev) (f1 cc args)) \/
    (forall ctx1 ctx2 cc args U σ1 σ2 ls,
       incl P0 U ->
       mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
       refine_prov (mcfg_eq_g_post g0 U) U
         (interp_cfg_model ctx1 (f1 cc args) (σ1, (ls, g0)))
         (interp_cfg_model ctx2 (f2 cc args) (σ2, (ls, g0)))).

  Section LeafKnotG.
    Context (P0 : list N)
            (g0 : @global_env (@ParamsV IP IPT))
            (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
            (Hctx : forall k, option_rel (leaf_ctx_fn_rel P0 g0) (lookup k ctx1) (lookup k ctx2)).

    Local Definition k_lg {X R : Type}
      (tau_flag : bool)
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) =>
        if tau_flag then Tau (interp_cfg_model ctx (k x) s')
        else interp_cfg_model ctx (k x) s'.

    Local Inductive lg_rel {R : Type} (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | LG_Tree U (t0 : @CFGtop (@ParamsV IP IPT) R) (s_a s_b : state) ls0
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_cfg_model ctx1 t0 (s_a, (ls0, g0)) ≅ a1 ->
        interp_cfg_model ctx2 t0 (s_b, (ls0, g0)) ≅ a2 ->
        ev_ok (@is_non_global_cfg_ev) t0 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b) ->
        lg_rel U0 U a1 a2
    | LG_Bind X (tau_flag : bool) U
        (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_lg tau_flag ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_lg tau_flag ctx2 k) ≅ a2 ->
        (forall x, ev_ok (@is_non_global_cfg_ev) (k x)) ->
        refine_prov (mcfg_eq_g_post g0 U0) U u1 u2 ->
        lg_rel U0 U a1 a2.

    Local Lemma lg_rel_obs_eq {R : Type} (U0 U : list N)
      (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      lg_rel U0 U a1 a2 ->
      lg_rel U0 U a1' a2'.
    Proof using.
      intros E1 E2 H.
      destruct H as [U t0 s_a s_b ls0 b1 b2 Eb1 Eb2 Ht0 Hinc Hm
                    | X tf U u1 u2 k b1 b2 Eb1 Eb2 Hk Hu].
      - eapply LG_Tree;
          [exact (transitivity Eb1 E1) | exact (transitivity Eb2 E2) | exact Ht0 | exact Hinc | exact Hm].
      - eapply LG_Bind;
          [exact (transitivity Eb1 E1) | exact (transitivity Eb2 E2) | exact Hk | exact Hu].
    Qed.

    Local Lemma lg_bind_true_step {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      (Hk : forall x, ev_ok (@is_non_global_cfg_ev) (k x))
      (Hu : refine_prov (mcfg_eq_g_post g0 U0) U u1 u2) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (ITree.bind u1 (k_lg true ctx1 k))
        (ITree.bind u2 (k_lg true ctx2 k)).
    Proof using.
      punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply LG_Tree; [reflexivity | reflexivity | exact (Hk x1) | exact Hinc | exact Hm].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_lg true ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_lg true ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_lg true ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_lg true ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Local Lemma lg_call_dispatch {X : Type} (ce : @CallE (@ParamsV IP IPT) X)
      (U0 U : list N) (s_a s_b : state) ls0
      (Hpu0 : incl P0 U0)
      (Hinc : incl U0 U)
      (Hm : mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) :
      (exists t_call : @CFGtop (@ParamsV IP IPT) X,
         mrec_ctx ctx1 X ce ≅ t_call /\
         mrec_ctx ctx2 X ce ≅ t_call /\
         ev_ok (@is_non_global_cfg_ev) t_call) \/
      refine_prov (mcfg_eq_g_post g0 U0) U
        (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (s_a, (ls0, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (s_b, (ls0, g0))).
    Proof using Hctx.
      destruct ce as [dt cc fv vs]; unfold mrec_ctx; cbn [Monads.bind Monad_itree].
      destruct fv as [db | |];
        [| right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
             [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]
        | right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
             [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]].
      destruct db as [addr | ? ? | ? | ? | ? | ? ? | |];
        try (right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
             [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]).
      - cbn [check_callee].
        destruct ((ptr_to_int addr =? ptr_to_int null)%Z).
        + right; cbn [EOU_to_itree].
          eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
          eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False);
            [apply refine_cfg_raiseUB_l | intros _ _ _ _ []].
        + cbn [EOU_to_itree lookup_defn].
          pose proof (Hctx (ptr_to_int addr)) as Hlk.
          destruct (lookup (ptr_to_int addr) ctx1) as [f1 |],
                   (lookup (ptr_to_int addr) ctx2) as [f2 |];
            inversion Hlk as [? ? [[<- Hf1] | Hf12] |]; subst.
          * left; exists (f1 cc vs);
              exact (conj (Eqit.bind_ret_l tt _) (conj (Eqit.bind_ret_l tt _) (Hf1 cc vs))).
          * right.
            eapply refine_prov_obs_eq;
              [symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l
              | symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l |].
            eapply refine_prov_weaken_incl;
              [apply (Hf12 ctx1 ctx2 cc vs U s_a s_b ls0 (incl_tran Hpu0 Hinc) Hm) |].
            intros U' [? ?] [? ?] _ (Hi & H1 & H2 & H3 & H4);
              exact (conj (incl_tran Hinc Hi) (conj H1 (conj H2 (conj H3 H4)))).
          * left; exists (inr <$> external_call dt (DVALUE_Base (DVALUE_Pointer addr)) vs);
              exact (conj (Eqit.bind_ret_l tt _) (conj (Eqit.bind_ret_l tt _) (ev_ok_external_call_inr dt _ vs))).
      - right; cbn [check_callee EOU_to_itree].
        eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
        eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False);
          [apply refine_cfg_raiseUB_l | intros _ _ _ _ []].
    Qed.

    Local Lemma lg_tree_step {R : Type} (U0 U : list N)
      (t0 : @CFGtop (@ParamsV IP IPT) R) (s_a s_b : state) ls0
      (Ht0 : ev_ok (@is_non_global_cfg_ev) t0)
      (Hpu0 : incl P0 U0)
      (Hinc : incl U0 U)
      (Hm : mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (interp_cfg_model ctx1 t0 (s_a, (ls0, g0)))
        (interp_cfg_model ctx2 t0 (s_b, (ls0, g0))).
    Proof using Hctx.
      punfold Ht0; destruct Ht0 as [rv t0' Hot | mt t0' Hot Hmt | X e k t0' Hot He Hk]; pclearbot.
      - assert (E1 : Ret ((s_a, (ls0, g0)), rv) ≅ interp_cfg_model ctx1 t0' (s_a, (ls0, g0)))
          by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_cfg_model_ret).
        assert (E2 : Ret ((s_b, (ls0, g0)), rv) ≅ interp_cfg_model ctx2 t0' (s_b, (ls0, g0)))
          by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_cfg_model_ret).
        eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact E1 | exact E2 |].
        apply RP_Step; cbn;
          exact (conj Hinc (conj Hm (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
      - assert (E1 : Tau (interp_cfg_model ctx1 mt (s_a, (ls0, g0))) ≅ interp_cfg_model ctx1 t0' (s_a, (ls0, g0)))
          by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_cfg_model_tau).
        assert (E2 : Tau (interp_cfg_model ctx2 mt (s_b, (ls0, g0))) ≅ interp_cfg_model ctx2 t0' (s_b, (ls0, g0)))
          by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_cfg_model_tau).
        eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact E1 | exact E2 |].
        apply RP_Step; cbn;
          eapply LG_Tree; [reflexivity | reflexivity | exact Hmt | exact Hinc | exact Hm].
      - destruct e as [ce | me].
        + assert (Ecall : forall ctx s,
                    Tau (interp_cfg_model ctx (ITree.bind (mrec_ctx ctx X ce) k) s) ≅
                    interp_cfg_model ctx t0' s).
          { intros ctx s; symmetry; rewrite (itree_eta t0'), Hot; unfold interp_cfg_model.
            rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
            cbn [_interp_mrec observe]; apply interp_mcfg_model_tau. }
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | apply Ecall | apply Ecall |].
          apply RP_Step; cbn.
          destruct (lg_call_dispatch ce U0 U s_a s_b ls0 Hpu0 Hinc Hm)
            as [(t_call & Ec1 & Ec2 & Ht_call) | Href_call].
          * eapply LG_Tree;
              [symmetry; apply interp_cfg_model_obs_eq; rewrite Ec1; reflexivity
              | symmetry; apply interp_cfg_model_obs_eq; rewrite Ec2; reflexivity
              | eapply ev_ok_bind; [exact Ht_call | exact Hk]
              | exact Hinc
              | exact Hm].
          * eapply LG_Bind with (tau_flag := false);
              [symmetry; apply interp_cfg_model_bind
              | symmetry; apply interp_cfg_model_bind
              | exact Hk
              | exact Href_call].
        + assert (Emcfg : forall ctx s,
                    ITree.bind (interp_mcfg_model (ITree.trigger me) s) (k_lg true ctx k) ≅
                    interp_cfg_model ctx t0' s).
          { intros ctx s; symmetry; rewrite (itree_eta t0'), Hot; unfold interp_cfg_model.
            rewrite (interp_mcfg_model_obs_eq _ _ s (unfold_interp_mrec (mrec_ctx ctx) _)).
            cbn [_interp_mrec observe].
            assert (Ev : Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (k x))) ≅
                         ITree.bind (ITree.trigger me) (fun x => Tau (interp_mrec (mrec_ctx ctx) (k x)))).
            { unfold ITree.trigger; rewrite Eqit.bind_vis; apply eqit_Vis; intros x; symmetry; apply Eqit.bind_ret_l. }
            rewrite (interp_mcfg_model_obs_eq _ _ s Ev), interp_mcfg_model_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; apply interp_mcfg_model_tau. }
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | apply Emcfg | apply Emcfg |].
          apply lg_bind_true_step; [exact Hk |].
          eapply refine_prov_weaken_incl;
            [apply (trigger_mcfg_non_global_g_sync me He g0 U s_a s_b ls0 Hm) |].
          intros U' [? ?] [? ?] _ (Hi & H1 & H2 & H3 & H4);
            exact (conj (incl_tran Hinc Hi) (conj H1 (conj H2 (conj H3 H4)))).
    Qed.

    Local Lemma lg_bind_false_step {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      (Hpu0 : incl P0 U0)
      (Hk : forall x, ev_ok (@is_non_global_cfg_ev) (k x))
      (Hu : refine_prov (mcfg_eq_g_post g0 U0) U u1 u2) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (ITree.bind u1 (k_lg false ctx1 k))
        (ITree.bind u2 (k_lg false ctx2 k)).
    Proof using Hctx.
      punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          assert (Eb1 : interp_cfg_model ctx1 (k x1) (s_a', (ls1', g0)) ≅ ITree.bind u1 (k_lg false ctx1 k))
            by (symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity).
          assert (Eb2 : interp_cfg_model ctx2 (k x1) (s_b', (ls1', g0)) ≅ ITree.bind u2 (k_lg false ctx2 k))
            by (symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity).
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_tree_step U0 U (k x1) s_a' s_b' ls1' (Hk x1) Hpu0 Hinc Hm).
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_lg false ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_lg false ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_lg false ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_lg false ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma cfg_leaf_g_sync {R : Type}
      (t : @CFGtop (@ParamsV IP IPT) R)
      (Hok : ev_ok (@is_non_global_cfg_ev) t)
      (U0 : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu0 : incl P0 U0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_g_post g0 U0) U0
        (interp_cfg_model ctx1 t (σ1, (ls, g0)))
        (interp_cfg_model ctx2 t (σ2, (ls, g0))).
    Proof using Hctx.
      assert (Hcore : forall U a1 a2,
                lg_rel U0 U a1 a2 ->
                refine_prov (mcfg_eq_g_post g0 U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := lg_rel U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b ls0 b1 b2 Eb1 Eb2 Ht0 Hinc Hm
                        | X [|] U u1 u2 k b1 b2 Eb1 Eb2 Hk Hu].
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_tree_step U0 U t0 s_a s_b ls0 Ht0 Hpu0 Hinc Hm).
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_bind_true_step U0 U u1 u2 k Hk Hu).
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_bind_false_step U0 U u1 u2 k Hpu0 Hk Hu). }
      apply Hcore.
      eapply LG_Tree; [reflexivity | reflexivity | exact Hok | apply incl_refl | exact Heq].
    Qed.

    Lemma mrec_knot_leaf_call_sim {X : Type} (ce : @CallE (@ParamsV IP IPT) X)
      (U0 : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu0 : incl P0 U0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_g_post g0 U0) U0
        (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, (ls, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, (ls, g0))).
    Proof using Hctx.
      destruct (lg_call_dispatch ce U0 U0 σ1 σ2 ls Hpu0 (incl_refl U0) Heq)
        as [(t_call & Ec1 & Ec2 & Ht_call) | Href_call].
      - eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_obs_eq, Ec1
          | symmetry; apply interp_cfg_model_obs_eq, Ec2 |].
        exact (cfg_leaf_g_sync t_call Ht_call U0 σ1 σ2 ls Hpu0 Heq).
      - exact Href_call.
    Qed.
  End LeafKnotG.

  Lemma m2r_collect_unique_allocas_intro
    (all_defs : list raw_id) (bks : ocfg dtyp)
    (bk : block dtyp) (q : local_id) (dt_q : dtyp)
    (anns_q : list (annotation dtyp)) (md_q : list (metadata dtyp)) :
    In bk bks ->
    In (IId q, INSTR_Alloca dt_q anns_q, md_q) (blk_code bk) ->
    m2r_count_id q all_defs = 1%nat ->
    In q (m2r_collect_unique_allocas all_defs bks).
  Proof using.
    intros Hbk Him Hcnt; unfold m2r_collect_unique_allocas.
    apply in_flat_map; exists bk; split; [exact Hbk |].
    apply in_flat_map; exists (IId q, INSTR_Alloca dt_q anns_q, md_q); split; [exact Him |].
    rewrite Hcnt; cbn; left; reflexivity.
  Qed.

  Lemma unique_def_code_split
    (fargs : list local_id) (bks : ocfg dtyp) (b_init : block dtyp)
    (pre_al : code dtyp) (p : local_id) (ins_p : instr dtyp)
    (md_p : list (metadata dtyp)) (post_al : code dtyp) :
    NoDup (List.map blk_id bks) ->
    In b_init bks ->
    blk_code b_init = pre_al ++ (IId p, ins_p, md_p) :: post_al ->
    m2r_count_id p (fargs ++ flat_map full_block_defs bks) = 1%nat ->
    ~ In p fargs /\
    ~ In p (List.map (fun '(x, _, _) => x) (blk_phis b_init)) /\
    ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre_al) /\
    ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) /\
    ~ In p (instr_id_defs (fst (fst (blk_term b_init)))) /\
    (forall bk, In bk bks -> blk_id bk <> blk_id b_init -> ~ In p (full_block_defs bk)).
  Proof using.
    intros Hnd_ids Hin_init Hsplit Hcnt.
    pose proof (m2r_nodup_map_inv blk_id bks Hnd_ids) as Hnd_bks.
    assert (Hge_init :
              (m2r_count_id p (full_block_defs b_init) <=
               m2r_count_id p (flat_map full_block_defs bks))%nat).
    { clear -Hin_init; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
      rewrite m2r_count_id_app; destruct Hin_init as [<- | Hin_init]; [lia | specialize (IH Hin_init); lia]. }
    rewrite m2r_count_id_app in Hcnt.
    assert (Hdefs_init :
              m2r_count_id p (List.map (fun '(x, _, _) => x) (blk_phis b_init)) = 0%nat /\
              m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre_al) = 0%nat /\
              m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) = 0%nat /\
              m2r_count_id p (instr_id_defs (fst (fst (blk_term b_init)))) = 0%nat /\
              m2r_count_id p fargs = 0%nat).
    { unfold full_block_defs in Hge_init.
      rewrite Hsplit, m2r_flat_map_app in Hge_init; cbn [flat_map instr_id_defs] in Hge_init.
      rewrite !m2r_count_id_app in Hge_init; cbn [m2r_count_id] in Hge_init.
      rewrite raw_id_eqb_refl in Hge_init; lia. }
    destruct Hdefs_init as (Hc_phi & Hc_pre & Hc_post & Hc_tm & Hc_fargs).
    rewrite m2r_count_id_zero in Hc_phi, Hc_pre, Hc_post, Hc_tm, Hc_fargs.
    refine (conj Hc_fargs (conj Hc_phi (conj Hc_pre (conj Hc_post (conj Hc_tm _))))).
    intros bk Hbk Hne_id Hdef_bk.
    assert (Hne_bk : bk <> b_init) by (intros ->; exact (Hne_id Logic.eq_refl)).
    assert (Hdef_init : In p (full_block_defs b_init)).
    { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
      rewrite Hsplit; apply in_flat_map; exists (IId p, ins_p, md_p);
        split; [apply in_app_iff; right; left; reflexivity | left; reflexivity]. }
    pose proof (m2r_count_id_in_two_elems full_block_defs bks bk b_init p
                  Hnd_bks Hbk Hin_init Hne_bk Hdef_bk Hdef_init).
    lia.
  Qed.

  Lemma refine_cfg_exc_gread_same_g
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (gid : raw_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' v1 v2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2))
      U
      (interp_cfg_exc ctx1 (gread gid) s1)
      (interp_cfg_exc ctx2 (gread gid) s2).
  Proof using.
    intros s1 s2; unfold gread, Subevent.trigger.
    apply refine_cfg_exc_trigger; [reflexivity | reflexivity |].
    eapply refine_prov_tau_expand;
      [change (ITree.trigger (subevent _ (GlobalRead gid)))
         with (@withCall (@ParamsV IP IPT) _ (ITree.trigger (subevent _ (GlobalRead gid))));
       apply tau_expand_cfg_withCall_trigger
      | change (ITree.trigger (subevent _ (GlobalRead gid)))
          with (@withCall (@ParamsV IP IPT) _ (ITree.trigger (subevent _ (GlobalRead gid))));
        apply tau_expand_cfg_withCall_trigger |].
    eapply refine_prov_weaken; [apply (refine_mcfg_gread_same_g gid U σ1 σ2 ls1 ls2 g) |].
    intros U' [s1' v1] [s2' v2] (-> & -> & -> & <- & _);
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma map_monad_indirectbr_addrs_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (f : function_id) (brs : list block_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' a1 a2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ a1 = a2))
      U
      (interp_cfg_exc ctx1
         (map_monad (fun b => ITree.bind (gread (blockaddress_id f b))
                                (fun ba => Ret (dvalue_ptr_address ba))) brs) s1)
      (interp_cfg_exc ctx2
         (map_monad (fun b => ITree.bind (gread (blockaddress_id f b))
                                (fun ba => Ret (dvalue_ptr_address ba))) brs) s2).
  Proof using.
    intros s1 s2; induction brs as [| b brs' IH];
      cbn [map_monad Monads.bind Monads.ret Monad_itree].
    - apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
    - eapply refine_cfg_exc_bind.
      + eapply refine_cfg_exc_bind; [apply refine_cfg_exc_gread_same_g |].
        intros U1 s1' ba1 s2' ba2 _ (-> & -> & -> & <-).
        apply refine_cfg_exc_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U1 s1' oz1 s2' oz2 _ (-> & -> & -> & <-).
        eapply refine_cfg_exc_bind; [exact IH |].
        intros U2 s1'' ozs1 s2'' ozs2 _ (-> & -> & -> & <-).
        apply refine_cfg_exc_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma denote_non_invoke_term_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (iid1 iid2 : instr_id) (tm : terminator dtyp) (md1 md2 : list (metadata dtyp))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hni : m2r_non_invoke_term tm = true)
    (Hvars : forall x,
               In x (full_term_uses tm) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2))
    (Hexc : forall ex,
              RExc U (σ1, ((sf1, fstk1), g)) (σ2, ((sf2, fstk2), g)) ex ex) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2 /\
            match r2 with
            | inl bid_target => In bid_target (m2r_term_succs tm)
            | inr _ => True
            end))
      U
      (interp_cfg_exc ctx1 (denote_terminator (iid1, tm, md1)) s1)
      (interp_cfg_exc ctx2 (denote_terminator (iid2, tm, md2)) s2).
  Proof using.
    intros s1 s2; cbn [denote_terminator].
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt e] default_br dests
                   | [t addr] brs fn | [t expr]
                   | [dt fnptrval] args to_label unwind_label anns obs |].
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' dv1 s2' dv2 _ (-> & -> & -> & <- & _).
      apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl I)))).
    - apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl I)))).
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
      destruct v1 as [db | |];
        [| apply refine_cfg_exc_raise_both | apply refine_cfg_exc_raise_both].
      destruct db as [? | sz x | ? | ? | ? | ? ? | |]; try apply refine_cfg_exc_raise_both.
      + destruct sz as [? | ? |];
          [apply refine_cfg_exc_raise_both | apply refine_cfg_exc_raise_both |].
        destruct (equ x one).
        * apply refine_cfg_exc_ret; cbn [m2r_term_succs];
            refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
            left; reflexivity.
        * apply refine_cfg_exc_ret; cbn [m2r_term_succs];
            refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
            right; left; reflexivity.
      + apply refine_cfg_exc_raiseUB_l.
    - apply refine_cfg_exc_ret; cbn [m2r_term_succs];
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
        left; reflexivity.
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' sel1 s2' sel2 _ (-> & -> & -> & <- & _).
      destruct (dvalue_is_poison sel1); [apply refine_cfg_exc_raiseUB_l |].
      set (sw_eou :=
             Monads.bind
               (map_monad
                  (fun '((TInt_Literal sz x), id) =>
                     Monads.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                       (fun s => Monads.ret (@DVALUE_Base (@ParamsV IP IPT) s, id)))
                  dests)
               (fun switches => select_switch sel1 default_br switches)).
      destruct sw_eou as [msg | msg | msg | bid] eqn:Esw; cbn [EOU_to_itree].
      + eapply refine_cfg_exc_bind with (RA := fun _ _ _ _ _ => False);
          [apply refine_cfg_exc_raise_both | intros _ _ _ _ _ _ []].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_bind | reflexivity |].
        eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False);
          [apply refine_cfg_exc_raiseOOM_l | intros _ _ _ _ []].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_bind | reflexivity |].
        eapply PassCommon.refine_prov_bind with (RPre := fun _ _ _ => False);
          [apply refine_cfg_exc_raiseUB_l | intros _ _ _ _ []].
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
          | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
        apply refine_cfg_exc_ret;
          refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _)))).
        unfold sw_eou in Esw.
        destruct (map_monad _ dests) as [? | ? | ? | switches] eqn:Emm;
          cbn [Monads.bind Monad_EOU] in Esw; try discriminate Esw.
        pose proof (switch_dests_map_snd dests switches Emm) as Hmap_eq.
        apply select_switch_in in Esw as [-> | Hin_sw]; cbn [m2r_term_succs].
        * left; reflexivity.
        * right; rewrite <- Hmap_eq; exact Hin_sw.
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & _).
      destruct (dvalue_is_poison a1); [apply refine_cfg_exc_raiseUB_l |].
      destruct fn as [f |]; [| apply refine_cfg_exc_raise_both].
      eapply refine_cfg_exc_bind; [apply map_monad_indirectbr_addrs_exc_sim |].
      intros U2 s1'' addrs1 s2'' addrs2 _ (-> & -> & -> & <-).
      destruct (dvalue_ptr_address a1) as [z |]; [| apply refine_cfg_exc_raise_both].
      destruct (indirectbr_target z (List.combine brs addrs1)) as [b |] eqn:Eib;
        [| apply refine_cfg_exc_raiseUB_l].
      apply refine_cfg_exc_ret;
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _)))).
      cbn [m2r_term_succs]; exact (indirectbr_target_In z brs addrs1 b Eib).
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' ex1 s2' ex2 _ (-> & -> & -> & <- & _).
      apply refine_cfg_exc_raiseLLVM_both, Hexc.
    - discriminate Hni.
    - apply refine_cfg_exc_raiseUB_l.
  Qed.

  Fixpoint write_phi_dvs
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) : @local_env (@ParamsV IP IPT) :=
    match dvs with
    | [] => env
    | (id, dv) :: rest => write_phi_dvs rest (Maps.add id dv env)
    end.

  Lemma write_phi_dvs_lookup_not_in
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) (x : local_id) :
    ~ In x (List.map fst dvs) ->
    Maps.lookup x (write_phi_dvs dvs env) = Maps.lookup x env.
  Proof using.
    revert env; induction dvs as [| [id dv] rest IH]; intros env Hnin; cbn [write_phi_dvs List.map fst] in *.
    - reflexivity.
    - rewrite IH by (intros H; apply Hnin; right; exact H).
      apply lookup_add_neq; intros ->; apply Hnin; left; reflexivity.
  Qed.

  Lemma write_phi_dvs_lookup_agree
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env1 env2 : @local_env (@ParamsV IP IPT)) (x : local_id) :
    Maps.lookup x env1 = Maps.lookup x env2 ->
    Maps.lookup x (write_phi_dvs dvs env1) = Maps.lookup x (write_phi_dvs dvs env2).
  Proof using.
    revert env1 env2; induction dvs as [| [id dv] rest IH]; intros env1 env2 Heq; cbn [write_phi_dvs].
    - exact Heq.
    - apply IH.
      destruct (raw_id_eqb_spec x id) as [-> | Hne].
      + rewrite !lookup_add_eq; reflexivity.
      + rewrite !lookup_add_neq by exact Hne; exact Heq.
  Qed.

  Lemma write_phi_dvs_safe_locals
    (P_safe : list N) (safe_sub : list local_id)
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) :
    (forall q, In q safe_sub -> ~ In q (List.map fst dvs)) ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (write_phi_dvs dvs env).
  Proof using.
    revert env; induction dvs as [| [id dv] rest IH]; intros env Hdisj Hsafe; cbn [write_phi_dvs].
    - exact Hsafe.
    - apply IH.
      + intros q Hq H; eapply Hdisj; [exact Hq | right; exact H].
      + apply safe_locals_env_add_other; [| exact Hsafe].
        intros Hid; eapply Hdisj; [exact Hid | left; reflexivity].
  Qed.

  Lemma tau_star_cfg_exc_write_phi_dvs
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_exc ctx
         (ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) dvs) (fun _ => Ret tt))
         (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (write_phi_dvs dvs (stack_vars sf)), fstk), g)), inr tt)).
  Proof using.
    revert sf; induction dvs as [| [id dv] rest IH]; intros sf;
      cbn [map_monad write_phi_dvs Monads.bind Monads.ret Monad_itree].
    - eapply tau_star_trans.
      + eapply TS_Eq;
          [rewrite (interp_cfg_exc_obs_eq ctx _ _ _ (Eqit.bind_ret_l _ _)),
                   interp_cfg_exc_ret; reflexivity
          | apply TS_Refl].
      + destruct sf as [sv se sl]; cbn; apply TS_Refl.
    - eapply tau_star_trans.
      + eapply TS_Eq;
          [rewrite (interp_cfg_exc_obs_eq ctx _ _ _ (Eqit.bind_bind _ _ _)),
                   interp_cfg_exc_bind; reflexivity
          | apply tau_star_bind, tau_star_cfg_exc_lwrite].
      + eapply tau_star_trans.
        * eapply TS_Eq; [rewrite Eqit.bind_ret_l; reflexivity |].
          eapply TS_Eq;
            [apply interp_cfg_exc_obs_eq;
             rewrite Eqit.bind_bind;
             eapply eq_itree_clo_bind with (UU := Logic.eq);
               [reflexivity | intros bs _ <-; apply Eqit.bind_ret_l]
            | apply IH].
        * destruct sf as [sv se sl]; cbn; apply TS_Refl.
  Qed.

  Lemma find_option_ann_num_elements_uses {T : Set}
    (anns : list (annotation T)) (t : T) (num_exp : exp T) :
    find_option ann_num_elements anns = Some (t, num_exp) ->
    forall x, In x (full_exp_uses num_exp) -> In x (flat_map full_ann_uses anns).
  Proof using.
    induction anns as [| a rest IH]; cbn [find_option flat_map]; [intros H; discriminate H |].
    destruct a; cbn [ann_num_elements full_ann_uses];
      try (intros H x Hx; apply in_app_iff; right; exact (IH H x Hx)).
    intros H x Hx; inversion H; subst; apply in_app_iff; left; exact Hx.
  Qed.

  Lemma map_monad_denote_phi_same_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (flat_map m2r_phi_entry_uses phis) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' dvs1 dvs2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ dvs1 = dvs2 /\
            List.map fst dvs2 = List.map (fun '(id, _, _) => id) phis))
      U
      (interp_cfg_exc ctx1 (map_monad (denote_phi bid_from) phis) s1)
      (interp_cfg_exc ctx2 (map_monad (denote_phi bid_from) phis) s2).
  Proof using.
    intros s1 s2; induction phis as [| [[id [fmf dt p_args]] md] rest IH];
      cbn [map_monad denote_phi Monads.bind Monads.ret Monad_itree List.map].
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
    - destruct (assoc bid_from p_args) as [op |] eqn:Eassoc.
      + destruct (m2r_assoc_in bid_from p_args op Eassoc) as [k0 Hin_op].
        eapply refine_cfg_exc_bind.
        * eapply refine_cfg_exc_bind.
          -- apply denote_exp_cfg_exc_sim.
             intros x Hx; apply Hvars.
             cbn [flat_map m2r_phi_entry_uses full_phi_uses].
             apply in_app_iff; left; apply in_app_iff; left.
             apply in_flat_map; exists (k0, op); split; [exact Hin_op | exact Hx].
          -- intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
             apply refine_cfg_exc_ret; repeat split; reflexivity.
        * intros U1 s1' p1 s2' p2 _ (-> & -> & -> & <- & ->).
          eapply refine_cfg_exc_bind.
          -- apply IH; intros x Hx; apply Hvars; cbn [flat_map]; apply in_app_iff; right; exact Hx.
          -- intros U2 s1'' dvs1 s2'' dvs2 _ (-> & -> & -> & <- & Hfst).
             apply refine_cfg_exc_ret; repeat split; [cbn; f_equal; exact Hfst].
      + eapply refine_cfg_exc_bind with (RA := fun _ _ _ _ _ => False);
          [apply refine_cfg_exc_raise_both | intros _ _ _ _ _ _ []].
  Qed.

  Lemma denote_phis_same_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (flat_map m2r_phi_entry_uses phis) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dvs,
              U' = U /\ r1 = tt /\ r2 = tt /\
              List.map fst dvs = List.map (fun '(id, _, _) => id) phis /\
              s1' = (σ1, ((upd_local_sf sf1 (write_phi_dvs dvs (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (write_phi_dvs dvs (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1 (denote_phis bid_from phis) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_phis bid_from phis) (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold denote_phis.
    eapply refine_cfg_exc_bind; [apply map_monad_denote_phi_same_exc_sim, Hvars |].
    intros U1 s1' dvs1 s2' dvs2 _ (-> & -> & -> & <- & Hfst).
    eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_write_phi_dvs |].
    eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_write_phi_dvs |].
    apply refine_prov_ret; exists dvs1; repeat split; try exact Hfst; reflexivity.
  Qed.

  Lemma stage1_alloca_lwrite_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (id0 : local_id) (dt_a : dtyp) (num : N) (align : option N)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists pr ptrs v σ1' σ2',
              ~ In pr U /\
              U' = pr :: U /\ r1 = tt /\ r2 = tt /\
              is_safe_ptr_dvalue (pr :: P_unprom) v /\
              stage1_mem_inv (pr :: U) (pr :: P_unprom) G σ1' σ2' /\
              (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
              Memory_stack_frame_stack (state_memory_stack σ2') =
                Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack σ2)) /\
              s1' = (σ1', ((upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2', ((upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1 (ITree.bind (alloca dt_a num align) (fun v => lwrite id0 v))
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (ITree.bind (alloca dt_a num align) (fun v => lwrite id0 v))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    eapply refine_cfg_exc_bind.
    - unfold alloca, Subevent.trigger; try unfold trigger_cast.
      apply refine_cfg_exc_memory_event.
      exact (stage1_alloca_unprom dt_a num align U P_unprom G σ1 σ2 Hinv).
    - intros U1 [σ1' rest1'] v1 [σ2' rest2'] v2 _
        ((<- & <-) & (pr & ptrs & Hnin & -> & <- & Hsafe_v & Hinv' & Hdisj & Hfs')).
      eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
      apply refine_prov_ret.
      exists pr, ptrs, v1, σ1', σ2'; repeat split; assumption.
  Qed.

  Lemma stage1_no_call_instr_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (TF : state -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c post_c : code dtyp)
    (safe_sub : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ im :: post_c)
    (Hsub : forall q,
              In q safe_sub ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hchk : check_other_instr_for_slot false safe_sub p im = true)
    (HTF_eq : forall s_a s_b,
                Memory_stack_frame_stack (state_memory_stack s_b) =
                  Memory_stack_frame_stack (state_memory_stack s_a) ->
                TF s_a -> TF s_b)
    (HTF_add : forall s_a s_b ptrs,
                 (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                 Memory_stack_frame_stack (state_memory_stack s_b) =
                   Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                 TF s_a -> TF s_b)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (HTF : TF σ2)
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
    (Huse_vars : forall x,
                   In x (m2r_code_entry_uses im) ->
                   Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' G σ1' σ2' /\
              TF σ2' /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
              ((sf1' = sf1 /\ sf2' = sf2) \/
               (exists id0 v,
                  fst (fst im) = IId id0 /\
                  sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                  sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
      U
      (interp_cfg_exc ctx1 (denote_instr im va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_instr im va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (check_other_instr_for_slot_inv false safe_sub p im Hchk)
      as (_ & Hsafe_im & Hnocall).
    destruct im as [[iid ins] md].
    destruct iid as [id0 | vid0], ins; cbn [m2r_safe_mem_instr_any] in Hsafe_im;
      try discriminate Hsafe_im.
    - (* IId id0, INSTR_Op op *)
      assert (Hnid_safe : ~ In id0 safe_sub).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Op op) md post_c Hbk Hsplit) as (? & ? & Hbad);
          discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses];
          apply in_app_iff; left; exact Hx.
      + intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (bind_unit_ret_r _))
          | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r _)) |].
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists P_unprom, σ1, σ2,
               (upd_local_sf sf1 (Maps.add id0 uv1 (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 uv1 (stack_vars sf2))).
        refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv (conj HTF (conj Hgenv (conj _ _)))))))))).
        * apply safe_locals_env_add_other; [exact Hnid_safe | exact Hsafe_loc].
        * right; exists id0, uv1; repeat split; reflexivity.
    - (* IId id0, INSTR_Call -> impossible since allow_calls = false *)
      exfalso; exact (Hnocall Logic.eq_refl (IId id0) fn args anns obs md Logic.eq_refl).
    - (* IId id0, INSTR_Alloca dt anns *)
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + destruct (find_option ann_num_elements annotations) as [[t num_exp] |] eqn:Enum.
        * eapply refine_cfg_exc_bind.
          -- apply denote_exp_cfg_exc_sim.
             intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses].
             apply in_app_iff; left.
             exact (find_option_ann_num_elements_uses annotations t num_exp Enum x Hx).
          -- intros U1 s1' n1 s2' n2 _ (-> & -> & -> & <- & _).
             destruct (dvalue_is_poison n1); [apply refine_cfg_exc_raiseUB_l |].
             eapply refine_cfg_exc_bind.
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros nb1 nb2 <-; repeat split; reflexivity.
             ++ intros U2 s1'' nb1 s2'' nb2 _ (-> & -> & -> & <-).
                exact (stage1_alloca_lwrite_exc_sim ctx1 ctx2 RExc id0 dt
                         (Z.to_N (dvalue_base_int_unsigned nb1))
                         (explicit_alignment annotations)
                         U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g Hinv).
        * exact (stage1_alloca_lwrite_exc_sim ctx1 ctx2 RExc id0 dt 1%N
                   (explicit_alignment annotations)
                   U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g Hinv).
      + intros U1 s1' _ s2' _ _
          (pr & ptrs & v & σ1' & σ2' & Hnin & -> & _ & _ & Hsafe_v & Hinv' & Hdisj & Hfs' & -> & ->).
        apply refine_cfg_exc_ret.
        assert (HincP : incl P_unprom (pr :: P_unprom)) by (intros x Hx; right; exact Hx).
        exists (pr :: P_unprom), σ1', σ2',
               (upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))).
        refine (conj (fun x Hx => or_intror Hx) (conj HincP
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv' (conj (HTF_add σ2 σ2' ptrs Hdisj Hfs' HTF)
                        (conj (genv_safe_incl P_unprom (pr :: P_unprom) g HincP Hgenv)
                          (conj _ _)))))))))).
        * apply safe_locals_env_add_safe; [exact Hsafe_v |].
          exact (safe_locals_env_incl P_unprom (pr :: P_unprom) safe_sub (stack_vars sf2) HincP Hsafe_loc).
        * right; exists id0, v; repeat split; reflexivity.
    - (* IId id0, INSTR_Load t ptr anns *)
      destruct ptr as [du_l ptr_e].
      assert (Hnid_safe : ~ In id0 safe_sub).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Load t (du_l, ptr_e) anns) md post_c Hbk Hsplit)
          as (? & ? & Hbad); discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & Hptr_safe).
        pose proof (Hptr_safe P_unprom safe_sub Hgenv Hsafe_loc Hsafe_im) as Ha_safe.
        eapply refine_cfg_exc_bind.
        * eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
          intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
        * intros U2 s1'' _ s2'' _ _ (-> & -> & ->).
          eapply refine_cfg_exc_bind.
          -- unfold load, Subevent.trigger; try unfold trigger_cast.
             apply refine_cfg_exc_memory_event.
             exact (stage1_load_unprom t a1 U P_unprom G σ1 σ2 Hinv Ha_safe).
          -- intros U3 [σ1_l r1_l] v1 [σ2_l r2_l] v2 _ ((<- & <-) & (-> & -> & -> & <-)).
             eapply refine_cfg_exc_bind.
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros w1 w2 <-; repeat split; reflexivity.
             ++ intros U4 s1_a w1 s2_a w2 _ (-> & -> & -> & <-).
                eapply refine_cfg_exc_bind.
                ** exact (assert_load_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc md w1 _ _
                            U P_unprom G σ1 σ2 ((sf1, fstk1), g) ((sf2, fstk2), g) Hinv).
                ** intros U5 s1_d _ s2_d _ _ (-> & -> & -> & _ & _).
                   eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
                   eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
                   apply refine_prov_ret.
                   exists P_unprom, σ1, σ2,
                          (upd_local_sf sf1 (Maps.add id0 w1 (stack_vars sf1))),
                          (upd_local_sf sf2 (Maps.add id0 w1 (stack_vars sf2))).
                   refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Logic.eq_refl (conj Logic.eq_refl
                                 (conj Hinv (conj HTF (conj Hgenv (conj _ _)))))))))).
                   --- apply safe_locals_env_add_other; [exact Hnid_safe | exact Hsafe_loc].
                   --- right; exists id0, w1; repeat split; reflexivity.
    - (* IId id0, INSTR_Fence *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
    - (* IVoid vid0, INSTR_Comment *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
    - (* IVoid vid0, INSTR_Call -> impossible since allow_calls = false *)
      exfalso; exact (Hnocall Logic.eq_refl (IVoid vid0) fn args anns obs md Logic.eq_refl).
    - (* IVoid vid0, INSTR_Store val ptr anns *)
      destruct val as [dt_s val_e], ptr as [du_s ptr_e].
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
        eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
            apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hx.
        * intros U2 s1'' a1 s2'' a2 _ (-> & -> & -> & <- & Hptr_safe).
          pose proof (Hptr_safe P_unprom safe_sub Hgenv Hsafe_loc Hsafe_im) as Ha_safe.
          eapply refine_cfg_exc_bind.
          -- eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
             intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U3 s1_a _ s2_a _ _ (-> & -> & ->).
             assert (Hdo_store :
                       forall a_st : @dvalue (@ParamsV IP IPT),
                         is_safe_ptr_dvalue P_unprom a_st ->
                         refine_prov
                           (exc_post RExc
                              (fun U' s1' s2' r1 r2 =>
                                 exists P_unprom' σ1' σ2' sf1' sf2',
                                   incl U U' /\
                                   incl P_unprom P_unprom' /\
                                   r1 = tt /\ r2 = tt /\
                                   s1' = (σ1', ((sf1', fstk1), g)) /\
                                   s2' = (σ2', ((sf2', fstk2), g)) /\
                                   stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                                   TF σ2' /\
                                   genv_safe P_unprom' g /\
                                   safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                                   ((sf1' = sf1 /\ sf2' = sf2) \/
                                    (exists id0 v,
                                       IVoid vid0 = IId id0 /\
                                       sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                                       sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
                           U
                           (interp_cfg_exc ctx1 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ1, ((sf1, fstk1), g)))
                           (interp_cfg_exc ctx2 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ2, ((sf2, fstk2), g)))).
             { intros a_st Ha_st.
               eapply refine_cfg_exc_bind.
               - unfold store, Subevent.trigger; try unfold trigger_cast.
                 apply refine_cfg_exc_memory_event.
                 exact (stage1_store_unprom dt_s a_st v1 U P_unprom G σ1 σ2 Hinv Ha_st).
               - intros U4 [σ1' rest1'] _ [σ2' rest2'] _ _
                   ((<- & <-) & (-> & _ & _ & Hinv' & Hfs')).
                 apply refine_cfg_exc_ret.
                 exists P_unprom, σ1', σ2', sf1, sf2.
                 refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                           (conj Logic.eq_refl (conj Logic.eq_refl
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Hinv' (conj (HTF_eq σ2 σ2' Hfs' HTF)
                                 (conj Hgenv (conj Hsafe_loc _)))))))))).
                 left; split; reflexivity. }
             destruct a1 as [[? | ? ? | ? | ? | ? | ? ? | |] | |];
               try (apply Hdo_store, Ha_safe).
             eapply refine_prov_obs_eq;
               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
             apply refine_cfg_exc_raiseUB_l.
    - (* IVoid vid0, INSTR_Fence *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
  Qed.

  Lemma stage1_no_call_code_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (TF : state -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_sub : list local_id) (p : local_id)
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_sub ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hchk : forallb (check_other_instr_for_slot false safe_sub p) cd = true)
    (HTF_eq : forall s_a s_b,
                Memory_stack_frame_stack (state_memory_stack s_b) =
                  Memory_stack_frame_stack (state_memory_stack s_a) ->
                TF s_a -> TF s_b)
    (HTF_add : forall s_a s_b ptrs,
                 (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                 Memory_stack_frame_stack (state_memory_stack s_b) =
                   Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                 TF s_a -> TF s_b)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (HTF : TF σ2)
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' G σ1' σ2' /\
              TF σ2' /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2')) /\
              (forall x,
                 ~ In x (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) ->
                 Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf1) /\
                 Maps.lookup x (stack_vars sf2') = Maps.lookup x (stack_vars sf2)) /\
              (sf1 = sf2 -> sf1' = sf2')))
      U
      (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_code cd va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    revert pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk Hinv HTF Hgenv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk Hinv HTF Hgenv Hsafe_loc Hvars;
      unfold denote_code; cbn [loop_monad forallb flat_map].
    - apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc
                      (conj Hvars (conj (fun _ _ => conj Logic.eq_refl Logic.eq_refl)
                                        (fun Heq => Heq))))))))))))).
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Huse_im : forall x,
                In x (m2r_code_entry_uses im) ->
                Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
      { intros x Hx; apply Hvars; intros ->.
        exact (proj1 (check_other_instr_for_slot_inv false safe_sub p im Hchk_im) Hx). }
      eapply refine_cfg_exc_bind.
      + exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc TF fargs bks bk pre_c (rest ++ post_c)
                 safe_sub p im va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                 Hnd_bks Hbk Hsplit Hsub Hchk_im HTF_eq HTF_add Hinv HTF Hgenv Hsafe_loc Huse_im).
      + intros U1 s1_m _ s2_m _ _
          (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
           HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & HTF1 & Hgenv1 & Hsafe1 & Hsf_step).
        assert (Hvars1 : forall x, x <> p -> Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m)).
        { intros x Hne.
          destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)].
          - exact (Hvars x Hne).
          - cbn [stack_vars upd_local_sf].
            destruct (raw_id_eqb_spec x id0) as [-> | Hne_id].
            + rewrite !lookup_add_eq; reflexivity.
            + rewrite !lookup_add_neq by exact Hne_id; exact (Hvars x Hne). }
        assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c).
        { rewrite <- app_assoc; exact Hsplit. }
        eapply refine_prov_weaken.
        * exact (IH (pre_c ++ [im]) U1 P1 σ1_m σ2_m sf1_m sf2_m
                   Hsplit_rest Hchk_rest Hinv1 HTF1 Hgenv1 Hsafe1 Hvars1).
        * intros U2 [s1_f res1] [s2_f res2].
          destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
            try (intros H; exact H).
          intros (P2 & σ1_f & σ2_f & sf1_f & sf2_f &
                  HincU2 & HincP2 & -> & -> & -> & -> & Hinv2 & HTF2 & Hgenv2 & Hsafe2 &
                  Hvars2 & Hpres2 & Heq2).
          exists P2, σ1_f, σ2_f, sf1_f, sf2_f.
          refine (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Logic.eq_refl (conj Logic.eq_refl
                        (conj Hinv2 (conj HTF2 (conj Hgenv2 (conj Hsafe2
                          (conj Hvars2 (conj _ _)))))))))))).
          -- intros x Hnin_all.
             destruct im as [[iid_im ins_im] md_im]; cbn [fst] in Hsf_step.
             assert (Hnin_im : ~ In x (instr_id_defs iid_im))
               by (intros Hx; apply Hnin_all, in_app_iff; left; exact Hx).
             assert (Hnin_rest : ~ In x (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest))
               by (intros Hx; apply Hnin_all, in_app_iff; right; exact Hx).
             destruct (Hpres2 x Hnin_rest) as [Hp1 Hp2]; rewrite Hp1, Hp2.
             destruct Hsf_step as [[-> ->] | (id0 & v & Heq_iid & -> & ->)];
               [split; reflexivity |].
             subst iid_im; cbn [instr_id_defs] in Hnin_im.
             assert (Hne_id : x <> id0) by (intros ->; apply Hnin_im; left; reflexivity).
             cbn [stack_vars upd_local_sf]; rewrite !lookup_add_neq by exact Hne_id;
               split; reflexivity.
          -- intros Heq_sf; apply Heq2.
             destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)]; [exact Heq_sf |].
             subst sf2; reflexivity.
  Qed.

  Lemma denote_phis_nil_eq (bid : block_id) :
    @denote_phis (@ParamsV IP IPT) bid [] ≅ Ret tt.
  Proof using.
    unfold denote_phis; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    rewrite !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma interp_cfg_exc_unfold_iter {I R : Type}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (body : I -> @CFGtop (@ParamsV IP IPT) (I + R))
    (i : I) (s : FusedS) :
    interp_cfg_exc ctx (ITree.iter body i) s ≅
    ITree.bind (interp_cfg_exc ctx (body i) s)
      (fun '(s', res) =>
         match res with
         | inl x => Ret (s', inl x)
         | inr (inl j) => Tau (interp_cfg_exc ctx (ITree.iter body j) s')
         | inr (inr r) => Ret (s', inr r)
         end).
  Proof using.
    rewrite (interp_cfg_exc_obs_eq ctx _ _ s (unfold_iter body i)).
    rewrite interp_cfg_exc_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' [x | [j | r]]] _ <-.
    - reflexivity.
    - apply interp_cfg_exc_tau.
    - apply interp_cfg_exc_ret.
  Qed.

  Lemma stage2_alloca_dead_instr_exc_l {IPWB : IPtrWellBehaved IP}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (p : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (σ1 σ2 : state)
    (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns : is_only_align_anns anns_al = true)
    (Hpu : incl P_safe U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2))
    (Hfs2 : Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists pr pt σ1',
              ~ In pr U /\
              U' = pr :: U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((upd_local_sf sf (Maps.add p (DVALUE_Base (DVALUE_Pointer pt)) (stack_vars sf)),
                            fstk), g)) /\
              s2' = (σ2, ((sf, fstk), g)) /\
              stage2_mem_inv (pr :: U) P_safe fs0 f2 (ptr_to_int pt) pr
                (N.to_nat (@store_size_dtyp SizeofV dt)) σ1' σ2))
      U
      (interp_cfg_exc ctx1 (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va)
         (σ1, ((sf, fstk), g)))
      (interp_cfg_exc ctx2 (Ret tt) (σ2, ((sf, fstk), g))).
  Proof using.
    destruct (is_only_align_anns_num_elts anns_al Hanns) as [Hnum _].
    cbn [denote_instr]; rewrite Hnum.
    assert (Eal :
              ITree.bind
                (ITree.bind (alloca dt 1%N (explicit_alignment anns_al)) (fun v => lwrite p v))
                (fun _ => Ret tt) ≅
              ITree.bind (alloca dt 1%N (explicit_alignment anns_al)) (fun v => lwrite p v)).
    { rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros v _ <-; apply bind_unit_ret_r. }
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_cfg_exc_obs_eq ctx1 _ _ _ Eal); apply interp_cfg_exc_bind
      | symmetry; rewrite interp_cfg_exc_ret; apply Eqit.bind_ret_r |].
    unfold alloca, Subevent.trigger; try unfold trigger_cast.
    eapply PassCommon.refine_prov_bind.
    - apply refine_cfg_exc_memory_event_l.
      exact (stage2_alloca_dead_l
               ((σ2, ((sf, fstk), g)), inr tt)
               dt (explicit_alignment anns_al) U P_safe fs0 f2 σ1 σ2 Hsc Hpu Heq Hfs2).
    - intros U1 [s1_a res_a] y2 _
        (pr & pt & Hnin & -> & -> & -> & Hinv').
      eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
      apply refine_prov_ret.
      destruct s1_a as [σ1' _]; exists pr, pt, σ1'; repeat split; assumption.
  Qed.

  Lemma stage2_instr_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ im :: post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hnin_p_use : ~ In p (m2r_code_entry_uses im))
    (Hchk : check_no_alloca_or_call_instr safe_no_p im = true)
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2)
    (Hgenv : genv_safe P_safe g)
    (Hsafe_loc : safe_locals_env P_safe safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists σ1' σ2' sf1' sf2',
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk), g)) /\
              s2' = (σ2', ((sf2', fstk), g)) /\
              stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
              safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_instr im va) (σ1, ((sf1, fstk), g)))
      (interp_cfg_exc ctx2 (denote_instr im va) (σ2, ((sf2, fstk), g))).
  Proof using.
    assert (Huse_vars : forall x,
              In x (m2r_code_entry_uses im) ->
              Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
    { intros x Hx; apply Hvars; intros ->; exact (Hnin_p_use Hx). }
    destruct (check_no_alloca_or_call_instr_inv safe_no_p im Hchk)
      as [(id0 & op & md & ->)
         | [(id0 & dt_l & du_l & ptr_e & anns_l & md & -> & Hsafe_ptr & Hderef_none)
         | [(vid0 & dt_s & val_e & du_s & ptr_e & anns_s & md & -> & Hsafe_ptr)
         | [(vid0 & msg_c & md & ->)
         | (iid0 & sync & ord & md & ->)]]]].
    - assert (Hnid_safe : ~ In id0 safe_no_p).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Op op) md post_c Hbk Hsplit) as (? & ? & Hbad);
          discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses];
          apply in_app_iff; left; exact Hx.
      + intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (bind_unit_ret_r _))
          | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r _)) |].
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists σ1, σ2,
               (upd_local_sf sf1 (Maps.add id0 uv1 (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 uv1 (stack_vars sf2))).
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj (safe_locals_env_add_other P_safe safe_no_p id0 uv1 _ Hnid_safe Hsafe_loc) _))))))).
        intros x Hne; cbn [stack_vars upd_local_sf].
        destruct (raw_id_eqb_spec x id0) as [-> | Hne_id];
          [rewrite !lookup_add_eq; reflexivity | rewrite !lookup_add_neq by exact Hne_id; exact (Hvars x Hne)].
    - assert (Hnid_safe : ~ In id0 safe_no_p).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Load dt_l (du_l, ptr_e) anns_l) md post_c Hbk Hsplit)
          as (? & ? & Hbad); discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & Hptr_safe).
        pose proof (Hptr_safe P_safe safe_no_p Hgenv Hsafe_loc Hsafe_ptr) as Ha_safe.
        eapply refine_cfg_exc_bind.
        * eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
          intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
        * intros U2 s1'' _ s2'' _ _ (-> & -> & ->).
          eapply refine_cfg_exc_bind.
          -- unfold load, Subevent.trigger; try unfold trigger_cast.
             apply refine_cfg_exc_memory_event.
             exact (stage2_load_safe dt_l a1 U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Ha_safe).
          -- intros U3 [σ1_l r1_l] v1 [σ2_l r2_l] v2 _ ((<- & <-) & (-> & -> & -> & <-)).
             eapply refine_cfg_exc_bind.
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros w1 w2 <-; repeat split; reflexivity.
             ++ intros U4 s1_a w1 s2_a w2 _ (-> & -> & -> & <-).
                unfold assert_load_dereferenceable; rewrite Hderef_none.
                eapply refine_prov_obs_eq;
                  [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_ret_l _ _))
                  | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_ret_l _ _)) |].
                eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
                eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
                apply refine_prov_ret.
                exists σ1, σ2,
                       (upd_local_sf sf1 (Maps.add id0 w1 (stack_vars sf1))),
                       (upd_local_sf sf2 (Maps.add id0 w1 (stack_vars sf2))).
                refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Logic.eq_refl (conj Logic.eq_refl
                            (conj Hinv (conj (safe_locals_env_add_other P_safe safe_no_p id0 w1 _ Hnid_safe Hsafe_loc) _))))))).
                intros x Hne; cbn [stack_vars upd_local_sf].
                destruct (raw_id_eqb_spec x id0) as [-> | Hne_id];
                  [rewrite !lookup_add_eq; reflexivity
                  | rewrite !lookup_add_neq by exact Hne_id; exact (Hvars x Hne)].
    - cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
        eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
            apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hx.
        * intros U2 s1'' a1 s2'' a2 _ (-> & -> & -> & <- & Hptr_safe).
          pose proof (Hptr_safe P_safe safe_no_p Hgenv Hsafe_loc Hsafe_ptr) as Ha_safe.
          eapply refine_cfg_exc_bind.
          -- eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
             intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U3 s1_a _ s2_a _ _ (-> & -> & ->).
             assert (Hdo_store :
                       forall a_st : @dvalue (@ParamsV IP IPT),
                         is_safe_ptr_dvalue P_safe a_st ->
                         refine_prov
                           (exc_post RExc
                              (fun U' s1' s2' r1 r2 =>
                                 exists σ1' σ2' sf1' sf2',
                                   U' = U /\ r1 = tt /\ r2 = tt /\
                                   s1' = (σ1', ((sf1', fstk), g)) /\
                                   s2' = (σ2', ((sf2', fstk), g)) /\
                                   stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
                                   safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
                                   (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
                           U
                           (interp_cfg_exc ctx1 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ1, ((sf1, fstk), g)))
                           (interp_cfg_exc ctx2 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ2, ((sf2, fstk), g)))).
             { intros a_st Ha_st.
               eapply refine_cfg_exc_bind.
               - unfold store, Subevent.trigger; try unfold trigger_cast.
                 apply refine_cfg_exc_memory_event.
                 exact (stage2_store_safe dt_s a_st v1 U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Ha_st).
               - intros U4 [σ1' rest1'] _ [σ2' rest2'] _ _ ((<- & <-) & (-> & _ & _ & Hinv')).
                 apply refine_cfg_exc_ret.
                 exists σ1', σ2', sf1, sf2; repeat split; assumption. }
             destruct a1 as [[? | ? ? | ? | ? | ? | ? ? | |] | |];
               try (apply Hdo_store, Ha_safe).
             eapply refine_prov_obs_eq;
               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
             apply refine_cfg_exc_raiseUB_l.
    - cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists σ1, σ2, sf1, sf2; repeat split; assumption.
    - destruct iid0; cbn [denote_instr]; apply refine_cfg_exc_ret;
        exists σ1, σ2, sf1, sf2; repeat split; assumption.
  Qed.

  Lemma stage2_code_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id)
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hnin_p_blk : ~ In p (full_block_uses bk))
    (Hchk : forallb (check_no_alloca_or_call_instr safe_no_p) cd = true)
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2)
    (Hgenv : genv_safe P_safe g)
    (Hsafe_loc : safe_locals_env P_safe safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists σ1' σ2' sf1' sf2',
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk), g)) /\
              s2' = (σ2', ((sf2', fstk), g)) /\
              stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
              safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_code cd va) (σ1, ((sf1, fstk), g)))
      (interp_cfg_exc ctx2 (denote_code cd va) (σ2, ((sf2, fstk), g))).
  Proof using.
    revert pre_c σ1 σ2 sf1 sf2 Hsplit Hchk Hinv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c σ1 σ2 sf1 sf2 Hsplit Hchk Hinv Hsafe_loc Hvars;
      unfold denote_code; cbn [loop_monad forallb].
    - apply refine_cfg_exc_ret; exists σ1, σ2, sf1, sf2; repeat split; assumption.
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Hnin_p_im : ~ In p (m2r_code_entry_uses im)).
      { intros Hp; apply Hnin_p_blk; eapply m2r_code_entry_uses_in_block; [| exact Hp].
        rewrite Hsplit; apply in_app_iff; right; left; reflexivity. }
      eapply refine_cfg_exc_bind.
      + exact (stage2_instr_exc_sim ctx1 ctx2 RExc fargs bks bk pre_c (rest ++ post_c)
                 safe_no_p p im va U P_safe fs0 f2 base_dead pr_dead sz_dead
                 σ1 σ2 sf1 sf2 fstk g
                 Hnd_bks Hbk Hsplit Hsub Hnin_p_im Hchk_im Hinv Hgenv Hsafe_loc Hvars).
      + intros U1 s1_m _ s2_m _ _
          (σ1_m & σ2_m & sf1_m & sf2_m & -> & _ & _ & -> & -> & Hinv1 & Hsafe1 & Hvars1).
        assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
          by (rewrite <- app_assoc; exact Hsplit).
        exact (IH (pre_c ++ [im]) σ1_m σ2_m sf1_m sf2_m Hsplit_rest Hchk_rest Hinv1 Hsafe1 Hvars1).
  Qed.

  Lemma try_elim_dead_alloca_denote_function_sim {IPWB : IPtrWellBehaved IP}
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    genv_safe P0 g0 ->
    try_elim_dead_alloca_in_defn df = Some df' ->
    leaf_ctx_fn_rel P0 g0 (denote_function df) (denote_function df').
  Proof using.
    intros Hgenv0 Htry.
    unfold try_elim_dead_alloca_in_defn in Htry.
    set (fargs := df_args df) in *.
    set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff, negb_true_iff in Eg1.
    destruct Eg1 as [[Hnd_bks Hno_entry_pred] _].
    apply m2r_nodup_ids_spec in Hnd_bks.
    apply in_raw_ids_false in Hno_entry_pred.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind_init;
      [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Efind_init)
      as [Hin_init Hid_init].
    destruct (m2r_is_empty (blk_phis b_init)
              && m2r_non_invoke_term (snd (fst (blk_term b_init)))) eqn:Eg2;
      [| discriminate Htry].
    rewrite andb_true_iff in Eg2; destruct Eg2 as [Hphis_init Hni_init].
    apply m2r_is_empty_spec in Hphis_init.
    set (all_defs := fargs ++ flat_map full_block_defs (blks c)) in *.
    set (all_uses := flat_map full_block_uses (blks c)) in *.
    set (safe_locals := m2r_collect_unique_allocas all_defs (blks c)) in *.
    destruct (find_trailing_dead_alloca_in_code all_defs all_uses safe_locals [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
      [| discriminate Htry].
    pose proof (find_trailing_dead_alloca_in_code_inv
                  all_defs all_uses safe_locals [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind_al) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals) in *.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & Hanns_al & _) &
                         Hsc & Hcnt_p & Hp_nuse & Hpre_chk & Hpost_chk).
    apply in_raw_ids_false in Hp_nuse.
    destruct (forallb
                (fun bk =>
                   if raw_id_eqb (blk_id bk) (init c) then true
                   else
                     forallb (check_no_alloca_or_call_instr safe_no_p) (blk_code bk) &&
                     m2r_non_invoke_term (snd (fst (blk_term bk))))
                (blks c)) eqn:Ebks_chk; [| discriminate Htry].
    inversion Htry; subst df'; clear Htry.
    assert (Hsub_safe : forall q, In q safe_no_p -> In q safe_locals).
    { intros q Hq; apply filter_In in Hq as [Hq _]; exact Hq. }
    assert (Hp_blk_nuse : forall bk, In bk (blks c) -> ~ In p (full_block_uses bk)).
    { intros bk Hbk Hp; apply Hp_nuse, in_flat_map; exists bk; split; assumption. }
    set (f_blk := fun bk : block dtyp =>
                    if raw_id_eqb (blk_id bk) (init c) then
                      {| blk_id       := blk_id bk;
                         blk_phis     := blk_phis bk;
                         blk_code     := pre_al ++ post_al;
                         blk_term     := blk_term bk;
                         blk_comments := blk_comments bk |}
                    else bk).
    set (c' := {| init := init c; blks := List.map f_blk (blks c); args := args c |}).
    assert (Hf_id : forall bk, In bk (blks c) -> blk_id (f_blk bk) = blk_id bk).
    { intros bk _; unfold f_blk; destruct (raw_id_eqb (blk_id bk) (init c)); reflexivity. }
    right.
    intros ctx1 ctx2 cc args U0 σ1_in σ2_in [sf_caller fstk_caller] Hpu0 Heq_in.
    unfold denote_function; cbn [df_prototype df_args df_instrs].
    fold fargs c c'.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    set (fname := show_raw_id (dc_name (df_prototype df))).
    set (fcc := anns_cconv (dc_annotations (df_prototype df))).
    set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
    pose proof (stage1_equal_to_mem_inv U0 P0 σ1_in σ2_in Hpu0 Heq_in) as Hinv0.
    eapply refine_cfg_model_bind.
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
      eapply refine_cfg_model_bind.
      + exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                 ("Argument of " ++ fname ++ " violates noundef.")%string
                 args U0 P0 [] σ1_in σ2_in ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv0).
      + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
        eapply refine_cfg_model_bind.
        * exact (push_call_frame_stage1_sim ctx1 ctx2 df
                   {| df_prototype := df_prototype df; df_args := fargs; df_instrs := c' |}
                   args1 U0 P0 [] σ1_in σ2_in sf_caller sf_caller fstk_caller fstk_caller g0
                   Logic.eq_refl Hinv0).
        * intros U_pf s1_pf varg1 s2_pf varg2 _
            (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
          fold fs0 in Htf_pf.
          set (sf0 := {| stack_vars := init_local_env bs;
                         stack_exc  := None;
                         stack_loc  := Some ""%string |}).
          set (fstk := sf_caller :: fstk_caller).
          assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
            by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
          assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
            by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                args1 bs vs Ecomb Hsub_safe))).
          set (sz_dead := N.to_nat (@store_size_dtyp SizeofV dt)).
          set (RExc_s2 :=
                 fun U_e (s1_e s2_e : FusedS) (ex1 ex2 : @exc (@ParamsV IP IPT)) =>
                   ex1 = ex2 /\
                   incl (pr_va :: U0) U_e /\
                   exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                     s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                     s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                     stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
          set (RA_s2 :=
                 fun U_e (s1_e s2_e : FusedS) (v1 v2 : @dvalue (@ParamsV IP IPT)) =>
                   v1 = v2 /\
                   incl (pr_va :: U0) U_e /\
                   exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                     s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                     s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                     stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
          eapply refine_cfg_model_bind with (RA := exc_post RExc_s2 RA_s2).
          -- change (interp_cfg_model ctx1 (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                       (σ1_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx1 (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                       (σ1_pf, ((sf0, fstk), g0))).
             change (interp_cfg_model ctx2 (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                       (σ2_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx2 (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                       (σ2_pf, ((sf0, fstk), g0))).
             unfold denote_cfg_map; cbn [init].
             eapply refine_cfg_exc_bind with
               (RA := fun U_e s1_e s2_e
                        (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) =>
                        r1 = r2 /\
                        incl (pr_va :: U0) U_e /\
                        exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                          s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                          s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                          stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
             ++ unfold denote_ocfg_map.
                eapply refine_prov_obs_eq;
                  [symmetry; apply interp_cfg_exc_unfold_iter
                  | symmetry; apply interp_cfg_exc_unfold_iter |].
                rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
                rewrite ScopeTheory.ocfg_map_find_block; cbn [blks].
                rewrite (m2r_find_block_map_id_pres f_blk (blks c) (init c) Hf_id), Efind_init.
                cbn [option_map]; unfold f_blk at 1; rewrite Hid_init, raw_id_eqb_refl.
                unfold denote_block; cbn [blk_phis blk_code blk_term]; rewrite Hphis_init.
                eapply PassCommon.refine_prov_bind with
                  (RPre := exc_post RExc_s2
                             (fun U_s s1_s s2_s
                                (lr1 lr2 : (block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) =>
                                exists P_pre f2 base_dead pr_dead σ1_b1 σ2_b1 sf1_b1 sf2_b1,
                                  incl (pr_va :: U0) U_s /\
                                  lr1 = lr2 /\
                                  s1_s = (σ1_b1, ((sf1_b1, fstk), g0)) /\
                                  s2_s = (σ2_b1, ((sf2_b1, fstk), g0)) /\
                                  stage2_mem_inv U_s P_pre fs0 f2 base_dead pr_dead sz_dead σ1_b1 σ2_b1 /\
                                  genv_safe P_pre g0 /\
                                  safe_locals_env P_pre safe_no_p (stack_vars sf2_b1) /\
                                  (forall x, x <> p -> Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                                  match lr1 with
                                  | inl j => snd j <> init c
                                  | inr _ => True
                                  end)).
                ** eapply refine_prov_obs_eq;
                     [symmetry;
                      apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                               (eq_itree_clo_bind _ _ _ _ Logic.eq
                                  (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                     (fun _ _ <- => Logic.eq_refl))
                                  (fun _ _ <- => Logic.eq_refl)))
                     | symmetry;
                       apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                (eq_itree_clo_bind _ _ _ _ Logic.eq
                                   (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                      (fun _ _ <- => Logic.eq_refl))
                                   (fun _ _ <- => Logic.eq_refl))) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_ret_l _ _))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_ret_l _ _)) |].
                   rewrite Hsplit_init.
                   eapply refine_cfg_exc_bind.
                   --- eapply refine_prov_obs_eq;
                         [symmetry;
                          apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                   (eq_itree_clo_bind _ _ _ _ Logic.eq
                                      (denote_code_app_eq pre_al _ (Some varg1))
                                      (fun _ _ <- => Logic.eq_refl)))
                         | symmetry;
                           apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                    (eq_itree_clo_bind _ _ _ _ Logic.eq
                                       (denote_code_app_eq pre_al post_al (Some varg1))
                                       (fun _ _ <- => Logic.eq_refl))) |].
                       eapply refine_cfg_exc_bind.
                       +++ assert (Hsplit_pre :
                                     blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                             by exact Hsplit_init.
                           exact (stage1_no_call_code_exc_sim ctx1 ctx2 RExc_s2
                                    (fun s => top_frame_unprom_from fs0 [] (state_memory_stack s))
                                    fargs (blks c) b_init [] pre_al
                                    ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                                    safe_no_p p (Some varg1) (Some varg1)
                                    (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf sf0 sf0 fstk fstk g0
                                    Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
                                    (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs) HT)
                                    (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                                       top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs)
                                         (top_frame_unprom_add_ptrs fs0 [] ptrs _ HT Hdisj))
                                    Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
                       +++ intros U_pre s1_pre _ s2_pre _ _
                             (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
                              HincU_pre & HincP_pre & _ & _ & -> & -> &
                              Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & _ & Heq_sf_pre).
                           pose proof (Heq_sf_pre Logic.eq_refl) as ->.
                           destruct Htf_pre as (f2 & Hfs2_pre & _).
                           pose proof (proj1 Hinv_pre) as Hpu_pre.
                           pose proof (stage1_mem_nil_is_equal U_pre P_pre σ1_pre σ2_pre Hinv_pre) as Heq_pre.
                           assert (Econs_l :
                                     @denote_code (@ParamsV IP IPT)
                                       ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al) (Some varg1) ≅
                                     ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                       (fun _ => denote_code post_al (Some varg1)))
                             by reflexivity.
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                                 (eq_itree_clo_bind _ _ _ _ Logic.eq Econs_l (fun _ _ <- => Logic.eq_refl)))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                                  (eq_itree_clo_bind _ _ _ _ Logic.eq
                                                     (symmetry (Eqit.bind_ret_l tt (fun _ => denote_code post_al (Some varg1))))
                                                     (fun _ _ <- => Logic.eq_refl))) |].
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                           eapply refine_cfg_exc_bind.
                           *** exact (stage2_alloca_dead_instr_exc_l ctx1 ctx2 RExc_s2
                                        p dt anns_al md_al (Some varg1) U_pre P_pre fs0 f2
                                        σ1_pre σ2_pre sf2_pre fstk g0
                                        Hsc Hanns_al Hpu_pre Heq_pre Hfs2_pre).
                           *** intros U_al s1_al _ s2_al _ _
                                 (pr_dead & pt_dead & σ1_al & Hnin_dead & -> & _ & _ & -> & -> & Hinv_al).
                               fold sz_dead in Hinv_al.
                               assert (HincU_al : incl (pr_va :: U0) (pr_dead :: U_pre))
                                 by (intros x Hx; right; apply HincU_pre, Hx).
                               assert (Hvars_al : forall x,
                                         x <> p ->
                                         Maps.lookup x (stack_vars (upd_local_sf sf2_pre (Maps.add p (DVALUE_Base (DVALUE_Pointer pt_dead)) (stack_vars sf2_pre)))) =
                                         Maps.lookup x (stack_vars sf2_pre)).
                               { intros x Hne; cbn [stack_vars upd_local_sf]; apply lookup_add_neq, Hne. }
                               assert (Hsplit_post :
                                         blk_code b_init = (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) ++ post_al ++ []).
                               { rewrite <- app_assoc, app_nil_r; exact Hsplit_init. }
                               eapply refine_cfg_exc_bind.
                               ---- exact (stage2_code_exc_sim ctx1 ctx2 RExc_s2
                                             fargs (blks c) b_init
                                             (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                                             safe_no_p p (Some varg1) (pr_dead :: U_pre) P_pre fs0 f2
                                             (ptr_to_int pt_dead) pr_dead sz_dead
                                             σ1_al σ2_pre _ sf2_pre fstk g0
                                             Hnd_bks Hin_init Hsplit_post Hsub_safe
                                             (Hp_blk_nuse b_init Hin_init) Hpost_chk
                                             Hinv_al Hgenv_pre Hsafe_pre Hvars_al).
                               ---- intros U_post s1_post _ s2_post _ _
                                      (σ1_post & σ2_post & sf1_post & sf2_post &
                                       -> & _ & _ & -> & -> & Hinv_post & Hsafe_post & Hvars_post).
                                    destruct (blk_term b_init) as [[iid_tm tm_init] md_tm] eqn:Etm_init.
                                    cbn [fst snd] in Hni_init.
                                    assert (Htm_vars : forall x,
                                              In x (full_term_uses tm_init) ->
                                              Maps.lookup x (stack_vars sf1_post) = Maps.lookup x (stack_vars sf2_post)).
                                    { intros x Hx; apply Hvars_post; intros ->.
                                      apply (Hp_blk_nuse b_init Hin_init), m2r_term_entry_uses_in_block.
                                      rewrite Etm_init; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                    eapply refine_prov_weaken.
                                    ++++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s2
                                                  iid_tm iid_tm tm_init md_tm md_tm
                                                  (pr_dead :: U_pre) σ1_post σ2_post sf1_post sf2_post fstk fstk g0
                                                  Hni_init Htm_vars).
                                         intros ex; refine (conj Logic.eq_refl (conj HincU_al _)).
                                         exists P_pre, f2, (ptr_to_int pt_dead), pr_dead, σ1_post, σ2_post, sf1_post, sf2_post;
                                           repeat split; exact Hinv_post.
                                    ++++ intros U_t [s1_t res1_t] [s2_t res2_t].
                                         destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                           try (intros H; exact H).
                                         intros (-> & -> & -> & <- & Hsucc).
                                         exists P_pre, f2, (ptr_to_int pt_dead), pr_dead,
                                                σ1_post, σ2_post, sf1_post, sf2_post.
                                         exact (conj HincU_al (conj Logic.eq_refl (conj Logic.eq_refl
                                                  (conj Logic.eq_refl (conj Hinv_post
                                                    (conj Hgenv_pre (conj Hsafe_post (conj Hvars_post Hsucc)))))))).
                   --- intros U_b1 s1_b1 bd1 s2_b1 bd2 _
                         (P_pre & f2 & base_dead & pr_dead & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
                          HincU_b1 & <- & -> & -> & Hinv_b1 & Hgenv_pre & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
                       destruct bd1 as [bid_next | dv_ret].
                       +++ assert (Hne_init : bid_next <> init c).
                           { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
                             unfold m2r_all_succs; apply in_flat_map; exists b_init; split; [exact Hin_init |].
                             unfold m2r_block_succs; destruct (blk_term b_init) as [[? ?] ?]; exact Hsucc_b1. }
                           apply refine_cfg_exc_ret.
                           exists P_pre, f2, base_dead, pr_dead, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hinv_b1
                                      (conj Hgenv_pre (conj Hsafe_b1 (conj Hvars_b1 Hne_init)))))))).
                       +++ apply refine_cfg_exc_ret.
                           exists P_pre, f2, base_dead, pr_dead, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hinv_b1
                                      (conj Hgenv_pre (conj Hsafe_b1 (conj Hvars_b1 I)))))))).
                ** intros U_step [s1_step res1_s] [s2_step res2_s] _.
                   destruct res1_s as [ex1 | [j1 | r1]], res2_s as [ex2 | [j2 | r2]]; cbn [exc_post];
                     try contradiction.
                   --- intros Hex; apply refine_prov_ret; exact Hex.
                   --- intros (P_pre & f2 & base_dead & pr_dead & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & <- & -> & -> & Hinv_s & Hgenv_pre & Hsafe_s & Hvars_s & Hne_s).
                       destruct j1 as [bid_from0 bid_src0].
                       apply refine_prov_tau_both.
                       set (RI_loop :=
                              fun U_l (s1_l s2_l : FusedS) (i1 i2 : block_id * block_id) =>
                                i1 = i2 /\
                                snd i2 <> init c /\
                                incl (pr_va :: U0) U_l /\
                                exists σ1_l σ2_l sf1_l sf2_l,
                                  s1_l = (σ1_l, ((sf1_l, fstk), g0)) /\
                                  s2_l = (σ2_l, ((sf2_l, fstk), g0)) /\
                                  stage2_mem_inv U_l P_pre fs0 f2 base_dead pr_dead sz_dead σ1_l σ2_l /\
                                  safe_locals_env P_pre safe_no_p (stack_vars sf2_l) /\
                                  (forall x, x <> p -> Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l))).
                       eapply (refine_cfg_exc_iter ctx1 ctx2 RI_loop RExc_s2 _ _ _ U_step).
                       +++ intros U_l s1_l s2_l [bf1 bs1] [bf2 bs2] Hinc_step
                             (Heq_ij & Hne_bs & HincU_l & σ1_l & σ2_l & sf1_l & sf2_l &
                              -> & -> & Hinv_l & Hsafe_l & Hvars_l).
                           inversion Heq_ij; subst bf1 bs1; clear Heq_ij; cbn [snd] in Hne_bs.
                           rewrite !ScopeTheory.ocfg_map_find_block; cbn [blks].
                           rewrite (m2r_find_block_map_id_pres f_blk (blks c) bs2 Hf_id).
                           destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur; cbn [option_map].
                           *** destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur)
                                 as [Hin_cur Hid_cur].
                               unfold f_blk at 1.
                               destruct (raw_id_eqb_spec (blk_id bk_cur) (init c)) as [Hbad | _];
                                 [exfalso; congruence |].
                               pose proof Ebks_chk as Hbk_cur_chk.
                               rewrite forallb_forall in Hbk_cur_chk.
                               specialize (Hbk_cur_chk bk_cur Hin_cur).
                               destruct (raw_id_eqb_spec (blk_id bk_cur) (init c)) as [Hbad | _];
                                 [exfalso; congruence |].
                               rewrite andb_true_iff in Hbk_cur_chk.
                               destruct Hbk_cur_chk as [Hcd_cur Hni_cur].
                               unfold denote_block.
                               eapply refine_cfg_exc_bind.
                               ---- eapply refine_cfg_exc_bind.
                                    ++++ apply denote_phis_same_exc_sim.
                                         intros x Hx; apply Hvars_l; intros ->.
                                         apply (Hp_blk_nuse bk_cur Hin_cur).
                                         apply in_flat_map in Hx as (pe & Hpe & Hx_pe).
                                         exact (m2r_phi_entry_uses_in_block bk_cur pe p Hpe Hx_pe).
                                    ++++ intros U_ph s1_ph _ s2_ph _ _
                                           (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
                                         assert (Hsafe_ph :
                                                   safe_locals_env P_pre safe_no_p
                                                     (write_phi_dvs dvs (stack_vars sf2_l))).
                                         { apply write_phi_dvs_safe_locals; [| exact Hsafe_l].
                                           intros q Hq Hin_dvs; rewrite Hfst_dvs in Hin_dvs.
                                           apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
                                           exact (unique_alloca_not_phi_def fargs (blks c) q Hnd_bks
                                                    (Hsub_safe q Hq) bk_cur q ph_q md_q Hin_cur Hpe_in Logic.eq_refl). }
                                         assert (Hvars_ph :
                                                   forall x,
                                                     x <> p ->
                                                     Maps.lookup x (write_phi_dvs dvs (stack_vars sf1_l)) =
                                                     Maps.lookup x (write_phi_dvs dvs (stack_vars sf2_l))).
                                         { intros x Hne; apply write_phi_dvs_lookup_agree, Hvars_l, Hne. }
                                         assert (Hsplit_cur : blk_code bk_cur = [] ++ blk_code bk_cur ++ [])
                                           by (rewrite app_nil_r; reflexivity).
                                         eapply refine_cfg_exc_bind.
                                         **** exact (stage2_code_exc_sim ctx1 ctx2 RExc_s2
                                                       fargs (blks c) bk_cur [] (blk_code bk_cur) []
                                                       safe_no_p p (Some varg1) U_l P_pre fs0 f2
                                                       base_dead pr_dead sz_dead
                                                       σ1_l σ2_l
                                                       (upd_local_sf sf1_l (write_phi_dvs dvs (stack_vars sf1_l)))
                                                       (upd_local_sf sf2_l (write_phi_dvs dvs (stack_vars sf2_l)))
                                                       fstk g0
                                                       Hnd_bks Hin_cur Hsplit_cur Hsub_safe
                                                       (Hp_blk_nuse bk_cur Hin_cur) Hcd_cur
                                                       Hinv_l Hgenv_pre Hsafe_ph Hvars_ph).
                                         **** intros U_cd s1_cd _ s2_cd _ _
                                                (σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                                 -> & _ & _ & -> & -> & Hinv_cd & Hsafe_cd & Hvars_cd).
                                              destruct (blk_term bk_cur) as [[iid_tc tm_cur] md_tc] eqn:Etm_cur.
                                              cbn [fst snd] in Hni_cur.
                                              assert (Htm_vars :
                                                        forall x,
                                                          In x (full_term_uses tm_cur) ->
                                                          Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)).
                                              { intros x Hx; apply Hvars_cd; intros ->.
                                                apply (Hp_blk_nuse bk_cur Hin_cur), m2r_term_entry_uses_in_block.
                                                rewrite Etm_cur; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                              eapply refine_prov_weaken.
                                              ----- apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s2
                                                             iid_tc iid_tc tm_cur md_tc md_tc
                                                             U_l σ1_cd σ2_cd sf1_cd sf2_cd fstk fstk g0
                                                             Hni_cur Htm_vars).
                                                    intros ex; refine (conj Logic.eq_refl (conj HincU_l _)).
                                                    exists P_pre, f2, base_dead, pr_dead, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                                      repeat split; exact Hinv_cd.
                                              ----- intros U_t [s1_t res1_t] [s2_t res2_t].
                                                    destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                                      try (intros H; exact H).
                                                    intros (-> & -> & -> & <- & Hsucc_cur).
                                                    exists σ1_cd, σ2_cd, sf1_cd, sf2_cd.
                                                    exact (conj Logic.eq_refl (conj Logic.eq_refl
                                                             (conj Logic.eq_refl (conj Logic.eq_refl
                                                               (conj Hinv_cd (conj Hsafe_cd (conj Hvars_cd Hsucc_cur))))))).
                               ---- intros U_bd s1_bd bd1 s2_bd bd2 _
                                      (σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                       -> & <- & -> & -> & Hinv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
                                    destruct bd1 as [bid_tgt | dv_cur].
                                    ++++ apply refine_cfg_exc_ret.
                                         assert (Hne_tgt : bid_tgt <> init c).
                                         { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
                                           unfold m2r_all_succs; apply in_flat_map; exists bk_cur; split; [exact Hin_cur |].
                                           unfold m2r_block_succs; destruct (blk_term bk_cur) as [[? ?] ?]; exact Hsucc_cur. }
                                         refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_l _))).
                                         exists σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                           exact (conj Logic.eq_refl (conj Logic.eq_refl
                                                    (conj Hinv_cd (conj Hsafe_cd Hvars_cd)))).
                                    ++++ apply refine_cfg_exc_ret.
                                         refine (conj Logic.eq_refl (conj HincU_l _)).
                                         exists P_pre, f2, base_dead, pr_dead, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                           exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_cd)).
                           *** apply refine_cfg_exc_ret.
                               refine (conj Logic.eq_refl (conj HincU_l _)).
                               exists P_pre, f2, base_dead, pr_dead, σ1_l, σ2_l, sf1_l, sf2_l;
                                 exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_l)).
                       +++ refine (conj Logic.eq_refl (conj Hne_s (conj HincU_s _))).
                           exists σ1_s, σ2_s, sf1_s, sf2_s;
                             exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_s (conj Hsafe_s Hvars_s)))).
                   --- intros (P_pre & f2 & base_dead & pr_dead & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & <- & -> & -> & Hinv_s & _).
                       apply refine_prov_ret.
                       refine (conj Logic.eq_refl (conj HincU_s _)).
                       exists P_pre, f2, base_dead, pr_dead, σ1_s, σ2_s, sf1_s, sf2_s;
                         exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_s)).
             ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _
                  (<- & HincU_ocfg & P_e & f2 & base_dead & pr_dead & σ1_e & σ2_e & sf1_e & sf2_e &
                   -> & -> & Hinv_e).
                destruct r_ocfg1 as [bid_miss | uv_ret].
                ** apply refine_cfg_exc_raise_both.
                ** apply refine_cfg_exc_ret.
                   refine (conj Logic.eq_refl (conj HincU_ocfg _)).
                   exists P_e, f2, base_dead, pr_dead, σ1_e, σ2_e, sf1_e, sf2_e;
                     exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_e)).
          -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
             assert (Hrv_unif :
                       rv1 = rv2 /\
                       incl (pr_va :: U0) U_rv /\
                       exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                         s1_rv = (σ1_e, ((sf1_e, fstk), g0)) /\
                         s2_rv = (σ2_e, ((sf2_e, fstk), g0)) /\
                         stage2_mem_inv U_rv P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
             { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                 try contradiction; destruct Hrv_post as [<- Hrest]; split; [reflexivity | exact Hrest]. }
             clear Hrv_post.
             destruct Hrv_unif as (<- & HincU_rv & P_e & f2 & base_dead & pr_dead &
                                   σ1_e & σ2_e & sf1_e & sf2_e & -> & -> & Hinv_e).
             eapply refine_cfg_model_bind.
             ++ exact (pop_call_frame_stage2_sim ctx1 ctx2 U_rv P_e fs0 f2 base_dead pr_dead sz_dead
                         σ1_e σ2_e sf1_e sf2_e sf_caller fstk_caller g0 Hinv_e).
             ++ intros U_pop s1_pop _ s2_pop _ _
                  (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Heq_pop & _).
                pose proof (stage1_equal_to_mem_inv U_rv [] σ1_pop σ2_pop
                              (fun _ H => match H with end) Heq_pop) as Hinv_pop.
                eapply refine_prov_weaken.
                ** exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                            (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                            U_rv [] [] σ1_pop σ2_pop
                            ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv_pop).
                ** intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                   exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                            (conj Heq_pop (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  (** ** 3N. Stage 1 SSA Promotion Helpers, Block Lookup & Block-Address Preservation *)

  Lemma stage1_prom_alloca_init_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (p init_reg : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns : is_only_align_anns anns_al = true)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Htf : top_frame_unprom_from fs0 G (state_memory_stack σ2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists gs0 σ1' σ2',
              ~ In (gs_pr gs0) U /\
              U' = gs_pr gs0 :: U /\
              r1 = tt /\ r2 = tt /\
              gs_dt gs0 = dt /\
              gs_db gs0 = DVALUE_Poison /\
              s1' = (σ1', ((upd_local_sf sf1
                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf1)),
                            fstk1), g)) /\
              s2' = (σ2', ((upd_local_sf sf2
                              (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                 (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2))),
                            fstk2), g)) /\
              stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
              top_frame_prom_from fs0 gs0 G (state_memory_stack σ2')))
      U
      (interp_cfg_exc ctx1
         (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (ITree.bind
            (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va2)
            (fun _ =>
               denote_instr
                 (IId init_reg,
                  INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
                  []) va2))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (is_only_align_anns_num_elts anns_al Hanns) as [Hnum _].
    eapply refine_prov_obs_eq;
      [symmetry;
       apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                (bind_unit_ret_r (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va1)))
      | reflexivity |].
    eapply refine_cfg_exc_bind.
    - cbn [denote_instr]; rewrite Hnum.
      assert (Eal :
                ITree.bind
                  (ITree.bind (alloca dt 1%N (explicit_alignment anns_al)) (fun v => lwrite p v))
                  (fun _ => Ret tt) ≅
                ITree.bind (alloca dt 1%N (explicit_alignment anns_al)) (fun v => lwrite p v)).
      { rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros v _ <-; apply bind_unit_ret_r. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ Eal)
        | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ Eal) |].
      eapply refine_cfg_exc_bind.
      + unfold alloca, Subevent.trigger; try unfold trigger_cast.
        apply refine_cfg_exc_memory_event.
        exact (stage1_alloca_prom dt (explicit_alignment anns_al) fs0 U P_unprom G σ1 σ2 Hsc Hinv Htf).
      + intros U1 [σ1' rest1'] v1 [σ2' rest2'] v2 _
          ((<- & <-) & (gs0 & Hnin & -> & Hdt0 & Hdb0 & -> & -> & Hinv' & Htf')).
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists gs0, σ1', σ2'; repeat split; assumption.
    - intros U1 s1_m _ s2_m _ _
        (gs0 & σ1' & σ2' & Hnin & -> & _ & _ & Hdt0 & Hdb0 & -> & -> & Hinv' & Htf').
      apply denote_init_copy_poison_exc_r.
      eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_ret | reflexivity |].
      destruct sf2 as [sv2 se2 sl2]; cbn [upd_local_sf stack_vars].
      apply refine_prov_ret.
      exists gs0, σ1', σ2'; repeat split; assumption.
  Qed.

  Lemma m2r_assoc_nodup {K V : Type} {Heq : RelDec (@Logic.eq K)} {Hcorr : RelDec_Correct Heq}
    (k : K) (l : list (K * V)) (v : V) :
    NoDup (List.map fst l) ->
    In (k, v) l ->
    assoc k l = Some v.
  Proof using.
    induction l as [| [k0 v0] rest IH]; cbn [List.map fst In assoc]; [intros _ [] |].
    intros Hnd [Heq_p | Hin].
    - inversion Heq_p; subst k0 v0.
      destruct (rel_dec k k) eqn:Er; [reflexivity |].
      exfalso; pose proof (proj2 (rel_dec_correct k k) Logic.eq_refl) as Htr; congruence.
    - inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct (rel_dec k k0) eqn:Er.
      + exfalso; pose proof (proj1 (rel_dec_correct k k0) Er) as ->.
        exact (Hnin (in_map fst rest (k0, v) Hin)).
      + exact (IH Hnd' Hin).
  Qed.

  Lemma denote_phis_stage1_prom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id) (phi_reg src_reg : local_id) (dt : dtyp)
    (incoming : list (block_id * exp dtyp))
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (dv0 : @dvalue (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hassoc : assoc bid_from incoming = Some (EXP_Ident (ID_Local src_reg)))
    (Hlk_src : Maps.lookup src_reg (stack_vars sf2) = Some dv0)
    (Hvars : forall x,
               In x (flat_map m2r_phi_entry_uses phis) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dvs,
              U' = U /\ r1 = tt /\ r2 = tt /\
              List.map fst dvs = List.map (fun '(id, _, _) => id) phis /\
              s1' = (σ1, ((upd_local_sf sf1 (write_phi_dvs dvs (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (write_phi_dvs ((phi_reg, dv0) :: dvs) (stack_vars sf2)),
                           fstk2), g))))
      U
      (interp_cfg_exc ctx1 (denote_phis bid_from phis) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (denote_phis bid_from ((phi_reg, Phi [] dt incoming, []) :: phis))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold denote_phis.
    cbn [map_monad denote_phi Monads.bind Monads.ret Monad_itree]; rewrite Hassoc.
    assert (Er_assoc :
      ITree.bind
        (ITree.bind
           (ITree.bind (denote_exp' (Some dt) (EXP_Ident (ID_Local src_reg)))
              (fun dv => Ret (phi_reg, dv)))
           (fun y =>
              ITree.bind (map_monad (denote_phi bid_from) phis)
                (fun ys => Ret (y :: ys))))
        (fun dvs =>
           ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) dvs) (fun _ => Ret tt)) ≅
      ITree.bind (denote_exp' (Some dt) (EXP_Ident (ID_Local src_reg)))
        (fun dv0' =>
           ITree.bind (map_monad (denote_phi bid_from) phis)
             (fun dvs =>
                ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) ((phi_reg, dv0') :: dvs))
                  (fun _ => Ret tt)))).
    { rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros dv0' _ <-; rewrite Eqit.bind_ret_l, Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros dvs _ <-; apply Eqit.bind_ret_l. }
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry; rewrite (interp_cfg_exc_obs_eq ctx2 _ _ _ Er_assoc);
        apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand_r;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    eapply refine_prov_obs_eq; [reflexivity | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some src_reg dv0 σ2 sf2 fstk2 g Hlk_src) |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; rewrite !Eqit.bind_ret_l; reflexivity |].
    eapply refine_cfg_exc_bind; [apply map_monad_denote_phi_same_exc_sim, Hvars |].
    intros U1 s1' dvs1 s2' dvs2 _ (-> & -> & -> & <- & Hfst).
    eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_write_phi_dvs |].
    eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_write_phi_dvs |].
    apply refine_prov_ret; exists dvs1; repeat split; try exact Hfst; reflexivity.
  Qed.

  Lemma pass1_end_map_fst
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id)) :
    List.map fst (List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out) =
    List.map blk_id (List.map (fun '(bk, _, _, _) => bk) pass1_out).
  Proof using.
    induction pass1_out as [| [[[bk pr] cd] er] rest IH]; cbn; [reflexivity | f_equal; exact IH].
  Qed.

  Lemma pass1_find_block_gen
    (f : block dtyp * local_id * code dtyp * local_id -> block dtyp)
    (ps : list (block dtyp * local_id * code dtyp * local_id))
    (Hf_id : forall bk pr cd er, blk_id (f (bk, pr, cd, er)) = blk_id bk) :
    (forall bid,
       find_block (List.map (fun '(bk, _, _, _) => bk) ps) bid = None ->
       find_block (List.map f ps) bid = None) /\
    (forall bid bk,
       find_block (List.map (fun '(bk, _, _, _) => bk) ps) bid = Some bk ->
       exists pr cd er,
         In (bk, pr, cd, er) ps /\
         find_block (List.map f ps) bid = Some (f (bk, pr, cd, er))).
  Proof using.
    induction ps as [| [[[bk0 pr0] cd0] er0] rest [IH_none IH_some]]; cbn [List.map].
    - split; [intros _ _; reflexivity | intros ? ? H; cbn in H; discriminate H].
    - pose proof (Hf_id bk0 pr0 cd0 er0) as Hid0.
      split.
      + intros bid Hnone.
        destruct (raw_id_eqb_spec (blk_id bk0) bid) as [Heq | Hne].
        * rewrite find_block_eq in Hnone by exact Heq; discriminate Hnone.
        * rewrite find_block_ineq in Hnone by exact Hne.
          rewrite find_block_ineq by congruence.
          exact (IH_none bid Hnone).
      + intros bid bk Hsome.
        destruct (raw_id_eqb_spec (blk_id bk0) bid) as [Heq | Hne].
        * rewrite find_block_eq in Hsome by exact Heq; inversion Hsome; subst bk0.
          rewrite find_block_eq by congruence.
          exists pr0, cd0, er0; split; [left; reflexivity | reflexivity].
        * rewrite find_block_ineq in Hsome by exact Hne.
          rewrite find_block_ineq by congruence.
          destruct (IH_some bid bk Hsome) as (pr & cd & er & Hin & Hfb).
          exists pr, cd, er; split; [right; exact Hin | exact Hfb].
  Qed.

  Lemma pass1_find_block_spec
    (init_bid : block_id) (dt : dtyp) (init_reg : local_id)
    (all_bks : ocfg dtyp)
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id))
    (Hbks : List.map (fun '(bk, _, _, _) => bk) pass1_out = all_bks) :
    let end_map := List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out in
    let bks' := build_promoted_blocks init_bid dt init_reg all_bks pass1_out in
    (forall bid, find_block all_bks bid = None -> find_block bks' bid = None) /\
    (forall bid bk,
       find_block all_bks bid = Some bk ->
       exists phi_r cd' end_r,
         In (bk, phi_r, cd', end_r) pass1_out /\
         find_block bks' bid =
           Some (if raw_id_eqb (blk_id bk) init_bid then
                   {| blk_id := blk_id bk; blk_phis := blk_phis bk; blk_code := cd';
                      blk_term := blk_term bk; blk_comments := blk_comments bk |}
                 else
                   let preds := List.filter (fun b_pred => in_raw_ids (blk_id bk) (m2r_block_succs b_pred)) all_bks in
                   let incoming := List.map (fun b_pred => (blk_id b_pred, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_pred) init_reg)))) preds in
                   {| blk_id := blk_id bk; blk_phis := (phi_r, Phi [] dt incoming, []) :: blk_phis bk;
                      blk_code := cd'; blk_term := blk_term bk; blk_comments := blk_comments bk |})).
  Proof using.
    intros end_map bks'; subst bks'; unfold build_promoted_blocks; fold end_map.
    rewrite <- Hbks at 1; rewrite <- Hbks at 2.
    apply (pass1_find_block_gen
             (fun '(bk, phi_r, cd', _) =>
                if raw_id_eqb (blk_id bk) init_bid then
                  {| blk_id := blk_id bk; blk_phis := blk_phis bk; blk_code := cd';
                     blk_term := blk_term bk; blk_comments := blk_comments bk |}
                else
                  let preds := List.filter (fun b_pred => in_raw_ids (blk_id bk) (m2r_block_succs b_pred)) all_bks in
                  let incoming := List.map (fun b_pred => (blk_id b_pred, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_pred) init_reg)))) preds in
                  {| blk_id := blk_id bk; blk_phis := (phi_r, Phi [] dt incoming, []) :: blk_phis bk;
                     blk_code := cd'; blk_term := blk_term bk; blk_comments := blk_comments bk |})
             pass1_out).
    intros bk pr cd er; destruct (raw_id_eqb (blk_id bk) init_bid); reflexivity.
  Qed.

  Lemma rewrite_code_for_slot_block_addresses_nil
    (p : local_id) (dt : dtyp) (cur_reg : local_id) (avoid : list raw_id)
    (cd cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id) :
    flat_map (fun '(_, i, _) => instr_block_addresses i) cd = [] ->
    rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid') ->
    flat_map (fun '(_, i, _) => instr_block_addresses i) cd' = [].
  Proof using.
    revert cur_reg avoid cd' end_reg avoid';
      induction cd as [| [[iid ins] md] rest IH];
      intros cur_reg avoid cd' end_reg avoid' Hba Hrw;
      cbn [rewrite_code_for_slot] in Hrw; cbn [flat_map] in Hba.
    - inversion Hrw; subst; reflexivity.
    - apply app_eq_nil in Hba as [Him_ba Hrest_ba].
      destruct (is_promotable_load_of p dt (iid, ins, md)) as [dst |].
      + destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
        inversion Hrw; subst; cbn; exact (IH cur_reg avoid rest' end_reg avoid' Hrest_ba E).
      + destruct (is_promotable_store_of p dt (iid, ins, md)) as [val_exp |] eqn:Est.
        * destruct (is_promotable_store_of_inv p dt (iid, ins, md) val_exp Est)
            as (_ & vid & anns_st & md_st & Heq_im & _).
          inversion Heq_im; subst iid ins md; clear Heq_im.
          cbn in Him_ba; rewrite !app_nil_r in Him_ba.
          destruct (rewrite_code_for_slot p dt (fresh_name "m2r_st" avoid)
                      (fresh_name "m2r_st" avoid :: avoid) rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; cbn; rewrite Him_ba; cbn.
          exact (IH _ _ rest' end_reg avoid' Hrest_ba E).
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; cbn; rewrite Him_ba; cbn.
          exact (IH cur_reg avoid rest' end_reg avoid' Hrest_ba E).
  Qed.

  Lemma flat_map_nil_in {A B : Type} (f : A -> list B) (xs : list A) :
    (forall x, In x xs -> f x = []) <-> flat_map f xs = [].
  Proof using.
    induction xs as [| x xs' IH]; cbn [flat_map In].
    - split; [intros _; reflexivity | intros _ ? []].
    - split.
      + intros Hall; rewrite (Hall x (or_introl Logic.eq_refl)); cbn.
        apply IH; intros y Hy; exact (Hall y (or_intror Hy)).
      + intros Hnil; apply app_eq_nil in Hnil as [Hx Hxs].
        intros y [<- | Hy]; [exact Hx | exact (proj2 IH Hxs y Hy)].
  Qed.

  Lemma promote_slot_in_defn_block_addresses
    (interproc_safe : bool) (df df' : definition dtyp (CFG.cfg dtyp)) :
    try_promote_slot_in_defn interproc_safe df = Some df' ->
    df_prototype df' = df_prototype df /\
    flat_map block_block_addresses (blks (df_instrs df')) =
    flat_map block_block_addresses (blks (df_instrs df)).
  Proof using.
    unfold try_promote_slot_in_defn; intros Htry.
    set (fargs := df_args df) in *; set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff in Eg1; destruct Eg1 as [[_ _] Hnba].
    apply cfg_no_block_addresses_nil in Hnba.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Ef; [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Ef) as [Hin_init _].
    destruct (m2r_is_empty (blk_phis b_init)); [| discriminate Htry].
    destruct (find_promotable_in_init_code interproc_safe
                (fargs ++ flat_map full_block_defs (blks c))
                (flat_map full_block_uses (blks c))
                (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))
                (init c) (blks c) b_init [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind; [| discriminate Htry].
    pose proof (find_promotable_in_init_code_inv interproc_safe
                  (fargs ++ flat_map full_block_defs (blks c))
                  (flat_map full_block_uses (blks c))
                  (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))
                  (init c) (blks c) b_init [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & _) & _).
    inversion Htry; subst df'; clear Htry.
    split; [reflexivity |].
    rewrite Hnba; apply (proj1 (flat_map_nil_in block_block_addresses _)).
    pose proof (proj2 (flat_map_nil_in block_block_addresses (blks c)) Hnba) as Hbk_nil.
    unfold promote_slot_in_cfg; cbn [blks].
    set (avoid0 := fargs ++ cfg_all_ids c).
    set (init_reg := fresh_name "m2r_init" avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    set (init_op := (IId init_reg, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison), [])).
    set (init_code' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al').
    set (bk_phis := List.combine (blks c) phi_regs).
    destruct (rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code' avoid3 bk_phis)
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hinit_ba : flat_map (fun '(_, i, _) => instr_block_addresses i) init_code' = []).
    { pose proof (Hbk_nil b_init Hin_init) as Hb0; unfold block_block_addresses in Hb0.
      apply app_eq_nil in Hb0 as [Hb0a _]; apply app_eq_nil in Hb0a as [_ Hb0_cd].
      rewrite Hsplit_init, flat_map_app in Hb0_cd; cbn [flat_map instr_block_addresses] in Hb0_cd.
      apply app_eq_nil in Hb0_cd as [Hpre_ba Hpost_ba].
      pose proof (rewrite_code_for_slot_block_addresses_nil p dt init_reg avoid2
                    post_al post_al' init_end_reg avoid3 Hpost_ba Erw_post) as Hpost'_ba.
      unfold init_code', init_op; rewrite flat_map_app; cbn; rewrite Hpre_ba, Hpost'_ba; reflexivity. }
    assert (Hinc2 : incl avoid0 avoid2).
    { intros z Hz; unfold avoid2, avoid1; apply in_app_iff; right; right; exact Hz. }
    assert (Hinit_nin0 : ~ In init_reg avoid0) by apply fresh_name_not_in.
    destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt init_reg avoid2 post_al
                post_al' init_end_reg avoid3 Erw_post Hinc2 Hinit_nin0) as [Hav3 Hinit_er_nin0].
    assert (Hinc3 : incl avoid0 avoid3) by (eapply incl_tran; eassumption).
    assert (Hlen_pr : List.length (blks c) = List.length phi_regs)
      by (symmetry; apply fresh_names_length).
    assert (Hphis_nin0 : forall r, In r (List.map snd bk_phis) -> ~ In r avoid0).
    { unfold bk_phis; rewrite (combine_snd_eq _ _ Hlen_pr).
      intros r Hr Hin0; eapply (fresh_names_disjoint "m2r_phi" _ avoid1 r Hr); right; exact Hin0. }
    destruct (rewrite_non_entry_blocks_pass1_spec avoid0 (init c) p dt init_end_reg init_code'
                avoid3 bk_phis pass1_out avoid_out Epass1 Hinc3 Hinit_er_nin0 Hphis_nin0)
      as (Hbks_p1 & _ & _ & Hall_p1).
    unfold bk_phis in Hbks_p1; rewrite (combine_fst_eq _ _ Hlen_pr) in Hbks_p1.
    unfold build_promoted_blocks; intros b' Hb'.
    apply in_map_iff in Hb' as [[[[bk phi_r] cd'] end_r] [<- Hin_p1]].
    assert (Hin_bk : In bk (blks c)).
    { rewrite <- Hbks_p1; exact (in_map (fun '(b0, _, _, _) => b0) _ _ Hin_p1). }
    pose proof (Hbk_nil bk Hin_bk) as Hbk_ba; unfold block_block_addresses in Hbk_ba.
    apply app_eq_nil in Hbk_ba as [Hbk_ba1 Hbk_tm]; apply app_eq_nil in Hbk_ba1 as [Hbk_ph Hbk_cd].
    pose proof (Hall_p1 bk phi_r cd' end_r Hin_p1) as (_ & _ & Hcd_spec).
    destruct (raw_id_eqb (blk_id bk) (init c)).
    - destruct Hcd_spec as [-> _]; unfold block_block_addresses; cbn.
      rewrite Hbk_ph, Hinit_ba, Hbk_tm; reflexivity.
    - destruct Hcd_spec as (av_in & av_out & _ & Erw_bk).
      pose proof (rewrite_code_for_slot_block_addresses_nil p dt phi_r av_in
                    (blk_code bk) cd' end_r av_out Hbk_cd Erw_bk) as Hcd'_ba.
      unfold block_block_addresses; cbn [blk_phis blk_code blk_term flat_map].
      assert (Hinc_ba :
        forall preds0,
          flat_map (fun x : block_id * exp dtyp => exp_block_addresses (snd x))
            (List.map
               (fun b_pred : block dtyp =>
                  (blk_id b_pred,
                   EXP_Ident (ID_Local (lookup_end_reg
                     (List.map (fun '(bk0, _, _, end_r0) => (blk_id bk0, end_r0)) pass1_out)
                     (blk_id b_pred) init_reg))))
               preds0) = []).
      { induction preds0 as [| bp rest_p IHp]; cbn; [reflexivity | exact IHp]. }
      rewrite Hinc_ba, Hbk_ph, Hcd'_ba, Hbk_tm; reflexivity.
  Qed.

  Lemma elim_dead_alloca_in_defn_block_addresses
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    try_elim_dead_alloca_in_defn df = Some df' ->
    df_prototype df' = df_prototype df /\
    flat_map block_block_addresses (blks (df_instrs df')) =
    flat_map block_block_addresses (blks (df_instrs df)).
  Proof using.
    unfold try_elim_dead_alloca_in_defn; intros Htry.
    set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff in Eg1; destruct Eg1 as [[_ _] Hnba].
    apply cfg_no_block_addresses_nil in Hnba.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Ef; [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Ef) as [Hin_init _].
    destruct (m2r_is_empty (blk_phis b_init) && m2r_non_invoke_term (snd (fst (blk_term b_init))));
      [| discriminate Htry].
    destruct (find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind; [| discriminate Htry].
    pose proof (find_trailing_dead_alloca_in_code_inv _ _ _ [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & _) & _).
    destruct (forallb _ (blks c)); [| discriminate Htry].
    inversion Htry; subst df'; clear Htry; split; [reflexivity |].
    rewrite Hnba; apply (proj1 (flat_map_nil_in block_block_addresses _)).
    pose proof (proj2 (flat_map_nil_in block_block_addresses (blks c)) Hnba) as Hbk_nil.
    cbn [blks]; intros b' Hb'; apply in_map_iff in Hb' as [bk [<- Hin_bk]].
    pose proof (Hbk_nil bk Hin_bk) as Hbk_ba.
    destruct (raw_id_eqb (blk_id bk) (init c)); [| exact Hbk_ba].
    pose proof (Hbk_nil b_init Hin_init) as Hb0; unfold block_block_addresses in Hb0.
    apply app_eq_nil in Hb0 as [Hb0a _]; apply app_eq_nil in Hb0a as [_ Hb0_cd].
    rewrite Hsplit_init, flat_map_app in Hb0_cd; cbn [flat_map instr_block_addresses] in Hb0_cd.
    apply app_eq_nil in Hb0_cd as [Hpre_ba Hpost_ba].
    unfold block_block_addresses in Hbk_ba |- *; cbn [blk_phis blk_code blk_term].
    apply app_eq_nil in Hbk_ba as [Hbk_ba1 Hbk_tm]; apply app_eq_nil in Hbk_ba1 as [Hbk_ph _].
    rewrite flat_map_app, Hbk_ph, Hpre_ba, Hpost_ba, Hbk_tm; reflexivity.
  Qed.

  (** ** 3O. Stage 1 Leaf Slot Promotion Simulation *)

  Lemma m2r_nodup_map_filter {A B : Type} (f : A -> B) (pred : A -> bool) (xs : list A) :
    NoDup (List.map f xs) ->
    NoDup (List.map f (List.filter pred xs)).
  Proof using.
    induction xs as [| x xs' IH]; cbn [List.map List.filter]; [intros _; constructor |].
    intros Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
    destruct (pred x); cbn [List.map].
    - constructor; [| exact (IH Hnd')].
      intros Hin; apply in_map_iff in Hin as (y & Heq & Hy).
      apply filter_In in Hy as [Hy _].
      apply Hnin; rewrite <- Heq; exact (in_map f xs' y Hy).
    - exact (IH Hnd').
  Qed.

  Lemma safe_locals_in_avoid0 (fargs : list local_id) (c : CFG.cfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c)) ->
    In q (fargs ++ cfg_all_ids c).
  Proof using.
    unfold m2r_collect_unique_allocas; intros Hq.
    apply in_flat_map in Hq as (bk & Hbk & Hq_bk).
    apply in_flat_map in Hq_bk as ([[iid ins] md] & Him & Hq_im).
    destruct iid as [id0 |]; [| contradiction Hq_im].
    destruct ins; try contradiction Hq_im.
    destruct (Nat.eqb (m2r_count_id id0 (fargs ++ flat_map full_block_defs (blks c))) 1%nat);
      cbn in Hq_im; [| contradiction Hq_im].
    destruct Hq_im as [<- | []].
    apply in_app_iff; right; eapply in_defs_in_cfg_all_ids; [exact Hbk |].
    unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists (IId q, INSTR_Alloca dt annotations, md);
      split; [exact Him | left; reflexivity].
  Qed.

  Lemma rewrite_code_for_slot_no_call_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (avoid0 : list raw_id) (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id) (dt : dtyp)
    (cur_reg : local_id) (avoid : list raw_id)
    (cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id)
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hsafe_av0 : incl safe_no_p avoid0)
    (Huses_av0 : forall im x, In im cd -> In x (m2r_code_entry_uses im) -> In x avoid0)
    (Hdefs_av0 : forall im x, In im cd -> In x (instr_id_defs (fst (fst im))) -> In x avoid0)
    (Hp_nd_cd : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd))
    (Hchk : forallb (check_code_entry_for_slot false safe_no_p p dt) cd = true)
    (Hrw : rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid'))
    (Hinc_av : incl avoid0 avoid)
    (Hcur_nin0 : ~ In cur_reg avoid0)
    (Hsc : is_scalar_dtyp dt = true)
    (Hdt : gs_dt gs = dt)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               In x avoid0 -> x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' gs' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              gs_dt gs' = dt /\
              Maps.lookup p (stack_vars sf1') = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs'))) /\
              Maps.lookup end_reg (stack_vars sf2') = Some (DVALUE_Base (gs_db gs')) /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' (gs' :: G) σ1' σ2' /\
              top_frame_prom_from fs0 gs' G (state_memory_stack σ2') /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_no_p (stack_vars sf2') /\
              (forall x,
                 In x avoid0 -> x <> p ->
                 Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_code cd' va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    revert pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
      Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
      Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
        Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
        Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars;
      cbn [rewrite_code_for_slot forallb flat_map] in *.
    - inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
      unfold denote_code; cbn [loop_monad].
      apply refine_cfg_exc_ret.
      exists P_unprom, gs, σ1, σ2, sf1, sf2;
        repeat split; try apply incl_refl; assumption.
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Hp_nd_im : ~ In p (instr_id_defs (fst (fst im)))).
      { destruct im as [[iid_i ?] ?]; intros Hp; apply Hp_nd_cd, in_app_iff; left; exact Hp. }
      assert (Hp_nd_rest : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest)).
      { intros Hp; apply Hp_nd_cd, in_app_iff; right; exact Hp. }
      assert (Huses_rest : forall im0 x, In im0 rest -> In x (m2r_code_entry_uses im0) -> In x avoid0)
        by (intros im0 x Him0 Hx; exact (Huses_av0 im0 x (or_intror Him0) Hx)).
      assert (Hdefs_rest : forall im0 x, In im0 rest -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0)
        by (intros im0 x Him0 Hx; exact (Hdefs_av0 im0 x (or_intror Him0) Hx)).
      assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
        by (rewrite <- app_assoc; exact Hsplit).
      unfold check_code_entry_for_slot in Hchk_im.
      destruct (is_promotable_load_of p dt im) as [dst |] eqn:Eld.
      + destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
        inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
        pose proof (Hdefs_av0 im dst (or_introl Logic.eq_refl)) as Hdst_av0_fn.
        destruct (is_promotable_load_of_inv p dt im dst Eld)
          as (Hdst_ne_p & anns_ld & md_ld & -> & _ & Hmd_ld).
        assert (Hdst_av0 : In dst avoid0) by (apply Hdst_av0_fn; left; reflexivity).
        assert (Hcur_ne_dst : cur_reg <> dst) by (intros ->; exact (Hcur_nin0 Hdst_av0)).
        assert (Hdst_nsafe : ~ In dst safe_no_p).
        { intros Hin_s.
          destruct (unique_alloca_code_def_is_alloca fargs bks dst Hnd_bks (Hsub dst Hin_s)
                      bk pre_c
                      (INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld)
                      md_ld (rest ++ post_c) Hbk Hsplit) as (? & ? & Hbad);
            discriminate Hbad. }
        unfold denote_code; cbn [loop_monad].
        eapply refine_cfg_exc_bind.
        * exact (denote_mk_load_val_exp_exc_sim ctx1 ctx2 RExc dst p cur_reg dt anns_ld md_ld
                   va1 va2 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                   Hdt Hsc Hmd_ld Hlk_p Hlk_cur Hinv).
        * intros U1 s1_m _ s2_m _ _ (dv_ld & -> & _ & _ & -> & ->).
          assert (Hlk_p1 : Maps.lookup p (Maps.add dst dv_ld (stack_vars sf1)) =
                           Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs)))).
          { rewrite lookup_add_neq by (intros ->; exact (Hdst_ne_p Logic.eq_refl)); exact Hlk_p. }
          assert (Hlk_cur1 : Maps.lookup cur_reg (Maps.add dst dv_ld (stack_vars sf2)) =
                             Some (DVALUE_Base (gs_db gs))).
          { rewrite lookup_add_neq by exact Hcur_ne_dst; exact Hlk_cur. }
          assert (Hsafe1 : safe_locals_env P_unprom safe_no_p (Maps.add dst dv_ld (stack_vars sf2)))
            by (apply safe_locals_env_add_other; assumption).
          assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                             Maps.lookup x (Maps.add dst dv_ld (stack_vars sf1)) =
                             Maps.lookup x (Maps.add dst dv_ld (stack_vars sf2))).
          { intros x Hx Hne; destruct (raw_id_eqb_spec x dst) as [-> | Hxd];
              [rewrite !lookup_add_eq; reflexivity | rewrite !lookup_add_neq by exact Hxd; exact (Hvars x Hx Hne)]. }
          exact (IH (pre_c ++ [_]) cur_reg avoid rest' er av' U P_unprom gs σ1 σ2
                   (upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)))
                   (upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)))
                   Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                   Hinc_av Hcur_nin0 Hdt Hlk_p1 Hlk_cur1 Hinv Htf Hgenv Hsafe1 Hvars1).
      + destruct (is_promotable_store_of p dt im) as [val_exp |] eqn:Est.
        * set (st_reg := fresh_name "m2r_st" avoid) in *.
          destruct (rewrite_code_for_slot p dt st_reg (st_reg :: avoid) rest) as [[rest' er] av'] eqn:Erest.
          inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
          pose proof (Huses_av0 im) as Hval_av0_fn.
          destruct (is_promotable_store_of_inv p dt im val_exp Est)
            as (Hnin_p_val & vid & anns_st & md_st & -> & _ & _).
          assert (Hst_nin0 : ~ In st_reg avoid0)
            by (intros Hin0; exact (fresh_name_not_in "m2r_st" avoid (Hinc_av _ Hin0))).
          assert (Hst_nsafe : ~ In st_reg safe_no_p)
            by (intros Hin_s; exact (Hst_nin0 (Hsafe_av0 st_reg Hin_s))).
          assert (Hval_vars : forall x,
                    In x (full_exp_uses val_exp) ->
                    Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
          { intros x Hx; apply Hvars.
            - apply Hval_av0_fn; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
                apply in_app_iff; left; apply in_app_iff; left; exact Hx.
            - intros ->; exact (Hnin_p_val Hx). }
          unfold denote_code; cbn [loop_monad].
          eapply refine_cfg_exc_bind.
          -- exact (denote_mk_store_val_exp_exc_sim ctx1 ctx2 RExc vid p st_reg dt val_exp
                      anns_st md_st va1 va2 fs0 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                      Hdt Hsc Hlk_p Hinv Htf Hval_vars).
          -- intros U1 s1_m _ s2_m _ _ (db' & bs' & σ1' & -> & _ & _ & _ & -> & -> & Hinv1 & Htf1).
             assert (Hinc_av1 : incl avoid0 (st_reg :: avoid))
               by (intros z Hz; right; exact (Hinc_av z Hz)).
             assert (Hlk_st : Maps.lookup st_reg (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)) =
                              Some (DVALUE_Base (gs_db (gs_set_val gs db' bs'))))
               by (cbn [gs_db gs_set_val]; apply lookup_add_eq).
             assert (Hsafe1 : safe_locals_env P_unprom safe_no_p
                                (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)))
               by (apply safe_locals_env_add_other; assumption).
             assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                                Maps.lookup x (stack_vars sf1) =
                                Maps.lookup x (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2))).
             { intros x Hx Hne; rewrite lookup_add_neq by (intros ->; exact (Hst_nin0 Hx));
                 exact (Hvars x Hx Hne). }
             exact (IH (pre_c ++ [_]) st_reg (st_reg :: avoid) rest' er av'
                      U P_unprom (gs_set_val gs db' bs') σ1' σ2 sf1
                      (upd_local_sf sf2 (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)))
                      Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                      Hinc_av1 Hst_nin0 Hdt Hlk_p Hlk_st Hinv1 Htf1 Hgenv Hsafe1 Hvars1).
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
          inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
          assert (Huse_im : forall x,
                    In x (m2r_code_entry_uses im) ->
                    Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
          { intros x Hx; apply Hvars;
              [exact (Huses_av0 im x (or_introl Logic.eq_refl) Hx)
              | intros ->; exact (proj1 (check_other_instr_for_slot_inv false safe_no_p p im Hchk_im) Hx)]. }
          unfold denote_code; cbn [loop_monad].
          eapply refine_cfg_exc_bind.
          -- exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc
                      (fun s => top_frame_prom_from fs0 gs G (state_memory_stack s))
                      fargs bks bk pre_c (rest ++ post_c)
                      safe_no_p p im va1 va2 U P_unprom (gs :: G) σ1 σ2 sf1 sf2 fstk1 fstk2 g
                      Hnd_bks Hbk Hsplit Hsub Hchk_im
                      (fun s_a s_b Heq_fs HT => top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs) HT)
                      (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                         top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs)
                           (top_frame_prom_add_ptrs fs0 gs G ptrs _ HT Hdisj))
                      Hinv Htf Hgenv Hsafe_loc Huse_im).
          -- intros U1 s1_m _ s2_m _ _
               (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
                HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & Htf1 & Hgenv1 & Hsafe1 & Hsf_step).
             assert (Hstep_env :
                       Maps.lookup p (stack_vars sf1_m) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) /\
                       Maps.lookup cur_reg (stack_vars sf2_m) = Some (DVALUE_Base (gs_db gs)) /\
                       (forall x, In x avoid0 -> x <> p ->
                          Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m))).
             { destruct Hsf_step as [[-> ->] | (id0 & v & Heq_iid & -> & ->)];
                 [exact (conj Hlk_p (conj Hlk_cur Hvars)) |].
               assert (Hid_av0 : In id0 avoid0).
               { apply (Hdefs_av0 im id0 (or_introl Logic.eq_refl)); rewrite Heq_iid; left; reflexivity. }
               assert (Hp_ne_id : p <> id0)
                 by (intros ->; apply Hp_nd_im; rewrite Heq_iid; left; reflexivity).
               assert (Hcur_ne_id : cur_reg <> id0)
                 by (intros ->; exact (Hcur_nin0 Hid_av0)).
               cbn [stack_vars upd_local_sf]; split;
                 [rewrite lookup_add_neq by exact Hp_ne_id; exact Hlk_p | split;
                 [rewrite lookup_add_neq by exact Hcur_ne_id; exact Hlk_cur |]].
               intros x Hx Hne; destruct (raw_id_eqb_spec x id0) as [-> | Hx_id];
                 [rewrite !lookup_add_eq; reflexivity
                 | rewrite !lookup_add_neq by exact Hx_id; exact (Hvars x Hx Hne)]. }
             destruct Hstep_env as (Hlk_p1 & Hlk_cur1 & Hvars1).
             eapply refine_prov_weaken.
             ++ exact (IH (pre_c ++ [im]) cur_reg avoid rest' er av' U1 P1 gs σ1_m σ2_m sf1_m sf2_m
                         Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                         Hinc_av Hcur_nin0 Hdt Hlk_p1 Hlk_cur1 Hinv1 Htf1 Hgenv1 Hsafe1 Hvars1).
             ++ intros U2 [s1_f res1] [s2_f res2].
                destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
                  try (intros H; exact H).
                intros (P2 & gs2 & σ1_f & σ2_f & sf1_f & sf2_f &
                        HincU2 & HincP2 & -> & -> & Hdt2 & Hlk_p2 & Hlk_er2 &
                        -> & -> & Hinv2 & Htf2 & Hgenv2 & Hsafe2 & Hvars2).
                exists P2, gs2, σ1_f, σ2_f, sf1_f, sf2_f.
                exact (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                         (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Hdt2 (conj Hlk_p2 (conj Hlk_er2
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Hinv2 (conj Htf2 (conj Hgenv2 (conj Hsafe2 Hvars2))))))))))))).
  Qed.

  Lemma try_promote_slot_leaf_denote_function_sim
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    genv_safe P0 g0 ->
    try_promote_slot_in_defn false df = Some df' ->
    leaf_ctx_fn_rel P0 g0 (denote_function df) (denote_function df').
  Proof using.
    intros Hgenv0 Htry.
    unfold try_promote_slot_in_defn in Htry.
    set (fargs := df_args df) in *.
    set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff, negb_true_iff in Eg1.
    destruct Eg1 as [[Hnd_bks Hno_entry_pred] _].
    apply m2r_nodup_ids_spec in Hnd_bks.
    apply in_raw_ids_false in Hno_entry_pred.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind_init;
      [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Efind_init)
      as [Hin_init Hid_init].
    destruct (m2r_is_empty (blk_phis b_init)) eqn:Ephis_init; [| discriminate Htry].
    apply m2r_is_empty_spec in Ephis_init.
    set (all_defs := fargs ++ flat_map full_block_defs (blks c)) in *.
    set (all_uses := flat_map full_block_uses (blks c)) in *.
    set (safe_locals := m2r_collect_unique_allocas all_defs (blks c)) in *.
    destruct (find_promotable_in_init_code false all_defs all_uses safe_locals
                (init c) (blks c) b_init [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
      [| discriminate Htry].
    pose proof (find_promotable_in_init_code_inv false all_defs all_uses safe_locals
                  (init c) (blks c) b_init [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind_al) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals) in *.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & Hanns_al & _) &
                         Hsc & Hcnt_p & _ & Hpre_chk & Hpost_chk & Hterm_p & Hni_init & Ebks_chk).
    apply in_raw_ids_false in Hterm_p.
    inversion Htry; subst df'; clear Htry.
    destruct (unique_def_code_split fargs (blks c) b_init pre_al p
                (INSTR_Alloca dt anns_al) md_al post_al Hnd_bks Hin_init Hsplit_init Hcnt_p)
      as (_ & _ & _ & Hp_nd_post & _ & Hp_nd_other).
    assert (Hsub_safe : forall q, In q safe_no_p -> In q safe_locals)
      by (intros q Hq; apply filter_In in Hq as [Hq _]; exact Hq).
    assert (Hp_nin_safe : ~ In p safe_no_p).
    { intros Hp; apply filter_In in Hp as [_ Hp]; rewrite raw_id_eqb_refl in Hp; discriminate Hp. }
    set (avoid0 := fargs ++ cfg_all_ids c).
    assert (Hsafe_av0 : incl safe_no_p avoid0)
      by (intros q Hq; apply safe_locals_in_avoid0, Hsub_safe, Hq).
    assert (Hblk_uses_av0 : forall bk x, In bk (blks c) -> In x (full_block_uses bk) -> In x avoid0)
      by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_uses_in_cfg_all_ids c bk x Hbk Hx)).
    assert (Hblk_defs_av0 : forall bk x, In bk (blks c) -> In x (full_block_defs bk) -> In x avoid0)
      by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_defs_in_cfg_all_ids c bk x Hbk Hx)).
    set (c' := promote_slot_in_cfg fargs c b_init pre_al (IId p, INSTR_Alloca dt anns_al, md_al) post_al p dt).
    set (init_reg := fresh_name "m2r_init" avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    set (init_op := (IId init_reg, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison), [])).
    set (init_code' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al').
    set (bk_phis := List.combine (blks c) phi_regs).
    destruct (rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code' avoid3 bk_phis)
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hc'_eq :
      c' = {| init := init c;
              blks := build_promoted_blocks (init c) dt init_reg (blks c) pass1_out;
              args := args c |}).
    { unfold c', promote_slot_in_cfg.
      fold avoid0 init_reg avoid1 phi_regs avoid2.
      rewrite Erw_post; fold init_op init_code' bk_phis.
      rewrite Epass1; reflexivity. }
    assert (Hinit_nin0 : ~ In init_reg avoid0) by apply fresh_name_not_in.
    assert (Hinc_av2 : incl avoid0 avoid2)
      by (intros z Hz; unfold avoid2, avoid1; apply in_app_iff; right; right; exact Hz).
    destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt init_reg avoid2 post_al
                post_al' init_end_reg avoid3 Erw_post Hinc_av2 Hinit_nin0)
      as [Hav3 Hinit_er_nin0].
    assert (Hinc_av3 : incl avoid0 avoid3) by (eapply incl_tran; eassumption).
    assert (Hlen_pr : List.length (blks c) = List.length phi_regs)
      by (symmetry; apply fresh_names_length).
    assert (Hphis_nin0 : forall r, In r (List.map snd bk_phis) -> ~ In r avoid0).
    { unfold bk_phis; rewrite (combine_snd_eq _ _ Hlen_pr).
      intros r Hr Hin0; eapply (fresh_names_disjoint "m2r_phi" _ avoid1 r Hr); right; exact Hin0. }
    destruct (rewrite_non_entry_blocks_pass1_spec avoid0 (init c) p dt init_end_reg init_code'
                avoid3 bk_phis pass1_out avoid_out Epass1 Hinc_av3 Hinit_er_nin0 Hphis_nin0)
      as (Hbks_p1 & _ & _ & Hall_p1).
    unfold bk_phis in Hbks_p1; rewrite (combine_fst_eq _ _ Hlen_pr) in Hbks_p1.
    set (end_map := List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out).
    assert (Hnd_end_map : NoDup (List.map fst end_map)).
    { unfold end_map; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks. }
    pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) pass1_out Hbks_p1)
      as [Hfb_none Hfb_some]; cbv zeta in Hfb_none, Hfb_some; fold end_map in Hfb_some.
    right.
    intros ctx1 ctx2 cc args U0 σ1_in σ2_in [sf_caller fstk_caller] Hpu0 Heq_in.
    unfold denote_function; cbn [df_prototype df_args df_instrs]; fold fargs c c'.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    set (fname := show_raw_id (dc_name (df_prototype df))).
    set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
    pose proof (stage1_equal_to_mem_inv U0 P0 σ1_in σ2_in Hpu0 Heq_in) as Hinv0.
    eapply refine_cfg_model_bind.
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
      eapply refine_cfg_model_bind.
      + exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                 ("Argument of " ++ fname ++ " violates noundef.")%string
                 args U0 P0 [] σ1_in σ2_in ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv0).
      + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
        eapply refine_cfg_model_bind.
        * exact (push_call_frame_stage1_sim ctx1 ctx2 df
                   {| df_prototype := df_prototype df; df_args := fargs; df_instrs := c' |}
                   args1 U0 P0 [] σ1_in σ2_in sf_caller sf_caller fstk_caller fstk_caller g0
                   Logic.eq_refl Hinv0).
        * intros U_pf s1_pf varg1 s2_pf varg2 _
            (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
          fold fs0 in Htf_pf.
          set (sf0 := {| stack_vars := init_local_env bs; stack_exc := None; stack_loc := Some ""%string |}).
          set (fstk := sf_caller :: fstk_caller).
          assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
            by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
          assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
            by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                args1 bs vs Ecomb Hsub_safe))).
          set (ExitRel :=
                 fun U_e (s1_e s2_e : FusedS) =>
                   incl (pr_va :: U0) U_e /\
                   (exists P_e σ1_e σ2_e sf1_e sf2_e,
                      s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                      s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                      ((stage1_mem_inv U_e P_e [] σ1_e σ2_e /\
                        top_frame_unprom_from fs0 [] (state_memory_stack σ2_e)) \/
                       (exists gs_e,
                          stage1_mem_inv U_e P_e (gs_e :: []) σ1_e σ2_e /\
                          top_frame_prom_from fs0 gs_e [] (state_memory_stack σ2_e))))).
          set (RExc_s1 := fun U_e s1_e s2_e (ex1 ex2 : @exc (@ParamsV IP IPT)) => ex1 = ex2 /\ ExitRel U_e s1_e s2_e).
          set (RA_s1   := fun U_e s1_e s2_e (v1 v2 : @dvalue (@ParamsV IP IPT)) => v1 = v2 /\ ExitRel U_e s1_e s2_e).
          eapply refine_cfg_model_bind with (RA := exc_post RExc_s1 RA_s1).
          -- change (interp_cfg_model ctx1 (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                       (σ1_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx1 (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                       (σ1_pf, ((sf0, fstk), g0))).
             change (interp_cfg_model ctx2 (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                       (σ2_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx2 (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                       (σ2_pf, ((sf0, fstk), g0))).
             unfold denote_cfg_map; rewrite Hc'_eq; cbn [init blks].
             eapply refine_cfg_exc_bind with
               (RA := fun U_e s1_e s2_e (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) =>
                        r1 = r2 /\ ExitRel U_e s1_e s2_e).
             ++ unfold denote_ocfg_map.
                eapply refine_prov_obs_eq;
                  [symmetry; apply interp_cfg_exc_unfold_iter
                  | symmetry; apply interp_cfg_exc_unfold_iter |].
                destruct (Hfb_some (init c) b_init Efind_init)
                  as (phi_init & cd_init & end_init & Hin_p1_init & Efind_init').
                pose proof (Hall_p1 b_init phi_init cd_init end_init Hin_p1_init)
                  as (_ & _ & Hinit_p1_spec).
                rewrite Hid_init, raw_id_eqb_refl in Hinit_p1_spec, Efind_init'.
                destruct Hinit_p1_spec as [-> ->].
                assert (Hlk_end_init : lookup_end_reg end_map (init c) init_reg = init_end_reg).
                { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                  unfold end_map; rewrite <- Hid_init.
                  exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_init). }
                rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
                rewrite ScopeTheory.ocfg_map_find_block, Efind_init'.
                unfold denote_block; cbn [blk_phis blk_code blk_term]; rewrite Ephis_init.
                eapply PassCommon.refine_prov_bind with
                  (RPre := exc_post RExc_s1
                             (fun U_s s1_s s2_s
                                (lr1 lr2 : (block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) =>
                                exists P_b1 gs_b1 σ1_b1 σ2_b1 sf1_b1 sf2_b1,
                                  incl (pr_va :: U0) U_s /\
                                  lr1 = lr2 /\
                                  s1_s = (σ1_b1, ((sf1_b1, fstk), g0)) /\
                                  s2_s = (σ2_b1, ((sf2_b1, fstk), g0)) /\
                                  gs_dt gs_b1 = dt /\
                                  Maps.lookup p (stack_vars sf1_b1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs_b1))) /\
                                  Maps.lookup init_end_reg (stack_vars sf2_b1) = Some (DVALUE_Base (gs_db gs_b1)) /\
                                  stage1_mem_inv U_s P_b1 (gs_b1 :: []) σ1_b1 σ2_b1 /\
                                  top_frame_prom_from fs0 gs_b1 [] (state_memory_stack σ2_b1) /\
                                  genv_safe P_b1 g0 /\
                                  safe_locals_env P_b1 safe_no_p (stack_vars sf2_b1) /\
                                  (forall x, In x avoid0 -> x <> p ->
                                     Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                                  match lr1 with
                                  | inl j => fst j = init c /\ In (snd j) (m2r_block_succs b_init) /\ snd j <> init c
                                  | inr _ => True
                                  end)).
                ** eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                         (eq_itree_clo_bind _ _ _ _ Logic.eq
                                            (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                               (fun _ _ <- => Logic.eq_refl)) (fun _ _ <- => Logic.eq_refl)))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                          (eq_itree_clo_bind _ _ _ _ Logic.eq
                                             (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                                (fun _ _ <- => Logic.eq_refl)) (fun _ _ <- => Logic.eq_refl))) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_ret_l _ _))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_ret_l _ _)) |].
                   rewrite Hsplit_init; unfold init_code'.
                   eapply refine_cfg_exc_bind.
                   --- eapply refine_prov_obs_eq;
                         [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                             (eq_itree_clo_bind _ _ _ _ Logic.eq
                                                (denote_code_app_eq pre_al _ (Some varg1))
                                                (fun _ _ <- => Logic.eq_refl)))
                         | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                              (eq_itree_clo_bind _ _ _ _ Logic.eq
                                                 (denote_code_app_eq pre_al _ (Some varg1))
                                                 (fun _ _ <- => Logic.eq_refl))) |].
                       eapply refine_cfg_exc_bind.
                       +++ assert (Hsplit_pre :
                                     blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                             by exact Hsplit_init.
                           exact (stage1_no_call_code_exc_sim ctx1 ctx2 RExc_s1
                                    (fun s => top_frame_unprom_from fs0 [] (state_memory_stack s))
                                    fargs (blks c) b_init [] pre_al
                                    ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                                    safe_no_p p (Some varg1) (Some varg1)
                                    (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf sf0 sf0 fstk fstk g0
                                    Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
                                    (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs) HT)
                                    (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                                       top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs)
                                         (top_frame_unprom_add_ptrs fs0 [] ptrs _ HT Hdisj))
                                    Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
                       +++ intros U_pre s1_pre _ s2_pre _ _
                             (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
                              HincU_pre & HincP_pre & _ & _ & -> & -> &
                              Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & _ & Heq_sf_pre).
                           pose proof (Heq_sf_pre Logic.eq_refl) as ->.
                           assert (Econs_l :
                                     @denote_code (@ParamsV IP IPT)
                                       ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al) (Some varg1) ≅
                                     ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                       (fun _ => denote_code post_al (Some varg1)))
                             by reflexivity.
                           assert (Econs_r :
                                     @denote_code (@ParamsV IP IPT)
                                       ((IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al') (Some varg1) ≅
                                     ITree.bind
                                       (ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                          (fun _ => denote_instr init_op (Some varg1)))
                                       (fun _ => denote_code post_al' (Some varg1))).
                           { unfold denote_code; cbn [loop_monad]; symmetry; apply Eqit.bind_bind. }
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                                 (eq_itree_clo_bind _ _ _ _ Logic.eq Econs_l (fun _ _ <- => Logic.eq_refl)))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                                  (eq_itree_clo_bind _ _ _ _ Logic.eq Econs_r (fun _ _ <- => Logic.eq_refl))) |].
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                           eapply refine_cfg_exc_bind.
                           *** exact (stage1_prom_alloca_init_exc_sim ctx1 ctx2 RExc_s1
                                        p init_reg dt anns_al md_al (Some varg1) (Some varg1)
                                        fs0 U_pre P_pre [] σ1_pre σ2_pre sf2_pre sf2_pre fstk fstk g0
                                        Hsc Hanns_al Hinv_pre Htf_pre).
                           *** intros U_al s1_al _ s2_al _ _
                                 (gs0 & σ1_al & σ2_al & _ & -> & _ & _ & Hdt0 & Hdb0 &
                                  -> & -> & Hinv_al & Htf_al).
                               assert (HincU_al : incl (pr_va :: U0) (gs_pr gs0 :: U_pre))
                                 by (intros x Hx; right; exact (HincU_pre x Hx)).
                               assert (Hlk_p_al :
                                         Maps.lookup p (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                         Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))))
                                 by apply lookup_add_eq.
                               assert (Hlk_init_al :
                                         Maps.lookup init_reg
                                           (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre))) =
                                         Some (DVALUE_Base (gs_db gs0))).
                               { rewrite Hdb0; apply lookup_add_eq. }
                               assert (Hsafe_al :
                                         safe_locals_env P_pre safe_no_p
                                           (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)))).
                               { apply safe_locals_env_add_other;
                                   [intros Hs; exact (Hinit_nin0 (Hsafe_av0 _ Hs)) |].
                                 apply safe_locals_env_add_other; [exact Hp_nin_safe | exact Hsafe_pre]. }
                               assert (Hvars_al :
                                         forall x, In x avoid0 -> x <> p ->
                                           Maps.lookup x (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                           Maps.lookup x (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                                            (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)))).
                               { intros x Hx _; rewrite (lookup_add_neq x init_reg)
                                   by (intros ->; exact (Hinit_nin0 Hx)); reflexivity. }
                               assert (Hsplit_post :
                                         blk_code b_init = (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) ++ post_al ++ [])
                                 by (rewrite <- app_assoc, app_nil_r; exact Hsplit_init).
                               assert (Huses_post : forall im0 x, In im0 post_al -> In x (m2r_code_entry_uses im0) -> In x avoid0).
                               { intros im0 x Him0 Hx; apply (Hblk_uses_av0 b_init x Hin_init).
                                 eapply m2r_code_entry_uses_in_block; [| exact Hx].
                                 rewrite Hsplit_init; apply in_app_iff; right; right; exact Him0. }
                               assert (Hdefs_post : forall im0 x, In im0 post_al -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
                               { intros im0 x Him0 Hx; apply (Hblk_defs_av0 b_init x Hin_init).
                                 unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
                                 rewrite Hsplit_init; apply in_flat_map; exists im0; split;
                                   [apply in_app_iff; right; right; exact Him0
                                   | destruct im0 as [[? ?] ?]; exact Hx]. }
                               eapply refine_cfg_exc_bind.
                               ---- exact (rewrite_code_for_slot_no_call_exc_sim ctx1 ctx2 RExc_s1
                                             avoid0 fargs (blks c) b_init
                                             (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                                             safe_no_p p dt init_reg avoid2 post_al' init_end_reg avoid3
                                             (Some varg1) (Some varg1) fs0 (gs_pr gs0 :: U_pre) P_pre gs0 []
                                             σ1_al σ2_al _ _ fstk fstk g0
                                             Hnd_bks Hin_init Hsplit_post Hsub_safe Hsafe_av0
                                             Huses_post Hdefs_post Hp_nd_post Hpost_chk Erw_post
                                             Hinc_av2 Hinit_nin0 Hsc Hdt0 Hlk_p_al Hlk_init_al
                                             Hinv_al Htf_al Hgenv_pre Hsafe_al Hvars_al).
                               ---- intros U_post s1_post _ s2_post _ _
                                      (P_post & gs_post & σ1_post & σ2_post & sf1_post & sf2_post &
                                       HincU_post & _ & _ & _ & Hdt_post & Hlk_p_post & Hlk_er_post &
                                       -> & -> & Hinv_post & Htf_post & Hgenv_post & Hsafe_post & Hvars_post).
                                    assert (HincU_p : incl (pr_va :: U0) U_post)
                                      by (eapply incl_tran; [exact HincU_al | exact HincU_post]).
                                    destruct (blk_term b_init) as [[iid_tm tm_init] md_tm] eqn:Etm_init.
                                    cbn [fst snd] in Hni_init.
                                    assert (Htm_vars : forall x,
                                              In x (full_term_uses tm_init) ->
                                              Maps.lookup x (stack_vars sf1_post) = Maps.lookup x (stack_vars sf2_post)).
                                    { intros x Hx; apply Hvars_post.
                                      - apply (Hblk_uses_av0 b_init x Hin_init), m2r_term_entry_uses_in_block.
                                        rewrite Etm_init; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                                      - intros ->; apply Hterm_p; rewrite Etm_init;
                                          cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                    eapply refine_prov_weaken.
                                    ++++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s1
                                                  iid_tm iid_tm tm_init md_tm md_tm
                                                  U_post σ1_post σ2_post sf1_post sf2_post fstk fstk g0
                                                  Hni_init Htm_vars).
                                         intros ex; refine (conj Logic.eq_refl (conj HincU_p _)).
                                         exists P_post, σ1_post, σ2_post, sf1_post, sf2_post;
                                           split; [reflexivity | split; [reflexivity | right; exists gs_post; split; assumption]].
                                    ++++ intros U_t [s1_t res1_t] [s2_t res2_t].
                                         destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                           try (intros H; exact H).
                                         intros (-> & -> & -> & <- & Hsucc).
                                         exists P_post, gs_post, σ1_post, σ2_post, sf1_post, sf2_post.
                                         exact (conj HincU_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                  (conj Logic.eq_refl (conj Hdt_post (conj Hlk_p_post
                                                    (conj Hlk_er_post (conj Hinv_post (conj Htf_post
                                                      (conj Hgenv_post (conj Hsafe_post (conj Hvars_post Hsucc)))))))))))).
                   --- intros U_b1 s1_b1 bd1 s2_b1 bd2 _
                         (P_b1 & gs_b1 & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
                          HincU_b1 & <- & -> & -> & Hdt_b1 & Hlk_p_b1 & Hlk_er_b1 &
                          Hinv_b1 & Htf_b1 & Hgenv_b1 & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
                       destruct bd1 as [bid_next | dv_ret].
                       +++ assert (Hsucc_init : In bid_next (m2r_block_succs b_init)).
                           { unfold m2r_block_succs; destruct (blk_term b_init) as [[? ?] ?]; exact Hsucc_b1. }
                           assert (Hne_init : bid_next <> init c).
                           { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
                             unfold m2r_all_succs; apply in_flat_map; exists b_init; split; assumption. }
                           apply refine_cfg_exc_ret.
                           exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hdt_b1 (conj Hlk_p_b1
                                      (conj Hlk_er_b1 (conj Hinv_b1 (conj Htf_b1
                                        (conj Hgenv_b1 (conj Hsafe_b1 (conj Hvars_b1
                                          (conj Logic.eq_refl (conj Hsucc_init Hne_init)))))))))))))).
                       +++ apply refine_cfg_exc_ret.
                           exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hdt_b1 (conj Hlk_p_b1
                                      (conj Hlk_er_b1 (conj Hinv_b1 (conj Htf_b1
                                        (conj Hgenv_b1 (conj Hsafe_b1 (conj Hvars_b1 I)))))))))))).
                ** intros U_step [s1_step res1_s] [s2_step res2_s] _.
                   destruct res1_s as [ex1 | [j1 | r1]], res2_s as [ex2 | [j2 | r2]]; cbn [exc_post];
                     try contradiction.
                   --- intros Hex; apply refine_prov_ret; exact Hex.
                   --- intros (P_s & gs_s & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & <- & -> & -> & Hdt_s & Hlk_p_s & Hlk_er_s &
                               Hinv_s & Htf_s & Hgenv_s & Hsafe_s & Hvars_s &
                               Hjid_s & Hsucc_s & Hne_s).
                       apply refine_prov_tau_both.
                       set (RI_loop :=
                              fun U_l (s1_l s2_l : FusedS) (i1 i2 : block_id * block_id) =>
                                i1 = i2 /\
                                snd i2 <> init c /\
                                incl (pr_va :: U0) U_l /\
                                (exists b_pred,
                                   In b_pred (blks c) /\
                                   blk_id b_pred = fst i2 /\
                                   In (snd i2) (m2r_block_succs b_pred)) /\
                                exists P_l gs_l σ1_l σ2_l sf1_l sf2_l,
                                  gs_dt gs_l = dt /\
                                  Maps.lookup p (stack_vars sf1_l) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs_l))) /\
                                  Maps.lookup (lookup_end_reg end_map (fst i2) init_reg) (stack_vars sf2_l) =
                                    Some (DVALUE_Base (gs_db gs_l)) /\
                                  s1_l = (σ1_l, ((sf1_l, fstk), g0)) /\
                                  s2_l = (σ2_l, ((sf2_l, fstk), g0)) /\
                                  stage1_mem_inv U_l P_l (gs_l :: []) σ1_l σ2_l /\
                                  top_frame_prom_from fs0 gs_l [] (state_memory_stack σ2_l) /\
                                  genv_safe P_l g0 /\
                                  safe_locals_env P_l safe_no_p (stack_vars sf2_l) /\
                                  (forall x, In x avoid0 -> x <> p ->
                                     Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l))).
                       eapply (refine_cfg_exc_iter ctx1 ctx2 RI_loop RExc_s1 _ _ _ U_step).
                       +++ intros U_l s1_l s2_l [bf1 bs1] [bf2 bs2] _
                             (Heq_ij & Hne_bs & HincU_l & (b_pred & Hin_pred & Hid_pred & Hsucc_pred) &
                              P_l & gs_l & σ1_l & σ2_l & sf1_l & sf2_l &
                              Hdt_l & Hlk_p_l & Hlk_end_l & -> & -> &
                              Hinv_l & Htf_l & Hgenv_l & Hsafe_l & Hvars_l).
                           inversion Heq_ij; subst bf1 bs1; clear Heq_ij; cbn [fst snd] in *.
                           rewrite !ScopeTheory.ocfg_map_find_block.
                           destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur.
                           *** destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur)
                                 as [Hin_cur Hid_cur].
                               destruct (Hfb_some bs2 bk_cur Efind_cur)
                                 as (phi_r & cd_cur' & end_r & Hin_p1_cur & Efind_cur').
                               rewrite Efind_cur'.
                               pose proof (Hall_p1 bk_cur phi_r cd_cur' end_r Hin_p1_cur)
                                 as (Hphi_nin0 & Hend_nin0 & Hcur_p1_spec).
                               destruct (raw_id_eqb_spec (blk_id bk_cur) (init c)) as [Hbad | Hne_cur_id];
                                 [exfalso; congruence |].
                               destruct Hcur_p1_spec as (av_in & av_out & Hinc_avin & Erw_cur).
                               pose proof Ebks_chk as Hbk_cur_chk.
                               rewrite forallb_forall in Hbk_cur_chk.
                               specialize (Hbk_cur_chk bk_cur Hin_cur).
                               destruct (raw_id_eqb_spec (blk_id bk_cur) (init c)) as [Hbad | _];
                                 [exfalso; congruence |].
                               unfold check_block_non_entry_for_slot in Hbk_cur_chk.
                               rewrite !andb_true_iff, !negb_true_iff in Hbk_cur_chk.
                               destruct Hbk_cur_chk as (((Hphi_np & Hcd_cur) & Htm_np) & Hni_cur).
                               apply in_raw_ids_false in Hphi_np; apply in_raw_ids_false in Htm_np.
                               pose proof (Hp_nd_other bk_cur Hin_cur (fun Heq => Hne_cur_id (eq_trans Heq Hid_init)))
                                 as Hp_nd_bk_cur.
                               set (preds_cur := List.filter (fun b_p => in_raw_ids (blk_id bk_cur) (m2r_block_succs b_p)) (blks c)).
                               set (inc_cur := List.map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg)))) preds_cur).
                               assert (Hassoc_cur :
                                         assoc bf2 inc_cur =
                                         Some (EXP_Ident (ID_Local (lookup_end_reg end_map bf2 init_reg)))).
                               { apply m2r_assoc_nodup.
                                 - unfold inc_cur; rewrite map_map; cbn [fst].
                                   exact (m2r_nodup_map_filter blk_id _ (blks c) Hnd_bks).
                                 - unfold inc_cur; rewrite <- Hid_pred at 1 2.
                                   apply (in_map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg))))).
                                   unfold preds_cur; apply filter_In; split; [exact Hin_pred |].
                                   rewrite Hid_cur; apply in_raw_ids_spec, Hsucc_pred. }
                               assert (Hphi_vars :
                                         forall x, In x (flat_map m2r_phi_entry_uses (blk_phis bk_cur)) ->
                                           Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l)).
                               { intros x Hx; apply Hvars_l;
                                   [apply (Hblk_uses_av0 bk_cur x Hin_cur);
                                    apply in_flat_map in Hx as (pe & Hpe & Hx_pe);
                                    exact (m2r_phi_entry_uses_in_block bk_cur pe x Hpe Hx_pe)
                                   | intros ->; exact (Hphi_np Hx)]. }
                               unfold denote_block; cbn [blk_phis blk_code blk_term]; fold preds_cur inc_cur.
                               eapply refine_cfg_exc_bind.
                               ---- eapply refine_cfg_exc_bind.
                                    ++++ exact (denote_phis_stage1_prom_sim ctx1 ctx2 RExc_s1
                                                  bf2 phi_r (lookup_end_reg end_map bf2 init_reg)
                                                  dt inc_cur (blk_phis bk_cur) (DVALUE_Base (gs_db gs_l))
                                                  U_l σ1_l σ2_l sf1_l sf2_l fstk fstk g0
                                                  Hassoc_cur Hlk_end_l Hphi_vars).
                                    ++++ intros U_ph s1_ph _ s2_ph _ _
                                           (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
                                         assert (Hp_nin_dvs : ~ In p (List.map fst dvs)).
                                         { rewrite Hfst_dvs; intros Hp_in; apply Hp_nd_bk_cur.
                                           unfold full_block_defs; apply in_app_iff; left; exact Hp_in. }
                                         assert (Hphi_nin_dvs : ~ In phi_r (List.map fst dvs)).
                                         { rewrite Hfst_dvs; intros Hpr_in; apply Hphi_nin0.
                                           apply (Hblk_defs_av0 bk_cur phi_r Hin_cur).
                                           unfold full_block_defs; apply in_app_iff; left; exact Hpr_in. }
                                         assert (Hlk_p_ph :
                                                   Maps.lookup p (write_phi_dvs dvs (stack_vars sf1_l)) =
                                                   Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs_l)))).
                                         { rewrite (write_phi_dvs_lookup_not_in dvs _ p Hp_nin_dvs); exact Hlk_p_l. }
                                         assert (Hlk_phi_ph :
                                                   Maps.lookup phi_r
                                                     (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l)) =
                                                   Some (DVALUE_Base (gs_db gs_l))).
                                         { cbn [write_phi_dvs];
                                             rewrite (write_phi_dvs_lookup_not_in dvs _ phi_r Hphi_nin_dvs);
                                             apply lookup_add_eq. }
                                         assert (Hsafe_ph :
                                                   safe_locals_env P_l safe_no_p
                                                     (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
                                         { apply write_phi_dvs_safe_locals; [| exact Hsafe_l].
                                           intros q Hq [Heq_q | Hin_dvs].
                                           - subst q; exact (Hphi_nin0 (Hsafe_av0 _ Hq)).
                                           - rewrite Hfst_dvs in Hin_dvs.
                                             apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
                                             exact (unique_alloca_not_phi_def fargs (blks c) q Hnd_bks
                                                      (Hsub_safe q Hq) bk_cur q ph_q md_q Hin_cur Hpe_in Logic.eq_refl). }
                                         assert (Hvars_ph :
                                                   forall x, In x avoid0 -> x <> p ->
                                                     Maps.lookup x (write_phi_dvs dvs (stack_vars sf1_l)) =
                                                     Maps.lookup x (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
                                         { intros x Hx Hne; cbn [write_phi_dvs]; apply write_phi_dvs_lookup_agree.
                                           rewrite (lookup_add_neq x phi_r) by (intros ->; exact (Hphi_nin0 Hx)).
                                           exact (Hvars_l x Hx Hne). }
                                         assert (Hsplit_cur : blk_code bk_cur = [] ++ blk_code bk_cur ++ [])
                                           by (rewrite app_nil_r; reflexivity).
                                         assert (Huses_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (m2r_code_entry_uses im0) -> In x avoid0)
                                           by (intros im0 x Him0 Hx; apply (Hblk_uses_av0 bk_cur x Hin_cur);
                                               eapply m2r_code_entry_uses_in_block; eassumption).
                                         assert (Hdefs_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
                                         { intros im0 x Him0 Hx; apply (Hblk_defs_av0 bk_cur x Hin_cur).
                                           unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
                                           apply in_flat_map; exists im0; split; [exact Him0 | destruct im0 as [[? ?] ?]; exact Hx]. }
                                         assert (Hp_nd_cd_cur : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk_cur))).
                                         { intros Hp_in; apply Hp_nd_bk_cur; unfold full_block_defs;
                                             apply in_app_iff; right; apply in_app_iff; left; exact Hp_in. }
                                         eapply refine_cfg_exc_bind.
                                         **** exact (rewrite_code_for_slot_no_call_exc_sim ctx1 ctx2 RExc_s1
                                                       avoid0 fargs (blks c) bk_cur [] (blk_code bk_cur) []
                                                       safe_no_p p dt phi_r av_in cd_cur' end_r av_out
                                                       (Some varg1) (Some varg1) fs0 U_l P_l gs_l []
                                                       σ1_l σ2_l _ _ fstk fstk g0
                                                       Hnd_bks Hin_cur Hsplit_cur Hsub_safe Hsafe_av0
                                                       Huses_cur Hdefs_cur Hp_nd_cd_cur Hcd_cur Erw_cur
                                                       Hinc_avin Hphi_nin0 Hsc Hdt_l Hlk_p_ph Hlk_phi_ph
                                                       Hinv_l Htf_l Hgenv_l Hsafe_ph Hvars_ph).
                                         **** intros U_cd s1_cd _ s2_cd _ _
                                                (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                                 HincU_cd & _ & _ & _ & Hdt_cd & Hlk_p_cd & Hlk_er_cd &
                                                 -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd).
                                              assert (HincU_c : incl (pr_va :: U0) U_cd)
                                                by (eapply incl_tran; [exact HincU_l | exact HincU_cd]).
                                              assert (Hlk_end_cur : lookup_end_reg end_map bs2 init_reg = end_r).
                                              { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                                                unfold end_map; rewrite <- Hid_cur.
                                                exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_cur). }
                                              destruct (blk_term bk_cur) as [[iid_tc tm_cur] md_tc] eqn:Etm_cur.
                                              cbn [fst snd] in Hni_cur.
                                              assert (Htm_vars :
                                                        forall x, In x (full_term_uses tm_cur) ->
                                                          Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)).
                                              { intros x Hx; apply Hvars_cd.
                                                - apply (Hblk_uses_av0 bk_cur x Hin_cur), m2r_term_entry_uses_in_block.
                                                  rewrite Etm_cur; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                                                - intros ->; apply Htm_np; rewrite Etm_cur;
                                                    cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                              eapply refine_prov_weaken.
                                              ----- apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s1
                                                             iid_tc iid_tc tm_cur md_tc md_tc
                                                             U_cd σ1_cd σ2_cd sf1_cd sf2_cd fstk fstk g0
                                                             Hni_cur Htm_vars).
                                                    intros ex; refine (conj Logic.eq_refl (conj HincU_c _)).
                                                    exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                                      split; [reflexivity | split; [reflexivity | right; exists gs_cd; split; assumption]].
                                              ----- intros U_t [s1_t res1_t] [s2_t res2_t].
                                                    destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                                      try (intros H; exact H).
                                                    intros (-> & -> & -> & <- & Hsucc_cur).
                                                    exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
                                                    exact (conj HincU_c (conj Logic.eq_refl (conj Logic.eq_refl
                                                             (conj Logic.eq_refl (conj Hdt_cd (conj Hlk_p_cd
                                                               (conj Hlk_end_cur (conj Hlk_er_cd (conj Hinv_cd
                                                                 (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd
                                                                   (conj Hvars_cd Hsucc_cur))))))))))))).
                               ---- intros U_bd s1_bd bd1 s2_bd bd2 _
                                      (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                       HincU_c & <- & -> & -> & Hdt_cd & Hlk_p_cd & Hlk_end_cur &
                                       Hlk_er_cd & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
                                    destruct bd1 as [bid_tgt | dv_cur].
                                    ++++ apply refine_cfg_exc_ret.
                                         assert (Hsucc_bk_cur : In bid_tgt (m2r_block_succs bk_cur)).
                                         { unfold m2r_block_succs; destruct (blk_term bk_cur) as [[? ?] ?]; exact Hsucc_cur. }
                                         assert (Hne_tgt : bid_tgt <> init c).
                                         { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
                                           unfold m2r_all_succs; apply in_flat_map; exists bk_cur; split; assumption. }
                                         refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_c (conj _ _)))).
                                         * exists bk_cur; exact (conj Hin_cur (conj Hid_cur Hsucc_bk_cur)).
                                         * exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd; cbn [fst].
                                           rewrite Hlk_end_cur.
                                           exact (conj Hdt_cd (conj Hlk_p_cd (conj Hlk_er_cd
                                                    (conj Logic.eq_refl (conj Logic.eq_refl
                                                      (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd
                                                        (conj Hsafe_cd Hvars_cd))))))))).
                                    ++++ apply refine_cfg_exc_ret.
                                         refine (conj Logic.eq_refl (conj HincU_c _)).
                                         exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                           split; [reflexivity | split; [reflexivity | right; exists gs_cd; split; assumption]].
                           *** rewrite (Hfb_none bs2 Efind_cur).
                               apply refine_cfg_exc_ret.
                               refine (conj Logic.eq_refl (conj HincU_l _)).
                               exists P_l, σ1_l, σ2_l, sf1_l, sf2_l;
                                 split; [reflexivity | split; [reflexivity | right; exists gs_l; split; assumption]].
                       +++ refine (conj Logic.eq_refl (conj Hne_s (conj HincU_s (conj _ _)))).
                           *** exists b_init;
                                 exact (conj Hin_init (conj (eq_trans Hid_init (eq_sym Hjid_s)) Hsucc_s)).
                           *** exists P_s, gs_s, σ1_s, σ2_s, sf1_s, sf2_s.
                               rewrite Hjid_s, Hlk_end_init.
                               exact (conj Hdt_s (conj Hlk_p_s (conj Hlk_er_s
                                        (conj Logic.eq_refl (conj Logic.eq_refl
                                          (conj Hinv_s (conj Htf_s (conj Hgenv_s
                                            (conj Hsafe_s Hvars_s))))))))).
                   --- intros (P_s & gs_s & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & <- & -> & -> & _ & _ & _ & Hinv_s & Htf_s & _).
                       apply refine_prov_ret.
                       refine (conj Logic.eq_refl (conj HincU_s _)).
                       exists P_s, σ1_s, σ2_s, sf1_s, sf2_s;
                         split; [reflexivity | split; [reflexivity | right; exists gs_s; split; assumption]].
             ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ (<- & Hexit_ocfg).
                destruct r_ocfg1 as [bid_miss | uv_ret].
                ** apply refine_cfg_exc_raise_both.
                ** apply refine_cfg_exc_ret; exact (conj Logic.eq_refl Hexit_ocfg).
          -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
             assert (Hrv_unif : rv1 = rv2 /\ ExitRel U_rv s1_rv s2_rv).
             { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                 try contradiction; exact Hrv_post. }
             clear Hrv_post; destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e & -> & -> & Hcase_e)].
             assert (Hpop :
                       refine_prov
                         (fun U' '(s1', r1) '(s2', r2) =>
                            exists σ1' σ2',
                              U' = U_rv /\ r1 = tt /\ r2 = tt /\
                              s1' = (σ1', ((sf_caller, fstk_caller), g0)) /\
                              s2' = (σ2', ((sf_caller, fstk_caller), g0)) /\
                              stage1_mem_inv U_rv P_e [] σ1' σ2' /\
                              Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
                         U_rv
                         (interp_cfg_model ctx1 pop_call_frame (σ1_e, ((sf1_e, sf_caller :: fstk_caller), g0)))
                         (interp_cfg_model ctx2 pop_call_frame (σ2_e, ((sf2_e, sf_caller :: fstk_caller), g0)))).
             { destruct Hcase_e as [[Hinv_e Htf_e] | (gs_e & Hinv_e & Htf_e)].
               - exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e []
                          σ1_e σ2_e sf1_e sf_caller sf2_e sf_caller fstk_caller fstk_caller g0 Hinv_e Htf_e).
               - exact (pop_call_frame_stage1_prom_sim ctx1 ctx2 fs0 U_rv P_e gs_e []
                          σ1_e σ2_e sf1_e sf_caller sf2_e sf_caller fstk_caller fstk_caller g0 Hinv_e Htf_e). }
             eapply refine_cfg_model_bind; [exact Hpop |].
             intros U_pop s1_pop _ s2_pop _ _ (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & _).
             pose proof (stage1_mem_nil_is_equal U_rv P_e σ1_pop σ2_pop Hinv_pop) as Heq_pop.
             eapply refine_prov_weaken.
             ++ exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                         (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                         U_rv P_e [] σ1_pop σ2_pop
                         ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv_pop).
             ++ intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                         (conj Heq_pop (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.


  (** ** 3P. Whole-Module Lifter & Fixed-Guard CPS Combinators *)

  Lemma refine_mcfg_raiseLLVM_both {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (ex : @exc (@ParamsV IP IPT)) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_mcfg_model (raiseLLVM ex) s1)
      (interp_mcfg_model (raiseLLVM ex) s2).
  Proof using.
    unfold raiseLLVM, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind | symmetry; apply interp_mcfg_model_bind |].
    eapply refine_prov_obs_eq;
      [symmetry; rewrite (interp_mcfg_model_non_intr _ s1 Logic.eq_refl); reflexivity
      | symmetry; rewrite (interp_mcfg_model_non_intr _ s2 Logic.eq_refl); reflexivity |].
    cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
      | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
    pstep; apply RP_Step; cbn; right; right; split; [apply EqE_bot_refl | intros [] [] _].
  Qed.

  Lemma library_functions_leaf_rel
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (decls : list (declaration dtyp)) :
    Forall (fun lib => leaf_ctx_fn_rel P0 g0 (snd lib) (snd lib))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    apply Forall_forall; intros [fnm fden] Hin.
    unfold library_functions, _LIBRARIES in Hin.
    apply filter_In in Hin as [[Heq | [Heq | []]] _]; inversion Heq; subst fnm fden; cbn [snd].
    - left; split; [reflexivity | exact (@ev_ok_puts_denotation)].
    - left; split; [reflexivity | exact (@ev_ok_putchar_denotation)].
  Qed.

  Lemma library_functions_no_puts_only_putchar
    (decls : list (declaration dtyp)) :
    negb (in_raw_ids (Name "puts"%string) (List.map dc_name decls)) = true ->
    Forall (fun lib => snd lib = @putchar_denotation (@ParamsV IP IPT))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    intros Hno; apply negb_true_iff, in_raw_ids_false in Hno.
    apply Forall_forall; intros [fnm fden] Hin.
    unfold library_functions, _LIBRARIES in Hin.
    apply filter_In in Hin as [Hin Hex].
    destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst fnm fden; [| reflexivity].
    exfalso; apply existsb_exists in Hex as (s & Hs & Heq_s).
    destruct (RawIDOrd.eq_dec s (Name "puts"%string)) as [-> | _];
      [exact (Hno Hs) | discriminate Heq_s].
  Qed.

  Lemma module_defs_refines_gen
    (Rfn : list N -> @global_env (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall2
                 (fun d1 d2 =>
                    dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                    Rfn P0 g0 (denote_function d1) (denote_function d2))
                 (m_definitions M1) (m_definitions M2))
    (Hlibs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall (fun lib => Rfn P0 g0 (snd lib) (snd lib))
                 (@library_functions (@ParamsV IP IPT) (m_declarations M1)))
    (Hmrec : forall P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls,
               (forall k, option_rel (Rfn P0 g0) (lookup k ctx1) (lookup k ctx2)) ->
               incl P0 U ->
               genv_safe P0 g0 ->
               mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
               refine_prov top_ans_post U
                 (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt CC_Ccc fv args)) (σ1, (ls, g0)))
                 (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt CC_Ccc fv args)) (σ2, (ls, g0)))) :
    prog_refines M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, denote_vellvm, init_fused_state.
    rewrite Hbg, Hdecls.
    set (ls0 := (Build_stack_frame Maps.empty None None, ([] : stack))).
    assert (Heq_init : mem_stack_equal (state_memory_stack initial_state)
                                       (state_memory_stack initial_state))
      by (repeat split; reflexivity).
    eapply refine_mcfg_model_bind.
    - exact (build_global_environment_safe_sim M1 U [] initial_state initial_state
               ls0 Maps.empty (fun _ H => match H with end) (genv_safe_empty []) Heq_init).
    - intros U1 [σ1_g rest1_g] _ [σ2_g rest2_g] _ _
        (P1 & g0 & _ & Hp1u1 & Hs1_g & Hs2_g & Hg0 & Heq_g).
      cbn [fst snd] in Hs1_g, Hs2_g, Heq_g; subst rest1_g rest2_g.
      eapply refine_mcfg_model_bind.
      + exact (map_monad_address_one_function_pair_sim (Rfn P1 g0)
                 (m_definitions M1) (m_definitions M2) U1 σ1_g σ2_g ls0 g0 (Hdefs P1 g0 Hg0)).
      + intros U2 s1_f defns1 s2_f defns2 _ (-> & -> & -> & Hdefns).
        eapply refine_mcfg_model_bind.
        * exact (map_monad_address_one_library_pair_sim (Rfn P1 g0)
                   (library_functions (m_declarations M1)) U1 σ1_g σ2_g ls0 g0 (Hlibs P1 g0 Hg0)).
        * intros U3 s1_l libs1 s2_l libs2 _ (-> & -> & -> & Hlibs_rel).
          eapply refine_mcfg_model_bind; [unfold ls0; apply refine_mcfg_gread_same_g |].
          intros U4 s1_e addr1 s2_e addr2 _ (-> & -> & -> & -> & _).
          eapply refine_mcfg_model_bind with (RA := top_ans_post).
          -- rewrite !denote_mcfg_eq_interp_mrec.
             exact (Hmrec P1 g0
                      (IntMaps.IP.of_list (defns1 ++ libs1))
                      (IntMaps.IP.of_list (defns2 ++ libs2))
                      ret_typ addr2 args U1 σ1_g σ2_g ls0
                      (of_list_lookup_pair (Rfn P1 g0) _ _ (Forall2_app Hdefns Hlibs_rel))
                      Hp1u1 Hg0 Heq_g).
          -- intros U5 s1_end rv1 s2_end rv2 _ Hrv; cbn [top_ans_post] in Hrv; subst rv2.
             destruct rv1 as [ex | v].
             ++ apply refine_mcfg_raiseLLVM_both.
             ++ eapply refine_prov_obs_eq;
                  [symmetry; apply interp_mcfg_model_ret
                  | symmetry; apply interp_mcfg_model_ret |].
                apply refine_prov_ret; reflexivity.
  Qed.

  Lemma leaf_module_defs_refines (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall2
                 (fun d1 d2 =>
                    dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                    leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
                 (m_definitions M1) (m_definitions M2)) :
    prog_refines M1 M2.
  Proof using.
    eapply (module_defs_refines_gen leaf_ctx_fn_rel M1 M2 Hbg Hdecls Hdefs).
    - intros P0 g0 _; apply library_functions_leaf_rel.
    - intros P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls Hctx Hpu _ Heq.
      eapply refine_prov_weaken;
        [exact (mrec_knot_leaf_call_sim P0 g0 ctx1 ctx2 Hctx
                  (Call dt CC_Ccc fv args) U σ1 σ2 ls Hpu Heq) |].
      intros U' [? r1] [? r2] (_ & _ & _ & _ & Hr); exact Hr.
  Qed.

  Definition s1_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) : Prop :=
    forall (k1 : A1 -> itree ProvBotE Ans) (k2 : A2 -> itree ProvBotE Ans),
      (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> m2r_paco r U' (k1 a1) (k2 a2)) ->
      m2r_paco r U (ITree.bind u1 k1) (ITree.bind u2 k2).

  Lemma refine_prov_to_s1_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    refine_prov RA U u1 u2 ->
    s1_cps r RA U u1 u2.
  Proof using.
    intros Href k1 k2 Hk.
    exact (refine_prov_to_cps r RA U u1 u2 Href r (fun _ _ _ H => H) k1 k2 Hk).
  Qed.

  Lemma s1_cps_obs_eq {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 u1' : itree ProvBotE A1) (u2 u2' : itree ProvBotE A2) :
    u1 ≅ u1' ->
    u2 ≅ u2' ->
    s1_cps r RA U u1 u2 ->
    s1_cps r RA U u1' u2'.
  Proof using.
    intros E1 E2 Hcps k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E1 | intros ? ? <-; reflexivity]
      | eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E2 | intros ? ? <-; reflexivity]
      | exact (Hcps k1 k2 Hk)].
  Qed.

  Lemma s1_cps_ret {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) :
    RA U a1 a2 ->
    s1_cps r RA U (Ret a1) (Ret a2).
  Proof using.
    intros Hra k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_ret_l
      | symmetry; apply Eqit.bind_ret_l
      | exact (Hk U a1 a2 (incl_refl U) Hra)].
  Qed.

  Lemma s1_cps_bind {A1 A2 B1 B2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (RB : list N -> B1 -> B2 -> Prop)
    (U : list N)
    (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2)
    (f1 : A1 -> itree ProvBotE B1) (f2 : A2 -> itree ProvBotE B2) :
    s1_cps r RA U u1 u2 ->
    (forall U1 a1 a2, incl U U1 -> RA U1 a1 a2 -> s1_cps r RB U1 (f1 a1) (f2 a2)) ->
    s1_cps r RB U (ITree.bind u1 f1) (ITree.bind u2 f2).
  Proof using.
    intros Hu Hf k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply Hu; intros U1 a1 a2 Hinc1 Ha.
    apply (Hf U1 a1 a2 Hinc1 Ha); intros U2 b1 b2 Hinc2 Hb.
    exact (Hk U2 b1 b2 (incl_tran Hinc1 Hinc2) Hb).
  Qed.

  Lemma s1_cps_weaken {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA RB : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    s1_cps r RA U u1 u2 ->
    (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> RB U' a1 a2) ->
    s1_cps r RB U u1 u2.
  Proof using.
    intros Hu Hw k1 k2 Hk.
    apply Hu; intros U' a1 a2 Hinc Ha.
    exact (Hk U' a1 a2 Hinc (Hw U' a1 a2 Hinc Ha)).
  Qed.

  Lemma s1_cps_to_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    s1_cps r top_ans_post U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros Hcps.
    eapply m2r_paco_obs_eq; [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply (Hcps (fun x => Ret x) (fun x => Ret x)).
    intros U' [s1 v1] [s2 v2] _ Heq.
    apply m2r_paco_fold, RP_Step; exact Heq.
  Qed.

  Lemma s1_cps_cfg_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    s1_cps r RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       s1_cps r RB U'
         (interp_cfg_model ctx1 (k1 a1) s1')
         (interp_cfg_model ctx2 (k2 a2) s2')) ->
    s1_cps r RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply s1_cps_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply s1_cps_bind; [exact Ht |].
    intros U' [s1' a1] [s2' a2] Hinc Ha; exact (Hk U' s1' a1 s2' a2 Hinc Ha).
  Qed.

  Lemma s1_cps_cfg_exc_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    s1_cps r (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1) (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       s1_cps r (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    s1_cps r (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply s1_cps_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply s1_cps_bind; [exact Ht |].
    intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] Hinc Hres; try contradiction.
    - apply s1_cps_ret; exact Hres.
    - exact (Hk U' s1' a1 s2' a2 Hinc Hres).
  Qed.

  (** ** 3Q. Stage 1 Interprocedural Knot ([s1_phi], [s1_lfp], and CPS Code Simulation) *)

  Lemma denote_operand_bundles_nil_eq (loc : string) (f : exp dtyp) :
    @denote_operand_bundles (@ParamsV IP IPT) loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad Monads.bind Monads.ret Monad_itree].
    apply Eqit.bind_ret_l.
  Qed.

  Lemma safe_mem_code_to_check_other
    (safe_locals : list local_id) (p_dummy : local_id) (cd : code dtyp) :
    ~ In p_dummy (flat_map m2r_code_entry_uses cd) ->
    forallb (m2r_safe_mem_instr_any safe_locals) cd = true ->
    forallb (check_other_instr_for_slot true safe_locals p_dummy) cd = true.
  Proof using.
    induction cd as [| im rest IH]; cbn [flat_map forallb]; [intros _ _; reflexivity |].
    intros Hnin Hchk.
    rewrite andb_true_iff in Hchk; destruct Hchk as [Him Hrest].
    assert (Hnin_im : ~ In p_dummy (m2r_code_entry_uses im))
      by (intros H; apply Hnin, in_app_iff; left; exact H).
    assert (Hnin_rest : ~ In p_dummy (flat_map m2r_code_entry_uses rest))
      by (intros H; apply Hnin, in_app_iff; right; exact H).
    rewrite andb_true_iff; split; [| exact (IH Hnin_rest Hrest)].
    unfold check_other_instr_for_slot, m2r_safe_mem_instr_any in *.
    rewrite andb_true_iff, negb_true_iff; split.
    - destruct (in_raw_ids p_dummy (m2r_code_entry_uses im)) eqn:Ein; [| reflexivity].
      apply m2r_in_raw_ids_true in Ein; contradiction (Hnin_im Ein).
    - destruct im as [[iid ins] md]; destruct iid, ins; exact Him.
  Qed.

  Definition s1_fn_entry_rel
    (f1 f2 : @function_denotation (@ParamsV IP IPT)) : Prop :=
    (f1 = @putchar_denotation (@ParamsV IP IPT) /\
     f2 = @putchar_denotation (@ParamsV IP IPT)) \/
    (exists d,
       m2r_defn_mem_safe d = true /\
       f1 = denote_function d /\
       f2 = denote_function d) \/
    (exists df df',
       try_promote_slot_in_defn true df = Some df' /\
       f1 = denote_function df /\
       f2 = denote_function df').

  Record s1_prom_static : Type := {
    sps_fargs    : list local_id;
    sps_c        : CFG.cfg dtyp;
    sps_b_init   : block dtyp;
    sps_p        : local_id;
    sps_dt       : dtyp;
    sps_init_reg : local_id;
    sps_end_reg0 : local_id;
    sps_code0'   : code dtyp;
    sps_pass1    : list (block dtyp * local_id * code dtyp * local_id)
  }.

  Definition sps_avoid0 (sp : s1_prom_static) : list raw_id :=
    sps_fargs sp ++ cfg_all_ids (sps_c sp).

  Definition sps_safe_no_p (sp : s1_prom_static) : list local_id :=
    let all_defs := sps_fargs sp ++ flat_map full_block_defs (blks (sps_c sp)) in
    let safe_locals := m2r_collect_unique_allocas all_defs (blks (sps_c sp)) in
    List.filter (fun q => negb (raw_id_eqb q (sps_p sp))) safe_locals.

  Definition sps_end_map (sp : s1_prom_static) : list (block_id * local_id) :=
    List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) (sps_pass1 sp).

  Definition sps_blks' (sp : s1_prom_static) : ocfg dtyp :=
    build_promoted_blocks (init (sps_c sp)) (sps_dt sp) (sps_init_reg sp)
      (blks (sps_c sp)) (sps_pass1 sp).

  Definition s1_prom_static_wf (sp : s1_prom_static) : Prop :=
    let c := sps_c sp in
    let p := sps_p sp in
    let dt := sps_dt sp in
    NoDup (List.map blk_id (blks c)) /\
    ~ In (init c) (m2r_all_succs c) /\
    In (sps_b_init sp) (blks c) /\
    blk_id (sps_b_init sp) = init c /\
    is_scalar_dtyp dt = true /\
    (forall bk,
       In bk (blks c) ->
       blk_id bk <> init c ->
       check_block_non_entry_for_slot true (sps_safe_no_p sp) p dt bk = true /\
       ~ In p (full_block_defs bk)) /\
    List.map (fun '(bk, _, _, _) => bk) (sps_pass1 sp) = blks c /\
    (forall bk phi_r cd' end_r,
       In (bk, phi_r, cd', end_r) (sps_pass1 sp) ->
       ~ In phi_r (sps_avoid0 sp) /\
       ~ In end_r (sps_avoid0 sp) /\
       (if raw_id_eqb (blk_id bk) (init c) then
          cd' = sps_code0' sp /\ end_r = sps_end_reg0 sp
        else
          exists av_in av_out,
            incl (sps_avoid0 sp) av_in /\
            rewrite_code_for_slot p dt phi_r av_in (blk_code bk) = (cd', end_r, av_out))).

  Section InterprocKnot.
    Context (g0 : @global_env (@ParamsV IP IPT))
            (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
            (Hctx : forall k, option_rel s1_fn_entry_rel (lookup k ctx1) (lookup k ctx2)).

    Local Definition s1_call_post
      (U0 P0 : list N) (G : list ghost_slot)
      (fs0 : @Framestack (@ParamsV IP IPT))
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      : list N -> Res (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) ->
        Res (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) -> Prop :=
      fun U' '(s1', rv1) '(s2', rv2) =>
        exists P' σ1' σ2',
          incl U0 U' /\
          incl P0 P' /\
          rv1 = rv2 /\
          s1' = (σ1', (ls1, g0)) /\
          s2' = (σ2', (ls2, g0)) /\
          stage1_mem_inv U' P' G σ1' σ2' /\
          Memory_stack_frame_stack (state_memory_stack σ2') = fs0 /\
          genv_safe P' g0.

    Local Definition s1_unprom_exit_rel
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS) : Prop :=
      incl U0 U_e /\
      exists P_e σ1_e σ2_e sf1_e sf2_e,
        incl P0 P_e /\
        s1_e = (σ1_e, ((sf1_e, fstk1), g0)) /\
        s2_e = (σ2_e, ((sf2_e, fstk2), g0)) /\
        stage1_mem_inv U_e P_e G σ1_e σ2_e /\
        top_frame_unprom_from fs0 G (state_memory_stack σ2_e) /\
        genv_safe P_e g0.

    Local Definition s1_unprom_rexc
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (x1 x2 : @exc (@ParamsV IP IPT)) : Prop :=
      x1 = x2 /\ s1_unprom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_unprom_rret
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) : Prop :=
      r1 = r2 /\ s1_unprom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_unprom_loop_inv
      (d : definition dtyp (CFG.cfg dtyp))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (_ : block_id * block_id) : Prop :=
      let c := df_instrs d in
      let safe_locals :=
        m2r_collect_unique_allocas (df_args d ++ flat_map full_block_defs (blks c)) (blks c) in
      incl U0 U /\
      exists P σ1 σ2 sf,
        incl P0 P /\
        s1 = (σ1, ((sf, fstk1), g0)) /\
        s2 = (σ2, ((sf, fstk2), g0)) /\
        stage1_mem_inv U P G σ1 σ2 /\
        top_frame_unprom_from fs0 G (state_memory_stack σ2) /\
        genv_safe P g0 /\
        safe_locals_env P safe_locals (stack_vars sf).

    Local Definition s1_prom_exit_rel
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS) : Prop :=
      incl U0 U_e /\
      exists P_e σ1_e σ2_e sf1_e sf2_e,
        incl P0 P_e /\
        s1_e = (σ1_e, ((sf1_e, fstk1), g0)) /\
        s2_e = (σ2_e, ((sf2_e, fstk2), g0)) /\
        genv_safe P_e g0 /\
        ((stage1_mem_inv U_e P_e G σ1_e σ2_e /\
          top_frame_unprom_from fs0 G (state_memory_stack σ2_e)) \/
         (exists gs_e,
            stage1_mem_inv U_e P_e (gs_e :: G) σ1_e σ2_e /\
            top_frame_prom_from fs0 gs_e G (state_memory_stack σ2_e))).

    Local Definition s1_prom_rexc
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (x1 x2 : @exc (@ParamsV IP IPT)) : Prop :=
      x1 = x2 /\ s1_prom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_prom_rret
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) : Prop :=
      r1 = r2 /\ s1_prom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_prom_loop_inv
      (sp : s1_prom_static)
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id) : Prop :=
      let c := sps_c sp in
      snd j <> init c /\
      incl U0 U /\
      (exists b_pred,
         In b_pred (blks c) /\
         blk_id b_pred = fst j /\
         In (snd j) (m2r_block_succs b_pred)) /\
      (exists P gs σ1 σ2 sf1 sf2,
         incl P0 P /\
         gs_dt gs = sps_dt sp /\
         Maps.lookup (sps_p sp) (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) /\
         Maps.lookup (lookup_end_reg (sps_end_map sp) (fst j) (sps_init_reg sp)) (stack_vars sf2) =
           Some (DVALUE_Base (gs_db gs)) /\
         s1 = (σ1, ((sf1, fstk1), g0)) /\
         s2 = (σ2, ((sf2, fstk2), g0)) /\
         stage1_mem_inv U P (gs :: G) σ1 σ2 /\
         top_frame_prom_from fs0 gs G (state_memory_stack σ2) /\
         genv_safe P g0 /\
         safe_locals_env P (sps_safe_no_p sp) (stack_vars sf2) /\
         (forall x,
            In x (sps_avoid0 sp) -> x <> sps_p sp ->
            Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2))).

    Local Definition s1_phi
      (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
      (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
      (exists dt cc fv vs P G σ1 σ2 ls1 ls2 k1 k2,
         stage1_mem_inv U P G σ1 σ2 /\
         genv_safe P g0 /\
         (forall U' a1 a2,
            incl U U' ->
            s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2 U' a1 a2 ->
            m2r_paco r U' (k1 a1) (k2 a2)) /\
         ITree.bind (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) (σ1, (ls1, g0))) k1 ≅ t1 /\
         ITree.bind (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) (σ2, (ls2, g0))) k2 ≅ t2)
      \/
      (exists d va fs0 U0 P0 G fstk1 fstk2 s1 s2 j k_out1 k_out2,
         m2r_defn_mem_safe d = true /\
         s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U s1 s2 j /\
         (forall U' a1 a2,
            incl U0 U' ->
            exc_post (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                     (s1_unprom_rret fs0 U0 P0 G fstk1 fstk2) U' a1 a2 ->
            m2r_paco r U' (k_out1 a1) (k_out2 a2)) /\
         ITree.bind (interp_cfg_exc ctx1 (denote_ocfg_map (ocfg_map (blks (df_instrs d))) va j) s1) k_out1 ≅ t1 /\
         ITree.bind (interp_cfg_exc ctx2 (denote_ocfg_map (ocfg_map (blks (df_instrs d))) va j) s2) k_out2 ≅ t2)
      \/
      (exists sp va fs0 U0 P0 G fstk1 fstk2 s1 s2 j k_out1 k_out2,
         s1_prom_static_wf sp /\
         s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U s1 s2 j /\
         (forall U' a1 a2,
            incl U0 U' ->
            exc_post (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                     (s1_prom_rret fs0 U0 P0 G fstk1 fstk2) U' a1 a2 ->
            m2r_paco r U' (k_out1 a1) (k_out2 a2)) /\
         ITree.bind (interp_cfg_exc ctx1 (denote_ocfg_map (ocfg_map (blks (sps_c sp))) va j) s1) k_out1 ≅ t1 /\
         ITree.bind (interp_cfg_exc ctx2 (denote_ocfg_map (ocfg_map (sps_blks' sp)) va j) s2) k_out2 ≅ t2).

    Local Lemma s1_phi_mon
      (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
      (Hle : forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2) :
      forall U t1 t2, s1_phi r1 U t1 t2 -> s1_phi r2 U t1 t2.
    Proof using.
      intros U t1 t2 [Hcall | [Hunp | Hprom]].
      - left; destruct Hcall as (dt & cc & fv & vs & P & G & σ1 & σ2 & ls1 & ls2 & k1 & k2 &
                                 Hinv & Hg & Hk & E1 & E2).
        exists dt, cc, fv, vs, P, G, σ1, σ2, ls1, ls2, k1, k2.
        refine (conj Hinv (conj Hg (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
      - right; left; destruct Hunp as (d & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                                       k1 & k2 & Hd & Hli & Hk & E1 & E2).
        exists d, va, fs0, U0, P0, G, fstk1, fstk2, s1, s2, j, k1, k2.
        refine (conj Hd (conj Hli (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
      - right; right; destruct Hprom as (sp & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                                         k1 & k2 & Hwf & Hli & Hk & E1 & E2).
        exists sp, va, fs0, U0, P0, G, fstk1, fstk2, s1, s2, j, k1, k2.
        refine (conj Hwf (conj Hli (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
    Qed.

    Local Definition s1_lfp (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
      forall R : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop,
        (forall U' a1 a2, s1_phi R U' a1 a2 -> R U' a1 a2) ->
        R U t1 t2.

    Local Lemma s1_lfp_fold (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_phi s1_lfp U t1 t2 ->
      s1_lfp U t1 t2.
    Proof using.
      intros Hphi R Hclosed.
      apply Hclosed.
      exact (s1_phi_mon s1_lfp R (fun U' a1 a2 Hl => Hl R Hclosed) U t1 t2 Hphi).
    Qed.

    Local Lemma s1_lfp_unfold (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_lfp U t1 t2 ->
      s1_phi s1_lfp U t1 t2.
    Proof using.
      intros Hl; apply (Hl (s1_phi s1_lfp)).
      intros U' a1 a2 H; exact (s1_phi_mon (s1_phi s1_lfp) s1_lfp (@s1_lfp_fold) U' a1 a2 H).
    Qed.

    Local Lemma s1_iter_one_step
      (RI   : list N -> FusedS -> FusedS -> block_id * block_id -> Prop)
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (RRet : list N -> FusedS -> FusedS ->
              (block_id * block_id) + @dvalue (@ParamsV IP IPT) ->
              (block_id * block_id) + @dvalue (@ParamsV IP IPT) -> Prop)
      (b1 b2 : block_id * block_id ->
               @CFGtop (@ParamsV IP IPT)
                 ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (k_out1 k_out2 : Res (@exc (@ParamsV IP IPT) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) ->
                       itree ProvBotE Ans)
      (Hbody :
         s1_cps s1_lfp
           (exc_post RExc
              (fun U' s1' s2' lr1 lr2 =>
                 match lr1, lr2 with
                 | inl j1, inl j2 => j1 = j2 /\ RI U' s1' s2' j1
                 | inr v1, inr v2 => RRet U' s1' s2' v1 v2
                 | _, _ => False
                 end))
           U
           (interp_cfg_exc ctx1 (b1 j) s1)
           (interp_cfg_exc ctx2 (b2 j) s2))
      (Hloop :
         forall U' s1' s2' j',
           incl U U' ->
           RI U' s1' s2' j' ->
           s1_lfp U'
             (ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j') s1') k_out1)
             (ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j') s2') k_out2))
      (Hk_out :
         forall U' a1 a2,
           incl U U' ->
           exc_post RExc RRet U' a1 a2 ->
           m2r_paco s1_lfp U' (k_out1 a1) (k_out2 a2)) :
      m2r_paco s1_lfp U
        (ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j) s1) k_out1)
        (ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j) s2) k_out2).
    Proof using.
      set (step_k := fun ctx (b : block_id * block_id ->
                                  @CFGtop (@ParamsV IP IPT)
                                    ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))
                         '(s', res) =>
                       match res with
                       | inl x => Ret (s', inl x)
                       | inr (inl j') => Tau (interp_cfg_exc ctx (ITree.iter b j') s')
                       | inr (inr v) => Ret (s', inr v)
                       end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) +
                                                 ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))).
      assert (Hunf : forall ctx b s i,
                interp_cfg_exc ctx (ITree.iter b i) s ≅
                ITree.bind (interp_cfg_exc ctx (b i) s) (step_k ctx b)).
      { intros ctx b s i.
        rewrite (interp_cfg_exc_obs_eq ctx _ _ s (unfold_iter b i)), interp_cfg_exc_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' [x | [j' | v]]] _ <-; cbn [step_k];
          [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
      assert (Eb1 : ITree.bind (interp_cfg_exc ctx1 (b1 j) s1)
                      (fun x => ITree.bind (step_k ctx1 b1 x) k_out1) ≅
                    ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j) s1) k_out1).
      { symmetry; rewrite <- Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf | intros ? ? <-; reflexivity]. }
      assert (Eb2 : ITree.bind (interp_cfg_exc ctx2 (b2 j) s2)
                      (fun x => ITree.bind (step_k ctx2 b2 x) k_out2) ≅
                    ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j) s2) k_out2).
      { symmetry; rewrite <- Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf | intros ? ? <-; reflexivity]. }
      eapply m2r_paco_obs_eq; [exact Eb1 | exact Eb2 |].
      apply Hbody.
      intros U' [s1' res1] [s2' res2] Hinc Hpost.
      destruct res1 as [x1 | [j1 | v1]], res2 as [x2 | [j2 | v2]]; cbn in Hpost; try contradiction.
      - eapply m2r_paco_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        exact (Hk_out U' (s1', inl x1) (s2', inl x2) Hinc Hpost).
      - destruct Hpost as [<- Hri].
        eapply m2r_paco_tau_both_r;
          [symmetry; apply Eqit.bind_tau | symmetry; apply Eqit.bind_tau |].
        exact (Hloop U' s1' s2' j1 Hinc Hri).
      - eapply m2r_paco_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        exact (Hk_out U' (s1', inr v1) (s2', inr v2) Hinc Hpost).
    Qed.

    Local Lemma s1_other_instr_exc_cps
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (TF : state -> Prop)
      (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
      (pre_c post_c : code dtyp)
      (safe_sub : list local_id) (p : local_id)
      (im : instr_id * instr dtyp * list (metadata dtyp))
      (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
      (U P_unprom : list N) (G : list ghost_slot)
      (σ1 σ2 : state)
      (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
      (Hnd_bks : NoDup (List.map blk_id bks))
      (Hbk : In bk bks)
      (Hsplit : blk_code bk = pre_c ++ im :: post_c)
      (Hsub : forall q,
                In q safe_sub ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
      (Hchk : check_other_instr_for_slot true safe_sub p im = true)
      (HTF_eq : forall s_a s_b,
                  Memory_stack_frame_stack (state_memory_stack s_b) =
                    Memory_stack_frame_stack (state_memory_stack s_a) ->
                  TF s_a -> TF s_b)
      (HTF_add : forall s_a s_b ptrs,
                   (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                   Memory_stack_frame_stack (state_memory_stack s_b) =
                     Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                   TF s_a -> TF s_b)
      (HRExc : forall U_x P_x σ1_x σ2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x G σ1_x σ2_x ->
                 TF σ2_x ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1, fstk1), g0)) (σ2_x, ((sf2, fstk2), g0)) ex ex)
      (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
      (HTF : TF σ2)
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
      (Huse_vars : forall x,
                     In x (m2r_code_entry_uses im) ->
                     Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                TF σ2' /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                ((sf1' = sf1 /\ sf2' = sf2) \/
                 (exists id0 v,
                    fst (fst im) = IId id0 /\
                    sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                    sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
        U
        (interp_cfg_exc ctx1 (denote_instr im va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_instr im va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      destruct im as [[iid ins] md].
      destruct ins as [| op | [dt_c fn_e] args_c anns_c obs_c | | | | | | | |];
        try (apply refine_prov_to_s1_cps;
             exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc TF fargs bks bk pre_c post_c
                      safe_sub p (iid, _, md) va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
                      Hnd_bks Hbk Hsplit Hsub Hchk HTF_eq HTF_add Hinv HTF Hgenv Hsafe_loc Huse_vars)).
      assert (Hcall_chk : obs_c = [] /\ intrinsic_exp fn_e = None).
      { unfold check_other_instr_for_slot in Hchk.
        destruct iid; rewrite !andb_true_iff in Hchk;
          destruct Hchk as [_ [[_ Hobs] Hintr]];
          apply m2r_is_empty_spec in Hobs;
          destruct (intrinsic_exp fn_e); try discriminate Hintr;
          exact (conj Hobs Logic.eq_refl). }
      destruct Hcall_chk as [-> Hintr_none].
      cbn [denote_instr]; rewrite Hintr_none.
      eapply s1_cps_cfg_exc_bind.
      - apply refine_prov_to_s1_cps.
        eapply denote_call_args_stage1_exc_sim; [exact Hinv |].
        intros x Hx; apply Huse_vars.
        cbn [m2r_code_entry_uses full_instr_uses].
        apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hx.
      - intros U1 s1_a vs1 s2_a vs2 _ (-> & -> & -> & <-).
        eapply s1_cps_cfg_exc_bind.
        + eapply s1_cps_obs_eq;
            [symmetry; apply interp_cfg_exc_obs_eq, denote_operand_bundles_nil_eq
            | symmetry; apply interp_cfg_exc_obs_eq, denote_operand_bundles_nil_eq |].
          apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
            exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
        + intros U2 s1_ob _ s2_ob _ _ (-> & -> & ->).
          eapply s1_cps_cfg_exc_bind with
            (RA := fun U_c s1_c s2_c rv1 rv2 =>
                     exists P_c σ1_c σ2_c,
                       incl U U_c /\
                       incl P_unprom P_c /\
                       rv1 = rv2 /\
                       s1_c = (σ1_c, ((sf1, fstk1), g0)) /\
                       s2_c = (σ2_c, ((sf2, fstk2), g0)) /\
                       stage1_mem_inv U_c P_c G σ1_c σ2_c /\
                       Memory_stack_frame_stack (state_memory_stack σ2_c) =
                         Memory_stack_frame_stack (state_memory_stack σ2) /\
                       genv_safe P_c g0).
          * eapply s1_cps_cfg_exc_bind.
            -- apply refine_prov_to_s1_cps, denote_exp_cfg_exc_sim.
               intros x Hx; apply Huse_vars.
               cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd].
               apply in_app_iff; left; apply in_app_iff; left; exact Hx.
            -- intros U3 s1_fn fv1 s2_fn fv2 _ (-> & -> & -> & <- & _).
               intros k_c1 k_c2 Hk_c.
               apply (m2r_cps_call_exc s1_lfp); apply s1_lfp_fold; left.
               exists dt_c, (anns_cconv anns_c), fv1, vs1, P_unprom, G,
                      σ1, σ2, (sf1, fstk1), (sf2, fstk2),
                      (fun '(s1', y1) => Tau (k_c1 (s1', inr y1))),
                      (fun '(s2', y2) => Tau (k_c2 (s2', inr y2))).
               refine (conj Hinv (conj Hgenv (conj _ (conj Logic.eq_refl Logic.eq_refl)))).
               intros U_c [s1_c rv1] [s2_c rv2] Hinc_c Hpost_c.
               apply m2r_paco_fold; eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |];
                 apply m2r_paco_unfold.
               exact (Hk_c U_c (s1_c, inr rv1) (s2_c, inr rv2) Hinc_c Hpost_c).
          * intros U_c s1_c rv1 s2_c rv2 _
              (P_c & σ1_c & σ2_c & HincU_c & HincP_c & <- & -> & -> & Hinv_c & Hfs_c & Hgenv_c).
            pose proof (HTF_eq σ2 σ2_c Hfs_c HTF) as HTF_c.
            pose proof (safe_locals_env_incl P_unprom P_c safe_sub (stack_vars sf2) HincP_c Hsafe_loc)
              as Hsafe_c.
            eapply s1_cps_cfg_exc_bind.
            -- apply refine_prov_to_s1_cps.
               exact (check_call_return_stage1_exc_sim ctx1 ctx2 RExc
                        (ann_fun_attributes anns_c) (ann_ret_attributes anns_c)
                        (metadata_range md) _ vs1 rv1
                        U_c P_c G σ1_c σ2_c ((sf1, fstk1), g0) ((sf2, fstk2), g0) Hinv_c).
            -- intros U_cr s1_cr res1 s2_cr res2 _ (-> & -> & -> & <-).
               eapply s1_cps_cfg_exc_bind.
               ++ destruct res1 as [ex | dv].
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_raiseLLVM_both.
                     exact (HRExc U_c P_c σ1_c σ2_c ex HincU_c HincP_c Hinv_c HTF_c Hgenv_c).
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                     exact (conj (Logic.eq_refl U_c)
                              (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
               ++ intros U_ret s1_ret dv1 s2_ret dv2 _ (-> & -> & -> & <-).
                  destruct iid as [id0 | vid0].
                  ** assert (Hid_nsafe : ~ In id0 safe_sub).
                     { intros Hin_s.
                       destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                                   bk pre_c (INSTR_Call (dt_c, fn_e) args_c anns_c []) md post_c
                                   Hbk Hsplit) as (? & ? & Hbad);
                         discriminate Hbad. }
                     apply refine_prov_to_s1_cps.
                     eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
                     eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
                     apply refine_prov_ret.
                     exists P_c, σ1_c, σ2_c,
                            (upd_local_sf sf1 (Maps.add id0 dv1 (stack_vars sf1))),
                            (upd_local_sf sf2 (Maps.add id0 dv1 (stack_vars sf2))).
                     refine (conj HincU_c (conj HincP_c
                               (conj Logic.eq_refl (conj Logic.eq_refl
                                 (conj Logic.eq_refl (conj Logic.eq_refl
                                   (conj Hinv_c (conj HTF_c (conj Hgenv_c
                                     (conj (safe_locals_env_add_other P_c safe_sub id0 dv1 _ Hid_nsafe Hsafe_c)
                                           _)))))))))).
                     right; exists id0, dv1; repeat split; reflexivity.
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                     exists P_c, σ1_c, σ2_c, sf1, sf2.
                     refine (conj HincU_c (conj HincP_c
                               (conj Logic.eq_refl (conj Logic.eq_refl
                                 (conj Logic.eq_refl (conj Logic.eq_refl
                                   (conj Hinv_c (conj HTF_c (conj Hgenv_c
                                     (conj Hsafe_c (or_introl (conj Logic.eq_refl Logic.eq_refl)))))))))))).
    Qed.

    Local Lemma s1_other_code_exc_cps
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (TF : state -> Prop)
      (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
      (pre_c cd post_c : code dtyp)
      (safe_sub : list local_id) (p : local_id)
      (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
      (U P_unprom : list N) (G : list ghost_slot)
      (σ1 σ2 : state)
      (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
      (Hnd_bks : NoDup (List.map blk_id bks))
      (Hbk : In bk bks)
      (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
      (Hsub : forall q,
                In q safe_sub ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
      (Hchk : forallb (check_other_instr_for_slot true safe_sub p) cd = true)
      (HTF_eq : forall s_a s_b,
                  Memory_stack_frame_stack (state_memory_stack s_b) =
                    Memory_stack_frame_stack (state_memory_stack s_a) ->
                  TF s_a -> TF s_b)
      (HTF_add : forall s_a s_b ptrs,
                   (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                   Memory_stack_frame_stack (state_memory_stack s_b) =
                     Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                   TF s_a -> TF s_b)
      (HRExc : forall U_x P_x σ1_x σ2_x sf1_x sf2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x G σ1_x σ2_x ->
                 TF σ2_x ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1_x, fstk1), g0)) (σ2_x, ((sf2_x, fstk2), g0)) ex ex)
      (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
      (HTF : TF σ2)
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
      (Hvars : forall x,
                 x <> p ->
                 Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                TF σ2' /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2')) /\
                (sf1 = sf2 -> sf1' = sf2')))
        U
        (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_code cd va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      revert pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk HRExc Hinv HTF Hgenv Hsafe_loc Hvars.
      induction cd as [| im rest IH];
        intros pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk HRExc Hinv HTF Hgenv Hsafe_loc Hvars;
        unfold denote_code; cbn [loop_monad forallb].
      - apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        exists P_unprom, σ1, σ2, sf1, sf2.
        refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv (conj HTF (conj Hgenv
                        (conj Hsafe_loc (conj Hvars (fun Heq => Heq)))))))))))).
      - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
        assert (Huse_im : forall x,
                  In x (m2r_code_entry_uses im) ->
                  Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
        { intros x Hx; apply Hvars; intros ->.
          unfold check_other_instr_for_slot in Hchk_im.
          rewrite andb_true_iff, negb_true_iff in Hchk_im.
          exact (in_raw_ids_false _ _ (proj1 Hchk_im) Hx). }
        eapply s1_cps_cfg_exc_bind.
        + exact (s1_other_instr_exc_cps RExc TF fargs bks bk pre_c (rest ++ post_c)
                   safe_sub p im va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2
                   Hnd_bks Hbk Hsplit Hsub Hchk_im HTF_eq HTF_add
                   (fun U_x P_x σ1_x σ2_x ex H1 H2 H3 H4 H5 =>
                      HRExc U_x P_x σ1_x σ2_x sf1 sf2 ex H1 H2 H3 H4 H5)
                   Hinv HTF Hgenv Hsafe_loc Huse_im).
        + intros U1 s1_m _ s2_m _ _
            (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
             HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & HTF1 & Hgenv1 & Hsafe1 & Hsf_step).
          assert (Hvars1 : forall x, x <> p -> Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m)).
          { intros x Hne; destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)];
              [exact (Hvars x Hne) |].
            cbn [stack_vars upd_local_sf]; destruct (raw_id_eqb_spec x id0) as [-> | Hx_id];
              [rewrite !lookup_add_eq; reflexivity
              | rewrite !lookup_add_neq by exact Hx_id; exact (Hvars x Hne)]. }
          assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
            by (rewrite <- app_assoc; exact Hsplit).
          eapply s1_cps_weaken.
          * exact (IH (pre_c ++ [im]) U1 P1 σ1_m σ2_m sf1_m sf2_m Hsplit_rest Hchk_rest
                     (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 =>
                        HRExc U_x P_x σ1_x σ2_x sf1_x sf2_x ex (incl_tran HincU1 H1) (incl_tran HincP1 H2))
                     Hinv1 HTF1 Hgenv1 Hsafe1 Hvars1).
          * intros U2 [s1_f res1] [s2_f res2] _.
            destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
              try (intros H; exact H).
            intros (P2 & σ1_f & σ2_f & sf1_f & sf2_f &
                    HincU2 & HincP2 & -> & -> & -> & -> & Hinv2 & HTF2 & Hgenv2 & Hsafe2 & Hvars2 & Heq2).
            exists P2, σ1_f, σ2_f, sf1_f, sf2_f.
            refine (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                      (conj Logic.eq_refl (conj Logic.eq_refl
                        (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Hinv2 (conj HTF2 (conj Hgenv2 (conj Hsafe2 (conj Hvars2 _))))))))))).
            intros Heq_sf; apply Heq2.
            destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)]; [exact Heq_sf | subst sf2; reflexivity].
    Qed.

    Local Lemma s1_rewrite_code_exc_cps
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (avoid0 : list raw_id) (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
      (pre_c cd post_c : code dtyp)
      (safe_no_p : list local_id) (p : local_id) (dt : dtyp)
      (cur_reg : local_id) (avoid : list raw_id)
      (cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id)
      (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
      (σ1 σ2 : state)
      (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
      (Hnd_bks : NoDup (List.map blk_id bks))
      (Hbk : In bk bks)
      (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
      (Hsub : forall q,
                In q safe_no_p ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
      (Hsafe_av0 : incl safe_no_p avoid0)
      (Huses_av0 : forall im x, In im cd -> In x (m2r_code_entry_uses im) -> In x avoid0)
      (Hdefs_av0 : forall im x, In im cd -> In x (instr_id_defs (fst (fst im))) -> In x avoid0)
      (Hp_nd_cd : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd))
      (Hchk : forallb (check_code_entry_for_slot true safe_no_p p dt) cd = true)
      (Hrw : rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid'))
      (Hinc_av : incl avoid0 avoid)
      (Hcur_nin0 : ~ In cur_reg avoid0)
      (Hsc : is_scalar_dtyp dt = true)
      (HRExc : forall U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x (gs_x :: G) σ1_x σ2_x ->
                 top_frame_prom_from fs0 gs_x G (state_memory_stack σ2_x) ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1_x, fstk1), g0)) (σ2_x, ((sf2_x, fstk2), g0)) ex ex)
      (Hdt : gs_dt gs = dt)
      (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
      (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
      (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
      (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_no_p (stack_vars sf2))
      (Hvars : forall x,
                 In x avoid0 -> x <> p ->
                 Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' gs' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                gs_dt gs' = dt /\
                Maps.lookup p (stack_vars sf1') = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs'))) /\
                Maps.lookup end_reg (stack_vars sf2') = Some (DVALUE_Base (gs_db gs')) /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' (gs' :: G) σ1' σ2' /\
                top_frame_prom_from fs0 gs' G (state_memory_stack σ2') /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_no_p (stack_vars sf2') /\
                (forall x,
                   In x avoid0 -> x <> p ->
                   Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
        U
        (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_code cd' va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      revert pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
        Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
        HRExc Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars.
      induction cd as [| im rest IH];
        intros pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
          Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
          HRExc Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars;
        cbn [rewrite_code_for_slot forallb flat_map] in *.
      - inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
        unfold denote_code; cbn [loop_monad].
        apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        exists P_unprom, gs, σ1, σ2, sf1, sf2;
          repeat split; try apply incl_refl; assumption.
      - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
        assert (Hp_nd_im : ~ In p (instr_id_defs (fst (fst im))))
          by (destruct im as [[iid_i ?] ?]; intros Hp; apply Hp_nd_cd, in_app_iff; left; exact Hp).
        assert (Hp_nd_rest : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest))
          by (intros Hp; apply Hp_nd_cd, in_app_iff; right; exact Hp).
        assert (Huses_rest : forall im0 x, In im0 rest -> In x (m2r_code_entry_uses im0) -> In x avoid0)
          by (intros im0 x Him0 Hx; exact (Huses_av0 im0 x (or_intror Him0) Hx)).
        assert (Hdefs_rest : forall im0 x, In im0 rest -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0)
          by (intros im0 x Him0 Hx; exact (Hdefs_av0 im0 x (or_intror Him0) Hx)).
        assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
          by (rewrite <- app_assoc; exact Hsplit).
        unfold check_code_entry_for_slot in Hchk_im.
        destruct (is_promotable_load_of p dt im) as [dst |] eqn:Eld.
        + destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
          inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
          pose proof (Hdefs_av0 im dst (or_introl Logic.eq_refl)) as Hdst_av0_fn.
          destruct (is_promotable_load_of_inv p dt im dst Eld)
            as (Hdst_ne_p & anns_ld & md_ld & -> & _ & Hmd_ld).
          assert (Hdst_av0 : In dst avoid0) by (apply Hdst_av0_fn; left; reflexivity).
          assert (Hcur_ne_dst : cur_reg <> dst) by (intros ->; exact (Hcur_nin0 Hdst_av0)).
          assert (Hdst_nsafe : ~ In dst safe_no_p).
          { intros Hin_s.
            destruct (unique_alloca_code_def_is_alloca fargs bks dst Hnd_bks (Hsub dst Hin_s)
                        bk pre_c
                        (INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld)
                        md_ld (rest ++ post_c) Hbk Hsplit) as (? & ? & Hbad);
              discriminate Hbad. }
          unfold denote_code; cbn [loop_monad].
          eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_mk_load_val_exp_exc_sim ctx1 ctx2 RExc dst p cur_reg dt anns_ld md_ld
                     va1 va2 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
                     Hdt Hsc Hmd_ld Hlk_p Hlk_cur Hinv).
          * intros U1 s1_m _ s2_m _ _ (dv_ld & -> & _ & _ & -> & ->).
            assert (Hlk_p1 : Maps.lookup p (Maps.add dst dv_ld (stack_vars sf1)) =
                             Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
              by (rewrite lookup_add_neq by (intros ->; exact (Hdst_ne_p Logic.eq_refl)); exact Hlk_p).
            assert (Hlk_cur1 : Maps.lookup cur_reg (Maps.add dst dv_ld (stack_vars sf2)) =
                               Some (DVALUE_Base (gs_db gs)))
              by (rewrite lookup_add_neq by exact Hcur_ne_dst; exact Hlk_cur).
            assert (Hsafe1 : safe_locals_env P_unprom safe_no_p (Maps.add dst dv_ld (stack_vars sf2)))
              by (apply safe_locals_env_add_other; assumption).
            assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                               Maps.lookup x (Maps.add dst dv_ld (stack_vars sf1)) =
                               Maps.lookup x (Maps.add dst dv_ld (stack_vars sf2))).
            { intros x Hx Hne; destruct (raw_id_eqb_spec x dst) as [-> | Hxd];
                [rewrite !lookup_add_eq; reflexivity
                | rewrite !lookup_add_neq by exact Hxd; exact (Hvars x Hx Hne)]. }
            exact (IH (pre_c ++ [_]) cur_reg avoid rest' er av' U P_unprom gs σ1 σ2
                     (upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)))
                     (upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)))
                     Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                     Hinc_av Hcur_nin0 HRExc Hdt Hlk_p1 Hlk_cur1 Hinv Htf Hgenv Hsafe1 Hvars1).
        + destruct (is_promotable_store_of p dt im) as [val_exp |] eqn:Est.
          * set (st_reg := fresh_name "m2r_st" avoid) in *.
            destruct (rewrite_code_for_slot p dt st_reg (st_reg :: avoid) rest) as [[rest' er] av'] eqn:Erest.
            inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
            pose proof (Huses_av0 im) as Hval_av0_fn.
            destruct (is_promotable_store_of_inv p dt im val_exp Est)
              as (Hnin_p_val & vid & anns_st & md_st & -> & _ & _).
            assert (Hst_nin0 : ~ In st_reg avoid0)
              by (intros Hin0; exact (fresh_name_not_in "m2r_st" avoid (Hinc_av _ Hin0))).
            assert (Hst_nsafe : ~ In st_reg safe_no_p)
              by (intros Hin_s; exact (Hst_nin0 (Hsafe_av0 st_reg Hin_s))).
            assert (Hval_vars : forall x,
                      In x (full_exp_uses val_exp) ->
                      Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
            { intros x Hx; apply Hvars.
              - apply Hval_av0_fn; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
                  apply in_app_iff; left; apply in_app_iff; left; exact Hx.
              - intros ->; exact (Hnin_p_val Hx). }
            unfold denote_code; cbn [loop_monad].
            eapply s1_cps_cfg_exc_bind.
            -- apply refine_prov_to_s1_cps.
               exact (denote_mk_store_val_exp_exc_sim ctx1 ctx2 RExc vid p st_reg dt val_exp
                        anns_st md_st va1 va2 fs0 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
                        Hdt Hsc Hlk_p Hinv Htf Hval_vars).
            -- intros U1 s1_m _ s2_m _ _ (db' & bs' & σ1' & -> & _ & _ & _ & -> & -> & Hinv1 & Htf1).
               assert (Hinc_av1 : incl avoid0 (st_reg :: avoid))
                 by (intros z Hz; right; exact (Hinc_av z Hz)).
               assert (Hlk_st : Maps.lookup st_reg (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)) =
                                Some (DVALUE_Base (gs_db (gs_set_val gs db' bs'))))
                 by (cbn [gs_db gs_set_val]; apply lookup_add_eq).
               assert (Hsafe1 : safe_locals_env P_unprom safe_no_p
                                  (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)))
                 by (apply safe_locals_env_add_other; assumption).
               assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                                  Maps.lookup x (stack_vars sf1) =
                                  Maps.lookup x (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2))).
               { intros x Hx Hne; rewrite lookup_add_neq by (intros ->; exact (Hst_nin0 Hx));
                   exact (Hvars x Hx Hne). }
               exact (IH (pre_c ++ [_]) st_reg (st_reg :: avoid) rest' er av'
                        U P_unprom (gs_set_val gs db' bs') σ1' σ2 sf1
                        (upd_local_sf sf2 (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2)))
                        Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                        Hinc_av1 Hst_nin0 HRExc Hdt Hlk_p Hlk_st Hinv1 Htf1 Hgenv Hsafe1 Hvars1).
          * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
            inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
            assert (Huse_im : forall x,
                      In x (m2r_code_entry_uses im) ->
                      Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
            { intros x Hx; apply Hvars.
              - exact (Huses_av0 im x (or_introl Logic.eq_refl) Hx).
              - intros ->; unfold check_other_instr_for_slot in Hchk_im;
                  rewrite andb_true_iff, negb_true_iff in Hchk_im;
                  exact (in_raw_ids_false _ _ (proj1 Hchk_im) Hx). }
            unfold denote_code; cbn [loop_monad].
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_other_instr_exc_cps RExc
                        (fun s => top_frame_prom_from fs0 gs G (state_memory_stack s))
                        fargs bks bk pre_c (rest ++ post_c)
                        safe_no_p p im va1 va2 U P_unprom (gs :: G) σ1 σ2 sf1 sf2 fstk1 fstk2
                        Hnd_bks Hbk Hsplit Hsub Hchk_im
                        (fun s_a s_b Heq_fs HT => top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs) HT)
                        (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                           top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs)
                             (top_frame_prom_add_ptrs fs0 gs G ptrs _ HT Hdisj))
                        (fun U_x P_x σ1_x σ2_x ex H1 H2 H3 H4 H5 =>
                           HRExc U_x P_x gs σ1_x σ2_x sf1 sf2 ex H1 H2 H3 H4 H5)
                        Hinv Htf Hgenv Hsafe_loc Huse_im).
            -- intros U1 s1_m _ s2_m _ _
                 (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
                  HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & Htf1 & Hgenv1 & Hsafe1 & Hsf_step).
               assert (Hstep_env :
                         Maps.lookup p (stack_vars sf1_m) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) /\
                         Maps.lookup cur_reg (stack_vars sf2_m) = Some (DVALUE_Base (gs_db gs)) /\
                         (forall x, In x avoid0 -> x <> p ->
                            Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m))).
               { destruct Hsf_step as [[-> ->] | (id0 & v & Heq_iid & -> & ->)];
                   [exact (conj Hlk_p (conj Hlk_cur Hvars)) |].
                 assert (Hid_av0 : In id0 avoid0)
                   by (apply (Hdefs_av0 im id0 (or_introl Logic.eq_refl)); rewrite Heq_iid; left; reflexivity).
                 assert (Hp_ne_id : p <> id0)
                   by (intros ->; apply Hp_nd_im; rewrite Heq_iid; left; reflexivity).
                 assert (Hcur_ne_id : cur_reg <> id0)
                   by (intros ->; exact (Hcur_nin0 Hid_av0)).
                 cbn [stack_vars upd_local_sf]; split;
                   [rewrite lookup_add_neq by exact Hp_ne_id; exact Hlk_p | split;
                   [rewrite lookup_add_neq by exact Hcur_ne_id; exact Hlk_cur |]].
                 intros x Hx Hne; destruct (raw_id_eqb_spec x id0) as [-> | Hx_id];
                   [rewrite !lookup_add_eq; reflexivity
                   | rewrite !lookup_add_neq by exact Hx_id; exact (Hvars x Hx Hne)]. }
               destruct Hstep_env as (Hlk_p1 & Hlk_cur1 & Hvars1).
               eapply s1_cps_weaken.
               ++ exact (IH (pre_c ++ [im]) cur_reg avoid rest' er av' U1 P1 gs σ1_m σ2_m sf1_m sf2_m
                           Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                           Hinc_av Hcur_nin0
                           (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 =>
                              HRExc U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex
                                (incl_tran HincU1 H1) (incl_tran HincP1 H2))
                           Hdt Hlk_p1 Hlk_cur1 Hinv1 Htf1 Hgenv1 Hsafe1 Hvars1).
               ++ intros U2 [s1_f res1] [s2_f res2] _.
                  destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
                    try (intros H; exact H).
                  intros (P2 & gs2 & σ1_f & σ2_f & sf1_f & sf2_f &
                          HincU2 & HincP2 & -> & -> & Hdt2 & Hlk_p2 & Hlk_er2 &
                          -> & -> & Hinv2 & Htf2 & Hgenv2 & Hsafe2 & Hvars2).
                  exists P2, gs2, σ1_f, σ2_f, sf1_f, sf2_f.
                  exact (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                           (conj Logic.eq_refl (conj Logic.eq_refl
                             (conj Hdt2 (conj Hlk_p2 (conj Hlk_er2
                               (conj Logic.eq_refl (conj Logic.eq_refl
                                 (conj Hinv2 (conj Htf2 (conj Hgenv2 (conj Hsafe2 Hvars2))))))))))))).
    Qed.

    Local Lemma s1_external_call_cfg_sim
      (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT)))
      (U P : list N) (G : list ghost_slot)
      (σ1 σ2 : state) (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Hinv : stage1_mem_inv U P G σ1 σ2)
      (Hg : genv_safe P g0) :
      refine_prov
        (s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2)
        U
        (interp_cfg_model ctx1 (inr <$> external_call dt fv vs) (σ1, (ls1, g0)))
        (interp_cfg_model ctx2 (inr <$> external_call dt fv vs) (σ2, (ls2, g0))).
    Proof using.
      unfold Functor.fmap, Functor_itree, ITree.map.
      eapply refine_cfg_model_bind.
      - unfold external_call, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ subevent resum ReSum_inr ReSum_inl ReSum_id id_ Id_IFun inr1 inl1].
        unfold fused_trigger_prov.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
        eapply PassCommon.refine_prov_bind; [apply refine_prov_refl_incl |].
        intros U' r1 r2 _ [Hinc <-].
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret.
        exact (conj Hinc (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      - intros U' s1' r1 s2' r2 _ (Hinc & -> & -> & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret.
        exists P, σ1, σ2.
        exact (conj Hinc
                 (conj (incl_refl P)
                    (conj Logic.eq_refl
                       (conj Logic.eq_refl
                          (conj Logic.eq_refl
                             (conj (stage1_mem_inv_incl_U U U' P G σ1 σ2 Hinc Hinv)
                                   (conj Logic.eq_refl Hg))))))).
    Qed.

    Local Definition ocfg_step_body
      (bmap : rmap (block dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      : (block_id * block_id) ->
        @CFGtop (@ParamsV IP IPT)
          ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) :=
      fun '((bid_from, bid_src) : block_id * block_id) =>
        match RM.find bid_src bmap with
        | None => Monads.ret (inr (inl (bid_from, bid_src)))
        | Some block_src =>
            Monads.bind (denote_block block_src bid_from va)
              (fun bd =>
                 match bd with
                 | inr dv => Monads.ret (inr (inr dv))
                 | inl bid_target => Monads.ret (inl (bid_src, bid_target))
                 end)
        end.

    Local Lemma denote_ocfg_map_eq_iter
      (bmap : rmap (block dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (j : block_id * block_id) :
      denote_ocfg_map bmap va j = ITree.iter (ocfg_step_body bmap va) j.
    Proof using.
      unfold denote_ocfg_map, ocfg_step_body; reflexivity.
    Qed.

    Local Lemma s1_unprom_block_body_cps
      (d : definition dtyp (CFG.cfg dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (Hd : m2r_defn_mem_safe d = true)
      (Hli : s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U s1 s2 j) :
      let bmap := ocfg_map (blks (df_instrs d)) in
      s1_cps s1_lfp
        (exc_post (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
           (fun U' s1' s2' lr1 lr2 =>
              match lr1, lr2 with
              | inl j1, inl j2 =>
                  j1 = j2 /\ s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U' s1' s2' j1
              | inr v1, inr v2 =>
                  s1_unprom_rret fs0 U0 P0 G fstk1 fstk2 U' s1' s2' v1 v2
              | _, _ => False
              end))
        U
        (interp_cfg_exc ctx1 (ocfg_step_body bmap va j) s1)
        (interp_cfg_exc ctx2 (ocfg_step_body bmap va j) s2).
    Proof using.
      cbv zeta.
      unfold m2r_defn_mem_safe in Hd.
      set (c := df_instrs d) in *.
      set (fargs := df_args d) in *.
      set (safe_locals :=
             m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c)) in *.
      rewrite andb_true_iff in Hd; destruct Hd as [Hnd_bks Hbks_chk].
      apply m2r_nodup_ids_spec in Hnd_bks.
      unfold s1_unprom_loop_inv in Hli; fold c fargs safe_locals in Hli.
      destruct Hli as (HincU0 & P & σ1 & σ2 & sf & HincP0 & -> & -> & Hinv & Htf & Hgenv & Hsafe_loc).
      destruct j as [bf bs]; unfold ocfg_step_body; cbn [Monads.bind Monads.ret Monad_itree].
      rewrite ScopeTheory.ocfg_map_find_block.
      destruct (find_block (blks c) bs) as [bk |] eqn:Efb.
      - destruct (m2r_find_block_some_inv (blks c) bs bk Efb) as [Hin_bk _].
        rewrite forallb_forall in Hbks_chk; specialize (Hbks_chk bk Hin_bk).
        rewrite andb_true_iff in Hbks_chk; destruct Hbks_chk as [Hcd_safe Hni_tm].
        unfold denote_block.
        eapply s1_cps_cfg_exc_bind.
        + eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_phis_same_exc_sim ctx1 ctx2
                     (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                     bf (blk_phis bk) U σ1 σ2 sf sf fstk1 fstk2 g0
                     (fun _ _ => Logic.eq_refl)).
          * intros U_ph s1_ph _ s2_ph _ _ (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
            set (sf_ph := upd_local_sf sf (write_phi_dvs dvs (stack_vars sf))).
            assert (Hsafe_ph : safe_locals_env P safe_locals (stack_vars sf_ph)).
            { apply write_phi_dvs_safe_locals; [| exact Hsafe_loc].
              intros q Hq Hin_dvs; rewrite Hfst_dvs in Hin_dvs.
              apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
              exact (unique_alloca_not_phi_def fargs (blks c) q Hnd_bks Hq
                       bk q ph_q md_q Hin_bk Hpe_in Logic.eq_refl). }
            set (p_dummy := fresh_name "m2r_unused" (flat_map m2r_code_entry_uses (blk_code bk))).
            assert (Hchk_cd : forallb (check_other_instr_for_slot true safe_locals p_dummy) (blk_code bk) = true)
              by (apply safe_mem_code_to_check_other; [apply fresh_name_not_in | exact Hcd_safe]).
            assert (Hsplit_cd : blk_code bk = [] ++ blk_code bk ++ [])
              by (rewrite app_nil_r; reflexivity).
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_other_code_exc_cps
                        (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                        (fun s => top_frame_unprom_from fs0 G (state_memory_stack s))
                        fargs (blks c) bk [] (blk_code bk) []
                        safe_locals p_dummy va va U P G σ1 σ2 sf_ph sf_ph fstk1 fstk2
                        Hnd_bks Hin_bk Hsplit_cd (fun q Hq => Hq) Hchk_cd
                        (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs) HT)
                        (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                           top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs)
                             (top_frame_unprom_add_ptrs fs0 G ptrs _ HT Hdisj))
                        (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                           conj Logic.eq_refl
                             (conj (incl_tran HincU0 H1)
                                (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                   (ex_intro _ sf1_x (ex_intro _ sf2_x
                                      (conj (incl_tran HincP0 H2)
                                         (conj Logic.eq_refl
                                            (conj Logic.eq_refl (conj H3 (conj H4 H5))))))))))))
                        Hinv Htf Hgenv Hsafe_ph (fun _ _ => Logic.eq_refl)).
            -- intros U_cd s1_cd _ s2_cd _ _
                 (P_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                  HincU_cd & HincP_cd & _ & _ & -> & -> &
                  Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & _ & Heq_sf_cd).
               pose proof (Heq_sf_cd Logic.eq_refl) as ->.
               destruct (blk_term bk) as [[iid_t tm] md_t]; cbn [fst snd] in Hni_tm.
               apply refine_prov_to_s1_cps.
               eapply refine_prov_weaken.
               ++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                           (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                           iid_t iid_t tm md_t md_t
                           U_cd σ1_cd σ2_cd sf2_cd sf2_cd fstk1 fstk2 g0
                           Hni_tm (fun _ _ => Logic.eq_refl)).
                  intros ex; refine (conj Logic.eq_refl (conj (incl_tran HincU0 HincU_cd) _)).
                  exists P_cd, σ1_cd, σ2_cd, sf2_cd, sf2_cd.
                  exact (conj (incl_tran HincP0 HincP_cd)
                           (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_cd (conj Htf_cd Hgenv_cd))))).
               ++ intros U_t [s1_t res1] [s2_t res2].
                  destruct res1 as [ex1 | bd1], res2 as [ex2 | bd2]; cbn [exc_post];
                    try (intros H; exact H).
                  intros (-> & -> & -> & <- & _).
                  exists P_cd, σ1_cd, σ2_cd, sf2_cd.
                  exact (conj (incl_tran HincU0 HincU_cd)
                           (conj (incl_tran HincP0 HincP_cd)
                              (conj Logic.eq_refl
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd Hsafe_cd)))))))).
        + intros U_bd s1_bd bd1 s2_bd bd2 _
            (P_cd & σ1_cd & σ2_cd & sf2_cd &
             HincU_c & HincP_c & <- & -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd).
          destruct bd1 as [bid_tgt | dv_cur].
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd Hsafe_cd)))))).
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf2_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hinv_cd (conj Htf_cd Hgenv_cd))))).
      - apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU0 _)).
        exists P, σ1, σ2, sf, sf.
        exact (conj HincP0 (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Hinv (conj Htf Hgenv))))).
    Qed.

    Local Lemma s1_unprom_denote_function_cps
      (d : definition dtyp (CFG.cfg dtyp))
      (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
      (U0 P0 : list N) (G : list ghost_slot)
      (σ1_in σ2_in : state)
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Hd : m2r_defn_mem_safe d = true)
      (Hinv0 : stage1_mem_inv U0 P0 G σ1_in σ2_in)
      (Hgenv0 : genv_safe P0 g0) :
      s1_cps s1_lfp
        (s1_call_post U0 P0 G (Memory_stack_frame_stack (state_memory_stack σ2_in)) ls1 ls2)
        U0
        (interp_cfg_model ctx1 (denote_function d cc args) (σ1_in, (ls1, g0)))
        (interp_cfg_model ctx2 (denote_function d cc args) (σ2_in, (ls2, g0))).
    Proof using.
      destruct ls1 as [sf_c1 fstk_c1], ls2 as [sf_c2 fstk_c2].
      unfold denote_function.
      destruct (dc_param_attrs (df_prototype d)) as [ret_attrs args_attrs].
      set (fname := show_raw_id (dc_name (df_prototype d))).
      set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
      eapply s1_cps_cfg_bind.
      - apply refine_prov_to_s1_cps.
        eapply refine_cfg_EOU; [apply refine_EOU_refl |].
        intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
      - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
        eapply s1_cps_cfg_bind.
        + apply refine_prov_to_s1_cps.
          exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                   ("Argument of " ++ fname ++ " violates noundef.")%string
                   args U0 P0 G σ1_in σ2_in
                   ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv0).
        + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
          eapply s1_cps_cfg_bind.
          * apply refine_prov_to_s1_cps.
            exact (push_call_frame_stage1_sim ctx1 ctx2 d d args1 U0 P0 G
                     σ1_in σ2_in sf_c1 sf_c2 fstk_c1 fstk_c2 g0 Logic.eq_refl Hinv0).
          * intros U_pf s1_pf varg1 s2_pf varg2 _
              (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
            fold fs0 in Htf_pf.
            set (sf0 := {| stack_vars := init_local_env bs;
                           stack_exc  := None;
                           stack_loc  := Some ""%string |}).
            set (fstk1 := sf_c1 :: fstk_c1).
            set (fstk2 := sf_c2 :: fstk_c2).
            assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
              by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
            assert (Hsafe_sf0 :
                      safe_locals_env (pr_va :: P0)
                        (m2r_collect_unique_allocas
                           (df_args d ++ flat_map full_block_defs (blks (df_instrs d)))
                           (blks (df_instrs d)))
                        (stack_vars sf0))
              by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) (df_args d) (blks (df_instrs d))
                                  _ args1 bs vs Ecomb (fun _ H => H)))).
            eapply s1_cps_cfg_bind with
              (RA := exc_post
                       (s1_unprom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                       (fun U_e s1_e s2_e v1 v2 =>
                          v1 = v2 /\
                          s1_unprom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_e s1_e s2_e)).
            -- change (interp_cfg_model ctx1
                         (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1)))
                         (σ1_pf, ((sf0, fstk1), g0)))
                 with (interp_cfg_exc ctx1
                         (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1))
                         (σ1_pf, ((sf0, fstk1), g0))).
               change (interp_cfg_model ctx2
                         (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1)))
                         (σ2_pf, ((sf0, fstk2), g0)))
                 with (interp_cfg_exc ctx2
                         (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1))
                         (σ2_pf, ((sf0, fstk2), g0))).
               unfold denote_cfg_map.
               eapply s1_cps_cfg_exc_bind with
                 (RA := s1_unprom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2).
               ++ rewrite !denote_ocfg_map_eq_iter.
                  intros k_o1 k_o2 Hk_o.
                  assert (Hli0 :
                            s1_unprom_loop_inv d fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2
                              (pr_va :: U0) (σ1_pf, ((sf0, fstk1), g0)) (σ2_pf, ((sf0, fstk2), g0))
                              (init (df_instrs d), init (df_instrs d))).
                  { split; [apply incl_refl |].
                    exists (pr_va :: P0), σ1_pf, σ2_pf, sf0.
                    exact (conj (incl_refl _)
                             (conj Logic.eq_refl (conj Logic.eq_refl
                                (conj Hinv_pf (conj Htf_pf (conj Hgenv_pf Hsafe_sf0)))))). }
                  eapply (s1_iter_one_step
                            (s1_unprom_loop_inv d fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_unprom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_unprom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (ocfg_step_body (ocfg_map (blks (df_instrs d))) (Some varg1))
                            (ocfg_step_body (ocfg_map (blks (df_instrs d))) (Some varg1))
                            (pr_va :: U0) _ _ (init (df_instrs d), init (df_instrs d)) k_o1 k_o2).
                  ** exact (s1_unprom_block_body_cps d (Some varg1) fs0
                              (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2
                              (pr_va :: U0) _ _ _ Hd Hli0).
                  ** intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; left.
                     exists d, (Some varg1), fs0, (pr_va :: U0), (pr_va :: P0), G,
                            fstk1, fstk2, s1', s2', j', k_o1, k_o2.
                     exact (conj Hd (conj Hli' (conj Hk_o (conj Logic.eq_refl Logic.eq_refl)))).
                  ** exact Hk_o.
               ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ [<- Hexit_ocfg].
                  destruct r_ocfg1 as [bid_miss | uv_ret].
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_raise_both.
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                       exact (conj Logic.eq_refl Hexit_ocfg).
            -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
               assert (Hrv_unif :
                         rv1 = rv2 /\
                         s1_unprom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_rv s1_rv s2_rv).
               { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                   try contradiction; exact Hrv_post. }
               clear Hrv_post.
               destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e &
                                         HincP_e & -> & -> & Hinv_e & Htf_e & Hgenv_e)].
               eapply s1_cps_cfg_bind.
               ++ apply refine_prov_to_s1_cps.
                  exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e G
                           σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e).
               ++ intros U_pop s1_pop _ s2_pop _ _
                    (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & Hfs_pop).
                  apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
                  ** exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                              (dc_attrs (df_prototype d)) ret_attrs None fname args1 rv1
                              U_rv P_e G σ1_pop σ2_pop
                              ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv_pop).
                  ** intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                     exists P_e, σ1_pop, σ2_pop.
                     exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                              (conj (fun x Hx => HincP_e x (or_intror Hx))
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Logic.eq_refl
                                          (conj Hinv_pop (conj Hfs_pop Hgenv_e))))))).
    Qed.

    Local Lemma s1_prom_block_body_cps
      (sp : s1_prom_static)
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (Hwf : s1_prom_static_wf sp)
      (Hli : s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U s1 s2 j) :
      s1_cps s1_lfp
        (exc_post (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
           (fun U' s1' s2' lr1 lr2 =>
              match lr1, lr2 with
              | inl j1, inl j2 =>
                  j1 = j2 /\ s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U' s1' s2' j1
              | inr v1, inr v2 =>
                  s1_prom_rret fs0 U0 P0 G fstk1 fstk2 U' s1' s2' v1 v2
              | _, _ => False
              end))
        U
        (interp_cfg_exc ctx1 (ocfg_step_body (ocfg_map (blks (sps_c sp))) va j) s1)
        (interp_cfg_exc ctx2 (ocfg_step_body (ocfg_map (sps_blks' sp)) va j) s2).
    Proof using.
      set (c := sps_c sp) in *.
      set (fargs := sps_fargs sp) in *.
      set (p := sps_p sp) in *.
      set (dt := sps_dt sp) in *.
      set (init_reg := sps_init_reg sp) in *.
      set (avoid0 := sps_avoid0 sp) in *.
      set (safe_no_p := sps_safe_no_p sp) in *.
      set (end_map := sps_end_map sp) in *.
      unfold s1_prom_static_wf in Hwf; fold c p dt safe_no_p avoid0 in Hwf.
      destruct Hwf as (Hnd_bks & Hno_entry_pred & _ & _ & Hsc & Hbks_other & Hbks_p1 & Hall_p1).
      unfold s1_prom_loop_inv in Hli; fold c p dt init_reg avoid0 safe_no_p end_map in Hli.
      destruct Hli as (Hne_bs & HincU_l & (b_pred & Hin_pred & Hid_pred & Hsucc_pred) &
                       P_l & gs_l & σ1_l & σ2_l & sf1_l & sf2_l &
                       HincP_l & Hdt_l & Hlk_p_l & Hlk_end_l & -> & -> &
                       Hinv_l & Htf_l & Hgenv_l & Hsafe_l & Hvars_l).
      assert (Hsub_safe : forall q,
                In q safe_no_p ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))).
      { intros q Hq; unfold safe_no_p, sps_safe_no_p in Hq; fold fargs c p in Hq.
        apply filter_In in Hq as [Hq _]; exact Hq. }
      assert (Hsafe_av0 : incl safe_no_p avoid0)
        by (intros q Hq; unfold avoid0, sps_avoid0; fold fargs c; apply safe_locals_in_avoid0, Hsub_safe, Hq).
      assert (Hblk_uses_av0 : forall bk x, In bk (blks c) -> In x (full_block_uses bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0, sps_avoid0; fold fargs c;
            apply in_app_iff; right; exact (in_uses_in_cfg_all_ids c bk x Hbk Hx)).
      assert (Hblk_defs_av0 : forall bk x, In bk (blks c) -> In x (full_block_defs bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0, sps_avoid0; fold fargs c;
            apply in_app_iff; right; exact (in_defs_in_cfg_all_ids c bk x Hbk Hx)).
      assert (Hnd_end_map : NoDup (List.map fst end_map))
        by (unfold end_map, sps_end_map; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks).
      pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) (sps_pass1 sp) Hbks_p1)
        as [Hfb_none Hfb_some]; cbv zeta in Hfb_none, Hfb_some; fold end_map in Hfb_some.
      destruct j as [bf2 bs2]; cbn [fst snd] in *.
      unfold ocfg_step_body, sps_blks'; fold c dt init_reg.
      cbn [Monads.bind Monads.ret Monad_itree].
      rewrite !ScopeTheory.ocfg_map_find_block.
      destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur.
      - destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur) as [Hin_cur Hid_cur].
        destruct (Hfb_some bs2 bk_cur Efind_cur)
          as (phi_r & cd_cur' & end_r & Hin_p1_cur & Efind_cur').
        rewrite Efind_cur'.
        pose proof (Hall_p1 bk_cur phi_r cd_cur' end_r Hin_p1_cur)
          as (Hphi_nin0 & Hend_nin0 & Hcur_p1_spec).
        destruct (raw_id_eqb_spec (blk_id bk_cur) (init c)) as [Hbad | Hne_cur_id];
          [exfalso; congruence |].
        destruct Hcur_p1_spec as (av_in & av_out & Hinc_avin & Erw_cur).
        destruct (Hbks_other bk_cur Hin_cur Hne_cur_id) as [Hbk_cur_chk Hp_nd_bk_cur].
        unfold check_block_non_entry_for_slot in Hbk_cur_chk.
        rewrite !andb_true_iff, !negb_true_iff in Hbk_cur_chk.
        destruct Hbk_cur_chk as (((Hphi_np & Hcd_cur) & Htm_np) & Hni_cur).
        apply in_raw_ids_false in Hphi_np; apply in_raw_ids_false in Htm_np.
        set (preds_cur := List.filter (fun b_p => in_raw_ids (blk_id bk_cur) (m2r_block_succs b_p)) (blks c)).
        set (inc_cur := List.map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg)))) preds_cur).
        assert (Hassoc_cur :
                  assoc bf2 inc_cur =
                  Some (EXP_Ident (ID_Local (lookup_end_reg end_map bf2 init_reg)))).
        { apply m2r_assoc_nodup.
          - unfold inc_cur; rewrite map_map; cbn [fst].
            exact (m2r_nodup_map_filter blk_id _ (blks c) Hnd_bks).
          - unfold inc_cur; rewrite <- Hid_pred at 1 2.
            apply (in_map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg))))).
            unfold preds_cur; apply filter_In; split; [exact Hin_pred |].
            rewrite Hid_cur; apply in_raw_ids_spec, Hsucc_pred. }
        assert (Hphi_vars :
                  forall x, In x (flat_map m2r_phi_entry_uses (blk_phis bk_cur)) ->
                    Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l)).
        { intros x Hx; apply Hvars_l;
            [apply (Hblk_uses_av0 bk_cur x Hin_cur);
             apply in_flat_map in Hx as (pe & Hpe & Hx_pe);
             exact (m2r_phi_entry_uses_in_block bk_cur pe x Hpe Hx_pe)
            | intros ->; exact (Hphi_np Hx)]. }
        unfold denote_block; cbn [blk_phis blk_code blk_term]; fold preds_cur inc_cur.
        eapply s1_cps_cfg_exc_bind.
        + eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_phis_stage1_prom_sim ctx1 ctx2
                     (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                     bf2 phi_r (lookup_end_reg end_map bf2 init_reg)
                     dt inc_cur (blk_phis bk_cur) (DVALUE_Base (gs_db gs_l))
                     U σ1_l σ2_l sf1_l sf2_l fstk1 fstk2 g0
                     Hassoc_cur Hlk_end_l Hphi_vars).
          * intros U_ph s1_ph _ s2_ph _ _ (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
            assert (Hp_nin_dvs : ~ In p (List.map fst dvs)).
            { rewrite Hfst_dvs; intros Hp_in; apply Hp_nd_bk_cur.
              unfold full_block_defs; apply in_app_iff; left; exact Hp_in. }
            assert (Hphi_nin_dvs : ~ In phi_r (List.map fst dvs)).
            { rewrite Hfst_dvs; intros Hpr_in; apply Hphi_nin0.
              apply (Hblk_defs_av0 bk_cur phi_r Hin_cur).
              unfold full_block_defs; apply in_app_iff; left; exact Hpr_in. }
            assert (Hlk_p_ph :
                      Maps.lookup p (write_phi_dvs dvs (stack_vars sf1_l)) =
                      Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs_l)))).
            { rewrite (write_phi_dvs_lookup_not_in dvs _ p Hp_nin_dvs); exact Hlk_p_l. }
            assert (Hlk_phi_ph :
                      Maps.lookup phi_r
                        (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l)) =
                      Some (DVALUE_Base (gs_db gs_l))).
            { cbn [write_phi_dvs];
                rewrite (write_phi_dvs_lookup_not_in dvs _ phi_r Hphi_nin_dvs);
                apply lookup_add_eq. }
            assert (Hsafe_ph :
                      safe_locals_env P_l safe_no_p
                        (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
            { apply write_phi_dvs_safe_locals; [| exact Hsafe_l].
              intros q Hq [Heq_q | Hin_dvs].
              - subst q; exact (Hphi_nin0 (Hsafe_av0 _ Hq)).
              - rewrite Hfst_dvs in Hin_dvs.
                apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
                exact (unique_alloca_not_phi_def fargs (blks c) q Hnd_bks
                         (Hsub_safe q Hq) bk_cur q ph_q md_q Hin_cur Hpe_in Logic.eq_refl). }
            assert (Hvars_ph :
                      forall x, In x avoid0 -> x <> p ->
                        Maps.lookup x (write_phi_dvs dvs (stack_vars sf1_l)) =
                        Maps.lookup x (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
            { intros x Hx Hne; cbn [write_phi_dvs]; apply write_phi_dvs_lookup_agree.
              rewrite (lookup_add_neq x phi_r) by (intros ->; exact (Hphi_nin0 Hx)).
              exact (Hvars_l x Hx Hne). }
            assert (Hsplit_cur : blk_code bk_cur = [] ++ blk_code bk_cur ++ [])
              by (rewrite app_nil_r; reflexivity).
            assert (Huses_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (m2r_code_entry_uses im0) -> In x avoid0)
              by (intros im0 x Him0 Hx; apply (Hblk_uses_av0 bk_cur x Hin_cur);
                  eapply m2r_code_entry_uses_in_block; eassumption).
            assert (Hdefs_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
            { intros im0 x Him0 Hx; apply (Hblk_defs_av0 bk_cur x Hin_cur).
              unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
              apply in_flat_map; exists im0; split; [exact Him0 | destruct im0 as [[? ?] ?]; exact Hx]. }
            assert (Hp_nd_cd_cur : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk_cur))).
            { intros Hp_in; apply Hp_nd_bk_cur; unfold full_block_defs;
                apply in_app_iff; right; apply in_app_iff; left; exact Hp_in. }
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_rewrite_code_exc_cps
                        (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                        avoid0 fargs (blks c) bk_cur [] (blk_code bk_cur) []
                        safe_no_p p dt phi_r av_in cd_cur' end_r av_out
                        va va fs0 U P_l gs_l G σ1_l σ2_l
                        (upd_local_sf sf1_l (write_phi_dvs dvs (stack_vars sf1_l)))
                        (upd_local_sf sf2_l (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l)))
                        fstk1 fstk2
                        Hnd_bks Hin_cur Hsplit_cur Hsub_safe Hsafe_av0
                        Huses_cur Hdefs_cur Hp_nd_cd_cur Hcd_cur Erw_cur
                        Hinc_avin Hphi_nin0 Hsc
                        (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                           conj Logic.eq_refl
                             (conj (incl_tran HincU_l H1)
                                (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                   (ex_intro _ sf1_x (ex_intro _ sf2_x
                                      (conj (incl_tran HincP_l H2)
                                         (conj Logic.eq_refl (conj Logic.eq_refl
                                            (conj H5 (or_intror (ex_intro _ gs_x (conj H3 H4))))))))))))))
                        Hdt_l Hlk_p_ph Hlk_phi_ph Hinv_l Htf_l Hgenv_l Hsafe_ph Hvars_ph).
            -- intros U_cd s1_cd _ s2_cd _ _
                 (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                  HincU_cd & HincP_cd & _ & _ & Hdt_cd & Hlk_p_cd & Hlk_er_cd &
                  -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd).
               assert (HincU_c : incl U0 U_cd) by (exact (incl_tran HincU_l HincU_cd)).
               assert (HincP_c : incl P0 P_cd) by (exact (incl_tran HincP_l HincP_cd)).
               assert (Hlk_end_cur : lookup_end_reg end_map bs2 init_reg = end_r).
               { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                 unfold end_map, sps_end_map; rewrite <- Hid_cur.
                 exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_cur). }
               destruct (blk_term bk_cur) as [[iid_tc tm_cur] md_tc] eqn:Etm_cur.
               cbn [fst snd] in Hni_cur.
               assert (Htm_vars :
                         forall x, In x (full_term_uses tm_cur) ->
                           Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)).
               { intros x Hx; apply Hvars_cd.
                 - apply (Hblk_uses_av0 bk_cur x Hin_cur), m2r_term_entry_uses_in_block.
                   rewrite Etm_cur; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                 - intros ->; apply Htm_np; rewrite Etm_cur;
                     cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
               apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
               ++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                           (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                           iid_tc iid_tc tm_cur md_tc md_tc
                           U_cd σ1_cd σ2_cd sf1_cd sf2_cd fstk1 fstk2 g0
                           Hni_cur Htm_vars).
                  intros ex; refine (conj Logic.eq_refl (conj HincU_c _)).
                  exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
                  exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Hgenv_cd (or_intror (ex_intro _ gs_cd (conj Hinv_cd Htf_cd))))))).
               ++ intros U_t [s1_t res1_t] [s2_t res2_t].
                  destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                    try (intros H; exact H).
                  intros (-> & -> & -> & <- & Hsucc_cur).
                  exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
                  exact (conj HincU_c (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Logic.eq_refl (conj Hdt_cd (conj Hlk_p_cd
                             (conj Hlk_end_cur (conj Hlk_er_cd (conj Hinv_cd
                               (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd
                                 (conj Hvars_cd Hsucc_cur)))))))))))))).
        + intros U_bd s1_bd bd1 s2_bd bd2 _
            (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
             HincU_c & HincP_c & <- & -> & -> & Hdt_cd & Hlk_p_cd & Hlk_end_cur &
             Hlk_er_cd & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
          destruct bd1 as [bid_tgt | dv_cur].
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            assert (Hsucc_bk_cur : In bid_tgt (m2r_block_succs bk_cur))
              by (unfold m2r_block_succs; destruct (blk_term bk_cur) as [[? ?] ?]; exact Hsucc_cur).
            assert (Hne_tgt : bid_tgt <> init c).
            { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
              unfold m2r_all_succs; apply in_flat_map; exists bk_cur; split; assumption. }
            refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_c (conj _ _)))).
            -- exists bk_cur; exact (conj Hin_cur (conj Hid_cur Hsucc_bk_cur)).
            -- exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd; cbn [fst]; fold end_map init_reg.
               rewrite Hlk_end_cur.
               exact (conj HincP_c (conj Hdt_cd (conj Hlk_p_cd (conj Hlk_er_cd
                        (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd Hvars_cd)))))))))).
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hgenv_cd (or_intror (ex_intro _ gs_cd (conj Hinv_cd Htf_cd))))))).
      - rewrite (Hfb_none bs2 Efind_cur).
        apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU_l _)).
        exists P_l, σ1_l, σ2_l, sf1_l, sf2_l.
        exact (conj HincP_l (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Hgenv_l (or_intror (ex_intro _ gs_l (conj Hinv_l Htf_l))))))).
    Qed.

    Local Lemma s1_prom_denote_function_cps
      (df df' : definition dtyp (CFG.cfg dtyp))
      (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
      (U0 P0 : list N) (G : list ghost_slot)
      (σ1_in σ2_in : state)
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Htry : try_promote_slot_in_defn true df = Some df')
      (Hinv0 : stage1_mem_inv U0 P0 G σ1_in σ2_in)
      (Hgenv0 : genv_safe P0 g0) :
      s1_cps s1_lfp
        (s1_call_post U0 P0 G (Memory_stack_frame_stack (state_memory_stack σ2_in)) ls1 ls2)
        U0
        (interp_cfg_model ctx1 (denote_function df cc args) (σ1_in, (ls1, g0)))
        (interp_cfg_model ctx2 (denote_function df' cc args) (σ2_in, (ls2, g0))).
    Proof using.
      destruct ls1 as [sf_c1 fstk_c1], ls2 as [sf_c2 fstk_c2].
      unfold try_promote_slot_in_defn in Htry.
      set (fargs := df_args df) in *.
      set (c := df_instrs df) in *.
      destruct (m2r_nodup_ids (List.map blk_id (blks c))
                && negb (in_raw_ids (init c) (m2r_all_succs c))
                && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
      rewrite !andb_true_iff, negb_true_iff in Eg1.
      destruct Eg1 as [[Hnd_bks Hno_entry_pred] _].
      apply m2r_nodup_ids_spec in Hnd_bks.
      apply in_raw_ids_false in Hno_entry_pred.
      destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind_init;
        [| discriminate Htry].
      destruct (m2r_find_block_some_inv (blks c) (init c) b_init Efind_init)
        as [Hin_init Hid_init].
      destruct (m2r_is_empty (blk_phis b_init)) eqn:Ephis_init; [| discriminate Htry].
      apply m2r_is_empty_spec in Ephis_init.
      set (all_defs := fargs ++ flat_map full_block_defs (blks c)) in *.
      set (all_uses := flat_map full_block_uses (blks c)) in *.
      set (safe_locals := m2r_collect_unique_allocas all_defs (blks c)) in *.
      destruct (find_promotable_in_init_code true all_defs all_uses safe_locals
                  (init c) (blks c) b_init [] (blk_code b_init))
        as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
        [| discriminate Htry].
      pose proof (find_promotable_in_init_code_inv true all_defs all_uses safe_locals
                    (init c) (blks c) b_init [] (blk_code b_init)
                    pre_al al_ins post_al p dt Efind_al) as Hal_inv.
      cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
      set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals) in *.
      destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & Hanns_al & _) &
                           Hsc & Hcnt_p & _ & Hpre_chk & Hpost_chk & Hterm_p & Hni_init & Ebks_chk).
      apply in_raw_ids_false in Hterm_p.
      inversion Htry; subst df'; clear Htry.
      destruct (unique_def_code_split fargs (blks c) b_init pre_al p
                  (INSTR_Alloca dt anns_al) md_al post_al Hnd_bks Hin_init Hsplit_init Hcnt_p)
        as (_ & _ & _ & Hp_nd_post & _ & Hp_nd_other).
      assert (Hsub_safe : forall q, In q safe_no_p -> In q safe_locals)
        by (intros q Hq; apply filter_In in Hq as [Hq _]; exact Hq).
      assert (Hp_nin_safe : ~ In p safe_no_p).
      { intros Hp; apply filter_In in Hp as [_ Hp]; rewrite raw_id_eqb_refl in Hp; discriminate Hp. }
      set (avoid0 := fargs ++ cfg_all_ids c).
      assert (Hsafe_av0 : incl safe_no_p avoid0)
        by (intros q Hq; apply safe_locals_in_avoid0, Hsub_safe, Hq).
      assert (Hblk_uses_av0 : forall bk x, In bk (blks c) -> In x (full_block_uses bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_uses_in_cfg_all_ids c bk x Hbk Hx)).
      assert (Hblk_defs_av0 : forall bk x, In bk (blks c) -> In x (full_block_defs bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_defs_in_cfg_all_ids c bk x Hbk Hx)).
      set (c' := promote_slot_in_cfg fargs c b_init pre_al (IId p, INSTR_Alloca dt anns_al, md_al) post_al p dt).
      set (init_reg := fresh_name "m2r_init" avoid0).
      set (avoid1 := init_reg :: avoid0).
      set (phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1).
      set (avoid2 := phi_regs ++ avoid1).
      destruct (rewrite_code_for_slot p dt init_reg avoid2 post_al)
        as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
      set (init_op := (IId init_reg, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison), [])).
      set (init_code' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al').
      set (bk_phis := List.combine (blks c) phi_regs).
      destruct (rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code' avoid3 bk_phis)
        as [pass1_out avoid_out] eqn:Epass1.
      assert (Hc'_eq :
        c' = {| init := init c;
                blks := build_promoted_blocks (init c) dt init_reg (blks c) pass1_out;
                args := args c |}).
      { unfold c', promote_slot_in_cfg.
        fold avoid0 init_reg avoid1 phi_regs avoid2.
        rewrite Erw_post; fold init_op init_code' bk_phis.
        rewrite Epass1; reflexivity. }
      assert (Hinit_nin0 : ~ In init_reg avoid0) by apply fresh_name_not_in.
      assert (Hinc_av2 : incl avoid0 avoid2)
        by (intros z Hz; unfold avoid2, avoid1; apply in_app_iff; right; right; exact Hz).
      destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt init_reg avoid2 post_al
                  post_al' init_end_reg avoid3 Erw_post Hinc_av2 Hinit_nin0)
        as [Hav3 Hinit_er_nin0].
      assert (Hinc_av3 : incl avoid0 avoid3) by (eapply incl_tran; eassumption).
      assert (Hlen_pr : List.length (blks c) = List.length phi_regs)
        by (symmetry; apply fresh_names_length).
      assert (Hphis_nin0 : forall r, In r (List.map snd bk_phis) -> ~ In r avoid0).
      { unfold bk_phis; rewrite (combine_snd_eq _ _ Hlen_pr).
        intros r Hr Hin0; eapply (fresh_names_disjoint "m2r_phi" _ avoid1 r Hr); right; exact Hin0. }
      destruct (rewrite_non_entry_blocks_pass1_spec avoid0 (init c) p dt init_end_reg init_code'
                  avoid3 bk_phis pass1_out avoid_out Epass1 Hinc_av3 Hinit_er_nin0 Hphis_nin0)
        as (Hbks_p1 & _ & _ & Hall_p1).
      unfold bk_phis in Hbks_p1; rewrite (combine_fst_eq _ _ Hlen_pr) in Hbks_p1.
      set (sp := {| sps_fargs    := fargs;
                    sps_c        := c;
                    sps_b_init   := b_init;
                    sps_p        := p;
                    sps_dt       := dt;
                    sps_init_reg := init_reg;
                    sps_end_reg0 := init_end_reg;
                    sps_code0'   := init_code';
                    sps_pass1    := pass1_out |}).
      assert (Hwf : s1_prom_static_wf sp).
      { unfold s1_prom_static_wf; cbn [sps_c sps_b_init sps_p sps_dt sps_pass1 sps_code0' sps_end_reg0].
        unfold sps_safe_no_p, sps_avoid0; cbn [sps_fargs sps_c sps_p]; fold all_defs safe_locals safe_no_p avoid0.
        refine (conj Hnd_bks (conj Hno_entry_pred (conj Hin_init (conj Hid_init (conj Hsc (conj _ (conj Hbks_p1 Hall_p1))))))).
        intros bk Hbk Hne; split.
        - pose proof Ebks_chk as Hb; rewrite forallb_forall in Hb; specialize (Hb bk Hbk).
          destruct (raw_id_eqb_spec (blk_id bk) (init c)) as [Hbad | _]; [exfalso; congruence | exact Hb].
        - exact (Hp_nd_other bk Hbk (fun Heq => Hne (eq_trans Heq Hid_init))). }
      set (end_map := sps_end_map sp).
      assert (Hnd_end_map : NoDup (List.map fst end_map))
        by (unfold end_map, sps_end_map; cbn [sps_pass1]; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks).
      pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) pass1_out Hbks_p1)
        as [_ Hfb_some]; cbv zeta in Hfb_some; fold end_map in Hfb_some.
      unfold denote_function; cbn [df_prototype df_args df_instrs]; fold fargs c c'.
      destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
      set (fname := show_raw_id (dc_name (df_prototype df))).
      set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
      eapply s1_cps_cfg_bind.
      - apply refine_prov_to_s1_cps.
        eapply refine_cfg_EOU; [apply refine_EOU_refl |].
        intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
      - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
        eapply s1_cps_cfg_bind.
        + apply refine_prov_to_s1_cps.
          exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                   ("Argument of " ++ fname ++ " violates noundef.")%string
                   args U0 P0 G σ1_in σ2_in
                   ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv0).
        + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
          eapply s1_cps_cfg_bind.
          * apply refine_prov_to_s1_cps.
            exact (push_call_frame_stage1_sim ctx1 ctx2 df
                     {| df_prototype := df_prototype df; df_args := fargs; df_instrs := c' |}
                     args1 U0 P0 G σ1_in σ2_in sf_c1 sf_c2 fstk_c1 fstk_c2 g0
                     Logic.eq_refl Hinv0).
          * intros U_pf s1_pf varg1 s2_pf varg2 _
              (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
            fold fs0 in Htf_pf.
            set (sf0 := {| stack_vars := init_local_env bs;
                           stack_exc  := None;
                           stack_loc  := Some ""%string |}).
            set (fstk1 := sf_c1 :: fstk_c1).
            set (fstk2 := sf_c2 :: fstk_c2).
            assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
              by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
            assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
              by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                  args1 bs vs Ecomb Hsub_safe))).
            eapply s1_cps_cfg_bind with
              (RA := exc_post
                       (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                       (fun U_e s1_e s2_e v1 v2 =>
                          v1 = v2 /\
                          s1_prom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_e s1_e s2_e)).
            -- change (interp_cfg_model ctx1
                         (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                         (σ1_pf, ((sf0, fstk1), g0)))
                 with (interp_cfg_exc ctx1
                         (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                         (σ1_pf, ((sf0, fstk1), g0))).
               change (interp_cfg_model ctx2
                         (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                         (σ2_pf, ((sf0, fstk2), g0)))
                 with (interp_cfg_exc ctx2
                         (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                         (σ2_pf, ((sf0, fstk2), g0))).
               unfold denote_cfg_map; rewrite Hc'_eq; cbn [init blks].
               change (build_promoted_blocks (init c) dt init_reg (blks c) pass1_out)
                 with (sps_blks' sp).
               eapply s1_cps_cfg_exc_bind with
                 (RA := s1_prom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2).
               ++ rewrite !denote_ocfg_map_eq_iter.
                  intros k_o1 k_o2 Hk_o.
                  eapply (s1_iter_one_step
                            (s1_prom_loop_inv sp fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_prom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (ocfg_step_body (ocfg_map (blks c)) (Some varg1))
                            (ocfg_step_body (ocfg_map (sps_blks' sp)) (Some varg1))
                            (pr_va :: U0)
                            (σ1_pf, ((sf0, fstk1), g0))
                            (σ2_pf, ((sf0, fstk2), g0))
                            (init c, init c) k_o1 k_o2).
                  ** destruct (Hfb_some (init c) b_init Efind_init)
                       as (phi_init & cd_init & end_init & Hin_p1_init & Efind_init').
                     pose proof (Hall_p1 b_init phi_init cd_init end_init Hin_p1_init)
                       as (_ & _ & Hinit_p1_spec).
                     rewrite Hid_init, raw_id_eqb_refl in Hinit_p1_spec, Efind_init'.
                     destruct Hinit_p1_spec as [-> ->].
                     assert (Hlk_end_init : lookup_end_reg end_map (init c) init_reg = init_end_reg).
                     { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                       unfold end_map, sps_end_map; cbn [sps_pass1]; rewrite <- Hid_init.
                       exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_init). }
                     unfold ocfg_step_body, sps_blks'; cbn [sps_c sps_dt sps_init_reg sps_pass1 Monads.bind Monads.ret Monad_itree].
                     rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
                     rewrite ScopeTheory.ocfg_map_find_block, Efind_init'.
                     unfold denote_block; cbn [blk_phis blk_code blk_term]; rewrite Ephis_init.
                     eapply s1_cps_obs_eq;
                       [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                           (eq_itree_clo_bind _ _ _ _ Logic.eq
                                              (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                                 (fun _ _ <- => Logic.eq_refl)) (fun _ _ <- => Logic.eq_refl)))
                       | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                            (eq_itree_clo_bind _ _ _ _ Logic.eq
                                               (eq_itree_clo_bind _ _ _ _ Logic.eq (denote_phis_nil_eq (init c))
                                                  (fun _ _ <- => Logic.eq_refl)) (fun _ _ <- => Logic.eq_refl))) |].
                     eapply s1_cps_obs_eq;
                       [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                       | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                     eapply s1_cps_obs_eq;
                       [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_ret_l _ _))
                       | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_ret_l _ _)) |].
                     rewrite Hsplit_init; unfold init_code'.
                     eapply s1_cps_cfg_exc_bind.
                     --- eapply s1_cps_obs_eq;
                           [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                               (eq_itree_clo_bind _ _ _ _ Logic.eq
                                                  (denote_code_app_eq pre_al _ (Some varg1))
                                                  (fun _ _ <- => Logic.eq_refl)))
                           | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                                (eq_itree_clo_bind _ _ _ _ Logic.eq
                                                   (denote_code_app_eq pre_al _ (Some varg1))
                                                   (fun _ _ <- => Logic.eq_refl))) |].
                         eapply s1_cps_cfg_exc_bind.
                         +++ assert (Hsplit_pre :
                                       blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                               by exact Hsplit_init.
                             exact (s1_other_code_exc_cps
                                      (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                      (fun s => top_frame_unprom_from fs0 G (state_memory_stack s))
                                      fargs (blks c) b_init [] pre_al
                                      ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                                      safe_no_p p (Some varg1) (Some varg1)
                                      (pr_va :: U0) (pr_va :: P0) G σ1_pf σ2_pf sf0 sf0 fstk1 fstk2
                                      Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
                                      (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs) HT)
                                      (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                                         top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs)
                                           (top_frame_unprom_add_ptrs fs0 G ptrs _ HT Hdisj))
                                      (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                                         conj Logic.eq_refl
                                           (conj H1
                                              (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                                 (ex_intro _ sf1_x (ex_intro _ sf2_x
                                                    (conj H2
                                                       (conj Logic.eq_refl (conj Logic.eq_refl
                                                          (conj H5 (or_introl (conj H3 H4)))))))))))))
                                      Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
                         +++ intros U_pre s1_pre _ s2_pre _ _
                               (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
                                HincU_pre & HincP_pre & _ & _ & -> & -> &
                                Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & Heq_sf_pre).
                             pose proof (Heq_sf_pre Logic.eq_refl) as ->.
                             assert (Econs_l :
                                       @denote_code (@ParamsV IP IPT)
                                         ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al) (Some varg1) ≅
                                       ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                         (fun _ => denote_code post_al (Some varg1)))
                               by reflexivity.
                             assert (Econs_r :
                                       @denote_code (@ParamsV IP IPT)
                                         ((IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al') (Some varg1) ≅
                                       ITree.bind
                                         (ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                            (fun _ => denote_instr init_op (Some varg1)))
                                         (fun _ => denote_code post_al' (Some varg1))).
                             { unfold denote_code; cbn [loop_monad]; symmetry; apply Eqit.bind_bind. }
                             eapply s1_cps_obs_eq;
                               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                                   (eq_itree_clo_bind _ _ _ _ Logic.eq Econs_l (fun _ _ <- => Logic.eq_refl)))
                               | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                                    (eq_itree_clo_bind _ _ _ _ Logic.eq Econs_r (fun _ _ <- => Logic.eq_refl))) |].
                             eapply s1_cps_obs_eq;
                               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                               | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                             eapply s1_cps_cfg_exc_bind.
                             *** apply refine_prov_to_s1_cps.
                                 exact (stage1_prom_alloca_init_exc_sim ctx1 ctx2
                                          (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                          p init_reg dt anns_al md_al (Some varg1) (Some varg1)
                                          fs0 U_pre P_pre G σ1_pre σ2_pre sf2_pre sf2_pre fstk1 fstk2 g0
                                          Hsc Hanns_al Hinv_pre Htf_pre).
                             *** intros U_al s1_al _ s2_al _ _
                                   (gs0 & σ1_al & σ2_al & _ & -> & _ & _ & Hdt0 & Hdb0 &
                                    -> & -> & Hinv_al & Htf_al).
                                 assert (HincU_al : incl (pr_va :: U0) (gs_pr gs0 :: U_pre))
                                   by (intros x Hx; right; exact (HincU_pre x Hx)).
                                 assert (Hlk_p_al :
                                           Maps.lookup p (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                           Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))))
                                   by apply lookup_add_eq.
                                 assert (Hlk_init_al :
                                           Maps.lookup init_reg
                                             (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                                (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre))) =
                                           Some (DVALUE_Base (gs_db gs0)))
                                   by (rewrite Hdb0; apply lookup_add_eq).
                                 assert (Hsafe_al :
                                           safe_locals_env P_pre safe_no_p
                                             (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                                (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)))).
                                 { apply safe_locals_env_add_other;
                                     [intros Hs; exact (Hinit_nin0 (Hsafe_av0 _ Hs)) |].
                                   apply safe_locals_env_add_other; [exact Hp_nin_safe | exact Hsafe_pre]. }
                                 assert (Hvars_al :
                                           forall x, In x avoid0 -> x <> p ->
                                             Maps.lookup x (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                             Maps.lookup x (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre))))
                                   by (intros x Hx _; rewrite (lookup_add_neq x init_reg)
                                         by (intros ->; exact (Hinit_nin0 Hx)); reflexivity).
                                 assert (Hsplit_post :
                                           blk_code b_init = (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) ++ post_al ++ [])
                                   by (rewrite <- app_assoc, app_nil_r; exact Hsplit_init).
                                 assert (Huses_post : forall im0 x, In im0 post_al -> In x (m2r_code_entry_uses im0) -> In x avoid0).
                                 { intros im0 x Him0 Hx; apply (Hblk_uses_av0 b_init x Hin_init).
                                   eapply m2r_code_entry_uses_in_block; [| exact Hx].
                                   rewrite Hsplit_init; apply in_app_iff; right; right; exact Him0. }
                                 assert (Hdefs_post : forall im0 x, In im0 post_al -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
                                 { intros im0 x Him0 Hx; apply (Hblk_defs_av0 b_init x Hin_init).
                                   unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
                                   rewrite Hsplit_init; apply in_flat_map; exists im0; split;
                                     [apply in_app_iff; right; right; exact Him0
                                     | destruct im0 as [[? ?] ?]; exact Hx]. }
                                 eapply s1_cps_cfg_exc_bind.
                                 ---- exact (s1_rewrite_code_exc_cps
                                               (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                               avoid0 fargs (blks c) b_init
                                               (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                                               safe_no_p p dt init_reg avoid2 post_al' init_end_reg avoid3
                                               (Some varg1) (Some varg1) fs0 (gs_pr gs0 :: U_pre) P_pre gs0 G
                                               σ1_al σ2_al _ _ fstk1 fstk2
                                               Hnd_bks Hin_init Hsplit_post Hsub_safe Hsafe_av0
                                               Huses_post Hdefs_post Hp_nd_post Hpost_chk Erw_post
                                               Hinc_av2 Hinit_nin0 Hsc
                                               (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                                                  conj Logic.eq_refl
                                                    (conj (incl_tran HincU_al H1)
                                                       (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                                          (ex_intro _ sf1_x (ex_intro _ sf2_x
                                                             (conj (incl_tran HincP_pre H2)
                                                                (conj Logic.eq_refl (conj Logic.eq_refl
                                                                   (conj H5 (or_intror (ex_intro _ gs_x (conj H3 H4))))))))))))))
                                               Hdt0 Hlk_p_al Hlk_init_al
                                               Hinv_al Htf_al Hgenv_pre Hsafe_al Hvars_al).
                                 ---- intros U_post s1_post _ s2_post _ _
                                        (P_post & gs_post & σ1_post & σ2_post & sf1_post & sf2_post &
                                         HincU_post & HincP_post & _ & _ & Hdt_post & Hlk_p_post & Hlk_er_post &
                                         -> & -> & Hinv_post & Htf_post & Hgenv_post & Hsafe_post & Hvars_post).
                                      assert (HincU_p : incl (pr_va :: U0) U_post)
                                        by (exact (incl_tran HincU_al HincU_post)).
                                      assert (HincP_p : incl (pr_va :: P0) P_post)
                                        by (exact (incl_tran HincP_pre HincP_post)).
                                      destruct (blk_term b_init) as [[iid_tm tm_init] md_tm] eqn:Etm_init.
                                      cbn [fst snd] in Hni_init.
                                      assert (Htm_vars : forall x,
                                                In x (full_term_uses tm_init) ->
                                                Maps.lookup x (stack_vars sf1_post) = Maps.lookup x (stack_vars sf2_post)).
                                      { intros x Hx; apply Hvars_post.
                                        - apply (Hblk_uses_av0 b_init x Hin_init), m2r_term_entry_uses_in_block.
                                          rewrite Etm_init; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                                        - intros ->; apply Hterm_p; rewrite Etm_init;
                                            cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                      apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
                                      ++++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                                                    (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                                    iid_tm iid_tm tm_init md_tm md_tm
                                                    U_post σ1_post σ2_post sf1_post sf2_post fstk1 fstk2 g0
                                                    Hni_init Htm_vars).
                                           intros ex; refine (conj Logic.eq_refl (conj HincU_p _)).
                                           exists P_post, σ1_post, σ2_post, sf1_post, sf2_post.
                                           exact (conj HincP_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                    (conj Hgenv_post (or_intror (ex_intro _ gs_post (conj Hinv_post Htf_post))))))).
                                      ++++ intros U_t [s1_t res1_t] [s2_t res2_t].
                                           destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                             try (intros H; exact H).
                                           intros (-> & -> & -> & <- & Hsucc).
                                           exists P_post, gs_post, σ1_post, σ2_post, sf1_post, sf2_post.
                                           exact (conj HincU_p (conj HincP_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                    (conj Logic.eq_refl (conj Hdt_post (conj Hlk_p_post
                                                      (conj Hlk_er_post (conj Hinv_post (conj Htf_post
                                                        (conj Hgenv_post (conj Hsafe_post (conj Hvars_post Hsucc))))))))))))).
                     --- intros U_b1 s1_b1 bd1 s2_b1 bd2 _
                           (P_b1 & gs_b1 & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
                            HincU_b1 & HincP_b1 & <- & -> & -> & Hdt_b1 & Hlk_p_b1 & Hlk_er_b1 &
                            Hinv_b1 & Htf_b1 & Hgenv_b1 & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
                         destruct bd1 as [bid_next | dv_ret].
                         +++ apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                             assert (Hsucc_init : In bid_next (m2r_block_succs b_init))
                               by (unfold m2r_block_succs; destruct (blk_term b_init) as [[? ?] ?]; exact Hsucc_b1).
                             assert (Hne_init : bid_next <> init c).
                             { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
                               unfold m2r_all_succs; apply in_flat_map; exists b_init; split; assumption. }
                             refine (conj Logic.eq_refl _).
                             unfold s1_prom_loop_inv; cbn [sps_c sps_dt sps_p sps_init_reg fst snd]; fold end_map.
                             unfold sps_safe_no_p, sps_avoid0; cbn [sps_fargs sps_c sps_p]; fold all_defs safe_locals safe_no_p avoid0.
                             refine (conj Hne_init (conj HincU_b1 (conj _ _))).
                             *** exists b_init; exact (conj Hin_init (conj Hid_init Hsucc_init)).
                             *** exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                                 rewrite Hlk_end_init.
                                 exact (conj HincP_b1 (conj Hdt_b1 (conj Hlk_p_b1 (conj Hlk_er_b1
                                          (conj Logic.eq_refl (conj Logic.eq_refl
                                            (conj Hinv_b1 (conj Htf_b1 (conj Hgenv_b1
                                              (conj Hsafe_b1 Hvars_b1)))))))))).
                         +++ apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                             refine (conj Logic.eq_refl (conj HincU_b1 _)).
                             exists P_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                             exact (conj HincP_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                      (conj Hgenv_b1 (or_intror (ex_intro _ gs_b1 (conj Hinv_b1 Htf_b1))))))).
                  ** intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; right.
                     exists sp, (Some varg1), fs0, (pr_va :: U0), (pr_va :: P0), G,
                            fstk1, fstk2, s1', s2', j', k_o1, k_o2.
                     exact (conj Hwf (conj Hli' (conj Hk_o (conj Logic.eq_refl Logic.eq_refl)))).
                  ** exact Hk_o.
               ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ [<- Hexit_ocfg].
                  destruct r_ocfg1 as [bid_miss | uv_ret].
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_raise_both.
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                       exact (conj Logic.eq_refl Hexit_ocfg).
            -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
               assert (Hrv_unif :
                         rv1 = rv2 /\
                         s1_prom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_rv s1_rv s2_rv).
               { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                   try contradiction; exact Hrv_post. }
               clear Hrv_post.
               destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e &
                                         HincP_e & -> & -> & Hgenv_e & Hcase_e)].
               assert (Hpop :
                         refine_prov
                           (fun U' '(s1', r1) '(s2', r2) =>
                              exists σ1' σ2',
                                U' = U_rv /\ r1 = tt /\ r2 = tt /\
                                s1' = (σ1', ((sf_c1, fstk_c1), g0)) /\
                                s2' = (σ2', ((sf_c2, fstk_c2), g0)) /\
                                stage1_mem_inv U_rv P_e G σ1' σ2' /\
                                Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
                           U_rv
                           (interp_cfg_model ctx1 pop_call_frame (σ1_e, ((sf1_e, sf_c1 :: fstk_c1), g0)))
                           (interp_cfg_model ctx2 pop_call_frame (σ2_e, ((sf2_e, sf_c2 :: fstk_c2), g0)))).
               { destruct Hcase_e as [[Hinv_e Htf_e] | (gs_e & Hinv_e & Htf_e)].
                 - exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e G
                            σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e).
                 - exact (pop_call_frame_stage1_prom_sim ctx1 ctx2 fs0 U_rv P_e gs_e G
                            σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e). }
               eapply s1_cps_cfg_bind; [apply refine_prov_to_s1_cps, Hpop |].
               intros U_pop s1_pop _ s2_pop _ _
                 (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & Hfs_pop).
               apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
               ++ exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                           (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                           U_rv P_e G σ1_pop σ2_pop
                           ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv_pop).
               ++ intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                  exists P_e, σ1_pop, σ2_pop.
                  exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                           (conj (fun x Hx => HincP_e x (or_intror Hx))
                              (conj Logic.eq_refl
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Hinv_pop (conj Hfs_pop Hgenv_e))))))).
    Qed.

    Local Lemma s1_phi_step (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_phi s1_lfp U t1 t2 ->
      m2r_paco s1_lfp U t1 t2.
    Proof using Hctx.
      intros [Hcall | [Hunp | Hprom]].
      - destruct Hcall as (dt & cc & fv & vs & P & G & σ1 & σ2 & ls1 & ls2 & k1 & k2 &
                           Hinv & Hg & Hk & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        revert k1 k2 Hk;
          change (s1_cps s1_lfp
                    (s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2)
                    U
                    (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) (σ1, (ls1, g0)))
                    (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) (σ2, (ls2, g0)))).
        unfold mrec_ctx; cbn [Monads.bind Monad_itree].
        destruct fv as [db | |];
          [| eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
               [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]
          | eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
               [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]].
        destruct db as [addr | ? ? | ? | ? | ? | ? ? | |];
          try (eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
               [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]).
        + cbn [check_callee].
          destruct ((ptr_to_int addr =? ptr_to_int null)%Z).
          * cbn [EOU_to_itree].
            eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
              [apply refine_prov_to_s1_cps, refine_cfg_raiseUB_l | intros _ _ _ _ _ _ []].
          * cbn [EOU_to_itree lookup_defn].
            eapply s1_cps_obs_eq;
              [symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l
              | symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l |].
            pose proof (Hctx (ptr_to_int addr)) as Hlk.
            destruct (lookup (ptr_to_int addr) ctx1) as [f1 |],
                     (lookup (ptr_to_int addr) ctx2) as [f2 |];
              inversion Hlk as [? ? Hf12 |]; subst.
            -- destruct Hf12 as [[-> ->] | [(d & Hd & -> & ->) | (df & df' & Htry & -> & ->)]].
               ++ apply refine_prov_to_s1_cps; eapply refine_prov_weaken;
                    [apply putchar_denotation_stage1_cfg_sim |].
                  intros U' [s1' r1] [s2' r2] (-> & -> & -> & <-).
                  exists P, σ1, σ2.
                  exact (conj (incl_refl U) (conj (incl_refl P)
                           (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                             (conj Hinv (conj Logic.eq_refl Hg))))))).
               ++ exact (s1_unprom_denote_function_cps d cc vs U P G σ1 σ2 ls1 ls2 Hd Hinv Hg).
               ++ exact (s1_prom_denote_function_cps df df' cc vs U P G σ1 σ2 ls1 ls2 Htry Hinv Hg).
            -- apply refine_prov_to_s1_cps.
               exact (s1_external_call_cfg_sim dt (DVALUE_Base (DVALUE_Pointer addr)) vs
                        U P G σ1 σ2 ls1 ls2 Hinv Hg).
        + cbn [check_callee EOU_to_itree].
          eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
            [apply refine_prov_to_s1_cps, refine_cfg_raiseUB_l | intros _ _ _ _ _ _ []].
      - destruct Hunp as (d & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                          k_out1 & k_out2 & Hd & Hli & Hk_out & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        pose proof (proj1 Hli) as Hinc0.
        rewrite !denote_ocfg_map_eq_iter.
        eapply (s1_iter_one_step
                  (s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2)
                  (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                  (s1_unprom_rret fs0 U0 P0 G fstk1 fstk2)
                  (ocfg_step_body (ocfg_map (blks (df_instrs d))) va)
                  (ocfg_step_body (ocfg_map (blks (df_instrs d))) va)
                  U s1 s2 j k_out1 k_out2).
        + exact (s1_unprom_block_body_cps d va fs0 U0 P0 G fstk1 fstk2 U s1 s2 j Hd Hli).
        + intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; left.
          exists d, va, fs0, U0, P0, G, fstk1, fstk2, s1', s2', j', k_out1, k_out2.
          rewrite !denote_ocfg_map_eq_iter.
          exact (conj Hd (conj Hli' (conj Hk_out (conj Logic.eq_refl Logic.eq_refl)))).
        + intros U' a1 a2 Hinc Ha; exact (Hk_out U' a1 a2 (incl_tran Hinc0 Hinc) Ha).
      - destruct Hprom as (sp & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                           k_out1 & k_out2 & Hwf & Hli & Hk_out & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        pose proof (proj1 (proj2 Hli)) as Hinc0.
        rewrite !denote_ocfg_map_eq_iter.
        eapply (s1_iter_one_step
                  (s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2)
                  (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                  (s1_prom_rret fs0 U0 P0 G fstk1 fstk2)
                  (ocfg_step_body (ocfg_map (blks (sps_c sp))) va)
                  (ocfg_step_body (ocfg_map (sps_blks' sp)) va)
                  U s1 s2 j k_out1 k_out2).
        + exact (s1_prom_block_body_cps sp va fs0 U0 P0 G fstk1 fstk2 U s1 s2 j Hwf Hli).
        + intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; right.
          exists sp, va, fs0, U0, P0, G, fstk1, fstk2, s1', s2', j', k_out1, k_out2.
          rewrite !denote_ocfg_map_eq_iter.
          exact (conj Hwf (conj Hli' (conj Hk_out (conj Logic.eq_refl Logic.eq_refl)))).
        + intros U' a1 a2 Hinc Ha; exact (Hk_out U' a1 a2 (incl_tran Hinc0 Hinc) Ha).
    Qed.

    Lemma s1_interproc_mrec_sim
      (P0 : list N) (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
      (args : list (@dvalue (@ParamsV IP IPT)))
      (U : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu : incl P0 U)
      (Hg : genv_safe P0 g0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov top_ans_post U
        (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt CC_Ccc fv args)) (σ1, (ls, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt CC_Ccc fv args)) (σ2, (ls, g0))).
    Proof using Hctx.
      apply m2r_paco_to_refine_prov.
      eapply (m2r_paco_acc (fun _ _ _ => False) s1_lfp).
      - intros r _ Hlr U' a1 a2 Hl.
        exact (m2r_paco_mon s1_lfp r Hlr U' a1 a2
                 (s1_phi_step U' a1 a2 (s1_lfp_unfold U' a1 a2 Hl))).
      - apply s1_lfp_fold; left.
        exists dt, CC_Ccc, fv, args, P0, ([] : list ghost_slot), σ1, σ2, ls, ls,
               (fun x : Ans => Ret x), (fun x : Ans => Ret x).
        refine (conj (stage1_equal_to_mem_inv U P0 σ1 σ2 Hpu Heq)
                 (conj Hg (conj _ (conj (Eqit.bind_ret_r _) (Eqit.bind_ret_r _))))).
        intros U' [s1' rv1] [s2' rv2] _ (P' & σ1' & σ2' & _ & _ & Heq_rv & _).
        apply m2r_paco_fold, RP_Step; exact Heq_rv.
    Qed.

  End InterprocKnot.

  Lemma interproc_module_defs_refines (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hnoputs : negb (in_raw_ids (Name "puts"%string) (List.map dc_name (m_declarations M1))) = true)
    (Hdefs : Forall2
               (fun d1 d2 =>
                  dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                  s1_fn_entry_rel (denote_function d1) (denote_function d2))
               (m_definitions M1) (m_definitions M2)) :
    prog_refines M1 M2.
  Proof using.
    eapply (module_defs_refines_gen (fun _ _ => s1_fn_entry_rel) M1 M2 Hbg Hdecls).
    - intros _ _ _; exact Hdefs.
    - intros _ _ _.
      pose proof (library_functions_no_puts_only_putchar (m_declarations M1) Hnoputs) as Hlf.
      induction Hlf as [| lib libs Hhd _ IH]; constructor;
        [left; exact (conj Hhd Hhd) | exact IH].
    - intros P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls Hctx Hpu Hg Heq.
      exact (s1_interproc_mrec_sim g0 ctx1 ctx2 Hctx P0 dt fv args U σ1 σ2 ls Hpu Hg Heq).
  Qed.

  Lemma build_global_environment_defs_eq
    (M : CFG.mcfg dtyp) (defs' : list (definition dtyp (CFG.cfg dtyp)))
    (Hproto : List.map df_prototype defs' = List.map df_prototype (m_definitions M))
    (Hba : flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
           flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) (m_definitions M)) :
    let M' := {| m_name         := m_name M;
                 m_target       := m_target M;
                 m_datalayout   := m_datalayout M;
                 m_type_defs    := m_type_defs M;
                 m_globals      := m_globals M;
                 m_declarations := m_declarations M;
                 m_definitions  := defs' |} in
    @build_global_environment (@ParamsV IP IPT) M' =
    @build_global_environment (@ParamsV IP IPT) M.
  Proof using.
    intros M'.
    assert (Hmba : mcfg_block_addresses M' = mcfg_block_addresses M)
      by (unfold mcfg_block_addresses; cbn [m_globals m_definitions]; rewrite Hba; reflexivity).
    unfold build_global_environment; rewrite Hmba;
      cbn [m_declarations m_globals m_definitions]; rewrite Hproto; reflexivity.
  Qed.

  Lemma leaf_ctx_fn_rel_refl_list
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
      defs defs.
  Proof using.
    induction defs as [| d rest IH]; constructor; [| exact IH].
    split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function d))].
  Qed.

  Lemma s1_fn_entry_rel_refl_safe_list
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    forallb m2r_defn_mem_safe defs = true ->
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         s1_fn_entry_rel (denote_function d1) (denote_function d2))
      defs defs.
  Proof using.
    induction defs as [| d rest IH]; cbn [forallb]; [intros _; constructor |].
    intros Hsafe; rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hd Hrest].
    constructor; [| exact (IH Hrest)].
    split; [reflexivity | right; left; exists d; exact (conj Hd (conj Logic.eq_refl Logic.eq_refl))].
  Qed.

  Lemma promote_first_in_defs_leaf_spec
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    promote_first_in_defs false defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    (forall P0 g0,
       genv_safe P0 g0 ->
       Forall2
         (fun d1 d2 =>
            dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
            leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
         defs defs').
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Hprom;
      cbn [promote_first_in_defs] in Hprom; [discriminate Hprom |].
    destruct (try_promote_slot_in_defn false df) as [df' |] eqn:Etry.
    - inversion Hprom; subst defs'; clear Hprom.
      destruct (promote_slot_in_defn_block_addresses false df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| apply leaf_ctx_fn_rel_refl_list].
      split; [rewrite Hpr; reflexivity | exact (try_promote_slot_leaf_denote_function_sim P0 g0 df df' Hg0 Etry)].
    - destruct (promote_first_in_defs false rest) as [rest' |] eqn:Erest;
        [| discriminate Hprom].
      inversion Hprom; subst defs'; clear Hprom; cbn [option_map List.map flat_map].
      destruct (IH rest' Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| exact (Hrel P0 g0 Hg0)].
      split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function df))].
  Qed.

  Lemma promote_first_in_defs_interproc_spec
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    forallb m2r_defn_mem_safe defs = true ->
    promote_first_in_defs true defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         s1_fn_entry_rel (denote_function d1) (denote_function d2))
      defs defs'.
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Hsafe Hprom;
      cbn [forallb promote_first_in_defs] in *; [discriminate Hprom |].
    rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hdf_safe Hrest_safe].
    destruct (try_promote_slot_in_defn true df) as [df' |] eqn:Etry.
    - inversion Hprom; subst defs'; clear Hprom.
      destruct (promote_slot_in_defn_block_addresses true df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      constructor; [| exact (s1_fn_entry_rel_refl_safe_list rest Hrest_safe)].
      split; [rewrite Hpr; reflexivity
             | right; right; exists df, df'; exact (conj Etry (conj Logic.eq_refl Logic.eq_refl))].
    - destruct (promote_first_in_defs true rest) as [rest' |] eqn:Erest;
        [| discriminate Hprom].
      inversion Hprom; subst defs'; clear Hprom; cbn [option_map List.map flat_map].
      destruct (IH rest' Hrest_safe Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      constructor; [| exact Hrel].
      split; [reflexivity
             | right; left; exists df; exact (conj Hdf_safe (conj Logic.eq_refl Logic.eq_refl))].
  Qed.

  Lemma elim_first_dead_alloca_in_defs_spec {IPWB : IPtrWellBehaved IP}
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    elim_first_dead_alloca_in_defs defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    (forall P0 g0,
       genv_safe P0 g0 ->
       Forall2
         (fun d1 d2 =>
            dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
            leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
         defs defs').
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Helim;
      cbn [elim_first_dead_alloca_in_defs] in Helim; [discriminate Helim |].
    destruct (try_elim_dead_alloca_in_defn df) as [df' |] eqn:Etry.
    - inversion Helim; subst defs'; clear Helim.
      destruct (elim_dead_alloca_in_defn_block_addresses df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| apply leaf_ctx_fn_rel_refl_list].
      split; [rewrite Hpr; reflexivity
             | exact (try_elim_dead_alloca_denote_function_sim P0 g0 df df' Hg0 Etry)].
    - destruct (elim_first_dead_alloca_in_defs rest) as [rest' |] eqn:Erest;
        [| discriminate Helim].
      inversion Helim; subst defs'; clear Helim; cbn [option_map List.map flat_map].
      destruct (IH rest' Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| exact (Hrel P0 g0 Hg0)].
      split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function df))].
  Qed.

End MemoryAndSerialization.


(** * 4. Top-Level Whole-Module Refinement Theorems *)

Theorem promote_slot_step_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (promote_slot_step_mcfg M).
Proof.
  intros IP IPT M.
  unfold promote_slot_step_mcfg.
  destruct (mcfg_no_inttoptr M) eqn:Eno_itp; [| apply prog_refines_refl].
  destruct (m2r_module_interproc_safe M) eqn:Eis.
  - unfold m2r_module_interproc_safe in Eis.
    rewrite !andb_true_iff in Eis; destruct Eis as [[[_ _] Hnoputs] Hsafe].
    destruct (promote_first_in_defs true (m_definitions M)) as [defs' |] eqn:Eprom;
      [| apply prog_refines_refl].
    destruct (promote_first_in_defs_interproc_spec (m_definitions M) defs' Hsafe Eprom)
      as (Hproto & Hba & Hrel).
    exact (interproc_module_defs_refines M _
             (build_global_environment_defs_eq M defs' Hproto Hba)
             Logic.eq_refl Hnoputs Hrel).
  - destruct (promote_first_in_defs false (m_definitions M)) as [defs' |] eqn:Eprom;
      [| apply prog_refines_refl].
    destruct (@promote_first_in_defs_leaf_spec IP IPT (m_definitions M) defs' Eprom)
      as (Hproto & Hba & Hrel).
    exact (leaf_module_defs_refines M _
             (build_global_environment_defs_eq M defs' Hproto Hba)
             Logic.eq_refl Hrel).
Qed.

Theorem promote_slot_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (promote_slot_iter fuel M).
Proof.
  intros IP IPT fuel.
  induction fuel as [| fuel' IH]; intros M; cbn [promote_slot_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans; [apply promote_slot_step_refines | apply IH].
Qed.

Theorem elim_dead_alloca_step_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (elim_dead_alloca_step_mcfg M).
Proof.
  intros IP IPT IPWB M.
  unfold elim_dead_alloca_step_mcfg.
  destruct (mcfg_no_inttoptr M); [| apply prog_refines_refl].
  destruct (elim_first_dead_alloca_in_defs (m_definitions M)) as [defs' |] eqn:Eelim;
    [| apply prog_refines_refl].
  destruct (@elim_first_dead_alloca_in_defs_spec IP IPT IPWB (m_definitions M) defs' Eelim)
    as (Hproto & Hba & Hrel).
  exact (leaf_module_defs_refines M _
           (build_global_environment_defs_eq M defs' Hproto Hba)
           Logic.eq_refl Hrel).
Qed.

Theorem elim_dead_alloca_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (elim_dead_alloca_iter fuel M).
Proof.
  intros IP IPT IPWB fuel.
  induction fuel as [| fuel' IH]; intros M; cbn [elim_dead_alloca_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans; [apply elim_dead_alloca_step_refines | apply IH].
Qed.

Theorem mem2reg_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (mem2reg_mcfg M).
Proof.
  intros IP IPT IPWB M.
  unfold mem2reg_mcfg.
  eapply prog_refines_trans;
    [apply promote_slot_iter_refines | apply elim_dead_alloca_iter_refines].
Qed.

Theorem mem2reg_mcfg_typ_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg typ),
    @prog_refines IP IPT (convert_types M) (mem2reg_mcfg_typ M).
Proof.
  intros IP IPT IPWB M.
  unfold mem2reg_mcfg_typ.
  apply mem2reg_mcfg_refines.
Qed.
