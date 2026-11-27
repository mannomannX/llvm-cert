(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Stack-Slot Promotion & Dead-Alloca Spec ([CertPasses.Mem2RegSpec])

    Purpose:
      Defines the computable Stage 1 scalar [alloca]-to-SSA promotion pass,
      Stage 2 reverse-order dead scalar [alloca] elimination, and the bounded
      top-level entry points [mem2reg_mcfg] and [mem2reg_mcfg_typ].

    Trust Contract & Fail-Closed Boundary:
      Extracted to OCaml. Purely syntactic, fail-closed transform over
      [CFG.mcfg dtyp] (default fuel 32); returns input unchanged whenever
      [mcfg_no_inttoptr], entry-block, or slot safety guards fail.

    Assumptions:
      Depends on [PassCommon] and [Vellvm] AST/semantics; zero custom axioms
      or [Admitted].

    Section Outline:
      1. Computable syntax inspectors and [m2r_module_interproc_safe].
      2. Stage 1: single-slot SSA promotion ([promote_slot_iter]).
      3. Stage 2: reverse-order dead scalar [alloca] elimination ([elim_dead_alloca_iter]).
      4. Top-level entry points ([mem2reg_mcfg], [mem2reg_mcfg_typ]). *)

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
  Structures.Functor
  Data.Monads.EitherMonad.

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
Import Logic.

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
  - destruct (raw_id_eqb x y) eqn:Exy; cbn; [apply raw_id_eqb_spec in Exy; subst y | apply raw_id_eqb_neq in Exy; rename Exy into Hne].
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

(** Exact flat LLVM-23-valid SSA replacement expressions for promoted [Store] and [Load] sites:
    - [mk_store_vec_exp] + [mk_store_ext_exp] evaluate [val_exp] at [Some dt] and check
      base-value well-formedness via [dvalue_to_dvalue_base] without nesting an instruction
      operator inside another instruction.
    - [mk_load_vec_exp] + [mk_load_cast_exp] construct a local [<1 x dt>] vector via
      [insertelement] and bitcast it to [dt] to deserialize through [memory_bytes_to_dvalue]
      without embedding local SSA names inside constant vector syntax. *)
Definition mk_store_vec_exp (dt : dtyp) (val_exp : exp dtyp) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  let i1_ty := DTYPE_Base (DTYPE_I 1) in
  OP_InsertElement (vec_ty, EXP_Poison) (dt, val_exp) (i1_ty, EXP_Bool false).

Definition mk_store_ext_exp (dt : dtyp) (vec_reg : local_id) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  let i1_ty := DTYPE_Base (DTYPE_I 1) in
  OP_ExtractElement (vec_ty, EXP_Ident (ID_Local vec_reg)) (i1_ty, EXP_Bool false).

Definition mk_load_vec_exp (dt : dtyp) (cur_reg : local_id) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  let i1_ty := DTYPE_Base (DTYPE_I 1) in
  OP_InsertElement (vec_ty, EXP_Poison) (dt, EXP_Ident (ID_Local cur_reg)) (i1_ty, EXP_Bool false).

Definition mk_load_cast_exp (dt : dtyp) (vec_reg : local_id) : exp dtyp :=
  let vec_ty := DTYPE_Array true 1%N dt in
  OP_Conversion CONV_Bitcast vec_ty (EXP_Ident (ID_Local vec_reg)) dt.

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
          let lv_reg := fresh_name "mlv" (p :: cur_reg :: avoid) in
          let '(rest', end_reg, avoid') :=
            rewrite_code_for_slot p dt cur_reg (lv_reg :: avoid) rest in
          ((IId lv_reg, INSTR_Op (mk_load_vec_exp dt cur_reg), []) ::
           (IId dst, INSTR_Op (mk_load_cast_exp dt lv_reg), []) :: rest',
           end_reg, avoid')
      | None =>
          match is_promotable_store_of p dt im with
          | Some val_exp =>
              let sv_reg := fresh_name "msv" (p :: avoid) in
              let st_reg := fresh_name "mst" (p :: sv_reg :: avoid) in
              let '(rest', end_reg, avoid') :=
                rewrite_code_for_slot p dt st_reg (st_reg :: sv_reg :: avoid) rest in
              ((IId sv_reg, INSTR_Op (mk_store_vec_exp dt val_exp), []) ::
               (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) :: rest',
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


