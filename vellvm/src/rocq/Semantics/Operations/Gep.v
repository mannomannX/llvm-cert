From Vellvm Require Import
  Utils
  Syntax
  VellvmIntegers
  EOU
  DynamicValues
  Params.
Open Scope Z.

Section GEP.
  Context {Pa : Params}.

  (** ** Get Element Pointer

      [getelementptr t, ptr a, i_1, ..., i_n] computes an address from [a] by
      a sequence of steps, one per index.  [gep_steps] lists them: for each
      index, its value and what it is scaled by.  The first index steps over
      whole objects of type [t]; each later one selects an element of the
      current aggregate type: an array or vector element (the index times
      the element size), or a struct field (its byte offset, scaled by 1).
      The address is [a] plus the sum of the steps ([gep_offset]), and the
      no-wrap flags are rules about the steps (see [gep_flags_violated]).
      A poison index makes the whole result poison.
   *)
  Fixpoint gep_steps_h (t:dtyp) (vs:list dvalue): EOUP (list (Z * Z)) :=
    match vs with
    | v :: vs' =>
        match v with
        | DVALUE_Base (DVALUE_I 8 i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-i8-indexable type")
            end
        | DVALUE_Base (DVALUE_I 32 i) =>
            let n := BinIntDef.Z.to_nat (unsigned i) in
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | DTYPE_Struct false ts =>
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    let end_of_prev_field := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + alloc_size_dtyp t)%N (firstn n ts) 0%N in
                    let offset := pad_to_align (dtyp_alignment t') end_of_prev_field in
                    cons (Z.of_N offset, 1) <$> gep_steps_h t' vs'
                end
            | DTYPE_Struct true ts =>
                let offset := fold_left (fun acc t => acc + alloc_size_dtyp t)%N
                                (firstn n ts) 0%N in
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    cons (Z.of_N offset, 1) <$> gep_steps_h t' vs'
                end
            | _ => raise_error ("non-i32-indexable type")
            end
        | DVALUE_Base (DVALUE_I 64 i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-i64-indexable type")
            end
        | DVALUE_Base (DVALUE_Iptr i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (to_Z i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-iptr-indexable type")
            end
        | DVALUE_Base (DVALUE_Poison) =>
            ret Pois
        | _ => raise_error "gep_steps_h: unsupported index type"
        end
    | [] => ret (NoPois [])
    end.

  Definition gep_steps (t:dtyp) (vs:list dvalue) : EOUP (list (Z * Z)) :=
    let first k vs' := cons (k, Z.of_N (alloc_size_dtyp t)) <$> gep_steps_h t vs' in
    match vs with
    | DVALUE_Base (DVALUE_I 8 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_I 32 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_I 64 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_Iptr i) :: vs' => first (to_Z i) vs'
    | DVALUE_Base (DVALUE_Poison)::_ => ret Pois
    | [] => raise_error "gep_steps: no indices"
    | _ => raise_error "gep_steps: unsupported index type"
    end.

  Definition gep_offset (steps : list (Z * Z)) : Z :=
    fold_left (fun off '(k, size) => off + k * size) steps 0.

  (** ** The no-wrap flags

      LangRef (getelementptr): with [nusw], [nuw], or [inbounds], "If any of
      the rules are violated, the result value is a poison value". *)

  (* The width of the pointer index type, in bits.  Vellvm's index type is
     the pointer size, also under the infinite-pointer parameters. *)
  Definition gep_index_bits : Z := 8 * Z.of_N pointer_size.

  Definition in_signed_index_range (x : Z) : bool :=
    (- 2 ^ (gep_index_bits - 1) <=? x) && (x <? 2 ^ (gep_index_bits - 1)).

  Definition in_unsigned_index_range (x : Z) : bool :=
    (0 <=? x) && (x <? 2 ^ gep_index_bits).

  (* LangRef [nusw]: the index fits the index type (trunc nsw); each
     index * size does not wrap (mul nsw); nor does each partial sum of the
     offsets (add nsw); nor does adding that sum to the address, truncated to
     the index type and read as unsigned.  [addr] is that truncated address
     and [off] the offset so far. *)
  Fixpoint gep_nusw_ok (addr off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let o := k * size in
        let off' := off + o in
        in_signed_index_range k && in_signed_index_range o
        && in_signed_index_range off' && in_unsigned_index_range (addr + off')
        && gep_nusw_ok addr off' steps'
    end.

  (* LangRef [nuw]: the same rules with every index and offset read as
     unsigned. *)
  Fixpoint gep_nuw_ok (addr off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let o := (k mod 2 ^ gep_index_bits) * size in
        let off' := off + o in
        in_unsigned_index_range o && in_unsigned_index_range off'
        && in_unsigned_index_range (addr + off')
        && gep_nuw_ok addr off' steps'
    end.

  (* The part of LangRef [inbounds] that does not need the bounds of an
     allocated object: nothing is allocated at address 0, and "the only
     pointer in bounds of the null pointer ... is the null pointer itself", so
     from a null base every step must stay at offset 0.  Being in bounds of
     a real allocated object is not checked. *)
  Fixpoint gep_inbounds_null_ok (off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let off' := off + k * size in
        (off' =? 0) && gep_inbounds_null_ok off' steps'
    end.

  (* Whether the flags make the result poison.  [inbounds] implies [nusw]. *)
  Definition gep_flags_violated (flags : gep_flags) (addr : Z) (steps : list (Z * Z)) : bool :=
    let a := addr mod 2 ^ gep_index_bits in
    ((gep_inbounds flags || gep_nusw flags) && negb (gep_nusw_ok a 0 steps))
    || (gep_nuw flags && negb (gep_nuw_ok a 0 steps))
    || (gep_inbounds flags && (addr =? 0) && negb (gep_inbounds_null_ok 0 steps)).

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a
     pointer, but no other pointer can be recursively followed.  The pointer
     sets the block into which we look, and the initial offset. *)
  (* TODO: This should take into account padding too... May break get_consecutive_ptrs and friends. *)
  Definition handle_gep_ptr (flags : gep_flags) (t:dtyp) (a:ptr) (vs:list dvalue) : EOUP ptr :=
    let ptr := ptr_to_int a in
    steps <- gep_steps t vs ;;
    if gep_flags_violated flags ptr steps
    then raise_ret Pois
    else NoPois <$> (int_to_ptr (ptr + gep_offset steps) (ptr_provenance a)).

  Lemma handle_gep_ptr_0 :
    forall (dt : dtyp) (p : ptr),
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr zero_iptr)] = ret p.
  Proof.
    intros dt p.
    unfold handle_gep_ptr; cbn.
    rewrite to_Z_0.
    replace (ptr_to_int p + 0 * Z.of_N (alloc_size_dtyp dt))%Z with (ptr_to_int p) by ring.
    rewrite int_to_ptr_ptr_to_int; auto.
  Qed.

  Lemma handle_gep_ptr_nil :
    forall flags (dt : dtyp) (p : ptr),
      handle_gep_ptr flags dt p [] = raise_error "gep_steps: no indices"%string.
  Proof.
    intros flags dt p.
    unfold handle_gep_ptr; cbn; auto.
  Qed.

  Lemma handle_gep_ptr_ix :
    forall (dt : dtyp) (p p' : ptr) ix,
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p' ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    unfold handle_gep_ptr in *; cbn in *.
    break_match_hyp; inv GEP.
    match goal with
    | H : _ = raise_ret p' |- _ => apply ptr_to_int_int_to_ptr in H; rewrite H
    end.
    ring.
  Qed.

  Lemma handle_gep_ptr_ix_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg ->
      exists msg',
        int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg'.
  Proof.
    intros dt p p' ix msg GEP.
    unfold handle_gep_ptr in *; cbn in *.
    exists msg.
    replace (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z
      with (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z by ring.
    break_match_hyp; inv GEP.
    auto.
  Qed.

  Lemma handle_gep_ptr_ix' :
    forall (dt : dtyp) (p p' : ptr) ix,
      ret p' = int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) ->
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p'.
  Proof.
    intros dt p p' ix IX.
    unfold handle_gep_ptr in *; cbn in *.
    replace (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z
      with (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z by ring.
    rewrite <- IX.
    reflexivity.
  Qed.

  Lemma handle_gep_ptr_ix'_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg ->
      exists msg', handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg'.
  Proof.
    intros dt p p' ix msg IX.
    unfold handle_gep_ptr in *; cbn in *.
    exists msg.
    replace (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z
      with (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z by ring.
    rewrite IX.
    auto.
  Qed.

  Lemma handle_gep_ptr_preserves_provenance :
    forall flags (dt : dtyp) ixs (p p' : ptr),
      handle_gep_ptr flags dt p ixs = ret p' ->
      ptr_provenance p = ptr_provenance p'.
  Proof.
    intros flags dt ixs p p' GEP.
    unfold handle_gep_ptr in GEP; cbn in GEP.
    repeat break_match_hyp_inv;
      cbn in *;
      symmetry;
      eapply int_to_ptr_provenance; eauto.
  Qed.

  Definition eval_gep (flags : gep_flags) (t:dtyp) (dv:dvalue) (vs:list dvalue) : EOU dvalue :=
    match dv with
    | DVALUE_Base (DVALUE_Pointer a) =>
        catch_pois (DVALUE_Base DVALUE_Poison)
          ((fun x => DVALUE_Base (DVALUE_Pointer x)) <$> handle_gep_ptr flags t a vs)
          ret
    | DVALUE_Base DVALUE_Poison => ret (DVALUE_Base DVALUE_Poison)
    | _ => raise_error "non-ptr"%string
    end.

  (** ** 64-Bit Modular Two's-Complement GEP Reassociation & Inbounds Theory *)

  Definition wrap_ptr64 (addr : Z) : Z :=
    addr mod (2 ^ 64).

  Lemma wrap_ptr64_range : forall addr : Z,
    0 <= wrap_ptr64 addr < 2 ^ 64.
  Proof.
    intros addr; unfold wrap_ptr64.
    apply Z.mod_pos_bound; reflexivity.
  Qed.

  Lemma wrap_ptr64_small : forall addr : Z,
    0 <= addr < 2 ^ 64 ->
    wrap_ptr64 addr = addr.
  Proof.
    intros addr H; unfold wrap_ptr64; apply Z.mod_small, H.
  Qed.

  Lemma gep_offset_fold_shift : forall steps init,
    fold_left (fun off '(k, size) => off + k * size) steps init = init + gep_offset steps.
  Proof.
    unfold gep_offset; intros steps.
    induction steps as [| [k sz] steps' IH]; intros init; cbn [fold_left]; [lia |].
    rewrite (IH (init + k * sz)), (IH (0 + k * sz)); lia.
  Qed.

  Lemma gep_offset_cons : forall k sz steps,
    gep_offset ((k, sz) :: steps) = k * sz + gep_offset steps.
  Proof.
    intros k sz steps; unfold gep_offset at 1; cbn [fold_left].
    rewrite gep_offset_fold_shift; lia.
  Qed.

  Lemma gep_offset_app : forall s1 s2,
    gep_offset (s1 ++ s2) = gep_offset s1 + gep_offset s2.
  Proof.
    intros s1 s2; unfold gep_offset at 1; rewrite fold_left_app.
    apply gep_offset_fold_shift.
  Qed.

  Lemma gep_offset_wrap64_reassoc : forall base off1 off2 : Z,
    wrap_ptr64 (wrap_ptr64 (base + off1) + off2) = wrap_ptr64 (base + (off1 + off2)).
  Proof.
    intros base off1 off2; unfold wrap_ptr64.
    pose proof (Z.div_mod (base + off1) (2 ^ 64) ltac:(discriminate)) as Hdm.
    replace (base + (off1 + off2))
      with (((base + off1) mod (2 ^ 64) + off2) + ((base + off1) / (2 ^ 64)) * (2 ^ 64))
      by lia.
    symmetry; apply Z_mod_plus_full.
  Qed.

  Lemma gep_steps_wrap64_reassoc : forall base steps1 steps2,
    wrap_ptr64 (wrap_ptr64 (base + gep_offset steps1) + gep_offset steps2) =
      wrap_ptr64 (base + gep_offset (steps1 ++ steps2)).
  Proof.
    intros base steps1 steps2; rewrite gep_offset_app.
    apply gep_offset_wrap64_reassoc.
  Qed.

  Lemma gep_inbounds_implies_wrap64_eq : forall base off : Z,
    0 <= base + off < 2 ^ 64 ->
    wrap_ptr64 (base + off) = base + off.
  Proof.
    intros base off H; apply wrap_ptr64_small, H.
  Qed.

  Lemma gep_nusw_ok_nonempty_range : forall steps addr off,
    steps <> [] ->
    gep_nusw_ok addr off steps = true ->
    in_unsigned_index_range (addr + (off + gep_offset steps)) = true.
  Proof.
    induction steps as [| [k sz] steps' IH]; intros addr off Hne Hok;
      [contradiction Hne; reflexivity |].
    cbn [gep_nusw_ok] in Hok.
    apply Bool.andb_true_iff in Hok as [Hok Hrest].
    apply Bool.andb_true_iff in Hok as [_ Hin_u].
    destruct steps' as [| p2 steps''].
    - unfold gep_offset; cbn [fold_left].
      replace (addr + (off + (0 + k * sz))) with (addr + (off + k * sz)) by lia.
      exact Hin_u.
    - assert (Hne' : p2 :: steps'' <> []) by discriminate.
      specialize (IH addr (off + k * sz) Hne' Hrest).
      rewrite gep_offset_cons.
      replace (addr + (off + (k * sz + gep_offset (p2 :: steps''))))
        with (addr + (off + k * sz + gep_offset (p2 :: steps'')))
        by lia.
      exact IH.
  Qed.

  Lemma gep_inbounds_flags_implies_wrap64_eq : forall flags base steps,
    pointer_size = 8%N ->
    0 <= base < 2 ^ 64 ->
    steps <> [] ->
    gep_inbounds flags = true ->
    gep_flags_violated flags base steps = false ->
    0 <= base + gep_offset steps < 2 ^ 64
    /\ wrap_ptr64 (base + gep_offset steps) = base + gep_offset steps.
  Proof.
    intros flags base steps Hptr64 Hbase Hne Hinb Hok.
    assert (Hbits : gep_index_bits = 64)
      by (unfold gep_index_bits; rewrite Hptr64; reflexivity).
    assert (Hnusw_ok : gep_nusw_ok base 0 steps = true).
    { unfold gep_flags_violated in Hok; cbv zeta in Hok.
      rewrite Hbits, (Z.mod_small base (2 ^ 64) Hbase), Hinb in Hok.
      destruct (gep_nusw_ok base 0 steps); [reflexivity | cbn in Hok; discriminate Hok]. }
    pose proof (@gep_nusw_ok_nonempty_range steps base 0 Hne Hnusw_ok) as Hrng.
    unfold in_unsigned_index_range in Hrng.
    rewrite Hbits, Z.add_0_l in Hrng.
    apply Bool.andb_true_iff in Hrng as [Hlo Hhi].
    apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi.
    split; [lia | apply gep_inbounds_implies_wrap64_eq; lia].
  Qed.
End GEP.
