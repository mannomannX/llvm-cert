(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified [mcfg dtyp] Module Exporter ([CertPasses.McfgExport])

    Provides a fail-fast, extraction-clean lowering from optimized Vellvm
    modules ([CFG.mcfg dtyp]) back to printable LLVM 23 surface syntax trees
    ([toplevel_entities typ (block typ * list (block typ))]):

    1. **Entry-Block Placement & Phi-Free Invariant ([place_entry_first_cfg])**:
       In textual LLVM IR (and [CFG.cfg_of_definition]), the first printed block
       of a function definition is unconditionally its entry block, and LLVM 23
       ([llvm-as]) forbids [phi] nodes in the entry block. [place_entry_first_cfg]
       validates block-ID uniqueness, locates [init c], rejects entry-block
       [phi]s, and places the entry block at the head of [blks] while preserving
       [find_block] and [refine_cfg] denotational semantics ([0 Admitted]).
    2. **Fail-Fast Dynamic-Type Reification ([reify_dtyp])**:
       Maps [DTYPE_Pointer] to LLVM 23 opaque [ptr] ([TYPE_Pointer None]) and
       rejects target-dependent/unprintable internal types ([DTYPE_Iptr],
       [DTYPE_Opaque]) with explicit [inl] diagnostics rather than silent
       fallback types.
    3. **Prototype, Reference, & Local-ID Normalization ([resolve_for_opt_tle],
       [export_mcfg_with_typ], [export_mcfg_with_tle])**:
       Expands [#N] attribute groups, callee attributes, and semantic value
       metadata prior to optimization while preserving/restoring [!N] metadata
       node IDs, deduplicating attributes by LLVM attribute slot, reconstructing
       [TYPE_Function] prototypes, and injectively normalizing local [Anon]/[Raw]
       identifiers to collision-free named identifiers so LLVM 23 ([llvm-as])
       never encounters sequential [%0, %1, ...] numbering gaps after passes. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  List
  Bool.
Import ListNotations.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  ScopeTheory
  Utils.rutt_cutoff
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Implementations.ParamsV
  Semantics.Denotation.

From CertPasses Require Import
  PassCommon.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.
Local Open Scope list_scope.

(** * 1. Duplicate-Free Block-ID Validation & [find_block] Helpers *)

Fixpoint nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && nodup_raw_ids rest
  end.

Lemma nodup_raw_ids_spec (xs : list raw_id) :
  nodup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rest IH]; cbn [nodup_raw_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, in_raw_ids_false, IH.
    split.
    + intros [Hnin Hnd]; constructor; assumption.
    + intros Hnd; inversion Hnd; subst; split; assumption.
Qed.

Lemma nodup_map_filter {A B : Type} (f : A -> B) (p : A -> bool) (xs : list A) :
  NoDup (List.map f xs) ->
  NoDup (List.map f (List.filter p xs)).
Proof.
  induction xs as [| x rest IH]; intros Hnd; [constructor |].
  cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
  cbn [List.filter].
  destruct (p x); [| apply IH, Hnd_rest].
  cbn [List.map]; constructor.
  - intros Hin.
    apply in_map_iff in Hin as (y & Heq & Hfilt).
    apply filter_In in Hfilt as [Hy _].
    apply Hnin; rewrite <- Heq; apply in_map, Hy.
  - apply IH, Hnd_rest.
Qed.

Lemma find_block_filter_id (p : raw_id -> bool) (bks : ocfg dtyp) (x : block_id)
  (Hx : p x = true) :
  find_block (List.filter (fun b => p (blk_id b)) bks) x = find_block bks x.
Proof.
  induction bks as [| b rest IH]; [reflexivity |].
  cbn [List.filter].
  destruct (RawIDOrd.eq_dec (blk_id b) x) as [Heq | Hneq].
  - rewrite Heq, Hx; cbv iota.
    rewrite !find_block_eq by exact Heq.
    reflexivity.
  - rewrite find_block_ineq by exact Hneq.
    destruct (p (blk_id b)); cbv iota.
    + rewrite find_block_ineq by exact Hneq; exact IH.
    + exact IH.
Qed.

(** * 2. Verified Entry-Block Placement ([place_entry_first_cfg]) *)

Definition place_entry_first_cfg (c : CFG.cfg dtyp) : (string + CFG.cfg dtyp)%type :=
  if negb (nodup_raw_ids (List.map blk_id (blks c))) then
    inl "place_entry_first_cfg: duplicate block IDs"%string
  else
    match find_block (blks c) (init c) with
    | None => inl "place_entry_first_cfg: missing entry block"%string
    | Some b_init =>
        match blk_phis b_init with
        | [] =>
            inr {| init := init c;
                   blks := b_init ::
                           List.filter
                             (fun b => negb (raw_id_eqb (blk_id b) (init c)))
                             (blks c);
                   args := args c |}
        | _ :: _ =>
            inl "place_entry_first_cfg: entry block contains phi nodes"%string
        end
    end.

Lemma place_entry_first_init :
  forall c c',
    place_entry_first_cfg c = inr c' ->
    init c' = init c.
Proof.
  intros c c' H; unfold place_entry_first_cfg in H.
  destruct (nodup_raw_ids (List.map blk_id (blks c))); cbn [negb] in H;
    [| discriminate H].
  destruct (find_block (blks c) (init c)) as [b_init |]; [| discriminate H].
  destruct (blk_phis b_init); [| discriminate H].
  inversion H; reflexivity.
Qed.

Lemma place_entry_first_find_block :
  forall c c' bid,
    place_entry_first_cfg c = inr c' ->
    find_block (blks c') bid = find_block (blks c) bid.
Proof.
  intros c c' bid H; unfold place_entry_first_cfg in H.
  destruct (nodup_raw_ids (List.map blk_id (blks c))); cbn [negb] in H;
    [| discriminate H].
  destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind;
    [| discriminate H].
  destruct (blk_phis b_init); [| discriminate H].
  inversion H; subst c'; clear H; cbn [blks].
  assert (Hid : blk_id b_init = init c).
  { symmetry; eapply find_block_has_id; exact Efind. }
  destruct (RawIDOrd.eq_dec (init c) bid) as [<- | Hne].
  - rewrite find_block_eq by exact Hid.
    symmetry; exact Efind.
  - assert (Hne_blk : blk_id b_init <> bid) by congruence.
    rewrite find_block_ineq by exact Hne_blk.
    apply (find_block_filter_id (fun id => negb (raw_id_eqb id (init c)))).
    apply Bool.negb_true_iff, raw_id_eqb_neq.
    intros Heq; apply Hne; symmetry; exact Heq.
Qed.

Lemma place_entry_first_cfg_refines_params {Pa : Params}
  (c c' : CFG.cfg dtyp) (H : place_entry_first_cfg c = inr c')
  (va : option (@ptr (@PROV Pa) (@PTR Pa))) :
  @refine_cfg Pa _ _ Logic.eq (denote_cfg c va) (denote_cfg c' va).
Proof.
  unfold denote_cfg, denote_cfg_map, refine_cfg.
  rewrite (place_entry_first_init c c' H).
  eapply ruttc_bind with (RR := Logic.eq).
  - unfold denote_ocfg_map.
    eapply ruttc_iter with (RR := Logic.eq) (II := Logic.eq); [| reflexivity].
    intros [from src] _ <-; cbv beta iota.
    rewrite !ocfg_map_find_block, (place_entry_first_find_block c c' src H).
    destruct (find_block (blks c) src) as [bk |]; cbv iota.
    + eapply ruttc_bind with (RR := Logic.eq).
      * apply refine_cfg_refl.
      * intros [tgt | dv] _ <-; cbv beta iota;
          apply ruttc_ret; constructor; reflexivity.
    + apply ruttc_ret; constructor; reflexivity.
  - intros [bid | uv] _ <-; cbv beta iota; apply refine_cfg_refl.
Qed.

Theorem place_entry_first_cfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} c c',
    place_entry_first_cfg c = inr c' ->
    forall va,
      @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq (denote_cfg c va) (denote_cfg c' va).
Proof.
  intros IP IPT c c' H va.
  exact (@place_entry_first_cfg_refines_params (@ParamsV IP IPT) c c' H va).
Qed.

Lemma place_entry_first_entry_invariant :
  forall c c',
    place_entry_first_cfg c = inr c' ->
    exists b0 bs,
      blks c' = b0 :: bs /\ blk_id b0 = init c' /\ blk_phis b0 = [].
Proof.
  intros c c' H; unfold place_entry_first_cfg in H.
  destruct (nodup_raw_ids (List.map blk_id (blks c))); cbn [negb] in H;
    [| discriminate H].
  destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind;
    [| discriminate H].
  destruct (blk_phis b_init) eqn:Ephis; [| discriminate H].
  inversion H; subst c'; clear H; cbn [blks init].
  eexists b_init, _; refine (conj eq_refl (conj _ Ephis)).
  symmetry; eapply find_block_has_id; exact Efind.
Qed.

Lemma place_entry_first_nodup :
  forall c c',
    place_entry_first_cfg c = inr c' ->
    NoDup (List.map blk_id (blks c')).
Proof.
  intros c c' H; unfold place_entry_first_cfg in H.
  destruct (nodup_raw_ids (List.map blk_id (blks c))) eqn:End;
    cbn [negb] in H; [| discriminate H].
  apply nodup_raw_ids_spec in End.
  destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind;
    [| discriminate H].
  destruct (blk_phis b_init); [| discriminate H].
  inversion H; subst c'; clear H; cbn [blks List.map].
  assert (Hid : blk_id b_init = init c).
  { symmetry; eapply find_block_has_id; exact Efind. }
  constructor.
  - intros Hin.
    apply in_map_iff in Hin as (b & Heq & Hfilt).
    apply filter_In in Hfilt as [_ Hneq].
    apply Bool.negb_true_iff, raw_id_eqb_neq in Hneq.
    apply Hneq; rewrite Heq; exact Hid.
  - apply nodup_map_filter, End.
Qed.

(** * 3. Injective Tagging, Attribute Deduplication, & Result Combinators *)

Fixpoint pos_tag (p : positive) : string :=
  match p with
  | xH => "1"%string
  | xO q => String "0"%char (pos_tag q)
  | xI q => String "1"%char (pos_tag q)
  end.

Lemma pos_tag_nonempty (p : positive) :
  pos_tag p <> ""%string.
Proof.
  destruct p; discriminate.
Qed.

Lemma pos_tag_inj (p1 p2 : positive) :
  pos_tag p1 = pos_tag p2 -> p1 = p2.
Proof.
  revert p2; induction p1 as [q1 IH | q1 IH |]; intros [q2 | q2 |] H; cbn in H;
    try discriminate H.
  - injection H as H; f_equal; exact (IH q2 H).
  - exfalso; injection H as H; exact (pos_tag_nonempty q1 H).
  - injection H as H; f_equal; exact (IH q2 H).
  - exfalso; injection H as H; exact (pos_tag_nonempty q2 (eq_sym H)).
  - reflexivity.
Qed.

Definition z_tag (z : Z) : string :=
  match z with
  | Z0 => "0"%string
  | Zpos p => String "p"%char (pos_tag p)
  | Zneg p => String "n"%char (pos_tag p)
  end.

Lemma z_tag_inj (z1 z2 : Z) :
  z_tag z1 = z_tag z2 -> z1 = z2.
Proof.
  destruct z1 as [| p1 | p1], z2 as [| p2 | p2]; intros H; cbn in H; try discriminate H.
  - reflexivity.
  - injection H as H; f_equal; exact (pos_tag_inj p1 p2 H).
  - injection H as H; f_equal; exact (pos_tag_inj p1 p2 H).
Qed.

Fixpoint str_starts_with (pfx s : string) : bool :=
  match pfx with
  | EmptyString => true
  | String c pfx' =>
      match s with
      | EmptyString => false
      | String d s' => Ascii.eqb c d && str_starts_with pfx' s'
      end
  end.

Lemma ascii_eqb_refl_local (c : ascii) :
  Ascii.eqb c c = true.
Proof.
  destruct c as [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Lemma str_starts_with_append (pfx rest : string) :
  str_starts_with pfx (String.append pfx rest) = true.
Proof.
  induction pfx as [| c pfx' IH]; cbn; [reflexivity |].
  change (String.append (String c pfx') rest)
    with (String c (String.append pfx' rest)); cbn.
  rewrite ascii_eqb_refl_local; exact IH.
Qed.

Lemma string_append_cancel_l (p s1 s2 : string) :
  String.append p s1 = String.append p s2 -> s1 = s2.
Proof.
  induction p as [| c p' IH]; cbn; [exact (fun H => H) |].
  intros H; injection H as H; exact (IH H).
Qed.

Definition rename_local_raw_id (pfx : string) (r : raw_id) : raw_id :=
  match r with
  | Name s => Name s
  | Anon z => Name (String.append pfx (String "a"%char (z_tag z)))
  | Raw z => Name (String.append pfx (String "r"%char (z_tag z)))
  end.

Lemma rename_local_raw_id_is_name (pfx : string) (r : raw_id) :
  exists s, rename_local_raw_id pfx r = Name s.
Proof.
  destruct r; cbn; eexists; reflexivity.
Qed.

Lemma rename_local_raw_id_inj (pfx : string) (r1 r2 : raw_id)
  (H1 : match r1 with Name s => str_starts_with pfx s = false | _ => True end)
  (H2 : match r2 with Name s => str_starts_with pfx s = false | _ => True end) :
  rename_local_raw_id pfx r1 = rename_local_raw_id pfx r2 -> r1 = r2.
Proof.
  destruct r1 as [s1 | z1 | z1], r2 as [s2 | z2 | z2]; cbn in *;
    intros Heq; injection Heq as Heq.
  - subst s2; reflexivity.
  - subst s1; rewrite str_starts_with_append in H1; discriminate H1.
  - subst s1; rewrite str_starts_with_append in H1; discriminate H1.
  - subst s2; rewrite str_starts_with_append in H2; discriminate H2.
  - apply string_append_cancel_l in Heq; injection Heq as Heq.
    f_equal; exact (z_tag_inj z1 z2 Heq).
  - apply string_append_cancel_l in Heq; discriminate Heq.
  - subst s2; rewrite str_starts_with_append in H2; discriminate H2.
  - apply string_append_cancel_l in Heq; discriminate Heq.
  - apply string_append_cancel_l in Heq; injection Heq as Heq.
    f_equal; exact (z_tag_inj z1 z2 Heq).
Qed.

Fixpoint mem_str (s : string) (seen : list string) : bool :=
  match seen with
  | [] => false
  | h :: tl => if String.eqb s h then true else mem_str s tl
  end.

Fixpoint dedup_by_key_aux {A : Type}
  (key : A -> string) (seen : list string) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest =>
      let k := key x in
      if mem_str k seen then dedup_by_key_aux key seen rest
      else x :: dedup_by_key_aux key (k :: seen) rest
  end.

Definition dedup_by_key {A : Type} (key : A -> string) (xs : list A) : list A :=
  dedup_by_key_aux key [] xs.

Definition param_attr_slot (pa : param_attr) : string :=
  match pa with
  | PARAMATTR_Zeroext => "zeroext"%string
  | PARAMATTR_Signext => "signext"%string
  | PARAMATTR_Inreg => "inreg"%string
  | PARAMATTR_Byval _ => "byval"%string
  | PARAMATTR_Byref _ => "byref"%string
  | PARAMATTR_Preallocated _ => "preallocated"%string
  | PARAMATTR_Inalloca _ => "inalloca"%string
  | PARAMATTR_Sret _ => "sret"%string
  | PARAMATTR_Elementtype _ => "elementtype"%string
  | PARAMATTR_Align _ => "align"%string
  | PARAMATTR_Noalias => "noalias"%string
  | PARAMATTR_Nocapture => "nocapture"%string
  | PARAMATTR_Nofree => "nofree"%string
  | PARAMATTR_Nest => "nest"%string
  | PARAMATTR_Returned => "returned"%string
  | PARAMATTR_Nonnull => "nonnull"%string
  | PARAMATTR_Dereferenceable _ => "deref"%string
  | PARAMATTR_Dereferenceable_or_null _ => "deref_null"%string
  | PARAMATTR_Swiftself => "swiftself"%string
  | PARAMATTR_Swiftasync => "swiftasync"%string
  | PARAMATTR_Swifterror => "swifterror"%string
  | PARAMATTR_Immarg => "immarg"%string
  | PARAMATTR_Noundef => "noundef"%string
  | PARAMATTR_Nofpclass _ => "nofpclass"%string
  | PARAMATTR_Nofreeobj => "nofreeobj"%string
  | PARAMATTR_Alignstack _ => "alignstack"%string
  | PARAMATTR_Allocalign => "allocalign"%string
  | PARAMATTR_Allocptr => "allocptr"%string
  | PARAMATTR_Readnone
  | PARAMATTR_Readonly
  | PARAMATTR_Writeonly => "rw"%string
  | PARAMATTR_Writable => "writable"%string
  | PARAMATTR_Dead_on_unwind => "dead_unwind"%string
  | PARAMATTR_Dead_on_return _ => "dead_ret"%string
  | PARAMATTR_Range _ _ _ => "range"%string
  | PARAMATTR_Initializes _ => "init"%string
  | PARAMATTR_Captures _ => "captures"%string
  end.

Definition fn_attr_slot (fa : fn_attr) : string :=
  match fa with
  | FNATTR_Alignstack _ => "alignstack"%string
  | FNATTR_Allockind _ => "allockind"%string
  | FNATTR_Allocsize _ _ => "allocsize"%string
  | FNATTR_Alwaysinline
  | FNATTR_Noinline => "inline_mode"%string
  | FNATTR_Builtin => "builtin"%string
  | FNATTR_Cold
  | FNATTR_Hot => "hot_cold"%string
  | FNATTR_Convergent => "convergent"%string
  | FNATTR_Disable_sanitizer_instrumentation => "dsi"%string
  | FNATTR_Fn_ret_thunk_extern => "frte"%string
  | FNATTR_Inaccessiblememonly
  | FNATTR_Inaccessiblemem_or_argmemonly
  | FNATTR_Readnone
  | FNATTR_Readonly
  | FNATTR_Writeonly
  | FNATTR_Argmemonly
  | FNATTR_Memory _ => "mem"%string
  | FNATTR_Inlinehint => "inlinehint"%string
  | FNATTR_Jumptable => "jumptable"%string
  | FNATTR_Minsize => "minsize"%string
  | FNATTR_Naked => "naked"%string
  | FNATTR_No_jump_tables => "njt"%string
  | FNATTR_Nobuiltin => "nobuiltin"%string
  | FNATTR_Noduplicate => "noduplicate"%string
  | FNATTR_Nofree => "nofree"%string
  | FNATTR_Noimplicitfloat => "noimplicitfloat"%string
  | FNATTR_Nomerge => "nomerge"%string
  | FNATTR_Nonlazybind => "nonlazybind"%string
  | FNATTR_Noprofile => "noprofile"%string
  | FNATTR_Noredzone => "noredzone"%string
  | FNATTR_Indirect_tls_seg_refs => "itsr"%string
  | FNATTR_Noreturn => "noreturn"%string
  | FNATTR_Norecurse => "norecurse"%string
  | FNATTR_Willreturn => "willreturn"%string
  | FNATTR_Nosync => "nosync"%string
  | FNATTR_Nounwind => "nounwind"%string
  | FNATTR_Nocreateundeforpoison => "ncup"%string
  | FNATTR_Nosanitize_bounds => "nsb"%string
  | FNATTR_Nosanitize_coverage => "nsc"%string
  | FNATTR_Null_pointer_is_valid => "npiv"%string
  | FNATTR_Optforfuzzing => "optfuzz"%string
  | FNATTR_Optnone => "optnone"%string
  | FNATTR_Optsize => "optsize"%string
  | FNATTR_Returns_twice => "returns_twice"%string
  | FNATTR_Safestack => "safestack"%string
  | FNATTR_Sanitize_address => "san_addr"%string
  | FNATTR_Sanitize_memory => "san_mem"%string
  | FNATTR_Sanitize_thread => "san_thr"%string
  | FNATTR_Sanitize_hwaddress => "san_hw"%string
  | FNATTR_Sanitize_memtag => "san_mtag"%string
  | FNATTR_Speculative_load_hardening => "slh"%string
  | FNATTR_Speculatable => "speculatable"%string
  | FNATTR_Ssp
  | FNATTR_Sspstrong
  | FNATTR_Sspreq => "ssp_mode"%string
  | FNATTR_Strictfp => "strictfp"%string
  | FNATTR_Tls_load_hoist => "s:tls-load-hoist"%string
  | FNATTR_Uwtable _ => "uwtable"%string
  | FNATTR_Nocf_check => "nocf_check"%string
  | FNATTR_Shadowcallstack => "scs"%string
  | FNATTR_Mustprogress => "mustprogress"%string
  | FNATTR_Vscale_range _ _ => "vscale_range"%string
  | FNATTR_String s => String.append "s:"%string s
  | FNATTR_Key_value (k, _) => String.append "s:"%string k
  | FNATTR_Attr_grp g => String.append "g:"%string (z_tag g)
  | FNATTR_UNKNOWN s => String.append "u:"%string s
  end.

Definition fast_math_slot (fm : fast_math) : string :=
  match fm with
  | Nnan => "nnan"%string
  | Ninf => "ninf"%string
  | Nsz => "nsz"%string
  | Arcp => "arcp"%string
  | Contract => "contract"%string
  | Afn => "afn"%string
  | Reassoc => "reassoc"%string
  | Fast => "fast"%string
  end.

Definition dedup_param_attrs (pas : list param_attr) : list param_attr :=
  dedup_by_key param_attr_slot pas.

Definition dedup_fn_attrs (fas : list fn_attr) : list fn_attr :=
  dedup_by_key fn_attr_slot fas.

Definition ann_dedup_slot {U : Set} (a : annotation U) : option string :=
  match a with
  | ANN_ret_attribute pa => Some (String.append "r:"%string (param_attr_slot pa))
  | ANN_fun_attribute fa => Some (String.append "f:"%string (fn_attr_slot fa))
  | ANN_fast_math_flag fm => Some (String.append "m:"%string (fast_math_slot fm))
  | _ => None
  end.

Fixpoint dedup_annotations_aux {U : Set}
  (seen : list string) (anns : list (annotation U)) : list (annotation U) :=
  match anns with
  | [] => []
  | a :: rest =>
      match ann_dedup_slot a with
      | None => a :: dedup_annotations_aux seen rest
      | Some k =>
          if mem_str k seen then dedup_annotations_aux seen rest
          else a :: dedup_annotations_aux (k :: seen) rest
      end
  end.

Definition dedup_annotations {U : Set} (anns : list (annotation U)) : list (annotation U) :=
  dedup_annotations_aux [] anns.

Definition res (A : Type) : Type := (string + A)%type.

Definition res_bind {A B : Type} (m : res A) (k : A -> res B) : res B :=
  match m with
  | inl err => inl err
  | inr x => k x
  end.

Definition res_map {A B : Type} (f : A -> B) (m : res A) : res B :=
  match m with
  | inl err => inl err
  | inr x => inr (f x)
  end.

Fixpoint res_map_list {A B : Type} (f : A -> res B) (xs : list A) : res (list B) :=
  match xs with
  | [] => inr []
  | x :: rest =>
      res_bind (f x) (fun y =>
      res_bind (res_map_list f rest) (fun ys =>
      inr (y :: ys)))
  end.

Definition res_map_opt {A B : Type} (f : A -> res B) (mx : option A) : res (option B) :=
  match mx with
  | None => inr None
  | Some x => res_map (@Some B) (f x)
  end.

Definition reify_dtyp_base (db : dtyp_base) : (string + typ)%type :=
  match db with
  | DTYPE_I sz => inr (TYPE_I sz)
  | DTYPE_B sz => inr (TYPE_B sz)
  | DTYPE_Pointer => inr (TYPE_Pointer None)
  | DTYPE_Void => inr TYPE_Void
  | DTYPE_FP fp => inr (TYPE_FP fp)
  | DTYPE_Label => inr TYPE_Label
  | DTYPE_Token => inr TYPE_Token
  | DTYPE_Metadata => inr TYPE_Metadata
  | DTYPE_X86_mmx => inr TYPE_X86_mmx
  | DTYPE_Iptr => inl "reify_dtyp: unsupported target-dependent DTYPE_Iptr"%string
  | DTYPE_Opaque => inl "reify_dtyp: unsupported DTYPE_Opaque"%string
  end.

Fixpoint reify_dtyp (dt : dtyp) : (string + typ)%type :=
  let fix reify_fields (ds : list dtyp) : (string + list typ)%type :=
    match ds with
    | [] => inr []
    | d :: rest =>
        res_bind (reify_dtyp d) (fun t =>
        res_bind (reify_fields rest) (fun ts =>
        inr (t :: ts)))
    end in
  match dt with
  | DTYPE_Base db => reify_dtyp_base db
  | DTYPE_Struct false fields => res_map TYPE_Struct (reify_fields fields)
  | DTYPE_Struct true fields => res_map TYPE_Packed_struct (reify_fields fields)
  | DTYPE_Array false sz sub => res_map (TYPE_Array sz) (reify_dtyp sub)
  | DTYPE_Array true sz sub => res_map (TYPE_Vector sz) (reify_dtyp sub)
  end.

Lemma reify_dtyp_rejects_iptr :
  reify_dtyp (DTYPE_Base DTYPE_Iptr) =
  inl "reify_dtyp: unsupported target-dependent DTYPE_Iptr"%string.
Proof.
  reflexivity.
Qed.

Lemma reify_dtyp_rejects_opaque :
  reify_dtyp (DTYPE_Base DTYPE_Opaque) =
  inl "reify_dtyp: unsupported DTYPE_Opaque"%string.
Proof.
  reflexivity.
Qed.

(** * 4. Fail-Fast Source-Type & Parameter-Attribute Lowering *)

Fixpoint lookup_type_def (env : list (ident * typ)) (id : ident) : option typ :=
  match env with
  | [] => None
  | (k, t) :: rest =>
      if ident_eqb id k then Some t else lookup_type_def rest id
  end.

Definition remove_type_def (env : list (ident * typ)) (id : ident) : list (ident * typ) :=
  List.filter (fun p => negb (ident_eqb id (fst p))) env.

Fixpoint lower_src_typ_step (rec_id : ident -> res typ) (t : typ) : res typ :=
  let fix lower_list (ts : list typ) : res (list typ) :=
    match ts with
    | [] => inr []
    | u :: us =>
        res_bind (lower_src_typ_step rec_id u) (fun u' =>
        res_bind (lower_list us) (fun us' =>
        inr (u' :: us')))
    end in
  match t with
  | TYPE_I sz => inr (TYPE_I sz)
  | TYPE_B sz => inr (TYPE_B sz)
  | TYPE_Pointer _ => inr (TYPE_Pointer None)
  | TYPE_Void => inr TYPE_Void
  | TYPE_FP fp => inr (TYPE_FP fp)
  | TYPE_Label => inr TYPE_Label
  | TYPE_Token => inr TYPE_Token
  | TYPE_Metadata => inr TYPE_Metadata
  | TYPE_X86_mmx => inr TYPE_X86_mmx
  | TYPE_Iptr => inl "lower_src_typ: unsupported target-dependent TYPE_Iptr"%string
  | TYPE_Opaque => inl "lower_src_typ: unsupported TYPE_Opaque"%string
  | TYPE_Function _ _ _ =>
      inl "lower_src_typ: unexpected nested TYPE_Function value type"%string
  | TYPE_Array sz sub =>
      res_map (TYPE_Array sz) (lower_src_typ_step rec_id sub)
  | TYPE_Vector sz sub =>
      res_bind (lower_src_typ_step rec_id sub) (fun sub' =>
      match sub' with
      | TYPE_I _ | TYPE_B _ | TYPE_Pointer None | TYPE_FP _ =>
          inr (TYPE_Vector sz sub')
      | _ => inl "lower_src_typ: invalid non-scalar TYPE_Vector element"%string
      end)
  | TYPE_Struct fields =>
      res_map TYPE_Struct (lower_list fields)
  | TYPE_Packed_struct fields =>
      res_map TYPE_Packed_struct (lower_list fields)
  | TYPE_Identified id => rec_id id
  end.

Fixpoint lower_src_typ_fuel
  (fuel : nat) (env : list (ident * typ)) (t : typ) : res typ :=
  match fuel with
  | O => inl "lower_src_typ: cyclic or unresolved TYPE_Identified"%string
  | S fuel' =>
      lower_src_typ_step
        (fun id =>
           match lookup_type_def env id with
           | None => inl "lower_src_typ: undefined TYPE_Identified"%string
           | Some body => lower_src_typ_fuel fuel' (remove_type_def env id) body
           end)
        t
  end.

Definition lower_src_typ (env : list (ident * typ)) (t : typ) : res typ :=
  lower_src_typ_fuel (S (List.length env)) env t.

Definition lower_param_attr (env : list (ident * typ)) (pa : param_attr) : res param_attr :=
  match pa with
  | PARAMATTR_Zeroext => inr PARAMATTR_Zeroext
  | PARAMATTR_Signext => inr PARAMATTR_Signext
  | PARAMATTR_Inreg => inr PARAMATTR_Inreg
  | PARAMATTR_Byval t => res_map PARAMATTR_Byval (lower_src_typ env t)
  | PARAMATTR_Byref t => res_map PARAMATTR_Byref (lower_src_typ env t)
  | PARAMATTR_Preallocated t => res_map PARAMATTR_Preallocated (lower_src_typ env t)
  | PARAMATTR_Inalloca t => res_map PARAMATTR_Inalloca (lower_src_typ env t)
  | PARAMATTR_Sret t => res_map PARAMATTR_Sret (lower_src_typ env t)
  | PARAMATTR_Elementtype t => res_map PARAMATTR_Elementtype (lower_src_typ env t)
  | PARAMATTR_Align a => inr (PARAMATTR_Align a)
  | PARAMATTR_Noalias => inr PARAMATTR_Noalias
  | PARAMATTR_Nocapture => inr PARAMATTR_Nocapture
  | PARAMATTR_Nofree => inr PARAMATTR_Nofree
  | PARAMATTR_Nest => inr PARAMATTR_Nest
  | PARAMATTR_Returned => inr PARAMATTR_Returned
  | PARAMATTR_Nonnull => inr PARAMATTR_Nonnull
  | PARAMATTR_Dereferenceable a => inr (PARAMATTR_Dereferenceable a)
  | PARAMATTR_Dereferenceable_or_null a => inr (PARAMATTR_Dereferenceable_or_null a)
  | PARAMATTR_Swiftself => inr PARAMATTR_Swiftself
  | PARAMATTR_Swiftasync => inr PARAMATTR_Swiftasync
  | PARAMATTR_Swifterror => inr PARAMATTR_Swifterror
  | PARAMATTR_Immarg => inr PARAMATTR_Immarg
  | PARAMATTR_Noundef => inr PARAMATTR_Noundef
  | PARAMATTR_Nofpclass mask => inr (PARAMATTR_Nofpclass mask)
  | PARAMATTR_Nofreeobj => inr PARAMATTR_Nofreeobj
  | PARAMATTR_Alignstack a => inr (PARAMATTR_Alignstack a)
  | PARAMATTR_Allocalign => inr PARAMATTR_Allocalign
  | PARAMATTR_Allocptr => inr PARAMATTR_Allocptr
  | PARAMATTR_Readnone => inr PARAMATTR_Readnone
  | PARAMATTR_Readonly => inr PARAMATTR_Readonly
  | PARAMATTR_Writeonly => inr PARAMATTR_Writeonly
  | PARAMATTR_Writable => inr PARAMATTR_Writable
  | PARAMATTR_Dead_on_unwind => inr PARAMATTR_Dead_on_unwind
  | PARAMATTR_Dead_on_return sz => inr (PARAMATTR_Dead_on_return sz)
  | PARAMATTR_Range t a b =>
      res_map (fun t' => PARAMATTR_Range t' a b) (lower_src_typ env t)
  | PARAMATTR_Initializes l => inr (PARAMATTR_Initializes l)
  | PARAMATTR_Captures p => inr (PARAMATTR_Captures p)
  end.

Definition lower_param_attrs
  (env : list (ident * typ)) (pas : list param_attr) : res (list param_attr) :=
  res_map_list (lower_param_attr env) pas.

(** * 5. Total AST Reification Across Expressions, Metadata, Instructions, & Blocks *)

Section ReifyExpMeta.
Context {U : Set} (ft : U -> res typ).

Fixpoint map_res_exp (e : exp U) : res (exp typ) :=
  let fix map_texps (tes : list (U * exp U)) : res (list (typ * exp typ)) :=
    match tes with
    | [] => inr []
    | (u, sub) :: rest =>
        res_bind (ft u) (fun t =>
        res_bind (map_res_exp sub) (fun sub' =>
        res_bind (map_texps rest) (fun rest' =>
        inr ((t, sub') :: rest'))))
    end in
  match e with
  | EXP_Ident id => inr (EXP_Ident id)
  | EXP_Integer x => inr (EXP_Integer x)
  | EXP_Float f => inr (EXP_Float f)
  | EXP_Bool b => inr (EXP_Bool b)
  | EXP_Null => inr EXP_Null
  | EXP_Zero_initializer => inr EXP_Zero_initializer
  | EXP_Cstring elts => res_map EXP_Cstring (map_texps elts)
  | EXP_Undef => inr EXP_Undef
  | EXP_Poison => inr EXP_Poison
  | EXP_Struct fields => res_map EXP_Struct (map_texps fields)
  | EXP_Packed_struct fields => res_map EXP_Packed_struct (map_texps fields)
  | EXP_Array elts => res_map EXP_Array (map_texps elts)
  | EXP_Vector elts => res_map EXP_Vector (map_texps elts)
  | OP_IBinop iop u v1 v2 =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (map_res_exp v2) (fun v2' =>
      inr (OP_IBinop iop t v1' v2'))))
  | OP_ICmp samesign cmp u v1 v2 =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (map_res_exp v2) (fun v2' =>
      inr (OP_ICmp samesign cmp t v1' v2'))))
  | OP_FBinop fop fm u v1 v2 =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (map_res_exp v2) (fun v2' =>
      inr (OP_FBinop fop fm t v1' v2'))))
  | OP_Fneg flags (u, v) =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v) (fun v' =>
      inr (OP_Fneg flags (t, v'))))
  | OP_FCmp cmp fm u v1 v2 =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (map_res_exp v2) (fun v2' =>
      inr (OP_FCmp cmp fm t v1' v2'))))
  | OP_Conversion conv u_from v u_to =>
      res_bind (ft u_from) (fun t_from =>
      res_bind (map_res_exp v) (fun v' =>
      res_bind (ft u_to) (fun t_to =>
      inr (OP_Conversion conv t_from v' t_to))))
  | OP_GetElementPtr flags u (u_ptr, ptrval) idxs =>
      res_bind (ft u) (fun t =>
      res_bind (ft u_ptr) (fun t_ptr =>
      res_bind (map_res_exp ptrval) (fun ptrval' =>
      res_bind (map_texps idxs) (fun idxs' =>
      inr (OP_GetElementPtr flags t (t_ptr, ptrval') idxs')))))
  | OP_ExtractElement (u_vec, vec) (u_idx, idx) =>
      res_bind (ft u_vec) (fun t_vec =>
      res_bind (map_res_exp vec) (fun vec' =>
      res_bind (ft u_idx) (fun t_idx =>
      res_bind (map_res_exp idx) (fun idx' =>
      inr (OP_ExtractElement (t_vec, vec') (t_idx, idx'))))))
  | OP_InsertElement (u_vec, vec) (u_elt, elt) (u_idx, idx) =>
      res_bind (ft u_vec) (fun t_vec =>
      res_bind (map_res_exp vec) (fun vec' =>
      res_bind (ft u_elt) (fun t_elt =>
      res_bind (map_res_exp elt) (fun elt' =>
      res_bind (ft u_idx) (fun t_idx =>
      res_bind (map_res_exp idx) (fun idx' =>
      inr (OP_InsertElement (t_vec, vec') (t_elt, elt') (t_idx, idx'))))))))
  | OP_ShuffleVector (u1, v1) (u2, v2) (um, mask) =>
      res_bind (ft u1) (fun t1 =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (ft u2) (fun t2 =>
      res_bind (map_res_exp v2) (fun v2' =>
      res_bind (ft um) (fun tm =>
      res_bind (map_res_exp mask) (fun mask' =>
      inr (OP_ShuffleVector (t1, v1') (t2, v2') (tm, mask'))))))))
  | OP_ExtractValue (u_vec, vec) idxs =>
      res_bind (ft u_vec) (fun t_vec =>
      res_bind (map_res_exp vec) (fun vec' =>
      inr (OP_ExtractValue (t_vec, vec') idxs)))
  | OP_InsertValue (u_vec, vec) (u_elt, elt) idxs =>
      res_bind (ft u_vec) (fun t_vec =>
      res_bind (map_res_exp vec) (fun vec' =>
      res_bind (ft u_elt) (fun t_elt =>
      res_bind (map_res_exp elt) (fun elt' =>
      inr (OP_InsertValue (t_vec, vec') (t_elt, elt') idxs)))))
  | OP_Select fm (u_c, cnd) (u1, v1) (u2, v2) =>
      res_bind (ft u_c) (fun t_c =>
      res_bind (map_res_exp cnd) (fun cnd' =>
      res_bind (ft u1) (fun t1 =>
      res_bind (map_res_exp v1) (fun v1' =>
      res_bind (ft u2) (fun t2 =>
      res_bind (map_res_exp v2) (fun v2' =>
      inr (OP_Select fm (t_c, cnd') (t1, v1') (t2, v2'))))))))
  | OP_Freeze (u, v) =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v) (fun v' =>
      inr (OP_Freeze (t, v'))))
  | EXP_Asm sideffect alignstack inteldialect unwind template constraints =>
      inr (EXP_Asm sideffect alignstack inteldialect unwind template constraints)
  | EXP_Metadata m =>
      res_map EXP_Metadata (map_res_metadata m)
  | EXP_Splat (u, elt) =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp elt) (fun elt' =>
      inr (EXP_Splat (t, elt'))))
  | EXP_BlockAddress fn blk =>
      inr (EXP_BlockAddress fn blk)
  end
with map_res_metadata (m : metadata U) : res (metadata typ) :=
  let fix map_mds (mds : list (metadata U)) : res (list (metadata typ)) :=
    match mds with
    | [] => inr []
    | md :: rest =>
        res_bind (map_res_metadata md) (fun md' =>
        res_bind (map_mds rest) (fun rest' =>
        inr (md' :: rest')))
    end in
  match m with
  | METADATA_Null => inr METADATA_Null
  | METADATA_Id id => inr (METADATA_Id id)
  | METADATA_Const (u, v) =>
      res_bind (ft u) (fun t =>
      res_bind (map_res_exp v) (fun v' =>
      inr (METADATA_Const (t, v'))))
  | METADATA_Node mds => res_map METADATA_Node (map_mds mds)
  | METADATA_Pair md1 md2 =>
      res_bind (map_res_metadata md1) (fun md1' =>
      res_bind (map_res_metadata md2) (fun md2' =>
      inr (METADATA_Pair md1' md2')))
  | METADATA_Debug dstr contents => inr (METADATA_Debug dstr contents)
  | METADATA_File_info finfo => inr (METADATA_File_info finfo)
  end.

End ReifyExpMeta.

Definition reify_exp (e : exp dtyp) : (string + exp typ)%type :=
  map_res_exp reify_dtyp e.

Definition reify_metadata (m : metadata dtyp) : (string + metadata typ)%type :=
  map_res_metadata reify_dtyp m.

Definition reify_metadata_list (mds : list (metadata dtyp)) : res (list (metadata typ)) :=
  res_map_list reify_metadata mds.

Definition reify_texp (te : texp dtyp) : (string + texp typ)%type :=
  let '(dt, e) := te in
  res_bind (reify_dtyp dt) (fun t =>
  res_bind (reify_exp e) (fun e' =>
  inr (t, e'))).

Definition reify_annotation
  (env : list (ident * typ)) (a : annotation dtyp) : res (annotation typ) :=
  match a with
  | ANN_linkage l => inr (ANN_linkage l)
  | ANN_preemption_specifier p => inr (ANN_preemption_specifier p)
  | ANN_visibility v => inr (ANN_visibility v)
  | ANN_dll_storage d => inr (ANN_dll_storage d)
  | ANN_thread_local_storage t => inr (ANN_thread_local_storage t)
  | ANN_unnamed_addr u => inr (ANN_unnamed_addr u)
  | ANN_addrspace n => inr (ANN_addrspace n)
  | ANN_section s => inr (ANN_section s)
  | ANN_partition s => inr (ANN_partition s)
  | ANN_comdat l => inr (ANN_comdat l)
  | ANN_align n => inr (ANN_align n)
  | ANN_no_sanitize => inr ANN_no_sanitize
  | ANN_no_sanitize_address => inr ANN_no_sanitize_address
  | ANN_no_sanitize_hwaddress => inr ANN_no_sanitize_hwaddress
  | ANN_sanitize_address_dyninit => inr ANN_sanitize_address_dyninit
  | ANN_metadata l => res_map ANN_metadata (reify_metadata_list l)
  | ANN_cconv c => inr (ANN_cconv c)
  | ANN_gc s => inr (ANN_gc s)
  | ANN_prefix t => res_map ANN_prefix (reify_texp t)
  | ANN_prologue t => res_map ANN_prologue (reify_texp t)
  | ANN_personality t => res_map ANN_personality (reify_texp t)
  | ANN_inalloca => inr ANN_inalloca
  | ANN_num_elements t => res_map ANN_num_elements (reify_texp t)
  | ANN_volatile => inr ANN_volatile
  | ANN_tail t => inr (ANN_tail t)
  | ANN_fast_math_flag f => inr (ANN_fast_math_flag f)
  | ANN_ret_attribute p => res_map ANN_ret_attribute (lower_param_attr env p)
  | ANN_fun_attribute f => inr (ANN_fun_attribute f)
  | ANN_atomic => inr ANN_atomic
  | ANN_syncscope s => inr (ANN_syncscope s)
  | ANN_ordering o => inr (ANN_ordering o)
  end.

Definition reify_annotations
  (env : list (ident * typ)) (anns : list (annotation dtyp))
  : res (list (annotation typ)) :=
  res_map dedup_annotations (res_map_list (reify_annotation env) anns).

Definition reify_cmpxchg (c : cmpxchg dtyp) : res (cmpxchg typ) :=
  res_bind (reify_texp (c_ptr c)) (fun ptr' =>
  res_bind (reify_texp (c_cmp c)) (fun cmp' =>
  res_bind (reify_texp (c_new c)) (fun new' =>
  inr {| c_weak             := c_weak c;
         c_volatile         := c_volatile c;
         c_ptr              := ptr';
         c_cmp              := cmp';
         c_new              := new';
         c_syncscope        := c_syncscope c;
         c_success_ordering := c_success_ordering c;
         c_failure_ordering := c_failure_ordering c;
         c_align            := c_align c |}))).

Definition reify_atomicrmw (a : atomicrmw dtyp) : res (atomicrmw typ) :=
  res_bind (reify_texp (a_ptr a)) (fun ptr' =>
  res_bind (reify_texp (a_val a)) (fun val' =>
  inr {| a_volatile  := a_volatile a;
         a_operation := a_operation a;
         a_ptr       := ptr';
         a_val       := val';
         a_syncscope := a_syncscope a;
         a_ordering  := a_ordering a;
         a_align     := a_align a |})).

Definition reify_operand (op : @operand dtyp) : res (@operand typ) :=
  match op with
  | SSA_value te => res_map SSA_value (reify_texp te)
  | Metadata_string m => res_map Metadata_string (reify_metadata m)
  end.

Definition reify_operand_bundle
  (ob : @operand_bundle dtyp) : res (@operand_bundle typ) :=
  res_bind (res_map_list reify_operand (ob_ops ob)) (fun ops' =>
  inr {| ob_tag := ob_tag ob; ob_ops := ops' |}).

Definition reify_landingpad_clause
  (cl : @landingpad_clause dtyp) : res (@landingpad_clause typ) :=
  match cl with
  | CATCH te => res_map CATCH (reify_texp te)
  | FILTER te => res_map FILTER (reify_texp te)
  end.

Definition reify_phi (p : phi dtyp) : res (phi typ) :=
  let '(Phi fm dt pargs) := p in
  res_bind (reify_dtyp dt) (fun t =>
  res_bind
    (res_map_list
       (fun '(bid, e) => res_map (pair bid) (reify_exp e))
       pargs)
    (fun pargs' => inr (Phi fm t pargs'))).

Definition fn_sig : Type := (typ * list typ * bool)%type.

Fixpoint lookup_fn_sig
  (sigs : list (function_id * fn_sig)) (fid : function_id) : option fn_sig :=
  match sigs with
  | [] => None
  | (k, sig) :: rest =>
      if raw_id_eqb fid k then Some sig else lookup_fn_sig rest fid
  end.

Definition typ_is_ptr (t : typ) : bool :=
  match t with
  | TYPE_Pointer None => true
  | _ => false
  end.

Definition reify_callee_texp
  (sigs : list (function_id * fn_sig)) (fn : texp dtyp) : res (texp typ) :=
  let '(dt, e) := fn in
  res_bind (reify_exp e) (fun e' =>
  match e with
  | EXP_Ident (ID_Global fid) =>
      match lookup_fn_sig sigs fid with
      | Some (ret_t, args_t, true) =>
          inr (TYPE_Function ret_t args_t true, e')
      | Some (ret_t, _, false) =>
          match dt with
          | DTYPE_Base DTYPE_Pointer =>
              if typ_is_ptr ret_t then inr (TYPE_Pointer None, e')
              else inr (ret_t, e')
          | _ => res_map (fun t => (t, e')) (reify_dtyp dt)
          end
      | None => res_map (fun t => (t, e')) (reify_dtyp dt)
      end
  | _ => res_map (fun t => (t, e')) (reify_dtyp dt)
  end).

Definition reify_call_arg
  (env : list (ident * typ)) (ca : texp dtyp * list param_attr)
  : res (texp typ * list param_attr) :=
  let '(te, pas) := ca in
  res_bind (reify_texp te) (fun te' =>
  res_bind (lower_param_attrs env pas) (fun pas' =>
  inr (te', dedup_param_attrs pas'))).

Definition reify_instr
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (ins : instr dtyp) : res (instr typ) :=
  match ins with
  | INSTR_Comment msg => inr (INSTR_Comment msg)
  | INSTR_Op op => res_map INSTR_Op (reify_exp op)
  | INSTR_Call fn cargs anns obs =>
      res_bind (reify_callee_texp sigs fn) (fun fn' =>
      res_bind (res_map_list (reify_call_arg env) cargs) (fun cargs' =>
      res_bind (reify_annotations env anns) (fun anns' =>
      res_bind (res_map_list reify_operand_bundle obs) (fun obs' =>
      inr (INSTR_Call fn' cargs' anns' obs')))))
  | INSTR_Alloca dt anns =>
      res_bind (reify_dtyp dt) (fun t =>
      res_bind (reify_annotations env anns) (fun anns' =>
      inr (INSTR_Alloca t anns')))
  | INSTR_Load dt ptr anns =>
      res_bind (reify_dtyp dt) (fun t =>
      res_bind (reify_texp ptr) (fun ptr' =>
      res_bind (reify_annotations env anns) (fun anns' =>
      inr (INSTR_Load t ptr' anns'))))
  | INSTR_Store val ptr anns =>
      res_bind (reify_texp val) (fun val' =>
      res_bind (reify_texp ptr) (fun ptr' =>
      res_bind (reify_annotations env anns) (fun anns' =>
      inr (INSTR_Store val' ptr' anns'))))
  | INSTR_Fence syncscope ord => inr (INSTR_Fence syncscope ord)
  | INSTR_AtomicCmpXchg c => res_map INSTR_AtomicCmpXchg (reify_cmpxchg c)
  | INSTR_AtomicRMW a => res_map INSTR_AtomicRMW (reify_atomicrmw a)
  | INSTR_VAArg va dt =>
      res_bind (reify_texp va) (fun va' =>
      res_bind (reify_dtyp dt) (fun t =>
      inr (INSTR_VAArg va' t)))
  | INSTR_LandingPad dt cleanup cs =>
      res_bind (reify_dtyp dt) (fun t =>
      res_bind (res_map_list reify_landingpad_clause cs) (fun cs' =>
      inr (INSTR_LandingPad t cleanup cs')))
  end.

Definition reify_terminator
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (tm : terminator dtyp) : res (terminator typ) :=
  match tm with
  | TERM_Ret v => res_map TERM_Ret (reify_texp v)
  | TERM_Ret_void => inr TERM_Ret_void
  | TERM_Br v br1 br2 =>
      res_map (fun v' => TERM_Br v' br1 br2) (reify_texp v)
  | TERM_Br_1 br => inr (TERM_Br_1 br)
  | TERM_Switch v def_dest brs =>
      res_map (fun v' => TERM_Switch v' def_dest brs) (reify_texp v)
  | TERM_IndirectBr v brs _ =>
      res_map (fun v' => TERM_IndirectBr v' brs None) (reify_texp v)
  | TERM_Resume v => res_map TERM_Resume (reify_texp v)
  | TERM_Invoke fn cargs to_lbl unwind_lbl anns obs =>
      res_bind (reify_callee_texp sigs fn) (fun fn' =>
      res_bind (res_map_list (reify_call_arg env) cargs) (fun cargs' =>
      res_bind (reify_annotations env anns) (fun anns' =>
      res_bind (res_map_list reify_operand_bundle obs) (fun obs' =>
      inr (TERM_Invoke fn' cargs' to_lbl unwind_lbl anns' obs')))))
  | TERM_Unreachable => inr TERM_Unreachable
  end.

Definition reify_phi_line
  (pl : local_id * phi dtyp * list (metadata dtyp))
  : res (local_id * phi typ * list (metadata typ)) :=
  let '(lid, p, mds) := pl in
  res_bind (reify_phi p) (fun p' =>
  res_bind (reify_metadata_list mds) (fun mds' =>
  inr (lid, p', mds'))).

Definition reify_code_line
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (cl : instr_id * instr dtyp * list (metadata dtyp))
  : res (instr_id * instr typ * list (metadata typ)) :=
  let '(iid, ins, mds) := cl in
  res_bind (reify_instr env sigs ins) (fun ins' =>
  res_bind (reify_metadata_list mds) (fun mds' =>
  inr (iid, ins', mds'))).

Definition reify_term_line
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (tl : instr_id * terminator dtyp * list (metadata dtyp))
  : res (instr_id * terminator typ * list (metadata typ)) :=
  let '(iid, tm, mds) := tl in
  res_bind (reify_terminator env sigs tm) (fun tm' =>
  res_bind (reify_metadata_list mds) (fun mds' =>
  inr (iid, tm', mds'))).

Definition reify_block_ctx
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (b : block dtyp) : res (block typ) :=
  res_bind (res_map_list reify_phi_line (blk_phis b)) (fun phis' =>
  res_bind (res_map_list (reify_code_line env sigs) (blk_code b)) (fun code' =>
  res_bind (reify_term_line env sigs (blk_term b)) (fun term' =>
  inr {| blk_id       := blk_id b;
         blk_phis     := phis';
         blk_code     := code';
         blk_term     := term';
         blk_comments := blk_comments b |}))).

Definition reify_block (b : block dtyp) : (string + block typ)%type :=
  reify_block_ctx [] [] b.

Definition reify_cfg_blocks
  (env : list (ident * typ)) (sigs : list (function_id * fn_sig))
  (c : CFG.cfg dtyp) : res (block typ * list (block typ)) :=
  res_bind (place_entry_first_cfg c) (fun c' =>
  match blks c' with
  | [] => inl "reify_cfg_blocks: internal empty CFG after place_entry_first_cfg"%string
  | b0 :: bs =>
      res_bind (reify_block_ctx env sigs b0) (fun b0' =>
      res_bind (res_map_list (reify_block_ctx env sigs) bs) (fun bs' =>
      inr (b0', bs')))
  end).

(** * 6. Module-Level Reification ([export_mcfg_to_tle] & [export_mcfg_with_typ]) *)

Definition reify_global
  (env : list (ident * typ)) (g : global dtyp) : res (global typ) :=
  res_bind (reify_dtyp (g_typ g)) (fun gt' =>
  res_bind (res_map_opt reify_exp (g_exp g)) (fun ge' =>
  res_bind (reify_annotations env (g_annotations g)) (fun ganns' =>
  inr {| g_ident                  := g_ident g;
         g_typ                    := gt';
         g_constant               := g_constant g;
         g_exp                    := ge';
         g_externally_initialized := g_externally_initialized g;
         g_alias                  := g_alias g;
         g_annotations            := ganns' |}))).

Definition reify_declaration (d : declaration dtyp) : res (declaration typ) :=
  let '(ret_pas, arg_pass) := dc_param_attrs d in
  res_bind (reify_dtyp (dc_type d)) (fun dt' =>
  res_bind (lower_param_attrs [] ret_pas) (fun ret_pas' =>
  res_bind (res_map_list (lower_param_attrs []) arg_pass) (fun arg_pass' =>
  res_bind (reify_annotations [] (dc_annotations d)) (fun anns' =>
  inr {| dc_name        := dc_name d;
         dc_type        := dt';
         dc_param_attrs := (dedup_param_attrs ret_pas',
                            List.map dedup_param_attrs arg_pass');
         dc_attrs       := dedup_fn_attrs (dc_attrs d);
         dc_annotations := anns' |})))).

Definition reify_definition
  (df : definition dtyp (CFG.cfg dtyp))
  : res (definition typ (block typ * list (block typ))) :=
  res_bind (reify_declaration (df_prototype df)) (fun proto' =>
  res_bind (reify_cfg_blocks [] [] (df_instrs df)) (fun body' =>
  inr {| df_prototype := proto';
         df_args      := df_args df;
         df_instrs    := body' |})).

Definition reify_modul
  (M : CFG.mcfg dtyp) : res (@CFG.modul typ (block typ * list (block typ))%type) :=
  res_bind
    (res_map_list (fun '(id, dt) => res_map (pair id) (reify_dtyp dt)) (m_type_defs M))
    (fun tdefs' =>
  res_bind (res_map_list (reify_global []) (m_globals M)) (fun globs' =>
  res_bind (res_map_list reify_declaration (m_declarations M)) (fun decls' =>
  res_bind (res_map_list reify_definition (m_definitions M)) (fun defs' =>
  inr {| m_name         := m_name M;
         m_target       := m_target M;
         m_datalayout   := m_datalayout M;
         m_type_defs    := tdefs';
         m_globals      := globs';
         m_declarations := decls';
         m_definitions  := defs' |})))).

(** * 6b. Pre-Optimization Reference Resolution, [!N] Restoration, & [Anon] Normalization *)

Definition is_semantic_md_kind (k : string) : bool :=
  String.eqb k "align"%string ||
  String.eqb k "nofpclass"%string ||
  String.eqb k "range"%string ||
  String.eqb k "dereferenceable"%string ||
  String.eqb k "dereferenceable_or_null"%string.

Section ResolveForOpt.
Context {U : Set}.

Definition resolve_opt_metadata
  (defs : IntMap (metadata U)) (md : metadata U) : metadata U :=
  match md with
  | METADATA_Pair (METADATA_Id (Name k)) (METADATA_Id (Anon n)) =>
      if is_semantic_md_kind k then
        match IntMaps.lookup n defs with
        | Some node => METADATA_Pair (METADATA_Id (Name k)) node
        | None => md
        end
      else md
  | _ => md
  end.

Definition resolve_opt_metadata_list
  (defs : IntMap (metadata U)) (mds : list (metadata U)) : list (metadata U) :=
  List.map (resolve_opt_metadata defs) mds.

Definition expand_decl_dedup
  (groups : IntMap (list fn_attr)) (d : declaration U) : declaration U :=
  let '(ret_pas, arg_pass) := dc_param_attrs d in
  mk_declaration
    (dc_name d)
    (dc_type d)
    (dedup_param_attrs ret_pas, List.map dedup_param_attrs arg_pass)
    (dedup_fn_attrs (expand_fn_attrs groups (dc_attrs d)))
    (dedup_annotations (dc_annotations d)).

Definition resolve_opt_call_args
  (args : list (texp U * list param_attr)) : list (texp U * list param_attr) :=
  List.map (fun '(te, pas) => (te, dedup_param_attrs pas)) args.

Definition resolve_opt_instr
  (groups : IntMap (list fn_attr))
  (callees : rmap (list param_attr * list (list param_attr)))
  (i : instr U) : instr U :=
  match i with
  | INSTR_Call fn args anns obs =>
      let '(args', anns') := merge_callee_attrs callees fn args anns in
      INSTR_Call
        fn
        (resolve_opt_call_args args')
        (dedup_annotations (expand_annotations groups anns'))
        obs
  | _ => i
  end.

Definition resolve_opt_terminator
  (groups : IntMap (list fn_attr))
  (callees : rmap (list param_attr * list (list param_attr)))
  (tm : terminator U) : terminator U :=
  match tm with
  | TERM_Invoke fn args to_lbl uw_lbl anns obs =>
      let '(args', anns') := merge_callee_attrs callees fn args anns in
      TERM_Invoke
        fn
        (resolve_opt_call_args args')
        to_lbl
        uw_lbl
        (dedup_annotations (expand_annotations groups anns'))
        obs
  | _ => tm
  end.

Definition resolve_opt_block
  (defs : IntMap (metadata U))
  (groups : IntMap (list fn_attr))
  (callees : rmap (list param_attr * list (list param_attr)))
  (b : block U) : block U :=
  mk_block
    (blk_id b)
    (List.map
       (fun '(id, p, md) => (id, p, resolve_opt_metadata_list defs md))
       (blk_phis b))
    (List.map
       (fun '(id, ins, md) =>
          (id, resolve_opt_instr groups callees ins, resolve_opt_metadata_list defs md))
       (blk_code b))
    (let '(id, tm, md) := blk_term b in
     (id, resolve_opt_terminator groups callees tm, resolve_opt_metadata_list defs md))
    (blk_comments b).

Definition resolve_opt_definition
  (defs : IntMap (metadata U))
  (groups : IntMap (list fn_attr))
  (callees : rmap (list param_attr * list (list param_attr)))
  (df : definition U (block U * list (block U)))
  : definition U (block U * list (block U)) :=
  let '(entry, bs) := df_instrs df in
  mk_definition
    (expand_decl_dedup groups (df_prototype df))
    (df_args df)
    (resolve_opt_block defs groups callees entry,
     List.map (resolve_opt_block defs groups callees) bs).

End ResolveForOpt.

(** Pre-optimization module-reference resolver for [verified-opt-fallback]:
    expands [#N] attribute groups and merges callee attributes across
    declarations, definitions, calls, and invokes while resolving only semantic
    value-metadata attachments inline so [!dbg], [!tbaa], and [distinct] loop
    metadata retain their [!N] node IDs. *)
Definition resolve_for_opt_tle
  (tles : toplevel_entities typ (block typ * list (block typ)))
  : toplevel_entities typ (block typ * list (block typ)) :=
  let defs := metadata_defs tles in
  let groups := attribute_groups tles in
  let callees := callee_attrs tles in
  List.map
    (fun tle =>
       match tle with
       | TLE_Declaration d => TLE_Declaration (expand_decl_dedup groups d)
       | TLE_Definition df => TLE_Definition (resolve_opt_definition defs groups callees df)
       | _ => tle
       end)
    tles.

(** Restore [!N] metadata references on instruction/phi/terminator attachments
    whose inline nodes match a lowered non-[distinct] [TLE_Metadata] entry. *)

Fixpoint lookup_md_id (tbl : list (int_ast * string)) (key : string) : option int_ast :=
  match tbl with
  | [] => None
  | (n, repr_s) :: rest =>
      if String.eqb key repr_s then Some n else lookup_md_id rest key
  end.

Definition build_md_repr_table
  (aux_tles : toplevel_entities typ (block typ * list (block typ)))
  : list (int_ast * string) :=
  List.flat_map
    (fun tle =>
       match tle with
       | TLE_Metadata (METADATA_Id (Anon n)) false node =>
           [(n, repr_metadata node)]
       | _ => []
       end)
    aux_tles.

Definition restore_attachment_md
  (tbl : list (int_ast * string)) (md : metadata typ) : metadata typ :=
  match md with
  | METADATA_Pair _ (METADATA_Id _) => md
  | METADATA_Pair _ (METADATA_File_info _) => md
  | METADATA_Pair kind node =>
      match lookup_md_id tbl (repr_metadata node) with
      | Some n => METADATA_Pair kind (METADATA_Id (Anon n))
      | None => md
      end
  | _ => md
  end.

Definition restore_block_md_ids
  (tbl : list (int_ast * string)) (b : block typ) : block typ :=
  mk_block
    (blk_id b)
    (List.map (fun '(lid, p, mds) => (lid, p, List.map (restore_attachment_md tbl) mds)) (blk_phis b))
    (List.map (fun '(iid, ins, mds) => (iid, ins, List.map (restore_attachment_md tbl) mds)) (blk_code b))
    (let '(iid, tm, mds) := blk_term b in
     (iid, tm, List.map (restore_attachment_md tbl) mds))
    (blk_comments b).

Definition restore_core_tle_md_ids
  (tbl : list (int_ast * string))
  (tle : toplevel_entity typ (block typ * list (block typ)))
  : toplevel_entity typ (block typ * list (block typ)) :=
  match tle with
  | TLE_Definition df =>
      let '(b0, bs) := df_instrs df in
      TLE_Definition
        {| df_prototype := df_prototype df;
           df_args      := df_args df;
           df_instrs    := (restore_block_md_ids tbl b0,
                            List.map (restore_block_md_ids tbl) bs) |}
  | _ => tle
  end.

(** Module-wide collision-free [Anon]/[Raw] local-identifier normalization. *)

Definition names_of_raw_id (r : raw_id) : list string :=
  match r with
  | Name s => [s]
  | _ => []
  end.

Definition names_of_ident (id : ident) : list string :=
  match id with
  | ID_Global _ => []
  | ID_Local r => names_of_raw_id r
  end.

Definition names_of_instr_id (iid : instr_id) : list string :=
  match iid with
  | IId r => names_of_raw_id r
  | IVoid _ => []
  end.

Fixpoint names_of_typ (t : typ) : list string :=
  let fix names_list (ts : list typ) : list string :=
    match ts with
    | [] => []
    | u :: us => names_of_typ u ++ names_list us
    end in
  match t with
  | TYPE_Pointer (Some sub) => names_of_typ sub
  | TYPE_Array _ sub => names_of_typ sub
  | TYPE_Function ret_t args_t _ => names_of_typ ret_t ++ names_list args_t
  | TYPE_Struct fields => names_list fields
  | TYPE_Packed_struct fields => names_list fields
  | TYPE_Vector _ sub => names_of_typ sub
  | TYPE_Identified id => names_of_ident id
  | _ => []
  end.

Definition names_of_param_attr (pa : param_attr) : list string :=
  match pa with
  | PARAMATTR_Byval t
  | PARAMATTR_Byref t
  | PARAMATTR_Preallocated t
  | PARAMATTR_Inalloca t
  | PARAMATTR_Sret t
  | PARAMATTR_Elementtype t
  | PARAMATTR_Range t _ _ => names_of_typ t
  | _ => []
  end.

Fixpoint names_of_exp (e : exp typ) : list string :=
  let fix names_texps (tes : list (typ * exp typ)) : list string :=
    match tes with
    | [] => []
    | (t, sub) :: rest => names_of_typ t ++ names_of_exp sub ++ names_texps rest
    end in
  match e with
  | EXP_Ident id => names_of_ident id
  | EXP_Cstring elts
  | EXP_Struct elts
  | EXP_Packed_struct elts
  | EXP_Array elts
  | EXP_Vector elts => names_texps elts
  | OP_IBinop _ t v1 v2
  | OP_ICmp _ _ t v1 v2
  | OP_FBinop _ _ t v1 v2
  | OP_FCmp _ _ t v1 v2 => names_of_typ t ++ names_of_exp v1 ++ names_of_exp v2
  | OP_Fneg _ (t, v)
  | OP_Freeze (t, v)
  | EXP_Splat (t, v) => names_of_typ t ++ names_of_exp v
  | OP_Conversion _ t1 v t2 => names_of_typ t1 ++ names_of_exp v ++ names_of_typ t2
  | OP_GetElementPtr _ t (tp, pv) idxs =>
      names_of_typ t ++ names_of_typ tp ++ names_of_exp pv ++ names_texps idxs
  | OP_ExtractElement (t1, v1) (t2, v2) =>
      names_of_typ t1 ++ names_of_exp v1 ++ names_of_typ t2 ++ names_of_exp v2
  | OP_InsertElement (t1, v1) (t2, v2) (t3, v3)
  | OP_ShuffleVector (t1, v1) (t2, v2) (t3, v3)
  | OP_Select _ (t1, v1) (t2, v2) (t3, v3) =>
      names_of_typ t1 ++ names_of_exp v1 ++
      names_of_typ t2 ++ names_of_exp v2 ++
      names_of_typ t3 ++ names_of_exp v3
  | OP_ExtractValue (t1, v1) _ => names_of_typ t1 ++ names_of_exp v1
  | OP_InsertValue (t1, v1) (t2, v2) _ =>
      names_of_typ t1 ++ names_of_exp v1 ++ names_of_typ t2 ++ names_of_exp v2
  | EXP_Metadata m => names_of_metadata m
  | EXP_BlockAddress _ blk => names_of_raw_id blk
  | _ => []
  end
with names_of_metadata (m : metadata typ) : list string :=
  let fix names_mds (mds : list (metadata typ)) : list string :=
    match mds with
    | [] => []
    | md :: rest => names_of_metadata md ++ names_mds rest
    end in
  match m with
  | METADATA_Const (t, v) => names_of_typ t ++ names_of_exp v
  | METADATA_Node mds => names_mds mds
  | METADATA_Pair m1 m2 => names_of_metadata m1 ++ names_of_metadata m2
  | _ => []
  end.

Definition names_of_texp (te : texp typ) : list string :=
  let '(t, e) := te in names_of_typ t ++ names_of_exp e.

Definition names_of_annotation (a : annotation typ) : list string :=
  match a with
  | ANN_metadata mds => List.flat_map names_of_metadata mds
  | ANN_prefix te
  | ANN_prologue te
  | ANN_personality te
  | ANN_num_elements te => names_of_texp te
  | ANN_ret_attribute pa => names_of_param_attr pa
  | _ => []
  end.

Definition names_of_operand (op : @operand typ) : list string :=
  match op with
  | SSA_value te => names_of_texp te
  | Metadata_string m => names_of_metadata m
  end.

Definition names_of_instr (ins : instr typ) : list string :=
  match ins with
  | INSTR_Op op => names_of_exp op
  | INSTR_Call fn args anns obs =>
      names_of_texp fn ++
      List.flat_map (fun '(te, pas) => names_of_texp te ++ List.flat_map names_of_param_attr pas) args ++
      List.flat_map names_of_annotation anns ++
      List.flat_map (fun ob => List.flat_map names_of_operand (ob_ops ob)) obs
  | INSTR_Alloca t anns =>
      names_of_typ t ++ List.flat_map names_of_annotation anns
  | INSTR_Load t ptr anns =>
      names_of_typ t ++ names_of_texp ptr ++ List.flat_map names_of_annotation anns
  | INSTR_Store val ptr anns =>
      names_of_texp val ++ names_of_texp ptr ++ List.flat_map names_of_annotation anns
  | INSTR_AtomicCmpXchg c =>
      names_of_texp (c_ptr c) ++ names_of_texp (c_cmp c) ++ names_of_texp (c_new c)
  | INSTR_AtomicRMW a =>
      names_of_texp (a_ptr a) ++ names_of_texp (a_val a)
  | INSTR_VAArg va t =>
      names_of_texp va ++ names_of_typ t
  | INSTR_LandingPad t _ cs =>
      names_of_typ t ++
      List.flat_map (fun cl => match cl with CATCH te | FILTER te => names_of_texp te end) cs
  | _ => []
  end.

Definition names_of_terminator (tm : terminator typ) : list string :=
  match tm with
  | TERM_Ret v
  | TERM_Resume v => names_of_texp v
  | TERM_Br v b1 b2 => names_of_texp v ++ names_of_raw_id b1 ++ names_of_raw_id b2
  | TERM_Br_1 b => names_of_raw_id b
  | TERM_Switch v def brs =>
      names_of_texp v ++ names_of_raw_id def ++
      List.flat_map (fun '(_, b) => names_of_raw_id b) brs
  | TERM_IndirectBr v brs _ =>
      names_of_texp v ++ List.flat_map names_of_raw_id brs
  | TERM_Invoke fn args to_l uw_l anns obs =>
      names_of_texp fn ++
      List.flat_map (fun '(te, pas) => names_of_texp te ++ List.flat_map names_of_param_attr pas) args ++
      names_of_raw_id to_l ++ names_of_raw_id uw_l ++
      List.flat_map names_of_annotation anns ++
      List.flat_map (fun ob => List.flat_map names_of_operand (ob_ops ob)) obs
  | _ => []
  end.

Definition names_of_block (b : block typ) : list string :=
  names_of_raw_id (blk_id b) ++
  List.flat_map
    (fun '(lid, Phi _ t pargs, mds) =>
       names_of_raw_id lid ++ names_of_typ t ++
       List.flat_map (fun '(bid, e) => names_of_raw_id bid ++ names_of_exp e) pargs ++
       List.flat_map names_of_metadata mds)
    (blk_phis b) ++
  List.flat_map
    (fun '(iid, ins, mds) =>
       names_of_instr_id iid ++ names_of_instr ins ++ List.flat_map names_of_metadata mds)
    (blk_code b) ++
  (let '(iid, tm, mds) := blk_term b in
   names_of_instr_id iid ++ names_of_terminator tm ++ List.flat_map names_of_metadata mds).

Definition names_of_declaration (d : declaration typ) : list string :=
  let '(ret_pas, arg_pass) := dc_param_attrs d in
  names_of_typ (dc_type d) ++
  List.flat_map names_of_param_attr ret_pas ++
  List.flat_map (List.flat_map names_of_param_attr) arg_pass ++
  List.flat_map names_of_annotation (dc_annotations d).

Definition names_of_tle
  (tle : toplevel_entity typ (block typ * list (block typ))) : list string :=
  match tle with
  | TLE_Declaration d => names_of_declaration d
  | TLE_Definition df =>
      let '(b0, bs) := df_instrs df in
      names_of_declaration (df_prototype df) ++
      List.flat_map names_of_raw_id (df_args df) ++
      names_of_block b0 ++
      List.flat_map names_of_block bs
  | TLE_Type_decl id t => names_of_ident id ++ names_of_typ t
  | TLE_Global g =>
      names_of_typ (g_typ g) ++
      (match g_exp g with None => [] | Some e => names_of_exp e end) ++
      List.flat_map names_of_annotation (g_annotations g)
  | TLE_Metadata _ _ md => names_of_metadata md
  | _ => []
  end.

Fixpoint repeat_underscore (n : nat) : string :=
  match n with
  | O => ""%string
  | S n' => String "_"%char (repeat_underscore n')
  end.

Definition choose_anon_prefix (names : list string) : string :=
  if negb (List.existsb (str_starts_with "_llv_"%string) names) then
    "_llv_"%string
  else
    let max_len := List.fold_left (fun acc s => Nat.max acc (String.length s)) names 0%nat in
    String.append "_llv"%string (String.append (repeat_underscore max_len) "_"%string).

Section RenameLocal.
Context (ren : raw_id -> raw_id).

Definition ren_ident (id : ident) : ident :=
  match id with
  | ID_Global g => ID_Global g
  | ID_Local l => ID_Local (ren l)
  end.

Definition ren_instr_id (iid : instr_id) : instr_id :=
  match iid with
  | IId l => IId (ren l)
  | IVoid n => IVoid n
  end.

Fixpoint ren_typ (t : typ) : typ :=
  let fix ren_typs (ts : list typ) : list typ :=
    match ts with
    | [] => []
    | u :: us => ren_typ u :: ren_typs us
    end in
  match t with
  | TYPE_I sz => TYPE_I sz
  | TYPE_B sz => TYPE_B sz
  | TYPE_Iptr => TYPE_Iptr
  | TYPE_Pointer None => TYPE_Pointer None
  | TYPE_Pointer (Some sub) => TYPE_Pointer (Some (ren_typ sub))
  | TYPE_Void => TYPE_Void
  | TYPE_FP fp => TYPE_FP fp
  | TYPE_Label => TYPE_Label
  | TYPE_Token => TYPE_Token
  | TYPE_Metadata => TYPE_Metadata
  | TYPE_X86_mmx => TYPE_X86_mmx
  | TYPE_Array sz sub => TYPE_Array sz (ren_typ sub)
  | TYPE_Function ret_t args_t vararg =>
      TYPE_Function (ren_typ ret_t) (ren_typs args_t) vararg
  | TYPE_Struct fields => TYPE_Struct (ren_typs fields)
  | TYPE_Packed_struct fields => TYPE_Packed_struct (ren_typs fields)
  | TYPE_Opaque => TYPE_Opaque
  | TYPE_Vector sz sub => TYPE_Vector sz (ren_typ sub)
  | TYPE_Identified id => TYPE_Identified (ren_ident id)
  end.

Definition ren_param_attr (pa : param_attr) : param_attr :=
  match pa with
  | PARAMATTR_Byval t => PARAMATTR_Byval (ren_typ t)
  | PARAMATTR_Byref t => PARAMATTR_Byref (ren_typ t)
  | PARAMATTR_Preallocated t => PARAMATTR_Preallocated (ren_typ t)
  | PARAMATTR_Inalloca t => PARAMATTR_Inalloca (ren_typ t)
  | PARAMATTR_Sret t => PARAMATTR_Sret (ren_typ t)
  | PARAMATTR_Elementtype t => PARAMATTR_Elementtype (ren_typ t)
  | PARAMATTR_Range t a b => PARAMATTR_Range (ren_typ t) a b
  | _ => pa
  end.

Fixpoint ren_exp (e : exp typ) : exp typ :=
  let fix ren_texps (tes : list (typ * exp typ)) : list (typ * exp typ) :=
    match tes with
    | [] => []
    | (t, sub) :: rest => (ren_typ t, ren_exp sub) :: ren_texps rest
    end in
  match e with
  | EXP_Ident id => EXP_Ident (ren_ident id)
  | EXP_Integer x => EXP_Integer x
  | EXP_Float f => EXP_Float f
  | EXP_Bool b => EXP_Bool b
  | EXP_Null => EXP_Null
  | EXP_Zero_initializer => EXP_Zero_initializer
  | EXP_Cstring elts => EXP_Cstring (ren_texps elts)
  | EXP_Undef => EXP_Undef
  | EXP_Poison => EXP_Poison
  | EXP_Struct fields => EXP_Struct (ren_texps fields)
  | EXP_Packed_struct fields => EXP_Packed_struct (ren_texps fields)
  | EXP_Array elts => EXP_Array (ren_texps elts)
  | EXP_Vector elts => EXP_Vector (ren_texps elts)
  | OP_IBinop iop t v1 v2 => OP_IBinop iop (ren_typ t) (ren_exp v1) (ren_exp v2)
  | OP_ICmp ss cmp t v1 v2 => OP_ICmp ss cmp (ren_typ t) (ren_exp v1) (ren_exp v2)
  | OP_FBinop fop fm t v1 v2 => OP_FBinop fop fm (ren_typ t) (ren_exp v1) (ren_exp v2)
  | OP_Fneg fm (t, v) => OP_Fneg fm (ren_typ t, ren_exp v)
  | OP_FCmp cmp fm t v1 v2 => OP_FCmp cmp fm (ren_typ t) (ren_exp v1) (ren_exp v2)
  | OP_Conversion conv t1 v t2 => OP_Conversion conv (ren_typ t1) (ren_exp v) (ren_typ t2)
  | OP_GetElementPtr gf t (tp, pv) idxs =>
      OP_GetElementPtr gf (ren_typ t) (ren_typ tp, ren_exp pv) (ren_texps idxs)
  | OP_ExtractElement (tv, vec) (ti, idx) =>
      OP_ExtractElement (ren_typ tv, ren_exp vec) (ren_typ ti, ren_exp idx)
  | OP_InsertElement (tv, vec) (te, elt) (ti, idx) =>
      OP_InsertElement (ren_typ tv, ren_exp vec) (ren_typ te, ren_exp elt) (ren_typ ti, ren_exp idx)
  | OP_ShuffleVector (t1, v1) (t2, v2) (tm, mask) =>
      OP_ShuffleVector (ren_typ t1, ren_exp v1) (ren_typ t2, ren_exp v2) (ren_typ tm, ren_exp mask)
  | OP_ExtractValue (tv, vec) idxs =>
      OP_ExtractValue (ren_typ tv, ren_exp vec) idxs
  | OP_InsertValue (tv, vec) (te, elt) idxs =>
      OP_InsertValue (ren_typ tv, ren_exp vec) (ren_typ te, ren_exp elt) idxs
  | OP_Select fm (tc, cnd) (t1, v1) (t2, v2) =>
      OP_Select fm (ren_typ tc, ren_exp cnd) (ren_typ t1, ren_exp v1) (ren_typ t2, ren_exp v2)
  | OP_Freeze (t, v) => OP_Freeze (ren_typ t, ren_exp v)
  | EXP_Asm se as_ id_ uw tmpl cstr => EXP_Asm se as_ id_ uw tmpl cstr
  | EXP_Metadata m => EXP_Metadata (ren_metadata m)
  | EXP_Splat (t, elt) => EXP_Splat (ren_typ t, ren_exp elt)
  | EXP_BlockAddress fn blk => EXP_BlockAddress fn (ren blk)
  end
with ren_metadata (m : metadata typ) : metadata typ :=
  let fix ren_mds (mds : list (metadata typ)) : list (metadata typ) :=
    match mds with
    | [] => []
    | md :: rest => ren_metadata md :: ren_mds rest
    end in
  match m with
  | METADATA_Null => METADATA_Null
  | METADATA_Id id => METADATA_Id id
  | METADATA_Const (t, v) => METADATA_Const (ren_typ t, ren_exp v)
  | METADATA_Node mds => METADATA_Node (ren_mds mds)
  | METADATA_Pair m1 m2 => METADATA_Pair (ren_metadata m1) (ren_metadata m2)
  | METADATA_Debug dstr c => METADATA_Debug dstr c
  | METADATA_File_info fi => METADATA_File_info fi
  end.

Definition ren_texp (te : texp typ) : texp typ :=
  let '(t, e) := te in (ren_typ t, ren_exp e).

Definition ren_annotation (a : annotation typ) : annotation typ :=
  match a with
  | ANN_metadata mds => ANN_metadata (List.map ren_metadata mds)
  | ANN_prefix te => ANN_prefix (ren_texp te)
  | ANN_prologue te => ANN_prologue (ren_texp te)
  | ANN_personality te => ANN_personality (ren_texp te)
  | ANN_num_elements te => ANN_num_elements (ren_texp te)
  | ANN_ret_attribute pa => ANN_ret_attribute (ren_param_attr pa)
  | _ => a
  end.

Definition ren_operand (op : @operand typ) : @operand typ :=
  match op with
  | SSA_value te => SSA_value (ren_texp te)
  | Metadata_string m => Metadata_string (ren_metadata m)
  end.

Definition ren_operand_bundle (ob : @operand_bundle typ) : @operand_bundle typ :=
  {| ob_tag := ob_tag ob; ob_ops := List.map ren_operand (ob_ops ob) |}.

Definition ren_call_arg
  (ca : texp typ * list param_attr) : texp typ * list param_attr :=
  let '(te, pas) := ca in (ren_texp te, List.map ren_param_attr pas).

Definition ren_instr (ins : instr typ) : instr typ :=
  match ins with
  | INSTR_Comment msg => INSTR_Comment msg
  | INSTR_Op op => INSTR_Op (ren_exp op)
  | INSTR_Call fn args anns obs =>
      INSTR_Call
        (ren_texp fn)
        (List.map ren_call_arg args)
        (List.map ren_annotation anns)
        (List.map ren_operand_bundle obs)
  | INSTR_Alloca t anns =>
      INSTR_Alloca (ren_typ t) (List.map ren_annotation anns)
  | INSTR_Load t ptr anns =>
      INSTR_Load (ren_typ t) (ren_texp ptr) (List.map ren_annotation anns)
  | INSTR_Store val ptr anns =>
      INSTR_Store (ren_texp val) (ren_texp ptr) (List.map ren_annotation anns)
  | INSTR_Fence ss ord => INSTR_Fence ss ord
  | INSTR_AtomicCmpXchg c =>
      INSTR_AtomicCmpXchg
        {| c_weak             := c_weak c;
           c_volatile         := c_volatile c;
           c_ptr              := ren_texp (c_ptr c);
           c_cmp              := ren_texp (c_cmp c);
           c_new              := ren_texp (c_new c);
           c_syncscope        := c_syncscope c;
           c_success_ordering := c_success_ordering c;
           c_failure_ordering := c_failure_ordering c;
           c_align            := c_align c |}
  | INSTR_AtomicRMW a =>
      INSTR_AtomicRMW
        {| a_volatile  := a_volatile a;
           a_operation := a_operation a;
           a_ptr       := ren_texp (a_ptr a);
           a_val       := ren_texp (a_val a);
           a_syncscope := a_syncscope a;
           a_ordering  := a_ordering a;
           a_align     := a_align a |}
  | INSTR_VAArg va t => INSTR_VAArg (ren_texp va) (ren_typ t)
  | INSTR_LandingPad t cl cs =>
      INSTR_LandingPad
        (ren_typ t)
        cl
        (List.map
           (fun clause =>
              match clause with
              | CATCH te => CATCH (ren_texp te)
              | FILTER te => FILTER (ren_texp te)
              end)
           cs)
  end.

Definition ren_terminator (tm : terminator typ) : terminator typ :=
  match tm with
  | TERM_Ret v => TERM_Ret (ren_texp v)
  | TERM_Ret_void => TERM_Ret_void
  | TERM_Br v b1 b2 => TERM_Br (ren_texp v) (ren b1) (ren b2)
  | TERM_Br_1 b => TERM_Br_1 (ren b)
  | TERM_Switch v def brs =>
      TERM_Switch (ren_texp v) (ren def) (List.map (fun '(lit, b) => (lit, ren b)) brs)
  | TERM_IndirectBr v brs fn =>
      TERM_IndirectBr (ren_texp v) (List.map ren brs) fn
  | TERM_Resume v => TERM_Resume (ren_texp v)
  | TERM_Invoke fn args to_l uw_l anns obs =>
      TERM_Invoke
        (ren_texp fn)
        (List.map ren_call_arg args)
        (ren to_l)
        (ren uw_l)
        (List.map ren_annotation anns)
        (List.map ren_operand_bundle obs)
  | TERM_Unreachable => TERM_Unreachable
  end.

Definition ren_phi (p : phi typ) : phi typ :=
  let '(Phi fm t pargs) := p in
  Phi fm (ren_typ t) (List.map (fun '(bid, e) => (ren bid, ren_exp e)) pargs).

Definition ren_block (b : block typ) : block typ :=
  mk_block
    (ren (blk_id b))
    (List.map (fun '(lid, p, mds) => (ren lid, ren_phi p, List.map ren_metadata mds)) (blk_phis b))
    (List.map (fun '(iid, ins, mds) => (ren_instr_id iid, ren_instr ins, List.map ren_metadata mds)) (blk_code b))
    (let '(iid, tm, mds) := blk_term b in
     (ren_instr_id iid, ren_terminator tm, List.map ren_metadata mds))
    (blk_comments b).

Definition ren_declaration (d : declaration typ) : declaration typ :=
  let '(ret_pas, arg_pass) := dc_param_attrs d in
  {| dc_name        := dc_name d;
     dc_type        := ren_typ (dc_type d);
     dc_param_attrs := (List.map ren_param_attr ret_pas,
                        List.map (List.map ren_param_attr) arg_pass);
     dc_attrs       := dc_attrs d;
     dc_annotations := List.map ren_annotation (dc_annotations d) |}.

Definition ren_tle
  (tle : toplevel_entity typ (block typ * list (block typ)))
  : toplevel_entity typ (block typ * list (block typ)) :=
  match tle with
  | TLE_Declaration d => TLE_Declaration (ren_declaration d)
  | TLE_Definition df =>
      let '(b0, bs) := df_instrs df in
      TLE_Definition
        {| df_prototype := ren_declaration (df_prototype df);
           df_args      := List.map ren (df_args df);
           df_instrs    := (ren_block b0, List.map ren_block bs) |}
  | TLE_Type_decl id t => TLE_Type_decl (ren_ident id) (ren_typ t)
  | TLE_Global g =>
      TLE_Global
        {| g_ident                  := g_ident g;
           g_typ                    := ren_typ (g_typ g);
           g_constant               := g_constant g;
           g_exp                    := option_map ren_exp (g_exp g);
           g_externally_initialized := g_externally_initialized g;
           g_alias                  := g_alias g;
           g_annotations            := List.map ren_annotation (g_annotations g) |}
  | TLE_Metadata id distinct md => TLE_Metadata id distinct (ren_metadata md)
  | _ => tle
  end.

End RenameLocal.

Definition normalize_tles_anon
  (tles : toplevel_entities typ (block typ * list (block typ)))
  : toplevel_entities typ (block typ * list (block typ)) :=
  let pfx := choose_anon_prefix (List.flat_map names_of_tle tles) in
  List.map (ren_tle (rename_local_raw_id pfx)) tles.

(** Direct structural exporter over [CFG.mcfg dtyp]. *)
Definition export_mcfg_to_tle
  (M : CFG.mcfg dtyp)
  : (string + toplevel_entities typ (block typ * list (block typ)))%type :=
  res_map
    (fun m => normalize_tles_anon (@toplevel_entities_of_modul typ (block typ * list (block typ))%type m))
    (reify_modul M).

(** Prototype-preserving exporter using the pre-[convert_types] [CFG.mcfg typ]
    header table so [TYPE_Function] signatures (erased to [DTYPE_Pointer] by
    [TypToDtyp.typ_to_dtyp]) and variadic call sites serialize as valid LLVM 23
    textual IR under [ShowAST.showProg]. *)

Fixpoint lookup_src_decl
  (decls : list (declaration typ)) (fid : function_id) : option (declaration typ) :=
  match decls with
  | [] => None
  | d :: rest =>
      if raw_id_eqb fid (dc_name d) then Some d else lookup_src_decl rest fid
  end.

Definition lower_fn_sig
  (env : list (ident * typ)) (d_src : declaration typ) : res (function_id * fn_sig) :=
  match dc_type d_src with
  | TYPE_Function ret_t args_t vararg =>
      res_bind (lower_src_typ env ret_t) (fun ret_t' =>
      res_bind (res_map_list (lower_src_typ env) args_t) (fun args_t' =>
      inr (dc_name d_src, (ret_t', args_t', vararg))))
  | _ =>
      inl "export_mcfg_with_typ: source declaration lacks TYPE_Function"%string
  end.

Definition reify_declaration_with_src
  (env : list (ident * typ)) (src_decls : list (declaration typ))
  (d : declaration dtyp) : res (declaration typ) :=
  match lookup_src_decl src_decls (dc_name d) with
  | None =>
      inl "export_mcfg_with_typ: missing source prototype for declaration"%string
  | Some d_src =>
      match dc_type d_src with
      | TYPE_Function ret_t args_t vararg =>
          let '(ret_pas, arg_pass) := dc_param_attrs d in
          if negb (Nat.eqb (List.length args_t) (List.length arg_pass)) then
            inl "export_mcfg_with_typ: declaration parameter/attribute arity mismatch"%string
          else
            res_bind (lower_src_typ env ret_t) (fun ret_t' =>
            res_bind (res_map_list (lower_src_typ env) args_t) (fun args_t' =>
            res_bind (lower_param_attrs env ret_pas) (fun ret_pas' =>
            res_bind (res_map_list (lower_param_attrs env) arg_pass) (fun arg_pass' =>
            res_bind (reify_annotations env (dc_annotations d)) (fun anns' =>
            inr {| dc_name        := dc_name d;
                   dc_type        := TYPE_Function ret_t' args_t' vararg;
                   dc_param_attrs := (dedup_param_attrs ret_pas',
                                      List.map dedup_param_attrs arg_pass');
                   dc_attrs       := dedup_fn_attrs (dc_attrs d);
                   dc_annotations := anns' |})))))
      | _ =>
          inl "export_mcfg_with_typ: source declaration lacks TYPE_Function"%string
      end
  end.

Definition reify_definition_with_src
  (env : list (ident * typ))
  (src_decls : list (declaration typ))
  (sigs : list (function_id * fn_sig))
  (df : definition dtyp (CFG.cfg dtyp))
  : res (definition typ (block typ * list (block typ))) :=
  res_bind (reify_declaration_with_src env src_decls (df_prototype df)) (fun proto' =>
  match dc_type proto' with
  | TYPE_Function _ args_t _ =>
      if negb (Nat.eqb (List.length (df_args df)) (List.length args_t)) then
        inl "export_mcfg_with_typ: definition parameter count mismatch"%string
      else
        res_bind (reify_cfg_blocks env sigs (df_instrs df)) (fun body' =>
        inr {| df_prototype := proto';
               df_args      := df_args df;
               df_instrs    := body' |})
  | _ =>
      inl "export_mcfg_with_typ: internal non-function prototype"%string
  end).

Definition export_mcfg_with_typ_raw
  (M_src : CFG.mcfg typ) (M_opt : CFG.mcfg dtyp)
  : (string + toplevel_entities typ (block typ * list (block typ)))%type :=
  let env := m_type_defs M_src in
  let src_decls := (m_declarations M_src ++ List.map df_prototype (m_definitions M_src))%list in
  res_bind (res_map_list (lower_fn_sig env) src_decls) (fun sigs =>
  res_bind (res_map_list (reify_global env) (m_globals M_opt)) (fun globs' =>
  res_bind (res_map_list (reify_declaration_with_src env src_decls) (m_declarations M_opt))
    (fun decls' =>
  res_bind (res_map_list (reify_definition_with_src env src_decls sigs) (m_definitions M_opt))
    (fun defs' =>
  let m_out : @CFG.modul typ (block typ * list (block typ))%type :=
    {| m_name         := m_name M_opt;
       m_target       := m_target M_opt;
       m_datalayout   := m_datalayout M_opt;
       m_type_defs    := [];
       m_globals      := globs';
       m_declarations := decls';
       m_definitions  := defs' |} in
  inr (@toplevel_entities_of_modul typ (block typ * list (block typ))%type m_out))))).

Definition export_mcfg_with_typ
  (M_src : CFG.mcfg typ) (M_opt : CFG.mcfg dtyp)
  : (string + toplevel_entities typ (block typ * list (block typ)))%type :=
  res_map normalize_tles_anon (export_mcfg_with_typ_raw M_src M_opt).

Definition strip_attr_grp_refs (fas : list fn_attr) : list fn_attr :=
  List.filter
    (fun fa => match fa with FNATTR_Attr_grp _ => false | _ => true end)
    fas.

Definition lower_tle_aux
  (env : list (ident * typ))
  (groups : IntMap (list fn_attr))
  (tle : toplevel_entity typ (block typ * list (block typ)))
  : res (list (toplevel_entity typ (block typ * list (block typ)))) :=
  match tle with
  | TLE_Metadata id distinct md =>
      res_bind (map_res_metadata (lower_src_typ env) id) (fun id' =>
      res_bind (map_res_metadata (lower_src_typ env) md) (fun md' =>
      inr [TLE_Metadata id' distinct md']))
  | TLE_Attribute_group i attrs =>
      let attrs' := dedup_fn_attrs (strip_attr_grp_refs (expand_fn_attrs groups attrs)) in
      match attrs' with
      | [] => inr []
      | _ :: _ => inr [TLE_Attribute_group i attrs']
      end
  | _ => inr []
  end.

Definition export_mcfg_with_tle
  (tles_src : toplevel_entities typ (block typ * list (block typ)))
  (M_opt : CFG.mcfg dtyp)
  : (string + toplevel_entities typ (block typ * list (block typ)))%type :=
  let M_src := CFG.mcfg_of_tle tles_src in
  let env := m_type_defs M_src in
  let groups := attribute_groups tles_src in
  res_bind (export_mcfg_with_typ_raw M_src M_opt) (fun core_tles =>
  res_bind (res_map_list (lower_tle_aux env groups) tles_src) (fun aux_lists =>
  let aux_tles := List.concat aux_lists in
  let md_tbl := build_md_repr_table aux_tles in
  let core_restored := List.map (restore_core_tle_md_ids md_tbl) core_tles in
  inr (normalize_tles_anon (core_restored ++ aux_tles)%list))).
