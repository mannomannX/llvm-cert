(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Module Split/Merge Composition Checker ([CertPasses.ModuleMerge])

    Removes [ir-bridge]'s module splitter and merger from the semantic TCB by
    validating [m_merged] directly against [m_orig] and a list of verified
    per-function slices [verified_slices]:

    1. **Global Layout & Alignment Identity (F-33, F-47)**:
       Enforces [m_globals m_merged = m_globals m_orig], rejects
       [LINKAGE_Extern_weak] on globals, and checks exact preservation of
       deduplicated module [blockaddress] allocations.
    2. **Declaration & Symbol Table Preservation (F-33)**:
       Enforces [m_declarations m_merged = m_declarations m_orig], rejects
       [LINKAGE_Extern_weak] on declarations and definitions, and enforces
       [NoDup] across all declared and defined function identifiers.
    3. **Prototype & Attribute Contract Preservation (F-19)**:
       Enforces positional [Forall2] alignment of [m_definitions] with exact
       equality of [df_prototype] and [df_args], statically blocking unverified
       [-O2]-inferred attributes ([willreturn], [readonly], [noalias],
       [memory(...)], [noundef], etc.) on merged function headers.
    4. **Per-Function Provenance & Compositional Linking (F-20, F-24, F-33)**:
       Requires every definition pair [(df_orig, df_merged)] either to be an
       unchanged pass-through ([df_merged = df_orig]) or to match a verified
       single-function slice [(fid, m_slice_src, m_slice_tgt)] (allowing
       externalized linkage on [m_slice_src] as emitted by [ir-bridge split]),
       and lifts open-world per-slice refinement to whole-module [@prog_refines]
       and end-to-end [IPZ -> IP64Bit] [I2F_toplevel.model_refine]. *)

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
  Bool.
Import ListNotations.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  Eq.Eqit
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
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
  Pipeline.

Set Default Goal Selector "!".
#[local] Open Scope list_scope.
#[local] Existing Instance MemoryModelStateV.
#[local] Existing Instance MemoryModelPrimitivesV.

(** * 1. Transparent Boolean Equality Deciders for Vellvm [mcfg dtyp] ASTs *)

Definition mm_dec_eqb {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
  (x y : A) : bool :=
  if dec x y then true else false.

Lemma mm_dec_eqb_eq {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
  (x y : A) :
  mm_dec_eqb dec x y = true <-> x = y.
Proof.
  unfold mm_dec_eqb; destruct (dec x y) as [Heq | Hne]; split; intros H;
    [exact Heq | reflexivity | discriminate H | exfalso; exact (Hne H)].
Qed.

Definition mm_unit_eqb (_ _ : unit) : bool := true.

Lemma mm_unit_eqb_eq (x y : unit) :
  mm_unit_eqb x y = true <-> x = y.
Proof.
  destruct x, y; split; reflexivity.
Qed.

Definition mm_bool_eqb : bool -> bool -> bool := Bool.eqb.

Lemma mm_bool_eqb_eq (x y : bool) :
  mm_bool_eqb x y = true <-> x = y.
Proof.
  exact (Bool.eqb_true_iff x y).
Qed.

Definition mm_pos_eqb : positive -> positive -> bool := Pos.eqb.

Lemma mm_pos_eqb_eq (x y : positive) :
  mm_pos_eqb x y = true <-> x = y.
Proof.
  exact (Pos.eqb_eq x y).
Qed.

Definition mm_N_eqb : N -> N -> bool := N.eqb.

Lemma mm_N_eqb_eq (x y : N) :
  mm_N_eqb x y = true <-> x = y.
Proof.
  exact (N.eqb_eq x y).
Qed.

Definition mm_Z_eqb : Z -> Z -> bool := Z.eqb.

Lemma mm_Z_eqb_eq (x y : Z) :
  mm_Z_eqb x y = true <-> x = y.
Proof.
  exact (Z.eqb_eq x y).
Qed.

Definition mm_string_eqb : string -> string -> bool :=
  mm_dec_eqb String.string_dec.

Lemma mm_string_eqb_eq (x y : string) :
  mm_string_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_dtyp_eqb : dtyp -> dtyp -> bool :=
  mm_dec_eqb dtyp_eq_dec.

Lemma mm_dtyp_eqb_eq (x y : dtyp) :
  mm_dtyp_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_block_addr_eqb :
  function_id * block_id -> function_id * block_id -> bool :=
  mm_dec_eqb block_address_eq_dec.

Lemma mm_block_addr_eqb_eq (x y : function_id * block_id) :
  mm_block_addr_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_dec_uint_eq_dec (x y : Decimal.uint) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition mm_dec_sint_eq_dec (x y : Decimal.signed_int) : {x = y} + {x <> y}.
Proof. decide equality; apply mm_dec_uint_eq_dec. Defined.

Definition mm_decimal_eq_dec (x y : Decimal.decimal) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply mm_dec_sint_eq_dec; apply mm_dec_uint_eq_dec.
Defined.

Definition mm_hex_uint_eq_dec (x y : Hexadecimal.uint) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition mm_hex_sint_eq_dec (x y : Hexadecimal.signed_int) : {x = y} + {x <> y}.
Proof. decide equality; apply mm_hex_uint_eq_dec. Defined.

Definition mm_int_syntax_eq_dec (x y : int_syntax) : {x = y} + {x <> y}.
Proof.
  decide equality; [apply mm_dec_sint_eq_dec | apply mm_hex_sint_eq_dec].
Defined.

Definition mm_int_syntax_eqb : int_syntax -> int_syntax -> bool :=
  mm_dec_eqb mm_int_syntax_eq_dec.

Lemma mm_int_syntax_eqb_eq (x y : int_syntax) :
  mm_int_syntax_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_decimal_eqb : Decimal.decimal -> Decimal.decimal -> bool :=
  mm_dec_eqb mm_decimal_eq_dec.

Lemma mm_decimal_eqb_eq (x y : Decimal.decimal) :
  mm_decimal_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_hex_uint_eqb : Hexadecimal.uint -> Hexadecimal.uint -> bool :=
  mm_dec_eqb mm_hex_uint_eq_dec.

Lemma mm_hex_uint_eqb_eq (x y : Hexadecimal.uint) :
  mm_hex_uint_eqb x y = true <-> x = y.
Proof.
  apply mm_dec_eqb_eq.
Qed.

Definition mm_option_eqb {A : Type} (eqA : A -> A -> bool)
  (o1 o2 : option A) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x1, Some x2 => eqA x1 x2
  | _, _ => false
  end.

Lemma mm_option_eqb_eq {A : Type} (eqA : A -> A -> bool)
  (HA : forall x y, eqA x y = true <-> x = y)
  (o1 o2 : option A) :
  mm_option_eqb eqA o1 o2 = true <-> o1 = o2.
Proof.
  destruct o1 as [x1 |], o2 as [x2 |]; cbn [mm_option_eqb].
  - rewrite (HA x1 x2); split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - split; discriminate.
  - split; discriminate.
  - split; reflexivity.
Qed.

Definition mm_prod_eqb {A B : Type}
  (eqA : A -> A -> bool) (eqB : B -> B -> bool)
  (p1 p2 : A * B) : bool :=
  match p1, p2 with
  | (a1, b1), (a2, b2) => eqA a1 a2 && eqB b1 b2
  end.

Lemma mm_prod_eqb_eq {A B : Type}
  (eqA : A -> A -> bool) (eqB : B -> B -> bool)
  (HA : forall x y, eqA x y = true <-> x = y)
  (HB : forall x y, eqB x y = true <-> x = y)
  (p1 p2 : A * B) :
  mm_prod_eqb eqA eqB p1 p2 = true <-> p1 = p2.
Proof.
  destruct p1 as [a1 b1], p2 as [a2 b2]; cbn [mm_prod_eqb].
  rewrite Bool.andb_true_iff, (HA a1 a2), (HB b1 b2).
  split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
Qed.

Definition mm_list_eqb {A : Type} (eqA : A -> A -> bool) :
  list A -> list A -> bool :=
  fix go l1 l2 :=
    match l1, l2 with
    | [], [] => true
    | x1 :: r1, x2 :: r2 => eqA x1 x2 && go r1 r2
    | _, _ => false
    end.

Lemma mm_list_eqb_in_eq {A : Type} (eqA : A -> A -> bool) (l1 : list A)
  (IH : forall x1, In x1 l1 -> forall x2, eqA x1 x2 = true <-> x1 = x2) :
  forall l2, mm_list_eqb eqA l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [| x1 r1 IHr]; intros [| x2 r2]; cbn [mm_list_eqb].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff.
    rewrite (IH x1 (or_introl Logic.eq_refl) x2).
    rewrite (IHr (fun z Hz => IH z (or_intror Hz)) r2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
Qed.

Lemma mm_list_eqb_eq {A : Type} (eqA : A -> A -> bool)
  (HA : forall x y, eqA x y = true <-> x = y)
  (l1 l2 : list A) :
  mm_list_eqb eqA l1 l2 = true <-> l1 = l2.
Proof.
  exact (mm_list_eqb_in_eq eqA l1 (fun x1 _ x2 => HA x1 x2) l2).
Qed.

Definition mm_instr_id_eqb (x y : instr_id) : bool :=
  match x, y with
  | IId id1, IId id2 => raw_id_eqb id1 id2
  | IVoid n1, IVoid n2 => mm_Z_eqb n1 n2
  | _, _ => false
  end.

Lemma mm_instr_id_eqb_eq (x y : instr_id) :
  mm_instr_id_eqb x y = true <-> x = y.
Proof.
  destruct x as [id1 | n1], y as [id2 | n2]; cbn [mm_instr_id_eqb];
    try (split; discriminate).
  - rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_Z_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_file_info_eqb (f1 f2 : file_info) : bool :=
  mm_string_eqb (filename f1) (filename f2) &&
  mm_Z_eqb (start_line f1) (start_line f2) &&
  mm_Z_eqb (start_col f1) (start_col f2) &&
  mm_Z_eqb (end_line f1) (end_line f2) &&
  mm_Z_eqb (end_col f1) (end_col f2).

Lemma mm_file_info_eqb_eq (f1 f2 : file_info) :
  mm_file_info_eqb f1 f2 = true <-> f1 = f2.
Proof.
  destruct f1 as [fn1 sl1 sc1 el1 ec1], f2 as [fn2 sl2 sc2 el2 ec2].
  unfold mm_file_info_eqb; cbn [filename start_line start_col end_line end_col].
  rewrite !Bool.andb_true_iff, mm_string_eqb_eq, !mm_Z_eqb_eq.
  split.
  - intros [[[[-> ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_fp_variant_eqb (x y : floating_point_variant) : bool :=
  match x, y with
  | FP_half, FP_half
  | FP_bfloat, FP_bfloat
  | FP_float, FP_float
  | FP_double, FP_double
  | FP_fp128, FP_fp128
  | FP_x86_fp80, FP_x86_fp80
  | FP_ppc_fp128, FP_ppc_fp128 => true
  | _, _ => false
  end.

Lemma mm_fp_variant_eqb_eq (x y : floating_point_variant) :
  mm_fp_variant_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_fp_variant_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Fixpoint mm_typ_eqb (t1 t2 : typ) : bool :=
  match t1, t2 with
  | TYPE_I sz1, TYPE_I sz2 => mm_pos_eqb sz1 sz2
  | TYPE_B sz1, TYPE_B sz2 => mm_pos_eqb sz1 sz2
  | TYPE_Iptr, TYPE_Iptr => true
  | TYPE_Pointer (Some u1), TYPE_Pointer (Some u2) => mm_typ_eqb u1 u2
  | TYPE_Pointer None, TYPE_Pointer None => true
  | TYPE_Void, TYPE_Void => true
  | TYPE_FP fp1, TYPE_FP fp2 => mm_fp_variant_eqb fp1 fp2
  | TYPE_Label, TYPE_Label => true
  | TYPE_Token, TYPE_Token => true
  | TYPE_Metadata, TYPE_Metadata => true
  | TYPE_X86_mmx, TYPE_X86_mmx => true
  | TYPE_Array sz1 u1, TYPE_Array sz2 u2 =>
      mm_N_eqb sz1 sz2 && mm_typ_eqb u1 u2
  | TYPE_Function ret1 args1 va1, TYPE_Function ret2 args2 va2 =>
      mm_typ_eqb ret1 ret2 && mm_list_eqb mm_typ_eqb args1 args2 && mm_bool_eqb va1 va2
  | TYPE_Struct fs1, TYPE_Struct fs2 =>
      mm_list_eqb mm_typ_eqb fs1 fs2
  | TYPE_Packed_struct fs1, TYPE_Packed_struct fs2 =>
      mm_list_eqb mm_typ_eqb fs1 fs2
  | TYPE_Opaque, TYPE_Opaque => true
  | TYPE_Vector sz1 u1, TYPE_Vector sz2 u2 =>
      mm_N_eqb sz1 sz2 && mm_typ_eqb u1 u2
  | TYPE_Identified id1, TYPE_Identified id2 =>
      ident_eqb id1 id2
  | _, _ => false
  end.

Lemma mm_typ_eqb_eq : forall (t1 t2 : typ),
  mm_typ_eqb t1 t2 = true <-> t1 = t2.
Proof.
  apply (@AstLib.typ_ind (fun t1 => forall t2, mm_typ_eqb t1 t2 = true <-> t1 = t2)).
  - intros sz1 [sz2 | | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite mm_pos_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros sz1 [| sz2 | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite mm_pos_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros u1 IHu [| | | [u2 |] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite (IHu u2); split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros [| | | [u2 |] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros fp1 [| | | [|] | | fp2 | | | | | | | | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite mm_fp_variant_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros sz1 u1 IHu [| | | [|] | | | | | | | sz2 u2 | | | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite Bool.andb_true_iff, mm_N_eqb_eq, (IHu u2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - intros ret1 args1 va1 IHret IHargs [| | | [|] | | | | | | | | ret2 args2 va2 | | | | |];
      cbn [mm_typ_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, (IHret ret2),
      (mm_list_eqb_in_eq mm_typ_eqb args1 IHargs args2), mm_bool_eqb_eq.
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - intros fs1 IHfs [| | | [|] | | | | | | | | | fs2 | | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite (mm_list_eqb_in_eq mm_typ_eqb fs1 IHfs fs2).
    split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros fs1 IHfs [| | | [|] | | | | | | | | | | fs2 | | |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite (mm_list_eqb_in_eq mm_typ_eqb fs1 IHfs fs2).
    split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - intros [| | | [|] | | | | | | | | | | | | |]; cbn [mm_typ_eqb];
      first [split; reflexivity | split; discriminate].
  - intros sz1 u1 IHu [| | | [|] | | | | | | | | | | | | sz2 u2 |]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite Bool.andb_true_iff, mm_N_eqb_eq, (IHu u2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - intros id1 [| | | [|] | | | | | | | | | | | | | id2]; cbn [mm_typ_eqb];
      try (split; discriminate).
    rewrite ident_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_linkage_eqb (x y : linkage) : bool :=
  match x, y with
  | LINKAGE_Private, LINKAGE_Private
  | LINKAGE_Internal, LINKAGE_Internal
  | LINKAGE_Available_externally, LINKAGE_Available_externally
  | LINKAGE_Linkonce, LINKAGE_Linkonce
  | LINKAGE_Weak, LINKAGE_Weak
  | LINKAGE_Common, LINKAGE_Common
  | LINKAGE_Appending, LINKAGE_Appending
  | LINKAGE_Extern_weak, LINKAGE_Extern_weak
  | LINKAGE_Linkonce_odr, LINKAGE_Linkonce_odr
  | LINKAGE_Weak_odr, LINKAGE_Weak_odr
  | LINKAGE_External, LINKAGE_External => true
  | _, _ => false
  end.

Lemma mm_linkage_eqb_eq (x y : linkage) :
  mm_linkage_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_linkage_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_preemption_eqb (x y : preemption_specifier) : bool :=
  match x, y with
  | PREEMPTION_Dso_preemptable, PREEMPTION_Dso_preemptable
  | PREEMPTION_Dso_local, PREEMPTION_Dso_local => true
  | _, _ => false
  end.

Lemma mm_preemption_eqb_eq (x y : preemption_specifier) :
  mm_preemption_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_preemption_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_dll_storage_eqb (x y : dll_storage) : bool :=
  match x, y with
  | DLLSTORAGE_Dllimport, DLLSTORAGE_Dllimport
  | DLLSTORAGE_Dllexport, DLLSTORAGE_Dllexport => true
  | _, _ => false
  end.

Lemma mm_dll_storage_eqb_eq (x y : dll_storage) :
  mm_dll_storage_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_dll_storage_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_visibility_eqb (x y : visibility) : bool :=
  match x, y with
  | VISIBILITY_Default, VISIBILITY_Default
  | VISIBILITY_Hidden, VISIBILITY_Hidden
  | VISIBILITY_Protected, VISIBILITY_Protected => true
  | _, _ => false
  end.

Lemma mm_visibility_eqb_eq (x y : visibility) :
  mm_visibility_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_visibility_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_cconv_ast_eqb (x y : cconv) : bool :=
  match x, y with
  | CC_Ccc, CC_Ccc
  | CC_Fastcc, CC_Fastcc
  | CC_Coldcc, CC_Coldcc
  | CC_Webkit_jscc, CC_Webkit_jscc
  | CC_Anyregcc, CC_Anyregcc
  | CC_Preserve_mostcc, CC_Preserve_mostcc
  | CC_Preserve_allcc, CC_Preserve_allcc
  | CC_Cxx_fast_tlscc, CC_Cxx_fast_tlscc
  | CC_Tailcc, CC_Tailcc
  | CC_Swiftcc, CC_Swiftcc
  | CC_Swifttailcc, CC_Swifttailcc
  | CC_cfguard_checkcc, CC_cfguard_checkcc => true
  | CC_Cc c1, CC_Cc c2 => mm_int_syntax_eqb c1 c2
  | _, _ => false
  end.

Lemma mm_cconv_ast_eqb_eq (x y : cconv) :
  mm_cconv_ast_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_cconv_ast_eqb];
    try solve [split; reflexivity | split; discriminate].
  rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_param_attr_eqb (x y : param_attr) : bool :=
  match x, y with
  | PARAMATTR_Zeroext, PARAMATTR_Zeroext
  | PARAMATTR_Signext, PARAMATTR_Signext
  | PARAMATTR_Inreg, PARAMATTR_Inreg
  | PARAMATTR_Noalias, PARAMATTR_Noalias
  | PARAMATTR_Nocapture, PARAMATTR_Nocapture
  | PARAMATTR_Nofree, PARAMATTR_Nofree
  | PARAMATTR_Nest, PARAMATTR_Nest
  | PARAMATTR_Returned, PARAMATTR_Returned
  | PARAMATTR_Nonnull, PARAMATTR_Nonnull
  | PARAMATTR_Swiftself, PARAMATTR_Swiftself
  | PARAMATTR_Swiftasync, PARAMATTR_Swiftasync
  | PARAMATTR_Swifterror, PARAMATTR_Swifterror
  | PARAMATTR_Immarg, PARAMATTR_Immarg
  | PARAMATTR_Noundef, PARAMATTR_Noundef
  | PARAMATTR_Nofreeobj, PARAMATTR_Nofreeobj
  | PARAMATTR_Allocalign, PARAMATTR_Allocalign
  | PARAMATTR_Allocptr, PARAMATTR_Allocptr
  | PARAMATTR_Readnone, PARAMATTR_Readnone
  | PARAMATTR_Readonly, PARAMATTR_Readonly
  | PARAMATTR_Writeonly, PARAMATTR_Writeonly
  | PARAMATTR_Writable, PARAMATTR_Writable
  | PARAMATTR_Dead_on_unwind, PARAMATTR_Dead_on_unwind => true
  | PARAMATTR_Byval t1, PARAMATTR_Byval t2
  | PARAMATTR_Byref t1, PARAMATTR_Byref t2
  | PARAMATTR_Preallocated t1, PARAMATTR_Preallocated t2
  | PARAMATTR_Inalloca t1, PARAMATTR_Inalloca t2
  | PARAMATTR_Sret t1, PARAMATTR_Sret t2
  | PARAMATTR_Elementtype t1, PARAMATTR_Elementtype t2 => mm_typ_eqb t1 t2
  | PARAMATTR_Align a1, PARAMATTR_Align a2
  | PARAMATTR_Dereferenceable a1, PARAMATTR_Dereferenceable a2
  | PARAMATTR_Dereferenceable_or_null a1, PARAMATTR_Dereferenceable_or_null a2
  | PARAMATTR_Alignstack a1, PARAMATTR_Alignstack a2 => mm_int_syntax_eqb a1 a2
  | PARAMATTR_Nofpclass m1, PARAMATTR_Nofpclass m2 => mm_Z_eqb m1 m2
  | PARAMATTR_Dead_on_return s1, PARAMATTR_Dead_on_return s2 =>
      mm_option_eqb mm_int_syntax_eqb s1 s2
  | PARAMATTR_Range t1 a1 b1, PARAMATTR_Range t2 a2 b2 =>
      mm_typ_eqb t1 t2 && mm_int_syntax_eqb a1 a2 && mm_int_syntax_eqb b1 b2
  | PARAMATTR_Initializes l1, PARAMATTR_Initializes l2 =>
      mm_list_eqb (mm_prod_eqb mm_int_syntax_eqb mm_int_syntax_eqb) l1 l2
  | PARAMATTR_Captures p1, PARAMATTR_Captures p2 =>
      mm_prod_eqb (mm_list_eqb mm_string_eqb) (mm_list_eqb mm_string_eqb) p1 p2
  | _, _ => false
  end.

Lemma mm_param_attr_eqb_eq (x y : param_attr) :
  mm_param_attr_eqb x y = true <-> x = y.
Proof.
  destruct x; destruct y; cbn [mm_param_attr_eqb];
    try solve [split; reflexivity | split; discriminate].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_typ_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_Z_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite (mm_option_eqb_eq _ mm_int_syntax_eqb_eq);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_typ_eqb_eq, !mm_int_syntax_eqb_eq;
      split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite (mm_list_eqb_eq _ (mm_prod_eqb_eq _ _ mm_int_syntax_eqb_eq mm_int_syntax_eqb_eq));
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite (mm_prod_eqb_eq _ _ (mm_list_eqb_eq _ mm_string_eqb_eq) (mm_list_eqb_eq _ mm_string_eqb_eq));
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_mem_loc_eqb (x y : mem_loc) : bool :=
  match x, y with
  | LOC_Default, LOC_Default
  | LOC_Argmem, LOC_Argmem
  | LOC_Inaccessiblemem, LOC_Inaccessiblemem
  | LOC_Errnomem, LOC_Errnomem => true
  | _, _ => false
  end.

Lemma mm_mem_loc_eqb_eq (x y : mem_loc) :
  mm_mem_loc_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_mem_loc_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_mem_access_kind_eqb (x y : mem_access_kind) : bool :=
  match x, y with
  | ACC_None, ACC_None
  | ACC_Read, ACC_Read
  | ACC_Write, ACC_Write
  | ACC_Readwrite, ACC_Readwrite => true
  | _, _ => false
  end.

Lemma mm_mem_access_kind_eqb_eq (x y : mem_access_kind) :
  mm_mem_access_kind_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_mem_access_kind_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_fn_attr_nullary_tag (x : fn_attr) : option positive :=
  match x with
  | FNATTR_Alwaysinline => Some 1%positive
  | FNATTR_Builtin => Some 2%positive
  | FNATTR_Cold => Some 3%positive
  | FNATTR_Convergent => Some 4%positive
  | FNATTR_Disable_sanitizer_instrumentation => Some 5%positive
  | FNATTR_Fn_ret_thunk_extern => Some 6%positive
  | FNATTR_Hot => Some 7%positive
  | FNATTR_Inaccessiblememonly => Some 8%positive
  | FNATTR_Inaccessiblemem_or_argmemonly => Some 9%positive
  | FNATTR_Inlinehint => Some 10%positive
  | FNATTR_Jumptable => Some 11%positive
  | FNATTR_Minsize => Some 12%positive
  | FNATTR_Naked => Some 13%positive
  | FNATTR_No_jump_tables => Some 14%positive
  | FNATTR_Nobuiltin => Some 15%positive
  | FNATTR_Noduplicate => Some 16%positive
  | FNATTR_Nofree => Some 17%positive
  | FNATTR_Noimplicitfloat => Some 18%positive
  | FNATTR_Noinline => Some 19%positive
  | FNATTR_Nomerge => Some 20%positive
  | FNATTR_Nonlazybind => Some 21%positive
  | FNATTR_Noprofile => Some 22%positive
  | FNATTR_Noredzone => Some 23%positive
  | FNATTR_Indirect_tls_seg_refs => Some 24%positive
  | FNATTR_Noreturn => Some 25%positive
  | FNATTR_Norecurse => Some 26%positive
  | FNATTR_Willreturn => Some 27%positive
  | FNATTR_Nosync => Some 28%positive
  | FNATTR_Nounwind => Some 29%positive
  | FNATTR_Nocreateundeforpoison => Some 30%positive
  | FNATTR_Nosanitize_bounds => Some 31%positive
  | FNATTR_Nosanitize_coverage => Some 32%positive
  | FNATTR_Null_pointer_is_valid => Some 33%positive
  | FNATTR_Optforfuzzing => Some 34%positive
  | FNATTR_Optnone => Some 35%positive
  | FNATTR_Optsize => Some 36%positive
  | FNATTR_Readnone => Some 37%positive
  | FNATTR_Readonly => Some 38%positive
  | FNATTR_Writeonly => Some 39%positive
  | FNATTR_Argmemonly => Some 40%positive
  | FNATTR_Returns_twice => Some 41%positive
  | FNATTR_Safestack => Some 42%positive
  | FNATTR_Sanitize_address => Some 43%positive
  | FNATTR_Sanitize_memory => Some 44%positive
  | FNATTR_Sanitize_thread => Some 45%positive
  | FNATTR_Sanitize_hwaddress => Some 46%positive
  | FNATTR_Sanitize_memtag => Some 47%positive
  | FNATTR_Speculative_load_hardening => Some 48%positive
  | FNATTR_Speculatable => Some 49%positive
  | FNATTR_Ssp => Some 50%positive
  | FNATTR_Sspstrong => Some 51%positive
  | FNATTR_Sspreq => Some 52%positive
  | FNATTR_Strictfp => Some 53%positive
  | FNATTR_Tls_load_hoist => Some 54%positive
  | FNATTR_Nocf_check => Some 55%positive
  | FNATTR_Shadowcallstack => Some 56%positive
  | FNATTR_Mustprogress => Some 57%positive
  | _ => None
  end.

Lemma mm_fn_attr_nullary_tag_inj (x y : fn_attr) (t : positive) :
  mm_fn_attr_nullary_tag x = Some t ->
  mm_fn_attr_nullary_tag y = Some t ->
  x = y.
Proof.
  destruct x, y; cbn [mm_fn_attr_nullary_tag]; intros Hx Hy;
    try discriminate Hx; try discriminate Hy;
    first [reflexivity | exfalso; congruence].
Qed.

Definition mm_fn_attr_eqb (x y : fn_attr) : bool :=
  match mm_fn_attr_nullary_tag x, mm_fn_attr_nullary_tag y with
  | Some t1, Some t2 => mm_pos_eqb t1 t2
  | None, None =>
      match x, y with
      | FNATTR_Alignstack a1, FNATTR_Alignstack a2 => mm_int_syntax_eqb a1 a2
      | FNATTR_Allockind k1, FNATTR_Allockind k2 => mm_string_eqb k1 k2
      | FNATTR_Allocsize a1 b1, FNATTR_Allocsize a2 b2 =>
          mm_int_syntax_eqb a1 a2 && mm_option_eqb mm_int_syntax_eqb b1 b2
      | FNATTR_Uwtable s1, FNATTR_Uwtable s2 =>
          mm_option_eqb mm_bool_eqb s1 s2
      | FNATTR_Vscale_range lo1 hi1, FNATTR_Vscale_range lo2 hi2 =>
          mm_int_syntax_eqb lo1 lo2 && mm_option_eqb mm_int_syntax_eqb hi1 hi2
      | FNATTR_String s1, FNATTR_String s2 => mm_string_eqb s1 s2
      | FNATTR_Key_value kv1, FNATTR_Key_value kv2 =>
          mm_prod_eqb mm_string_eqb mm_string_eqb kv1 kv2
      | FNATTR_Attr_grp g1, FNATTR_Attr_grp g2 => mm_Z_eqb g1 g2
      | FNATTR_Memory e1, FNATTR_Memory e2 =>
          mm_list_eqb (mm_prod_eqb mm_mem_loc_eqb mm_mem_access_kind_eqb) e1 e2
      | FNATTR_UNKNOWN s1, FNATTR_UNKNOWN s2 => mm_string_eqb s1 s2
      | _, _ => false
      end
  | _, _ => false
  end.

Lemma mm_fn_attr_eqb_eq (x y : fn_attr) :
  mm_fn_attr_eqb x y = true <-> x = y.
Proof.
  unfold mm_fn_attr_eqb.
  destruct (mm_fn_attr_nullary_tag x) as [t1 |] eqn:Ex,
           (mm_fn_attr_nullary_tag y) as [t2 |] eqn:Ey.
  - rewrite mm_pos_eqb_eq; split.
    + intros <-; exact (mm_fn_attr_nullary_tag_inj x y t1 Ex Ey).
    + intros ->; congruence.
  - split; [discriminate | intros ->; congruence].
  - split; [discriminate | intros ->; congruence].
  - destruct x; try discriminate Ex; destruct y; try discriminate Ey;
      try solve [split; discriminate].
    + rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite Bool.andb_true_iff, mm_int_syntax_eqb_eq, (mm_option_eqb_eq _ mm_int_syntax_eqb_eq);
        split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
    + rewrite (mm_option_eqb_eq _ mm_bool_eqb_eq);
        split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite Bool.andb_true_iff, mm_int_syntax_eqb_eq, (mm_option_eqb_eq _ mm_int_syntax_eqb_eq);
        split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
    + rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite (mm_prod_eqb_eq _ _ mm_string_eqb_eq mm_string_eqb_eq);
        split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite mm_Z_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite (mm_list_eqb_eq _ (mm_prod_eqb_eq _ _ mm_mem_loc_eqb_eq mm_mem_access_kind_eqb_eq));
        split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
    + rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_tls_eqb (x y : thread_local_storage) : bool :=
  match x, y with
  | TLS_NONE, TLS_NONE
  | TLS_Localdynamic, TLS_Localdynamic
  | TLS_Initialexec, TLS_Initialexec
  | TLS_Localexec, TLS_Localexec => true
  | _, _ => false
  end.

Lemma mm_tls_eqb_eq (x y : thread_local_storage) :
  mm_tls_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_tls_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_icmp_eqb (x y : icmp) : bool :=
  match x, y with
  | LLVMAst.Eq, LLVMAst.Eq
  | Ne, Ne
  | Ugt, Ugt
  | Uge, Uge
  | Ult, Ult
  | Ule, Ule
  | Sgt, Sgt
  | Sge, Sge
  | Slt, Slt
  | Sle, Sle => true
  | _, _ => false
  end.

Lemma mm_icmp_eqb_eq (x y : icmp) :
  mm_icmp_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_icmp_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_fcmp_eqb (x y : fcmp) : bool :=
  match x, y with
  | FFalse, FFalse
  | FOeq, FOeq
  | FOgt, FOgt
  | FOge, FOge
  | FOlt, FOlt
  | FOle, FOle
  | FOne, FOne
  | FOrd, FOrd
  | FUno, FUno
  | FUeq, FUeq
  | FUgt, FUgt
  | FUge, FUge
  | FUlt, FUlt
  | FUle, FUle
  | FUne, FUne
  | FTrue, FTrue => true
  | _, _ => false
  end.

Lemma mm_fcmp_eqb_eq (x y : fcmp) :
  mm_fcmp_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_fcmp_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_ibinop_eqb (x y : ibinop) : bool :=
  match x, y with
  | LLVMAst.Add a1 b1, LLVMAst.Add a2 b2
  | LLVMAst.Sub a1 b1, LLVMAst.Sub a2 b2
  | LLVMAst.Mul a1 b1, LLVMAst.Mul a2 b2
  | Shl a1 b1, Shl a2 b2 => mm_bool_eqb a1 a2 && mm_bool_eqb b1 b2
  | UDiv e1, UDiv e2
  | SDiv e1, SDiv e2
  | LShr e1, LShr e2
  | AShr e1, AShr e2
  | LLVMAst.Or e1, LLVMAst.Or e2 => mm_bool_eqb e1 e2
  | URem, URem
  | SRem, SRem
  | And, And
  | Xor, Xor => true
  | _, _ => false
  end.

Lemma mm_ibinop_eqb_eq (x y : ibinop) :
  mm_ibinop_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_ibinop_eqb];
    try solve [split; reflexivity | split; discriminate];
    try (rewrite Bool.andb_true_iff, !mm_bool_eqb_eq;
         split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity]);
    (rewrite mm_bool_eqb_eq;
     split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity]).
Qed.

Definition mm_fbinop_eqb (x y : fbinop) : bool :=
  match x, y with
  | FAdd, FAdd
  | FSub, FSub
  | FMul, FMul
  | FDiv, FDiv
  | FRem, FRem => true
  | _, _ => false
  end.

Lemma mm_fbinop_eqb_eq (x y : fbinop) :
  mm_fbinop_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_fbinop_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_fast_math_eqb (x y : fast_math) : bool :=
  match x, y with
  | Nnan, Nnan
  | Ninf, Ninf
  | Nsz, Nsz
  | Arcp, Arcp
  | Contract, Contract
  | Afn, Afn
  | Reassoc, Reassoc
  | Fast, Fast => true
  | _, _ => false
  end.

Lemma mm_fast_math_eqb_eq (x y : fast_math) :
  mm_fast_math_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_fast_math_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_pure_conv_eqb (x y : pure_conversion) : bool :=
  match x, y with
  | Trunc a1 b1, Trunc a2 b2 => mm_bool_eqb a1 a2 && mm_bool_eqb b1 b2
  | Zext b1, Zext b2
  | Uitofp b1, Uitofp b2 => mm_bool_eqb b1 b2
  | Fptrunc fm1, Fptrunc fm2
  | Fpext fm1, Fpext fm2 => mm_list_eqb mm_fast_math_eqb fm1 fm2
  | Sext, Sext
  | Sitofp, Sitofp
  | Fptoui, Fptoui
  | Fptosi, Fptosi => true
  | _, _ => false
  end.

Lemma mm_pure_conv_eqb_eq (x y : pure_conversion) :
  mm_pure_conv_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_pure_conv_eqb];
    try solve [split; reflexivity | split; discriminate].
  - rewrite Bool.andb_true_iff, !mm_bool_eqb_eq;
      split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - rewrite mm_bool_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite (mm_list_eqb_eq _ mm_fast_math_eqb_eq);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite (mm_list_eqb_eq _ mm_fast_math_eqb_eq);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_bool_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_impure_conv_eqb (x y : impure_conversion) : bool :=
  match x, y with
  | Inttoptr, Inttoptr
  | Ptrtoint, Ptrtoint
  | Ptrtoaddr, Ptrtoaddr
  | Addrspacecast, Addrspacecast => true
  | _, _ => false
  end.

Lemma mm_impure_conv_eqb_eq (x y : impure_conversion) :
  mm_impure_conv_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_impure_conv_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_conv_type_eqb (x y : conversion_type) : bool :=
  match x, y with
  | CONV_Bitcast, CONV_Bitcast => true
  | CONV_Pure c1, CONV_Pure c2 => mm_pure_conv_eqb c1 c2
  | CONV_Impure c1, CONV_Impure c2 => mm_impure_conv_eqb c1 c2
  | _, _ => false
  end.

Lemma mm_conv_type_eqb_eq (x y : conversion_type) :
  mm_conv_type_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_conv_type_eqb];
    try solve [split; reflexivity | split; discriminate].
  - rewrite mm_pure_conv_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_impure_conv_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_gep_flags_eqb (x y : gep_flags) : bool :=
  mm_bool_eqb (gep_inbounds x) (gep_inbounds y) &&
  mm_bool_eqb (gep_nusw x) (gep_nusw y) &&
  mm_bool_eqb (gep_nuw x) (gep_nuw y).

Lemma mm_gep_flags_eqb_eq (x y : gep_flags) :
  mm_gep_flags_eqb x y = true <-> x = y.
Proof.
  destruct x as [i1 s1 u1], y as [i2 s2 u2]; unfold mm_gep_flags_eqb; cbn.
  rewrite !Bool.andb_true_iff, !mm_bool_eqb_eq.
  split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
Qed.

Definition mm_float_hex_type_eqb (x y : float_hex_type) : bool :=
  match x, y with
  | FH_X, FH_X
  | FH_K, FH_K
  | FH_L, FH_L
  | FH_M, FH_M
  | FH_H, FH_H
  | FH_R, FH_R => true
  | _, _ => false
  end.

Lemma mm_float_hex_type_eqb_eq (x y : float_hex_type) :
  mm_float_hex_type_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_float_hex_type_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_float_syntax_eqb (x y : float_syntax) : bool :=
  match x, y with
  | FS_decimal d1, FS_decimal d2 => mm_decimal_eqb d1 d2
  | FS_hex t1 u1, FS_hex t2 u2 => mm_float_hex_type_eqb t1 t2 && mm_hex_uint_eqb u1 u2
  | _, _ => false
  end.

Lemma mm_float_syntax_eqb_eq (x y : float_syntax) :
  mm_float_syntax_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_float_syntax_eqb]; try (split; discriminate).
  - rewrite mm_decimal_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite Bool.andb_true_iff, mm_float_hex_type_eqb_eq, mm_hex_uint_eqb_eq;
      split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
Qed.

Definition mm_texp_list_eqb (eqE : exp dtyp -> exp dtyp -> bool) :
  list (dtyp * exp dtyp) -> list (dtyp * exp dtyp) -> bool :=
  fix go l1 l2 :=
    match l1, l2 with
    | [], [] => true
    | (dt1, e1) :: r1, (dt2, e2) :: r2 =>
        mm_dtyp_eqb dt1 dt2 && eqE e1 e2 && go r1 r2
    | _, _ => false
    end.

Lemma mm_texp_list_eqb_in_eq (eqE : exp dtyp -> exp dtyp -> bool)
  (l1 : list (dtyp * exp dtyp))
  (IH : forall p, In p l1 -> forall e2, eqE (snd p) e2 = true <-> snd p = e2) :
  forall l2, mm_texp_list_eqb eqE l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [| [dt1 e1] r1 IHr]; intros [| [dt2 e2] r2]; cbn [mm_texp_list_eqb].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite !Bool.andb_true_iff, mm_dtyp_eqb_eq.
    pose proof (IH (dt1, e1) (or_introl Logic.eq_refl) e2) as He1; cbn [snd] in He1.
    rewrite He1, (IHr (fun p Hp => IH p (or_intror Hp)) r2).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
Qed.

Fixpoint mm_exp_eqb (e1 e2 : exp dtyp) : bool :=
  match e1, e2 with
  | EXP_Ident id1, EXP_Ident id2 => ident_eqb id1 id2
  | EXP_Integer x1, EXP_Integer x2 => mm_int_syntax_eqb x1 x2
  | EXP_Float f1, EXP_Float f2 => mm_float_syntax_eqb f1 f2
  | EXP_Bool b1, EXP_Bool b2 => mm_bool_eqb b1 b2
  | EXP_Null, EXP_Null => true
  | EXP_Zero_initializer, EXP_Zero_initializer => true
  | EXP_Cstring elts1, EXP_Cstring elts2 =>
      mm_texp_list_eqb mm_exp_eqb elts1 elts2
  | EXP_Undef, EXP_Undef => true
  | EXP_Poison, EXP_Poison => true
  | EXP_Struct fs1, EXP_Struct fs2 =>
      mm_texp_list_eqb mm_exp_eqb fs1 fs2
  | EXP_Packed_struct fs1, EXP_Packed_struct fs2 =>
      mm_texp_list_eqb mm_exp_eqb fs1 fs2
  | EXP_Array elts1, EXP_Array elts2 =>
      mm_texp_list_eqb mm_exp_eqb elts1 elts2
  | EXP_Vector elts1, EXP_Vector elts2 =>
      mm_texp_list_eqb mm_exp_eqb elts1 elts2
  | OP_IBinop iop1 t1 v1 w1, OP_IBinop iop2 t2 v2 w2 =>
      mm_ibinop_eqb iop1 iop2 && mm_dtyp_eqb t1 t2 && mm_exp_eqb v1 v2 && mm_exp_eqb w1 w2
  | OP_ICmp ss1 cmp1 t1 v1 w1, OP_ICmp ss2 cmp2 t2 v2 w2 =>
      mm_bool_eqb ss1 ss2 && mm_icmp_eqb cmp1 cmp2 && mm_dtyp_eqb t1 t2 &&
      mm_exp_eqb v1 v2 && mm_exp_eqb w1 w2
  | OP_FBinop fop1 fm1 t1 v1 w1, OP_FBinop fop2 fm2 t2 v2 w2 =>
      mm_fbinop_eqb fop1 fop2 && mm_list_eqb mm_fast_math_eqb fm1 fm2 &&
      mm_dtyp_eqb t1 t2 && mm_exp_eqb v1 v2 && mm_exp_eqb w1 w2
  | OP_Fneg fm1 (dt1, v1), OP_Fneg fm2 (dt2, v2) =>
      mm_list_eqb mm_fast_math_eqb fm1 fm2 && mm_dtyp_eqb dt1 dt2 && mm_exp_eqb v1 v2
  | OP_FCmp cmp1 fm1 t1 v1 w1, OP_FCmp cmp2 fm2 t2 v2 w2 =>
      mm_fcmp_eqb cmp1 cmp2 && mm_list_eqb mm_fast_math_eqb fm1 fm2 &&
      mm_dtyp_eqb t1 t2 && mm_exp_eqb v1 v2 && mm_exp_eqb w1 w2
  | OP_Conversion c1 tf1 v1 tt1, OP_Conversion c2 tf2 v2 tt2 =>
      mm_conv_type_eqb c1 c2 && mm_dtyp_eqb tf1 tf2 && mm_exp_eqb v1 v2 && mm_dtyp_eqb tt1 tt2
  | OP_GetElementPtr fl1 t1 (tp1, ep1) idxs1, OP_GetElementPtr fl2 t2 (tp2, ep2) idxs2 =>
      mm_gep_flags_eqb fl1 fl2 && mm_dtyp_eqb t1 t2 && mm_dtyp_eqb tp1 tp2 &&
      mm_exp_eqb ep1 ep2 && mm_texp_list_eqb mm_exp_eqb idxs1 idxs2
  | OP_ExtractElement (tv1, ev1) (ti1, ei1), OP_ExtractElement (tv2, ev2) (ti2, ei2) =>
      mm_dtyp_eqb tv1 tv2 && mm_exp_eqb ev1 ev2 && mm_dtyp_eqb ti1 ti2 && mm_exp_eqb ei1 ei2
  | OP_InsertElement (tv1, ev1) (te1, ee1) (ti1, ei1),
    OP_InsertElement (tv2, ev2) (te2, ee2) (ti2, ei2) =>
      mm_dtyp_eqb tv1 tv2 && mm_exp_eqb ev1 ev2 &&
      mm_dtyp_eqb te1 te2 && mm_exp_eqb ee1 ee2 &&
      mm_dtyp_eqb ti1 ti2 && mm_exp_eqb ei1 ei2
  | OP_ShuffleVector (ta1, ea1) (tb1, eb1) (tm1, em1),
    OP_ShuffleVector (ta2, ea2) (tb2, eb2) (tm2, em2) =>
      mm_dtyp_eqb ta1 ta2 && mm_exp_eqb ea1 ea2 &&
      mm_dtyp_eqb tb1 tb2 && mm_exp_eqb eb1 eb2 &&
      mm_dtyp_eqb tm1 tm2 && mm_exp_eqb em1 em2
  | OP_ExtractValue (tv1, ev1) idxs1, OP_ExtractValue (tv2, ev2) idxs2 =>
      mm_dtyp_eqb tv1 tv2 && mm_exp_eqb ev1 ev2 && mm_list_eqb mm_int_syntax_eqb idxs1 idxs2
  | OP_InsertValue (tv1, ev1) (te1, ee1) idxs1,
    OP_InsertValue (tv2, ev2) (te2, ee2) idxs2 =>
      mm_dtyp_eqb tv1 tv2 && mm_exp_eqb ev1 ev2 &&
      mm_dtyp_eqb te1 te2 && mm_exp_eqb ee1 ee2 &&
      mm_list_eqb mm_int_syntax_eqb idxs1 idxs2
  | OP_Select fm1 (tc1, ec1) (ta1, ea1) (tb1, eb1),
    OP_Select fm2 (tc2, ec2) (ta2, ea2) (tb2, eb2) =>
      mm_list_eqb mm_fast_math_eqb fm1 fm2 &&
      mm_dtyp_eqb tc1 tc2 && mm_exp_eqb ec1 ec2 &&
      mm_dtyp_eqb ta1 ta2 && mm_exp_eqb ea1 ea2 &&
      mm_dtyp_eqb tb1 tb2 && mm_exp_eqb eb1 eb2
  | OP_Freeze (t1, v1), OP_Freeze (t2, v2) =>
      mm_dtyp_eqb t1 t2 && mm_exp_eqb v1 v2
  | EXP_Asm s1 a1 i1 u1 tp1 oc1, EXP_Asm s2 a2 i2 u2 tp2 oc2 =>
      mm_bool_eqb s1 s2 && mm_bool_eqb a1 a2 && mm_bool_eqb i1 i2 && mm_bool_eqb u1 u2 &&
      mm_string_eqb tp1 tp2 && mm_string_eqb oc1 oc2
  | EXP_Metadata m1, EXP_Metadata m2 => mm_metadata_eqb m1 m2
  | EXP_Splat (t1, v1), EXP_Splat (t2, v2) =>
      mm_dtyp_eqb t1 t2 && mm_exp_eqb v1 v2
  | EXP_BlockAddress fn1 blk1, EXP_BlockAddress fn2 blk2 =>
      raw_id_eqb fn1 fn2 && raw_id_eqb blk1 blk2
  | _, _ => false
  end
with mm_metadata_eqb (m1 m2 : metadata dtyp) : bool :=
  match m1, m2 with
  | METADATA_Null, METADATA_Null => true
  | METADATA_Id id1, METADATA_Id id2 => raw_id_eqb id1 id2
  | METADATA_Const (t1, e1), METADATA_Const (t2, e2) =>
      mm_dtyp_eqb t1 t2 && mm_exp_eqb e1 e2
  | METADATA_Node ms1, METADATA_Node ms2 =>
      mm_list_eqb mm_metadata_eqb ms1 ms2
  | METADATA_Pair a1 b1, METADATA_Pair a2 b2 =>
      mm_metadata_eqb a1 a2 && mm_metadata_eqb b1 b2
  | METADATA_Debug s1 c1, METADATA_Debug s2 c2 =>
      mm_string_eqb s1 s2 && mm_string_eqb c1 c2
  | METADATA_File_info f1, METADATA_File_info f2 =>
      mm_file_info_eqb f1 f2
  | _, _ => false
  end.

Lemma mm_exp_metadata_eqb_eq :
  (forall (e1 e2 : exp dtyp), mm_exp_eqb e1 e2 = true <-> e1 = e2) /\
  (forall (m1 m2 : metadata dtyp), mm_metadata_eqb m1 m2 = true <-> m1 = m2).
Proof.
  apply (@AstLib.exp_metadata_mut_ind dtyp
           (fun e1 => forall e2, mm_exp_eqb e1 e2 = true <-> e1 = e2)
           (fun m1 => forall m2, mm_metadata_eqb m1 m2 = true <-> m1 = m2)).
  - (* EXP_Ident *)
    intros id1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite ident_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Integer *)
    intros x1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Float *)
    intros f1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite mm_float_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Bool *)
    intros b1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite mm_bool_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Null *)
    intros e2; destruct e2; cbn [mm_exp_eqb]; first [split; reflexivity | split; discriminate].
  - (* EXP_Zero_initializer *)
    intros e2; destruct e2; cbn [mm_exp_eqb]; first [split; reflexivity | split; discriminate].
  - (* EXP_Cstring *)
    intros elts1 IH e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (mm_texp_list_eqb_in_eq mm_exp_eqb elts1 IH);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Undef *)
    intros e2; destruct e2; cbn [mm_exp_eqb]; first [split; reflexivity | split; discriminate].
  - (* EXP_Poison *)
    intros e2; destruct e2; cbn [mm_exp_eqb]; first [split; reflexivity | split; discriminate].
  - (* EXP_Struct *)
    intros fs1 IH e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (mm_texp_list_eqb_in_eq mm_exp_eqb fs1 IH);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Packed_struct *)
    intros fs1 IH e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (mm_texp_list_eqb_in_eq mm_exp_eqb fs1 IH);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Array *)
    intros elts1 IH e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (mm_texp_list_eqb_in_eq mm_exp_eqb elts1 IH);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Vector *)
    intros elts1 IH e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (mm_texp_list_eqb_in_eq mm_exp_eqb elts1 IH);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* OP_IBinop *)
    intros iop1 t1 v1 w1 IHv IHw e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_ibinop_eqb_eq, mm_dtyp_eqb_eq, (IHv _), (IHw _).
    split; [intros [[[-> ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> ->; repeat split; reflexivity].
  - (* OP_Fneg *)
    intros fm1 [dt1 v1] IHv e2; cbn [snd] in IHv.
    destruct e2 as [| | | | | | | | | | | | | | | | fm2 [dt2 v2] | | | | | | | | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, (mm_list_eqb_eq _ mm_fast_math_eqb_eq), mm_dtyp_eqb_eq, (IHv v2).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - (* OP_ICmp *)
    intros ss1 cmp1 t1 v1 w1 IHv IHw e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_bool_eqb_eq, mm_icmp_eqb_eq, mm_dtyp_eqb_eq, (IHv _), (IHw _).
    split; [intros [[[[-> ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_FBinop *)
    intros fop1 fm1 t1 v1 w1 IHv IHw e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_fbinop_eqb_eq, (mm_list_eqb_eq _ mm_fast_math_eqb_eq),
      mm_dtyp_eqb_eq, (IHv _), (IHw _).
    split; [intros [[[[-> ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_FCmp *)
    intros cmp1 fm1 t1 v1 w1 IHv IHw e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_fcmp_eqb_eq, (mm_list_eqb_eq _ mm_fast_math_eqb_eq),
      mm_dtyp_eqb_eq, (IHv _), (IHw _).
    split; [intros [[[[-> ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_Conversion *)
    intros c1 tf1 v1 tt1 IHv e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_conv_type_eqb_eq, !mm_dtyp_eqb_eq, (IHv _).
    split; [intros [[[-> ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> ->; repeat split; reflexivity].
  - (* OP_GetElementPtr *)
    intros fl1 t1 [tp1 ep1] idxs1 IHep IHidxs e2; cbn [snd] in IHep.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | fl2 t2 [tp2 ep2] idxs2 | | | | | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_gep_flags_eqb_eq, !mm_dtyp_eqb_eq, (IHep ep2),
      (mm_texp_list_eqb_in_eq mm_exp_eqb idxs1 IHidxs idxs2).
    split; [intros [[[[-> ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_ExtractElement *)
    intros [tv1 ev1] [ti1 ei1] IHev IHei e2; cbn [snd] in IHev, IHei.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | [tv2 ev2] [ti2 ei2] | | | | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, !mm_dtyp_eqb_eq, (IHev ev2), (IHei ei2).
    split; [intros [[[-> ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> ->; repeat split; reflexivity].
  - (* OP_InsertElement *)
    intros [tv1 ev1] [te1 ee1] [ti1 ei1] IHev IHee IHei e2; cbn [snd] in IHev, IHee, IHei.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | [tv2 ev2] [te2 ee2] [ti2 ei2] | | | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, !mm_dtyp_eqb_eq, (IHev ev2), (IHee ee2), (IHei ei2).
    split; [intros [[[[[-> ->] ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_ShuffleVector *)
    intros [ta1 ea1] [tb1 eb1] [tm1 em1] IHea IHeb IHem e2; cbn [snd] in IHea, IHeb, IHem.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | [ta2 ea2] [tb2 eb2] [tm2 em2] | | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, !mm_dtyp_eqb_eq, (IHea ea2), (IHeb eb2), (IHem em2).
    split; [intros [[[[[-> ->] ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_ExtractValue *)
    intros [tv1 ev1] idxs1 IHev e2; cbn [snd] in IHev.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | | [tv2 ev2] idxs2 | | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, mm_dtyp_eqb_eq, (IHev ev2), (mm_list_eqb_eq _ mm_int_syntax_eqb_eq).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - (* OP_InsertValue *)
    intros [tv1 ev1] [te1 ee1] idxs1 IHev IHee e2; cbn [snd] in IHev, IHee.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | | | [tv2 ev2] [te2 ee2] idxs2 | | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, !mm_dtyp_eqb_eq, (IHev ev2), (IHee ee2),
      (mm_list_eqb_eq _ mm_int_syntax_eqb_eq).
    split; [intros [[[[-> ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_Select *)
    intros fm1 [tc1 ec1] [ta1 ea1] [tb1 eb1] IHec IHea IHeb e2; cbn [snd] in IHec, IHea, IHeb.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | | | | fm2 [tc2 ec2] [ta2 ea2] [tb2 eb2] | | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, (mm_list_eqb_eq _ mm_fast_math_eqb_eq),
      !mm_dtyp_eqb_eq, (IHec ec2), (IHea ea2), (IHeb eb2).
    split; [intros [[[[[[-> ->] ->] ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> -> -> ->; repeat split; reflexivity].
  - (* OP_Freeze *)
    intros [t1 v1] IHv e2; cbn [snd] in IHv.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | | | | | [t2 v2] | | | | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, mm_dtyp_eqb_eq, (IHv v2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* EXP_Asm *)
    intros s1 a1 i1 u1 tp1 oc1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite !Bool.andb_true_iff, !mm_bool_eqb_eq, !mm_string_eqb_eq.
    split; [intros [[[[[-> ->] ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> -> ->; repeat split; reflexivity].
  - (* EXP_Metadata *)
    intros m1 IHm e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite (IHm _); split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* EXP_Splat *)
    intros [t1 v1] IHv e2; cbn [snd] in IHv.
    destruct e2 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | [t2 v2] | ];
      cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, mm_dtyp_eqb_eq, (IHv v2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* EXP_BlockAddress *)
    intros fn1 blk1 e2; destruct e2; cbn [mm_exp_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, !raw_id_eqb_spec.
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* METADATA_Null *)
    intros m2; destruct m2; cbn [mm_metadata_eqb]; first [split; reflexivity | split; discriminate].
  - (* METADATA_Id *)
    intros id1 m2; destruct m2; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* METADATA_Const *)
    intros [t1 e1] IHe m2; cbn [snd] in IHe.
    destruct m2 as [| | [t2 e2] | | | |]; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, mm_dtyp_eqb_eq, (IHe e2).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* METADATA_Node *)
    intros ms1 IHms m2; destruct m2; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite (mm_list_eqb_in_eq mm_metadata_eqb ms1 IHms);
      split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - (* METADATA_Pair *)
    intros a1 b1 IHa IHb m2; destruct m2; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, (IHa _), (IHb _).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* METADATA_Debug *)
    intros s1 c1 m2; destruct m2; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite Bool.andb_true_iff, !mm_string_eqb_eq.
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - (* METADATA_File_info *)
    intros f1 m2; destruct m2; cbn [mm_metadata_eqb]; try (split; discriminate).
    rewrite mm_file_info_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Lemma mm_exp_eqb_eq (e1 e2 : exp dtyp) :
  mm_exp_eqb e1 e2 = true <-> e1 = e2.
Proof.
  exact (proj1 mm_exp_metadata_eqb_eq e1 e2).
Qed.

Lemma mm_metadata_eqb_eq (m1 m2 : metadata dtyp) :
  mm_metadata_eqb m1 m2 = true <-> m1 = m2.
Proof.
  exact (proj2 mm_exp_metadata_eqb_eq m1 m2).
Qed.

Definition mm_texp_eqb : texp dtyp -> texp dtyp -> bool :=
  mm_prod_eqb mm_dtyp_eqb mm_exp_eqb.

Lemma mm_texp_eqb_eq (x y : texp dtyp) :
  mm_texp_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _ mm_dtyp_eqb_eq mm_exp_eqb_eq x y).
Qed.

Definition mm_tint_literal_eqb (x y : tint_literal) : bool :=
  match x, y with
  | TInt_Literal sz1 v1, TInt_Literal sz2 v2 =>
      mm_pos_eqb sz1 sz2 && mm_int_syntax_eqb v1 v2
  end.

Lemma mm_tint_literal_eqb_eq (x y : tint_literal) :
  mm_tint_literal_eqb x y = true <-> x = y.
Proof.
  destruct x as [sz1 v1], y as [sz2 v2]; cbn [mm_tint_literal_eqb].
  rewrite Bool.andb_true_iff, mm_pos_eqb_eq, mm_int_syntax_eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
Qed.

Definition mm_phi_eqb (x y : phi dtyp) : bool :=
  match x, y with
  | Phi fm1 dt1 args1, Phi fm2 dt2 args2 =>
      mm_list_eqb mm_fast_math_eqb fm1 fm2 &&
      mm_dtyp_eqb dt1 dt2 &&
      mm_list_eqb (mm_prod_eqb raw_id_eqb mm_exp_eqb) args1 args2
  end.

Lemma mm_phi_eqb_eq (x y : phi dtyp) :
  mm_phi_eqb x y = true <-> x = y.
Proof.
  destruct x as [fm1 dt1 args1], y as [fm2 dt2 args2]; cbn [mm_phi_eqb].
  rewrite !Bool.andb_true_iff, (mm_list_eqb_eq _ mm_fast_math_eqb_eq),
    mm_dtyp_eqb_eq, (mm_list_eqb_eq _ (mm_prod_eqb_eq _ _ raw_id_eqb_spec mm_exp_eqb_eq)).
  split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
Qed.

Definition mm_ordering_eqb (x y : ordering) : bool :=
  match x, y with
  | Unordered, Unordered
  | Monotonic, Monotonic
  | Acquire, Acquire
  | Release, Release
  | Acq_rel, Acq_rel
  | Seq_cst, Seq_cst => true
  | _, _ => false
  end.

Lemma mm_ordering_eqb_eq (x y : ordering) :
  mm_ordering_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_ordering_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_cmpxchg_eqb (x y : cmpxchg dtyp) : bool :=
  mm_option_eqb mm_unit_eqb (c_weak x) (c_weak y) &&
  mm_option_eqb mm_unit_eqb (c_volatile x) (c_volatile y) &&
  mm_texp_eqb (c_ptr x) (c_ptr y) &&
  mm_texp_eqb (c_cmp x) (c_cmp y) &&
  mm_texp_eqb (c_new x) (c_new y) &&
  mm_option_eqb mm_string_eqb (c_syncscope x) (c_syncscope y) &&
  mm_ordering_eqb (c_success_ordering x) (c_success_ordering y) &&
  mm_ordering_eqb (c_failure_ordering x) (c_failure_ordering y) &&
  mm_option_eqb mm_int_syntax_eqb (c_align x) (c_align y).

Lemma mm_cmpxchg_eqb_eq (x y : cmpxchg dtyp) :
  mm_cmpxchg_eqb x y = true <-> x = y.
Proof.
  destruct x as [w1 v1 p1 c1 n1 s1 so1 fo1 al1],
           y as [w2 v2 p2 c2 n2 s2 so2 fo2 al2].
  unfold mm_cmpxchg_eqb; cbn.
  rewrite !Bool.andb_true_iff,
    !(mm_option_eqb_eq _ mm_unit_eqb_eq),
    !mm_texp_eqb_eq,
    (mm_option_eqb_eq _ mm_string_eqb_eq),
    !mm_ordering_eqb_eq,
    (mm_option_eqb_eq _ mm_int_syntax_eqb_eq).
  split.
  - intros [[[[[[[[-> ->] ->] ->] ->] ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_atomic_rmw_op_eqb (x y : atomic_rmw_operation) : bool :=
  match x, y with
  | Axchg, Axchg
  | Aadd, Aadd
  | Asub, Asub
  | Aand, Aand
  | Anand, Anand
  | Aor, Aor
  | Axor, Axor
  | Amax, Amax
  | Amin, Amin
  | Aumax, Aumax
  | Aumin, Aumin
  | Afadd, Afadd
  | Afsub, Afsub
  | Afmax, Afmax
  | Afmin, Afmin
  | Afmaximum, Afmaximum
  | Afminimum, Afminimum
  | Auinc_wrap, Auinc_wrap
  | Audec_wrap, Audec_wrap
  | Ausub_cond, Ausub_cond
  | Ausub_sat, Ausub_sat => true
  | _, _ => false
  end.

Lemma mm_atomic_rmw_op_eqb_eq (x y : atomic_rmw_operation) :
  mm_atomic_rmw_op_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_atomic_rmw_op_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_atomicrmw_eqb (x y : atomicrmw dtyp) : bool :=
  mm_option_eqb mm_unit_eqb (a_volatile x) (a_volatile y) &&
  mm_atomic_rmw_op_eqb (a_operation x) (a_operation y) &&
  mm_texp_eqb (a_ptr x) (a_ptr y) &&
  mm_texp_eqb (a_val x) (a_val y) &&
  mm_option_eqb mm_string_eqb (a_syncscope x) (a_syncscope y) &&
  mm_ordering_eqb (a_ordering x) (a_ordering y) &&
  mm_option_eqb mm_int_syntax_eqb (a_align x) (a_align y).

Lemma mm_atomicrmw_eqb_eq (x y : atomicrmw dtyp) :
  mm_atomicrmw_eqb x y = true <-> x = y.
Proof.
  destruct x as [v1 op1 p1 val1 s1 o1 al1],
           y as [v2 op2 p2 val2 s2 o2 al2].
  unfold mm_atomicrmw_eqb; cbn.
  rewrite !Bool.andb_true_iff,
    (mm_option_eqb_eq _ mm_unit_eqb_eq),
    mm_atomic_rmw_op_eqb_eq,
    !mm_texp_eqb_eq,
    (mm_option_eqb_eq _ mm_string_eqb_eq),
    mm_ordering_eqb_eq,
    (mm_option_eqb_eq _ mm_int_syntax_eqb_eq).
  split.
  - intros [[[[[[-> ->] ->] ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_unnamed_addr_eqb (x y : unnamed_addr) : bool :=
  match x, y with
  | Unnamed_addr, Unnamed_addr
  | Local_Unnamed_addr, Local_Unnamed_addr => true
  | _, _ => false
  end.

Lemma mm_unnamed_addr_eqb_eq (x y : unnamed_addr) :
  mm_unnamed_addr_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_unnamed_addr_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_tailcall_eqb (x y : tailcall) : bool :=
  match x, y with
  | Tail, Tail
  | Musttail, Musttail
  | Notail, Notail => true
  | _, _ => false
  end.

Lemma mm_tailcall_eqb_eq (x y : tailcall) :
  mm_tailcall_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_tailcall_eqb];
    first [split; reflexivity | split; discriminate].
Qed.

Definition mm_annotation_eqb (x y : annotation dtyp) : bool :=
  match x, y with
  | ANN_linkage l1, ANN_linkage l2 => mm_linkage_eqb l1 l2
  | ANN_preemption_specifier p1, ANN_preemption_specifier p2 => mm_preemption_eqb p1 p2
  | ANN_visibility v1, ANN_visibility v2 => mm_visibility_eqb v1 v2
  | ANN_dll_storage d1, ANN_dll_storage d2 => mm_dll_storage_eqb d1 d2
  | ANN_thread_local_storage t1, ANN_thread_local_storage t2 => mm_tls_eqb t1 t2
  | ANN_unnamed_addr u1, ANN_unnamed_addr u2 => mm_unnamed_addr_eqb u1 u2
  | ANN_addrspace n1, ANN_addrspace n2
  | ANN_align n1, ANN_align n2 => mm_int_syntax_eqb n1 n2
  | ANN_section s1, ANN_section s2
  | ANN_partition s1, ANN_partition s2
  | ANN_gc s1, ANN_gc s2
  | ANN_syncscope s1, ANN_syncscope s2 => mm_string_eqb s1 s2
  | ANN_comdat l1, ANN_comdat l2 => raw_id_eqb l1 l2
  | ANN_no_sanitize, ANN_no_sanitize
  | ANN_no_sanitize_address, ANN_no_sanitize_address
  | ANN_no_sanitize_hwaddress, ANN_no_sanitize_hwaddress
  | ANN_sanitize_address_dyninit, ANN_sanitize_address_dyninit
  | ANN_inalloca, ANN_inalloca
  | ANN_volatile, ANN_volatile
  | ANN_atomic, ANN_atomic => true
  | ANN_metadata m1, ANN_metadata m2 => mm_list_eqb mm_metadata_eqb m1 m2
  | ANN_cconv c1, ANN_cconv c2 => mm_cconv_ast_eqb c1 c2
  | ANN_prefix t1, ANN_prefix t2
  | ANN_prologue t1, ANN_prologue t2
  | ANN_personality t1, ANN_personality t2
  | ANN_num_elements t1, ANN_num_elements t2 => mm_texp_eqb t1 t2
  | ANN_tail t1, ANN_tail t2 => mm_tailcall_eqb t1 t2
  | ANN_fast_math_flag f1, ANN_fast_math_flag f2 => mm_fast_math_eqb f1 f2
  | ANN_ret_attribute p1, ANN_ret_attribute p2 => mm_param_attr_eqb p1 p2
  | ANN_fun_attribute f1, ANN_fun_attribute f2 => mm_fn_attr_eqb f1 f2
  | ANN_ordering o1, ANN_ordering o2 => mm_ordering_eqb o1 o2
  | _, _ => false
  end.

Lemma mm_annotation_eqb_eq (x y : annotation dtyp) :
  mm_annotation_eqb x y = true <-> x = y.
Proof.
  destruct x; destruct y; cbn [mm_annotation_eqb];
    try solve [split; reflexivity | split; discriminate].
  - rewrite mm_linkage_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_preemption_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_visibility_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_dll_storage_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_tls_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_unnamed_addr_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_int_syntax_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite (mm_list_eqb_eq _ mm_metadata_eqb_eq); split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_cconv_ast_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_tailcall_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_fast_math_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_param_attr_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_fn_attr_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_ordering_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_operand_eqb (x y : @operand dtyp) : bool :=
  match x, y with
  | SSA_value t1, SSA_value t2 => mm_texp_eqb t1 t2
  | Metadata_string m1, Metadata_string m2 => mm_metadata_eqb m1 m2
  | _, _ => false
  end.

Lemma mm_operand_eqb_eq (x y : @operand dtyp) :
  mm_operand_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_operand_eqb]; try (split; discriminate).
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_metadata_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
Qed.

Definition mm_operand_bundle_eqb (x y : @operand_bundle dtyp) : bool :=
  mm_string_eqb (ob_tag x) (ob_tag y) &&
  mm_list_eqb mm_operand_eqb (ob_ops x) (ob_ops y).

Lemma mm_operand_bundle_eqb_eq (x y : @operand_bundle dtyp) :
  mm_operand_bundle_eqb x y = true <-> x = y.
Proof.
  destruct x as [t1 o1], y as [t2 o2]; unfold mm_operand_bundle_eqb; cbn.
  rewrite Bool.andb_true_iff, mm_string_eqb_eq, (mm_list_eqb_eq _ mm_operand_eqb_eq).
  split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
Qed.

Definition mm_landingpad_clause_eqb (x y : @landingpad_clause dtyp) : bool :=
  match x, y with
  | CATCH t1, CATCH t2
  | FILTER t1, FILTER t2 => mm_texp_eqb t1 t2
  | _, _ => false
  end.

Lemma mm_landingpad_clause_eqb_eq (x y : @landingpad_clause dtyp) :
  mm_landingpad_clause_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_landingpad_clause_eqb]; try (split; discriminate);
    (rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity]).
Qed.

Definition mm_call_arg_eqb :
  texp dtyp * list param_attr -> texp dtyp * list param_attr -> bool :=
  mm_prod_eqb mm_texp_eqb (mm_list_eqb mm_param_attr_eqb).

Lemma mm_call_arg_eqb_eq (x y : texp dtyp * list param_attr) :
  mm_call_arg_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _ mm_texp_eqb_eq (mm_list_eqb_eq _ mm_param_attr_eqb_eq) x y).
Qed.

Definition mm_instr_eqb (x y : instr dtyp) : bool :=
  match x, y with
  | INSTR_Comment m1, INSTR_Comment m2 => mm_string_eqb m1 m2
  | INSTR_Op op1, INSTR_Op op2 => mm_exp_eqb op1 op2
  | INSTR_Call fn1 args1 anns1 obs1, INSTR_Call fn2 args2 anns2 obs2 =>
      mm_texp_eqb fn1 fn2 &&
      mm_list_eqb mm_call_arg_eqb args1 args2 &&
      mm_list_eqb mm_annotation_eqb anns1 anns2 &&
      mm_list_eqb mm_operand_bundle_eqb obs1 obs2
  | INSTR_Alloca t1 anns1, INSTR_Alloca t2 anns2 =>
      mm_dtyp_eqb t1 t2 && mm_list_eqb mm_annotation_eqb anns1 anns2
  | INSTR_Load t1 ptr1 anns1, INSTR_Load t2 ptr2 anns2 =>
      mm_dtyp_eqb t1 t2 && mm_texp_eqb ptr1 ptr2 && mm_list_eqb mm_annotation_eqb anns1 anns2
  | INSTR_Store val1 ptr1 anns1, INSTR_Store val2 ptr2 anns2 =>
      mm_texp_eqb val1 val2 && mm_texp_eqb ptr1 ptr2 && mm_list_eqb mm_annotation_eqb anns1 anns2
  | INSTR_Fence s1 o1, INSTR_Fence s2 o2 =>
      mm_option_eqb mm_string_eqb s1 s2 && mm_ordering_eqb o1 o2
  | INSTR_AtomicCmpXchg c1, INSTR_AtomicCmpXchg c2 => mm_cmpxchg_eqb c1 c2
  | INSTR_AtomicRMW a1, INSTR_AtomicRMW a2 => mm_atomicrmw_eqb a1 a2
  | INSTR_VAArg va1 t1, INSTR_VAArg va2 t2 =>
      mm_texp_eqb va1 va2 && mm_dtyp_eqb t1 t2
  | INSTR_LandingPad r1 cl1 cs1, INSTR_LandingPad r2 cl2 cs2 =>
      mm_dtyp_eqb r1 r2 && mm_bool_eqb cl1 cl2 &&
      mm_list_eqb mm_landingpad_clause_eqb cs1 cs2
  | _, _ => false
  end.

Lemma mm_instr_eqb_eq (x y : instr dtyp) :
  mm_instr_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_instr_eqb]; try (split; discriminate).
  - rewrite mm_string_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_exp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_texp_eqb_eq,
      (mm_list_eqb_eq _ mm_call_arg_eqb_eq),
      (mm_list_eqb_eq _ mm_annotation_eqb_eq),
      (mm_list_eqb_eq _ mm_operand_bundle_eqb_eq).
    split; [intros [[[-> ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> ->; repeat split; reflexivity].
  - rewrite Bool.andb_true_iff, mm_dtyp_eqb_eq, (mm_list_eqb_eq _ mm_annotation_eqb_eq).
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_dtyp_eqb_eq, mm_texp_eqb_eq,
      (mm_list_eqb_eq _ mm_annotation_eqb_eq).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite !Bool.andb_true_iff, !mm_texp_eqb_eq,
      (mm_list_eqb_eq _ mm_annotation_eqb_eq).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite Bool.andb_true_iff, (mm_option_eqb_eq _ mm_string_eqb_eq), mm_ordering_eqb_eq.
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - rewrite mm_cmpxchg_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite mm_atomicrmw_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite Bool.andb_true_iff, mm_texp_eqb_eq, mm_dtyp_eqb_eq.
    split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; split; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_dtyp_eqb_eq, mm_bool_eqb_eq,
      (mm_list_eqb_eq _ mm_landingpad_clause_eqb_eq).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
Qed.

Definition mm_terminator_eqb (x y : terminator dtyp) : bool :=
  match x, y with
  | TERM_Ret v1, TERM_Ret v2 => mm_texp_eqb v1 v2
  | TERM_Ret_void, TERM_Ret_void => true
  | TERM_Br v1 a1 b1, TERM_Br v2 a2 b2 =>
      mm_texp_eqb v1 v2 && raw_id_eqb a1 a2 && raw_id_eqb b1 b2
  | TERM_Br_1 b1, TERM_Br_1 b2 => raw_id_eqb b1 b2
  | TERM_Switch v1 d1 brs1, TERM_Switch v2 d2 brs2 =>
      mm_texp_eqb v1 v2 && raw_id_eqb d1 d2 &&
      mm_list_eqb (mm_prod_eqb mm_tint_literal_eqb raw_id_eqb) brs1 brs2
  | TERM_IndirectBr v1 brs1 fn1, TERM_IndirectBr v2 brs2 fn2 =>
      mm_texp_eqb v1 v2 && mm_list_eqb raw_id_eqb brs1 brs2 &&
      mm_option_eqb raw_id_eqb fn1 fn2
  | TERM_Resume v1, TERM_Resume v2 => mm_texp_eqb v1 v2
  | TERM_Invoke fn1 args1 to1 uw1 anns1 obs1,
    TERM_Invoke fn2 args2 to2 uw2 anns2 obs2 =>
      mm_texp_eqb fn1 fn2 &&
      mm_list_eqb mm_call_arg_eqb args1 args2 &&
      raw_id_eqb to1 to2 &&
      raw_id_eqb uw1 uw2 &&
      mm_list_eqb mm_annotation_eqb anns1 anns2 &&
      mm_list_eqb mm_operand_bundle_eqb obs1 obs2
  | TERM_Unreachable, TERM_Unreachable => true
  | _, _ => false
  end.

Lemma mm_terminator_eqb_eq (x y : terminator dtyp) :
  mm_terminator_eqb x y = true <-> x = y.
Proof.
  destruct x, y; cbn [mm_terminator_eqb];
    try solve [split; reflexivity | split; discriminate].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_texp_eqb_eq, !raw_id_eqb_spec.
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite raw_id_eqb_spec; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_texp_eqb_eq, raw_id_eqb_spec,
      (mm_list_eqb_eq _ (mm_prod_eqb_eq _ _ mm_tint_literal_eqb_eq raw_id_eqb_spec)).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_texp_eqb_eq,
      (mm_list_eqb_eq _ raw_id_eqb_spec), (mm_option_eqb_eq _ raw_id_eqb_spec).
    split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; repeat split; reflexivity].
  - rewrite mm_texp_eqb_eq; split; [intros ->; reflexivity | intros H; injection H as ->; reflexivity].
  - rewrite !Bool.andb_true_iff, mm_texp_eqb_eq,
      (mm_list_eqb_eq _ mm_call_arg_eqb_eq),
      !raw_id_eqb_spec,
      (mm_list_eqb_eq _ mm_annotation_eqb_eq),
      (mm_list_eqb_eq _ mm_operand_bundle_eqb_eq).
    split; [intros [[[[[-> ->] ->] ->] ->] ->]; reflexivity | intros H; injection H as -> -> -> -> -> ->; repeat split; reflexivity].
Qed.

Definition mm_phi_entry_eqb :
  local_id * phi dtyp * list (metadata dtyp) ->
  local_id * phi dtyp * list (metadata dtyp) -> bool :=
  mm_prod_eqb (mm_prod_eqb raw_id_eqb mm_phi_eqb) (mm_list_eqb mm_metadata_eqb).

Lemma mm_phi_entry_eqb_eq (x y : local_id * phi dtyp * list (metadata dtyp)) :
  mm_phi_entry_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _
           (mm_prod_eqb_eq _ _ raw_id_eqb_spec mm_phi_eqb_eq)
           (mm_list_eqb_eq _ mm_metadata_eqb_eq) x y).
Qed.

Definition mm_code_entry_eqb :
  instr_id * instr dtyp * list (metadata dtyp) ->
  instr_id * instr dtyp * list (metadata dtyp) -> bool :=
  mm_prod_eqb (mm_prod_eqb mm_instr_id_eqb mm_instr_eqb) (mm_list_eqb mm_metadata_eqb).

Lemma mm_code_entry_eqb_eq (x y : instr_id * instr dtyp * list (metadata dtyp)) :
  mm_code_entry_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _
           (mm_prod_eqb_eq _ _ mm_instr_id_eqb_eq mm_instr_eqb_eq)
           (mm_list_eqb_eq _ mm_metadata_eqb_eq) x y).
Qed.

Definition mm_term_entry_eqb :
  instr_id * terminator dtyp * list (metadata dtyp) ->
  instr_id * terminator dtyp * list (metadata dtyp) -> bool :=
  mm_prod_eqb (mm_prod_eqb mm_instr_id_eqb mm_terminator_eqb) (mm_list_eqb mm_metadata_eqb).

Lemma mm_term_entry_eqb_eq (x y : instr_id * terminator dtyp * list (metadata dtyp)) :
  mm_term_entry_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _
           (mm_prod_eqb_eq _ _ mm_instr_id_eqb_eq mm_terminator_eqb_eq)
           (mm_list_eqb_eq _ mm_metadata_eqb_eq) x y).
Qed.

Definition mm_block_eqb (x y : block dtyp) : bool :=
  raw_id_eqb (blk_id x) (blk_id y) &&
  mm_list_eqb mm_phi_entry_eqb (blk_phis x) (blk_phis y) &&
  mm_list_eqb mm_code_entry_eqb (blk_code x) (blk_code y) &&
  mm_term_entry_eqb (blk_term x) (blk_term y) &&
  mm_option_eqb (mm_list_eqb mm_string_eqb) (blk_comments x) (blk_comments y).

Lemma mm_block_eqb_eq (x y : block dtyp) :
  mm_block_eqb x y = true <-> x = y.
Proof.
  destruct x as [id1 ph1 cd1 tm1 cm1], y as [id2 ph2 cd2 tm2 cm2].
  unfold mm_block_eqb; cbn.
  rewrite !Bool.andb_true_iff, raw_id_eqb_spec,
    (mm_list_eqb_eq _ mm_phi_entry_eqb_eq),
    (mm_list_eqb_eq _ mm_code_entry_eqb_eq),
    mm_term_entry_eqb_eq,
    (mm_option_eqb_eq _ (mm_list_eqb_eq _ mm_string_eqb_eq)).
  split.
  - intros [[[[-> ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_cfg_eqb (x y : CFG.cfg dtyp) : bool :=
  raw_id_eqb (init x) (init y) &&
  mm_list_eqb mm_block_eqb (blks x) (blks y) &&
  mm_list_eqb raw_id_eqb (args x) (args y).

Lemma mm_cfg_eqb_eq (x y : CFG.cfg dtyp) :
  mm_cfg_eqb x y = true <-> x = y.
Proof.
  destruct x as [in1 bk1 ar1], y as [in2 bk2 ar2].
  unfold mm_cfg_eqb; cbn.
  rewrite !Bool.andb_true_iff, raw_id_eqb_spec,
    (mm_list_eqb_eq _ mm_block_eqb_eq),
    (mm_list_eqb_eq _ raw_id_eqb_spec).
  split.
  - intros [[-> ->] ->]; reflexivity.
  - intros H; injection H as -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_global_eqb (x y : global dtyp) : bool :=
  raw_id_eqb (g_ident x) (g_ident y) &&
  mm_dtyp_eqb (g_typ x) (g_typ y) &&
  mm_bool_eqb (g_constant x) (g_constant y) &&
  mm_option_eqb mm_exp_eqb (g_exp x) (g_exp y) &&
  mm_bool_eqb (g_externally_initialized x) (g_externally_initialized y) &&
  mm_bool_eqb (g_alias x) (g_alias y) &&
  mm_list_eqb mm_annotation_eqb (g_annotations x) (g_annotations y).

Lemma mm_global_eqb_eq (x y : global dtyp) :
  mm_global_eqb x y = true <-> x = y.
Proof.
  destruct x as [id1 ty1 c1 ex1 ei1 al1 an1],
           y as [id2 ty2 c2 ex2 ei2 al2 an2].
  unfold mm_global_eqb; cbn.
  rewrite !Bool.andb_true_iff, raw_id_eqb_spec, mm_dtyp_eqb_eq,
    !mm_bool_eqb_eq, (mm_option_eqb_eq _ mm_exp_eqb_eq),
    (mm_list_eqb_eq _ mm_annotation_eqb_eq).
  split.
  - intros [[[[[[-> ->] ->] ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_param_attrs_pair_eqb :
  list param_attr * list (list param_attr) ->
  list param_attr * list (list param_attr) -> bool :=
  mm_prod_eqb
    (mm_list_eqb mm_param_attr_eqb)
    (mm_list_eqb (mm_list_eqb mm_param_attr_eqb)).

Lemma mm_param_attrs_pair_eqb_eq
  (x y : list param_attr * list (list param_attr)) :
  mm_param_attrs_pair_eqb x y = true <-> x = y.
Proof.
  exact (mm_prod_eqb_eq _ _
           (mm_list_eqb_eq _ mm_param_attr_eqb_eq)
           (mm_list_eqb_eq _ (mm_list_eqb_eq _ mm_param_attr_eqb_eq)) x y).
Qed.

Definition mm_declaration_eqb (x y : declaration dtyp) : bool :=
  raw_id_eqb (dc_name x) (dc_name y) &&
  mm_dtyp_eqb (dc_type x) (dc_type y) &&
  mm_param_attrs_pair_eqb (dc_param_attrs x) (dc_param_attrs y) &&
  mm_list_eqb mm_fn_attr_eqb (dc_attrs x) (dc_attrs y) &&
  mm_list_eqb mm_annotation_eqb (dc_annotations x) (dc_annotations y).

Lemma mm_declaration_eqb_eq (x y : declaration dtyp) :
  mm_declaration_eqb x y = true <-> x = y.
Proof.
  destruct x as [nm1 ty1 pa1 fa1 an1], y as [nm2 ty2 pa2 fa2 an2].
  unfold mm_declaration_eqb; cbn.
  rewrite !Bool.andb_true_iff, raw_id_eqb_spec, mm_dtyp_eqb_eq,
    mm_param_attrs_pair_eqb_eq,
    (mm_list_eqb_eq _ mm_fn_attr_eqb_eq),
    (mm_list_eqb_eq _ mm_annotation_eqb_eq).
  split.
  - intros [[[[-> ->] ->] ->] ->]; reflexivity.
  - intros H; injection H as -> -> -> -> ->; repeat split; reflexivity.
Qed.

Definition mm_definition_eqb
  (x y : definition dtyp (CFG.cfg dtyp)) : bool :=
  mm_declaration_eqb (df_prototype x) (df_prototype y) &&
  mm_list_eqb raw_id_eqb (df_args x) (df_args y) &&
  mm_cfg_eqb (df_instrs x) (df_instrs y).

Lemma mm_definition_eqb_eq (x y : definition dtyp (CFG.cfg dtyp)) :
  mm_definition_eqb x y = true <-> x = y.
Proof.
  destruct x as [p1 a1 i1], y as [p2 a2 i2]; unfold mm_definition_eqb; cbn.
  rewrite !Bool.andb_true_iff, mm_declaration_eqb_eq,
    (mm_list_eqb_eq _ raw_id_eqb_spec), mm_cfg_eqb_eq.
  split.
  - intros [[-> ->] ->]; reflexivity.
  - intros H; injection H as -> -> ->; repeat split; reflexivity.
Qed.


(** * 2. Module Split/Merge Soundness Invariants & Executable Validator *)

Fixpoint mm_nodup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (in_raw_ids x rest) && mm_nodup_raw_ids rest
  end.

Lemma mm_nodup_raw_ids_spec (xs : list raw_id) :
  mm_nodup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rest IH]; cbn [mm_nodup_raw_ids].
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, in_raw_ids_false, IH.
    split; [intros [Hnin Hnd]; constructor; assumption
           | intros Hnd; inversion Hnd; subst; split; assumption].
Qed.

Definition opt_linkage_no_extern_weak (ol : option linkage) : bool :=
  match ol with
  | Some LINKAGE_Extern_weak => false
  | _ => true
  end.

Lemma opt_linkage_no_extern_weak_spec (ol : option linkage) :
  opt_linkage_no_extern_weak ol = true <-> ol <> Some LINKAGE_Extern_weak.
Proof.
  destruct ol as [l |]; [destruct l |]; cbn [opt_linkage_no_extern_weak];
    first [split; [discriminate | intros H; exfalso; exact (H Logic.eq_refl)]
          | split; [intros _ H; discriminate H | intros _; reflexivity]].
Qed.

Definition global_no_extern_weak (g : global dtyp) : bool :=
  opt_linkage_no_extern_weak (g_linkage g).

Definition decl_no_extern_weak (d : declaration dtyp) : bool :=
  opt_linkage_no_extern_weak (dc_linkage d).

(** [ir-bridge split] externalizes internal/private linkage on extracted
    per-function slices so LLVM [-O2] ([GlobalDCE]) cannot delete the slice
    entry definition.  Slice linkage is therefore compatible when it is either
    externalized ([None] / [Some LINKAGE_External]) or identical to [m_orig],
    and never [LINKAGE_Extern_weak]. *)
Definition dc_linkage_slice_compatible
  (orig_lnk slice_lnk : option linkage) : bool :=
  opt_linkage_no_extern_weak slice_lnk &&
  match slice_lnk with
  | None | Some LINKAGE_External => true
  | _ => mm_option_eqb mm_linkage_eqb slice_lnk orig_lnk
  end.

Lemma dc_linkage_slice_compatible_spec
  (orig_lnk slice_lnk : option linkage) :
  dc_linkage_slice_compatible orig_lnk slice_lnk = true ->
  slice_lnk <> Some LINKAGE_Extern_weak /\
  (slice_lnk = None \/ slice_lnk = Some LINKAGE_External \/ slice_lnk = orig_lnk).
Proof.
  unfold dc_linkage_slice_compatible.
  rewrite Bool.andb_true_iff, opt_linkage_no_extern_weak_spec.
  intros [Hnw Hlnk]; split; [exact Hnw |].
  destruct slice_lnk as [l |]; [| left; reflexivity].
  destruct l;
    try (apply (mm_option_eqb_eq _ mm_linkage_eqb_eq) in Hlnk; right; right; exact Hlnk).
  right; left; reflexivity.
Qed.

(** Match a single [(df_orig, df_merged)] pair against one verified slice entry
    [(fid, m_slice_src, m_slice_tgt)]. *)
Definition check_slice_matches_defn
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : bool :=
  let '(fid, m_slice_src, m_slice_tgt) := entry in
  let proto_orig := df_prototype df_orig in
  raw_id_eqb (dc_name proto_orig) fid &&
  match m_definitions m_slice_src, m_definitions m_slice_tgt with
  | [df_src], [df_tgt] =>
      let proto_src := df_prototype df_src in
      let proto_tgt := df_prototype df_tgt in
      raw_id_eqb (dc_name proto_src) fid &&
      mm_dtyp_eqb (dc_type proto_src) (dc_type proto_orig) &&
      mm_param_attrs_pair_eqb (dc_param_attrs proto_src) (dc_param_attrs proto_orig) &&
      cconv_eqb (anns_cconv (dc_annotations proto_src))
                (anns_cconv (dc_annotations proto_orig)) &&
      dc_linkage_slice_compatible (dc_linkage proto_orig) (dc_linkage proto_src) &&
      mm_list_eqb raw_id_eqb (df_args df_src) (df_args df_orig) &&
      mm_cfg_eqb (df_instrs df_src) (df_instrs df_orig) &&
      raw_id_eqb (dc_name proto_tgt) fid &&
      decl_no_extern_weak proto_tgt &&
      mm_list_eqb raw_id_eqb (df_args df_tgt) (df_args df_merged) &&
      mm_cfg_eqb (df_instrs df_tgt) (df_instrs df_merged)
  | _, _ => false
  end.

Definition check_defn_pair
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) : bool :=
  mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig) &&
  mm_list_eqb raw_id_eqb (df_args df_merged) (df_args df_orig) &&
  (mm_definition_eqb df_merged df_orig ||
   existsb (check_slice_matches_defn df_orig df_merged) verified_slices).

Fixpoint check_defs_merge
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp))) : bool :=
  match defs_orig, defs_merged with
  | [], [] => true
  | d1 :: r1, d2 :: r2 =>
      check_defn_pair verified_slices d1 d2 && check_defs_merge verified_slices r1 r2
  | _, _ => false
  end.

(** Decidable boolean module-merge checker closing F-19, F-24, F-33, and F-47. *)
Definition check_module_merge
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) : bool :=
  mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig) &&
  forallb global_no_extern_weak (m_globals m_orig) &&
  mm_list_eqb mm_declaration_eqb (m_declarations m_merged) (m_declarations m_orig) &&
  forallb decl_no_extern_weak (m_declarations m_orig) &&
  forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig) &&
  mm_nodup_raw_ids
    (List.map dc_name
       (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))) &&
  mm_list_eqb mm_block_addr_eqb
    (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
    (nodup block_address_eq_dec (mcfg_block_addresses m_orig)) &&
  check_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

Fixpoint validate_defs_merge
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp)))
  : string + unit :=
  match defs_orig, defs_merged with
  | [], [] => inr tt
  | [], _ :: _ =>
      inl "validate_module_merge: extra function definition in m_merged"%string
  | _ :: _, [] =>
      inl "validate_module_merge: missing function definition in m_merged"%string
  | df_orig :: r1, df_merged :: r2 =>
      let fname := show_raw_id (dc_name (df_prototype df_orig)) in
      if negb (mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig)) then
        inl ("validate_module_merge: prototype/attribute desync on @" ++ fname)%string
      else if negb (mm_list_eqb raw_id_eqb (df_args df_merged) (df_args df_orig)) then
        inl ("validate_module_merge: formal parameter list desync on @" ++ fname)%string
      else if negb (mm_definition_eqb df_merged df_orig ||
                    existsb (check_slice_matches_defn df_orig df_merged) verified_slices) then
        inl ("validate_module_merge: unverified body modification on @" ++ fname)%string
      else
        validate_defs_merge verified_slices r1 r2
  end.

(** Diagnostic wrapper suitable for OCaml CLI extraction ([Extract.v]). *)
Definition validate_module_merge
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  : string + unit :=
  if negb (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig)) then
    inl "validate_module_merge: m_globals layout or alignment mismatch"%string
  else if negb (forallb global_no_extern_weak (m_globals m_orig)) then
    inl "validate_module_merge: extern_weak global linkage is unsupported"%string
  else if negb (mm_list_eqb mm_declaration_eqb (m_declarations m_merged) (m_declarations m_orig)) then
    inl "validate_module_merge: m_declarations symbol table mismatch"%string
  else if negb (forallb decl_no_extern_weak (m_declarations m_orig)) then
    inl "validate_module_merge: extern_weak declaration linkage is unsupported"%string
  else if negb (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig)) then
    inl "validate_module_merge: extern_weak definition linkage is unsupported"%string
  else if negb (mm_nodup_raw_ids
                  (List.map dc_name
                     (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig)))) then
    inl "validate_module_merge: duplicate function symbol in declarations/definitions"%string
  else if negb (mm_list_eqb mm_block_addr_eqb
                  (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
                  (nodup block_address_eq_dec (mcfg_block_addresses m_orig))) then
    inl "validate_module_merge: module blockaddress table mismatch"%string
  else
    validate_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

Lemma validate_defs_merge_ok_iff
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  forall defs_orig defs_merged,
    validate_defs_merge verified_slices defs_orig defs_merged = inr tt <->
    check_defs_merge verified_slices defs_orig defs_merged = true.
Proof.
  induction defs_orig as [| d1 r1 IH]; intros [| d2 r2];
    cbn [validate_defs_merge check_defs_merge].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - unfold check_defn_pair; cbv zeta.
    destruct (mm_declaration_eqb (df_prototype d2) (df_prototype d1)); cbn [negb andb];
      [| split; discriminate].
    destruct (mm_list_eqb raw_id_eqb (df_args d2) (df_args d1)); cbn [negb andb];
      [| split; discriminate].
    destruct (mm_definition_eqb d2 d1 ||
              existsb (check_slice_matches_defn d1 d2) verified_slices);
      cbn [negb andb]; [exact (IH r2) | split; discriminate].
Qed.

Theorem validate_module_merge_ok_iff
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  validate_module_merge m_orig m_merged verified_slices = inr tt <->
  check_module_merge m_orig m_merged verified_slices = true.
Proof.
  unfold validate_module_merge, check_module_merge.
  destruct (mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb global_no_extern_weak (m_globals m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_list_eqb mm_declaration_eqb (m_declarations m_merged) (m_declarations m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb decl_no_extern_weak (m_declarations m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_nodup_raw_ids
              (List.map dc_name
                 (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))));
    cbn [negb andb]; [| split; discriminate].
  destruct (mm_list_eqb mm_block_addr_eqb
              (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
              (nodup block_address_eq_dec (mcfg_block_addresses m_orig)));
    cbn [negb andb]; [| split; discriminate].
  apply validate_defs_merge_ok_iff.
Qed.


(** * 3. Structural Reflection Lemmas *)

Record slice_witness_prop
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (fid : function_id)
  (m_slice_src m_slice_tgt : CFG.mcfg dtyp)
  (df_src df_tgt : definition dtyp (CFG.cfg dtyp)) : Prop :=
  { sw_fid_eq :
      dc_name (df_prototype df_orig) = fid;
    sw_src_defs :
      m_definitions m_slice_src = [df_src];
    sw_tgt_defs :
      m_definitions m_slice_tgt = [df_tgt];
    sw_src_name :
      dc_name (df_prototype df_src) = fid;
    sw_src_type :
      dc_type (df_prototype df_src) = dc_type (df_prototype df_orig);
    sw_src_param_attrs :
      dc_param_attrs (df_prototype df_src) = dc_param_attrs (df_prototype df_orig);
    sw_src_cconv :
      cconv_eqb (anns_cconv (dc_annotations (df_prototype df_src)))
                (anns_cconv (dc_annotations (df_prototype df_orig))) = true;
    sw_src_linkage_no_ew :
      dc_linkage (df_prototype df_src) <> Some LINKAGE_Extern_weak;
    sw_src_linkage_compat :
      dc_linkage (df_prototype df_src) = None \/
      dc_linkage (df_prototype df_src) = Some LINKAGE_External \/
      dc_linkage (df_prototype df_src) = dc_linkage (df_prototype df_orig);
    sw_src_args :
      df_args df_src = df_args df_orig;
    sw_src_instrs :
      df_instrs df_src = df_instrs df_orig;
    sw_tgt_name :
      dc_name (df_prototype df_tgt) = fid;
    sw_tgt_no_ew :
      dc_linkage (df_prototype df_tgt) <> Some LINKAGE_Extern_weak;
    sw_tgt_args :
      df_args df_tgt = df_args df_merged;
    sw_tgt_instrs :
      df_instrs df_tgt = df_instrs df_merged }.

Lemma check_slice_matches_defn_spec
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp))
  (fid : function_id)
  (m_slice_src m_slice_tgt : CFG.mcfg dtyp) :
  check_slice_matches_defn df_orig df_merged (fid, m_slice_src, m_slice_tgt) = true ->
  exists df_src df_tgt,
    slice_witness_prop df_orig df_merged fid m_slice_src m_slice_tgt df_src df_tgt.
Proof.
  unfold check_slice_matches_defn; cbv zeta.
  rewrite Bool.andb_true_iff, raw_id_eqb_spec.
  intros [Hfid Hm].
  destruct (m_definitions m_slice_src) as [| df_src [| ? ?]]; try discriminate Hm.
  destruct (m_definitions m_slice_tgt) as [| df_tgt [| ? ?]]; try discriminate Hm.
  rewrite !Bool.andb_true_iff in Hm.
  destruct Hm as [[[[[[[[[[Hsn Hsty] Hspa] Hscc] Hslnk] Hsargs] Hscfg] Htn] Htew] Htargs] Htcfg].
  apply raw_id_eqb_spec in Hsn.
  apply mm_dtyp_eqb_eq in Hsty.
  apply mm_param_attrs_pair_eqb_eq in Hspa.
  apply dc_linkage_slice_compatible_spec in Hslnk as [Hs_noew Hs_compat].
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Hsargs.
  apply mm_cfg_eqb_eq in Hscfg.
  apply raw_id_eqb_spec in Htn.
  apply opt_linkage_no_extern_weak_spec in Htew.
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Htargs.
  apply mm_cfg_eqb_eq in Htcfg.
  exists df_src, df_tgt; constructor; assumption + reflexivity.
Qed.

Definition defn_pair_provenance
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) : Prop :=
  df_prototype df_merged = df_prototype df_orig /\
  df_args df_merged = df_args df_orig /\
  (df_merged = df_orig \/
   exists fid m_slice_src m_slice_tgt df_src df_tgt,
     In (fid, m_slice_src, m_slice_tgt) verified_slices /\
     slice_witness_prop df_orig df_merged fid m_slice_src m_slice_tgt df_src df_tgt).

Lemma check_defn_pair_spec
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) :
  check_defn_pair verified_slices df_orig df_merged = true ->
  defn_pair_provenance verified_slices df_orig df_merged.
Proof.
  unfold check_defn_pair.
  rewrite !Bool.andb_true_iff, Bool.orb_true_iff.
  intros [[Hproto Hargs] Hdisj].
  apply mm_declaration_eqb_eq in Hproto.
  apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Hargs.
  refine (conj Hproto (conj Hargs _)).
  destruct Hdisj as [Heq | Hex].
  - left; apply mm_definition_eqb_eq, Heq.
  - right; apply existsb_exists in Hex as [[[fid m_src] m_tgt] [Hin Hmatch]].
    destruct (check_slice_matches_defn_spec df_orig df_merged fid m_src m_tgt Hmatch)
      as [df_src [df_tgt Hsw]].
    exists fid, m_src, m_tgt, df_src, df_tgt; exact (conj Hin Hsw).
Qed.

Lemma check_defs_merge_Forall2
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  forall defs_orig defs_merged,
    check_defs_merge verified_slices defs_orig defs_merged = true ->
    Forall2 (defn_pair_provenance verified_slices) defs_orig defs_merged.
Proof.
  induction defs_orig as [| d1 r1 IH]; intros [| d2 r2] H;
    cbn [check_defs_merge] in H; try discriminate H.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hhd Htl].
    constructor; [exact (check_defn_pair_spec verified_slices d1 d2 Hhd) | exact (IH r2 Htl)].
Qed.

Lemma check_defs_merge_prototypes_eq
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp))) :
  check_defs_merge verified_slices defs_orig defs_merged = true ->
  List.map df_prototype defs_merged = List.map df_prototype defs_orig.
Proof.
  intros H; pose proof (check_defs_merge_Forall2 verified_slices defs_orig defs_merged H) as HF.
  induction HF as [| d1 d2 r1 r2 [Hpr _] _ IH]; cbn [List.map];
    [reflexivity | rewrite Hpr, IH; reflexivity].
Qed.

Theorem check_module_merge_globals_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  m_globals m_merged = m_globals m_orig.
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[[H _] _] _] _] _] _] _].
  exact (proj1 (mm_list_eqb_eq _ mm_global_eqb_eq _ _) H).
Qed.

Theorem check_module_merge_globals_no_extern_weak
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall (fun g => g_linkage g <> Some LINKAGE_Extern_weak) (m_globals m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[[_ H] _] _] _] _] _] _].
  apply Forall_forall; intros g Hg.
  rewrite forallb_forall in H; apply opt_linkage_no_extern_weak_spec, (H g Hg).
Qed.

Theorem check_module_merge_declarations_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  m_declarations m_merged = m_declarations m_orig.
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[_ H] _] _] _] _] _].
  exact (proj1 (mm_list_eqb_eq _ mm_declaration_eqb_eq _ _) H).
Qed.

Theorem check_module_merge_declarations_no_extern_weak
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall (fun d => dc_linkage d <> Some LINKAGE_Extern_weak) (m_declarations m_orig) /\
  Forall (fun df => dc_linkage (df_prototype df) <> Some LINKAGE_Extern_weak) (m_definitions m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[[[[_ Hd] Hdf] _] _] _]].
  split; apply Forall_forall.
  - intros d Hin; rewrite forallb_forall in Hd; apply opt_linkage_no_extern_weak_spec, (Hd d Hin).
  - intros df Hin; rewrite forallb_forall in Hdf; apply opt_linkage_no_extern_weak_spec, (Hdf df Hin).
Qed.

Theorem check_module_merge_symbol_nodup
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  NoDup (List.map dc_name (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[[_ Hnd] _] _].
  exact (proj1 (mm_nodup_raw_ids_spec _) Hnd).
Qed.

Theorem check_module_merge_block_addresses_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  nodup block_address_eq_dec (mcfg_block_addresses m_merged) =
  nodup block_address_eq_dec (mcfg_block_addresses m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [[_ Hba] _].
  exact (proj1 (mm_list_eqb_eq _ mm_block_addr_eqb_eq _ _) Hba).
Qed.

Theorem check_module_merge_defs_Forall2
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  Forall2 (defn_pair_provenance verified_slices)
    (m_definitions m_orig) (m_definitions m_merged).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [_ Hdefs].
  exact (check_defs_merge_Forall2 verified_slices _ _ Hdefs).
Qed.

Theorem check_module_merge_prototypes_eq
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
  check_module_merge m_orig m_merged verified_slices = true ->
  List.map df_prototype (m_definitions m_merged) =
  List.map df_prototype (m_definitions m_orig).
Proof.
  unfold check_module_merge; rewrite !Bool.andb_true_iff.
  intros [_ Hdefs].
  exact (check_defs_merge_prototypes_eq verified_slices _ _ Hdefs).
Qed.

Theorem check_module_merge_build_global_environment_eq
  {Pa : Params}
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true) :
  @build_global_environment Pa m_merged = @build_global_environment Pa m_orig.
Proof.
  unfold build_global_environment.
  rewrite (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk),
          (check_module_merge_prototypes_eq m_orig m_merged verified_slices Hchk),
          (check_module_merge_block_addresses_eq m_orig m_merged verified_slices Hchk),
          (check_module_merge_globals_eq m_orig m_merged verified_slices Hchk).
  reflexivity.
Qed.


(** * 4. Open-World Per-Slice Refinement & Whole-Module Compositional Linking *)

Section CompositionalLinking.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  (** General relational lifter for [cfg_local_sim] across arbitrary pairs of
      modules sharing [build_global_environment] and [m_declarations]. *)
  Lemma map_monad_address_defs_stack_sim
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall env va,
                    (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                      env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               defs1 defs2) :
    forall stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_function defs1)
        (map_monad address_one_function defs2).
  Proof using.
    induction Hdefs as [| d1 d2 r1 r2 (Hpr & Har & Hbd) _ IH];
      intros stk env1 env2; cbn [map_monad].
    - apply gen_stack_sim_ret; repeat split; [reflexivity | constructor].
    - eapply gen_stack_sim_bind.
      + unfold address_one_function; rewrite Hpr.
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise, trigger_cast; apply gen_stack_sim_trigger_sync;
                 [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]).
          apply gen_stack_sim_ret; repeat split; try reflexivity.
          apply cfg_stack_sim_denote_function;
            [symmetry; exact Hpr | symmetry; exact Har | exact Hbd].
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hhd).
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; [reflexivity | constructor; assumption].
  Qed.

  #[local] Definition mm_mrec_ctx
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

  Lemma module_defs_cfg_sim_refines
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall env va,
                    (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                      env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               (m_definitions M1) (m_definitions M2)) :
    @prog_refines IP IPT M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & _ & _ & <-); reflexivity | apply incl_refl |].
    eapply mcfg_stack_sim_to_model with (stk := []) (env1 := Maps.empty) (env2 := Maps.empty).
    { unfold init_fused_state, fused_state_match; repeat split; try reflexivity; constructor. }
    apply mcfg_stack_sim_interp_intrinsics.
    unfold denote_vellvm; rewrite Hbg, Hdecls.
    eapply gen_stack_sim_bind;
      [apply mcfg_stack_sim_refl_diag; constructor |].
    intros stk1 e1 e2 [] _ (_ & <- & _).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_defs_stack_sim _ _ Hdefs) |].
    intros ? ? ? defns1 defns2 (-> & -> & -> & Hdefns).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_library_stack_sim _
                (library_functions_stack_sync (m_declarations M1))) |].
    intros ? ? ? libs1 libs2 (-> & -> & -> & Hlibs).
    eapply gen_stack_sim_bind.
    { unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]. }
    intros ? ? ? addr _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - assert (Hmrec_eq : forall fundefs,
                denote_mcfg fundefs ret_typ addr args =
                interp_mrec (mm_mrec_ctx fundefs)
                  (mm_mrec_ctx fundefs _ (Call ret_typ CC_Ccc addr args)))
        by (intros fundefs; unfold denote_mcfg, mrec; reflexivity).
      rewrite !Hmrec_eq.
      assert (Hctx : forall k,
                option_rel
                  (fun f1 f2 =>
                     forall stk env1 env2 cc fargs,
                       cfg_stack_sim
                         (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                         stk env1 env2 (f1 cc fargs) (f2 cc fargs))
                  (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
                  (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { apply of_list_fn_ctx_stack_sim, Forall2_app; assumption. }
      eapply cfg_to_mcfg_stack_sim_mrec with
        (ctx1 := IntMaps.IP.of_list (defns1 ++ libs1))
        (ctx2 := IntMaps.IP.of_list (defns2 ++ libs2));
        [exact Hctx | reflexivity | reflexivity |].
      unfold mm_mrec_ctx; cbn [Monads.bind Monad_itree].
      eapply gen_stack_sim_bind;
        [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
      assert (Hext :
        cfg_stack_sim
          (fun stk' e1' e2' r1 r2 => stk' = stk1 /\ e1' = e1 /\ e2' = e1 /\ r1 = r2)
          stk1 e1 e1
          (Functor.fmap inr (external_call ret_typ addr args))
          (Functor.fmap inr (external_call ret_typ addr args))).
      { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
        eapply gen_stack_sim_bind.
        - apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
        - intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity. }
      unfold lookup_defn.
      destruct addr as [[p | | | | | | |] | |]; try exact Hext.
      pose proof (Hctx (ptr_to_int p)) as Hlk.
      destruct (lookup (ptr_to_int p) (IntMaps.IP.of_list (defns1 ++ libs1))) as [f1 |],
               (lookup (ptr_to_int p) (IntMaps.IP.of_list (defns2 ++ libs2))) as [f2 |];
        inversion Hlk as [? ? Hf12 |]; subst; [apply Hf12 | exact Hext].
    - intros ? ? ? rv _ (-> & -> & -> & <-).
      destruct rv as [ex | v].
      + unfold raiseLLVM, trigger_cast; pstep; apply GSS_Step;
          unfold gss_step_body, ITree.trigger; cbn.
        right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
      + apply gen_stack_sim_ret; reflexivity.
  Qed.

  (** General relational lifter for [refine_cfg Logic.eq] ([ruttc]) across
      arbitrary pairs of modules sharing [build_global_environment] and
      [m_declarations]. *)
  Lemma map_monad_address_defs_refines
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall va,
                    @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                      (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               defs1 defs2) :
    refine_mcfg
      (Forall2
         (fun '(k1, fn1) '(k2, fn2) =>
            k1 = k2 /\
            forall cc args, refine_cfg Logic.eq (fn1 cc args) (fn2 cc args)))
      (map_monad address_one_function defs1)
      (map_monad address_one_function defs2).
  Proof using.
    induction Hdefs as [| d1 d2 r1 r2 (Hpr & Har & Hbd) _ IH]; cbn [map_monad].
    - apply ruttc_ret; constructor.
    - eapply ruttc_bind.
      + unfold address_one_function; rewrite Hpr.
        eapply ruttc_bind; [apply refine_mcfg_refl | intros fv _ <-].
        destruct fv as [[p | | | | | | |] | |]; try apply refine_mcfg_refl.
        apply ruttc_ret; split; [reflexivity |].
        apply refine_cfg_denote_function;
          [symmetry; exact Hpr | symmetry; exact Har | exact Hbd].
      + intros [k1 fn1] [k2 fn2] Hhd.
        eapply ruttc_bind; [exact IH | intros tl1 tl2 Htl; apply ruttc_ret; constructor; assumption].
  Qed.

  Lemma module_defs_ruttc_refines
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : Forall2
               (fun d1 d2 =>
                  df_prototype d2 = df_prototype d1 /\
                  df_args d2 = df_args d1 /\
                  forall va,
                    @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                      (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
               (m_definitions M1) (m_definitions M2)) :
    @prog_refines IP IPT M1 M2.
  Proof using.
    apply refine_vellvm_to_prog; intros ret_typ entry args.
    unfold denote_vellvm; rewrite Hbg, Hdecls.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros [] _ <-].
    eapply ruttc_bind; [exact (map_monad_address_defs_refines _ _ Hdefs) |].
    intros defns1 defns2 Hdefns.
    eapply ruttc_bind; [apply refine_mcfg_refl | intros libs _ <-].
    eapply ruttc_bind; [apply refine_mcfg_refl | intros addr _ <-].
    eapply ruttc_bind.
    - apply refine_mcfg_denote_mcfg, of_list_fn_ctx_refines.
      apply Forall2_app; [exact Hdefns | apply Forall2_fn_refl].
    - intros rv _ <-; destruct rv; apply refine_mcfg_refl.
  Qed.

  (** Open-world per-CFG refinement contract for a verified slice
      [(fid, m_slice_src, m_slice_tgt)]: at the [denote_cfg] level, [CallE],
      [MemoryE], [IntrinsicE], [GlobalE], [StackE], and [LLVMExcE] are all
      uninterpreted events, so [cfg_local_sim] makes zero closed-world
      assumptions about sibling callees or external calls (closing F-33). *)
  Definition slice_body_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      forall (env : @local_env (@ParamsV IP IPT)) (va : option (@ptr (@ParamsV IP IPT))),
        (forall x, In x (df_args df_src) -> exists v, Maps.lookup x env = Some v) ->
        cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
          env env (denote_cfg (df_instrs df_src) va) (denote_cfg (df_instrs df_tgt) va).

  Definition slice_ruttc_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      forall va : option (@ptr (@ParamsV IP IPT)),
        @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
          (denote_cfg (df_instrs df_src) va) (denote_cfg (df_instrs df_tgt) va).

  (** Master Open-World Compositional Module-Merge Refinement Theorem:
      If [check_module_merge m_orig m_merged verified_slices = true] and every
      slice in [verified_slices] satisfies [slice_body_refines], then
      [m_merged] refines [m_orig] under whole-module Vellvm 3.0 model
      semantics [@prog_refines IP IPT]. *)
  Theorem check_module_merge_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_body_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply module_defs_cfg_sim_refines.
    - exact (check_module_merge_build_global_environment_eq m_orig m_merged verified_slices Hchk).
    - exact (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk).
    - pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
      induction Hprov as [| df_orig df_merged r1 r2 (Hpr & Har & Hdisj) _ IH];
        [constructor | constructor; [| exact IH]].
      refine (conj Hpr (conj Har _)).
      intros env va Henv.
      destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
      + apply SCCP.denote_cfg_refl_sim.
      + rewrite Forall_forall in Hslices.
        pose proof (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                      (sw_src_defs _ _ _ _ _ _ _ Hsw)
                      (sw_tgt_defs _ _ _ _ _ _ _ Hsw)
                      env va) as Hsim.
        rewrite (sw_src_args _ _ _ _ _ _ _ Hsw),
                (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                (sw_tgt_instrs _ _ _ _ _ _ _ Hsw) in Hsim.
        exact (Hsim Henv).
  Qed.

  Theorem check_module_merge_ruttc_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_ruttc_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply module_defs_ruttc_refines.
    - exact (check_module_merge_build_global_environment_eq m_orig m_merged verified_slices Hchk).
    - exact (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk).
    - pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
      induction Hprov as [| df_orig df_merged r1 r2 (Hpr & Har & Hdisj) _ IH];
        [constructor | constructor; [| exact IH]].
      refine (conj Hpr (conj Har _)).
      intros va.
      destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
      + apply refine_cfg_refl.
      + rewrite Forall_forall in Hslices.
        pose proof (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                      (sw_src_defs _ _ _ _ _ _ _ Hsw)
                      (sw_tgt_defs _ _ _ _ _ _ _ Hsw)
                      va) as Hsim.
        rewrite (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                (sw_tgt_instrs _ _ _ _ _ _ _ Hsw) in Hsim.
        exact Hsim.
  Qed.

  Corollary validate_module_merge_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hval : validate_module_merge m_orig m_merged verified_slices = inr tt)
    (Hslices : Forall slice_body_refines verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply (check_module_merge_refines m_orig m_merged verified_slices);
      [exact (proj1 (validate_module_merge_ok_iff m_orig m_merged verified_slices) Hval)
      | exact Hslices].
  Qed.

End CompositionalLinking.

(** Concrete instantiations at [IPZ] and [IP64Bit], plus end-to-end
    [IPZ -> IPZ -> IP64Bit] composition with [I2F_toplevel.model_refine]. *)
Theorem check_module_merge_refines_IPZ
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices) :
  @prog_refines IPZ IPZTheory m_orig m_merged.
Proof.
  exact (@check_module_merge_refines IPZ IPZTheory m_orig m_merged verified_slices Hchk Hslices).
Qed.

Theorem check_module_merge_refines_64
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IP64Bit IP64BitTheory) verified_slices) :
  @prog_refines IP64Bit IP64BitTheory m_orig m_merged.
Proof.
  exact (@check_module_merge_refines IP64Bit IP64BitTheory m_orig m_merged verified_slices Hchk Hslices).
Qed.

Theorem check_module_merge_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (check_module_merge_refines_IPZ m_orig m_merged verified_slices Hchk Hslices).
  - exact (I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.

Corollary validate_module_merge_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hval : validate_module_merge m_orig m_merged verified_slices = inr tt)
  (Hslices : Forall (@slice_body_refines IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  exact (check_module_merge_I2F_model_refine m_orig m_merged verified_slices
           ret_typ entry args1 args2 s1 s2
           (proj1 (validate_module_merge_ok_iff m_orig m_merged verified_slices) Hval)
           Hslices Hargs Hs).
Qed.


(** * 5. Safe-Path [Pipeline.optimize_mcfg] & Heterogeneous Slice Splicing (F-20) *)

Section SafePathSlices.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  (** Direct [slice_body_refines] instances for [SCCP] and [DCE] single-CFG
      passes, plus [slice_ruttc_refines] for [SimplifyCFG] sub-passes. *)
  Lemma sccp_mcfg_satisfies_slice_body_refines
    (fid : function_id) (M : CFG.mcfg dtyp) :
    slice_body_refines (fid, M, sccp_mcfg M).
  Proof using.
    intros df_src df_tgt Hsrc Htgt env va Henv.
    unfold sccp_mcfg, map_mcfg_with_args in Htgt; rewrite Hsrc in Htgt.
    cbn [m_definitions List.map map_defn_with_args] in Htgt.
    injection Htgt as <-; cbn [df_instrs].
    exact (SCCP.sccp_cfg_sim (df_args df_src) (df_instrs df_src) env va Henv).
  Qed.

  Lemma dce_mcfg_once_satisfies_slice_body_refines
    (fid : function_id) (M : CFG.mcfg dtyp) :
    slice_body_refines (fid, M, dce_mcfg_once M).
  Proof using.
    intros df_src df_tgt Hsrc Htgt env va Henv.
    unfold dce_mcfg_once, map_mcfg_with_args in Htgt; rewrite Hsrc in Htgt.
    cbn [m_definitions List.map map_defn_with_args] in Htgt.
    injection Htgt as <-; cbn [df_instrs].
    exact (DCE.dce_cfg_once_sim (df_args df_src) (df_instrs df_src) env va Henv).
  Qed.

  (** Universal contextual splicing contract for a verified single-function
      slice: replacing [c_src] with [c_tgt] inside ANY host module [M_host]
      refines [M_host] and preserves [blockaddress] tables. *)
  Definition splice_valid_defn
    (fargs : list local_id) (c_src c_tgt : CFG.cfg dtyp) : Prop :=
    flat_map block_block_addresses (blks c_tgt) =
      flat_map block_block_addresses (blks c_src) /\
    forall (M_host : CFG.mcfg dtyp)
           (pre post : list (definition dtyp (CFG.cfg dtyp)))
           (proto : declaration dtyp),
      m_definitions M_host =
        pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c_src |} :: post ->
      @prog_refines IP IPT M_host
        {| m_name         := m_name M_host;
           m_target       := m_target M_host;
           m_datalayout   := m_datalayout M_host;
           m_type_defs    := m_type_defs M_host;
           m_globals      := m_globals M_host;
           m_declarations := m_declarations M_host;
           m_definitions  :=
             pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c_tgt |} :: post |}.

  Definition slice_valid_in_any_host
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      splice_valid_defn (df_args df_src) (df_instrs df_src) (df_instrs df_tgt).

  Lemma splice_valid_defn_refl (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c c.
  Proof using.
    split; [reflexivity |].
    intros M_host pre post proto Hdefs.
    rewrite <- Hdefs; destruct M_host; cbn; apply prog_refines_refl.
  Qed.

  Lemma splice_valid_defn_trans
    (fargs : list local_id) (c1 c2 c3 : CFG.cfg dtyp) :
    splice_valid_defn fargs c1 c2 ->
    splice_valid_defn fargs c2 c3 ->
    splice_valid_defn fargs c1 c3.
  Proof using.
    intros [Hba12 Href12] [Hba23 Href23].
    split; [etransitivity; [exact Hba23 | exact Hba12] |].
    intros M_host pre post proto Hdefs.
    eapply prog_refines_trans.
    - exact (Href12 M_host pre post proto Hdefs).
    - exact (Href23 _ pre post proto Logic.eq_refl).
  Qed.

  Lemma build_global_env_splice_eq
    (M_host : CFG.mcfg dtyp)
    (pre post : list (definition dtyp (CFG.cfg dtyp)))
    (proto : declaration dtyp)
    (fargs : list local_id)
    (c1 c2 : CFG.cfg dtyp)
    (Hdefs : m_definitions M_host =
               pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c1 |} :: post)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1)) :
    @build_global_environment (@ParamsV IP IPT)
      {| m_name         := m_name M_host;
         m_target       := m_target M_host;
         m_datalayout   := m_datalayout M_host;
         m_type_defs    := m_type_defs M_host;
         m_globals      := m_globals M_host;
         m_declarations := m_declarations M_host;
         m_definitions  :=
           pre ++ {| df_prototype := proto; df_args := fargs; df_instrs := c2 |} :: post |} =
    @build_global_environment (@ParamsV IP IPT) M_host.
  Proof using.
    apply Mem2Reg.build_global_environment_defs_eq.
    - rewrite Hdefs, !map_app; cbn [List.map df_prototype]; reflexivity.
    - rewrite Hdefs, !flat_map_app; cbn [flat_map df_instrs]; rewrite Hba; reflexivity.
  Qed.

  Lemma splice_valid_of_cfg_local_sim
    (fargs : list local_id) (c1 c2 : CFG.cfg dtyp)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1))
    (Hsim : forall env va,
              (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
              cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                env env (denote_cfg c1 va) (denote_cfg c2 va)) :
    splice_valid_defn fargs c1 c2.
  Proof using.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    apply module_defs_cfg_sim_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c1 c2 Hdefs Hba).
    - reflexivity.
    - rewrite Hdefs; cbn [m_definitions].
      assert (Hrefl : forall ds,
                Forall2
                  (fun d1 d2 : definition dtyp (CFG.cfg dtyp) =>
                     df_prototype d2 = df_prototype d1 /\
                     df_args d2 = df_args d1 /\
                     forall env va,
                       (forall x, In x (df_args d1) -> exists v, Maps.lookup x env = Some v) ->
                       cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                         env env (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
                  ds ds).
      { induction ds as [| d rest IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros env va _; apply SCCP.denote_cfg_refl_sim. }
      apply Forall2_app; [apply Hrefl |].
      constructor; [| apply Hrefl].
      exact (conj Logic.eq_refl (conj Logic.eq_refl Hsim)).
  Qed.

  Lemma splice_valid_of_ruttc
    (fargs : list local_id) (c1 c2 : CFG.cfg dtyp)
    (Hba : flat_map block_block_addresses (blks c2) =
           flat_map block_block_addresses (blks c1))
    (Hsim : forall va,
              @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                (denote_cfg c1 va) (denote_cfg c2 va)) :
    splice_valid_defn fargs c1 c2.
  Proof using.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    apply module_defs_ruttc_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c1 c2 Hdefs Hba).
    - reflexivity.
    - rewrite Hdefs; cbn [m_definitions].
      assert (Hrefl : forall ds,
                Forall2
                  (fun d1 d2 : definition dtyp (CFG.cfg dtyp) =>
                     df_prototype d2 = df_prototype d1 /\
                     df_args d2 = df_args d1 /\
                     forall va,
                       @refine_cfg (@ParamsV IP IPT) _ _ Logic.eq
                         (denote_cfg (df_instrs d1) va) (denote_cfg (df_instrs d2) va))
                  ds ds).
      { induction ds as [| d rest IH]; constructor; [| exact IH].
        refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        intros va; apply refine_cfg_refl. }
      apply Forall2_app; [apply Hrefl |].
      constructor; [| apply Hrefl].
      exact (conj Logic.eq_refl (conj Logic.eq_refl Hsim)).
  Qed.

  Lemma slice_body_refines_to_valid_in_any_host
    (fid : function_id) (m_src m_tgt : CFG.mcfg dtyp)
    (Hba : forall df_src df_tgt,
             m_definitions m_src = [df_src] ->
             m_definitions m_tgt = [df_tgt] ->
             flat_map block_block_addresses (blks (df_instrs df_tgt)) =
             flat_map block_block_addresses (blks (df_instrs df_src)))
    (Hbody : slice_body_refines (fid, m_src, m_tgt)) :
    slice_valid_in_any_host (fid, m_src, m_tgt).
  Proof using.
    intros df_src df_tgt Hsrc Htgt.
    exact (splice_valid_of_cfg_local_sim (df_args df_src)
             (df_instrs df_src) (df_instrs df_tgt)
             (Hba df_src df_tgt Hsrc Htgt)
             (Hbody df_src df_tgt Hsrc Htgt)).
  Qed.

  (** Sequential Heterogeneous Module-Merge Refinement Theorem:
      Lifts [check_module_merge] when each verified slice satisfies
      [slice_valid_in_any_host] (covering [cfg_local_sim], [ruttc], AND
      Safe-Path [Pipeline.optimize_mcfg] including [Mem2Reg]). *)
  Theorem check_module_merge_universal_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_valid_in_any_host verified_slices) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    pose proof (check_module_merge_globals_eq m_orig m_merged verified_slices Hchk) as Hglob.
    pose proof (check_module_merge_declarations_eq m_orig m_merged verified_slices Hchk) as Hdecl.
    pose proof (check_module_merge_defs_Forall2 m_orig m_merged verified_slices Hchk) as Hprov.
    assert (Hstep :
      forall pre r_orig r_merged,
        Forall2 (defn_pair_provenance verified_slices) r_orig r_merged ->
        @prog_refines IP IPT
          {| m_name         := m_name m_orig;
             m_target       := m_target m_orig;
             m_datalayout   := m_datalayout m_orig;
             m_type_defs    := m_type_defs m_orig;
             m_globals      := m_globals m_orig;
             m_declarations := m_declarations m_orig;
             m_definitions  := pre ++ r_orig |}
          {| m_name         := m_name m_orig;
             m_target       := m_target m_orig;
             m_datalayout   := m_datalayout m_orig;
             m_type_defs    := m_type_defs m_orig;
             m_globals      := m_globals m_orig;
             m_declarations := m_declarations m_orig;
             m_definitions  := pre ++ r_merged |}).
    { intros pre r_orig; revert pre.
      induction r_orig as [| d1 r1 IH]; intros pre [| d2 r2] HF;
        inversion HF as [| ? ? ? ? (Hpr & Har & Hdisj) HF_tl]; subst.
      - apply prog_refines_refl.
      - destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
        + change (pre ++ d1 :: r1) with ((pre ++ [d1]) ++ r1).
          change (pre ++ d1 :: r2) with ((pre ++ [d1]) ++ r2).
          rewrite !app_assoc; exact (IH (pre ++ [d1]) r2 HF_tl).
        + rewrite Forall_forall in Hslices.
          destruct (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                      (sw_src_defs _ _ _ _ _ _ _ Hsw)
                      (sw_tgt_defs _ _ _ _ _ _ _ Hsw))
            as [_ Hsplice].
          assert (Hd1 :
            d1 = {| df_prototype := df_prototype d1;
                    df_args      := df_args df_src;
                    df_instrs    := df_instrs df_src |}).
          { destruct d1; cbn in *.
            rewrite (sw_src_args _ _ _ _ _ _ _ Hsw), (sw_src_instrs _ _ _ _ _ _ _ Hsw); reflexivity. }
          assert (Hd2 :
            d2 = {| df_prototype := df_prototype d1;
                    df_args      := df_args df_src;
                    df_instrs    := df_instrs df_tgt |}).
          { destruct d2; cbn in *.
            rewrite (sw_src_args _ _ _ _ _ _ _ Hsw), (sw_tgt_instrs _ _ _ _ _ _ _ Hsw),
                    <- Har, <- Hpr; reflexivity. }
          eapply prog_refines_trans.
          * eapply (Hsplice _ pre r1 (df_prototype d1)).
            cbn [m_definitions]; rewrite <- Hd1; reflexivity.
          * cbn [m_name m_target m_datalayout m_type_defs m_globals m_declarations].
            rewrite <- Hd2.
            change (pre ++ d2 :: r1) with ((pre ++ [d2]) ++ r1).
            change (pre ++ d2 :: r2) with ((pre ++ [d2]) ++ r2).
            rewrite !app_assoc; exact (IH (pre ++ [d2]) r2 HF_tl). }
    eapply prog_refines_trans.
    - destruct m_orig; exact (Hstep [] _ _ Hprov).
    - cbn [app]; intros ret_typ entry args U.
      unfold run_mcfg_model, denote_vellvm.
      rewrite <- Hglob, <- Hdecl.
      unfold build_global_environment, mcfg_block_addresses; cbn.
      apply refine_prov_refl.
  Qed.

  (** ** Proof that [Pipeline.optimize_mcfg] on a Safe Single-Function Slice
         Satisfies [slice_valid_in_any_host] (Closing F-20) *)

  (** Single-definition modules have no distinct internal callees, so
      [Inline.inline_mcfg] is an exact syntactic identity. *)
  Lemma match_inlinable_call_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    Inline.match_inlinable_call_instr [df] (dc_name (df_prototype df)) im = None.
  Proof using.
    unfold Inline.match_inlinable_call_instr.
    destruct im as [[iid ins] md].
    destruct ins as [| | [ret_dt fn_e] call_args call_anns obs | | | | | | | |];
      try reflexivity.
    destruct fn_e; try reflexivity.
    destruct id as [callee_gid |]; try reflexivity.
    destruct obs; [| reflexivity].
    cbn [Inline.find_defn_by_gid].
    destruct (raw_id_eqb (dc_name (df_prototype df)) callee_gid); reflexivity.
  Qed.

  Lemma find_call_in_code_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (acc : code dtyp) (cd : code dtyp) :
    Inline.find_call_in_code [df] (dc_name (df_prototype df)) acc cd = None.
  Proof using.
    revert acc; induction cd as [| im rest IH]; intros acc;
      cbn [Inline.find_call_in_code]; [reflexivity |].
    rewrite match_inlinable_call_single_def_none; exact (IH (im :: acc)).
  Qed.

  Lemma find_call_in_blks_single_def_none
    (df : definition dtyp (CFG.cfg dtyp))
    (all_bks acc : ocfg dtyp) (bks : ocfg dtyp) :
    Inline.find_call_in_blks [df] (dc_name (df_prototype df)) all_bks acc bks = None.
  Proof using.
    revert acc; induction bks as [| bk rest IH]; intros acc;
      cbn [Inline.find_call_in_blks]; [reflexivity |].
    destruct (Inline.block_in_cfg_loop all_bks bk); [exact (IH (bk :: acc)) |].
    rewrite find_call_in_code_single_def_none; exact (IH (bk :: acc)).
  Qed.

  Lemma inline_one_site_single_def_id (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    inline_one_site_mcfg M = M.
  Proof using.
    intros Hdefs; unfold inline_one_site_mcfg.
    destruct (Inline.is_hygienic_module M); [| reflexivity].
    rewrite Hdefs; cbn [Inline.inline_first_in_defs].
    destruct (Inline.is_inlinable_caller df); [| reflexivity].
    rewrite find_call_in_blks_single_def_none; reflexivity.
  Qed.

  Lemma inline_mcfg_single_def_id (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    inline_mcfg M = M.
  Proof using.
    intros Hdefs; unfold inline_mcfg.
    assert (Hiter : forall fuel (M0 : CFG.mcfg dtyp),
              m_definitions M0 = [df] -> Inline.inline_iter fuel M0 = M0).
    { induction fuel as [| fuel' IH]; intros M0 HM0; cbn [Inline.inline_iter]; [reflexivity |].
      rewrite (inline_one_site_single_def_id M0 df HM0); exact (IH M0 HM0). }
    exact (Hiter Inline.inline_default_fuel M Hdefs).
  Qed.

  (** Splicing lemmas for [sccp_mcfg], [dce_mcfg], and [simplifycfg_mcfg]. *)
  Lemma map_mcfg_cfg_single_def
    (f : CFG.cfg dtyp -> CFG.cfg dtyp) (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    m_definitions (map_mcfg_cfg f M) =
      [{| df_prototype := df_prototype df;
          df_args      := df_args df;
          df_instrs    := f (df_instrs df) |}].
  Proof using.
    intros Hdefs; unfold map_mcfg_cfg; rewrite Hdefs; reflexivity.
  Qed.

  Lemma map_mcfg_with_args_single_def
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp) (M : CFG.mcfg dtyp)
    (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    m_definitions (map_mcfg_with_args f M) =
      [{| df_prototype := df_prototype df;
          df_args      := df_args df;
          df_instrs    := f (df_args df) (df_instrs df) |}].
  Proof using.
    intros Hdefs; unfold map_mcfg_with_args; rewrite Hdefs; reflexivity.
  Qed.

  Lemma sccp_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SCCP.sccp_cfg fargs c).
  Proof using.
    exact (splice_valid_of_cfg_local_sim fargs c (SCCP.sccp_cfg fargs c)
             (SCCP.sccp_cfg_block_addresses fargs c)
             (SCCP.sccp_cfg_sim fargs c)).
  Qed.

  Lemma dce_cfg_once_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (DCE.dce_cfg_once fargs c).
  Proof using.
    exact (splice_valid_of_cfg_local_sim fargs c (DCE.dce_cfg_once fargs c)
             (DCE.dce_cfg_once_block_addresses fargs c)
             (DCE.dce_cfg_once_sim fargs c)).
  Qed.

  Lemma fold_const_term_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.fold_const_term_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.fold_const_term_cfg c)
             (SimplifyCFG.fold_const_term_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_fold_const c)).
  Qed.

  Lemma elim_unreachable_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.elim_unreachable_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.elim_unreachable_cfg c)
             (SimplifyCFG.elim_unreachable_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_elim_unreachable c)).
  Qed.

  Lemma coalesce_one_cfg_splice_valid (fargs : list local_id) (c : CFG.cfg dtyp) :
    splice_valid_defn fargs c (SimplifyCFG.coalesce_one_cfg c).
  Proof using.
    exact (splice_valid_of_ruttc fargs c (SimplifyCFG.coalesce_one_cfg c)
             (SimplifyCFG.coalesce_one_cfg_block_addresses c)
             (SimplifyCFG.denote_cfg_coalesce_one c)).
  Qed.

  Lemma coalesce_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (SimplifyCFG.coalesce_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (SimplifyCFG.coalesce_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold SimplifyCFG.coalesce_mcfg.
    assert (Hiter :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        exists c',
          m_definitions (SimplifyCFG.coalesce_mcfg_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
          m_declarations (SimplifyCFG.coalesce_mcfg_iter fuel M0) = m_declarations M0 /\
          splice_valid_defn (df_args df) c0 c').
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0; cbn [SimplifyCFG.coalesce_mcfg_iter].
      - exists c0; refine (conj HM0 (conj Logic.eq_refl (splice_valid_defn_refl _ _))).
      - assert (HM1 :
          m_definitions (SimplifyCFG.coalesce_one_mcfg M0) =
            [{| df_prototype := df_prototype df;
                df_args      := df_args df;
                df_instrs    := SimplifyCFG.coalesce_one_cfg c0 |}]).
        { unfold SimplifyCFG.coalesce_one_mcfg, map_mcfg_cfg; rewrite HM0; reflexivity. }
        destruct (IH (SimplifyCFG.coalesce_one_mcfg M0)
                     (SimplifyCFG.coalesce_one_cfg c0) HM1)
          as (c' & Hdefs' & Hdecls' & Hsv').
        exists c'; split; [exact Hdefs' | split; [exact Hdecls' |]].
        exact (splice_valid_defn_trans _ _ _ _ (coalesce_one_cfg_splice_valid _ c0) Hsv'). }
    intros Hdefs; destruct df as [pr ar c0]; exact (Hiter _ M c0 Hdefs).
  Qed.

  Lemma simplifycfg_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (simplifycfg_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (simplifycfg_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    intros Hdefs; unfold simplifycfg_mcfg.
    set (M1 := SimplifyCFG.fold_const_term_mcfg M).
    set (M2 := SimplifyCFG.elim_unreachable_mcfg M1).
    pose proof (map_mcfg_cfg_single_def SimplifyCFG.fold_const_term_cfg M df Hdefs) as HM1.
    pose proof (map_mcfg_cfg_single_def SimplifyCFG.elim_unreachable_cfg M1 _ HM1) as HM2.
    cbn [df_prototype df_args df_instrs] in HM2.
    destruct (coalesce_mcfg_single_def M2 _ HM2) as (c' & HM3 & Hdecl3 & Hsv3).
    cbn [df_prototype df_args df_instrs] in HM3, Hsv3.
    exists c'; split; [exact HM3 | split; [exact Hdecl3 |]].
    eapply splice_valid_defn_trans; [apply fold_const_term_cfg_splice_valid |].
    eapply splice_valid_defn_trans; [apply elim_unreachable_cfg_splice_valid | exact Hsv3].
  Qed.

  Lemma dce_mcfg_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp)) :
    m_definitions M = [df] ->
    exists c',
      m_definitions (dce_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (dce_mcfg M) = m_declarations M /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    intros Hdefs; unfold dce_mcfg.
    pose proof (map_mcfg_with_args_single_def DCE.dce_cfg_once M df Hdefs) as HM1.
    pose proof (map_mcfg_with_args_single_def DCE.dce_cfg_once (dce_mcfg_once M) _ HM1) as HM2.
    pose proof (map_mcfg_with_args_single_def DCE.dce_cfg_once (dce_mcfg_once (dce_mcfg_once M)) _ HM2) as HM3.
    cbn [df_prototype df_args df_instrs] in HM2, HM3.
    eexists; split; [exact HM3 | split; [reflexivity |]].
    eapply splice_valid_defn_trans; [apply dce_cfg_once_splice_valid |].
    eapply splice_valid_defn_trans; [apply dce_cfg_once_splice_valid | apply dce_cfg_once_splice_valid].
  Qed.

  (** ** [Mem2Reg] Leaf-Slice Splicing (Closing F-20)

      In [Mem2Reg], [m2r_module_interproc_safe M] is [false] whenever
      [m_declarations M] is non-empty (which holds for every slice produced by
      [ir-bridge split] from a multi-function module) OR when the slice
      definition contains no [INSTR_Call] instructions (in which case
      [try_promote_slot_in_defn true = try_promote_slot_in_defn false] and
      call-freeness is preserved across [promote_slot_in_cfg]).  In both cases,
      every promotion and dead-alloca step on the slice uses [Mem2Reg]'s
      open-world leaf simulation ([leaf_module_defs_refines]) and splices
      validly into ANY host module! *)

  Definition mm_code_entry_no_call
    (im : instr_id * instr dtyp * list (metadata dtyp)) : bool :=
    match snd (fst im) with
    | INSTR_Call _ _ _ _ => false
    | _ => true
    end.

  Definition mm_defn_no_calls (df : definition dtyp (CFG.cfg dtyp)) : bool :=
    forallb (fun bk => forallb mm_code_entry_no_call (blk_code bk)) (blks (df_instrs df)).

  Definition slice_m2r_safe (M : CFG.mcfg dtyp) : bool :=
    match m_declarations M with
    | _ :: _ => true
    | [] =>
        match m_definitions M with
        | [df] => mm_defn_no_calls df
        | _ => false
        end
    end.

  Lemma check_other_instr_no_call_indep
    (b : bool) (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp)) :
    mm_code_entry_no_call im = true ->
    Mem2Reg.check_other_instr_for_slot b safe_no_p p im =
    Mem2Reg.check_other_instr_for_slot false safe_no_p p im.
  Proof using.
    destruct im as [[iid ins] md]; cbn [mm_code_entry_no_call fst snd].
    destruct ins; try reflexivity; discriminate.
  Qed.

  Lemma forallb_eq_on {A : Type} (f g : A -> bool) (xs : list A)
    (Heq : forall x, In x xs -> f x = g x) :
    forallb f xs = forallb g xs.
  Proof using.
    induction xs as [| x rest IH]; [reflexivity |]; cbn [forallb].
    rewrite (Heq x (or_introl Logic.eq_refl)),
            (IH (fun y Hy => Heq y (or_intror Hy))); reflexivity.
  Qed.

  Lemma find_promotable_no_call_indep_and_inv
    (b : bool) (all_defs all_uses : list raw_id) (safe_locals : list local_id)
    (init_bid : block_id) (bks : ocfg dtyp) (b_init : block dtyp)
    (Hbks : forall bk, In bk bks -> forallb mm_code_entry_no_call (blk_code bk) = true) :
    forall acc rem,
      forallb mm_code_entry_no_call acc = true ->
      forallb mm_code_entry_no_call rem = true ->
      Mem2Reg.find_promotable_in_init_code b all_defs all_uses safe_locals
        init_bid bks b_init acc rem =
      Mem2Reg.find_promotable_in_init_code false all_defs all_uses safe_locals
        init_bid bks b_init acc rem /\
      (forall pre_al al_ins post_al p dt,
         Mem2Reg.find_promotable_in_init_code false all_defs all_uses safe_locals
           init_bid bks b_init acc rem = Some (pre_al, al_ins, post_al, p, dt) ->
         forallb mm_code_entry_no_call pre_al = true /\
         mm_code_entry_no_call al_ins = true /\
         forallb mm_code_entry_no_call post_al = true).
  Proof using.
    intros acc rem; revert acc.
    induction rem as [| im post_al IH]; intros acc Hacc Hrem;
      cbn [Mem2Reg.find_promotable_in_init_code].
    - split; [reflexivity | intros; discriminate].
    - cbn [forallb] in Hrem; apply Bool.andb_true_iff in Hrem as [Him Hpost].
      assert (Hpre : forallb mm_code_entry_no_call (List.rev acc) = true).
      { rewrite forallb_forall in Hacc |- *.
        intros x Hx; apply Hacc; apply in_rev; rewrite rev_involutive; exact Hx. }
      assert (Hcand_eq :
        (let pre_al := List.rev acc in
         match im with
         | (IId p, INSTR_Alloca dt anns_al, md_al) =>
             let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
             if is_scalar_dtyp dt
                && Mem2Reg.is_only_align_anns anns_al
                && Mem2Reg.is_debug_or_file_md md_al
                && Nat.eqb (Mem2Reg.m2r_count_id p all_defs) 1%nat
                && in_raw_ids p all_uses
                && forallb (Mem2Reg.check_other_instr_for_slot b safe_no_p p) pre_al
                && forallb (Mem2Reg.check_code_entry_for_slot b safe_no_p p dt) post_al
                && negb (in_raw_ids p (Mem2Reg.m2r_term_entry_uses (blk_term b_init)))
                && Mem2Reg.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                && forallb
                     (fun bk =>
                        if raw_id_eqb (blk_id bk) init_bid then true
                        else Mem2Reg.check_block_non_entry_for_slot b safe_no_p p dt bk)
                     bks
             then Some (pre_al, im, post_al, p, dt)
             else None
         | _ => None
         end) =
        (let pre_al := List.rev acc in
         match im with
         | (IId p, INSTR_Alloca dt anns_al, md_al) =>
             let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
             if is_scalar_dtyp dt
                && Mem2Reg.is_only_align_anns anns_al
                && Mem2Reg.is_debug_or_file_md md_al
                && Nat.eqb (Mem2Reg.m2r_count_id p all_defs) 1%nat
                && in_raw_ids p all_uses
                && forallb (Mem2Reg.check_other_instr_for_slot false safe_no_p p) pre_al
                && forallb (Mem2Reg.check_code_entry_for_slot false safe_no_p p dt) post_al
                && negb (in_raw_ids p (Mem2Reg.m2r_term_entry_uses (blk_term b_init)))
                && Mem2Reg.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                && forallb
                     (fun bk =>
                        if raw_id_eqb (blk_id bk) init_bid then true
                        else Mem2Reg.check_block_non_entry_for_slot false safe_no_p p dt bk)
                     bks
             then Some (pre_al, im, post_al, p, dt)
             else None
         | _ => None
         end)).
      { cbv zeta; destruct im as [[iid ins] md]; destruct iid; try reflexivity;
          destruct ins as [| | | dt anns_al | | | | | | |]; try reflexivity.
        set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q id)) safe_locals).
        assert (H1 : forallb (Mem2Reg.check_other_instr_for_slot b safe_no_p id) (List.rev acc) =
                     forallb (Mem2Reg.check_other_instr_for_slot false safe_no_p id) (List.rev acc)).
        { apply forallb_eq_on; intros x Hx; apply check_other_instr_no_call_indep.
          rewrite forallb_forall in Hpre; exact (Hpre x Hx). }
        assert (H2 : forall cd,
                       forallb mm_code_entry_no_call cd = true ->
                       forallb (Mem2Reg.check_code_entry_for_slot b safe_no_p id dt) cd =
                       forallb (Mem2Reg.check_code_entry_for_slot false safe_no_p id dt) cd).
        { intros cd Hcd; apply forallb_eq_on; intros x Hx.
          unfold Mem2Reg.check_code_entry_for_slot.
          destruct (Mem2Reg.is_promotable_load_of id dt x); [reflexivity |].
          destruct (Mem2Reg.is_promotable_store_of id dt x); [reflexivity |].
          apply check_other_instr_no_call_indep.
          rewrite forallb_forall in Hcd; exact (Hcd x Hx). }
        assert (H3 : forallb
                       (fun bk =>
                          if raw_id_eqb (blk_id bk) init_bid then true
                          else Mem2Reg.check_block_non_entry_for_slot b safe_no_p id dt bk) bks =
                     forallb
                       (fun bk =>
                          if raw_id_eqb (blk_id bk) init_bid then true
                          else Mem2Reg.check_block_non_entry_for_slot false safe_no_p id dt bk) bks).
        { apply forallb_eq_on; intros bk Hbk.
          destruct (raw_id_eqb (blk_id bk) init_bid); [reflexivity |].
          unfold Mem2Reg.check_block_non_entry_for_slot.
          rewrite (H2 (blk_code bk) (Hbks bk Hbk)); reflexivity. }
        rewrite H1, (H2 post_al Hpost), H3; reflexivity. }
      rewrite Hcand_eq.
      assert (Hacc' : forallb mm_code_entry_no_call (im :: acc) = true)
        by (cbn [forallb]; rewrite Him, Hacc; reflexivity).
      destruct (IH (im :: acc) Hacc' Hpost) as [Heq_rec Hinv_rec].
      set (cand0 :=
             match im with
             | (IId p, INSTR_Alloca dt anns_al, md_al) =>
                 let safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals in
                 if is_scalar_dtyp dt
                    && Mem2Reg.is_only_align_anns anns_al
                    && Mem2Reg.is_debug_or_file_md md_al
                    && Nat.eqb (Mem2Reg.m2r_count_id p all_defs) 1%nat
                    && in_raw_ids p all_uses
                    && forallb (Mem2Reg.check_other_instr_for_slot false safe_no_p p) (List.rev acc)
                    && forallb (Mem2Reg.check_code_entry_for_slot false safe_no_p p dt) post_al
                    && negb (in_raw_ids p (Mem2Reg.m2r_term_entry_uses (blk_term b_init)))
                    && Mem2Reg.m2r_non_invoke_term (snd (fst (blk_term b_init)))
                    && forallb
                         (fun bk =>
                            if raw_id_eqb (blk_id bk) init_bid then true
                            else Mem2Reg.check_block_non_entry_for_slot false safe_no_p p dt bk)
                         bks
                 then Some (List.rev acc, im, post_al, p, dt)
                 else None
             | _ => None
             end).
      destruct cand0 as [[[[[pa ai] po] p0] dt0] |] eqn:Ecand.
      + split; [reflexivity |].
        intros pre_al al_ins post_al0 p dt Hsome; injection Hsome as <- <- <- <- <-.
        unfold cand0 in Ecand.
        destruct im as [[iid ins] md]; try discriminate Ecand;
          destruct iid; try discriminate Ecand;
          destruct ins; try discriminate Ecand.
        destruct (is_scalar_dtyp _ && _ && _ && _ && _ && _ && _ && _ && _ && _);
          [injection Ecand as <- <- <- _ _; exact (conj Hpre (conj Him Hpost))
          | discriminate Ecand].
      + split; [exact Heq_rec | exact Hinv_rec].
  Qed.

  Lemma rewrite_code_for_slot_no_call
    (p : local_id) (dt : dtyp) :
    forall cur_reg avoid cd cd' end_r avoid',
      forallb mm_code_entry_no_call cd = true ->
      Mem2Reg.rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_r, avoid') ->
      forallb mm_code_entry_no_call cd' = true.
  Proof using.
    intros cur_reg avoid cd; revert cur_reg avoid.
    induction cd as [| im rest IH]; intros cur_reg avoid cd' end_r avoid' Hnc Hrw;
      cbn [Mem2Reg.rewrite_code_for_slot] in Hrw.
    - injection Hrw as <- _ _; reflexivity.
    - cbn [forallb] in Hnc; apply Bool.andb_true_iff in Hnc as [Him Hrest].
      destruct (Mem2Reg.is_promotable_load_of p dt im) as [dst |].
      + destruct (Mem2Reg.rewrite_code_for_slot p dt cur_reg avoid rest) as [[r' er] av'] eqn:Er.
        injection Hrw as <- _ _; cbn [forallb mm_code_entry_no_call fst snd].
        exact (IH cur_reg avoid r' er av' Hrest Er).
      + destruct (Mem2Reg.is_promotable_store_of p dt im) as [val_e |].
        * set (st_reg := PassCommon.fresh_name "m2r_st"%string avoid) in *.
          destruct (Mem2Reg.rewrite_code_for_slot p dt st_reg (st_reg :: avoid) rest)
            as [[r' er] av'] eqn:Er.
          injection Hrw as <- _ _; cbn [forallb mm_code_entry_no_call fst snd].
          exact (IH st_reg (st_reg :: avoid) r' er av' Hrest Er).
        * destruct (Mem2Reg.rewrite_code_for_slot p dt cur_reg avoid rest) as [[r' er] av'] eqn:Er.
          injection Hrw as <- _ _; cbn [forallb]; rewrite Him.
          exact (IH cur_reg avoid r' er av' Hrest Er).
  Qed.

  Lemma pass1_no_call
    (init_bid : block_id) (p : local_id) (dt : dtyp)
    (init_end_reg : local_id) (init_code' : code dtyp)
    (Hinit_nc : forallb mm_code_entry_no_call init_code' = true) :
    forall avoid bk_phis pass1_out avoid',
      (forall bk pr, In (bk, pr) bk_phis -> forallb mm_code_entry_no_call (blk_code bk) = true) ->
      Mem2Reg.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid bk_phis =
        (pass1_out, avoid') ->
      forall bk pr cd' er,
        In (bk, pr, cd', er) pass1_out ->
        forallb mm_code_entry_no_call cd' = true.
  Proof using.
    intros avoid bk_phis; revert avoid.
    induction bk_phis as [| [bk0 pr0] rest IH];
      intros avoid pass1_out avoid' Hbk Hrw bk pr cd' er Hin;
      cbn [Mem2Reg.rewrite_non_entry_blocks_pass1] in Hrw.
    - injection Hrw as <- _; contradiction.
    - destruct (raw_id_eqb (blk_id bk0) init_bid).
      + destruct (Mem2Reg.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' avoid rest)
          as [ro av'] eqn:Er.
        injection Hrw as <- _; destruct Hin as [Heq | Hin].
        * injection Heq as _ _ <- _; exact Hinit_nc.
        * exact (IH avoid ro av' (fun b q H => Hbk b q (or_intror H)) Er bk pr cd' er Hin).
      + destruct (Mem2Reg.rewrite_code_for_slot p dt pr0 avoid (blk_code bk0))
          as [[cd0 er0] av1] eqn:Ecd0.
        destruct (Mem2Reg.rewrite_non_entry_blocks_pass1 init_bid p dt init_end_reg init_code' av1 rest)
          as [ro av2] eqn:Er.
        injection Hrw as <- _; destruct Hin as [Heq | Hin].
        * injection Heq as _ _ <- _.
          exact (rewrite_code_for_slot_no_call p dt pr0 avoid (blk_code bk0) cd0 er0 av1
                   (Hbk bk0 pr0 (or_introl Logic.eq_refl)) Ecd0).
        * exact (IH av1 ro av2 (fun b q H => Hbk b q (or_intror H)) Er bk pr cd' er Hin).
  Qed.

  Lemma try_promote_slot_no_calls_indep_and_pres
    (b : bool) (df : definition dtyp (CFG.cfg dtyp)) :
    mm_defn_no_calls df = true ->
    Mem2Reg.try_promote_slot_in_defn b df = Mem2Reg.try_promote_slot_in_defn false df /\
    (forall df',
       Mem2Reg.try_promote_slot_in_defn false df = Some df' ->
       mm_defn_no_calls df' = true).
  Proof using.
    intros Hnc; unfold mm_defn_no_calls in Hnc.
    rewrite forallb_forall in Hnc.
    unfold Mem2Reg.try_promote_slot_in_defn; cbv zeta.
    destruct (Mem2Reg.m2r_nodup_ids _ && _ && _); [| split; [reflexivity | discriminate]].
    destruct (find_block (blks (df_instrs df)) (init (df_instrs df))) as [b_init |] eqn:Efb;
      [| split; [reflexivity | discriminate]].
    assert (Hin_init : In b_init (blks (df_instrs df)))
      by (eapply ScopeTheory.find_block_In'; exact Efb).
    destruct (Mem2Reg.m2r_is_empty (blk_phis b_init)); [| split; [reflexivity | discriminate]].
    destruct (find_promotable_no_call_indep_and_inv b
                (df_args df ++ flat_map PassCommon.full_block_defs (blks (df_instrs df)))
                (flat_map PassCommon.full_block_uses (blks (df_instrs df)))
                (Mem2Reg.m2r_collect_unique_allocas
                   (df_args df ++ flat_map PassCommon.full_block_defs (blks (df_instrs df)))
                   (blks (df_instrs df)))
                (init (df_instrs df)) (blks (df_instrs df)) b_init Hnc
                [] (blk_code b_init) Logic.eq_refl (Hnc b_init Hin_init))
      as [Hfind_eq Hfind_inv].
    rewrite Hfind_eq.
    destruct (Mem2Reg.find_promotable_in_init_code false _ _ _ _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Ef0;
      [| split; [reflexivity | discriminate]].
    split; [reflexivity |].
    intros df' Hsome; injection Hsome as <-.
    destruct (Hfind_inv pre_al al_ins post_al p dt Logic.eq_refl) as (Hpre & Hal & Hpost).
    unfold mm_defn_no_calls, Mem2Reg.promote_slot_in_cfg; cbn [df_instrs blks]; cbv zeta.
    set (c := df_instrs df).
    set (avoid0 := df_args df ++ PassCommon.cfg_all_ids c).
    set (init_reg := PassCommon.fresh_name "m2r_init"%string avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := PassCommon.fresh_names "m2r_phi"%string (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (Mem2Reg.rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    pose proof (rewrite_code_for_slot_no_call p dt init_reg avoid2 post_al
                  post_al' init_end_reg avoid3 Hpost Erw_post) as Hpost'.
    set (init_op := (IId init_reg, INSTR_Op (PassCommon.mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
                     ([] : list (metadata dtyp)))).
    set (init_code' := pre_al ++ al_ins :: init_op :: post_al').
    assert (Hinit_nc : forallb mm_code_entry_no_call init_code' = true).
    { unfold init_code'; rewrite forallb_app; cbn [forallb].
      rewrite Hpre, Hal, Hpost'; reflexivity. }
    destruct (Mem2Reg.rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code'
                avoid3 (List.combine (blks c) phi_regs))
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hcomb : forall bk pr, In (bk, pr) (List.combine (blks c) phi_regs) ->
                                  forallb mm_code_entry_no_call (blk_code bk) = true).
    { intros bk pr Hin; apply in_combine_l in Hin; exact (Hnc bk Hin). }
    pose proof (pass1_no_call (init c) p dt init_end_reg init_code' Hinit_nc
                  avoid3 _ pass1_out avoid_out Hcomb Epass1) as Hp1.
    unfold Mem2Reg.build_promoted_blocks; apply forallb_forall.
    intros bk_out Hbk_out; apply in_map_iff in Hbk_out as [[[[bk pr] cd'] er] [<- Hin_p1]].
    destruct (raw_id_eqb (blk_id bk) (init c)); cbn [blk_code]; exact (Hp1 bk pr cd' er Hin_p1).
  Qed.

  Lemma try_promote_slot_proto_indep
    (proto1 proto2 : declaration dtyp)
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (df' : definition dtyp (CFG.cfg dtyp)) :
    Mem2Reg.try_promote_slot_in_defn false
      {| df_prototype := proto1; df_args := fargs; df_instrs := c |} = Some df' ->
    df_args df' = fargs /\
    Mem2Reg.try_promote_slot_in_defn false
      {| df_prototype := proto2; df_args := fargs; df_instrs := c |} =
      Some {| df_prototype := proto2; df_args := fargs; df_instrs := df_instrs df' |}.
  Proof using.
    unfold Mem2Reg.try_promote_slot_in_defn; cbn [df_args df_instrs df_prototype].
    destruct (Mem2Reg.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks c) (init c)) as [b_init |]; [| discriminate].
    destruct (Mem2Reg.m2r_is_empty (blk_phis b_init)); [| discriminate].
    destruct (Mem2Reg.find_promotable_in_init_code false _ _ _ _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |]; [| discriminate].
    intros H; injection H as <-; cbn; split; reflexivity.
  Qed.

  Lemma try_elim_dead_alloca_proto_indep
    (proto1 proto2 : declaration dtyp)
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (df' : definition dtyp (CFG.cfg dtyp)) :
    Mem2Reg.try_elim_dead_alloca_in_defn
      {| df_prototype := proto1; df_args := fargs; df_instrs := c |} = Some df' ->
    df_args df' = fargs /\
    Mem2Reg.try_elim_dead_alloca_in_defn
      {| df_prototype := proto2; df_args := fargs; df_instrs := c |} =
      Some {| df_prototype := proto2; df_args := fargs; df_instrs := df_instrs df' |}.
  Proof using.
    unfold Mem2Reg.try_elim_dead_alloca_in_defn; cbn [df_args df_instrs df_prototype].
    destruct (Mem2Reg.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks c) (init c)) as [b_init |]; [| discriminate].
    destruct (Mem2Reg.m2r_is_empty _ && _); [| discriminate].
    destruct (Mem2Reg.find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |]; [| discriminate].
    destruct (forallb _ (blks c)); [| discriminate].
    intros H; injection H as <-; cbn; split; reflexivity.
  Qed.

  Lemma try_elim_dead_alloca_no_calls_pres
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    mm_defn_no_calls df = true ->
    Mem2Reg.try_elim_dead_alloca_in_defn df = Some df' ->
    mm_defn_no_calls df' = true.
  Proof using.
    intros Hnc; unfold mm_defn_no_calls in Hnc; rewrite forallb_forall in Hnc.
    unfold Mem2Reg.try_elim_dead_alloca_in_defn; cbv zeta.
    destruct (Mem2Reg.m2r_nodup_ids _ && _ && _); [| discriminate].
    destruct (find_block (blks (df_instrs df)) (init (df_instrs df))) as [b_init |] eqn:Efb;
      [| discriminate].
    assert (Hin_init : In b_init (blks (df_instrs df)))
      by (eapply ScopeTheory.find_block_In'; exact Efb).
    destruct (Mem2Reg.m2r_is_empty _ && _); [| discriminate].
    destruct (Mem2Reg.find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Etr; [| discriminate].
    pose proof (Mem2Reg.find_trailing_dead_alloca_in_code_inv _ _ _ [] (blk_code b_init)
                  pre_al al_ins post_al p dt Etr) as Hsplit.
    cbv zeta in Hsplit; cbn [List.rev app] in Hsplit.
    destruct Hsplit as (Hcode_eq & _).
    destruct (forallb _ (blks (df_instrs df))); [| discriminate].
    intros Hsome; injection Hsome as <-.
    unfold mm_defn_no_calls; cbn [df_instrs blks]; apply forallb_forall.
    intros bk' Hbk'; apply in_map_iff in Hbk' as [bk [<- Hin_bk]].
    destruct (raw_id_eqb (blk_id bk) (init (df_instrs df))); [| exact (Hnc bk Hin_bk)].
    cbn [blk_code]; pose proof (Hnc b_init Hin_init) as Hb0.
    rewrite Hcode_eq, forallb_app in Hb0; cbn [forallb] in Hb0.
    rewrite !Bool.andb_true_iff in Hb0; destruct Hb0 as [Hpre [_ Hpost]].
    rewrite forallb_app, Hpre, Hpost; reflexivity.
  Qed.

  Lemma splice_valid_of_try_promote_leaf
    (proto0 : declaration dtyp) (fargs : list local_id)
    (c : CFG.cfg dtyp) (df' : definition dtyp (CFG.cfg dtyp))
    (Etry : Mem2Reg.try_promote_slot_in_defn false
              {| df_prototype := proto0; df_args := fargs; df_instrs := c |} = Some df') :
    splice_valid_defn fargs c (df_instrs df').
  Proof using.
    destruct (Mem2Reg.promote_slot_in_defn_block_addresses false
                {| df_prototype := proto0; df_args := fargs; df_instrs := c |} df' Etry)
      as [_ Hba]; cbn [df_instrs] in Hba.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    destruct (try_promote_slot_proto_indep proto0 proto fargs c df' Etry) as [_ Etry_host].
    apply Mem2Reg.leaf_module_defs_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c (df_instrs df') Hdefs Hba).
    - reflexivity.
    - intros P0 g0 Hg0; rewrite Hdefs; cbn [m_definitions].
      apply Forall2_app; [apply Mem2Reg.leaf_ctx_fn_rel_refl_list |].
      constructor; [| apply Mem2Reg.leaf_ctx_fn_rel_refl_list].
      split; [reflexivity |].
      exact (Mem2Reg.try_promote_slot_leaf_denote_function_sim P0 g0 _ _ Hg0 Etry_host).
  Qed.

  Lemma splice_valid_of_try_elim_dead_alloca {IPWB : IPtrWellBehaved IP}
    (proto0 : declaration dtyp) (fargs : list local_id)
    (c : CFG.cfg dtyp) (df' : definition dtyp (CFG.cfg dtyp))
    (Etry : Mem2Reg.try_elim_dead_alloca_in_defn
              {| df_prototype := proto0; df_args := fargs; df_instrs := c |} = Some df') :
    splice_valid_defn fargs c (df_instrs df').
  Proof using.
    destruct (Mem2Reg.elim_dead_alloca_in_defn_block_addresses
                {| df_prototype := proto0; df_args := fargs; df_instrs := c |} df' Etry)
      as [_ Hba]; cbn [df_instrs] in Hba.
    split; [exact Hba |].
    intros M_host pre post proto Hdefs.
    destruct (try_elim_dead_alloca_proto_indep proto0 proto fargs c df' Etry) as [_ Etry_host].
    apply Mem2Reg.leaf_module_defs_refines.
    - exact (build_global_env_splice_eq M_host pre post proto fargs c (df_instrs df') Hdefs Hba).
    - reflexivity.
    - intros P0 g0 Hg0; rewrite Hdefs; cbn [m_definitions].
      apply Forall2_app; [apply Mem2Reg.leaf_ctx_fn_rel_refl_list |].
      constructor; [| apply Mem2Reg.leaf_ctx_fn_rel_refl_list].
      split; [reflexivity |].
      exact (Mem2Reg.try_elim_dead_alloca_denote_function_sim P0 g0 _ _ Hg0 Etry_host).
  Qed.

  Lemma promote_slot_step_safe_single_def
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (Mem2Reg.promote_slot_step_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (Mem2Reg.promote_slot_step_mcfg M) = m_declarations M /\
      slice_m2r_safe (Mem2Reg.promote_slot_step_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold Mem2Reg.promote_slot_step_mcfg.
    destruct (PassCommon.mcfg_no_inttoptr M);
      [| exists (df_instrs df); destruct df;
         exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _))))].
    assert (Heq_try :
      Mem2Reg.try_promote_slot_in_defn (Mem2Reg.m2r_module_interproc_safe M) df =
      Mem2Reg.try_promote_slot_in_defn false df).
    { unfold slice_m2r_safe in Hsafe.
      destruct (m_declarations M) as [| decl0 rest_d] eqn:Edecl.
      - rewrite Hdefs in Hsafe.
        exact (proj1 (try_promote_slot_no_calls_indep_and_pres _ df Hsafe)).
      - unfold Mem2Reg.m2r_module_interproc_safe; rewrite Edecl, Bool.andb_false_r; cbn [andb]; reflexivity. }
    rewrite Hdefs; cbn [Mem2Reg.promote_first_in_defs]; rewrite Heq_try.
    destruct (Mem2Reg.try_promote_slot_in_defn false df) as [df' |] eqn:Etry.
    - destruct df as [pr ar c0].
      destruct (try_promote_slot_proto_indep pr pr ar c0 df' Etry) as [Har' Etry'].
      destruct (Mem2Reg.promote_slot_in_defn_block_addresses false _ df' Etry) as [Hpr' _].
      cbn [df_prototype df_args df_instrs] in *.
      assert (Hdf' : df' = {| df_prototype := pr; df_args := ar; df_instrs := df_instrs df' |})
        by (destruct df'; cbn in *; congruence).
      exists (df_instrs df'); rewrite <- Hdf'.
      refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ _))).
      + unfold slice_m2r_safe in Hsafe |- *; cbn [m_declarations m_definitions].
        destruct (m_declarations M); [| reflexivity].
        rewrite Hdefs in Hsafe.
        exact (proj2 (try_promote_slot_no_calls_indep_and_pres false _ Hsafe) df' Etry).
      + exact (splice_valid_of_try_promote_leaf pr ar c0 df' Etry).
    - cbn [option_map]; exists (df_instrs df); destruct df as [pr ar c0].
      exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _)))).
  Qed.

  Lemma elim_dead_alloca_step_safe_single_def {IPWB : IPtrWellBehaved IP}
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (Mem2Reg.elim_dead_alloca_step_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (Mem2Reg.elim_dead_alloca_step_mcfg M) = m_declarations M /\
      slice_m2r_safe (Mem2Reg.elim_dead_alloca_step_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold Mem2Reg.elim_dead_alloca_step_mcfg.
    destruct (PassCommon.mcfg_no_inttoptr M);
      [| exists (df_instrs df); destruct df;
         exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _))))].
    rewrite Hdefs; cbn [Mem2Reg.elim_first_dead_alloca_in_defs].
    destruct (Mem2Reg.try_elim_dead_alloca_in_defn df) as [df' |] eqn:Etry.
    - destruct df as [pr ar c0].
      destruct (try_elim_dead_alloca_proto_indep pr pr ar c0 df' Etry) as [Har' _].
      destruct (Mem2Reg.elim_dead_alloca_in_defn_block_addresses _ df' Etry) as [Hpr' _].
      cbn [df_prototype df_args df_instrs] in *.
      assert (Hdf' : df' = {| df_prototype := pr; df_args := ar; df_instrs := df_instrs df' |})
        by (destruct df'; cbn in *; congruence).
      exists (df_instrs df'); rewrite <- Hdf'.
      refine (conj Logic.eq_refl (conj Logic.eq_refl (conj _ _))).
      + unfold slice_m2r_safe in Hsafe |- *; cbn [m_declarations m_definitions].
        destruct (m_declarations M); [| reflexivity].
        rewrite Hdefs in Hsafe.
        exact (try_elim_dead_alloca_no_calls_pres _ df' Hsafe Etry).
      + exact (splice_valid_of_try_elim_dead_alloca pr ar c0 df' Etry).
    - cbn [option_map]; exists (df_instrs df); destruct df as [pr ar c0].
      exact (conj Hdefs (conj Logic.eq_refl (conj Hsafe (splice_valid_defn_refl _ _)))).
  Qed.

  Lemma mem2reg_mcfg_safe_single_def {IPWB : IPtrWellBehaved IP}
    (M : CFG.mcfg dtyp) (df : definition dtyp (CFG.cfg dtyp))
    (Hdefs : m_definitions M = [df])
    (Hsafe : slice_m2r_safe M = true) :
    exists c',
      m_definitions (mem2reg_mcfg M) =
        [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c' |}] /\
      m_declarations (mem2reg_mcfg M) = m_declarations M /\
      slice_m2r_safe (mem2reg_mcfg M) = true /\
      splice_valid_defn (df_args df) (df_instrs df) c'.
  Proof using.
    unfold mem2reg_mcfg.
    assert (Hprom :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        slice_m2r_safe M0 = true ->
        exists c1,
          m_definitions (Mem2Reg.promote_slot_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c1 |}] /\
          m_declarations (Mem2Reg.promote_slot_iter fuel M0) = m_declarations M0 /\
          slice_m2r_safe (Mem2Reg.promote_slot_iter fuel M0) = true /\
          splice_valid_defn (df_args df) c0 c1).
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0 Hs0; cbn [Mem2Reg.promote_slot_iter].
      - exists c0; exact (conj HM0 (conj Logic.eq_refl (conj Hs0 (splice_valid_defn_refl _ _)))).
      - destruct (promote_slot_step_safe_single_def M0 _ HM0 Hs0)
          as (c_mid & HM1 & Hd1 & Hs1 & Hsv1).
        cbn [df_prototype df_args df_instrs] in *.
        destruct (IH _ c_mid HM1 Hs1) as (c1 & HM2 & Hd2 & Hs2 & Hsv2).
        exists c1; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
        exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2). }
    assert (Helim :
      forall fuel (M0 : CFG.mcfg dtyp) (c0 : CFG.cfg dtyp),
        m_definitions M0 =
          [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c0 |}] ->
        slice_m2r_safe M0 = true ->
        exists c1,
          m_definitions (Mem2Reg.elim_dead_alloca_iter fuel M0) =
            [{| df_prototype := df_prototype df; df_args := df_args df; df_instrs := c1 |}] /\
          m_declarations (Mem2Reg.elim_dead_alloca_iter fuel M0) = m_declarations M0 /\
          slice_m2r_safe (Mem2Reg.elim_dead_alloca_iter fuel M0) = true /\
          splice_valid_defn (df_args df) c0 c1).
    { induction fuel as [| fuel' IH]; intros M0 c0 HM0 Hs0; cbn [Mem2Reg.elim_dead_alloca_iter].
      - exists c0; exact (conj HM0 (conj Logic.eq_refl (conj Hs0 (splice_valid_defn_refl _ _)))).
      - destruct (elim_dead_alloca_step_safe_single_def M0 _ HM0 Hs0)
          as (c_mid & HM1 & Hd1 & Hs1 & Hsv1).
        cbn [df_prototype df_args df_instrs] in *.
        destruct (IH _ c_mid HM1 Hs1) as (c1 & HM2 & Hd2 & Hs2 & Hsv2).
        exists c1; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
        exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2). }
    destruct df as [pr ar c0].
    destruct (Hprom Mem2Reg.mem2reg_default_fuel M c0 Hdefs Hsafe)
      as (c1 & HM1 & Hd1 & Hs1 & Hsv1).
    destruct (Helim Mem2Reg.mem2reg_default_fuel _ c1 HM1 Hs1)
      as (c2 & HM2 & Hd2 & Hs2 & Hsv2).
    exists c2; refine (conj HM2 (conj (eq_trans Hd2 Hd1) (conj Hs2 _))).
    exact (splice_valid_defn_trans _ _ _ _ Hsv1 Hsv2).
  Qed.

  (** Full 7-stage [Pipeline.optimize_mcfg] slice theorem (F-20):
      When [m_slice_src] has a single definition and either has non-empty
      [m_declarations] (as emitted by [ir-bridge split] for any multi-function
      module) or is a call-free leaf, [(fid, m_slice_src, optimize_mcfg m_slice_src)]
      splices validly into ANY host module [m_orig]! *)
  Theorem optimize_mcfg_slice_valid {IPWB : IPtrWellBehaved IP}
    (fid : function_id) (m_slice_src : CFG.mcfg dtyp)
    (Hsafe : slice_m2r_safe m_slice_src = true) :
    slice_valid_in_any_host (fid, m_slice_src, optimize_mcfg m_slice_src).
  Proof using.
    intros df_src df_tgt Hsrc Htgt.
    unfold optimize_mcfg in Htgt.
    destruct (mem2reg_mcfg_safe_single_def m_slice_src df_src Hsrc Hsafe)
      as (c1 & HM1 & Hd1 & Hs1 & Hsv1).
    rewrite (inline_mcfg_single_def_id (mem2reg_mcfg m_slice_src) _ HM1) in Htgt.
    destruct (mem2reg_mcfg_safe_single_def (mem2reg_mcfg m_slice_src) _ HM1 Hs1)
      as (c2 & HM2 & _ & _ & Hsv2).
    cbn [df_prototype df_args df_instrs] in HM2, Hsv2.
    pose proof (map_mcfg_with_args_single_def SCCP.sccp_cfg _ _ HM2) as HM3.
    cbn [df_prototype df_args df_instrs] in HM3.
    destruct (simplifycfg_mcfg_single_def _ _ HM3) as (c4 & HM4 & _ & Hsv4).
    cbn [df_prototype df_args df_instrs] in HM4, Hsv4.
    destruct (dce_mcfg_single_def _ _ HM4) as (c5 & HM5 & _ & Hsv5).
    cbn [df_prototype df_args df_instrs] in HM5, Hsv5.
    destruct (simplifycfg_mcfg_single_def _ _ HM5) as (c6 & HM6 & _ & Hsv6).
    cbn [df_prototype df_args df_instrs] in HM6, Hsv6.
    rewrite HM6 in Htgt; injection Htgt as <-; cbn [df_instrs].
    eapply splice_valid_defn_trans; [exact Hsv1 |].
    eapply splice_valid_defn_trans; [exact Hsv2 |].
    eapply splice_valid_defn_trans; [apply sccp_cfg_splice_valid |].
    eapply splice_valid_defn_trans; [exact Hsv4 |].
    eapply splice_valid_defn_trans; [exact Hsv5 | exact Hsv6].
  Qed.

End SafePathSlices.

Theorem check_module_merge_universal_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hchk : check_module_merge m_orig m_merged verified_slices = true)
  (Hslices : Forall (@slice_valid_in_any_host IPZ IPZTheory) verified_slices)
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (@check_module_merge_universal_refines IPZ IPZTheory m_orig m_merged
             verified_slices Hchk Hslices).
  - exact (I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.


(** * 6. Parser [METADATA_File_info] Normalization for Multi-File CLI Validation *)

Definition keep_non_file_info_md (m : metadata dtyp) : bool :=
  match m with
  | METADATA_File_info _ => false
  | _ => true
  end.

Definition strip_file_info_mds (mds : list (metadata dtyp)) : list (metadata dtyp) :=
  List.filter keep_non_file_info_md mds.

Definition strip_file_info_block (bk : block dtyp) : block dtyp :=
  {| blk_id       := blk_id bk;
     blk_phis     := List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) (blk_phis bk);
     blk_code     := List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) (blk_code bk);
     blk_term     := let '(iid, tm, md) := blk_term bk in (iid, tm, strip_file_info_mds md);
     blk_comments := blk_comments bk |}.

Definition strip_file_info_cfg (c : CFG.cfg dtyp) : CFG.cfg dtyp :=
  {| init := init c;
     blks := List.map strip_file_info_block (blks c);
     args := args c |}.

Definition strip_file_info_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_cfg strip_file_info_cfg M.

Definition check_module_merge_parsed
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) : bool :=
  check_module_merge
    (strip_file_info_mcfg m_orig)
    (strip_file_info_mcfg m_merged)
    (List.map
       (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
       verified_slices).

Definition validate_module_merge_parsed
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  : string + unit :=
  validate_module_merge
    (strip_file_info_mcfg m_orig)
    (strip_file_info_mcfg m_merged)
    (List.map
       (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
       verified_slices).

Lemma strip_file_info_mds_idem (mds : list (metadata dtyp)) :
  strip_file_info_mds (strip_file_info_mds mds) = strip_file_info_mds mds.
Proof.
  induction mds as [| m rest IH]; [reflexivity |]; cbn [strip_file_info_mds List.filter].
  destruct (keep_non_file_info_md m) eqn:Ek; [cbn [List.filter]; rewrite Ek, IH; reflexivity | exact IH].
Qed.

Lemma find_option_filter_none {A B : Type}
  (f : A -> option B) (p : A -> bool) (xs : list A)
  (Hnone : forall x, p x = false -> f x = None) :
  find_option f (List.filter p xs) = find_option f xs.
Proof.
  induction xs as [| x rest IH]; [reflexivity |]; cbn [List.filter find_option].
  destruct (p x) eqn:Ep.
  - cbn [find_option]; destruct (f x); [reflexivity | exact IH].
  - rewrite (Hnone x Ep); exact IH.
Qed.

Lemma load_metadata_attrs_strip (mds : list (metadata dtyp)) :
  load_metadata_attrs (strip_file_info_mds mds) = load_metadata_attrs mds.
Proof.
  unfold load_metadata_attrs, strip_file_info_mds.
  induction mds as [| m rest IH]; [reflexivity |]; cbn [List.filter flat_map].
  destruct m; cbn [keep_non_file_info_md flat_map load_metadata_attr];
    try (rewrite IH; reflexivity); exact IH.
Qed.

Lemma metadata_range_strip (mds : list (metadata dtyp)) :
  metadata_range (strip_file_info_mds mds) = metadata_range mds.
Proof.
  unfold metadata_range, strip_file_info_mds.
  apply find_option_filter_none; intros m Hm; destruct m; try discriminate Hm; reflexivity.
Qed.

Lemma load_metadata_dereferenceable_strip (mds : list (metadata dtyp)) :
  load_metadata_dereferenceable (strip_file_info_mds mds) = load_metadata_dereferenceable mds.
Proof.
  unfold load_metadata_dereferenceable, strip_file_info_mds.
  apply find_option_filter_none; intros m Hm; destruct m; try discriminate Hm; reflexivity.
Qed.

Lemma strip_file_info_cfg_block_addresses (c : CFG.cfg dtyp) :
  flat_map block_block_addresses (blks (strip_file_info_cfg c)) =
  flat_map block_block_addresses (blks c).
Proof.
  unfold strip_file_info_cfg; cbn [blks].
  induction (blks c) as [| bk rest IH]; [reflexivity |]; cbn [List.map flat_map].
  rewrite IH; f_equal.
  unfold block_block_addresses, strip_file_info_block; cbn [blk_phis blk_code blk_term].
  assert (Hph : forall ps : list (local_id * phi dtyp * list (metadata dtyp)),
            flat_map (fun '(_, p, _) => phi_block_addresses p)
              (List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps) =
            flat_map (fun '(_, p, _) => phi_block_addresses p) ps).
  { induction ps as [| [[id p] md] rp IHp]; [reflexivity | cbn; rewrite IHp; reflexivity]. }
  assert (Hcd : forall cd : code dtyp,
            flat_map (fun '(_, i, _) => instr_block_addresses i)
              (List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd) =
            flat_map (fun '(_, i, _) => instr_block_addresses i) cd).
  { induction cd as [| [[iid ins] md] rc IHc]; [reflexivity | cbn; rewrite IHc; reflexivity]. }
  rewrite Hph, Hcd; destruct (blk_term bk) as [[iid tm] md]; reflexivity.
Qed.

Section StripFileInfoRefinement.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).

  Lemma refine_cfg_raise_any {A : Type} (s1 s2 : string) :
    @refine_cfg PaV A A Logic.eq (raise s1) (raise s2).
  Proof using.
    unfold raise, trigger_cast; eapply ruttc_trigger';
      [cbn; unfold resum, ReSum_id, id_, Id_IFun; exact I | intros [] [] _].
  Qed.

  Lemma refine_cfg_raiseUB_any {A : Type} (s1 s2 : string) :
    @refine_cfg PaV A A Logic.eq (raiseUB s1) (raiseUB s2).
  Proof using.
    unfold raiseUB, trigger_cast; apply ruttc_trigger_cutl; constructor.
  Qed.

  Lemma refine_cfg_assert_alignment_msg
    (a : @dvalue PaV) (anns : list (annotation dtyp)) (m1 m2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (EOU_to_itree (assert_alignment a anns m1))
      (EOU_to_itree (assert_alignment a anns m2)).
  Proof using.
    apply refine_EOU_to_cfg; unfold assert_alignment, assert_aligned_to.
    destruct a as [[p | | | | | | |] | |], (find_option ann_align anns) as [al |];
      try (constructor; reflexivity).
    destruct (ptr_aligned_to p (Z.to_N (denote_int_syntax al))); constructor; reflexivity.
  Qed.

  Lemma refine_cfg_apply_value_attrs_msg
    (attrs : list param_attr) (m1 m2 : string) (v : @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (EOU_to_itree (apply_value_attrs attrs m1 v))
      (EOU_to_itree (apply_value_attrs attrs m2 v)).
  Proof using.
    apply refine_EOU_to_cfg; unfold apply_value_attrs.
    destruct (existsb attr_is_noundef attrs && negb (dvalue_well_defined (value_attrs_poison attrs v)));
      constructor; reflexivity.
  Qed.

  Lemma refine_cfg_assert_deref_msg
    (or_null : bool) (n : N) (v : @dvalue PaV) (m1 m2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (assert_dereferenceable or_null n v m1)
      (assert_dereferenceable or_null n v m2).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [[p | | | | | | |] | |];
      try apply refine_cfg_raise_any;
      try apply refine_cfg_raiseUB_any.
    apply refine_cfg_refl.
  Qed.

  Lemma refine_cfg_apply_attrs_msg
    (attrs : list param_attr) (m1 m2 : string) (v : @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (apply_attrs attrs m1 v)
      (apply_attrs attrs m2 v).
  Proof using.
    unfold apply_attrs.
    eapply ruttc_bind; [apply refine_cfg_apply_value_attrs_msg | intros v' _ <-].
    eapply ruttc_bind.
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[on n] |],
               v' as [[p | | | | | | |] | |];
        try apply refine_cfg_refl; apply refine_cfg_assert_deref_msg.
    - intros [] _ _; apply ruttc_ret; reflexivity.
  Qed.

  Lemma refine_cfg_call_args_msg
    (cargs : list (texp dtyp * list param_attr)) (m1 m2 : string) :
    @refine_cfg PaV _ _ Logic.eq
      (denote_call_args cargs m1)
      (denote_call_args cargs m2).
  Proof using.
    unfold denote_call_args; induction cargs as [| [[t op] attrs] rest IH]; cbn [map_monad].
    - apply ruttc_ret; reflexivity.
    - eapply ruttc_bind.
      + eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
        apply refine_cfg_apply_attrs_msg.
      + intros v' _ <-; eapply ruttc_bind; [exact IH | intros vs _ <-; apply ruttc_ret; reflexivity].
  Qed.

  Lemma refine_cfg_operand_bundles_msg
    (f : exp dtyp) (obs : list (@operand_bundle dtyp)) (l1 l2 : string) :
    @refine_cfg PaV unit unit Logic.eq
      (denote_operand_bundles l1 f obs)
      (denote_operand_bundles l2 f obs).
  Proof using.
    unfold denote_operand_bundles.
    eapply ruttc_bind; [| intros _ _ _; apply ruttc_ret; reflexivity].
    induction obs as [| ob rest IH]; cbn [map_monad]; [apply ruttc_ret; reflexivity |].
    eapply ruttc_bind.
    - eapply ruttc_bind; [apply refine_cfg_refl | intros vs _ <-].
      unfold bundle_check.
      destruct (is_llvm_assume f); [| apply ruttc_ret; reflexivity].
      unfold assume_bundle_checks.
      repeat (cbn [find option_map snd];
              match goal with |- context [String.eqb ?a ?b] => destruct (String.eqb a b) end);
        cbn [find option_map snd];
        try (apply ruttc_ret; reflexivity).
      + unfold assume_nonnull, assume_violated, assume_malformed.
        destruct vs as [| p [| ? ?]]; [apply refine_cfg_raise_any | | apply refine_cfg_raise_any].
        destruct (dvalue_ptr_address p) as [a |]; [| apply refine_cfg_raiseUB_any].
        destruct (a =? 0)%Z; [apply refine_cfg_raiseUB_any | apply ruttc_ret; reflexivity].
      + unfold assume_noundef, assume_violated, assume_malformed.
        destruct vs as [| v [| ? ?]]; [apply refine_cfg_raise_any | | apply refine_cfg_raise_any].
        destruct (dvalue_well_defined v); [apply ruttc_ret; reflexivity | apply refine_cfg_raiseUB_any].
      + unfold assume_align, assume_violated, assume_malformed.
        destruct vs as [| p [| al off]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint al),
                 (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end);
          try apply refine_cfg_raiseUB_any.
        destruct (if is_power_of_two z0 then ((z - z1) mod z0 =? 0)%Z else (z =? 0)%Z);
          [apply ruttc_ret; reflexivity | apply refine_cfg_raiseUB_any].
      + unfold assume_dereferenceable, assume_violated, assume_malformed; cbv zeta.
        destruct vs as [| p [| sz [| ? ?]]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint sz); try apply refine_cfg_raiseUB_any.
        destruct (z0 =? 0)%Z; [apply ruttc_ret; reflexivity | apply refine_cfg_assert_deref_msg].
      + unfold assume_dereferenceable, assume_violated, assume_malformed; cbv zeta.
        destruct vs as [| p [| sz [| ? ?]]]; try apply refine_cfg_raise_any.
        destruct (dvalue_ptr_address p), (bundle_uint sz); try apply refine_cfg_raiseUB_any.
        destruct (z0 =? 0)%Z; [apply ruttc_ret; reflexivity | apply refine_cfg_assert_deref_msg].
    - intros [] _ _; eapply ruttc_bind; [exact IH | intros _ _ _; apply ruttc_ret; reflexivity].
  Qed.

  Lemma refine_cfg_check_call_return_msg
    (fattrs : list fn_attr) (rattrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax)))
    (l1 l2 : string) (vs : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV) :
    @refine_cfg PaV _ _ Logic.eq
      (check_call_return fattrs rattrs ranges l1 vs res)
      (check_call_return fattrs rattrs ranges l2 vs res).
  Proof using.
    unfold check_call_return.
    eapply ruttc_bind.
    - apply refine_EOU_to_cfg; unfold check_call_result.
      destruct res as [_ | v].
      + destruct (existsb fn_attr_is_nounwind fattrs); constructor; reflexivity.
      + destruct (existsb fn_attr_is_noreturn fattrs); [constructor |].
        destruct (existsb fn_attr_is_nocreateundeforpoison fattrs &&
                  forallb dvalue_well_defined vs && negb (dvalue_well_defined v));
          constructor; reflexivity.
    - intros [] _ _; destruct res as [ex | v]; [apply ruttc_ret; reflexivity |].
      eapply ruttc_bind; [apply refine_cfg_apply_attrs_msg | intros v' _ <-; apply ruttc_ret; reflexivity].
  Qed.

  Lemma denote_phis_strip_eq
    (from : block_id)
    (ps1 ps2 : list (local_id * phi dtyp * list (metadata dtyp)))
    (Heq : List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps1 =
           List.map (fun '(id, p, md) => (id, p, strip_file_info_mds md)) ps2) :
    @refine_cfg PaV unit unit Logic.eq (denote_phis from ps1) (denote_phis from ps2).
  Proof using.
    unfold denote_phis.
    eapply ruttc_bind.
    - revert ps2 Heq; induction ps1 as [| [[id1 [fm1 dt1 args1]] md1] r1 IH];
        intros [| [[id2 [fm2 dt2 args2]] md2] r2] Heq;
        cbn [List.map] in Heq; try discriminate Heq; cbn [map_monad].
      + apply ruttc_ret; reflexivity.
      + injection Heq as <- <- <- _ Htl.
        eapply ruttc_bind.
        * unfold denote_phi; cbv zeta.
          destruct (assoc from args1) as [op |]; [apply refine_cfg_refl | apply refine_cfg_raise_any].
        * intros dv _ <-; eapply ruttc_bind;
            [exact (IH r2 Htl) | intros dvs _ <-; apply ruttc_ret; reflexivity].
    - intros dvs _ <-; apply refine_cfg_refl.
  Qed.

  Lemma denote_instr_strip_eq
    (iid : instr_id) (ins : instr dtyp)
    (md1 md2 : list (metadata dtyp)) (va : option (@ptr PaV))
    (Hmd : strip_file_info_mds md1 = strip_file_info_mds md2) :
    @refine_cfg PaV unit unit Logic.eq
      (denote_instr (iid, ins, md1) va)
      (denote_instr (iid, ins, md2) va).
  Proof using.
    assert (Hla : load_metadata_attrs md1 = load_metadata_attrs md2)
      by (rewrite <- (load_metadata_attrs_strip md1), <- (load_metadata_attrs_strip md2), Hmd; reflexivity).
    assert (Hmr : metadata_range md1 = metadata_range md2)
      by (rewrite <- (metadata_range_strip md1), <- (metadata_range_strip md2), Hmd; reflexivity).
    assert (Hld : load_metadata_dereferenceable md1 = load_metadata_dereferenceable md2)
      by (rewrite <- (load_metadata_dereferenceable_strip md1),
                  <- (load_metadata_dereferenceable_strip md2), Hmd; reflexivity).
    unfold denote_instr; cbv zeta.
    destruct iid as [id | vid], ins as
      [ msg
      | op
      | [dt f] cargs anns obs
      | dt anns
      | dt [du ptr_e] anns
      | [dt val_e] [du ptr_e] anns
      | ss ord
      | cpx
      | armw
      | [t va_e] argty
      | rty clp cs ];
      try apply refine_cfg_raise_any;
      try apply refine_cfg_refl.
    - (* INSTR_Call (IId) *)
      eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros vs _ <-].
      eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros res _ <-].
      rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros res' _ <-].
      apply refine_cfg_refl.
    - (* INSTR_Alloca *)
      destruct (find_option ann_num_elements anns) as [[t num_e] |]; [| apply refine_cfg_refl].
      eapply ruttc_bind.
      + eapply ruttc_bind; [apply refine_cfg_refl | intros n _ <-].
        destruct (dvalue_is_poison n); [apply refine_cfg_raiseUB_any | apply refine_cfg_refl].
      + intros [] _ _; apply ruttc_ret; reflexivity.
    - (* INSTR_Load *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
      eapply ruttc_bind; [apply refine_cfg_assert_alignment_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
      rewrite Hla, Hmr; eapply ruttc_bind; [apply refine_cfg_apply_value_attrs_msg | intros v' _ <-].
      eapply ruttc_bind.
      + unfold assert_load_dereferenceable; rewrite Hld.
        destruct (load_metadata_dereferenceable md2) as [[on n] |];
          [apply refine_cfg_assert_deref_msg | apply ruttc_ret; reflexivity].
      + intros [] _ _; apply refine_cfg_refl.
    - (* INSTR_LandingPad (IId) *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros [e |] _ <-];
        [apply refine_cfg_refl | apply refine_cfg_raise_any].
    - (* INSTR_Call (IVoid) *)
      eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros vs _ <-].
      eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros res _ <-].
      rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros res' _ <-].
      apply refine_cfg_refl.
    - (* INSTR_Store (IVoid) *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
      eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
      eapply ruttc_bind; [apply refine_cfg_assert_alignment_msg | intros [] _ _].
      eapply ruttc_bind.
      + destruct a as [[| | | | | | |] | |]; try apply refine_cfg_refl; apply refine_cfg_raiseUB_any.
      + intros [] _ _; apply ruttc_ret; reflexivity.
  Qed.

  Lemma denote_code_strip_eq
    (cd1 cd2 : code dtyp) (va : option (@ptr PaV))
    (Heq : List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd1 =
           List.map (fun '(iid, ins, md) => (iid, ins, strip_file_info_mds md)) cd2) :
    @refine_cfg PaV unit unit Logic.eq (denote_code cd1 va) (denote_code cd2 va).
  Proof using.
    revert cd2 Heq; induction cd1 as [| [[iid1 ins1] md1] r1 IH];
      intros [| [[iid2 ins2] md2] r2] Heq;
      cbn [List.map] in Heq; try discriminate Heq; cbn [denote_code loop_monad].
    - apply ruttc_ret; reflexivity.
    - injection Heq as <- <- Hmd Htl.
      eapply ruttc_bind; [exact (denote_instr_strip_eq iid1 ins1 md1 md2 va Hmd) |].
      intros [] _ _; exact (IH r2 Htl).
  Qed.

  Lemma denote_term_strip_eq
    (iid : instr_id) (tm : terminator dtyp)
    (md1 md2 : list (metadata dtyp))
    (Hmd : strip_file_info_mds md1 = strip_file_info_mds md2) :
    @refine_cfg PaV _ _ Logic.eq
      (denote_terminator (iid, tm, md1))
      (denote_terminator (iid, tm, md2)).
  Proof using.
    assert (Hmr : metadata_range md1 = metadata_range md2)
      by (rewrite <- (metadata_range_strip md1), <- (metadata_range_strip md2), Hmd; reflexivity).
    unfold denote_terminator; cbv zeta.
    destruct tm as
      [ [dt op]
      |
      | [dt op] br1 br2
      | br
      | [dt e] def_br dests
      | [dt addr] brs fn
      | [dt expr]
      | [dt fn_e] cargs to_lbl uw_lbl anns obs
      | ];
      try apply refine_cfg_refl;
      try apply refine_cfg_raiseUB_any.
    - (* TERM_Br *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros v _ <-].
      destruct v as [[| sz cbit | | | | | |] | |];
        try apply refine_cfg_raise_any;
        try apply refine_cfg_raiseUB_any.
      revert cbit; destruct sz as [p | p |]; intros cbit;
        try apply refine_cfg_raise_any; apply refine_cfg_refl.
    - (* TERM_Switch *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros sel _ <-].
      destruct (dvalue_is_poison sel); [apply refine_cfg_raiseUB_any | apply refine_cfg_refl].
    - (* TERM_IndirectBr *)
      eapply ruttc_bind; [apply refine_cfg_refl | intros a _ <-].
      destruct (dvalue_is_poison a); [apply refine_cfg_raiseUB_any |].
      destruct fn as [f |]; [| apply refine_cfg_raise_any].
      eapply ruttc_bind; [apply refine_cfg_refl | intros addrs _ <-].
      destruct (dvalue_ptr_address a) as [z |]; [| apply refine_cfg_raise_any].
      destruct (indirectbr_target z (List.combine brs addrs));
        [apply refine_cfg_refl | apply refine_cfg_raiseUB_any].
    - (* TERM_Invoke *)
      eapply ruttc_bind; [apply refine_cfg_call_args_msg | intros uvs _ <-].
      eapply ruttc_bind; [apply refine_cfg_operand_bundles_msg | intros [] _ _].
      eapply ruttc_bind; [apply refine_cfg_refl | intros fv _ <-].
      eapply ruttc_bind; [apply refine_cfg_refl | intros rv _ <-].
      rewrite Hmr; eapply ruttc_bind; [apply refine_cfg_check_call_return_msg | intros rv' _ <-].
      apply refine_cfg_refl.
  Qed.

  Lemma denote_cfg_strip_gen
    (c1 c2 : CFG.cfg dtyp) (va : option (@ptr PaV))
    (Hstrip : strip_file_info_cfg c1 = strip_file_info_cfg c2) :
    @refine_cfg PaV _ _ Logic.eq (denote_cfg c1 va) (denote_cfg c2 va).
  Proof using.
    unfold strip_file_info_cfg in Hstrip; injection Hstrip as Hinit Hbks _.
    unfold denote_cfg, denote_cfg_map; rewrite Hinit.
    eapply ruttc_bind.
    - unfold denote_ocfg_map, refine_cfg.
      eapply ruttc_iter with (II := Logic.eq); [| reflexivity].
      intros [from src] _ <-; cbv beta iota.
      rewrite !ScopeTheory.ocfg_map_find_block.
      assert (Hfb :
        option_map strip_file_info_block (find_block (blks c1) src) =
        option_map strip_file_info_block (find_block (blks c2) src)).
      { rewrite <- !(ScopeTheory.find_block_map strip_file_info_block _ src)
          by (intros ?; reflexivity).
        rewrite Hbks; reflexivity. }
      destruct (find_block (blks c1) src) as [bk1 |],
               (find_block (blks c2) src) as [bk2 |];
        cbn [option_map] in Hfb; try discriminate Hfb.
      + injection Hfb as Hbk.
        unfold strip_file_info_block in Hbk.
        destruct (blk_term bk1) as [[ti1 tm1] tmd1] eqn:Et1,
                 (blk_term bk2) as [[ti2 tm2] tmd2] eqn:Et2.
        injection Hbk as _ Hph Hcd <- <- Htmd _.
        eapply ruttc_bind.
        * unfold denote_block; rewrite Et1, Et2.
          eapply ruttc_bind; [exact (denote_phis_strip_eq from _ _ Hph) | intros [] _ _].
          eapply ruttc_bind; [exact (denote_code_strip_eq _ _ va Hcd) | intros [] _ _].
          exact (denote_term_strip_eq ti1 tm1 tmd1 tmd2 Htmd).
        * intros [tgt | dv] _ <-; cbv beta iota; apply ruttc_ret; constructor; reflexivity.
      + apply ruttc_ret; constructor; reflexivity.
    - intros [bid | uv] _ <-; cbv beta iota;
        [apply refine_cfg_raise_any | apply ruttc_ret; reflexivity].
  Qed.

  Lemma strip_file_info_cfg_idem (c : CFG.cfg dtyp) :
    strip_file_info_cfg (strip_file_info_cfg c) = strip_file_info_cfg c.
  Proof using.
    destruct c as [in0 bks0 ar0]; unfold strip_file_info_cfg; cbn [init blks args]; f_equal.
    induction bks0 as [| [id ph cd [[ti tm] tmd] cm] rest IH]; [reflexivity |].
    cbn [List.map]; f_equal; [| exact IH].
    unfold strip_file_info_block; cbn [blk_id blk_phis blk_code blk_term blk_comments].
    rewrite strip_file_info_mds_idem; f_equal.
    - induction ph as [| [[x p] md] rp IHp]; [reflexivity |].
      cbn [List.map]; rewrite strip_file_info_mds_idem, IHp; reflexivity.
    - induction cd as [| [[i ins] md] rc IHc]; [reflexivity |].
      cbn [List.map]; rewrite strip_file_info_mds_idem, IHc; reflexivity.
  Qed.

  Theorem strip_file_info_mcfg_refines_fwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT M (strip_file_info_mcfg M).
  Proof using.
    apply lift_cfg_pass.
    - exact strip_file_info_cfg_block_addresses.
    - intros c va; apply denote_cfg_strip_gen.
      symmetry; apply strip_file_info_cfg_idem.
  Qed.

  Theorem strip_file_info_mcfg_refines_bwd (M : CFG.mcfg dtyp) :
    @prog_refines IP IPT (strip_file_info_mcfg M) M.
  Proof using.
    apply module_defs_ruttc_refines.
    - unfold strip_file_info_mcfg, build_global_environment.
      rewrite map_mcfg_cfg_prototypes,
              (map_mcfg_cfg_block_addresses strip_file_info_cfg M strip_file_info_cfg_block_addresses).
      reflexivity.
    - reflexivity.
    - unfold strip_file_info_mcfg, map_mcfg_cfg; cbn [m_definitions].
      induction (m_definitions M) as [| d rest IH]; [constructor |].
      cbn [List.map map_defn_cfg]; constructor; [| exact IH].
      refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros va; apply denote_cfg_strip_gen, strip_file_info_cfg_idem.
  Qed.

  Theorem check_module_merge_parsed_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge_parsed m_orig m_merged verified_slices = true)
    (Hslices :
       Forall slice_body_refines
         (List.map
            (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
            verified_slices)) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    eapply prog_refines_trans; [apply strip_file_info_mcfg_refines_fwd |].
    eapply prog_refines_trans;
      [exact (check_module_merge_refines _ _ _ Hchk Hslices)
      | apply strip_file_info_mcfg_refines_bwd].
  Qed.

  Corollary validate_module_merge_parsed_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hval : validate_module_merge_parsed m_orig m_merged verified_slices = inr tt)
    (Hslices :
       Forall slice_body_refines
         (List.map
            (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
            verified_slices)) :
    @prog_refines IP IPT m_orig m_merged.
  Proof using.
    apply (check_module_merge_parsed_refines m_orig m_merged verified_slices);
      [exact (proj1 (validate_module_merge_ok_iff _ _ _) Hval) | exact Hslices].
  Qed.

End StripFileInfoRefinement.

Theorem validate_module_merge_parsed_I2F_model_refine
  (m_orig m_merged : CFG.mcfg dtyp)
  (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
  (ret_typ : dtyp) (entry : function_id)
  (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
  (s1 : @FusedS PInf) (s2 : @FusedS PFin)
  (Hval : validate_module_merge_parsed m_orig m_merged verified_slices = inr tt)
  (Hslices :
     Forall (@slice_body_refines IPZ IPZTheory)
       (List.map
          (fun '(fid, ms, mt) => (fid, strip_file_info_mcfg ms, strip_file_info_mcfg mt))
          verified_slices))
  (Hargs : Forall2 I2F_dvalue args1 args2)
  (Hs : I2F_FusedS s1 s2) :
  @prog_refines IPZ IPZTheory m_orig m_merged /\
  I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
    (interp_mcfg (@denote_vellvm PInf ret_typ entry args1 m_merged) s1)
    (interp_mcfg (@denote_vellvm PFin ret_typ entry args2 m_merged) s2).
Proof.
  split.
  - exact (@validate_module_merge_parsed_refines IPZ IPZTheory m_orig m_merged
             verified_slices Hval Hslices).
  - exact (I2F_toplevel.model_refine ret_typ entry args1 args2 m_merged s1 s2 Hargs Hs).
Qed.

(** * 7. Surface-Syntax [toplevel_entities] CLI Entrypoint *)

Definition mm_strip_leading_at (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 64%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition mm_tle_to_dtyp_mcfg
  (tle : toplevel_entities typ (block typ * list (block typ))) : CFG.mcfg dtyp :=
  convert_types (CFG.mcfg_of_tle (ModuleRefs.resolve_module_refs tle)).

Definition validate_module_merge_tle
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (verified_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  : string + unit :=
  validate_module_merge_parsed
    (mm_tle_to_dtyp_mcfg orig_tle)
    (mm_tle_to_dtyp_mcfg merged_tle)
    (List.map
       (fun '(fn_str, s_tle, t_tle) =>
          (Name (mm_strip_leading_at fn_str),
           mm_tle_to_dtyp_mcfg s_tle,
           mm_tle_to_dtyp_mcfg t_tle))
       verified_slices).

Theorem validate_module_merge_tle_refines
  (orig_tle merged_tle : toplevel_entities typ (block typ * list (block typ)))
  (verified_slices :
    list (string *
          toplevel_entities typ (block typ * list (block typ)) *
          toplevel_entities typ (block typ * list (block typ))))
  (Hval : validate_module_merge_tle orig_tle merged_tle verified_slices = inr tt)
  (Hslices :
     Forall (@slice_body_refines IPZ IPZTheory)
       (List.map
          (fun '(fn_str, s_tle, t_tle) =>
             (Name (mm_strip_leading_at fn_str),
              strip_file_info_mcfg (mm_tle_to_dtyp_mcfg s_tle),
              strip_file_info_mcfg (mm_tle_to_dtyp_mcfg t_tle)))
          verified_slices)) :
  @prog_refines IPZ IPZTheory
    (mm_tle_to_dtyp_mcfg orig_tle)
    (mm_tle_to_dtyp_mcfg merged_tle).
Proof.
  unfold validate_module_merge_tle in Hval.
  apply (@validate_module_merge_parsed_refines IPZ IPZTheory _ _ _ Hval).
  clear Hval.
  induction verified_slices as [| [[fn_str s_tle] t_tle] rest IH]; cbn in *.
  - constructor.
  - inversion Hslices as [| ? ? Hhd Htl]; subst.
    constructor; [exact Hhd | exact (IH Htl)].
Qed.
