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
  Bool
  Lia
  Classes.RelationClasses.
Import ListNotations.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
  Semantics.VellvmIntegers
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
  Semantics.Libraries
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
  Pipeline
  McfgExport.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.
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

Definition mm_fn_attr_from_tag (t : positive) : option fn_attr :=
  match t with
  | 1%positive => Some FNATTR_Alwaysinline
  | 2%positive => Some FNATTR_Builtin
  | 3%positive => Some FNATTR_Cold
  | 4%positive => Some FNATTR_Convergent
  | 5%positive => Some FNATTR_Disable_sanitizer_instrumentation
  | 6%positive => Some FNATTR_Fn_ret_thunk_extern
  | 7%positive => Some FNATTR_Hot
  | 8%positive => Some FNATTR_Inaccessiblememonly
  | 9%positive => Some FNATTR_Inaccessiblemem_or_argmemonly
  | 10%positive => Some FNATTR_Inlinehint
  | 11%positive => Some FNATTR_Jumptable
  | 12%positive => Some FNATTR_Minsize
  | 13%positive => Some FNATTR_Naked
  | 14%positive => Some FNATTR_No_jump_tables
  | 15%positive => Some FNATTR_Nobuiltin
  | 16%positive => Some FNATTR_Noduplicate
  | 17%positive => Some FNATTR_Nofree
  | 18%positive => Some FNATTR_Noimplicitfloat
  | 19%positive => Some FNATTR_Noinline
  | 20%positive => Some FNATTR_Nomerge
  | 21%positive => Some FNATTR_Nonlazybind
  | 22%positive => Some FNATTR_Noprofile
  | 23%positive => Some FNATTR_Noredzone
  | 24%positive => Some FNATTR_Indirect_tls_seg_refs
  | 25%positive => Some FNATTR_Noreturn
  | 26%positive => Some FNATTR_Norecurse
  | 27%positive => Some FNATTR_Willreturn
  | 28%positive => Some FNATTR_Nosync
  | 29%positive => Some FNATTR_Nounwind
  | 30%positive => Some FNATTR_Nocreateundeforpoison
  | 31%positive => Some FNATTR_Nosanitize_bounds
  | 32%positive => Some FNATTR_Nosanitize_coverage
  | 33%positive => Some FNATTR_Null_pointer_is_valid
  | 34%positive => Some FNATTR_Optforfuzzing
  | 35%positive => Some FNATTR_Optnone
  | 36%positive => Some FNATTR_Optsize
  | 37%positive => Some FNATTR_Readnone
  | 38%positive => Some FNATTR_Readonly
  | 39%positive => Some FNATTR_Writeonly
  | 40%positive => Some FNATTR_Argmemonly
  | 41%positive => Some FNATTR_Returns_twice
  | 42%positive => Some FNATTR_Safestack
  | 43%positive => Some FNATTR_Sanitize_address
  | 44%positive => Some FNATTR_Sanitize_memory
  | 45%positive => Some FNATTR_Sanitize_thread
  | 46%positive => Some FNATTR_Sanitize_hwaddress
  | 47%positive => Some FNATTR_Sanitize_memtag
  | 48%positive => Some FNATTR_Speculative_load_hardening
  | 49%positive => Some FNATTR_Speculatable
  | 50%positive => Some FNATTR_Ssp
  | 51%positive => Some FNATTR_Sspstrong
  | 52%positive => Some FNATTR_Sspreq
  | 53%positive => Some FNATTR_Strictfp
  | 54%positive => Some FNATTR_Tls_load_hoist
  | 55%positive => Some FNATTR_Nocf_check
  | 56%positive => Some FNATTR_Shadowcallstack
  | 57%positive => Some FNATTR_Mustprogress
  | _ => None
  end.

Lemma mm_fn_attr_nullary_tag_from (x : fn_attr) (t : positive) :
  mm_fn_attr_nullary_tag x = Some t ->
  mm_fn_attr_from_tag t = Some x.
Proof.
  destruct x; cbn [mm_fn_attr_nullary_tag]; intro H;
    try discriminate H; inversion H; reflexivity.
Qed.

Lemma mm_fn_attr_nullary_tag_inj (x y : fn_attr) (t : positive) :
  mm_fn_attr_nullary_tag x = Some t ->
  mm_fn_attr_nullary_tag y = Some t ->
  x = y.
Proof.
  intros Hx Hy.
  apply mm_fn_attr_nullary_tag_from in Hx.
  apply mm_fn_attr_nullary_tag_from in Hy.
  rewrite Hx in Hy; inversion Hy; reflexivity.
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
  destruct x as [i1 s1 u1], y as [i2 s2 u2]; unfold mm_gep_flags_eqb; cbn [gep_inbounds gep_nusw gep_nuw].
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
  unfold mm_cmpxchg_eqb;
    cbn [c_weak c_volatile c_ptr c_cmp c_new c_syncscope c_success_ordering c_failure_ordering c_align].
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
  unfold mm_atomicrmw_eqb;
    cbn [a_volatile a_operation a_ptr a_val a_syncscope a_ordering a_align].
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
  destruct x as [t1 o1], y as [t2 o2]; unfold mm_operand_bundle_eqb; cbn [ob_tag ob_ops].
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
  unfold mm_block_eqb; cbn [blk_id blk_phis blk_code blk_term blk_comments].
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
  unfold mm_cfg_eqb; cbn [init blks args].
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
  unfold mm_global_eqb; cbn [g_ident g_typ g_constant g_exp g_externally_initialized g_alias g_annotations].
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
  unfold mm_declaration_eqb; cbn [dc_name dc_type dc_param_attrs dc_attrs dc_annotations].
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
  destruct x as [p1 a1 i1], y as [p2 a2 i2]; unfold mm_definition_eqb; cbn [df_prototype df_args df_instrs].
  rewrite !Bool.andb_true_iff, mm_declaration_eqb_eq,
    (mm_list_eqb_eq _ raw_id_eqb_spec), mm_cfg_eqb_eq.
  split.
  - intros [[-> ->] ->]; reflexivity.
  - intros H; injection H as -> -> ->; repeat split; reflexivity.
Qed.


