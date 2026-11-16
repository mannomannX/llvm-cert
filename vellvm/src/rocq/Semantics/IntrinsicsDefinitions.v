(* begin hide *)
From ExtLib Require Import
  Programming.Eqv
  Data.String.

From ITree Require Import ITree.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.DynamicValues
  VellvmIntegers
  Numeric
  LLVMEvents
  Conversion
  EOU.

From Flocq.IEEE754 Require Import
  Binary
  Bits.

Import EqvNotation.
(* end hide *)

(** * Intrinsics VIR provides an easily extensible support for instrinsics.
    
    There are several ways to define the semantics of intrinsics:

    1. As LLVM IR "library" code.

       This is the most easily extensible way to extend VIR with semantics for
       intrinsics. It works by providing a `.ll` file that defines the meaning
       of the intrinsic using standard LLVM instructions.  There are a few
       potential semantic implications that may impact reasoning about such
       intrinsics.  In particular, because such an intrinsic is just an
       "ordinary" LLVM function:

       - calling it will create a stack frame, and do a function call it will
       - have global address address in the heap

       Neither of which would be true of "real" intrinsics.

    2. As a Rocq function that directly manipulates [VIR] [dvalue].
       These are either defined below in this file _or_, like some memory
       intrinsics and varargs that interact with LLVM IR's effects, defined
       elsewhere.

       Each such intrinsic must be:

        - registered by providing a [declaration typ] and added to
          [defined_intrinsics_decls]

        - _if_ the intrinsics is a pure computation, it must be implemented as a
          pure Gallina function of type [semantic_function] and added to
          [defined_intrinsics]

        - _if_ it is impure, i.e. depends on the memory, as is the case for
          [memcpy], its implementation must be provided in [src/rocq/Semantics/Implementations/Memory.v]
          and a test on its name added to [handle_intrinsicM] (for the
          memory intrinsics, [declares] against their declarations).
 *)

(** The declaration of an intrinsic, without attributes.  Only its name
    matters to the semantics (see [lookup_intrinsic_declaration]). *)
Definition intrinsic_decl (name : string) (ret : typ) (args : list typ) : declaration typ :=
  {|
    dc_name        := Name name;
    dc_type        := TYPE_Function ret args false;
    dc_param_attrs := ([], map (fun _ => []) args);
    dc_attrs       := [];
    dc_annotations := []
  |}.

Definition vellvm_internal_throw_decl : declaration typ :=
  intrinsic_decl "llvm.vellvm.internal.throw" TYPE_Void [].

(* A poison condition is UB in [llvm_assume] itself. *)
Definition assume_decl : declaration typ :=
  intrinsic_decl "llvm.assume" TYPE_Void [TYPE_I 1].

Definition va_start_decl : declaration typ :=
  intrinsic_decl "llvm.va_start" TYPE_Void [TYPE_Pointer None].

Definition va_end_decl : declaration typ :=
  intrinsic_decl "llvm.va_end" TYPE_Void [TYPE_Pointer None].

Definition va_copy_decl : declaration typ :=
  intrinsic_decl "llvm.va_copy" TYPE_Void [TYPE_Pointer None; TYPE_Pointer None].

Definition fabs_32_decl : declaration typ :=
  intrinsic_decl "llvm.fabs.f32" (TYPE_FP FP_float) [TYPE_FP FP_float].

Definition fabs_64_decl : declaration typ :=
  intrinsic_decl "llvm.fabs.f64" (TYPE_FP FP_double) [TYPE_FP FP_double].

Definition maxnum_32_decl : declaration typ :=
  intrinsic_decl "llvm.maxnum.f32" (TYPE_FP FP_float) [TYPE_FP FP_float; TYPE_FP FP_float].

Definition maxnum_64_decl : declaration typ :=
  intrinsic_decl "llvm.maxnum.f64" (TYPE_FP FP_double) [TYPE_FP FP_double; TYPE_FP FP_double].

Definition minimum_32_decl : declaration typ :=
  intrinsic_decl "llvm.minimum.f32" (TYPE_FP FP_float) [TYPE_FP FP_float; TYPE_FP FP_float].

Definition minimum_64_decl : declaration typ :=
  intrinsic_decl "llvm.minimum.f64" (TYPE_FP FP_double) [TYPE_FP FP_double; TYPE_FP FP_double].

Definition minnum_32_decl : declaration typ :=
  intrinsic_decl "llvm.minnum.f32" (TYPE_FP FP_float) [TYPE_FP FP_float; TYPE_FP FP_float].

Definition minnum_64_decl : declaration typ :=
  intrinsic_decl "llvm.minnum.f64" (TYPE_FP FP_double) [TYPE_FP FP_double; TYPE_FP FP_double].

Definition maximum_32_decl : declaration typ :=
  intrinsic_decl "llvm.maximum.f32" (TYPE_FP FP_float) [TYPE_FP FP_float; TYPE_FP FP_float].

Definition maximum_64_decl : declaration typ :=
  intrinsic_decl "llvm.maximum.f64" (TYPE_FP FP_double) [TYPE_FP FP_double; TYPE_FP FP_double].

Definition copysign_32_decl : declaration typ :=
  intrinsic_decl "llvm.copysign.f32" (TYPE_FP FP_float) [TYPE_FP FP_float; TYPE_FP FP_float].

Definition copysign_64_decl : declaration typ :=
  intrinsic_decl "llvm.copysign.f64" (TYPE_FP FP_double) [TYPE_FP FP_double; TYPE_FP FP_double].

Definition fma_32_decl : declaration typ :=
  intrinsic_decl "llvm.fma.f32" (TYPE_FP FP_float)
    [TYPE_FP FP_float; TYPE_FP FP_float; TYPE_FP FP_float].

Definition fma_64_decl : declaration typ :=
  intrinsic_decl "llvm.fma.f64" (TYPE_FP FP_double)
    [TYPE_FP FP_double; TYPE_FP FP_double; TYPE_FP FP_double].

Definition fmuladd_32_decl : declaration typ :=
  intrinsic_decl "llvm.fmuladd.f32" (TYPE_FP FP_float)
    [TYPE_FP FP_float; TYPE_FP FP_float; TYPE_FP FP_float].

Definition fmuladd_64_decl : declaration typ :=
  intrinsic_decl "llvm.fmuladd.f64" (TYPE_FP FP_double)
    [TYPE_FP FP_double; TYPE_FP FP_double; TYPE_FP FP_double].

Definition extra_fp_decls : list (declaration typ) :=
  [ minnum_32_decl;
    minnum_64_decl;
    maximum_32_decl;
    maximum_64_decl;
    copysign_32_decl;
    copysign_64_decl;
    fma_32_decl;
    fma_64_decl;
    fmuladd_32_decl;
    fmuladd_64_decl
  ].

(* Saturated arithmetic: https://llvm.org/docs/LangRef.html#saturation-arithmetic-intrinsics *)
Definition ushl_sat_decl (name : string) (sz : positive) : declaration typ :=
  intrinsic_decl name (TYPE_I sz) [TYPE_I sz; TYPE_I sz].

Definition ushl_sat_1_decl  := ushl_sat_decl "llvm.ushl.sat.i1" 1.
Definition ushl_sat_8_decl  := ushl_sat_decl "llvm.ushl.sat.i8" 8.
Definition ushl_sat_16_decl := ushl_sat_decl "llvm.ushl.sat.i16" 16.
Definition ushl_sat_32_decl := ushl_sat_decl "llvm.ushl.sat.i32" 32.
Definition ushl_sat_64_decl := ushl_sat_decl "llvm.ushl.sat.i64" 64.

(** Width-indexed pure integer intrinsic declarations (C23 / Rust core::num). *)
Definition int_width_mangling (sz : positive) : string :=
  match sz with
  | 1%positive => "i1"%string
  | 8%positive => "i8"%string
  | 16%positive => "i16"%string
  | 32%positive => "i32"%string
  | 64%positive => "i64"%string
  | _ => ""%string
  end.

Definition int_std_widths : list positive := [8%positive; 16%positive; 32%positive; 64%positive].
Definition int_bswap_widths : list positive := [16%positive; 32%positive; 64%positive].
Definition int_expect_widths : list positive :=
  [1%positive; 8%positive; 16%positive; 32%positive; 64%positive].

Definition int_unop_decl (op : string) (sz : positive) : declaration typ :=
  intrinsic_decl ("llvm." ++ op ++ "." ++ int_width_mangling sz)%string
    (TYPE_I sz) [TYPE_I sz].

Definition int_unop_flag_decl (op : string) (sz : positive) : declaration typ :=
  intrinsic_decl ("llvm." ++ op ++ "." ++ int_width_mangling sz)%string
    (TYPE_I sz) [TYPE_I sz; TYPE_I 1].

Definition int_binop_decl (op : string) (sz : positive) : declaration typ :=
  intrinsic_decl ("llvm." ++ op ++ "." ++ int_width_mangling sz)%string
    (TYPE_I sz) [TYPE_I sz; TYPE_I sz].

Definition int_ternop_decl (op : string) (sz : positive) : declaration typ :=
  intrinsic_decl ("llvm." ++ op ++ "." ++ int_width_mangling sz)%string
    (TYPE_I sz) [TYPE_I sz; TYPE_I sz; TYPE_I sz].

Definition int_ovf_binop_decl (op : string) (sz : positive) : declaration typ :=
  intrinsic_decl ("llvm." ++ op ++ ".with.overflow." ++ int_width_mangling sz)%string
    (TYPE_Struct [TYPE_I sz; TYPE_I 1]) [TYPE_I sz; TYPE_I sz].

Definition extra_int_decls : list (declaration typ) :=
  (List.map (int_binop_decl "smin"%string) int_std_widths ++
   List.map (int_binop_decl "smax"%string) int_std_widths ++
   List.map (int_binop_decl "umin"%string) int_std_widths ++
   List.map (int_binop_decl "umax"%string) int_std_widths ++
   List.map (int_unop_flag_decl "abs"%string) int_std_widths ++
   List.map (int_binop_decl "uadd.sat"%string) int_std_widths ++
   List.map (int_binop_decl "usub.sat"%string) int_std_widths ++
   List.map (int_binop_decl "sadd.sat"%string) int_std_widths ++
   List.map (int_binop_decl "ssub.sat"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "uadd"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "usub"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "umul"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "sadd"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "ssub"%string) int_std_widths ++
   List.map (int_ovf_binop_decl "smul"%string) int_std_widths ++
   List.map (int_unop_decl "ctpop"%string) int_std_widths ++
   List.map (int_unop_flag_decl "ctlz"%string) int_std_widths ++
   List.map (int_unop_flag_decl "cttz"%string) int_std_widths ++
   List.map (int_unop_decl "bswap"%string) int_bswap_widths ++
   List.map (int_ternop_decl "fshl"%string) int_std_widths ++
   List.map (int_ternop_decl "fshr"%string) int_std_widths ++
   List.map (int_binop_decl "expect"%string) int_expect_widths)%list.

(** The memory intrinsics, under both pointer manglings ([p0i8], i.e. [i8*],
    and [p0], i.e. [ptr], which is what current LLVM emits) and both length
    types.  memcpy and memmove take [(dst, src, len, isvolatile)]; memset
    takes [(dst, val, len, isvolatile)].  Their semantics is in
    [Implementations/Memory.v]. *)
Definition mem_pointer_manglings : list (string * typ) :=
  [("p0i8", TYPE_Pointer (Some (TYPE_I 8))); ("p0", TYPE_Pointer None)].

Definition mem_length_manglings : list (string * typ) :=
  [("i32", TYPE_I 32); ("i64", TYPE_I 64)].

(** One declaration per pointer and length mangling; [mk p pt l lt] builds
    it from the pointer mangling [p] (type [pt]) and the length mangling [l]
    (type [lt]). *)
Definition mem_intrinsic_decls (mk : string -> typ -> string -> typ -> declaration typ)
  : list (declaration typ) :=
  flat_map (fun '(p, pt) => map (fun '(l, lt) => mk p pt l lt) mem_length_manglings)
    mem_pointer_manglings.

(** memcpy and memmove: [llvm.<op>.<p>.<p>.<l>]. *)
Definition memtransfer_decls (op : string) : list (declaration typ) :=
  mem_intrinsic_decls (fun p pt l lt =>
    intrinsic_decl ("llvm." ++ op ++ "." ++ p ++ "." ++ p ++ "." ++ l)%string
      TYPE_Void [pt; pt; lt; TYPE_I 1]).

Definition memcpy_decls : list (declaration typ) := memtransfer_decls "memcpy".

Definition memmove_decls : list (declaration typ) := memtransfer_decls "memmove".

(** memset: [llvm.memset.<p>.<l>]. *)
Definition memset_decls : list (declaration typ) :=
  mem_intrinsic_decls (fun p pt l lt =>
    intrinsic_decl ("llvm.memset." ++ p ++ "." ++ l)%string
      TYPE_Void [pt; TYPE_I 8; lt; TYPE_I 1]).

Definition malloc_decl : declaration typ :=
  intrinsic_decl "malloc" (TYPE_Pointer (Some (TYPE_I 8))) [TYPE_I 64].

Definition free_decl : declaration typ :=
  intrinsic_decl "free" TYPE_Void [TYPE_Pointer (Some (TYPE_I 8))].

(* This may seem to overlap with `defined_intrinsics`, but there are few differences:
   1. This one is defined outside of the module and could be used at the LLVM AST generation stage without yet specifying memory model.
   2. It includes declarations for built-in memory-dependent intrinisics such as `memcpy`.
 *)
Definition defined_intrinsics_decls :=
  [ (* pure intrinsics *)
    fabs_32_decl;
    fabs_64_decl;
    maxnum_32_decl ;
    maxnum_64_decl;
    minimum_32_decl;
    minimum_64_decl;
    ushl_sat_1_decl;
    ushl_sat_8_decl;
    ushl_sat_16_decl;
    ushl_sat_32_decl;
    ushl_sat_64_decl]
  ++ extra_fp_decls
  ++ extra_int_decls
  ++
  (* memory intrinsics *)
  memcpy_decls ++ memmove_decls ++ memset_decls ++
  [ malloc_decl;
    free_decl;

    (* exception intrinsics *)
    vellvm_internal_throw_decl;

    (* assumptions *)
    assume_decl;

    (* Vararg intrinsics *)
    va_start_decl;
    va_end_decl;
    va_copy_decl
  ].


(* This function extracts the string of the form [llvm._] from an LLVM expression.
   It returns None if the expression is not an intrinsic definition.
*)
Definition intrinsic_ident (id:ident) : option string :=
  match id with
  | ID_Global (Name s) =>
      if orb (orb (String.prefix "llvm." s)
                  (Rocqlib.proj_sumbool (string_dec "malloc" s)))
             (Rocqlib.proj_sumbool (string_dec "free" s))
      then Some s else None
  | _ => None
  end.

(* Returns `true` only if both function are named and have the same name.  *)
Definition function_name_eq (a b:function_id) : bool :=
  match a, b with
  | Name aname, Name bname => String.eqb aname bname
  | _, _ => false
  end.

(** Is [name] the name of one of [decls]? *)
Definition declares (decls : list (declaration typ)) (name : string) : bool :=
  existsb (fun d => function_name_eq (Name name) (dc_name d)) decls.

Definition lookup_intrinsic_declaration name : option (declaration typ) :=
  List.find (fun x => function_name_eq name (dc_name x)) defined_intrinsics_decls.

Definition intrinsic_exp {T} (e:exp T) : option string :=
  match e with
  | EXP_Ident (ID_Global (Name s)) =>
      match lookup_intrinsic_declaration (Name s) with
      | Some x => Some s
      | None => None
      end
  | _ => None
  end.



(** Width-polymorphic pure integer intrinsic kernels (independent of [Params] / [E]). *)
Fixpoint count_lz_nat (rem : nat) (u : Z) : Z :=
  match rem with
  | O => 0%Z
  | S rem' =>
      if Z.testbit u (Z.of_nat rem')
      then 0%Z
      else (1 + count_lz_nat rem' u)%Z
  end.

Fixpoint count_tz_nat (rem idx : nat) (u : Z) : Z :=
  match rem with
  | O => 0%Z
  | S rem' =>
      if Z.testbit u (Z.of_nat idx)
      then 0%Z
      else (1 + count_tz_nat rem' (S idx) u)%Z
  end.

Definition int_smin {w : positive} (a b : @bit_int w) : @bit_int w :=
  if @Integers.lt w a b then a else b.

Definition int_smax {w : positive} (a b : @bit_int w) : @bit_int w :=
  if @Integers.lt w a b then b else a.

Definition int_umin {w : positive} (a b : @bit_int w) : @bit_int w :=
  if @Integers.ltu w a b then a else b.

Definition int_umax {w : positive} (a b : @bit_int w) : @bit_int w :=
  if @Integers.ltu w a b then b else a.

Definition int_abs {w : positive} (a : @bit_int w) (is_int_min_poison : bool) : option (@bit_int w) :=
  if Z.eqb (@Integers.signed w a) (@Integers.min_signed w)
  then (if is_int_min_poison then None else Some a)
  else Some (@Integers.repr w (Z.abs (@Integers.signed w a))).

Definition int_uadd_sat {w : positive} (a b : @bit_int w) : @bit_int w :=
  @Integers.repr w (Z.min (@Integers.unsigned w a + @Integers.unsigned w b)%Z (@Integers.max_unsigned w)).

Definition int_usub_sat {w : positive} (a b : @bit_int w) : @bit_int w :=
  @Integers.repr w (Z.max (@Integers.unsigned w a - @Integers.unsigned w b)%Z 0%Z).

Definition int_sadd_sat {w : positive} (a b : @bit_int w) : @bit_int w :=
  @Integers.repr w
    (Z.min (Z.max (@Integers.signed w a + @Integers.signed w b)%Z (@Integers.min_signed w))
           (@Integers.max_signed w)).

Definition int_ssub_sat {w : positive} (a b : @bit_int w) : @bit_int w :=
  @Integers.repr w
    (Z.min (Z.max (@Integers.signed w a - @Integers.signed w b)%Z (@Integers.min_signed w))
           (@Integers.max_signed w)).

Definition int_uadd_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  (@Integers.add w a b,
   Z.gtb (@Integers.unsigned w a + @Integers.unsigned w b)%Z (@Integers.max_unsigned w)).

Definition int_usub_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  (@Integers.sub w a b, Z.ltb (@Integers.unsigned w a) (@Integers.unsigned w b)).

Definition int_umul_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  (@Integers.mul w a b,
   Z.gtb (@Integers.unsigned w a * @Integers.unsigned w b)%Z (@Integers.max_unsigned w)).

Definition int_sadd_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  let s := (@Integers.signed w a + @Integers.signed w b)%Z in
  (@Integers.add w a b,
   orb (Z.ltb s (@Integers.min_signed w)) (Z.gtb s (@Integers.max_signed w))).

Definition int_ssub_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  let s := (@Integers.signed w a - @Integers.signed w b)%Z in
  (@Integers.sub w a b,
   orb (Z.ltb s (@Integers.min_signed w)) (Z.gtb s (@Integers.max_signed w))).

Definition int_smul_ovf {w : positive} (a b : @bit_int w) : @bit_int w * bool :=
  let s := (@Integers.signed w a * @Integers.signed w b)%Z in
  (@Integers.mul w a b,
   orb (Z.ltb s (@Integers.min_signed w)) (Z.gtb s (@Integers.max_signed w))).

Definition int_ctpop {w : positive} (a : @bit_int w) : @bit_int w :=
  let u := @Integers.unsigned w a in
  let cnt := fold_left
               (fun (acc : Z) (i : nat) =>
                  if Z.testbit u (Z.of_nat i) then (acc + 1)%Z else acc)
               (seq 0%nat (Pos.to_nat w))
               0%Z in
  @Integers.repr w cnt.

Definition int_ctlz {w : positive} (a : @bit_int w) (is_zero_poison : bool) : option (@bit_int w) :=
  if @Integers.eq w a (@Integers.zero w)
  then (if is_zero_poison then None else Some (@Integers.repr w (Z.pos w)))
  else Some (@Integers.repr w (count_lz_nat (Pos.to_nat w) (@Integers.unsigned w a))).

Definition int_cttz {w : positive} (a : @bit_int w) (is_zero_poison : bool) : option (@bit_int w) :=
  if @Integers.eq w a (@Integers.zero w)
  then (if is_zero_poison then None else Some (@Integers.repr w (Z.pos w)))
  else Some (@Integers.repr w (count_tz_nat (Pos.to_nat w) 0%nat (@Integers.unsigned w a))).

Definition int_bswap {w : positive} (a : @bit_int w) : @bit_int w :=
  let u := @Integers.unsigned w a in
  let nbytes := Nat.div (Pos.to_nat w) 8%nat in
  let rev := fold_left
               (fun (acc : Z) (idx : nat) =>
                  Z.lor (Z.shiftl acc 8%Z)
                        (Z.land (Z.shiftr u (8 * Z.of_nat idx)%Z) 255%Z))
               (seq 0%nat nbytes)
               0%Z in
  @Integers.repr w rev.

Definition int_fshl {w : positive} (a b c : @bit_int w) : @bit_int w :=
  let bw := Z.pos w in
  let sh := Z.modulo (@Integers.unsigned w c) bw in
  if Z.eqb sh 0%Z
  then a
  else @Integers.repr w
         (Z.lor (Z.shiftl (@Integers.unsigned w a) sh)
                (Z.shiftr (@Integers.unsigned w b) (bw - sh)%Z)).

Definition int_fshr {w : positive} (a b c : @bit_int w) : @bit_int w :=
  let bw := Z.pos w in
  let sh := Z.modulo (@Integers.unsigned w c) bw in
  if Z.eqb sh 0%Z
  then b
  else @Integers.repr w
         (Z.lor (Z.shiftl (@Integers.unsigned w a) (bw - sh)%Z)
                (Z.shiftr (@Integers.unsigned w b) sh)).

(* This functor module provides a way to (extensibly) add the semantic behavior
   for intrinsics defined outside of the core Vellvm operational semantics.

   Internally, invocation of an intrinsic looks no different than that of an
   external function call, so each LLVM intrinsic instruction should produce
   a Call effect.

   Each intrinsic is identified by its name (a string) and its denotation is
   given by a function from a list of dynamic values to a dynamic value (or
   possibly an error).

   NOTE: The intrinsics that can be defined at this layer of the semantics
   cannot affect the core interpreter state or the memory model.  This layer is
   useful for implementing "pure value" intrinsics like floating point
   operations, etc.  Also note that such intrinsics cannot themselves generate
   any other effects.

*)
Section Intrinsics.
  Context {Pa : Params}.
 
  Open Scope string_scope.

  Context {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{ExternalCallE -< E} `{MemoryE -< E}.
    
  (* Each (pure) intrinsic is defined by a function of the following type.

   - each intrinsic should "morally" be a total function: assuming the LLVM program
     is well formed, the intrisnic should always produce an LLVM value (which itself
     might be poison)

   - error should be returned only in the case that the LLVM program is ill-formed
     (e.g. if the wrong number and/or type of arguments is given to the intrinsic)

   - The right-hand [dvalue] of the [+] result is used to throw an exception.
   *)
  Definition pure_base_function := list dvalue_base -> EOU (dvalue_base + dvalue_base).
  Definition pure_function      := list dvalue -> EOU (dvalue + dvalue).
  Definition semantic_function  := list dvalue -> option ptr -> itree E (dvalue + dvalue).

  (* An association list mapping intrinsic names to their semantic definitions *)
  Definition intrinsic_definitions := list (declaration typ * semantic_function).


  (* Intrinsics semantic functions -------------------------------------------- *)

  #[local] Notation retr x := (ret (inr x)).
  (* LANGREF: [llvm.fabs] is explicitly *not* a "floating-point math
     operation": it "acts directly on the underlying bit representation and
     never changes anything except possibly for the sign bit".  So its result
     on a NaN is fully determined -- the payload and quiet bit are preserved
     and the sign is cleared -- with none of the non-determinism that applies
     to NaN results of genuine math operations.

     [Float.abs] / [Float32.abs] are [Babs] instantiated with [abs_nan], which
     clears the sign.  Flocq's [b64_abs] / [b32_abs] instead use [unop_nan_pl],
     which returns the NaN completely unchanged, sign included -- so
     [llvm.fabs(-NaN)] used to come back negative. *)

  (* Absolute value for Float. *)
  Definition llvm_fabs_f32 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float d] => retr (DVALUE_Float (Float32.abs d))
      | _ => raise_error "llvm_fabs_f32 got incorrect / ill-typed inputs"
      end.

  (* Abosulute value for Doubles. *)
  Definition llvm_fabs_f64 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Double d] => retr (DVALUE_Double (Float.abs d))
      | _ => raise_error "llvm_fabs_f64 got incorrect / ill-typed inputs"
      end.

  (* Is a NaN payload quiet?  The quiet bit is the top bit of the significand:
     bit 51 for binary64, bit 22 for binary32. *)
  Definition quiet_nan_pl64 (pl : positive) : bool := Pos.testbit pl 51%N.
  Definition quiet_nan_pl32 (pl : positive) : bool := Pos.testbit pl 22%N.

  (* LANGREF (llvm.maxnum): "If both operands are qNaNs, returns a NaN. If one
     operand is qNaN and another operand is a number, returns the number. If
     both operands are numbers, returns the greater of the two arguments. -0.0
     is considered to be less than +0.0 for this intrinsic."

     Note that a qNaN operand does *not* propagate -- returning the qNaN, as we
     used to, is simply wrong, not a permitted resolution of NaN
     non-determinism.

     For a *signaling* NaN operand the LangRef does leave the result
     non-deterministic: the intrinsic may "return a NaN" or "treat the
     signaling NaN as a quiet NaN".  We resolve that by returning a NaN, which
     keeps the sNaN behaviour the tests in tests/llvm-arith/double already pin
     down.  Once NaN choices become draw events this is the branch point.

     The [Ceq] case is what implements "-0.0 is less than +0.0": for equal
     non-zero operands either answer is the same value, and for the +0.0/-0.0
     pair it picks the positive one regardless of argument order. *)
  Definition Float_maxnum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl64 pl then b else build_nan _ _ (binop_nan_pl64 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl64 pl then a else build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Ceq a b
      then (if Bsign _ _ a then b else a)
      else (if Float.cmp Clt a b then b else a)
    end.

  Definition Float32_maxnum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl32 pl then b else build_nan _ _ (binop_nan_pl32 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl32 pl then a else build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Ceq a b
      then (if Bsign _ _ a then b else a)
      else (if Float32.cmp Clt a b then b else a)
    end.

  Definition llvm_maxnum_f64 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => retr (DVALUE_Double (Float_maxnum a b))
      | _ => raise_error "llvm_maxnum_f64 got incorrect / ill-typed inputs"
      end.

  Definition llvm_maxnum_f32 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => retr (DVALUE_Float (Float32_maxnum a b))
      | _ => raise_error "llvm_maxnum_f32 got incorrect / ill-typed inputs"
      end.

  (* LANGREF (llvm.minimum): "If either operand is a NaN, returns a NaN.
     Otherwise returns the lesser of the two arguments. -0.0 is considered to
     be less than +0.0 for this intrinsic."

     Unlike [llvm.maxnum], propagating a NaN operand is the specified
     behaviour, so only the signed-zero case needed fixing here. *)
  Definition Float_minimum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Ceq a b
      then (if Bsign _ _ a then a else b)
      else (if Float.cmp Clt a b then a else b)
    end.

  Definition Float32_minimum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Ceq a b
      then (if Bsign _ _ a then a else b)
      else (if Float32.cmp Clt a b then a else b)
    end.

  Definition llvm_minimum_f64 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => retr (DVALUE_Double (Float_minimum a b))
      | _ => raise_error "llvm_minimum_f64 got incorrect / ill-typed inputs"
      end.

  Definition llvm_minimum_f32 : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => retr (DVALUE_Float (Float32_minimum a b))
      | _ => raise_error "llvm_minimum_f32 got incorrect / ill-typed inputs"
      end.

  (* Saturated arithmetic: https://llvm.org/docs/LangRef.html#saturation-arithmetic-intrinsics *)
  Definition ushl_sat {I : Type} `{TDI : ToDvalueBase I} `{VMI : VMemInt I} (x y : I) : EOU dvalue_base :=
    res <- mshl x y;;
    let res_u := munsigned res in
    let res_u' := Z.shiftl (munsigned x) (munsigned y) in
    if option_pred (fun bw => munsigned y >=? Zpos bw) (@mbitwidth I VMI)
    then ret DVALUE_Poison
    else
      if (res_u' >? res_u)
      then 
        match (@mmax_unsigned I VMI) with
        | None =>
            raise_error "ushl_sat issue with unbounded integer type."
        | Some m =>
            match mrepr m with
            | raise_oom _ =>
                raise_error "ushl_sat: cannot represent maximum value in type... Should not happen."
            (* Note: we have enlarged the monad, so that statically we don't rule out new absurd cases such as failure or ub *)
            | m => tdb <$> m
            end
        end
      else ret (tdb res).

  Definition llvm_ushl_sat_1: pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 1 a; DVALUE_I 1 b] => inr <$> ushl_sat a b
      | _ => raise_error "llvm_ushl_sat_1 got incorrect / ill-typed inputs"
      end.

  Definition llvm_ushl_sat_8: pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 8 a; DVALUE_I 8 b] => inr <$> ushl_sat a b
      | _ => raise_error "llvm_ushl_sat_8 got incorrect / ill-typed inputs"
      end.

  Definition llvm_ushl_sat_16: pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 16 a; DVALUE_I 16 b] => inr <$> ushl_sat a b
      | _ => raise_error "llvm_ushl_sat_16 got incorrect / ill-typed inputs"
      end.

  Definition llvm_ushl_sat_32: pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 32 a; DVALUE_I 32 b] => inr <$> ushl_sat a b
      | _ => raise_error "llvm_ushl_sat_32 got incorrect / ill-typed inputs"
      end.

  Definition llvm_ushl_sat_64: pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 64 a; DVALUE_I 64 b] => inr <$> ushl_sat a b
      | _ => raise_error "llvm_ushl_sat_64 got incorrect / ill-typed inputs"
      end.

  Definition llvm_vellvm_internal_throw : pure_base_function :=
    fun args =>
      match args with
      (* Raise: the [inl] branch of the intrinsic's [exc + dvalue] result is
         turned into an abortive [LLVMExc] by [denote_instr]. The payload is a
         placeholder panic object, treated opaquely by the unwind machinery. *)
      | [] => ret (inl DVALUE_None)
      | _ => raise_error "llvm_vellvm_internal_throw got incorrect / ill-typed inputs"
      end.

  (* LangRef (llvm.assume): "If the condition is violated during execution,
     the behavior is undefined."  Its operand bundles belong to the call, not
     to the intrinsic: [denote_operand_bundles] (Denotation.v) checks them. *)
  Definition llvm_assume : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 1 c] =>
          if equ c one then ret (inr DVALUE_None)
          else raise_ub "llvm.assume: the condition is false."
      | [DVALUE_Poison] => raise_ub "llvm.assume: the condition is poison."
      | _ => raise_error "llvm.assume got incorrect / ill-typed inputs"
      end.

  Definition llvm_va_start : semantic_function :=
    fun args varargs =>
      match args, varargs with
    | [ a ], Some varargs =>
        match a with
        | DVALUE_Base DVALUE_Poison => raiseUB ("Store to poisoned address in va_start.")
        | _ => store DTYPE_Pointer a (DVALUE_Pointer varargs);;
              retr (DVALUE_Base DVALUE_None)
        end
    | _, _ => raise "va_start: invalid arguments."
    end.
  
  Definition llvm_va_copy : semantic_function :=
    fun args varargs =>
      match args with
      | [dest; src] =>
          vargs <- load DTYPE_Pointer src;;
          store DTYPE_Pointer dest vargs;;
          retr (DVALUE_Base DVALUE_None)
      | _ => raise ": va_copy invalid arguments"
      end.

  Definition llvm_va_end  : semantic_function :=
    fun args varargs =>
      retr (DVALUE_Base DVALUE_None).

  Definition pure_base_to_pure : pure_base_function -> pure_function :=
    fun f args =>
      args' <- map_monad dvalue_to_dvalue_base args ;;
      ans <- f args' ;;
      match ans with
      | inr x => retr (DVALUE_Base x)
      | inl x => ret (inl (DVALUE_Base x))
      end.
  
  Definition pure_to_semantic : pure_function -> semantic_function :=
    fun f args _ => EOU_to_itree (f args).

  Definition pure_base_to_semantic : pure_base_function -> semantic_function :=
    fun f => pure_to_semantic (pure_base_to_pure f).

  (** IEEE-754-2008 [minNum], IEEE-754-2019 [maximum], and bitwise [copysign]. *)
  Definition Float_minnum (a b : float) : float :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl64 pl then b else build_nan _ _ (binop_nan_pl64 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl64 pl then a else build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
        if Float.cmp Ceq a b
        then (if Bsign _ _ a then a else b)
        else (if Float.cmp Clt a b then a else b)
    end.

  Definition Float32_minnum (a b : float32) : float32 :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl32 pl then b else build_nan _ _ (binop_nan_pl32 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl32 pl then a else build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
        if Float32.cmp Ceq a b
        then (if Bsign _ _ a then a else b)
        else (if Float32.cmp Clt a b then a else b)
    end.

  Definition Float_maximum (a b : float) : float :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
        if Float.cmp Ceq a b
        then (if Bsign _ _ a then b else a)
        else (if Float.cmp Clt a b then b else a)
    end.

  Definition Float32_maximum (a b : float32) : float32 :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
        if Float32.cmp Ceq a b
        then (if Bsign _ _ a then b else a)
        else (if Float32.cmp Clt a b then b else a)
    end.

  Definition Float_copysign (a b : float) : float :=
    if Bsign _ _ b then Float.neg (Float.abs a) else Float.abs a.

  Definition Float32_copysign (a b : float32) : float32 :=
    if Bsign _ _ b then Float32.neg (Float32.abs a) else Float32.abs a.

  (** Poison-propagating pure intrinsic combinators. *)
  Definition is_f32_or_poison (v : dvalue_base) : bool :=
    match v with
    | DVALUE_Float _ | DVALUE_Poison => true
    | _ => false
    end.

  Definition is_f64_or_poison (v : dvalue_base) : bool :=
    match v with
    | DVALUE_Double _ | DVALUE_Poison => true
    | _ => false
    end.

  Definition is_int_sz_or_poison (sz : positive) (v : dvalue_base) : bool :=
    match v with
    | DVALUE_I w _ => Pos.eqb w sz
    | DVALUE_Poison => true
    | _ => false
    end.

  Definition llvm_f32_binop (err : string) (op : float32 -> float32 -> float32) : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2] =>
          match v1 with
          | DVALUE_Float a =>
              match v2 with
              | DVALUE_Float b => retr (DVALUE_Float (op a b))
              | DVALUE_Poison => retr DVALUE_Poison
              | _ => raise_error err
              end
          | DVALUE_Poison =>
              if is_f32_or_poison v2 then retr DVALUE_Poison else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_f64_binop (err : string) (op : float -> float -> float) : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2] =>
          match v1 with
          | DVALUE_Double a =>
              match v2 with
              | DVALUE_Double b => retr (DVALUE_Double (op a b))
              | DVALUE_Poison => retr DVALUE_Poison
              | _ => raise_error err
              end
          | DVALUE_Poison =>
              if is_f64_or_poison v2 then retr DVALUE_Poison else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_f32_ternop (err : string) (op : float32 -> float32 -> float32 -> float32)
    : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2; v3] =>
          match v1 with
          | DVALUE_Float a =>
              match v2 with
              | DVALUE_Float b =>
                  match v3 with
                  | DVALUE_Float c => retr (DVALUE_Float (op a b c))
                  | DVALUE_Poison => retr DVALUE_Poison
                  | _ => raise_error err
                  end
              | DVALUE_Poison =>
                  if is_f32_or_poison v3 then retr DVALUE_Poison else raise_error err
              | _ => raise_error err
              end
          | DVALUE_Poison =>
              if andb (is_f32_or_poison v2) (is_f32_or_poison v3)
              then retr DVALUE_Poison
              else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_f64_ternop (err : string) (op : float -> float -> float -> float)
    : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2; v3] =>
          match v1 with
          | DVALUE_Double a =>
              match v2 with
              | DVALUE_Double b =>
                  match v3 with
                  | DVALUE_Double c => retr (DVALUE_Double (op a b c))
                  | DVALUE_Poison => retr DVALUE_Poison
                  | _ => raise_error err
                  end
              | DVALUE_Poison =>
                  if is_f64_or_poison v3 then retr DVALUE_Poison else raise_error err
              | _ => raise_error err
              end
          | DVALUE_Poison =>
              if andb (is_f64_or_poison v2) (is_f64_or_poison v3)
              then retr DVALUE_Poison
              else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_minnum_f32 : pure_base_function :=
    llvm_f32_binop "llvm.minnum.f32 got incorrect / ill-typed inputs" Float32_minnum.
  Definition llvm_minnum_f64 : pure_base_function :=
    llvm_f64_binop "llvm.minnum.f64 got incorrect / ill-typed inputs" Float_minnum.
  Definition llvm_maximum_f32 : pure_base_function :=
    llvm_f32_binop "llvm.maximum.f32 got incorrect / ill-typed inputs" Float32_maximum.
  Definition llvm_maximum_f64 : pure_base_function :=
    llvm_f64_binop "llvm.maximum.f64 got incorrect / ill-typed inputs" Float_maximum.
  Definition llvm_copysign_f32 : pure_base_function :=
    llvm_f32_binop "llvm.copysign.f32 got incorrect / ill-typed inputs" Float32_copysign.
  Definition llvm_copysign_f64 : pure_base_function :=
    llvm_f64_binop "llvm.copysign.f64 got incorrect / ill-typed inputs" Float_copysign.
  Definition llvm_fma_f32 : pure_base_function :=
    llvm_f32_ternop "llvm.fma.f32 got incorrect / ill-typed inputs" Float32.fma.
  Definition llvm_fma_f64 : pure_base_function :=
    llvm_f64_ternop "llvm.fma.f64 got incorrect / ill-typed inputs" Float.fma.
  Definition llvm_fmuladd_f32 : pure_base_function :=
    llvm_f32_ternop "llvm.fmuladd.f32 got incorrect / ill-typed inputs" Float32.fma.
  Definition llvm_fmuladd_f64 : pure_base_function :=
    llvm_f64_ternop "llvm.fmuladd.f64 got incorrect / ill-typed inputs" Float.fma.

  Definition extra_fp_intrinsics : intrinsic_definitions :=
    [ (minnum_32_decl, pure_base_to_semantic llvm_minnum_f32);
      (minnum_64_decl, pure_base_to_semantic llvm_minnum_f64);
      (maximum_32_decl, pure_base_to_semantic llvm_maximum_f32);
      (maximum_64_decl, pure_base_to_semantic llvm_maximum_f64);
      (copysign_32_decl, pure_base_to_semantic llvm_copysign_f32);
      (copysign_64_decl, pure_base_to_semantic llvm_copysign_f64);
      (fma_32_decl, pure_base_to_semantic llvm_fma_f32);
      (fma_64_decl, pure_base_to_semantic llvm_fma_f64);
      (fmuladd_32_decl, pure_base_to_semantic llvm_fmuladd_f32);
      (fmuladd_64_decl, pure_base_to_semantic llvm_fmuladd_f64)
    ].

  (** Width-polymorphic integer intrinsic combinators. *)
  Definition llvm_int_unop (err : string) (sz : positive)
    (op : forall w : positive, @bit_int w -> @bit_int w) : pure_base_function :=
    fun args =>
      match args with
      | [v1] =>
          match v1 with
          | DVALUE_I w a =>
              if Pos.eqb w sz then retr (DVALUE_I w (op w a)) else raise_error err
          | DVALUE_Poison => retr DVALUE_Poison
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_int_unop_flag (err : string) (sz : positive)
    (op : forall w : positive, @bit_int w -> bool -> option (@bit_int w)) : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2] =>
          match v1 with
          | DVALUE_I w1 a =>
              if Pos.eqb w1 sz
              then
                match v2 with
                | DVALUE_I w2 flag =>
                    if Pos.eqb w2 1%positive
                    then
                      let b := negb (@Integers.eq w2 flag (@Integers.zero w2)) in
                      match op w1 a b with
                      | Some r => retr (DVALUE_I w1 r)
                      | None => retr DVALUE_Poison
                      end
                    else raise_error err
                | DVALUE_Poison => retr DVALUE_Poison
                | _ => raise_error err
                end
              else raise_error err
          | DVALUE_Poison =>
              if is_int_sz_or_poison 1%positive v2 then retr DVALUE_Poison else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_int_binop (err : string) (sz : positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w) : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2] =>
          match v1 with
          | DVALUE_I w1 a =>
              match Pos.eq_dec w1 sz with
              | left H1 =>
                  let a' := @eq_rect positive w1 (fun w => @bit_int w) a sz H1 in
                  match v2 with
                  | DVALUE_I w2 b =>
                      match Pos.eq_dec w2 sz with
                      | left H2 =>
                          let b' := @eq_rect positive w2 (fun w => @bit_int w) b sz H2 in
                          retr (DVALUE_I sz (op sz a' b'))
                      | right _ => raise_error err
                      end
                  | DVALUE_Poison => retr DVALUE_Poison
                  | _ => raise_error err
                  end
              | right _ => raise_error err
              end
          | DVALUE_Poison =>
              if is_int_sz_or_poison sz v2 then retr DVALUE_Poison else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_expect_int (err : string) (sz : positive) : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2] =>
          match v1 with
          | DVALUE_I w1 a =>
              if andb (Pos.eqb w1 sz) (is_int_sz_or_poison sz v2)
              then retr (DVALUE_I w1 a)
              else raise_error err
          | DVALUE_Poison =>
              if is_int_sz_or_poison sz v2 then retr DVALUE_Poison else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_int_ternop (err : string) (sz : positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w -> @bit_int w)
    : pure_base_function :=
    fun args =>
      match args with
      | [v1; v2; v3] =>
          match v1 with
          | DVALUE_I w1 a =>
              match Pos.eq_dec w1 sz with
              | left H1 =>
                  let a' := @eq_rect positive w1 (fun w => @bit_int w) a sz H1 in
                  match v2 with
                  | DVALUE_I w2 b =>
                      match Pos.eq_dec w2 sz with
                      | left H2 =>
                          let b' := @eq_rect positive w2 (fun w => @bit_int w) b sz H2 in
                          match v3 with
                          | DVALUE_I w3 c =>
                              match Pos.eq_dec w3 sz with
                              | left H3 =>
                                  let c' := @eq_rect positive w3 (fun w => @bit_int w) c sz H3 in
                                  retr (DVALUE_I sz (op sz a' b' c'))
                              | right _ => raise_error err
                              end
                          | DVALUE_Poison => retr DVALUE_Poison
                          | _ => raise_error err
                          end
                      | right _ => raise_error err
                      end
                  | DVALUE_Poison =>
                      if is_int_sz_or_poison sz v3 then retr DVALUE_Poison else raise_error err
                  | _ => raise_error err
                  end
              | right _ => raise_error err
              end
          | DVALUE_Poison =>
              if andb (is_int_sz_or_poison sz v2) (is_int_sz_or_poison sz v3)
              then retr DVALUE_Poison
              else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition llvm_int_ovf_binop (err : string) (sz : positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w * bool) : pure_function :=
    fun args =>
      args' <- map_monad dvalue_to_dvalue_base args ;;
      let poison_struct :=
        DVALUE_Struct false [DVALUE_Base DVALUE_Poison; DVALUE_Base DVALUE_Poison] in
      match args' with
      | [v1; v2] =>
          match v1 with
          | DVALUE_I w1 a =>
              match Pos.eq_dec w1 sz with
              | left H1 =>
                  let a' := @eq_rect positive w1 (fun w => @bit_int w) a sz H1 in
                  match v2 with
                  | DVALUE_I w2 b =>
                      match Pos.eq_dec w2 sz with
                      | left H2 =>
                          let b' := @eq_rect positive w2 (fun w => @bit_int w) b sz H2 in
                          let p := op sz a' b' in
                          let bit :=
                            if snd p then @Integers.one 1%positive else @Integers.zero 1%positive in
                          retr (DVALUE_Struct false
                                  [DVALUE_Base (DVALUE_I sz (fst p));
                                   DVALUE_Base (DVALUE_I 1%positive bit)])
                      | right _ => raise_error err
                      end
                  | DVALUE_Poison => retr poison_struct
                  | _ => raise_error err
                  end
              | right _ => raise_error err
              end
          | DVALUE_Poison =>
              if is_int_sz_or_poison sz v2 then retr poison_struct else raise_error err
          | _ => raise_error err
          end
      | _ => raise_error err
      end.

  Definition mk_int_unop_defs (op_name : string) (widths : list positive)
    (op : forall w : positive, @bit_int w -> @bit_int w) : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_unop_decl op_name sz,
          pure_base_to_semantic
            (llvm_int_unop ("llvm." ++ op_name ++ " got incorrect / ill-typed inputs")%string sz op)))
      widths.

  Definition mk_int_unop_flag_defs (op_name : string) (widths : list positive)
    (op : forall w : positive, @bit_int w -> bool -> option (@bit_int w)) : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_unop_flag_decl op_name sz,
          pure_base_to_semantic
            (llvm_int_unop_flag
               ("llvm." ++ op_name ++ " got incorrect / ill-typed inputs")%string sz op)))
      widths.

  Definition mk_int_binop_defs (op_name : string) (widths : list positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w) : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_binop_decl op_name sz,
          pure_base_to_semantic
            (llvm_int_binop ("llvm." ++ op_name ++ " got incorrect / ill-typed inputs")%string sz op)))
      widths.

  Definition mk_expect_int_defs (widths : list positive) : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_binop_decl "expect"%string sz,
          pure_base_to_semantic
            (llvm_expect_int "llvm.expect got incorrect / ill-typed inputs"%string sz)))
      widths.

  Definition mk_int_ternop_defs (op_name : string) (widths : list positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w -> @bit_int w)
    : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_ternop_decl op_name sz,
          pure_base_to_semantic
            (llvm_int_ternop
               ("llvm." ++ op_name ++ " got incorrect / ill-typed inputs")%string sz op)))
      widths.

  Definition mk_int_ovf_binop_defs (op_name : string) (widths : list positive)
    (op : forall w : positive, @bit_int w -> @bit_int w -> @bit_int w * bool)
    : intrinsic_definitions :=
    List.map
      (fun sz =>
         (int_ovf_binop_decl op_name sz,
          pure_to_semantic
            (llvm_int_ovf_binop
               ("llvm." ++ op_name ++ ".with.overflow got incorrect / ill-typed inputs")%string sz op)))
      widths.

  Definition extra_int_intrinsics : intrinsic_definitions :=
    (mk_int_binop_defs "smin"%string int_std_widths (@int_smin) ++
     mk_int_binop_defs "smax"%string int_std_widths (@int_smax) ++
     mk_int_binop_defs "umin"%string int_std_widths (@int_umin) ++
     mk_int_binop_defs "umax"%string int_std_widths (@int_umax) ++
     mk_int_unop_flag_defs "abs"%string int_std_widths (@int_abs) ++
     mk_int_binop_defs "uadd.sat"%string int_std_widths (@int_uadd_sat) ++
     mk_int_binop_defs "usub.sat"%string int_std_widths (@int_usub_sat) ++
     mk_int_binop_defs "sadd.sat"%string int_std_widths (@int_sadd_sat) ++
     mk_int_binop_defs "ssub.sat"%string int_std_widths (@int_ssub_sat) ++
     mk_int_ovf_binop_defs "uadd"%string int_std_widths (@int_uadd_ovf) ++
     mk_int_ovf_binop_defs "usub"%string int_std_widths (@int_usub_ovf) ++
     mk_int_ovf_binop_defs "umul"%string int_std_widths (@int_umul_ovf) ++
     mk_int_ovf_binop_defs "sadd"%string int_std_widths (@int_sadd_ovf) ++
     mk_int_ovf_binop_defs "ssub"%string int_std_widths (@int_ssub_ovf) ++
     mk_int_ovf_binop_defs "smul"%string int_std_widths (@int_smul_ovf) ++
     mk_int_unop_defs "ctpop"%string int_std_widths (@int_ctpop) ++
     mk_int_unop_flag_defs "ctlz"%string int_std_widths (@int_ctlz) ++
     mk_int_unop_flag_defs "cttz"%string int_std_widths (@int_cttz) ++
     mk_int_unop_defs "bswap"%string int_bswap_widths (@int_bswap) ++
     mk_int_ternop_defs "fshl"%string int_std_widths (@int_fshl) ++
     mk_int_ternop_defs "fshr"%string int_std_widths (@int_fshr) ++
     mk_expect_int_defs int_expect_widths)%list.

  (* Clients of Vellvm can register the names of their own intrinsics
     definitions here. *)
  Definition defined_intrinsics : intrinsic_definitions :=
    ([ (fabs_32_decl, pure_base_to_semantic llvm_fabs_f32) ;
       (fabs_64_decl, pure_base_to_semantic llvm_fabs_f64) ;
       (maxnum_32_decl , pure_base_to_semantic llvm_maxnum_f32) ;
       (maxnum_64_decl , pure_base_to_semantic llvm_maxnum_f64);
       (minimum_32_decl, pure_base_to_semantic llvm_minimum_f32);
       (minimum_64_decl, pure_base_to_semantic llvm_minimum_f64);
       (ushl_sat_1_decl, pure_base_to_semantic llvm_ushl_sat_1);
       (ushl_sat_8_decl, pure_base_to_semantic llvm_ushl_sat_8);
       (ushl_sat_16_decl, pure_base_to_semantic llvm_ushl_sat_16);
       (ushl_sat_32_decl, pure_base_to_semantic llvm_ushl_sat_32);
       (ushl_sat_64_decl, pure_base_to_semantic llvm_ushl_sat_64) ] ++
     extra_fp_intrinsics ++
     extra_int_intrinsics ++
     [ (vellvm_internal_throw_decl, pure_base_to_semantic llvm_vellvm_internal_throw);
       (assume_decl, pure_base_to_semantic llvm_assume);
       (va_start_decl, llvm_va_start);
       (va_end_decl, llvm_va_end);
       (va_copy_decl, llvm_va_copy)
     ])%list.

End Intrinsics.
