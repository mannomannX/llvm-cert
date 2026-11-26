(**
    These "Repr" instances for Vellvm should serialize Vellvm ASTs
    into a Rocq string which represents the AST, allowing ASTs to be
    serialized and read back into Rocq later.

*)

From Vellvm Require Import LLVMAst ShowAST Utils DynamicTypes.

From Stdlib Require Import List Ascii ZArith String.

Import ListNotations.

Set Warnings "-extraction-opaque-accessed,-extraction".

(* Class for the Rocq representation of a structure using tail-recursive reversed-char accumulation. *)
Class Repr A : Type :=
  {
    repr_acc : A -> list ascii -> list ascii
  }.

Definition repr {A : Type} `{Repr A} (a : A) : string :=
  rev_chars_to_string (repr_acc a []).

Section ReprInstances.

  Local Open Scope string.
  Local Infix "|>" := (fun x f => f x) (at level 50, left associativity).

  #[global]
   Instance reprList (A : Type) `{Repr A} : Repr (list A) :=
    {
      repr_acc l acc :=
        acc |> push_str_rev "[" |> push_sep_rev "; " repr_acc l |> push_str_rev "]"
    }.

  #[global]
   Instance reprInt : Repr LLVMAst.int_ast :=
    {
      repr_acc i acc :=
        acc |> push_str_rev "(" |> push_Z_rev i |> push_str_rev ")%Z"
    }.

  #[global]
   Instance reprBool : Repr bool :=
    {
      repr_acc := push_bool_rev
    }.

  #[global]
    Instance reprUnit : Repr unit :=
    {
      repr_acc _ acc := push_str_rev "tt" acc
    }.

  #[global]
   Instance reprString : Repr string
    := {| repr_acc := push_quoted_string_rev |}.

  Definition repr_raw_id_acc (rid : raw_id) (acc : list ascii) : list ascii
    := match rid with
       | Name s => acc |> push_str_rev "(Name " |> repr_acc s |> push_str_rev ")"
       | Anon i => acc |> push_str_rev "(Anon " |> repr_acc i |> push_str_rev ")"
       | Raw i  => acc |> push_str_rev "(Raw " |> repr_acc i |> push_str_rev ")"
       end.

  #[global]
   Instance reprRawId : Repr raw_id
    := {| repr_acc := repr_raw_id_acc |}.

  Definition repr_ident_acc (i : ident) (acc : list ascii) : list ascii
    := match i with
       | ID_Global r => acc |> push_str_rev "(ID_Global " |> repr_acc r |> push_str_rev ")"
       | ID_Local r  => acc |> push_str_rev "(ID_Local " |> repr_acc r |> push_str_rev ")"
       end.

  #[global]
   Instance reprIdent : Repr ident
    := {| repr_acc := repr_ident_acc |}.

  #[global]
   Instance reprN : Repr N
    := {| repr_acc := push_N_rev |}.

  #[global]
   Instance reprPos : Repr positive
    := {| repr_acc p acc := push_str_rev (show p) acc |}.

  Definition repr_file_info_acc (f : file_info) (acc : list ascii) : list ascii :=
    acc |> push_str_rev "(mk_file_info "
        |> push_str_rev """"
        |> push_str_rev f.(filename)
        |> push_str_rev """ "
        |> repr_acc f.(start_line) |> push_str_rev " "
        |> repr_acc f.(start_col)  |> push_str_rev " "
        |> repr_acc f.(end_line)   |> push_str_rev " "
        |> repr_acc f.(end_col)    |> push_str_rev ")".

  #[global]
   Instance reprFile_info : Repr file_info := {| repr_acc := repr_file_info_acc |}.

  Definition repr_fp_variant (fp : floating_point_variant) : string :=
    match fp with
    | FP_half => "FP_half"
    | FP_bfloat => "FP_bfloat"
    | FP_float  => "FP_float"
    | FP_double => "FP_double"
    | FP_fp128 => "FP_fp128"
    | FP_x86_fp80 => "FP_x86_fp80"
    | FP_ppc_fp128 => "FP_ppc_fp128"
    end.

  #[global]
  Instance repr_floating_point_variant : Repr floating_point_variant
   := {| repr_acc fp acc := push_str_rev (repr_fp_variant fp) acc |}.

  Definition repr_dtyp_base_acc (t : dtyp_base) (acc : list ascii) : list ascii :=
    match t with
    | DTYPE_I sz => acc |> push_str_rev "(DTYPE_I " |> repr_acc sz |> push_str_rev ")"
    | DTYPE_Iptr => push_str_rev "DTYPE_Iptr" acc
    | DTYPE_Pointer => push_str_rev "DTYPE_Pointer" acc
    | DTYPE_Void => push_str_rev "DTYPE_Void" acc
    | DTYPE_FP fp => acc |> push_str_rev "(DTYPE_FP " |> repr_acc fp |> push_str_rev ")"
    | DTYPE_Label => push_str_rev "DTYPE_Label" acc
    | DTYPE_Token => push_str_rev "DTYPE_Token" acc
    | DTYPE_Metadata => push_str_rev "DTYPE_Metadata" acc
    | DTYPE_X86_mmx => push_str_rev "DTYPE_X86_mmx" acc
    | DTYPE_Opaque => push_str_rev "DTYPE_Opaque" acc
    | DTYPE_B sz => acc |> push_str_rev "(DTYPE_B " |> repr_acc sz |> push_str_rev ")"
    end.

  #[global]
  Instance repr_dtyp_base_Repr : Repr dtyp_base :=
    {| repr_acc := repr_dtyp_base_acc |}.

  Fixpoint repr_dtyp_acc (t : dtyp) (acc : list ascii) : list ascii :=
    let fix go_fields (first : bool) (xs : list dtyp) (a : list ascii) {struct xs} : list ascii :=
      match xs with
      | [] => a
      | f :: rest =>
          let a1 := if first then a else push_str_rev "; " a in
          go_fields false rest (repr_dtyp_acc f a1)
      end in
    match t with
    | DTYPE_Base tb => acc |> push_str_rev "(DTYPE_Base (" |> repr_acc tb |> push_str_rev "))"
    | DTYPE_Struct p fields =>
        acc |> push_str_rev "(DTYPE_Struct " |> repr_acc p |> push_str_rev " ["
            |> go_fields true fields |> push_str_rev "])"
    | DTYPE_Array v sz t' =>
        acc |> push_str_rev "(DTYPE_Array " |> repr_acc v |> push_str_rev " ("
            |> repr_acc sz |> push_str_rev ") (" |> repr_dtyp_acc t' |> push_str_rev "))"
    end.

  Definition repr_dtyp (t : dtyp) : string :=
    rev_chars_to_string (repr_dtyp_acc t []).

  Fixpoint repr_typ_acc (t : typ) (acc : list ascii) : list ascii :=
    let fix go_typs (first : bool) (xs : list typ) (a : list ascii) {struct xs} : list ascii :=
      match xs with
      | [] => a
      | ty :: rest =>
          let a1 := if first then a else push_str_rev "; " a in
          go_typs false rest (repr_typ_acc ty a1)
      end in
    match t with
    | TYPE_I sz                 => acc |> push_str_rev "(TYPE_I " |> repr_acc sz |> push_str_rev ")"
    | TYPE_B sz                 => acc |> push_str_rev "(TYPE_B " |> repr_acc sz |> push_str_rev ")"
    | TYPE_Iptr                 => push_str_rev "TYPE_Iptr" acc
    | TYPE_Pointer (Some t')    => acc |> push_str_rev "(TYPE_Pointer (Some " |> repr_typ_acc t' |> push_str_rev "))"
    | TYPE_Pointer None         => push_str_rev "(TYPE_Pointer None)" acc
    | TYPE_Void                 => push_str_rev "TYPE_Void" acc
    | TYPE_FP fp                => acc |> push_str_rev "(TYPE_FP " |> repr_acc fp |> push_str_rev ")"
    | TYPE_Label                => push_str_rev "TYPE_Label" acc
    | TYPE_Token                => push_str_rev "TYPE_Token" acc
    | TYPE_Metadata             => push_str_rev "TYPE_Metadata" acc
    | TYPE_X86_mmx              => push_str_rev "TYPE_X86_mmx" acc
    | TYPE_Array sz t'          => acc |> push_str_rev "(TYPE_Array (" |> repr_acc sz |> push_str_rev ") (" |> repr_typ_acc t' |> push_str_rev "))"
    | TYPE_Function ret args varargs
      => acc |> push_str_rev "(TYPE_Function (" |> repr_typ_acc ret
             |> push_str_rev ")
        ["
             |> go_typs true args
             |> push_str_rev "] "
             |> push_str_rev (if varargs then "true" else "false")
             |> push_str_rev ")"
    | TYPE_Struct fields        => acc |> push_str_rev "(TYPE_Struct [" |> go_typs true fields |> push_str_rev "])"
    | TYPE_Packed_struct fields => acc |> push_str_rev "(TYPE_Packed_struct [" |> go_typs true fields |> push_str_rev "])"
    | TYPE_Opaque               => push_str_rev "TYPE_Opaque" acc
    | TYPE_Vector sz t'         => acc |> push_str_rev "(TYPE_Vector (" |> repr_acc sz |> push_str_rev ") (" |> repr_typ_acc t' |> push_str_rev "))"
    | TYPE_Identified id        => acc |> push_str_rev "(TYPE_Identified " |> repr_acc id |> push_str_rev ")"
    end.

  Definition repr_typ (t : typ) : string :=
    rev_chars_to_string (repr_typ_acc t []).

  #[global]
   Instance reprTyp : Repr typ :=
    {|
      repr_acc := repr_typ_acc
    |}.

  Definition repr_ibinop_acc (iop : ibinop) (acc : list ascii) : list ascii
    := match iop with
       (* TODO print flags *)
       | LLVMAst.Add a b => acc |> push_str_rev "(LLVMAst.Add " |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
       | Sub a b => acc |> push_str_rev "(Sub " |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
       | Mul a b => acc |> push_str_rev "(Mul " |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
       | Shl a b => acc |> push_str_rev "(Shl " |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
       | UDiv f  => acc |> push_str_rev "(UDiv " |> repr_acc f |> push_str_rev ")"
       | SDiv f  => acc |> push_str_rev "(SDiv " |> repr_acc f |> push_str_rev ")"
       | LShr f  => acc |> push_str_rev "(LShr " |> repr_acc f |> push_str_rev ")"
       | AShr f  => acc |> push_str_rev "(AShr " |> repr_acc f |> push_str_rev ")"
       | URem    => push_str_rev "URem" acc
       | SRem    => push_str_rev "SRem" acc
       | And     => push_str_rev "And" acc
       | Or dj   => acc |> push_str_rev "(Or " |> repr_acc dj |> push_str_rev ")"
       | Xor     => push_str_rev "Xor" acc
       end.

  #[global]
   Instance reprIBinop : Repr ibinop
    := {| repr_acc := repr_ibinop_acc |}.

  Definition repr_gep_flags_acc (f : gep_flags) (acc : list ascii) : list ascii :=
    acc |> push_str_rev "(mk_gep_flags " |> repr_acc (gep_inbounds f) |> push_str_rev " "
        |> repr_acc (gep_nusw f) |> push_str_rev " "
        |> repr_acc (gep_nuw f) |> push_str_rev ")".

  Definition repr_icmp (cmp : icmp) : string
    := match cmp with
       | Eq  => "Eq"
       | Ne  => "Ne"
       | Ugt => "Ugt"
       | Uge => "Uge"
       | Ult => "Ult"
       | Ule => "Ule"
       | Sgt => "Sgt"
       | Sge => "Sge"
       | Slt => "Slt"
       | Sle => "Sle"
       end.

  #[global]
   Instance reprICmp : Repr icmp
    := {| repr_acc cmp acc := push_str_rev (repr_icmp cmp) acc |}.

  #[global]
   Instance reprPair (A B : Type) `{Repr A} `{Repr B} : Repr (A * B) :=
    {|
      repr_acc p acc :=
        match p with
        | (a, b) => acc |> push_str_rev "(" |> repr_acc a |> push_str_rev ", " |> repr_acc b |> push_str_rev ")"
        end
    |}.

  Definition repr_fast_math (fm : fast_math) : string :=
    match fm with
    | Nnan => "Nnan"
    | Ninf => "Ninf"
    | Nsz => "Nsz"
    | Arcp => "Arcp"
    | Contract => "Contract"
    | Afn => "Afn"
    | Reassoc => "Reassoc"
    | Fast => "Fast"
    end.

  #[global]
   Instance reprFastMath : Repr fast_math :=
    {| repr_acc fm acc := push_str_rev (repr_fast_math fm) acc |}.

  Definition pair_repr {A B : Type} (fa : A -> string) (fb : B -> string) (ab : A * B) : string :=
    match ab with
    | (a, b) =>
      "(" ++ fa a ++ ", " ++ fb b ++ ")"
    end.

  Definition repr_pure_conversion_acc (ct : pure_conversion) (acc : list ascii) : list ascii :=
    match ct with
    | Trunc a b => acc |> push_str_rev "(Trunc " |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
    | Zext a => acc |> push_str_rev "(Zext " |> repr_acc a |> push_str_rev ")"
    | Sext => push_str_rev "Sext" acc
    | Fptrunc flags => acc |> push_str_rev "(Fptrunc " |> repr_acc flags |> push_str_rev ")"
    | Fpext flags => acc |> push_str_rev "(Fpext " |> repr_acc flags |> push_str_rev ")"
    | Uitofp a => acc |> push_str_rev "(Uitofp " |> repr_acc a |> push_str_rev ")"
    | Sitofp => push_str_rev "Sitofp" acc
    | Fptoui => push_str_rev "Fptoui" acc
    | Fptosi => push_str_rev "Fptosi" acc
    end.

  #[global] Instance ReprPureConversion : Repr pure_conversion :=
    {| repr_acc := repr_pure_conversion_acc |}.

  Definition repr_impure_conversion (ct : impure_conversion) : string :=
    match ct with
    | Inttoptr  => "Inttoptr "
    | Ptrtoint => "Ptrtoint"
    | Ptrtoaddr => "Ptrtoaddr"
    | Addrspacecast => "Addrspacecast"
    end.

  #[global] Instance ReprImpureConversion : Repr impure_conversion :=
    {| repr_acc ct acc := push_str_rev (repr_impure_conversion ct) acc |}.

  Definition repr_conversion_type_acc (ct : conversion_type) (acc : list ascii) : list ascii :=
    match ct with
    | CONV_Bitcast => push_str_rev "CONV_Bitcast" acc
    | CONV_Pure ct' => acc |> push_str_rev "(CONV_Pure " |> repr_acc ct' |> push_str_rev ")"
    | CONV_Impure ct' => acc |> push_str_rev "(CONV_Impure " |> repr_acc ct' |> push_str_rev ")"
    end.

  #[global]
   Instance reprConversionType : Repr conversion_type :=
    {| repr_acc := repr_conversion_type_acc |}.

  Definition repr_fbinop (f : fbinop) : string :=
    match f with
    | FAdd => "FAdd"
    | FSub => "FSub"
    | FMul => "FMul"
    | FDiv => "FDiv"
    | FRem => "FRem"
    end.

  #[global]
   Instance reprFBinop : Repr fbinop :=
    {| repr_acc f acc := push_str_rev (repr_fbinop f) acc |}.

  Definition repr_fcmp (f : fcmp) : string :=
    match f with
    | FFalse => "FFalse"
    | FOeq => "FOeq"
    | FOgt => "FOgt"
    | FOge => "FOge"
    | FOlt => "FOlt"
    | FOle => "FOle"
    | FOne => "FOne"
    | FOrd => "FOrd"
    | FUno => "FUno"
    | FUeq => "FUeq"
    | FUgt => "FUgt"
    | FUge => "FUge"
    | FUlt => "FUlt"
    | FUle => "FUle"
    | FUne => "FUne"
    | FTrue => "FTrue"
    end.

  #[global]
   Instance reprFCmp : Repr fcmp :=
    {| repr_acc f acc := push_str_rev (repr_fcmp f) acc |}.

  Fixpoint repr_Decimal_uint_go (depth : nat) (u : Decimal.uint) (acc : list ascii) : list ascii :=
    match u with
    | Decimal.Nil => acc |> push_str_rev "Decimal.Nil" |> push_chars_n ")"%char depth
    | Decimal.D0 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D0 " acc)
    | Decimal.D1 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D1 " acc)
    | Decimal.D2 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D2 " acc)
    | Decimal.D3 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D3 " acc)
    | Decimal.D4 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D4 " acc)
    | Decimal.D5 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D5 " acc)
    | Decimal.D6 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D6 " acc)
    | Decimal.D7 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D7 " acc)
    | Decimal.D8 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D8 " acc)
    | Decimal.D9 u' => repr_Decimal_uint_go (S depth) u' (push_str_rev "(Decimal.D9 " acc)
    end.

  Definition repr_Decimal_uint (u : Decimal.uint) : string :=
    rev_chars_to_string (repr_Decimal_uint_go 0 u []).

  #[global]
    Instance reprDecimalUINT : Repr Decimal.uint :=
    {| repr_acc := repr_Decimal_uint_go 0 |}.

  Definition repr_Decimal_signed_int_acc (d : Decimal.signed_int) (acc : list ascii) : list ascii :=
    match d with
    | Decimal.Pos u => acc |> push_str_rev "(Decimal.Pos " |> repr_acc u |> push_str_rev ")"
    | Decimal.Neg u => acc |> push_str_rev "(Decimal.Neg " |> repr_acc u |> push_str_rev ")"
    end.

  #[global]
    Instance reprDecimalSignedInt : Repr Decimal.signed_int :=
    {| repr_acc := repr_Decimal_signed_int_acc |}.

  Definition repr_Decimal_decimal_acc (d : Decimal.decimal) (acc : list ascii) : list ascii :=
    match d with
    | Decimal.Decimal i f =>
        acc |> push_str_rev "(Decimal.Decimal " |> repr_acc i |> push_str_rev " " |> repr_acc f |> push_str_rev ")"
    | Decimal.DecimalExp i f e =>
        acc |> push_str_rev "(Decimal.DecimalExp " |> repr_acc i |> push_str_rev " "
            |> repr_acc f |> push_str_rev " " |> repr_acc e |> push_str_rev ")"
    end.

  #[global]
    Instance reprDecimalDecimal : Repr Decimal.decimal :=
    {| repr_acc := repr_Decimal_decimal_acc |}.

  Fixpoint repr_Hexadecimal_uint_go (depth : nat) (u : Hexadecimal.uint) (acc : list ascii) : list ascii :=
    match u with
    | Hexadecimal.Nil => acc |> push_str_rev "Hexadecimal.Nil" |> push_chars_n ")"%char depth
    | Hexadecimal.D0 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D0 " acc)
    | Hexadecimal.D1 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D1 " acc)
    | Hexadecimal.D2 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D2 " acc)
    | Hexadecimal.D3 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D3 " acc)
    | Hexadecimal.D4 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D4 " acc)
    | Hexadecimal.D5 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D5 " acc)
    | Hexadecimal.D6 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D6 " acc)
    | Hexadecimal.D7 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D7 " acc)
    | Hexadecimal.D8 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D8 " acc)
    | Hexadecimal.D9 u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.D9 " acc)
    | Hexadecimal.Da u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.Da " acc)
    | Hexadecimal.Db u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.Db " acc)
    | Hexadecimal.Dc u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.Dc " acc)
    | Hexadecimal.Dd u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.Dd " acc)
    | Hexadecimal.De u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.De " acc)
    | Hexadecimal.Df u' => repr_Hexadecimal_uint_go (S depth) u' (push_str_rev "(Hexadecimal.Df " acc)
    end.

  Definition repr_Hexadecimal_uint (u : Hexadecimal.uint) : string :=
    rev_chars_to_string (repr_Hexadecimal_uint_go 0 u []).

  #[global]
    Instance reprHexadecimalUINT : Repr Hexadecimal.uint :=
    {| repr_acc := repr_Hexadecimal_uint_go 0 |}.

  Definition repr_Hexadecimal_signed_int_acc (d : Hexadecimal.signed_int) (acc : list ascii) : list ascii :=
    match d with
    | Hexadecimal.Pos u => acc |> push_str_rev "(Hexadecimal.Pos " |> repr_acc u |> push_str_rev ")"
    | Hexadecimal.Neg u => acc |> push_str_rev "(Hexadecimal.Neg " |> repr_acc u |> push_str_rev ")"
    end.

  #[global]
    Instance reprHexadecimalSignedInt : Repr Hexadecimal.signed_int :=
    {| repr_acc := repr_Hexadecimal_signed_int_acc |}.

  Definition repr_Number_signed_int_acc (n : Number.signed_int) (acc : list ascii) : list ascii :=
    match n with
    | Number.IntDecimal i => acc |> push_str_rev "(Number.IntDecimal " |> repr_acc i |> push_str_rev ")"
    | Number.IntHexadecimal i => acc |> push_str_rev "(Number.IntHexadecimal " |> repr_acc i |> push_str_rev ")"
    end.

  #[global]
    Instance reprNumberSignedInt : Repr Number.signed_int :=
    {| repr_acc := repr_Number_signed_int_acc |}.

  Definition repr_int_syntax_acc (n : int_syntax) (acc : list ascii) : list ascii :=
    repr_Number_signed_int_acc n acc.

  #[global]
    Instance reprIntSyntax : Repr int_syntax :=
    {| repr_acc := repr_int_syntax_acc |}.

  Definition repr_float_hex_type (fp : float_hex_type) : string :=
    match fp with
    | FH_X => "FH_X"
    | FH_K => "FH_K"
    | FH_L => "FH_L"
    | FH_M => "FH_M"
    | FH_H => "FH_H"
    | FH_R => "FH_R"
    end.

  #[global]
    Instance reprFloatHexType : Repr float_hex_type :=
    {| repr_acc fp acc := push_str_rev (repr_float_hex_type fp) acc |}.

  Definition repr_float_syntax_acc (f : float_syntax) (acc : list ascii) : list ascii :=
    match f with
    | FS_decimal d => acc |> push_str_rev "(FS_decimal " |> repr_acc d |> push_str_rev ")"
    | FS_hex t u => acc |> push_str_rev "(FS_hex " |> repr_acc t |> push_str_rev " " |> repr_acc u |> push_str_rev ")"
    end.

  #[global]
    Instance reprFloatSyntax : Repr float_syntax :=
    {| repr_acc := repr_float_syntax_acc |}.

  Fixpoint repr_exp_acc (v : exp typ) (acc : list ascii) {struct v} : list ascii :=
    let fix go_texps (first : bool) (xs : list (typ * exp typ)) (a : list ascii) {struct xs} : list ascii :=
      match xs with
      | [] => a
      | (t, e) :: rest =>
          let a1 := if first then a else push_str_rev "; " a in
          go_texps false rest
            (a1 |> push_str_rev "(" |> repr_typ_acc t |> push_str_rev ", " |> repr_exp_acc e |> push_str_rev ")")
      end in
    let push_texp (te : typ * exp typ) (a : list ascii) : list ascii :=
      let '(t, e) := te in
      a |> push_str_rev "(" |> repr_typ_acc t |> push_str_rev ", " |> repr_exp_acc e |> push_str_rev ")" in
    match v with
    | EXP_Ident id => acc |> push_str_rev "(EXP_Ident " |> repr_acc id |> push_str_rev ")"
    | EXP_Integer x => acc |> push_str_rev "(EXP_Integer " |> repr_acc x |> push_str_rev ")"
    | EXP_Float f  => acc |> push_str_rev "(EXP_Float " |> repr_acc f |> push_str_rev ")"
    | EXP_Bool b => acc |> push_str_rev "(EXP_Bool " |> repr_acc b |> push_str_rev ")"
    | EXP_Null => push_str_rev "EXP_Null" acc
    | EXP_Zero_initializer => push_str_rev "EXP_Zero_initializer" acc
    | EXP_Cstring s => acc |> push_str_rev "(EXP_Cstring [" |> go_texps true s |> push_str_rev "])"
    | EXP_Undef => push_str_rev "EXP_Undef" acc
    | EXP_Poison => push_str_rev "EXP_Poison" acc
    | EXP_Struct fields => acc |> push_str_rev "(EXP_Struct [" |> go_texps true fields |> push_str_rev "])"
    | EXP_Packed_struct fields => acc |> push_str_rev "(EXP_Packed_struct [" |> go_texps true fields |> push_str_rev "])"
    | EXP_Array fields => acc |> push_str_rev "(EXP_Array [" |> go_texps true fields |> push_str_rev "])"
    | EXP_Vector fields => acc |> push_str_rev "(EXP_vector [" |> go_texps true fields |> push_str_rev "])"
    | OP_IBinop iop t v1 v2 =>
        acc |> push_str_rev "(OP_IBinop " |> repr_acc iop |> push_str_rev " " |> repr_acc t
            |> push_str_rev " " |> repr_exp_acc v1 |> push_str_rev " " |> repr_exp_acc v2 |> push_str_rev ")"
    | OP_ICmp s cmp t v1 v2 =>
        acc |> push_str_rev "(OP_ICmp " |> repr_acc s |> push_str_rev " " |> repr_acc cmp
            |> push_str_rev " " |> repr_acc t |> push_str_rev " " |> repr_exp_acc v1
            |> push_str_rev " " |> repr_exp_acc v2 |> push_str_rev ")"
    | OP_FBinop fop fm t v1 v2 =>
        acc |> push_str_rev "(OP_FBinop " |> repr_acc fop |> push_str_rev " ["
            |> push_sep_rev "; " repr_acc fm |> push_str_rev "] " |> repr_acc t
            |> push_str_rev " " |> repr_exp_acc v1 |> push_str_rev " " |> repr_exp_acc v2 |> push_str_rev ")"
    | OP_Fneg fm v' =>
        acc |> push_str_rev "(OP_Fneg [" |> push_sep_rev "; " repr_acc fm
            |> push_str_rev "] " |> push_texp v' |> push_str_rev ")"
    | OP_FCmp cmp fm t v1 v2 =>
        acc |> push_str_rev "(OP_FCmp " |> repr_acc cmp |> push_str_rev " ["
            |> push_sep_rev "; " repr_acc fm |> push_str_rev "] " |> repr_acc t
            |> push_str_rev " " |> repr_exp_acc v1 |> push_str_rev " " |> repr_exp_acc v2 |> push_str_rev ")"
    | OP_Conversion c from v' to =>
        acc |> push_str_rev "(OP_Conversion " |> repr_acc c |> push_str_rev " " |> repr_acc from
            |> push_str_rev " " |> repr_exp_acc v' |> push_str_rev " " |> repr_acc to |> push_str_rev ")"
    | OP_GetElementPtr flags t ptrval idxs =>
        acc |> push_str_rev "(OP_GetElementPtr " |> repr_gep_flags_acc flags |> push_str_rev " "
            |> repr_acc t |> push_str_rev "(" |> push_texp ptrval |> push_str_rev ") ["
            |> go_texps true idxs |> push_str_rev "])"
    | OP_ExtractElement v' i =>
        acc |> push_str_rev "(OP_ExtractElement " |> push_texp v' |> push_str_rev " " |> push_texp i |> push_str_rev ")"
    | OP_InsertElement v' e i =>
        acc |> push_str_rev "(OP_ExtractElement " |> push_texp v' |> push_str_rev " "
            |> push_texp e |> push_str_rev " " |> push_texp i |> push_str_rev ")"
    | OP_ShuffleVector v1 v2 mask =>
        acc |> push_str_rev "(OP_ShuffleVector " |> push_texp v1 |> push_str_rev " "
            |> push_texp v2 |> push_str_rev " " |> push_texp mask |> push_str_rev ")"
    | OP_ExtractValue v' idxs =>
        acc |> push_str_rev "(OP_ExtractValue " |> push_texp v' |> push_str_rev " ["
            |> push_sep_rev "; " (fun x a => push_str_rev (show x) a) idxs |> push_str_rev "])"
    | OP_InsertValue v' e idxs =>
        acc |> push_str_rev "(OP_ExtractValue " |> push_texp v' |> push_str_rev " "
            |> push_texp e |> push_str_rev " ["
            |> push_sep_rev "; " (fun x a => push_str_rev (show x) a) idxs |> push_str_rev "])"
    | OP_Select fm cnd v1 v2 =>
        acc |> push_str_rev "(OP_Select [" |> push_sep_rev "; " repr_acc fm |> push_str_rev "] "
            |> push_texp cnd |> push_str_rev " " |> push_texp v1 |> push_str_rev " " |> push_texp v2 |> push_str_rev ")"
    | OP_Freeze v' =>
        acc |> push_str_rev "(OP_Freeze " |> push_texp v' |> push_str_rev ")"
    | EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints =>
        acc |> push_str_rev "(EXP_Asm "
            |> repr_acc sideffect |> push_str_rev " "
            |> repr_acc alignstack |> push_str_rev " "
            |> repr_acc inteldialect |> push_str_rev " "
            |> repr_acc unwind |> push_str_rev " "
            |> push_str_rev """" |> push_str_rev template |> push_str_rev """ "
            |> push_str_rev """" |> push_str_rev operand_constraints |> push_str_rev """)"
    | EXP_Metadata md =>
        acc |> push_str_rev "(EXP_Metadata " |> repr_metadata_acc md |> push_str_rev ")"
    | EXP_Splat elt =>
        acc |> push_str_rev "(EXP_splt " |> push_texp elt |> push_str_rev ")"
    | EXP_BlockAddress fn blk =>
        acc |> push_str_rev "(EXP_BlockAddress " |> repr_acc fn |> push_str_rev " " |> repr_acc blk |> push_str_rev ")"
    end with
  repr_metadata_acc (m : metadata typ) (acc : list ascii) {struct m} : list ascii :=
    let fix go_mds (first : bool) (xs : list (metadata typ)) (a : list ascii) {struct xs} : list ascii :=
      match xs with
      | [] => a
      | md :: rest =>
          let a1 := if first then a else push_str_rev "; " a in
          go_mds false rest (repr_metadata_acc md a1)
      end in
    match m with
    | METADATA_Null => push_str_rev "METADATA_Null" acc
    | METADATA_Const (t, e) =>
        acc |> push_str_rev "(METADATA_Const (" |> repr_typ_acc t |> push_str_rev ", "
            |> repr_exp_acc e |> push_str_rev "))"
    | METADATA_Id id => acc |> push_str_rev "(METADATA_Id " |> repr_acc id |> push_str_rev ")"
    | METADATA_Node mds => acc |> push_str_rev "(METADATA_Node [" |> go_mds true mds |> push_str_rev "])"
    | METADATA_Pair md1 md2 =>
        acc |> push_str_rev "(METADATA_Pair " |> repr_metadata_acc md1 |> push_str_rev " "
            |> repr_metadata_acc md2 |> push_str_rev ")"
    | METADATA_Debug s1 s2 =>
        acc |> push_str_rev "(METADATA_Debug " |> repr_acc s1 |> push_str_rev ", " |> repr_acc s2 |> push_str_rev ")"
    | METADATA_File_info f =>
        acc |> push_str_rev "(METADATA_File_info " |> repr_acc f |> push_str_rev ")"
    end.

  Definition repr_exp (v : exp typ) : string :=
    rev_chars_to_string (repr_exp_acc v []).

  Definition repr_metadata (m : metadata typ) : string :=
    rev_chars_to_string (repr_metadata_acc m []).

  #[global]
   Instance reprExp : Repr (exp typ)
    := {| repr_acc := repr_exp_acc |}.

  #[global]
   Instance reprTExp : Repr (texp typ)
    := {| repr_acc te acc :=
            match te with
            | (t, e) => acc |> push_str_rev "(" |> repr_acc t |> push_str_rev ", " |> repr_acc e |> push_str_rev ")"
            end
       |}.

  #[global]
   Instance reprMetadata : Repr (metadata typ) :=
    {| repr_acc := repr_metadata_acc |}.

  Definition repr_opt_acc {A} `{Repr A} (ma : option A) (acc : list ascii) : list ascii
    := match ma with
       | None   => push_str_rev "None" acc
       | Some a => acc |> push_str_rev "(Some " |> repr_acc a |> push_str_rev ")"
       end.

  #[global]
   Instance reprOption (A : Type) `{Repr A} : Repr (option A) :=
    {| repr_acc := repr_opt_acc |}.

  Definition repr_param_attr_acc (pa : param_attr) (acc : list ascii) : list ascii :=
    match pa with
    | PARAMATTR_Zeroext => push_str_rev "PARAMATTR_Zeroext" acc
    | PARAMATTR_Signext => push_str_rev "PARAMATTR_Signext" acc
    | PARAMATTR_Inreg => push_str_rev "PARAMATTR_Inreg" acc
    | PARAMATTR_Byval t => acc |> push_str_rev "PARAMATTR_Byval " |> repr_acc t
    | PARAMATTR_Byref t => acc |> push_str_rev "PARAMATTR_Byref " |> repr_acc t
    | PARAMATTR_Preallocated t => acc |> push_str_rev "PARAMATTR_Preallocated " |> repr_acc t
    | PARAMATTR_Inalloca t => acc |> push_str_rev "PARAMATTR_Inalloca " |> repr_acc t
    | PARAMATTR_Sret t => acc |> push_str_rev "PARAMATTR_Sret " |> repr_acc t
    | PARAMATTR_Elementtype t => acc |> push_str_rev "PARAMATTR_Elementtype " |> repr_acc t
    | PARAMATTR_Align a => acc |> push_str_rev "(PARAMATTR_Align " |> repr_acc a |> push_str_rev ")"
    | PARAMATTR_Noalias => push_str_rev "PARAMATTR_Noalias" acc
    | PARAMATTR_Nocapture => push_str_rev "PARAMATTR_Nocapture" acc
    | PARAMATTR_Nofree => push_str_rev "PARAMATTR_Nofree" acc
    | PARAMATTR_Nest => push_str_rev "PARAMATTR_Nest" acc
    | PARAMATTR_Returned => push_str_rev "PARAMATTR_Returned" acc
    | PARAMATTR_Nonnull => push_str_rev "PARAMATTR_Nonnull" acc
    | PARAMATTR_Dereferenceable a => acc |> push_str_rev "(PARAMATTR_Dereferenceable " |> repr_acc a |> push_str_rev ")"
    | PARAMATTR_Dereferenceable_or_null a => acc |> push_str_rev "(PARAMATTR_Dereferenceable_or_null " |> repr_acc a |> push_str_rev ")"
    | PARAMATTR_Swiftself => push_str_rev "PARAMATTR_Swiftself" acc
    | PARAMATTR_Swiftasync => push_str_rev "PARAMATTR_Swiftasync" acc
    | PARAMATTR_Swifterror => push_str_rev "PARAMATTR_Swifterror" acc
    | PARAMATTR_Immarg => push_str_rev "PARAMATTR_Immarg" acc
    | PARAMATTR_Noundef => push_str_rev "PARAMATTR_Noundef" acc
    | PARAMATTR_Nofpclass mask => acc |> push_str_rev "(PARAMATTR_Nofpclass " |> repr_acc mask |> push_str_rev ")"
    | PARAMATTR_Nofreeobj => push_str_rev "PARAMATTR_Nofreeobj" acc
    | PARAMATTR_Alignstack a => acc |> push_str_rev "PARAMATTR_Alignstack " |> repr_acc a
    | PARAMATTR_Allocalign => push_str_rev "PARAMATTR_Allocalign" acc
    | PARAMATTR_Allocptr => push_str_rev "PARAMATTR_Allocptr" acc
    | PARAMATTR_Readnone => push_str_rev "PARAMATTR_Readnone" acc
    | PARAMATTR_Readonly => push_str_rev "PARAMATTR_Readonly" acc
    | PARAMATTR_Writeonly => push_str_rev "PARAMATTR_Writeonly" acc
    | PARAMATTR_Writable => push_str_rev "PARAMATTR_Writable" acc
    | PARAMATTR_Dead_on_unwind => push_str_rev "PARAMATTR_Dead_on_unwind" acc
    | PARAMATTR_Dead_on_return size => acc |> push_str_rev "(PARAMATTR_Dead_on_return " |> repr_acc size |> push_str_rev ")"
    | PARAMATTR_Range t a b =>
        acc |> push_str_rev "(PARAMATTR_Range " |> repr_acc t |> push_str_rev " "
            |> repr_acc a |> push_str_rev " " |> repr_acc b |> push_str_rev ")"
    | PARAMATTR_Initializes l => acc |> push_str_rev "(PARAMATTR_Initializes " |> repr_acc l |> push_str_rev ")"
    | PARAMATTR_Captures p => acc |> push_str_rev "(PARAMATTR_Captures " |> repr_acc p |> push_str_rev ")"
    end.

  #[global]
   Instance reprParamAttr : Repr param_attr :=
    {| repr_acc := repr_param_attr_acc |}.

  Definition repr_linkage (l : linkage) : string :=
    match l with
    | LINKAGE_Private => "LINKAGE_Private"
    | LINKAGE_Internal => "LINKAGE_Internal"
    | LINKAGE_Available_externally => "LINKAGE_Available_externally"
    | LINKAGE_Linkonce => "LINKAGE_Linkonce"
    | LINKAGE_Weak => "LINKAGE_Weak"
    | LINKAGE_Common => "LINKAGE_Common"
    | LINKAGE_Appending => "LINKAGE_Appending"
    | LINKAGE_Extern_weak => "LINKAGE_Extern_weak"
    | LINKAGE_Linkonce_odr => "LINKAGE_Linkonce_odr"
    | LINKAGE_Weak_odr => "LINKAGE_Weak_odr"
    | LINKAGE_External => "LINKAGE_External"
    end.

  #[global]
   Instance reprLinkage : Repr linkage :=
    {| repr_acc l acc := push_str_rev (repr_linkage l) acc |}.

  Definition repr_visibility (v : visibility) : string :=
    match v with
    | VISIBILITY_Default => "VISIBILITY_Default"
    | VISIBILITY_Hidden => "VISIBILITY_Hidden"
    | VISIBILITY_Protected => "VISIBILITY_Protected"
    end.

  #[global]
   Instance reprVisibility : Repr visibility :=
    {| repr_acc v acc := push_str_rev (repr_visibility v) acc |}.

  Definition repr_dll_storage (d : dll_storage) : string :=
    match d with
    | DLLSTORAGE_Dllimport => "DLLSTORAGE_Dllimport"
    | DLLSTORAGE_Dllexport => "DLLSTORAGE_Dllexport"
    end.

  #[global]
   Instance reprDll_Storage : Repr dll_storage :=
    {| repr_acc d acc := push_str_rev (repr_dll_storage d) acc |}.

  Definition repr_cconv (c : cconv) : string :=
    match c with
    | CC_Ccc => "CC_Ccc"
    | CC_Fastcc => "CC_Fastcc"
    | CC_Coldcc => "CC_Coldcc"
    | CC_Cc cc => "CC_Cc cc"
    | CC_Webkit_jscc => "CC_Webkit_jscc"
    | CC_Anyregcc  => "CC_Anyregcc"
    | CC_Preserve_allcc => "CC_Preserve_allcc"
    | CC_Cxx_fast_tlscc =>  "CC_Cxx_fast_tlscc"
    | CC_Tailcc =>  "CC_Tailcc"
    | CC_Swiftcc => "CC_Swiftcc"
    | CC_Swifttailcc => "CC_Swifttailcc"
    | CC_cfguard_checkcc => "CC_cfguard_checkcc"
    | CC_Preserve_mostcc => "CC_Preserve_mostcc"
    end.

  #[global]
   Instance reprCconv : Repr cconv :=
    {| repr_acc c acc := push_str_rev (repr_cconv c) acc |}.

  Definition repr_mem_loc (loc : mem_loc) : string :=
    match loc with
    | LOC_Default => "LOC_Default"
    | LOC_Argmem => "LOC_Argmem"
    | LOC_Inaccessiblemem  => "LOC_Inaccessiblemem"
    | LOC_Errnomem => "LOC_Errnomem"
    end.

  #[global]
    Instance reprMemLoc : Repr mem_loc :=
    {| repr_acc loc acc := push_str_rev (repr_mem_loc loc) acc |}.

  Definition repr_mem_access_kind (k : mem_access_kind) : string :=
    match k with
    | ACC_None => "ACC_None"
    | ACC_Read => "ACC_Read"
    | ACC_Write => "ACC_Write"
    | ACC_Readwrite => "ACC_Readwrite"
    end.

  #[global]
    Instance reprMemAccessKind : Repr mem_access_kind :=
    {| repr_acc k acc := push_str_rev (repr_mem_access_kind k) acc |}.

  Definition repr_fn_attr_acc (fa : fn_attr) (acc : list ascii) : list ascii :=
    match fa with
    | FNATTR_Alignstack a => acc |> push_str_rev "(FNATTR_Alignstack " |> repr_acc a |> push_str_rev ")"
    | FNATTR_Allockind kind => acc |> push_str_rev "(FNATTR_Allockind " |> repr_acc kind |> push_str_rev ")"
    | FNATTR_Allocsize l l2 =>
        acc |> push_str_rev "(FNATTR_Allocsize " |> repr_acc l
            |> (match l2 with None => fun a => a | Some s => repr_acc s end)
            |> push_str_rev ")"
    | FNATTR_Alwaysinline => push_str_rev "FNATTR_Alwaysinline" acc
    | FNATTR_Builtin => push_str_rev "FNATTR_Builtin" acc
    | FNATTR_Cold => push_str_rev "FNATTR_Cold" acc
    | FNATTR_Convergent => push_str_rev "FNATTR_Convergent" acc
    | FNATTR_Disable_sanitizer_instrumentation => push_str_rev "FNATTR__Disable_sanitizer_instrumentation" acc
    | FNATTR_Fn_ret_thunk_extern => push_str_rev "FNATTR_Fn_ret_thunk_extern" acc
    | FNATTR_Hot => push_str_rev "FNATTR_Hot" acc
    | FNATTR_Inaccessiblememonly => push_str_rev "FNATTR_Inaccessiblememonly" acc
    | FNATTR_Inaccessiblemem_or_argmemonly => push_str_rev "FNATTR_Inaccessiblemem_or_argmemonly" acc
    | FNATTR_Inlinehint => push_str_rev "FNATTR_Inlinehint" acc
    | FNATTR_Jumptable => push_str_rev "FNATTR_Jumptable" acc
    | FNATTR_Minsize => push_str_rev "FNATTR_Minsize" acc
    | FNATTR_Naked => push_str_rev "FNATTR_Naked" acc
    | FNATTR_No_jump_tables => push_str_rev "FNATTR_No_jump_tables" acc
    | FNATTR_Nobuiltin => push_str_rev "FNATTR_Nobuiltin" acc
    | FNATTR_Noduplicate => push_str_rev "FNATTR_Noduplicate" acc
    | FNATTR_Nofree => push_str_rev "FNATTR_Nofree" acc
    | FNATTR_Noimplicitfloat => push_str_rev "FNATTR_Noimplicitfloat" acc
    | FNATTR_Noinline => push_str_rev "FNATTR_Noinline" acc
    | FNATTR_Nomerge => push_str_rev "FNATTR_Nomerge" acc
    | FNATTR_Nonlazybind => push_str_rev "FNATTR_Nonlazybind" acc
    | FNATTR_Noprofile => push_str_rev "FNATTR_Noprofile" acc
    | FNATTR_Noredzone => push_str_rev "FNATTR_Noredzone" acc
    | FNATTR_Indirect_tls_seg_refs => push_str_rev "FNATTR_Indirect_tls_seg_refs" acc
    | FNATTR_Noreturn => push_str_rev "FNATTR_Noreturn" acc
    | FNATTR_Norecurse => push_str_rev "FNATTR_Norecurse" acc
    | FNATTR_Willreturn => push_str_rev "FNATTR_Willreturn" acc
    | FNATTR_Nosync => push_str_rev "FNATTR_Nosync" acc
    | FNATTR_Nounwind => push_str_rev "FNATTR_Nounwind" acc
    | FNATTR_Nocreateundeforpoison => push_str_rev "FNATTR_Nocreateundeforpoison" acc
    | FNATTR_Nosanitize_bounds => push_str_rev "FNATTR_Nosanitize_bounds" acc
    | FNATTR_Nosanitize_coverage => push_str_rev "FNATTR_Nosanitize_coverage" acc
    | FNATTR_Null_pointer_is_valid => push_str_rev "FNATTR_Null_pointer_is_valid" acc
    | FNATTR_Optforfuzzing => push_str_rev "FNATTR_Optforfuzzing" acc
    | FNATTR_Optnone => push_str_rev "FNATTR_Optnone" acc
    | FNATTR_Optsize => push_str_rev "FNATTR_Optsize" acc
    | FNATTR_Readnone => push_str_rev "FNATTR_Readnone" acc
    | FNATTR_Readonly => push_str_rev "FNATTR_Readonly" acc
    | FNATTR_Writeonly => push_str_rev "FNATTR_Writeonly" acc
    | FNATTR_Argmemonly => push_str_rev "FNATTR_Argmemonly" acc
    | FNATTR_Returns_twice => push_str_rev "FNATTR_Returns_twice" acc
    | FNATTR_Safestack => push_str_rev "FNATTR_Safestack" acc
    | FNATTR_Sanitize_address => push_str_rev "FNATTR_Sanitize_address" acc
    | FNATTR_Sanitize_memory => push_str_rev "FNATTR_Sanitize_memory" acc
    | FNATTR_Sanitize_thread => push_str_rev "FNATTR_Sanitize_thread" acc
    | FNATTR_Sanitize_hwaddress => push_str_rev "FNATTR_Sanitize_hwaddress" acc
    | FNATTR_Sanitize_memtag => push_str_rev "FNATTR_Sanitize_memtag" acc
    | FNATTR_Speculative_load_hardening => push_str_rev "FNATTR_Speculative_load_hardening" acc
    | FNATTR_Speculatable => push_str_rev "FNATTR_Speculatable" acc
    | FNATTR_Ssp => push_str_rev "FNATTR_Ssp" acc
    | FNATTR_Sspreq => push_str_rev "FNATTR_Sspreq" acc
    | FNATTR_Sspstrong => push_str_rev "FNATTR_Sspstrong" acc
    | FNATTR_Strictfp => push_str_rev "FNATTR_Strictfp" acc
    | FNATTR_Tls_load_hoist => push_str_rev "FNATTR_Tls_load_hoist" acc
    | FNATTR_Uwtable sync => acc |> push_str_rev "FNATTR_Uwtable " |> repr_acc sync
    | FNATTR_Nocf_check => push_str_rev "FNATTR_Nocf_check" acc
    | FNATTR_Shadowcallstack => push_str_rev "FNATTR_Shadowcallstack" acc
    | FNATTR_Mustprogress => push_str_rev "FNATTR_Mustprogress" acc
    | FNATTR_Vscale_range min max =>
        acc |> push_str_rev "(FNATTR_Denormal_fp_math32 " |> repr_acc min
            |> (match max with None => fun a => a | Some s => repr_acc s end)
            |> push_str_rev ")"
    | FNATTR_String s => acc |> push_str_rev "(FNATTR_String " |> repr_acc s |> push_str_rev ")"
    | FNATTR_Key_value kv => acc |> push_str_rev "(FNATTR_Key_value " |> repr_acc kv |> push_str_rev ")"
    | FNATTR_Attr_grp g => acc |> push_str_rev "(FNATTR_Attr_grp " |> repr_acc g |> push_str_rev ")"
    | FNATTR_Memory l => acc |> push_str_rev "(FNATTR_Memory " |> repr_acc l |> push_str_rev ")"
    | FNATTR_UNKNOWN s => acc |> push_str_rev "(FNATTR_UNKNOWN " |> repr_acc s |> push_str_rev ")"
    end.

  #[global]
   Instance reprFn_Attr : Repr fn_attr :=
    {| repr_acc := repr_fn_attr_acc |}.

  Definition repr_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_NONE => "TLS_NONE"
    | TLS_Localdynamic => "TLS_Localdynamic"
    | TLS_Initialexec => "TLS_Initialexec"
    | TLS_Localexec => "TLS_Localexec"
    end.

  #[global]
   Instance reprThread_Local_Storage : Repr thread_local_storage :=
    {| repr_acc tls acc := push_str_rev (repr_thread_local_storage tls) acc |}.

  Definition repr_preemption_specifier (p : preemption_specifier) : string :=
    match p with
    | PREEMPTION_Dso_preemptable => "PREEMPTION_Dso_preemptable"
    | PREEMPTION_Dso_local => "PREEMPTION_Dso_local"
    end.

  #[global]
   Instance reprPremptionSpecifier : Repr preemption_specifier :=
    {| repr_acc p acc := push_str_rev (repr_preemption_specifier p) acc |}.

  Definition repr_unnamed_addr (u : unnamed_addr) : string :=
    match u with
    | Unnamed_addr => "Unnamed_addr"
    | Local_Unnamed_addr => "Local_Unnamed_addr"
    end.

  #[global]
   Instance reprUnnamedAddr : Repr unnamed_addr :=
    {| repr_acc u acc := push_str_rev (repr_unnamed_addr u) acc |}.

  Definition repr_tailcall (t : tailcall) : string :=
    match t with
    | Tail => "Tail"
    | Musttail => "Musttail"
    | Notail => "Notail"
    end.

  #[global]
   Instance reprTailcall : Repr tailcall :=
    {| repr_acc t acc := push_str_rev (show_tailcall t) acc |}.

  Definition repr_ordering (o : ordering) : string :=
    match o with
    | Unordered => "Unordered"
    | Monotonic => "Monotonic"
    | Acquire => "Acquire"
    | Release => "Release"
    | Acq_rel => "Acq_rel"
    | Seq_cst => "Seq_cst"
    end.

  #[global]
    Instance reprOrdering : Repr ordering :=
    {| repr_acc o acc := push_str_rev (repr_ordering o) acc |}.

  Definition repr_annotation_acc (a : annotation typ) (acc : list ascii) : list ascii :=
    match a with
    | ANN_linkage l => acc |> push_str_rev "ANN_linkage " |> repr_acc l
    | ANN_preemption_specifier p => acc |> push_str_rev "ANN_preemption_specifier " |> repr_acc p
    | ANN_visibility v => acc |> push_str_rev "ANN_visibility " |> repr_acc v
    | ANN_dll_storage d => acc |> push_str_rev "ANN_dll_storage " |> repr_acc d
    | ANN_thread_local_storage t => acc |> push_str_rev "ANN_thread_local_storage " |> repr_acc t
    | ANN_unnamed_addr u => acc |> push_str_rev "ANN_unnamed_addr " |> repr_acc u
    | ANN_addrspace n => acc |> push_str_rev "ANN_addrspace " |> repr_acc n
    | ANN_section s => acc |> push_str_rev "ANN_section " |> repr_acc s
    | ANN_partition s => acc |> push_str_rev "ANN_partition " |> repr_acc s
    | ANN_comdat l => acc |> push_str_rev "ANN_comdat " |> repr_acc l
    | ANN_align n => acc |> push_str_rev "ANN_align " |> repr_acc n
    | ANN_no_sanitize => push_str_rev "ANN_no_sanitize" acc
    | ANN_no_sanitize_address => push_str_rev "ANN_no_sanitize_address" acc
    | ANN_no_sanitize_hwaddress => push_str_rev "ANN_no_sanitize_hwaddress" acc
    | ANN_sanitize_address_dyninit => push_str_rev "ANN_sanitize_address_dyninit" acc
    | ANN_metadata m => acc |> push_str_rev "ANN_metadata " |> repr_acc m
    | ANN_cconv c => acc |> push_str_rev "ANN_cconv " |> repr_acc c
    | ANN_gc s => acc |> push_str_rev "ANN_gc " |> repr_acc s
    | ANN_prefix t => acc |> push_str_rev "ANN_prefix " |> repr_acc t
    | ANN_prologue t => acc |> push_str_rev "ANN_prologue " |> repr_acc t
    | ANN_personality t => acc |> push_str_rev "ANN_personality " |> repr_acc t
    | ANN_inalloca => push_str_rev "ANN_inalloca" acc
    | ANN_num_elements t => acc |> push_str_rev "ANN_num_elements " |> repr_acc t
    | ANN_volatile => push_str_rev "ANN_volatile" acc
    | ANN_tail t => acc |> push_str_rev "ANN_tail " |> repr_acc t
    | ANN_fast_math_flag f => acc |> push_str_rev "ANN_fast_math_flag " |> repr_acc f
    | ANN_ret_attribute r => acc |> push_str_rev "ANN_ret_attribute " |> repr_acc r
    | ANN_fun_attribute f => acc |> push_str_rev "ANN_fun_attribute " |> repr_acc f
    | ANN_atomic => push_str_rev "ANN_atomic" acc
    | ANN_syncscope s => acc |> push_str_rev "ANN_syncscope " |> repr_acc s
    | ANN_ordering o => acc |> push_str_rev "ANN_ordering " |> repr_acc o
    end.

  #[global]
   Instance reprAnnotation : Repr (annotation typ) :=
    {| repr_acc := repr_annotation_acc |}.

  Definition repr_atomic_rmw_operation (op : atomic_rmw_operation) : string :=
    match op with
    | Axchg => "Axchg"
    | Aadd => "Aadd"
    | Asub => "Asub"
    | Aand => "Aand"
    | Anand => "Anand"
    | Aor => "Aor"
    | Axor => "Axor"
    | Amax => "Amax"
    | Amin => "Amin"
    | Aumax => "Aumax"
    | Aumin => "Aumin"
    | Afadd => "Afadd"
    | Afsub => "Afsub"
    | Afmax => "Afmax"
    | Afmin => "Afmin"
    | Afmaximum => "Afmaximum"
    | Afminimum => "Afminimum"
    | Auinc_wrap => "Auinc_wrap"
    | Audec_wrap => "Audec_wrap"
    | Ausub_cond => "Ausub_cond"
    | Ausub_sat => "Ausub_sat"
    end.

  #[global]
   Instance reprAtomicRMWOperation : Repr atomic_rmw_operation :=
    {| repr_acc op acc := push_str_rev (repr_atomic_rmw_operation op) acc |}.

  Definition repr_atomicrmw_acc (rmw : atomicrmw typ) (acc : list ascii) : list ascii
    := match rmw with
       | mk_atomicrmw a_volatile a_operation a_ptr a_val a_syncscope a_ordering a_align =>
           acc |> push_str_rev "(mk_atomicrmw " |> repr_acc a_volatile |> push_str_rev " "
               |> repr_acc a_operation |> push_str_rev " "
               |> repr_acc a_ptr |> push_str_rev " " |> repr_acc a_val |> push_str_rev " "
               |> repr_acc a_syncscope |> push_str_rev " "
               |> repr_acc a_ordering |> push_str_rev " " |> repr_acc a_align |> push_str_rev ")"
       end.

  #[global]
   Instance reprAtomicRMW : Repr (atomicrmw typ) :=
    {| repr_acc := repr_atomicrmw_acc |}.

  Definition repr_cmpxchg_acc (cmp : cmpxchg typ) (acc : list ascii) : list ascii
    := match cmp with
       | mk_cmpxchg c_weak c_volatile c_ptr c_cmp c_new c_syncscope c_success_ordering
           c_failure_ordering c_align =>
           acc |> push_str_rev "(mk_cmpxchg " |> repr_acc c_weak |> push_str_rev " "
               |> repr_acc c_volatile |> push_str_rev " " |> repr_acc c_ptr |> push_str_rev " "
               |> repr_acc c_cmp |> push_str_rev " " |> repr_acc c_new |> push_str_rev " "
               |> repr_acc c_syncscope |> push_str_rev " " |> repr_acc c_success_ordering
               |> push_str_rev " " |> repr_acc c_failure_ordering |> push_str_rev " "
               |> repr_acc c_align |> push_str_rev ")"
       end.

  #[global]
   Instance reprCmpxchg : Repr (cmpxchg typ) :=
    {| repr_acc := repr_cmpxchg_acc |}.

  #[global]
    Instance reprClause : Repr (@landingpad_clause typ) :=
    {| repr_acc c acc :=
         match c with
         | CATCH t => acc |> push_str_rev "(CATCH " |> repr_acc t |> push_str_rev ")"
         | FILTER t => acc |> push_str_rev "(FILTER " |> repr_acc t |> push_str_rev ")"
         end
    |}.

  #[global] Instance reprOperand : Repr operand :=
    {| repr_acc op acc :=
         match op with
         | SSA_value t => acc |> push_str_rev "(SSA_value " |> repr_acc t |> push_str_rev ")"
         | Metadata_string m => acc |> push_str_rev "(Metadata_string " |> repr_acc m |> push_str_rev ")"
         end
    |}.

  #[global] Instance ReprOperand_bundle : Repr operand_bundle :=
    {| repr_acc ob acc :=
         acc |> push_str_rev "(mk_operand_bundle "
             |> repr_acc (ob_tag ob)
             |> repr_acc (ob_ops ob)
             |> push_str_rev ")"
    |}.

  Definition repr_instr_acc (i : instr typ) (acc : list ascii) : list ascii
    := match i with
       | INSTR_Comment s => acc |> push_str_rev "(INSTR_Comment " |> push_str_rev s |> push_str_rev ")"
       | INSTR_Op e => acc |> push_str_rev "(INSTR_Op " |> repr_acc e |> push_str_rev ")"
       | INSTR_Call e params annotations obs =>
           acc |> push_str_rev "(INSTR_Call " |> repr_acc e |> push_str_rev " "
               |> repr_acc params |> push_str_rev " " |> repr_acc annotations
               |> repr_acc obs |> push_str_rev ")"
       | INSTR_Alloca t anns =>
           acc |> push_str_rev "(INSTR_Alloca " |> repr_acc t |> push_str_rev " "
               |> repr_acc anns |> push_str_rev ")"
       | INSTR_Load t ptr anns =>
           acc |> push_str_rev "(INSTR_Load " |> repr_acc t |> push_str_rev " "
               |> repr_acc ptr |> push_str_rev " " |> repr_acc anns |> push_str_rev ")"
       | INSTR_Store tval ptr anns =>
           acc |> push_str_rev "(INSTR_Store " |> repr_acc tval |> push_str_rev " "
               |> repr_acc ptr |> push_str_rev " " |> repr_acc anns |> push_str_rev ")"
       | INSTR_Fence str ord =>
           acc |> push_str_rev "(INSTR_Fence " |> push_str_rev (show str) |> push_str_rev " "
               |> repr_acc ord |> push_str_rev ")"
       | INSTR_AtomicCmpXchg cmpx =>
           acc |> push_str_rev "(INSTR_AtomicCmpXchg " |> repr_acc cmpx |> push_str_rev ")"
       | INSTR_AtomicRMW rmw =>
           acc |> push_str_rev "(INSTR_AtomicRMW " |> repr_acc rmw |> push_str_rev ")"
       | INSTR_VAArg e t =>
           acc |> push_str_rev "(INSTR_VAArg " |> repr_acc e |> push_str_rev " "
               |> repr_acc t |> push_str_rev ")"
       | INSTR_LandingPad t b cs =>
           acc |> push_str_rev "(INSTR_LandingPad " |> repr_acc t |> push_str_rev " "
               |> repr_acc b |> push_str_rev " " |> repr_acc cs |> push_str_rev ")"
       end.

  #[global]
   Instance reprInstr : Repr (instr typ)
    := {| repr_acc := repr_instr_acc |}.

  #[global]
   Instance reprInstrId : Repr instr_id
    := {| repr_acc i acc :=
            match i with
            | IId raw => acc |> push_str_rev "(IId " |> repr_acc raw |> push_str_rev ")"
            | IVoid n => acc |> push_str_rev "(IVoid " |> repr_acc n |> push_str_rev ")"
            end
       |}.

  #[global]
  Instance reprTintLiteral : Repr tint_literal
    := {| repr_acc tl acc :=
            match tl with
            | TInt_Literal sz x =>
                acc |> push_str_rev "(TInt_Literal " |> repr_acc sz |> push_str_rev " "
                    |> repr_acc x |> push_str_rev ")"
            end
       |}.

  Definition repr_terminator_acc (t : terminator typ) (acc : list ascii) : list ascii
    := match t with
       | TERM_Ret v => acc |> push_str_rev "(TERM_Ret " |> repr_acc v |> push_str_rev ")"
       | TERM_Ret_void => push_str_rev "TERM_Ret_void" acc
       | TERM_Br te b1 b2 =>
           acc |> push_str_rev "(TERM_Br " |> repr_acc te |> push_str_rev " "
               |> repr_acc b1 |> push_str_rev " " |> repr_acc b2 |> push_str_rev ")"
       | TERM_Br_1 b => acc |> push_str_rev "(TERM_Br_1 " |> repr_acc b |> push_str_rev ")"
       | TERM_Switch v dest brs =>
           acc |> push_str_rev "(TERM_Switch " |> repr_acc v |> push_str_rev " "
               |> repr_acc dest |> repr_acc brs |> push_str_rev ")"
       | TERM_IndirectBr v brs fn =>
           acc |> push_str_rev "(TERM_IndirectBr " |> repr_acc v |> push_str_rev " "
               |> repr_acc brs |> push_str_rev " " |> repr_acc fn |> push_str_rev ")"
       | TERM_Resume v => acc |> push_str_rev "(TERM_Resume " |> repr_acc v |> push_str_rev ")"
       | TERM_Invoke fnptrval args to_label unwind_label anns obs =>
           acc |> push_str_rev "(TERM_Invoke " |> repr_acc fnptrval |> push_str_rev " "
               |> repr_acc args |> push_str_rev " " |> repr_acc to_label |> push_str_rev " "
               |> repr_acc unwind_label |> repr_acc anns |> repr_acc obs |> push_str_rev ")"
       | TERM_Unreachable => push_str_rev "TERM_Unreachable" acc
       end.

  #[global]
   Instance reprTerminator : Repr (terminator typ)
    := {| repr_acc := repr_terminator_acc |}.

  Definition repr_phi_acc (p : phi typ) (acc : list ascii) : list ascii
    := match p with
       | Phi fm t args =>
           acc |> push_str_rev "(Phi [" |> push_sep_rev "; " repr_acc fm |> push_str_rev "] "
               |> repr_acc t |> repr_acc args |> push_str_rev ")"
       end.

  #[global]
   Instance reprPhi : Repr (phi typ)
    := {| repr_acc := repr_phi_acc |}.

  Definition repr_block_acc (b : block typ) (acc : list ascii) : list ascii
    := match b with
       | mk_block blk_id blk_phis blk_code blk_term blk_comments =>
           acc |> push_str_rev "(mk_block " |> repr_acc blk_id |> push_str_rev " "
               |> repr_acc blk_phis |> push_str_rev " " |> repr_acc blk_code |> push_str_rev " "
               |> repr_acc blk_term |> push_str_rev " " |> repr_acc blk_comments |> push_str_rev ")"
       end.

  #[global]
   Instance reprBlock : Repr (block typ) :=
    {| repr_acc := repr_block_acc |}.

  Definition repr_declaration_acc (dec : declaration typ) (acc : list ascii) : list ascii
    := match dec with
       | mk_declaration dc_name dc_type dc_param_attrs dc_attrs dc_annotations =>
           acc |> push_str_rev "(mk_declaration " |> repr_acc dc_name |> push_str_rev " "
               |> repr_acc dc_type |> push_str_rev " "
               |> repr_acc dc_param_attrs |> push_str_rev " "
               |> repr_acc dc_attrs |> push_str_rev " "
               |> repr_acc dc_annotations |> push_str_rev ")"
       end.

  #[global]
   Instance reprDeclaration : Repr (declaration typ) :=
    {| repr_acc := repr_declaration_acc |}.

  Definition repr_definition_acc
    (defn : definition typ (block typ * list (block typ))) (acc : list ascii) : list ascii
    := match defn with
       | mk_definition df_prototype df_args df_instrs =>
           acc |> push_str_rev "(mk_definition " |> repr_acc df_prototype |> push_str_rev " "
               |> repr_acc df_args |> push_str_rev " "
               |> repr_acc df_instrs |> push_str_rev ")"
       end.

  #[global]
   Instance reprDefinition : Repr (definition typ (block typ * list (block typ))) :=
    {| repr_acc := repr_definition_acc |}.

  Definition repr_global_acc (g : global typ) (acc : list ascii) : list ascii :=
    match g with
    | mk_global g_ident g_typ g_constant g_exp g_externally_initialized g_alias g_annotations =>
        acc |> push_str_rev "(mk_global " |> repr_acc g_ident |> push_str_rev " "
            |> repr_acc g_typ |> push_str_rev " "
            |> repr_acc g_constant |> push_str_rev " "
            |> repr_acc g_exp |> push_str_rev " "
            |> repr_acc g_externally_initialized |> push_str_rev " "
            |> repr_acc g_alias |> push_str_rev " "
            |> repr_acc g_annotations |> push_str_rev ")"
    end.

  #[global]
   Instance reprGlobal : Repr (global typ) :=
    {| repr_acc := repr_global_acc |}.

  Definition repr_tle_acc
    (tle : toplevel_entity typ (block typ * list (block typ))) (acc : list ascii) : list ascii
    := match tle with
       | TLE_Comment msg => acc |> push_str_rev "(TLE_Comment " |> repr_acc msg |> push_str_rev ")"
       | TLE_Target tgt => acc |> push_str_rev "(TLE_Target " |> repr_acc tgt |> push_str_rev ")"
       | TLE_Datalayout layout => acc |> push_str_rev "(TLE_Datalayout " |> repr_acc layout |> push_str_rev ")"
       | TLE_Declaration decl => acc |> push_str_rev "(TLE_Declaration " |> repr_acc decl |> push_str_rev ")"
       | TLE_Definition defn => acc |> push_str_rev "(TLE_Definition " |> repr_acc defn |> push_str_rev ")"
       | TLE_Type_decl id t => acc |> push_str_rev "(TLE_Type_decl " |> repr_acc id |> push_str_rev " " |> repr_acc t |> push_str_rev ")"
       | TLE_Source_filename s => acc |> push_str_rev "(TLE_Source_filename " |> repr_acc s |> push_str_rev ")"
       | TLE_Global g => acc |> push_str_rev "(TLE_Global " |> repr_acc g |> push_str_rev ")"
       | TLE_Metadata id b md =>
           acc |> push_str_rev "(TLE_Metadata " |> repr_acc id |> push_str_rev " "
               |> repr_acc b |> push_str_rev " " |> repr_acc md |> push_str_rev ")"
       | TLE_Attribute_group i attrs =>
           acc |> push_str_rev "(TLE_Attribute_group " |> repr_acc i |> push_str_rev " "
               |> repr_acc attrs |> push_str_rev ")"
       end.

  Definition repr_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string :=
    rev_chars_to_string (repr_tle_acc tle []).

  #[global]
   Instance reprTLE : Repr (toplevel_entity typ (block typ * list (block typ))) :=
    {| repr_acc := repr_tle_acc |}.

End ReprInstances.
