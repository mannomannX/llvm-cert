(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Total S-Expression Lexer & [cert-v1] Parser ([CertValidator.CertFormatParse])

    Purpose:
      Defines a total, extraction-ready S-expression tokenizer, bounded-depth
      stack parser ([parse_sexp], depth [1024]), and canonical [cert-v1]
      deserializer ([parse_cert]) enforcing SHA-256 hex and closed [CE_Let]s.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed total parser ([parse_cert_sexp_wf], [parse_cert_wf]); syntax
      errors, depth overflow, or non-canonical literals yield [inl] diagnostics,
      while [inr cert] guarantees [wf_proof_certificate cert = true].

    Assumptions:
      Depends on Stdlib, [CertValidator.common.Diag], and
      [CertValidator.{LratCore,CertFormatAst}]; zero Vellvm deps or axioms.

    Section Outline:
      4. Total S-Expression Tokenizer & Bounded-Depth Parser ([parse_sexp]);
      5. Canonical [cert-v1] S-Expression Deserializer ([parse_cert]). *)

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
  Lia.
Import ListNotations.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  LratCore
  CertFormatAst.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments N.shiftl : simpl never.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Z.gtb _ _ : simpl nomatch.
#[local] Arguments Z.geb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 4. Total S-Expression Tokenizer & Bounded-Depth Parser ([parse_sexp], [parse_cert]) *)

Unset Elimination Schemes.
Inductive sexp : Set :=
| SAtom (s : string)
| SStr (s : string)
| SList (es : list sexp).
Set Elimination Schemes.

Fixpoint sexp_depth (sx : sexp) : nat :=
  match sx with
  | SAtom _ | SStr _ => 1%nat
  | SList es =>
      let fix max_d_acc (acc : nat) (xs : list sexp) {struct xs} : nat :=
          match xs with
          | [] => acc
          | x :: rest => max_d_acc (Nat.max acc (sexp_depth x)) rest
          end in
      S (max_d_acc 0%nat es)
  end.

Variant sexp_tok : Set :=
| TOK_LParen
| TOK_RParen
| TOK_Atom (s : string)
| TOK_Str (s : string).

Variant tok_mode : Set :=
| TM_Normal
| TM_InString (rev_acc : list ascii)
| TM_InEscape (rev_acc : list ascii)
| TM_InAtom (rev_acc : list ascii).

Definition is_sexp_ws (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 32 || Nat.eqb n 9 || Nat.eqb n 10 || Nat.eqb n 12 || Nat.eqb n 13.

Definition is_valid_atom_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (33 <=? n)%nat && (n <=? 126)%nat &&
  negb (Nat.eqb n 34) &&
  negb (Nat.eqb n 40) &&
  negb (Nat.eqb n 41) &&
  negb (Nat.eqb n 59).

Fixpoint tokenize_loop (mode : tok_mode) (rev_toks : list sexp_tok) (cs : list ascii) {struct cs}
  : string + list sexp_tok :=
  match cs with
  | [] =>
      match mode with
      | TM_Normal => inr (rev_tr rev_toks)
      | TM_InAtom rev_acc =>
          inr (rev_tr (TOK_Atom (rev_chars_to_str_acc EmptyString rev_acc) :: rev_toks))
      | TM_InString _ => inl "unterminated string literal in S-expression"
      | TM_InEscape _ => inl "unterminated escape sequence in S-expression"
      end
  | c :: rest =>
      let n := nat_of_ascii c in
      match mode with
      | TM_Normal =>
          if is_sexp_ws c then tokenize_loop TM_Normal rev_toks rest
          else if Nat.eqb n 40 then tokenize_loop TM_Normal (TOK_LParen :: rev_toks) rest
          else if Nat.eqb n 41 then tokenize_loop TM_Normal (TOK_RParen :: rev_toks) rest
          else if Nat.eqb n 34 then tokenize_loop (TM_InString []) rev_toks rest
          else if is_valid_atom_char c then tokenize_loop (TM_InAtom [c]) rev_toks rest
          else inl "invalid character in S-expression"
      | TM_InString rev_acc =>
          if Nat.eqb n 34 then
            tokenize_loop TM_Normal
              (TOK_Str (rev_chars_to_str_acc EmptyString rev_acc) :: rev_toks) rest
          else if Nat.eqb n 92 then
            tokenize_loop (TM_InEscape rev_acc) rev_toks rest
          else if (n <? 32)%nat || Nat.eqb n 127 then
            inl "raw control character in S-expression string literal"
          else
            tokenize_loop (TM_InString (c :: rev_acc)) rev_toks rest
      | TM_InEscape rev_acc =>
          if Nat.eqb n 92 then
            tokenize_loop (TM_InString (ascii_of_nat 92 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 34 then
            tokenize_loop (TM_InString (ascii_of_nat 34 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 110 then
            tokenize_loop (TM_InString (ascii_of_nat 10 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 114 then
            tokenize_loop (TM_InString (ascii_of_nat 13 :: rev_acc)) rev_toks rest
          else if Nat.eqb n 116 then
            tokenize_loop (TM_InString (ascii_of_nat 9 :: rev_acc)) rev_toks rest
          else
            inl "unsupported escape sequence in S-expression string literal"
      | TM_InAtom rev_acc =>
          let done_atom := TOK_Atom (rev_chars_to_str_acc EmptyString rev_acc) in
          if is_sexp_ws c then
            tokenize_loop TM_Normal (done_atom :: rev_toks) rest
          else if Nat.eqb n 40 then
            tokenize_loop TM_Normal (TOK_LParen :: done_atom :: rev_toks) rest
          else if Nat.eqb n 41 then
            tokenize_loop TM_Normal (TOK_RParen :: done_atom :: rev_toks) rest
          else if is_valid_atom_char c then
            tokenize_loop (TM_InAtom (c :: rev_acc)) rev_toks rest
          else
            inl "invalid character in bare atom"
      end
  end.

Definition max_sexp_depth : nat := 1024%nat.

Definition push_sexp_item (item : sexp) (stack : list (list sexp)) (top_rev : list sexp)
  : list (list sexp) * list sexp :=
  match stack with
  | [] => ([], item :: top_rev)
  | cur :: parents => ((item :: cur) :: parents, top_rev)
  end.

Fixpoint parse_sexp_toks (stack : list (list sexp)) (top_rev : list sexp)
                         (toks : list sexp_tok) {struct toks} : string + sexp :=
  match toks with
  | [] =>
      match stack with
      | _ :: _ => inl "unclosed opening parenthesis in S-expression"
      | [] =>
          match rev_tr top_rev with
          | [root] => inr root
          | [] => inl "empty S-expression input"
          | _ :: _ :: _ => inl "trailing tokens after root S-expression"
          end
      end
  | tok :: rest =>
      match tok with
      | TOK_Atom a =>
          let '(st', top') := push_sexp_item (SAtom a) stack top_rev in
          parse_sexp_toks st' top' rest
      | TOK_Str s =>
          let '(st', top') := push_sexp_item (SStr s) stack top_rev in
          parse_sexp_toks st' top' rest
      | TOK_LParen =>
          if (S (List.length stack) <=? max_sexp_depth)%nat then
            parse_sexp_toks ([] :: stack) top_rev rest
          else
            inl "S-expression exceeds maximum nesting depth 1024"
      | TOK_RParen =>
          match stack with
          | [] => inl "unexpected closing parenthesis in S-expression"
          | cur_rev :: parents =>
              let '(st', top') := push_sexp_item (SList (rev_tr cur_rev)) parents top_rev in
              parse_sexp_toks st' top' rest
          end
      end
  end.

Definition parse_sexp (input : string) : string + sexp :=
  match tokenize_loop TM_Normal [] (str_to_chars input) with
  | inl err => inl err
  | inr toks => parse_sexp_toks [] [] toks
  end.

(** ** 5. Canonical [cert-v1] S-Expression Deserializer ([parse_cert]) *)

Fixpoint parse_digits_acc (acc : N) (cs : list ascii) {struct cs} : option N :=
  match cs with
  | [] => Some acc
  | c :: rest =>
      let n := nat_of_ascii c in
      if (48 <=? n)%nat && (n <=? 57)%nat then
        parse_digits_acc (10 * acc + N.of_nat (n - 48))%N rest
      else
        None
  end.

Definition parse_canonical_N (s : string) : option N :=
  match str_to_chars s with
  | [] => None
  | [c] =>
      let n := nat_of_ascii c in
      if (48 <=? n)%nat && (n <=? 57)%nat then Some (N.of_nat (n - 48)) else None
  | c0 :: rest =>
      let n0 := nat_of_ascii c0 in
      if (49 <=? n0)%nat && (n0 <=? 57)%nat then
        parse_digits_acc (N.of_nat (n0 - 48)) rest
      else
        None
  end.

Definition parse_u64_N (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n =>
          if (n <? N.shiftl 1 64)%N then inr n
          else inl "integer literal exceeds 64-bit unsigned range"
      | None => inl "expected canonical unsigned integer atom"
      end
  | _ => inl "expected unsigned integer atom"
  end.

Definition parse_bv_N (w : positive) (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n =>
          if (n <? N.shiftl 1 (N.pos w))%N then inr n
          else inl "bitvector constant exceeds declared width"
      | None => inl "expected canonical unsigned integer for bitvector constant"
      end
  | _ => inl "expected atom for bitvector constant"
  end.

Lemma parse_bv_N_bound : forall w sx n,
  parse_bv_N w sx = inr n -> (n <? N.shiftl 1 (N.pos w))%N = true.
Proof.
  intros w [s | s | es] n H; cbn in H; try discriminate.
  destruct (parse_canonical_N s) as [m |]; [| discriminate].
  destruct (m <? N.shiftl 1 (N.pos w))%N eqn:Hb; [| discriminate].
  inversion H; subst; exact Hb.
Qed.

Definition parse_bit_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr 1%positive
      else if String.eqb s "8" then inr 8%positive
      else if String.eqb s "16" then inr 16%positive
      else if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else if String.eqb s "128" then inr 128%positive
      else inl "expected supported bit width (1, 8, 16, 32, 64, or 128)"
  | _ => inl "expected supported bit width (1, 8, 16, 32, 64, or 128)"
  end.

Lemma parse_bit_width_supported : forall sx w,
  parse_bit_width_sexp sx = inr w -> is_supported_bit_width w = true.
Proof.
  intros [s | s | es] w H; cbn in H; try discriminate.
  repeat match goal with
  | H0 : (if ?c then _ else _) = _ |- _ =>
      destruct c; [inversion H0; subst; reflexivity |]
  end; discriminate.
Qed.

Definition parse_bool01 (sx : sexp) : string + bool :=
  match sx with
  | SAtom s =>
      if String.eqb s "0" then inr false
      else if String.eqb s "1" then inr true
      else inl "expected boolean flag 0 or 1"
  | _ => inl "expected boolean flag 0 or 1"
  end.

Definition parse_bool_tf (sx : sexp) : string + bool :=
  match sx with
  | SAtom s =>
      if String.eqb s "false" then inr false
      else if String.eqb s "true" then inr true
      else inl "expected boolean atom true or false"
  | _ => inl "expected boolean atom true or false"
  end.

Definition parse_nonempty_str (sx : sexp) : string + string :=
  match sx with
  | SStr s =>
      if negb (String.eqb s "") then inr s
      else inl "expected non-empty string literal"
  | _ => inl "expected string literal"
  end.

Lemma parse_nonempty_str_ok : forall sx s,
  parse_nonempty_str sx = inr s -> negb (String.eqb s "") = true.
Proof.
  intros [a | s0 | es] s H; cbn in H; try discriminate.
  destruct (negb (String.eqb s0 "")) eqn:Hne; [| discriminate].
  inversion H; subst; exact Hne.
Qed.

Definition parse_sha256_atom (sx : sexp) : string + string :=
  match sx with
  | SAtom s =>
      if is_sha256_hex s then inr s
      else inl "expected 64-character lowercase hex SHA-256 digest"
  | _ => inl "expected bare atom for SHA-256 digest"
  end.

Lemma parse_sha256_atom_ok : forall sx s,
  parse_sha256_atom sx = inr s -> is_sha256_hex s = true.
Proof.
  intros [s0 | s0 | es] s H; cbn in H; try discriminate.
  destruct (is_sha256_hex s0) eqn:Hh; [| discriminate].
  inversion H; subst; exact Hh.
Qed.

Definition parse_cert_binop (sx : sexp) : string + cert_binop :=
  match sx with
  | SAtom s =>
      if String.eqb s "add" then inr CB_Add
      else if String.eqb s "sub" then inr CB_Sub
      else if String.eqb s "mul" then inr CB_Mul
      else if String.eqb s "udiv" then inr CB_UDiv
      else if String.eqb s "sdiv" then inr CB_SDiv
      else if String.eqb s "urem" then inr CB_URem
      else if String.eqb s "srem" then inr CB_SRem
      else if String.eqb s "shl" then inr CB_Shl
      else if String.eqb s "lshr" then inr CB_LShr
      else if String.eqb s "ashr" then inr CB_AShr
      else if String.eqb s "and" then inr CB_And
      else if String.eqb s "or" then inr CB_Or
      else if String.eqb s "xor" then inr CB_Xor
      else inl "unknown binary operator in cert-v1 expression"
  | _ => inl "unknown binary operator in cert-v1 expression"
  end.

Definition parse_cert_icmp_pred (sx : sexp) : string + cert_icmp_pred :=
  match sx with
  | SAtom s =>
      if String.eqb s "eq" then inr CIP_Eq
      else if String.eqb s "ne" then inr CIP_Ne
      else if String.eqb s "ult" then inr CIP_Ult
      else if String.eqb s "ule" then inr CIP_Ule
      else if String.eqb s "ugt" then inr CIP_Ugt
      else if String.eqb s "uge" then inr CIP_Uge
      else if String.eqb s "slt" then inr CIP_Slt
      else if String.eqb s "sle" then inr CIP_Sle
      else if String.eqb s "sgt" then inr CIP_Sgt
      else if String.eqb s "sge" then inr CIP_Sge
      else inl "unknown icmp predicate in cert-v1 expression"
  | _ => inl "unknown icmp predicate in cert-v1 expression"
  end.

Definition parse_cert_cast_kind (sx : sexp) : string + cert_cast_kind :=
  match sx with
  | SAtom s =>
      if String.eqb s "zext" then inr CCK_ZExt
      else if String.eqb s "sext" then inr CCK_SExt
      else if String.eqb s "trunc" then inr CCK_Trunc
      else inl "unknown cast kind in cert-v1 expression"
  | _ => inl "unknown cast kind in cert-v1 expression"
  end.

Section ParseLetBinds.
  Variable rec_parse : list (string * positive) -> sexp -> string + cert_expr.

  Fixpoint parse_let_binds_acc
    (acc_rev : list (string * cert_expr))
    (cur_env : list (string * positive)) (seen : list string)
    (bs : list sexp) {struct bs}
    : string + (list (string * cert_expr) * list (string * positive)) :=
    match bs with
    | [] => inr (List.rev_append acc_rev [], cur_env)
    | b_item :: rest =>
        match b_item with
        | SList [SStr bnm; bexpr_sx] =>
            if is_dollar_let_name bnm && negb (string_in_list bnm seen) then
              match rec_parse cur_env bexpr_sx with
              | inl err => inl err
              | inr be =>
                  let env_next := (bnm, cert_expr_bit_width be) :: cur_env in
                  parse_let_binds_acc ((bnm, be) :: acc_rev) env_next (bnm :: seen) rest
              end
            else inl "invalid or duplicate let binding name"
        | _ => inl "malformed let binding entry"
        end
    end.

  Definition parse_let_binds (cur_env : list (string * positive)) (seen : list string)
                             (bs : list sexp)
    : string + (list (string * cert_expr) * list (string * positive)) :=
    parse_let_binds_acc [] cur_env seen bs.
End ParseLetBinds.

Lemma parse_let_binds_acc_wf :
  forall (rec_parse : list (string * positive) -> sexp -> string + cert_expr)
         (Hrec : forall env sx e, rec_parse env sx = inr e -> wf_cert_expr env e = true)
         bs env0 seen0 acc_rev cur_env seen parsed_bs final_env,
    (forall tail env_tail,
       wf_let_binds_step wf_cert_expr cur_env seen tail = Some env_tail ->
       wf_let_binds_step wf_cert_expr env0 seen0 (List.rev_append acc_rev tail) = Some env_tail) ->
    parse_let_binds_acc rec_parse acc_rev cur_env seen bs = inr (parsed_bs, final_env) ->
    wf_let_binds_step wf_cert_expr env0 seen0 parsed_bs = Some final_env.
Proof.
  intros rec_parse Hrec bs env0 seen0.
  induction bs as [| b_item rest IH]; intros acc_rev cur_env seen parsed_bs final_env Hacc Hp;
    cbn [parse_let_binds_acc] in Hp.
  - inversion Hp; subst parsed_bs final_env; clear Hp.
    exact (Hacc [] cur_env eq_refl).
  - destruct b_item as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
    destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)) eqn:Hnm; [| discriminate Hp].
    destruct (rec_parse cur_env bexpr_sx) as [| be] eqn:Hbe; [discriminate Hp |].
    apply andb_true_iff in Hnm as [Hd Hns].
    apply (IH ((bnm, be) :: acc_rev)
              ((bnm, cert_expr_bit_width be) :: cur_env) (bnm :: seen)
              parsed_bs final_env); [| exact Hp].
    intros tail env_tail Htail; cbn [List.rev_append].
    apply Hacc; cbn [wf_let_binds_step].
    rewrite Hd, Hns, (Hrec cur_env bexpr_sx be Hbe); exact Htail.
Qed.

Lemma parse_let_binds_wf :
  forall (rec_parse : list (string * positive) -> sexp -> string + cert_expr)
         (Hrec : forall env sx e, rec_parse env sx = inr e -> wf_cert_expr env e = true)
         bs cur_env seen parsed_bs final_env,
    parse_let_binds rec_parse cur_env seen bs = inr (parsed_bs, final_env) ->
    wf_let_binds_step wf_cert_expr cur_env seen parsed_bs = Some final_env.
Proof.
  intros rec_parse Hrec bs cur_env seen parsed_bs final_env Hp.
  exact (parse_let_binds_acc_wf rec_parse Hrec bs cur_env seen [] cur_env seen
           parsed_bs final_env (fun _ _ H => H) Hp).
Qed.

Lemma rev_append_cons_nonnil : forall {A : Type} (x : A) (acc tail : list A),
  List.rev_append (x :: acc) tail <> [].
Proof.
  intros A x acc; revert x; induction acc as [| y rest IH]; intros x tail; cbn.
  - discriminate.
  - exact (IH y (x :: tail)).
Qed.

Lemma parse_let_binds_acc_nonempty :
  forall rec_parse bs a acc_rev cur_env seen parsed_bs final_env,
    parse_let_binds_acc rec_parse (a :: acc_rev) cur_env seen bs = inr (parsed_bs, final_env) ->
    parsed_bs <> [].
Proof.
  intros rec_parse bs; induction bs as [| b_item rest IH];
    intros a acc_rev cur_env seen parsed_bs final_env Hp; cbn [parse_let_binds_acc] in Hp.
  - inversion Hp; subst parsed_bs; clear Hp; exact (rev_append_cons_nonnil a acc_rev []).
  - destruct b_item as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
    destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)); [| discriminate Hp].
    destruct (rec_parse cur_env bexpr_sx); [discriminate Hp |].
    exact (IH _ _ _ _ _ _ Hp).
Qed.

Lemma parse_let_binds_nonempty :
  forall rec_parse b0 rest cur_env seen parsed_bs final_env,
    parse_let_binds rec_parse cur_env seen (b0 :: rest) = inr (parsed_bs, final_env) ->
    parsed_bs <> [].
Proof.
  intros rec_parse b0 rest cur_env seen parsed_bs final_env Hp.
  unfold parse_let_binds in Hp; cbn [parse_let_binds_acc] in Hp.
  destruct b0 as [| | [| [| bnm |] [| bexpr_sx [| ? ?]]]]; try discriminate Hp.
  destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)); [| discriminate Hp].
  destruct (rec_parse cur_env bexpr_sx) as [| be]; [discriminate Hp |].
  exact (parse_let_binds_acc_nonempty rec_parse rest (bnm, be) []
           ((bnm, cert_expr_bit_width be) :: cur_env) (bnm :: seen)
           parsed_bs final_env Hp).
Qed.

Fixpoint parse_cert_expr_fueled (fuel : nat) (let_env : list (string * positive)) (sx : sexp)
                                {struct fuel}
  : string + cert_expr :=
  match fuel with
  | O => inl "cert-v1 expression fuel exhausted"
  | S fuel' =>
      match sx with
      | SList (SAtom tag :: args) =>
          if String.eqb tag "bv" then
            match args with
            | [w_sx; val_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_bv_N w val_sx with
                    | inl err => inl err
                    | inr val => inr (CE_BvConst w val)
                    end
                end
            | _ => inl "malformed bv expression"
            end
          else if String.eqb tag "poison" then
            match args with
            | [w_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w => inr (CE_Poison w)
                end
            | _ => inl "malformed poison expression"
            end
          else if String.eqb tag "var" then
            match args with
            | [nm_sx; w_sx] =>
                match parse_nonempty_str nm_sx, parse_bit_width_sexp w_sx with
                | inr nm, inr w =>
                    match lookup_let_width let_env nm with
                    | Some bw =>
                        if Pos.eqb bw w then inr (CE_Var nm w)
                        else inl "let-bound variable bitwidth mismatch"
                    | None =>
                        if negb (starts_with_dollar nm) then inr (CE_Var nm w)
                        else inl "unbound $-prefixed let variable in cert-v1 expression"
                    end
                | inl err, _ => inl err
                | _, inl err => inl err
                end
            | _ => inl "malformed var expression"
            end
          else if String.eqb tag "binop" then
            match args with
            | [op_sx; w_sx; SList (SAtom f_tag :: [nuw_sx; nsw_sx; ex_sx; dj_sx]);
               lhs_sx; rhs_sx] =>
                if String.eqb f_tag "flags" then
                  match parse_cert_binop op_sx, parse_bit_width_sexp w_sx,
                        parse_bool01 nuw_sx, parse_bool01 nsw_sx,
                        parse_bool01 ex_sx, parse_bool01 dj_sx with
                  | inr op, inr w, inr nuw, inr nsw, inr ex, inr dj =>
                      let fl := mk_cert_binop_flags nuw nsw ex dj in
                      if wf_binop_flags_for op fl then
                        match parse_cert_expr_fueled fuel' let_env lhs_sx,
                              parse_cert_expr_fueled fuel' let_env rhs_sx with
                        | inr l, inr r =>
                            if Pos.eqb (cert_expr_bit_width l) w &&
                               Pos.eqb (cert_expr_bit_width r) w
                            then inr (CE_BinOp op w fl l r)
                            else inl "binop operand bitwidth mismatch"
                        | inl err, _ => inl err
                        | _, inl err => inl err
                        end
                      else inl "invalid poison flags for binary operator"
                  | inl err, _, _, _, _, _ => inl err
                  | _, inl err, _, _, _, _ => inl err
                  | _, _, inl err, _, _, _ => inl err
                  | _, _, _, inl err, _, _ => inl err
                  | _, _, _, _, inl err, _ => inl err
                  | _, _, _, _, _, inl err => inl err
                  end
                else inl "expected flags tag in binop expression"
            | _ => inl "malformed binop expression"
            end
          else if String.eqb tag "icmp" then
            match args with
            | [pr_sx; ss_sx; w_sx; lhs_sx; rhs_sx] =>
                match parse_cert_icmp_pred pr_sx, parse_bool01 ss_sx, parse_bit_width_sexp w_sx with
                | inr pr, inr ss, inr w =>
                    match parse_cert_expr_fueled fuel' let_env lhs_sx,
                          parse_cert_expr_fueled fuel' let_env rhs_sx with
                    | inr l, inr r =>
                        if Pos.eqb (cert_expr_bit_width l) w &&
                           Pos.eqb (cert_expr_bit_width r) w
                        then inr (CE_ICmp pr ss w l r)
                        else inl "icmp operand bitwidth mismatch"
                    | inl err, _ => inl err
                    | _, inl err => inl err
                    end
                | inl err, _, _ => inl err
                | _, inl err, _ => inl err
                | _, _, inl err => inl err
                end
            | _ => inl "malformed icmp expression"
            end
          else if String.eqb tag "cast" then
            match args with
            | [k_sx; fw_sx; tw_sx; SList (SAtom f_tag :: [nn_sx; nuw_sx; nsw_sx]); op_sx] =>
                if String.eqb f_tag "flags" then
                  match parse_cert_cast_kind k_sx,
                        parse_bit_width_sexp fw_sx, parse_bit_width_sexp tw_sx,
                        parse_bool01 nn_sx, parse_bool01 nuw_sx, parse_bool01 nsw_sx with
                  | inr k, inr fw, inr tw, inr nn, inr nuw, inr nsw =>
                      let fl := mk_cert_cast_flags nn nuw nsw in
                      if wf_cast_spec k fw tw fl then
                        match parse_cert_expr_fueled fuel' let_env op_sx with
                        | inr o =>
                            if Pos.eqb (cert_expr_bit_width o) fw
                            then inr (CE_Cast k fw tw fl o)
                            else inl "cast operand bitwidth mismatch"
                        | inl err => inl err
                        end
                      else inl "invalid cast width relation or flags"
                  | inl err, _, _, _, _, _ => inl err
                  | _, inl err, _, _, _, _ => inl err
                  | _, _, inl err, _, _, _ => inl err
                  | _, _, _, inl err, _, _ => inl err
                  | _, _, _, _, inl err, _ => inl err
                  | _, _, _, _, _, inl err => inl err
                  end
                else inl "expected flags tag in cast expression"
            | _ => inl "malformed cast expression"
            end
          else if String.eqb tag "select" then
            match args with
            | [w_sx; c_sx; t_sx; f_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_cert_expr_fueled fuel' let_env c_sx,
                          parse_cert_expr_fueled fuel' let_env t_sx,
                          parse_cert_expr_fueled fuel' let_env f_sx with
                    | inr c, inr tv, inr fv =>
                        if Pos.eqb (cert_expr_bit_width c) 1%positive &&
                           Pos.eqb (cert_expr_bit_width tv) w &&
                           Pos.eqb (cert_expr_bit_width fv) w
                        then inr (CE_Select w c tv fv)
                        else inl "select operand bitwidth mismatch"
                    | inl err, _, _ => inl err
                    | _, inl err, _ => inl err
                    | _, _, inl err => inl err
                    end
                end
            | _ => inl "malformed select expression"
            end
          else if String.eqb tag "freeze" then
            match args with
            | [w_sx; op_sx] =>
                match parse_bit_width_sexp w_sx with
                | inl err => inl err
                | inr w =>
                    match parse_cert_expr_fueled fuel' let_env op_sx with
                    | inr o =>
                        if Pos.eqb (cert_expr_bit_width o) w
                        then inr (CE_Freeze w o)
                        else inl "freeze operand bitwidth mismatch"
                    | inl err => inl err
                    end
                end
            | _ => inl "malformed freeze expression"
            end
          else if String.eqb tag "let" then
            match args with
            | [SList bind_sxs; body_sx] =>
                match bind_sxs with
                | [] => inl "empty let binding list in cert-v1 expression"
                | b0 :: brest =>
                    match parse_let_binds (parse_cert_expr_fueled fuel')
                                          let_env [] (b0 :: brest) with
                    | inl err => inl err
                    | inr (parsed_bs, env') =>
                        match parse_cert_expr_fueled fuel' env' body_sx with
                        | inl err => inl err
                        | inr body => inr (CE_Let parsed_bs body)
                        end
                    end
                end
            | _ => inl "malformed let expression"
            end
          else inl "unknown cert-v1 expression tag"
      | _ => inl "malformed cert-v1 expression"
      end
  end.

Definition parse_cert_expr (let_env : list (string * positive)) (sx : sexp)
  : string + cert_expr :=
  parse_cert_expr_fueled (sexp_depth sx) let_env sx.

Lemma parse_cert_expr_fueled_wf : forall fuel let_env sx e,
  parse_cert_expr_fueled fuel let_env sx = inr e ->
  wf_cert_expr let_env e = true.
Proof.
  induction fuel as [| fuel' IH]; intros let_env sx e Hp.
  - cbn in Hp; discriminate.
  - cbn [parse_cert_expr_fueled] in Hp.
    destruct sx as [| | [| [tag | |] args]]; try discriminate.
    destruct (String.eqb tag "bv") eqn:Hbv.
    + destruct args as [| w_sx [| val_sx [| ? ?]]]; try discriminate.
      destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
      destruct (parse_bv_N w val_sx) as [| val] eqn:Hv; [discriminate |].
      inversion Hp; subst; cbn.
      rewrite (parse_bit_width_supported w_sx w Hw), (parse_bv_N_bound w val_sx val Hv);
        reflexivity.
    + destruct (String.eqb tag "poison") eqn:Hpsn.
      * destruct args as [| w_sx [| ? ?]]; try discriminate.
        destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
        inversion Hp; subst; cbn; exact (parse_bit_width_supported w_sx w Hw).
      * destruct (String.eqb tag "var") eqn:Hvar.
        -- destruct args as [| nm_sx [| w_sx [| ? ?]]]; try discriminate.
           destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
           destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
           destruct (lookup_let_width let_env nm) as [bw |] eqn:Hlu.
           ++ destruct (Pos.eqb bw w) eqn:Hbw; [| discriminate].
              inversion Hp; subst; cbn.
              rewrite (parse_nonempty_str_ok nm_sx nm Hnm),
                      (parse_bit_width_supported w_sx w Hw), Hlu, Hbw; reflexivity.
           ++ destruct (negb (starts_with_dollar nm)) eqn:Hnd; [| discriminate].
              inversion Hp; subst; cbn.
              rewrite (parse_nonempty_str_ok nm_sx nm Hnm),
                      (parse_bit_width_supported w_sx w Hw), Hlu, Hnd; reflexivity.
        -- destruct (String.eqb tag "binop") eqn:Hbin.
           ++ destruct args as
                [| op_sx [| w_sx [| [| | [| [f_tag | |] [| nuw_sx [| nsw_sx [| ex_sx [| dj_sx [| ? ?]]]]]]]
                                  [| lhs_sx [| rhs_sx [| ? ?]]]]]];
                try discriminate.
              destruct (String.eqb f_tag "flags"); [| discriminate].
              destruct (parse_cert_binop op_sx) as [| op]; [discriminate |].
              destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
              destruct (parse_bool01 nuw_sx) as [| nuw]; [discriminate |].
              destruct (parse_bool01 nsw_sx) as [| nsw]; [discriminate |].
              destruct (parse_bool01 ex_sx) as [| ex]; [discriminate |].
              destruct (parse_bool01 dj_sx) as [| dj]; [discriminate |].
              destruct (wf_binop_flags_for op (mk_cert_binop_flags nuw nsw ex dj)) eqn:Hfl;
                [| discriminate].
              destruct (parse_cert_expr_fueled fuel' let_env lhs_sx) as [| l] eqn:Hl;
                [discriminate |].
              destruct (parse_cert_expr_fueled fuel' let_env rhs_sx) as [| r] eqn:Hr;
                [discriminate |].
              destruct (Pos.eqb (cert_expr_bit_width l) w &&
                        Pos.eqb (cert_expr_bit_width r) w) eqn:Hws; [| discriminate].
              apply andb_true_iff in Hws as [Hwl Hwr].
              inversion Hp; subst; cbn.
              rewrite (parse_bit_width_supported w_sx w Hw), Hfl,
                      (IH _ _ _ Hl), (IH _ _ _ Hr), Hwl, Hwr; reflexivity.
           ++ destruct (String.eqb tag "icmp") eqn:Hicmp.
              ** destruct args as [| pr_sx [| ss_sx [| w_sx [| lhs_sx [| rhs_sx [| ? ?]]]]]];
                   try discriminate.
                 destruct (parse_cert_icmp_pred pr_sx) as [| pr]; [discriminate |].
                 destruct (parse_bool01 ss_sx) as [| ss]; [discriminate |].
                 destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
                 destruct (parse_cert_expr_fueled fuel' let_env lhs_sx) as [| l] eqn:Hl;
                   [discriminate |].
                 destruct (parse_cert_expr_fueled fuel' let_env rhs_sx) as [| r] eqn:Hr;
                   [discriminate |].
                 destruct (Pos.eqb (cert_expr_bit_width l) w &&
                           Pos.eqb (cert_expr_bit_width r) w) eqn:Hws; [| discriminate].
                 apply andb_true_iff in Hws as [Hwl Hwr].
                 inversion Hp; subst; cbn.
                 rewrite (parse_bit_width_supported w_sx w Hw),
                         (IH _ _ _ Hl), (IH _ _ _ Hr), Hwl, Hwr; reflexivity.
              ** destruct (String.eqb tag "cast") eqn:Hcast.
                 --- destruct args as
                       [| k_sx [| fw_sx [| tw_sx
                         [| [| | [| [f_tag | |] [| nn_sx [| nuw_sx [| nsw_sx [| ? ?]]]]]]
                          [| op_sx [| ? ?]]]]]];
                       try discriminate.
                     destruct (String.eqb f_tag "flags"); [| discriminate].
                     destruct (parse_cert_cast_kind k_sx) as [| k]; [discriminate |].
                     destruct (parse_bit_width_sexp fw_sx) as [| fw]; [discriminate |].
                     destruct (parse_bit_width_sexp tw_sx) as [| tw]; [discriminate |].
                     destruct (parse_bool01 nn_sx) as [| nn]; [discriminate |].
                     destruct (parse_bool01 nuw_sx) as [| nuw]; [discriminate |].
                     destruct (parse_bool01 nsw_sx) as [| nsw]; [discriminate |].
                     destruct (wf_cast_spec k fw tw (mk_cert_cast_flags nn nuw nsw)) eqn:Hcs;
                       [| discriminate].
                     destruct (parse_cert_expr_fueled fuel' let_env op_sx) as [| o] eqn:Ho;
                       [discriminate |].
                     destruct (Pos.eqb (cert_expr_bit_width o) fw) eqn:Hwo; [| discriminate].
                     inversion Hp; subst; cbn.
                     rewrite Hcs, (IH _ _ _ Ho), Hwo; reflexivity.
                 --- destruct (String.eqb tag "select") eqn:Hsel.
                     +++ destruct args as [| w_sx [| c_sx [| t_sx [| f_sx [| ? ?]]]]];
                           try discriminate.
                         destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env c_sx) as [| c] eqn:Hc;
                           [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env t_sx) as [| tv] eqn:Ht;
                           [discriminate |].
                         destruct (parse_cert_expr_fueled fuel' let_env f_sx) as [| fv] eqn:Hf;
                           [discriminate |].
                         destruct (Pos.eqb (cert_expr_bit_width c) 1%positive &&
                                   Pos.eqb (cert_expr_bit_width tv) w &&
                                   Pos.eqb (cert_expr_bit_width fv) w) eqn:Hws; [| discriminate].
                         rewrite !andb_true_iff in Hws; destruct Hws as ((Hwc & Hwt) & Hwf).
                         inversion Hp; subst; cbn.
                         rewrite (parse_bit_width_supported w_sx w Hw),
                                 (IH _ _ _ Hc), (IH _ _ _ Ht), (IH _ _ _ Hf),
                                 Hwc, Hwt, Hwf; reflexivity.
                     +++ destruct (String.eqb tag "freeze") eqn:Hfrz.
                         *** destruct args as [| w_sx [| op_sx [| ? ?]]]; try discriminate.
                             destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw;
                               [discriminate |].
                             destruct (parse_cert_expr_fueled fuel' let_env op_sx) as [| o] eqn:Ho;
                               [discriminate |].
                             destruct (Pos.eqb (cert_expr_bit_width o) w) eqn:Hwo;
                               [| discriminate].
                             inversion Hp; subst; cbn.
                             rewrite (parse_bit_width_supported w_sx w Hw),
                                     (IH _ _ _ Ho), Hwo; reflexivity.
                         *** destruct (String.eqb tag "let") eqn:Hlet; [| discriminate].
                             destruct args as [| [| | [| b0 brest]] [| body_sx [| ? ?]]];
                               try discriminate.
                             destruct (parse_let_binds (parse_cert_expr_fueled fuel')
                                                       let_env [] (b0 :: brest))
                               as [| [parsed_bs env']] eqn:Hbs; [discriminate |].
                             destruct (parse_cert_expr_fueled fuel' env' body_sx)
                               as [| body] eqn:Hbody; [discriminate |].
                             inversion Hp; subst; cbn [wf_cert_expr].
                             pose proof (parse_let_binds_nonempty _ _ _ _ _ _ _ Hbs) as Hne.
                             pose proof (parse_let_binds_wf _ IH _ _ _ _ _ Hbs) as Hwfb.
                             destruct parsed_bs as [| p0 pr]; [congruence |].
                             rewrite Hwfb; exact (IH _ _ _ Hbody).
Qed.

Lemma parse_cert_expr_wf : forall sx let_env e,
  parse_cert_expr let_env sx = inr e -> wf_cert_expr let_env e = true.
Proof.
  intros sx let_env e Hp; exact (parse_cert_expr_fueled_wf (sexp_depth sx) let_env sx e Hp).
Qed.

Fixpoint map_parse_list_acc {A : Set} (f : sexp -> string + A)
                            (acc : list A) (xs : list sexp) {struct xs}
  : string + list A :=
  match xs with
  | [] => inr (List.rev_append acc [])
  | x :: rest =>
      match f x with
      | inl err => inl err
      | inr y => map_parse_list_acc f (y :: acc) rest
      end
  end.

Definition map_parse_list {A : Set} (f : sexp -> string + A) (xs : list sexp)
  : string + list A :=
  map_parse_list_acc f [] xs.

Lemma forallb_rev_append {A : Type} :
  forall (p : A -> bool) (xs acc : list A),
    forallb p xs = true ->
    forallb p acc = true ->
    forallb p (List.rev_append xs acc) = true.
Proof.
  intros p xs; induction xs as [| x rest IH]; intros acc Hxs Hacc; cbn in *.
  - exact Hacc.
  - apply andb_true_iff in Hxs as [Hx Hrest].
    apply IH; [exact Hrest | cbn; rewrite Hx, Hacc; reflexivity].
Qed.

Lemma map_parse_list_acc_forallb {A : Set} :
  forall (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall sx y, f sx = inr y -> wf y = true)
         xs acc ys,
    forallb wf acc = true ->
    map_parse_list_acc f acc xs = inr ys ->
    forallb wf ys = true.
Proof.
  intros f wf Hwf xs.
  induction xs as [| x rest IH]; intros acc ys Hacc Hp; cbn in Hp.
  - inversion Hp; subst; exact (forallb_rev_append wf acc [] Hacc eq_refl).
  - destruct (f x) as [| y] eqn:Hy; [discriminate |].
    apply (IH (y :: acc) ys); [| exact Hp].
    cbn; rewrite (Hwf x y Hy), Hacc; reflexivity.
Qed.

Lemma map_parse_list_forallb {A : Set} :
  forall (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall sx y, f sx = inr y -> wf y = true)
         xs ys,
    map_parse_list f xs = inr ys -> forallb wf ys = true.
Proof.
  intros f wf Hwf xs ys Hp.
  exact (map_parse_list_acc_forallb f wf Hwf xs [] ys eq_refl Hp).
Qed.

Definition parse_tagged_nonempty_str_sexp (expected_tag : string) (sx : sexp)
  : string + string :=
  match sx with
  | SList [SAtom tag; val_sx] =>
      if String.eqb tag expected_tag then parse_nonempty_str val_sx
      else inl "unexpected S-expression field tag"
  | _ => inl "expected tagged string S-expression"
  end.

Lemma parse_tagged_nonempty_str_ok : forall tag sx out,
  parse_tagged_nonempty_str_sexp tag sx = inr out -> negb (String.eqb out "") = true.
Proof.
  intros tag [? | ? | [| [t0 | ? | ?] [| val_sx [| ? ?]]]] out H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_nonempty_str_ok val_sx out H).
Qed.

Definition parse_tagged_sha256_sexp (expected_tag : string) (sx : sexp)
  : string + string :=
  match sx with
  | SList [SAtom tag; digest_sx] =>
      if String.eqb tag expected_tag then parse_sha256_atom digest_sx
      else inl "unexpected SHA-256 field tag"
  | _ => inl "expected tagged SHA-256 S-expression"
  end.

Lemma parse_tagged_sha256_ok : forall tag sx out,
  parse_tagged_sha256_sexp tag sx = inr out -> is_sha256_hex out = true.
Proof.
  intros tag [? | ? | [| [t0 | ? | ?] [| d_sx [| ? ?]]]] out H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_sha256_atom_ok d_sx out H).
Qed.

Definition parse_tagged_expr_sexp (expected_tag : string) (sx : sexp)
  : string + cert_expr :=
  match sx with
  | SList [SAtom tag; expr_sx] =>
      if String.eqb tag expected_tag then parse_cert_expr [] expr_sx
      else inl "unexpected expression field tag"
  | _ => inl "expected tagged expression S-expression"
  end.

Lemma parse_tagged_expr_wf : forall tag sx e,
  parse_tagged_expr_sexp tag sx = inr e -> wf_cert_expr [] e = true.
Proof.
  intros tag [| | [| [t0 | |] [| e_sx [| ? ?]]]] e H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (parse_cert_expr_wf e_sx [] e H).
Qed.

Definition parse_ub_assumption_sexp (sx : sexp) : string + ub_assumption :=
  match sx with
  | SList (SAtom tag :: args) =>
      if String.eqb tag "param-noundef" then
        match args with
        | [nm_sx; w_sx] =>
            match parse_nonempty_str nm_sx, parse_bit_width_sexp w_sx with
            | inr nm, inr w => inr (UBA_ParamNoUndef nm w)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed param-noundef assumption"
        end
      else if String.eqb tag "ptr-nonnull" then
        match args with
        | [nm_sx] =>
            match parse_nonempty_str nm_sx with
            | inr nm => inr (UBA_PtrNonNull nm)
            | inl err => inl err
            end
        | _ => inl "malformed ptr-nonnull assumption"
        end
      else if String.eqb tag "ptr-aligned" then
        match args with
        | [nm_sx; al_sx] =>
            match parse_nonempty_str nm_sx, parse_u64_N al_sx with
            | inr nm, inr al =>
                if is_power_of_two_N al then inr (UBA_PtrAligned nm al)
                else inl "ptr-aligned alignment must be a power of two"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed ptr-aligned assumption"
        end
      else if String.eqb tag "ptr-dereferenceable" then
        match args with
        | [nm_sx; b_sx] =>
            match parse_nonempty_str nm_sx, parse_u64_N b_sx with
            | inr nm, inr b =>
                if (0 <? b)%N then inr (UBA_PtrDereferenceable nm b)
                else inl "ptr-dereferenceable byte count must be positive"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed ptr-dereferenceable assumption"
        end
      else if String.eqb tag "load-noundef" then
        match args with
        | [sl_sx; w_sx] =>
            match parse_nonempty_str sl_sx, parse_bit_width_sexp w_sx with
            | inr sl, inr w => inr (UBA_LoadNoUndef sl w)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed load-noundef assumption"
        end
      else if String.eqb tag "divisor-nonzero" then
        match args with
        | [d_sx] =>
            match parse_cert_expr [] d_sx with
            | inr d => inr (UBA_DivisorNonZero d)
            | inl err => inl err
            end
        | _ => inl "malformed divisor-nonzero assumption"
        end
      else if String.eqb tag "sdiv-no-overflow" then
        match args with
        | [l_sx; r_sx] =>
            match parse_cert_expr [] l_sx, parse_cert_expr [] r_sx with
            | inr l, inr r =>
                if Pos.eqb (cert_expr_bit_width l) (cert_expr_bit_width r)
                then inr (UBA_SignedDivNoOverflow l r)
                else inl "sdiv-no-overflow operand width mismatch"
            | inl err, _ => inl err
            | _, inl err => inl err
            end
        | _ => inl "malformed sdiv-no-overflow assumption"
        end
      else if String.eqb tag "branch-cond-defined" then
        match args with
        | [c_sx] =>
            match parse_cert_expr [] c_sx with
            | inr c =>
                if Pos.eqb (cert_expr_bit_width c) 1%positive
                then inr (UBA_BranchCondDefined c)
                else inl "branch-cond-defined expression must have width 1"
            | inl err => inl err
            end
        | _ => inl "malformed branch-cond-defined assumption"
        end
      else if String.eqb tag "unreachable-eliminated" then
        match args with
        | [] => inr UBA_UnreachableEliminated
        | _ => inl "malformed unreachable-eliminated assumption"
        end
      else inl "unknown ub-assumption tag"
  | _ => inl "malformed ub-assumption entry"
  end.

Lemma parse_ub_assumption_wf : forall sx u,
  parse_ub_assumption_sexp sx = inr u -> wf_ub_assumption u = true.
Proof.
  intros [| | [| [tag | |] args]] u H; cbn in H; try discriminate.
  destruct (String.eqb tag "param-noundef").
  - destruct args as [| nm_sx [| w_sx [| ? ?]]]; try discriminate.
    destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hnm), (parse_bit_width_supported _ _ Hw); reflexivity.
  - destruct (String.eqb tag "ptr-nonnull").
    + destruct args as [| nm_sx [| ? ?]]; try discriminate.
      destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
      inversion H; subst; cbn; exact (parse_nonempty_str_ok _ _ Hnm).
    + destruct (String.eqb tag "ptr-aligned").
      * destruct args as [| nm_sx [| al_sx [| ? ?]]]; try discriminate.
        destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
        destruct (parse_u64_N al_sx) as [| al]; [discriminate |].
        destruct (is_power_of_two_N al) eqn:Hal; [| discriminate].
        inversion H; subst; cbn; rewrite (parse_nonempty_str_ok _ _ Hnm), Hal; reflexivity.
      * destruct (String.eqb tag "ptr-dereferenceable").
        -- destruct args as [| nm_sx [| b_sx [| ? ?]]]; try discriminate.
           destruct (parse_nonempty_str nm_sx) as [| nm] eqn:Hnm; [discriminate |].
           destruct (parse_u64_N b_sx) as [| b]; [discriminate |].
           destruct (0 <? b)%N eqn:Hb; [| discriminate].
           inversion H; subst; cbn; rewrite (parse_nonempty_str_ok _ _ Hnm), Hb; reflexivity.
        -- destruct (String.eqb tag "load-noundef").
           ++ destruct args as [| sl_sx [| w_sx [| ? ?]]]; try discriminate.
              destruct (parse_nonempty_str sl_sx) as [| sl] eqn:Hsl; [discriminate |].
              destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
              inversion H; subst; cbn.
              rewrite (parse_nonempty_str_ok _ _ Hsl), (parse_bit_width_supported _ _ Hw);
                reflexivity.
           ++ destruct (String.eqb tag "divisor-nonzero").
              ** destruct args as [| d_sx [| ? ?]]; try discriminate.
                 destruct (parse_cert_expr [] d_sx) as [| d] eqn:Hd; [discriminate |].
                 inversion H; subst; cbn; exact (parse_cert_expr_wf _ _ _ Hd).
              ** destruct (String.eqb tag "sdiv-no-overflow").
                 --- destruct args as [| l_sx [| r_sx [| ? ?]]]; try discriminate.
                     destruct (parse_cert_expr [] l_sx) as [| l] eqn:Hl; [discriminate |].
                     destruct (parse_cert_expr [] r_sx) as [| r] eqn:Hr; [discriminate |].
                     destruct (Pos.eqb (cert_expr_bit_width l) (cert_expr_bit_width r)) eqn:Hw;
                       [| discriminate].
                     inversion H; subst; cbn.
                     rewrite (parse_cert_expr_wf _ _ _ Hl), (parse_cert_expr_wf _ _ _ Hr), Hw;
                       reflexivity.
                 --- destruct (String.eqb tag "branch-cond-defined").
                     +++ destruct args as [| c_sx [| ? ?]]; try discriminate.
                         destruct (parse_cert_expr [] c_sx) as [| c] eqn:Hc; [discriminate |].
                         destruct (Pos.eqb (cert_expr_bit_width c) 1%positive) eqn:Hw;
                           [| discriminate].
                         inversion H; subst; cbn.
                         rewrite (parse_cert_expr_wf _ _ _ Hc), Hw; reflexivity.
                     +++ destruct (String.eqb tag "unreachable-eliminated"); [| discriminate].
                         destruct args as [| ? ?]; [| discriminate].
                         inversion H; subst; reflexivity.
Qed.

Definition parse_value_equiv_sexp (sx : sexp) : string + value_equivalence :=
  match sx with
  | SList [SAtom tag; sr_sx; tr_sx; w_sx; se_sx; te_sx] =>
      if String.eqb tag "equiv" then
        match parse_nonempty_str sr_sx, parse_nonempty_str tr_sx,
              parse_bit_width_sexp w_sx,
              parse_cert_expr [] se_sx, parse_cert_expr [] te_sx with
        | inr sr, inr tr, inr w, inr se, inr te =>
            if Pos.eqb (cert_expr_bit_width se) w &&
               Pos.eqb (cert_expr_bit_width te) w
            then inr (mk_value_equivalence sr tr w se te)
            else inl "value equivalence expression width mismatch"
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "expected equiv tag in value-equivs"
  | _ => inl "malformed value equivalence entry"
  end.

Lemma parse_value_equiv_wf : forall sx ve,
  parse_value_equiv_sexp sx = inr ve -> wf_value_equivalence ve = true.
Proof.
  intros [| | [| [tag | |] [| sr_sx [| tr_sx [| w_sx [| se_sx [| te_sx [| ? ?]]]]]]]] ve H;
    cbn in H; try discriminate.
  destruct (String.eqb tag "equiv"); [| discriminate].
  destruct (parse_nonempty_str sr_sx) as [| sr] eqn:Hsr; [discriminate |].
  destruct (parse_nonempty_str tr_sx) as [| tr] eqn:Htr; [discriminate |].
  destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
  destruct (parse_cert_expr [] se_sx) as [| se] eqn:Hse; [discriminate |].
  destruct (parse_cert_expr [] te_sx) as [| te] eqn:Hte; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width se) w &&
            Pos.eqb (cert_expr_bit_width te) w) eqn:Hws; [| discriminate].
  apply andb_true_iff in Hws as [Hw1 Hw2].
  inversion H; subst; unfold wf_value_equivalence; cbn.
  rewrite (parse_nonempty_str_ok _ _ Hsr), (parse_nonempty_str_ok _ _ Htr),
          (parse_bit_width_supported _ _ Hw),
          (parse_cert_expr_wf _ _ _ Hse), (parse_cert_expr_wf _ _ _ Hte),
          Hw1, Hw2; reflexivity.
Qed.

Definition parse_mem_invariant_sexp (sx : sexp) : string + memory_invariant :=
  match sx with
  | SList (SAtom tag :: args) =>
      if String.eqb tag "alloca-promoted" then
        match args with
        | [sl_sx; w_sx; e_sx] =>
            match parse_nonempty_str sl_sx, parse_bit_width_sexp w_sx,
                  parse_cert_expr [] e_sx with
            | inr sl, inr w, inr e =>
                if Pos.eqb (cert_expr_bit_width e) w
                then inr (MI_AllocaPromoted sl w e)
                else inl "alloca-promoted expression width mismatch"
            | inl err, _, _ => inl err
            | _, inl err, _ => inl err
            | _, _, inl err => inl err
            end
        | _ => inl "malformed alloca-promoted entry"
        end
      else if String.eqb tag "slot-refines" then
        match args with
        | [s1_sx; s2_sx; w_sx; e1_sx; e2_sx] =>
            match parse_nonempty_str s1_sx, parse_nonempty_str s2_sx,
                  parse_bit_width_sexp w_sx,
                  parse_cert_expr [] e1_sx, parse_cert_expr [] e2_sx with
            | inr s1, inr s2, inr w, inr e1, inr e2 =>
                if Pos.eqb (cert_expr_bit_width e1) w &&
                   Pos.eqb (cert_expr_bit_width e2) w
                then inr (MI_SlotRefines s1 s2 w e1 e2)
                else inl "slot-refines expression width mismatch"
            | inl err, _, _, _, _ => inl err
            | _, inl err, _, _, _ => inl err
            | _, _, inl err, _, _ => inl err
            | _, _, _, inl err, _ => inl err
            | _, _, _, _, inl err => inl err
            end
        | _ => inl "malformed slot-refines entry"
        end
      else inl "unknown memory invariant tag"
  | _ => inl "malformed memory invariant entry"
  end.

Lemma parse_mem_invariant_wf : forall sx mi,
  parse_mem_invariant_sexp sx = inr mi -> wf_memory_invariant mi = true.
Proof.
  intros [| | [| [tag | |] args]] mi H; cbn in H; try discriminate.
  destruct (String.eqb tag "alloca-promoted").
  - destruct args as [| sl_sx [| w_sx [| e_sx [| ? ?]]]]; try discriminate.
    destruct (parse_nonempty_str sl_sx) as [| sl] eqn:Hsl; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    destruct (parse_cert_expr [] e_sx) as [| e] eqn:He; [discriminate |].
    destruct (Pos.eqb (cert_expr_bit_width e) w) eqn:Hwe; [| discriminate].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hsl), (parse_bit_width_supported _ _ Hw),
            (parse_cert_expr_wf _ _ _ He), Hwe; reflexivity.
  - destruct (String.eqb tag "slot-refines"); [| discriminate].
    destruct args as [| s1_sx [| s2_sx [| w_sx [| e1_sx [| e2_sx [| ? ?]]]]]];
      try discriminate.
    destruct (parse_nonempty_str s1_sx) as [| s1] eqn:Hs1; [discriminate |].
    destruct (parse_nonempty_str s2_sx) as [| s2] eqn:Hs2; [discriminate |].
    destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
    destruct (parse_cert_expr [] e1_sx) as [| e1] eqn:He1; [discriminate |].
    destruct (parse_cert_expr [] e2_sx) as [| e2] eqn:He2; [discriminate |].
    destruct (Pos.eqb (cert_expr_bit_width e1) w &&
              Pos.eqb (cert_expr_bit_width e2) w) eqn:Hws; [| discriminate].
    apply andb_true_iff in Hws as [Hw1 Hw2].
    inversion H; subst; cbn.
    rewrite (parse_nonempty_str_ok _ _ Hs1), (parse_nonempty_str_ok _ _ Hs2),
            (parse_bit_width_supported _ _ Hw),
            (parse_cert_expr_wf _ _ _ He1), (parse_cert_expr_wf _ _ _ He2),
            Hw1, Hw2; reflexivity.
Qed.

Definition parse_tagged_section_list {A : Set}
  (expected_tag : string) (item_parser : sexp -> string + A) (sx : sexp)
  : string + list A :=
  match sx with
  | SList (SAtom tag :: items) =>
      if String.eqb tag expected_tag then map_parse_list item_parser items
      else inl "unexpected section tag"
  | _ => inl "expected tagged list section"
  end.

Lemma parse_tagged_section_list_wf {A : Set} :
  forall tag (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall x y, f x = inr y -> wf y = true)
         sx ys,
    parse_tagged_section_list tag f sx = inr ys -> forallb wf ys = true.
Proof.
  intros tag f wf Hwf [| | [| [t0 | |] items]] ys H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (map_parse_list_forallb f wf Hwf items ys H).
Qed.

Definition parse_block_cert_kind (sx : sexp) : string + block_cert_kind :=
  match sx with
  | SList [SAtom tag; SAtom k] =>
      if String.eqb tag "kind" then
        if String.eqb k "entry" then inr BCK_Entry
        else if String.eqb k "cutpoint" then inr BCK_Cutpoint
        else if String.eqb k "return" then inr BCK_Return
        else inl "unknown block certificate kind"
      else inl "expected kind tag in block certificate"
  | _ => inl "malformed kind field in block certificate"
  end.

Definition parse_block_cert_sexp (sx : sexp) : string + block_certificate :=
  match sx with
  | SList [SAtom tag; src_sx; tgt_sx; kind_sx; ub_sx; eq_sx; mem_sx] =>
      if String.eqb tag "block" then
        match parse_tagged_nonempty_str_sexp "src-bb" src_sx,
              parse_tagged_nonempty_str_sexp "tgt-bb" tgt_sx,
              parse_block_cert_kind kind_sx,
              parse_tagged_section_list "ub-assumptions" parse_ub_assumption_sexp ub_sx,
              parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx,
              parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx with
        | inr sbb, inr tbb, inr k, inr ubs, inr eqs, inr mems =>
            inr (mk_block_certificate sbb tbb k ubs eqs mems)
        | inl err, _, _, _, _, _ => inl err
        | _, inl err, _, _, _, _ => inl err
        | _, _, inl err, _, _, _ => inl err
        | _, _, _, inl err, _, _ => inl err
        | _, _, _, _, inl err, _ => inl err
        | _, _, _, _, _, inl err => inl err
        end
      else inl "expected block tag"
  | _ => inl "malformed block certificate"
  end.

Lemma parse_block_cert_wf : forall sx bc,
  parse_block_cert_sexp sx = inr bc -> wf_block_certificate bc = true.
Proof.
  intros [| | [| [tag | |] [| src_sx [| tgt_sx [| kind_sx [| ub_sx [| eq_sx [| mem_sx [| ? ?]]]]]]]]]
         bc H; cbn in H; try discriminate.
  destruct (String.eqb tag "block"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "src-bb" src_sx) as [| sbb] eqn:Hs; [discriminate |].
  destruct (parse_tagged_nonempty_str_sexp "tgt-bb" tgt_sx) as [| tbb] eqn:Ht; [discriminate |].
  destruct (parse_block_cert_kind kind_sx) as [| k]; [discriminate |].
  destruct (parse_tagged_section_list "ub-assumptions" parse_ub_assumption_sexp ub_sx)
    as [| ubs] eqn:Hub; [discriminate |].
  destruct (parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx)
    as [| eqs] eqn:Heq; [discriminate |].
  destruct (parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx)
    as [| mems] eqn:Hmem; [discriminate |].
  inversion H; subst; unfold wf_block_certificate; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hs),
          (parse_tagged_nonempty_str_ok _ _ _ Ht),
          (parse_tagged_section_list_wf _ _ _ parse_ub_assumption_wf _ _ Hub),
          (parse_tagged_section_list_wf _ _ _ parse_value_equiv_wf _ _ Heq),
          (parse_tagged_section_list_wf _ _ _ parse_mem_invariant_wf _ _ Hmem);
    reflexivity.
Qed.

Definition parse_cutpoint_inv_sexp (sx : sexp) : string + loop_cutpoint_invariant :=
  match sx with
  | SList [SAtom tag; sh_sx; th_sx; g_sx; eq_sx; mem_sx] =>
      if String.eqb tag "cutpoint-inv" then
        match parse_tagged_nonempty_str_sexp "src-hdr" sh_sx,
              parse_tagged_nonempty_str_sexp "tgt-hdr" th_sx,
              parse_tagged_expr_sexp "guard" g_sx,
              parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx,
              parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx with
        | inr sh, inr th, inr g, inr eqs, inr mems =>
            if Pos.eqb (cert_expr_bit_width g) 1%positive
            then inr (mk_loop_cutpoint_invariant sh th g eqs mems)
            else inl "cutpoint-inv guard expression must have width 1"
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "expected cutpoint-inv tag"
  | _ => inl "malformed cutpoint-inv entry"
  end.

Lemma parse_cutpoint_inv_wf : forall sx lci,
  parse_cutpoint_inv_sexp sx = inr lci -> wf_loop_cutpoint_invariant lci = true.
Proof.
  intros [| | [| [tag | |] [| sh_sx [| th_sx [| g_sx [| eq_sx [| mem_sx [| ? ?]]]]]]]]
         lci H; cbn in H; try discriminate.
  destruct (String.eqb tag "cutpoint-inv"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "src-hdr" sh_sx) as [| sh] eqn:Hsh; [discriminate |].
  destruct (parse_tagged_nonempty_str_sexp "tgt-hdr" th_sx) as [| th] eqn:Hth; [discriminate |].
  destruct (parse_tagged_expr_sexp "guard" g_sx) as [| g] eqn:Hg; [discriminate |].
  destruct (parse_tagged_section_list "value-equivs" parse_value_equiv_sexp eq_sx)
    as [| eqs] eqn:Heq; [discriminate |].
  destruct (parse_tagged_section_list "mem-invariants" parse_mem_invariant_sexp mem_sx)
    as [| mems] eqn:Hmem; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width g) 1%positive) eqn:Hwg; [| discriminate].
  inversion H; subst; unfold wf_loop_cutpoint_invariant; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hsh),
          (parse_tagged_nonempty_str_ok _ _ _ Hth),
          (parse_tagged_expr_wf _ _ _ Hg), Hwg,
          (parse_tagged_section_list_wf _ _ _ parse_value_equiv_wf _ _ Heq),
          (parse_tagged_section_list_wf _ _ _ parse_mem_invariant_wf _ _ Hmem);
    reflexivity.
Qed.

Definition parse_alias_witness_sexp (sx : sexp) : string + alias_witness :=
  match sx with
  | SList [SAtom tag; l_sx; r_sx] =>
      let kind_res :=
          if String.eqb tag "noalias" then inr ARK_NoAlias
          else if String.eqb tag "mustalias" then inr ARK_MustAlias
          else inl "unknown alias witness relation tag" in
      match kind_res, parse_nonempty_str l_sx, parse_nonempty_str r_sx with
      | inr k, inr l, inr r => inr (mk_alias_witness k l r)
      | inl err, _, _ => inl err
      | _, inl err, _ => inl err
      | _, _, inl err => inl err
      end
  | _ => inl "malformed alias witness entry"
  end.

Lemma parse_alias_witness_wf : forall sx aw,
  parse_alias_witness_sexp sx = inr aw -> wf_alias_witness aw = true.
Proof.
  intros [| | [| [tag | |] [| l_sx [| r_sx [| ? ?]]]]] aw H; cbn in H; try discriminate.
  destruct (if String.eqb tag "noalias" then inr ARK_NoAlias
            else if String.eqb tag "mustalias" then inr ARK_MustAlias
            else inl "unknown alias witness relation tag") as [| k]; [discriminate |].
  destruct (parse_nonempty_str l_sx) as [| l] eqn:Hl; [discriminate |].
  destruct (parse_nonempty_str r_sx) as [| r] eqn:Hr; [discriminate |].
  inversion H; subst; unfold wf_alias_witness; cbn.
  rewrite (parse_nonempty_str_ok _ _ Hl), (parse_nonempty_str_ok _ _ Hr); reflexivity.
Qed.

Definition parse_return_obligation_sexp (sx : sexp) : string + return_obligation :=
  match sx with
  | SList [SAtom rtag; body_sx] =>
      if String.eqb rtag "return" then
        match body_sx with
        | SList [SAtom vtag] =>
            if String.eqb vtag "void-equiv" then inr RO_VoidEquiv
            else inl "unknown return obligation tag"
        | SList [SAtom stag;
                 SList [SAtom wtag; w_sx];
                 src_sx; tgt_sx;
                 SList [SAtom vftag; vf_sx]] =>
            if String.eqb stag "scalar-refines" &&
               String.eqb wtag "width" &&
               String.eqb vftag "smt-verified"
            then
              match parse_bit_width_sexp w_sx,
                    parse_tagged_expr_sexp "src" src_sx,
                    parse_tagged_expr_sexp "tgt" tgt_sx,
                    parse_bool_tf vf_sx with
              | inr w, inr se, inr te, inr vf =>
                  if Pos.eqb (cert_expr_bit_width se) w &&
                     Pos.eqb (cert_expr_bit_width te) w
                  then inr (RO_ScalarRefines w se te vf)
                  else inl "scalar-refines expression width mismatch"
              | inl err, _, _, _ => inl err
              | _, inl err, _, _ => inl err
              | _, _, inl err, _ => inl err
              | _, _, _, inl err => inl err
              end
            else inl "malformed scalar-refines obligation"
        | _ => inl "malformed return obligation body"
        end
      else inl "expected return section tag"
  | _ => inl "malformed return section"
  end.

Lemma parse_return_obligation_wf : forall sx ro,
  parse_return_obligation_sexp sx = inr ro -> wf_return_obligation ro = true.
Proof.
  intros [| | [| [rtag | |] [| body_sx [| ? ?]]]] ro H; cbn in H; try discriminate.
  destruct (String.eqb rtag "return"); [| discriminate].
  destruct body_sx as [| | [| [stag | |] rest]]; try discriminate.
  destruct rest as [| [| | [| [wtag | |] [| w_sx [| ? ?]]]]
                    [| src_sx [| tgt_sx [| [| | [| [vftag | |] [| vf_sx [| ? ?]]]] [| ? ?]]]]];
    try (destruct (String.eqb stag "void-equiv"); [inversion H; subst; reflexivity | discriminate]);
    try discriminate.
  destruct (String.eqb stag "scalar-refines" && String.eqb wtag "width" &&
            String.eqb vftag "smt-verified"); [| discriminate].
  destruct (parse_bit_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
  destruct (parse_tagged_expr_sexp "src" src_sx) as [| se] eqn:Hse; [discriminate |].
  destruct (parse_tagged_expr_sexp "tgt" tgt_sx) as [| te] eqn:Hte; [discriminate |].
  destruct (parse_bool_tf vf_sx) as [| vf]; [discriminate |].
  destruct (Pos.eqb (cert_expr_bit_width se) w &&
            Pos.eqb (cert_expr_bit_width te) w) eqn:Hws; [| discriminate].
  apply andb_true_iff in Hws as [Hw1 Hw2].
  inversion H; subst; cbn.
  rewrite (parse_bit_width_supported _ _ Hw),
          (parse_tagged_expr_wf _ _ _ Hse), (parse_tagged_expr_wf _ _ _ Hte),
          Hw1, Hw2; reflexivity.
Qed.

Definition parse_nonempty_tagged_section {A : Set}
  (expected_tag : string) (item_parser : sexp -> string + A) (sx : sexp)
  : string + list A :=
  match sx with
  | SList (SAtom tag :: first_item :: more_items) =>
      if String.eqb tag expected_tag then
        map_parse_list item_parser (first_item :: more_items)
      else inl "unexpected optional section tag"
  | _ => inl "optional cert-v1 section must be a non-empty tagged list"
  end.

Lemma parse_nonempty_tagged_section_wf {A : Set} :
  forall tag (f : sexp -> string + A) (wf : A -> bool)
         (Hwf : forall x y, f x = inr y -> wf y = true)
         sx ys,
    parse_nonempty_tagged_section tag f sx = inr ys -> forallb wf ys = true.
Proof.
  intros tag f wf Hwf [| | [| [t0 | |] [| x0 xr]]] ys H; cbn in H; try discriminate.
  destruct (String.eqb t0 tag); [| discriminate].
  exact (map_parse_list_forallb f wf Hwf (x0 :: xr) ys H).
Qed.

Definition parse_optional_tail (tail : list sexp)
  : string + (list loop_cutpoint_invariant * list alias_witness * return_obligation) :=
  match tail with
  | [ret_sx] =>
      match parse_return_obligation_sexp ret_sx with
      | inr ro => inr ([], [], ro)
      | inl err => inl err
      end
  | [sec1_sx; ret_sx] =>
      match sec1_sx with
      | SList (SAtom sec_tag :: _) =>
          if String.eqb sec_tag "loop-invariants" then
            match parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp sec1_sx,
                  parse_return_obligation_sexp ret_sx with
            | inr lcis, inr ro => inr (lcis, [], ro)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
          else if String.eqb sec_tag "alias-witnesses" then
            match parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp sec1_sx,
                  parse_return_obligation_sexp ret_sx with
            | inr aws, inr ro => inr ([], aws, ro)
            | inl err, _ => inl err
            | _, inl err => inl err
            end
          else inl "unknown optional section in cert-v1"
      | _ => inl "malformed optional section in cert-v1"
      end
  | [loop_sx; alias_sx; ret_sx] =>
      match parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp loop_sx,
            parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp alias_sx,
            parse_return_obligation_sexp ret_sx with
      | inr lcis, inr aws, inr ro => inr (lcis, aws, ro)
      | inl err, _, _ => inl err
      | _, inl err, _ => inl err
      | _, _, inl err => inl err
      end
  | _ => inl "invalid optional/return section sequence in cert-v1"
  end.

Lemma parse_optional_tail_wf : forall tail lcis aws ro,
  parse_optional_tail tail = inr (lcis, aws, ro) ->
  forallb wf_loop_cutpoint_invariant lcis = true /\
  forallb wf_alias_witness aws = true /\
  wf_return_obligation ro = true.
Proof.
  intros tail lcis aws ro H.
  destruct tail as [| s1 [| s2 [| s3 [| ? ?]]]]; cbn in H; try discriminate.
  - destruct (parse_return_obligation_sexp s1) as [| r0] eqn:Hr; [discriminate |].
    inversion H; subst; repeat split; exact (parse_return_obligation_wf _ _ Hr).
  - destruct s1 as [| | [| [sec_tag | |] s1_rest]]; try discriminate.
    destruct (String.eqb sec_tag "loop-invariants") eqn:Hli.
    + destruct (parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp
                  (SList (SAtom sec_tag :: s1_rest))) as [| ls] eqn:Hls; [discriminate |].
      destruct (parse_return_obligation_sexp s2) as [| r0] eqn:Hr; [discriminate |].
      inversion H; subst; repeat split.
      * exact (parse_nonempty_tagged_section_wf _ _ _ parse_cutpoint_inv_wf _ _ Hls).
      * exact (parse_return_obligation_wf _ _ Hr).
    + destruct (String.eqb sec_tag "alias-witnesses") eqn:Haw; [| discriminate].
      destruct (parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp
                  (SList (SAtom sec_tag :: s1_rest))) as [| ws] eqn:Hws; [discriminate |].
      destruct (parse_return_obligation_sexp s2) as [| r0] eqn:Hr; [discriminate |].
      inversion H; subst; repeat split.
      * exact (parse_nonempty_tagged_section_wf _ _ _ parse_alias_witness_wf _ _ Hws).
      * exact (parse_return_obligation_wf _ _ Hr).
  - destruct (parse_nonempty_tagged_section "loop-invariants" parse_cutpoint_inv_sexp s1)
      as [| ls] eqn:Hls; [discriminate |].
    destruct (parse_nonempty_tagged_section "alias-witnesses" parse_alias_witness_sexp s2)
      as [| ws] eqn:Hws; [discriminate |].
    destruct (parse_return_obligation_sexp s3) as [| r0] eqn:Hr; [discriminate |].
    inversion H; subst; repeat split.
    + exact (parse_nonempty_tagged_section_wf _ _ _ parse_cutpoint_inv_wf _ _ Hls).
    + exact (parse_nonempty_tagged_section_wf _ _ _ parse_alias_witness_wf _ _ Hws).
    + exact (parse_return_obligation_wf _ _ Hr).
Qed.

Definition parse_pos_str (s : string) : option positive :=
  match parse_canonical_N s with
  | Some (Npos p) => Some p
  | _ => None
  end.

Definition parse_signed_lit_str (s : string) : option lit :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 45 then
        match parse_pos_str rest with
        | Some p => Some (Z.neg p)
        | None => None
        end
      else
        match parse_pos_str s with
        | Some p => Some (Z.pos p)
        | None => None
        end
  | EmptyString => None
  end.

Definition parse_pos_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      match parse_pos_str s with
      | Some p => inr p
      | None => inl "expected canonical positive integer in LRAT section"
      end
  | _ => inl "expected positive integer atom in LRAT section"
  end.

Definition parse_lit_sexp (sx : sexp) : string + lit :=
  match sx with
  | SAtom s =>
      match parse_signed_lit_str s with
      | Some l => inr l
      | None => inl "expected non-zero canonical literal in LRAT section"
      end
  | _ => inl "expected literal atom in LRAT section"
  end.

Definition parse_lrat_step_sexp (sx : sexp) : string + lrat_step :=
  match sx with
  | SList [SAtom tag; cid_sx; SList lit_sxs; SList hint_sxs] =>
      if String.eqb tag "add" then
        match parse_pos_sexp cid_sx,
              map_parse_list parse_lit_sexp lit_sxs,
              map_parse_list parse_pos_sexp hint_sxs with
        | inr cid, inr cl, inr hints => inr (LRAT_Add cid cl hints)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "unknown LRAT step tag"
  | SList [SAtom tag; SList cid_sxs] =>
      if String.eqb tag "del" then
        match map_parse_list parse_pos_sexp cid_sxs with
        | inr cids => inr (LRAT_Del cids)
        | inl err => inl err
        end
      else inl "unknown LRAT step tag"
  | _ => inl "malformed LRAT step S-expression"
  end.

Definition is_lrat_section_sexp (sx : sexp) : bool :=
  match sx with
  | SList (SAtom tag :: _) => String.eqb tag "lrat"
  | _ => false
  end.

Definition parse_optional_tail_with_lrat (tail : list sexp)
  : string + (list loop_cutpoint_invariant * list alias_witness *
              return_obligation * option (list lrat_step)) :=
  match rev_tr tail with
  | last_sx :: rev_prefix =>
      if is_lrat_section_sexp last_sx then
        match parse_optional_tail (rev_tr rev_prefix),
              parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp last_sx with
        | inr (lcis, aws, ro), inr pf => inr (lcis, aws, ro, Some pf)
        | inl err, _ => inl err
        | _, inl err => inl err
        end
      else
        match parse_optional_tail tail with
        | inr (lcis, aws, ro) => inr (lcis, aws, ro, None)
        | inl err => inl err
        end
  | [] => inl "missing return section in cert-v1"
  end.

Lemma parse_optional_tail_with_lrat_wf : forall tail lcis aws ro opt_pf,
  parse_optional_tail_with_lrat tail = inr (lcis, aws, ro, opt_pf) ->
  forallb wf_loop_cutpoint_invariant lcis = true /\
  forallb wf_alias_witness aws = true /\
  wf_return_obligation ro = true.
Proof.
  intros tail lcis aws ro opt_pf H.
  unfold parse_optional_tail_with_lrat in H.
  destruct (rev_tr tail) as [| last_sx rev_prefix]; [discriminate H |].
  destruct (is_lrat_section_sexp last_sx).
  - destruct (parse_optional_tail (rev_tr rev_prefix)) as [| [[ls ws] r0]] eqn:Ht;
      [discriminate H |].
    destruct (parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp last_sx)
      as [| pf]; [discriminate H |].
    inversion H; subst; exact (parse_optional_tail_wf _ _ _ _ Ht).
  - destruct (parse_optional_tail tail) as [| [[ls ws] r0]] eqn:Ht;
      [discriminate H |].
    inversion H; subst; exact (parse_optional_tail_wf _ _ _ _ Ht).
Qed.

Definition parse_cert_sexp (root : sexp) : string + proof_certificate :=
  match root with
  | SList (SAtom schema_tag :: fn_sx :: sh_sx :: th_sx :: blks_sx :: tail) =>
      if String.eqb schema_tag "cert-v1" then
        match parse_tagged_nonempty_str_sexp "fn" fn_sx,
              parse_tagged_sha256_sexp "src-sha256" sh_sx,
              parse_tagged_sha256_sexp "tgt-sha256" th_sx,
              parse_tagged_section_list "blocks" parse_block_cert_sexp blks_sx,
              parse_optional_tail_with_lrat tail with
        | inr fn_nm, inr sh, inr th, inr blks, inr (lcis, aws, ro, opt_pf) =>
            inr (mk_proof_certificate fn_nm sh th blks lcis aws ro opt_pf)
        | inl err, _, _, _, _ => inl err
        | _, inl err, _, _, _ => inl err
        | _, _, inl err, _, _ => inl err
        | _, _, _, inl err, _ => inl err
        | _, _, _, _, inl err => inl err
        end
      else inl "unsupported certificate schema tag (expected cert-v1)"
  | _ => inl "malformed cert-v1 root S-expression"
  end.

Definition parse_cert (input : string) : string + proof_certificate :=
  match parse_sexp input with
  | inl err => inl (diag "cert-parse" err)
  | inr root =>
      match parse_cert_sexp root with
      | inl err => inl (diag "cert-parse" err)
      | inr cert => inr cert
      end
  end.

Theorem parse_cert_sexp_wf : forall root cert,
  parse_cert_sexp root = inr cert -> wf_proof_certificate cert = true.
Proof.
  intros [| | [| [schema_tag | |] [| fn_sx [| sh_sx [| th_sx [| blks_sx tail]]]]]] cert H;
    cbn in H; try discriminate.
  destruct (String.eqb schema_tag "cert-v1"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "fn" fn_sx) as [| fn_nm] eqn:Hfn; [discriminate |].
  destruct (parse_tagged_sha256_sexp "src-sha256" sh_sx) as [| sh] eqn:Hsh; [discriminate |].
  destruct (parse_tagged_sha256_sexp "tgt-sha256" th_sx) as [| th] eqn:Hth; [discriminate |].
  destruct (parse_tagged_section_list "blocks" parse_block_cert_sexp blks_sx)
    as [| blks] eqn:Hblks; [discriminate |].
  destruct (parse_optional_tail_with_lrat tail) as [| [[[lcis aws] ro] opt_pf]] eqn:Htail;
    [discriminate |].
  pose proof (parse_optional_tail_with_lrat_wf _ _ _ _ _ Htail) as (Hlcis & Haws & Hro).
  inversion H; subst; unfold wf_proof_certificate; cbn.
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hfn),
          (parse_tagged_sha256_ok _ _ _ Hsh),
          (parse_tagged_sha256_ok _ _ _ Hth),
          (parse_tagged_section_list_wf _ _ _ parse_block_cert_wf _ _ Hblks),
          Hlcis, Haws, Hro; reflexivity.
Qed.

Theorem parse_cert_wf : forall input cert,
  parse_cert input = inr cert -> wf_proof_certificate cert = true.
Proof.
  intros input cert H; unfold parse_cert in H.
  destruct (parse_sexp input) as [| root]; [discriminate |].
  destruct (parse_cert_sexp root) as [| c0] eqn:Es; [discriminate |].
  inversion H; subst c0; exact (parse_cert_sexp_wf root cert Es).
Qed.

