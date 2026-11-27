(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.CertFormat]: Umbrella Certificate Format, DIMACS/LRAT Parsers & Soundness

    Re-exports [CertFormatAst], [CertFormatParse], and [CertFormatGates],
    and provides tail-recursive DIMACS CNF and standard ASCII LRAT parsers
    ([parse_dimacs_cnf], [parse_ascii_lrat], [validate_dimacs_lrat_str])
    together with [validate_dimacs_lrat_str_sound]. *)

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
  LratCore.

From CertValidator Require Export
  CertFormatAst
  CertFormatParse
  CertFormatGates.

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

(** ** 7. Tail-Recursive DIMACS CNF & Standard ASCII LRAT Parsers ([D-01]) *)

Fixpoint split_lines_acc (cur_rev : list ascii) (acc : list string) (cs : list ascii)
  {struct cs} : list string :=
  match cs with
  | [] =>
      let last_ln := rev_chars_to_str_acc EmptyString cur_rev in
      rev_tr (last_ln :: acc)
  | c :: rest =>
      let n := nat_of_ascii c in
      if Nat.eqb n 10 then
        let ln := rev_chars_to_str_acc EmptyString cur_rev in
        split_lines_acc [] (ln :: acc) rest
      else if Nat.eqb n 13 then
        split_lines_acc cur_rev acc rest
      else
        split_lines_acc (c :: cur_rev) acc rest
  end.

Definition split_lines (s : string) : list string :=
  split_lines_acc [] [] (str_to_chars s).

Definition is_line_ws (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 32 || Nat.eqb n 9 || Nat.eqb n 11 || Nat.eqb n 12.

Fixpoint split_ws_tokens_acc (cur_opt : option (list ascii)) (acc : list string)
                             (cs : list ascii) {struct cs} : list string :=
  match cs with
  | [] =>
      match cur_opt with
      | None => rev_tr acc
      | Some rev_cs => rev_tr (rev_chars_to_str_acc EmptyString rev_cs :: acc)
      end
  | c :: rest =>
      if is_line_ws c then
        match cur_opt with
        | None => split_ws_tokens_acc None acc rest
        | Some rev_cs =>
            split_ws_tokens_acc None (rev_chars_to_str_acc EmptyString rev_cs :: acc) rest
        end
      else
        match cur_opt with
        | None => split_ws_tokens_acc (Some [c]) acc rest
        | Some rev_cs => split_ws_tokens_acc (Some (c :: rev_cs)) acc rest
        end
  end.

Definition split_ws_tokens (s : string) : list string :=
  split_ws_tokens_acc None [] (str_to_chars s).

Definition is_comment_toks (toks : list string) : bool :=
  match toks with
  | [] => true
  | t :: _ =>
      match t with
      | String c _ => Nat.eqb (nat_of_ascii c) 99
      | EmptyString => false
      end
  end.

Fixpoint find_dimacs_header (lines : list string) {struct lines}
  : string + (N * N * list string) :=
  match lines with
  | [] => inl "missing 'p cnf <vars> <clauses>' header in DIMACS CNF"
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        find_dimacs_header rest
      else
        match toks with
        | [p_tok; cnf_tok; nv_s; nc_s] =>
            if String.eqb p_tok "p" && String.eqb cnf_tok "cnf" then
              match parse_canonical_N nv_s, parse_canonical_N nc_s with
              | Some nv, Some nc => inr (nv, nc, rest)
              | _, _ => inl "invalid variable or clause count in DIMACS header"
              end
            else inl "expected 'p cnf <vars> <clauses>' header before clauses"
        | _ => inl "malformed 'p cnf <vars> <clauses>' DIMACS header"
        end
  end.

Fixpoint parse_dimacs_line_toks
  (max_var : N) (next_cid : positive) (cur_rev : list lit) (acc_rev : cnf)
  (toks : list string) {struct toks}
  : string + (positive * list lit * cnf) :=
  match toks with
  | [] => inr (next_cid, cur_rev, acc_rev)
  | tok :: rest =>
      if String.eqb tok "0" then
        parse_dimacs_line_toks max_var (Pos.succ next_cid) []
          ((next_cid, rev_tr cur_rev) :: acc_rev) rest
      else
        match parse_signed_lit_str tok with
        | Some (Zpos v) =>
            if (N.pos v <=? max_var)%N then
              parse_dimacs_line_toks max_var next_cid (Z.pos v :: cur_rev) acc_rev rest
            else inl "DIMACS literal exceeds declared num_vars bound"
        | Some (Zneg v) =>
            if (N.pos v <=? max_var)%N then
              parse_dimacs_line_toks max_var next_cid (Z.neg v :: cur_rev) acc_rev rest
            else inl "DIMACS literal exceeds declared num_vars bound"
        | _ => inl "invalid literal token in DIMACS CNF"
        end
  end.

Fixpoint parse_dimacs_lines
  (max_var expected_clauses : N)
  (next_cid : positive) (cur_rev : list lit) (acc_rev : cnf)
  (lines : list string) {struct lines} : string + cnf :=
  match lines with
  | [] =>
      match cur_rev with
      | _ :: _ => inl "unterminated clause without trailing 0 in DIMACS CNF"
      | [] =>
          if N.eqb (N.pred (N.pos next_cid)) expected_clauses then
            inr (rev_tr acc_rev)
          else inl "DIMACS clause count does not match 'p cnf' header"
      end
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        parse_dimacs_lines max_var expected_clauses next_cid cur_rev acc_rev rest
      else
        match parse_dimacs_line_toks max_var next_cid cur_rev acc_rev toks with
        | inl err => inl err
        | inr (next_cid', cur_rev', acc_rev') =>
            parse_dimacs_lines max_var expected_clauses next_cid' cur_rev' acc_rev' rest
        end
  end.

Definition parse_dimacs_cnf (input : string) : string + cnf :=
  match find_dimacs_header (split_lines input) with
  | inl err => inl err
  | inr (nv, nc, rest) => parse_dimacs_lines nv nc 1%positive [] [] rest
  end.

Fixpoint parse_lrat_lits_to_zero (acc_rev : list lit) (toks : list string) {struct toks}
  : string + (list lit * list string) :=
  match toks with
  | [] => inl "missing 0 terminator after LRAT literals"
  | tok :: rest =>
      if String.eqb tok "0" then inr (rev_tr acc_rev, rest)
      else
        match parse_signed_lit_str tok with
        | Some l => parse_lrat_lits_to_zero (l :: acc_rev) rest
        | None => inl "invalid literal in ASCII LRAT line"
        end
  end.

Fixpoint parse_lrat_pos_to_end (acc_rev : list positive) (toks : list string) {struct toks}
  : string + list positive :=
  match toks with
  | [] => inl "missing trailing 0 terminator in ASCII LRAT line"
  | [tok] =>
      if String.eqb tok "0" then inr (rev_tr acc_rev)
      else inl "expected trailing 0 terminator in ASCII LRAT line"
  | tok :: rest =>
      match parse_pos_str tok with
      | Some p => parse_lrat_pos_to_end (p :: acc_rev) rest
      | None => inl "invalid or non-positive clause hint ID in ASCII LRAT line"
      end
  end.

Definition parse_ascii_lrat_line (toks : list string) : string + lrat_step :=
  match toks with
  | [] => inl "empty LRAT line"
  | cid_s :: rest =>
      match parse_pos_str cid_s, rest with
      | Some cid, tag_s :: rest2 =>
          if String.eqb tag_s "d" then
            match parse_lrat_pos_to_end [] rest2 with
            | inr cids => inr (LRAT_Del cids)
            | inl err => inl err
            end
          else
            match parse_lrat_lits_to_zero [] rest with
            | inl err => inl err
            | inr (cl, hint_toks) =>
                match parse_lrat_pos_to_end [] hint_toks with
                | inr hints => inr (LRAT_Add cid cl hints)
                | inl err => inl err
                end
            end
      | _, _ => inl "malformed ASCII LRAT proof line"
      end
  end.

Fixpoint parse_ascii_lrat_lines (acc_rev : list lrat_step) (lines : list string)
  {struct lines} : string + list lrat_step :=
  match lines with
  | [] => inr (rev_tr acc_rev)
  | ln :: rest =>
      let toks := split_ws_tokens ln in
      if is_comment_toks toks then
        parse_ascii_lrat_lines acc_rev rest
      else
        match parse_ascii_lrat_line toks with
        | inl err => inl err
        | inr step => parse_ascii_lrat_lines (step :: acc_rev) rest
        end
  end.

Definition parse_ascii_lrat (input : string) : string + list lrat_step :=
  parse_ascii_lrat_lines [] (split_lines input).

Definition validate_dimacs_lrat_str (cnf_str lrat_str : string) : string + unit :=
  match parse_dimacs_cnf cnf_str, parse_ascii_lrat lrat_str with
  | inr f, inr pf =>
      if check_lrat_unsat f pf then inr tt
      else
        inl (diag "lrat-check"
          ("LRAT UNSAT proof (" ++ diag_nat_dec (length_tr pf) ++ " step(s)) verification failed"))
  | inl err, _ => inl (diag "dimacs-parse" err)
  | _, inl err => inl (diag "lrat-parse" err)
  end.

Theorem validate_dimacs_lrat_str_sound :
  forall cnf_str lrat_str,
    validate_dimacs_lrat_str cnf_str lrat_str = inr tt ->
    exists f pf,
      parse_dimacs_cnf cnf_str = inr f /\
      parse_ascii_lrat lrat_str = inr pf /\
      forall assign : positive -> bool, eval_cnf assign f = false.
Proof.
  intros cnf_str lrat_str H.
  unfold validate_dimacs_lrat_str in H.
  destruct (parse_dimacs_cnf cnf_str) as [| f] eqn:Ef; [discriminate H |].
  destruct (parse_ascii_lrat lrat_str) as [| pf] eqn:Ep; [discriminate H |].
  destruct (check_lrat_unsat f pf) eqn:Hchk; [| discriminate H].
  exists f, pf; split;
    [first [reflexivity | exact Ef]
    | split; [first [reflexivity | exact Ep] | exact (check_lrat_unsat_sound f pf Hchk)]].
Qed.
