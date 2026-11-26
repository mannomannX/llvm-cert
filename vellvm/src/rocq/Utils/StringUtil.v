From Stdlib Require Import Program String Ascii List Decimal ZArith.
From Vellvm.Utils Require Import ListUtil.
Import ListNotations.
Open Scope string.

(* Reduction on a string of the shape ["foo" ++ show(i) ++ ...]
   breaks "foo" into a sequence of [Chars], rendering the goal unreadable.
   We prevent reduction in [append] as a quick fix.
 *)
Arguments append : simpl never.

Fixpoint string_fold_left {A} (f : A -> ascii -> A) (s:string) (acc:A) : A :=
  match s with
  | EmptyString => acc
  | String ch s =>
      string_fold_left f s (f acc ch)
  end.

Definition rev_string (s : string) : string
  := string_fold_left (fun acc x => String x acc) s EmptyString.

Definition string_of_list_ascii_tail_rec (s : list ascii) : string
  := rev_string (fold_left (fun acc ch => String ch acc) s EmptyString).

Definition list_ascii_of_string_tail_rec (s : string) : list ascii
  := rev_tail_rec (string_fold_left (fun acc ch => ch :: acc) s []).

(* The following is reproduced from the QuickChick library to avoid a heavy dependency *)
Section Show.

  Fixpoint push_str_rev (s : string) (acc : list ascii) : list ascii :=
    match s with
    | EmptyString => acc
    | String c rest => push_str_rev rest (c :: acc)
    end.

  Fixpoint rev_chars_to_string_go (cs : list ascii) (acc : string) : string :=
    match cs with
    | [] => acc
    | c :: rest => rev_chars_to_string_go rest (String c acc)
    end.

  Definition rev_chars_to_string (cs : list ascii) : string :=
    rev_chars_to_string_go cs EmptyString.

  Fixpoint push_chars_n (c : ascii) (n : nat) (acc : list ascii) : list ascii :=
    match n with
    | O => acc
    | S n' => push_chars_n c n' (c :: acc)
    end.

  Fixpoint push_uint_rev (n : uint) (acc : list ascii) : list ascii :=
    match n with
    | Nil => acc
    | D0 n' => push_uint_rev n' ("0"%char :: acc)
    | D1 n' => push_uint_rev n' ("1"%char :: acc)
    | D2 n' => push_uint_rev n' ("2"%char :: acc)
    | D3 n' => push_uint_rev n' ("3"%char :: acc)
    | D4 n' => push_uint_rev n' ("4"%char :: acc)
    | D5 n' => push_uint_rev n' ("5"%char :: acc)
    | D6 n' => push_uint_rev n' ("6"%char :: acc)
    | D7 n' => push_uint_rev n' ("7"%char :: acc)
    | D8 n' => push_uint_rev n' ("8"%char :: acc)
    | D9 n' => push_uint_rev n' ("9"%char :: acc)
    end.

  Definition push_int_rev (n : int) (acc : list ascii) : list ascii :=
    match n with
    | Pos n' => push_uint_rev n' acc
    | Neg n' => push_uint_rev n' ("-"%char :: acc)
    end.

  Definition push_Z_rev (n : Z) (acc : list ascii) : list ascii :=
    push_int_rev (Z.to_int n) acc.

  Definition push_N_rev (n : N) (acc : list ascii) : list ascii :=
    push_Z_rev (Z.of_N n) acc.

  Definition push_nat_rev (n : nat) (acc : list ascii) : list ascii :=
    push_uint_rev (Nat.to_uint n) acc.

  Definition push_bool_rev (b : bool) (acc : list ascii) : list ascii :=
    push_str_rev (if b then "true" else "false") acc.

  Fixpoint push_sep_tail_rev {A : Type} (sep : string) (f : A -> list ascii -> list ascii)
    (l : list A) (acc : list ascii) : list ascii :=
    match l with
    | [] => acc
    | h :: t => push_sep_tail_rev sep f t (f h (push_str_rev sep acc))
    end.

  Definition push_sep_rev {A : Type} (sep : string) (f : A -> list ascii -> list ascii)
    (l : list A) (acc : list ascii) : list ascii :=
    match l with
    | [] => acc
    | h :: t => push_sep_tail_rev sep f t (f h acc)
    end.

  Definition contents {A : Type} (s : A -> string) (l : list A) : string :=
    rev_chars_to_string (push_sep_rev "; " (fun x acc => push_str_rev (s x) acc) l []).

  Class Show (A : Type) : Type :=
    { show : A -> string }.

  Definition show_uint (n : uint) : string :=
    rev_chars_to_string (push_uint_rev n []).

  Definition show_int (n : int) : string :=
    match n with
    | Pos n => show_uint n
    | Neg n => String "-" (show_uint n)
    end.

  Definition show_nat (n : nat) : string :=
    show_uint (Nat.to_uint n).

  Definition show_bool (b : bool) : string :=
    match b with
    | true => "true"
    | false => "false"
    end.

  Definition show_Z (n : Z) : string :=
    show_int (Z.to_int n).

  Definition show_N : N -> string :=
    show_Z ∘ Z.of_N.

  #[global] Instance showUint : Show uint :=
    {|
      show := show_uint
    |}.

  #[global] Instance showInt : Show int :=
    {|
      show := show_int
    |}.

  #[global] Instance showNat : Show nat :=
    {|
      show := show_nat
    |}.

  #[global] Instance showBool : Show bool :=
    {|
      show := show_bool
    |}.

  #[global] Instance showZ : Show Z :=
    {|
      show := show_Z
    |}.

  #[global] Instance showN : Show N :=
    {|
      show := show_N
    |}.

  Fixpoint from_list (s : list ascii) : string :=
    match s with
    | [] => EmptyString
    | c :: s' => String c (from_list s')
    end.

  Definition unit_digit (n : nat) : ascii :=
    ascii_of_nat ((n mod 10) + 48 (* 0 *)).

  Definition three_digit (n : nat) : string :=
    let n0 := unit_digit n in
    let n1 := unit_digit (n / 10) in
    let n2 := unit_digit (n / 100) in
    from_list [n2; n1; n0].

  Definition digit_of_ascii (c : ascii) : option nat :=
    let n := nat_of_ascii c in
    if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
      Some (n - 48)
    else
      None.

  Definition unthree_digit (c2 c1 c0 : ascii) : option ascii :=
    let doa := digit_of_ascii in
    match doa c2, doa c1, doa c0 with
    | Some n2, Some n1, Some n0 =>
        Some (ascii_of_nat (n2 * 100 + n1 * 10 + n0))
    | _, _, _ => None
    end.

  Definition push_three_digit_rev (n : nat) (acc : list ascii) : list ascii :=
    let n0 := unit_digit n in
    let n1 := unit_digit (n / 10) in
    let n2 := unit_digit (n / 100) in
    n0 :: n1 :: n2 :: acc.

  Fixpoint push_quoted_string_body_rev (s : string) (acc : list ascii) : list ascii :=
    match s with
    | EmptyString => acc
    | String c s' =>
        let n := nat_of_ascii c in
        let acc' :=
          if ascii_dec c "009" (* TAB *) then push_str_rev "\t" acc
          else if ascii_dec c "010" (* NEWLINE *) then push_str_rev "\n" acc
          else if ascii_dec c "013" (* CARRIAGE RETURN *) then push_str_rev "\r" acc
          else if ascii_dec c """" (* DOUBLEQUOTE *) then push_str_rev "\""" acc
          else if ascii_dec c "\" (* BACKSLASH *) then push_str_rev "\\" acc
          else if ((n <? 32)%nat (* SPACE *) || (126 <? n)%nat (* ~ *))%bool
               then push_three_digit_rev n ("\"%char :: acc)
               else c :: acc in
        push_quoted_string_body_rev s' acc'
    end.

  Definition push_quoted_string_rev (s : string) (acc : list ascii) : list ascii :=
    """"%char :: push_quoted_string_body_rev s (""""%char :: acc).

  Definition show_quoted_string (s : string) : string :=
    rev_chars_to_string (""""%char :: push_quoted_string_body_rev s []).

  #[global] Instance showString : Show string :=
    {|
      show s := rev_chars_to_string (push_quoted_string_rev s [])
    |}.

  
  #[global] Instance showPair {A B : Type} `{_ : Show A} `{_ : Show B} : Show (A * B) :=
    {|
      show p := match p with (a,b) => ("(" ++ show a ++ ", " ++  show b ++ ")")%string end
    |}.
  
  #[global] Instance showOpt {A : Type} `{_ : Show A} : Show (option A) :=
    {|
      show x := match x with
                | Some x => "Some " ++ (show x)
                | None => "None"
                end
    |}.

  #[global] Instance showList {A : Type} `{_ : Show A} : Show (list A) :=
    {|
      show l :=
        rev_chars_to_string
          ("]"%char :: push_sep_rev "; " (fun x acc => push_str_rev (show x) acc) l ["["%char])
    |}.

  Definition newline := String "010" ""%string.
  
End Show.
