From Vellvm Require Import
  Utils
  Syntax
  EOU
  DynamicValues
  Params.

Section Compare.
  Context {Pa : Params}.

  (* The scalar operands [icmp] accepts (LangRef: "integer or pointer
     typed"): comparing poison with any of them yields poison. *)
  Definition is_icmp_operand (d : dvalue_base) : bool :=
    match d with
    | DVALUE_I _ _ | DVALUE_Iptr _ | DVALUE_Pointer _ => true
    | _ => false
    end.

  Definition eval_icmp_base (samesign:bool) (icmp : icmp) (v1 v2 : dvalue_base) : EOU dvalue_base.
    refine
      (match v1, v2 with
       | DVALUE_I sz1 i1, DVALUE_I sz2 i2 =>
           _
       | DVALUE_Iptr i1, DVALUE_Iptr i2 => eval_int_icmp samesign icmp i1 i2
       | DVALUE_Poison, DVALUE_Poison => ret DVALUE_Poison
       | DVALUE_Poison, _ => if is_icmp_operand v2 then ret DVALUE_Poison else raise_error "ill_typed-iop"
       | _, DVALUE_Poison => if is_icmp_operand v1 then ret DVALUE_Poison else raise_error "ill_typed-iop"
       | DVALUE_Pointer a1, DVALUE_Pointer a2 =>
           let i1 := ptr_to_int a1 in
           let i2 := ptr_to_int a2 in
           eval_int_icmp samesign icmp i1 i2
       | _, _ => raise_error ("eval_icmp_base: ill_typed-icmp: " ++ show v1 ++ ", " ++ show v2)
       end).
    destruct (Pos.eq_dec sz1 sz2); subst.
    - exact (eval_int_icmp samesign icmp i1 i2).
    - exact (raise_error ("eval_icmp_base: ill_typed-icmp: " ++ show v1 ++ ", " ++ show v2)).
  Defined.
  Arguments eval_icmp_base _ _ _ _ : simpl nomatch.

  Definition eval_icmp (samesign:bool) (icmp : icmp) (v1 v2 : dvalue) : EOU dvalue :=
    match v1, v2 with
    | DVALUE_Base dv1, DVALUE_Base dv2 =>
        DVALUE_Base <$> (eval_icmp_base samesign icmp dv1 dv2)
    | DVALUE_Base dv1, DVALUE_Array true elts2 =>
        match dv1 with
        | DVALUE_Poison =>
            elts2' <- map_monad dvalue_to_dvalue_base elts2 ;;
            val <- vec_loop (eval_icmp_base samesign icmp)
                     (List.combine (repeat DVALUE_Poison (Datatypes.length elts2')) elts2') ;;
            ret (canonicalize_vector (List.map DVALUE_Base val))
        | _ => raise_error "eval_icmp_base: ill-typed icmp"
        end
    | DVALUE_Array true elts1, DVALUE_Base dv2 =>
        match dv2 with
        | DVALUE_Poison =>
            elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
            val <- vec_loop (eval_icmp_base samesign icmp)
                     (List.combine elts1' (repeat DVALUE_Poison (Datatypes.length elts1'))) ;;
            ret (canonicalize_vector (List.map DVALUE_Base val))
        | _ => raise_error "eval_icmp_base: ill-typed icmp"
        end
    | (DVALUE_Array true elts1), (DVALUE_Array true elts2) =>
        let n := N.length elts1 in
        let m := N.length elts2 in
        if (n =? m)%N then
          elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
          elts2' <- map_monad dvalue_to_dvalue_base elts2 ;;
          val <- vec_loop (eval_icmp_base samesign icmp) (List.combine elts1' elts2') ;;
          ret (canonicalize_vector (List.map DVALUE_Base val))
        else
          raise_ub "icmp of different-length vectors"
    | _, _ => raise_error "eval_icmp_base: ill-typed icmp"
    end.

  Arguments eval_icmp _ _ _ _ : simpl nomatch.
    
End Compare.
