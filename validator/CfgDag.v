(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Symbolic CFG DAG Representation & Evaluator ([CertValidator.CfgDag])

    Defines [cfg_dag], [dag_outcome], [eval_cfg_dag], and [wf_cfg_dag] shared
    between [CertValidator.CertValidator] and the machine-code ISA semantics
    ([Rv64Sem], [A64CoreSem]), breaking the circular dependency on the LLVM
    certificate validator. *)

From Stdlib Require Import
  ZArith
  PArith
  Strings.String
  List
  Bool.
Import ListNotations.

From Vellvm Require Import
  Numeric.Integers
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.DynamicValues.

From CertValidator Require Import
  CertFormatAst
  AlgRulesEval
  AlgRulesNormBinop.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.

Inductive cfg_dag : Set :=
| CD_Unreachable
| CD_RetVoid
| CD_RetScalar (w : positive) (ret_e : cert_expr)
| CD_Eval (w : positive) (step_e : cert_expr) (next : cfg_dag)
| CD_BlockAssume (uas : list ub_assumption) (next : cfg_dag)
| CD_Branch (cond : cert_expr) (on_true on_false : cfg_dag).

Variant dag_outcome {Pa : Params} : Type :=
| DO_UB
| DO_Ret (dv : @dvalue Pa).

Fixpoint eval_cfg_dag {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (d : cfg_dag)
  {struct d} : @dag_outcome Pa :=
  match d with
  | CD_Unreachable => DO_UB
  | CD_RetVoid => DO_Ret (DVALUE_Base DVALUE_None)
  | CD_RetScalar _ ret_e =>
      match eval_closed_cert_expr penv foracle ret_e with
      | raise_ret dv => DO_Ret dv
      | _ => DO_UB
      end
  | CD_Eval _ step_e next =>
      match eval_closed_cert_expr penv foracle step_e with
      | raise_ret _ => eval_cfg_dag penv foracle next
      | _ => DO_UB
      end
  | CD_BlockAssume _ next =>
      eval_cfg_dag penv foracle next
  | CD_Branch cond on_true on_false =>
      match eval_closed_cert_expr penv foracle cond with
      | raise_ret (DVALUE_Base (@DVALUE_I _ 1%positive cbit)) =>
          if (@Integers.unsigned 1 cbit =? 1)%Z
          then eval_cfg_dag penv foracle on_true
          else eval_cfg_dag penv foracle on_false
      | _ => DO_UB
      end
  end.

Fixpoint wf_cfg_dag (allowed : list (string * positive)) (d : cfg_dag)
  {struct d} : bool :=
  match d with
  | CD_Unreachable | CD_RetVoid => true
  | CD_RetScalar w ret_e =>
      wt_cert_expr [] ret_e &&
      Pos.eqb (cert_expr_bit_width ret_e) w &&
      is_let_free_expr ret_e &&
      vars_subset_b (collect_free_vars [] ret_e) allowed
  | CD_Eval w step_e next =>
      wt_cert_expr [] step_e &&
      Pos.eqb (cert_expr_bit_width step_e) w &&
      is_let_free_expr step_e &&
      vars_subset_b (collect_free_vars [] step_e) allowed &&
      wf_cfg_dag allowed next
  | CD_BlockAssume _ next =>
      wf_cfg_dag allowed next
  | CD_Branch cond on_true on_false =>
      wt_cert_expr [] cond &&
      Pos.eqb (cert_expr_bit_width cond) 1%positive &&
      is_let_free_expr cond &&
      vars_subset_b (collect_free_vars [] cond) allowed &&
      wf_cfg_dag allowed on_true &&
      wf_cfg_dag allowed on_false
  end.
