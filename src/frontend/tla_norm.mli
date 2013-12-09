

(*
 *A set of normalization functions for expanding TLA built-in formulas

 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

val unchanged_normalize : unit Expr.Visit.scx -> Expr.T.expr -> Expr.T.expr
val action_normalize : unit Expr.Visit.scx -> Expr.T.expr -> Expr.T.expr
