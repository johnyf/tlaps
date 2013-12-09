
(*
 * Coalescing transforms a formula to a satisfying-equiavelnt formula.
 * There are differnt kinds of coalescing:
   * 1) coalsecing non-leibzniz formulas into leibniz formulas. The resuled
   * formulas can then be used in first-order theorem provers.
   * 2) coalsecing non-propositional formulas into propositional ones. The
   * resulted formula can then be used in propositional temporal logic provers.
 *
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

val coalesce_fol : Expr.T.expr -> Expr.T.expr
