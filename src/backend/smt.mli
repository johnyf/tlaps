(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

open Expr.T

module Smt2 : sig
    val fmt_smtlib : hyp list -> expr -> string;;
    val fmt_z3 : hyp list -> expr -> string;;
    val fmt_yices : hyp list -> expr -> string;;
    val fmt_spass : hyp list -> expr -> string;;
    val fmt_tptp : hyp list -> expr -> string;;
end;;