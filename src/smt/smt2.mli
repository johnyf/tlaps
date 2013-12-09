(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Expr.T

(* val fmt_expr : hyp list -> expr -> string list;; *)
val fmt_smtlib : hyp list -> expr -> string;;
val fmt_z3 : hyp list -> expr -> string;;
val fmt_yices : hyp list -> expr -> string;;
val fmt_spass : hyp list -> expr -> string;;
val fmt_tptp : hyp list -> expr -> string;;

val fmt_smtlib_fcncheck : hyp list -> expr -> string;;
val fmt_z3_fcncheck : hyp list -> expr -> string;;
val fmt_yices_fcncheck : hyp list -> expr -> string;;
val fmt_spass_fcncheck : hyp list -> expr -> string;;

val _fmt_smtlib : bool -> hyp list -> expr -> string;;
val _fmt_z3 : bool -> hyp list -> expr -> string;;
val _fmt_yices : bool -> hyp list -> expr -> string;;
val _fmt_spass : bool -> hyp list -> expr -> string;;
val _fmt_tptp : bool -> hyp list -> expr -> string;;
