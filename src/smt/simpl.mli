(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

open Expr.T

val abstract : hyp list -> expr -> expr ;;
val simpl_eq : hyp list -> expr list -> expr list ;;