(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

open Expr.T

val gr0 : expr -> expr;;
val gr1 : hyp list -> expr -> expr;;
val unbound : hyp list -> expr -> expr;;