(*
 * expr/constness.ml --- detect constant operators
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

val is_const : 'a Property.wrapped -> bool

val propagate : unit E_visit.map
