(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(*
Revision.f "$Rev: 29867 $";;
*)

let rev = ref "";;
let f x = if x > !rev then rev := x;;

f "$Rev: 29867 $";;

let get () = String.sub !rev 6 (String.length !rev - 8);;
