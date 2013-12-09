(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Expr.T

val types : Typesystem.types;;

type inferAction = 
  | Update_fact 
  | Update_safe
  (* | Get_type *)
  (* | Get_type_bounds *)
;;

val type_inference : hyp list -> expr list -> unit ;;

(* backend/smtground.ml *)
val type_infer :  inferAction -> hyp list -> expr -> Typesystem.TLAtype.t ->Typesystem.TLAtype.t ;;
val infer_facts_bounded : hyp list -> expr -> unit ;;

val get_type : hyp list -> expr -> Typesystem.TLAtype.t ;;

(* val get_all_types_fact : ?min:Typesystem.TLAtype.t -> hyp list -> expr -> unit ;; *)

val paint_types : hyp list -> expr -> expr ;;
(* val paint_types : hyp list -> 'a Property.wrapped -> 'a Property.wrapped ;; *)
val paint_bs : hyp list -> bound list -> bound list ;;
(* val tfind : 'a Property.wrapped -> string -> Typesystem.TLAtype.t ;; *)
(* val typetree : hyp list -> expr -> unit ;; *)