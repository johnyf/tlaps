(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T

module SSet : Set.S with type elt = string ;;

module StringList : sig
    type t = string list
    val compare : t -> t -> int
end ;;

module SSMap : Map.S with type key = StringList.t ;;

module Int : sig
    type t = int
    val compare : t -> t -> int
end ;;

module ISet : Set.S with type elt = Int.t ;;

val ( |> ) : 'a -> ('a -> 'b) -> 'b ;;
val ( |>> ) : 'a * 'b -> ('a -> 'c) -> 'c * 'b ;;
val ( ||> ) : 'a * 'b -> ('b -> 'c) -> 'a * 'c ;;
val kk : unit -> 'a -> 'a ;;
val tap : ('a -> unit) -> 'a -> 'a ;;
val pairself : ('a -> 'b) -> ('a * 'a) -> ('b * 'b) ;;

val print_prop : unit -> Format.formatter -> Expr.T.expr -> unit ;;

(* val printscx : hyp list -> unit ;; *)

(* exception Unification_failed of string ;;
exception Unsupported_type of string ;;
exception Untyped_symbol of string ;;
exception Infer_other of string ;;
exception No_function_domain of string ;;
exception Unsupported_expression of expr ;; *)

val filter_true  : expr list -> expr list ;;
val filter_false : expr list -> expr list ;;

val smt_id : string -> string ;;
val fof_id_vars : bool -> string -> string ;;
val lookup_id : hyp list -> int -> string ;;
val is_bvar : hyp list -> int -> bool ;;

val applyint2u :   unit Property.pfuncs ;;
val apply_int2u :  'a Property.wrapped -> bool ;;
val applystr2u :   unit Property.pfuncs ;;
val apply_str2u :  'a Property.wrapped -> bool ;;
val applyu2bool :  unit Property.pfuncs ;;
val apply_u2bool : 'a Property.wrapped -> bool ;;
val fmtasint :     unit Property.pfuncs ;;
val fmt_as_int :   'a Property.wrapped -> bool ;;
val fmtasbool :    unit Property.pfuncs ;;
val fmt_as_bool :  'a Property.wrapped -> bool ;;
val isconc :       unit Property.pfuncs ;;
val is_conc :      'a Property.wrapped -> bool ;;
val isFld :       unit Property.pfuncs ;;
val is_Fld :      'a Property.wrapped -> bool ;;

(* val is_bounded_var : string -> bool ;; *)
val is_nonbasic_var : string -> bool ;;
val boundvar : unit Property.pfuncs ;;
val has_boundvar : expr -> bool ;;
val is_field : string -> bool ;;
(* val quant_id : string -> string ;; *)

val unditto : bound list -> bound list ;;
val add_bs_ctx : bound list -> hyp list -> hyp list ;;

val n_to_list : int -> int list ;;
(* val concat0 : string -> 'a list -> string ;; *)
val concat1 : ('a -> string, unit, string) format -> 'a list -> string ;;
val concat2 : ('a -> string, unit, string) format -> 'a list -> string ;;
val remove_repeated : 'a list -> 'a list ;;

val ctr : int ref ;;
val unique_id : unit -> int ;;
val fresh_name : unit -> string ;;
val fresh_id : unit -> string ;;

val prime : string -> string ;;
val unprime_id : string -> string ;;

val mk_string : string -> string;;

val split_domain :
  quantifier ->
  expr ->
  (Util.hint * kind * bound_domain) list ->
  bound list ->
  (Util.hint * kind * bound_domain) list * expr
;;

val deconj : expr -> expr list;;
val deimpl : expr -> expr list * expr ;;
val unroll_seq : sequent -> expr ;;
val opaque : ?strong:bool -> hyp list -> expr -> expr ;;

val proc_assumptions :
  (hyp list -> expr -> (hyp * hyp list) list -> 'a) ->
  (hyp * hyp list) list -> 'a list ;;
val preprocess_context : 'a list -> ('a * 'a list) list ;;

(* val arity : expr -> int ;; *)

val fresh_bound_to_exp : string Property.wrapped -> expr -> expr * hyp ;;

val get_operators : hyp list -> expr -> string list ;;
val free_vars : hyp list -> expr -> string list ;;

val record_ids : int SSMap.t ref ;;
val add_record_id : string list -> int ;;
val get_recid : string list -> int ;;

val field_ids : SSet.t ref ;;
val add_field : string -> unit ;;
val add_field_prefix : string -> string ;;

val tla_op_set : SSet.t ref ;;
val add_tla_op : SSet.elt -> unit ;;
(* val returns_bool : hyp list -> expr -> bool ;; *)

val nonbasic_ops : (hyp list * expr) Typesystem.SMap.t ref ;;
val nonbasic_prefix : string ;;
(* val add_nonbasic_op : string -> hyp list -> expr -> unit ;;
val remove_nonbasic_op : string -> unit ;;
val find_nonbasic_op : hyp list -> expr -> string ;; *)

val chooses : (hyp list * expr) Typesystem.SMap.t ref ;;
val add_choose : string -> hyp list -> expr -> unit ;;

type provermode = Smtlib | CVC3 | Z3 | Yices | Spass | Fof ;;
val mode : provermode ref ;;

val simplefacts : (hyp list * Expr.T.expr) list ref ;;
val add_simplefact : hyp list -> expr -> unit ;;
(* val mem_simplefacts : hyp list -> expr -> bool ;; *)
val remove_simplefact : expr list -> unit ;;
val simp_simplefacts : hyp list -> expr -> expr ;;

val perms : 'a list -> ('a * 'a) list ;;

val is_term : expr -> bool ;;
val is_domain : expr -> bool ;;

val tuple_id : Typesystem.TLAtype.t list -> string ;;
val tuples : Typesystem.TLAtype.t list list ref ;;
val add_tuple : Typesystem.TLAtype.t list -> unit ;;

(* val flatten_conj : expr -> expr ;;
val flatten_disj : expr -> expr ;;
val simp_trivial : expr -> expr ;; *)

val unprime : hyp list -> expr -> expr ;;
val renameb : hyp list -> expr -> expr ;;
(* val upperbv : hyp list -> expr -> expr ;; *)

(* val flag_nat_cond : unit Property.pfuncs ;; *)
(* val apply_nat_cond : expr -> bool ;; *)
val newvars : (hyp list * expr) Typesystem.SMap.t ref ;;
val mk_newvar_id : hyp list -> expr -> string ;;
val unspec : hyp list -> expr -> expr ;;
val insert_intdiv_cond : hyp list -> expr -> expr ;;
