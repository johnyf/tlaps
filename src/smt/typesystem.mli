(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* backend/yices.ml *)
module SMap : Map.S with type key = string;;
type tlatype =
    | Bot
    | Bool
    | Int
    | Real
    | Str
    | P of tlatype
    | Fcn of tlatype * tlatype
    | Rec of tlatype SMap.t
    | Tup of tlatype list
;;
module SSet : Set.S with type elt = string;;

module TLAtypeMap : Map.S with type key = tlatype ;;
class types : object
  method find : string -> tlatype
  method update : string -> tlatype -> unit
  method remove : string -> unit
  method setmap : tlatype SMap.t -> unit
  method getall : tlatype SMap.t
  method to_TLAtypeMap : string list TLAtypeMap.t

  method exists : string -> bool
  method sprint_all : string
  method reset : unit
end
;;

module TLAtype : sig
  type t = tlatype
  val is_atomic : t -> bool
  val to_string : t -> string
  val apply_fcn : t -> t list -> t
  val max_numbers : t -> t -> t
  val max : t -> t -> t
  val eq : t -> t -> bool
  val gt : t -> t -> bool
  val gt0 : t -> t -> bool
  val returns : t -> t
  val to_safe_type : t -> t
  val base : t -> t
  val get_fieldtyp : string -> t -> t
  val args : t -> t list
  val dot : t -> string -> t
end;;

val list_to_map : (string * 'a) list -> 'a SMap.t;;

val expr_type : TLAtype.t option Property.pfuncs ;;
val ( <<< ) : 'a Property.wrapped -> TLAtype.t option -> 'a Property.wrapped ;;
val assign_type : 'a Property.wrapped -> TLAtype.t option -> 'a Property.wrapped ;;
val remove_type : 'a Property.wrapped -> 'a Property.wrapped ;;
val has_type : 'a Property.wrapped -> bool ;;
val typ : 'a Property.wrapped -> TLAtype.t option;;
val typbot : 'a Property.wrapped -> TLAtype.t ;;
val typpbot : 'a Property.wrapped -> TLAtype.t ;;
val typ_to_str : 'a Property.wrapped -> string ;;


(* A persistent union-find data structure.

   The datatype [t] maintains a partition of the set [0,1,...,n-1],
   where [n] is the value passed to [create]. *)

type t

val create : int -> t
val find : t -> int -> int
val union : t -> int -> int -> t
