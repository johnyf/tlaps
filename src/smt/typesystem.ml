(*
 * TLA+ type system
 *
 * Author: Hernán Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 34678 $";;

open Printf
open Property

(* open Smtcommons *)
module SSet = Set.Make (String)
module SMap = Map.Make (String)
(* module SMap = Smtcommons.SMap *)
(* module SSet = Smtcommons.SSet *)

let list_to_map ls = List.fold_left (fun m (fd,tp) -> SMap.add fd tp m) SMap.empty ls
let fieldList map = List.map (fun (f,_) -> f) (SMap.bindings map)

type tlatype = Bot | Bool | Int | Real | Str (* Basic types *)
    | P of tlatype                           (* Power set *)
    | Fcn of tlatype * tlatype               (* Function *)
    | Rec of tlatype SMap.t                  (* Record *)
    | Tup of tlatype list                    (* Tuple *) 

module TLAtype = 
  struct
    type t = tlatype

    let base = function
        | P s' -> s'
        | s -> s

    let rec to_string = function
        | Bot       -> "*"
        | Bool      -> "Bool"
        | Int       -> "Int"
        | Real      -> "Real"
        | Str       -> "Str"
        | P t       -> sprintf "Set(%s)" (to_string t)
        | Fcn (a,b) -> sprintf "(%s -> %s)" (to_string a) (to_string b)
        | Rec map   -> sprintf "Rec_<%s>" (typeMap_to_string map)
        | Tup es    -> sprintf "Tuple_[%s]" (String.concat ";" (List.map (fun t -> (to_string t)) es))
    and typeMap_to_string map = 
        String.concat "," (List.map (fun (f,t) -> sprintf "(%s:%s)" f (to_string t)) (SMap.bindings map))
    ;;

    let is_atomic = function
        | Bot | Bool | Str | Int | Real -> true
        | _ -> false
    ;;

    let rec eq x y = 
        match x,y with
        | P t, P u -> eq t u
        | Fcn (a,b), Fcn (a',b') -> eq a a' && eq b b'
        | Tup l1, Tup l2 -> l1 = l2
        | Rec m1, Rec m2 -> 
            let bs1 = SMap.fold (fun f t1 r -> 
                try let t2 = SMap.find f m2 in
                    eq t1 t2 :: r
                with Not_found -> 
                    false :: r
                ) m1 []
            in
            let bs2 = SMap.fold (fun f t1 r -> 
                try let t2 = SMap.find f m1 in
                    eq t1 t2 :: r
                with Not_found -> 
                    false :: r
                ) m2 []
            in
            List.for_all (fun b -> b) (bs1 @ bs2)
        | t,u when is_atomic t && is_atomic u -> t = u
        | _ -> false
    ;;

    let rec gt0 x y = 
        match x, y with
        | x, Bot          when x != Bot
            -> true
        | P a, P b ->
            gt0 a b
        | Fcn (a,b), Fcn (a',b') ->
            (gt0 a a' && eq b b') || 
            (eq a a' && gt0 b b') ||
            (gt0 a a' && gt0 b b')
        | Rec m1, Rec m2 ->
            let bs = SMap.fold (fun f t1 r -> 
                try let t2 = SMap.find f m2 in
                    gt0 t1 t2 :: r
                with Not_found -> 
                    true :: r
                ) m1 []
            in
            List.exists (fun b -> b) bs
        | Tup t1, Tup t2 -> 
            begin try List.exists2 (fun x y -> gt0 x y) t1 t2
            with Not_found | Invalid_argument _ | Failure _ -> false end
        | _ -> 
            false
            
    let rec gt x y = 
        match x, y with
        | x, Bot          when x != Bot
            -> true
        | P a, P b ->
            gt a b
        | Fcn (a,b), Fcn (a',b') ->
            (gt a a' && eq b b') || 
            (eq a a' && gt b b') ||
            (gt a a' && gt b b')
        | Real, Int
            -> true
        | Rec m1, Rec m2 ->
            let bs = SMap.fold (fun f t1 r -> 
                try let t2 = SMap.find f m2 in
                    gt t1 t2 :: r
                with Not_found -> 
                    true :: r
                ) m1 []
            in
            List.exists (fun b -> b) bs
        | Tup t1, Tup t2 -> 
            begin try List.exists2 (fun x y -> gt x y) t1 t2
            with Not_found | Invalid_argument _ | Failure _ -> false end
        | _ -> 
            false

    let compare x y = if eq x y then 0 else if gt y x then -1 else 1

    let rec merge_record f l1 l2 =
        let rec merge_record_aux l1 l2 = match l1, l2 with
        | [], ys -> ys
        | xs, [] -> xs
        | (x,t1)::xs, (y,t2)::ys when x = y -> (x, f t1 t2) :: (merge_record_aux xs ys)
        | (x,t1)::xs, (y,t2)::ys when String.compare x y = 1 -> (x,t1) :: (merge_record_aux xs ((y,t2)::ys))
        | (x,t1)::xs, (y,t2)::ys -> (y,t2) :: (merge_record_aux ((x,t1)::xs) ys)
        in
        list_to_map (merge_record_aux (SMap.bindings l1) (SMap.bindings l2))

    let merge_tuple f t1 t2 = 
        try List.map2 f t1 t2 with Invalid_argument _ -> [Bot]
    ;;

    let rec max t1 t2 = 
        match t1, t2 with
        | Rec l1, Rec l2 -> Rec (merge_record max l1 l2)
        | Tup t1, Tup t2 -> Tup (merge_tuple max t1 t2)
        | Fcn (a,b), Fcn (a',b') -> Fcn (max a a', max b b')
        | P a, P b -> P (max a b)
        | _ -> if gt t1 t2 then t1 else t2
    
    let rec max_numbers t1 t2 =
        match t1,t2 with
        | (Int | Real), (Int | Real) -> max t1 t2
        (* | (Nat | Int | Real | Bot), (Nat | Int | Real | Bot) -> max t1 t2 *)
        | Rec l1, Rec l2 -> Rec (merge_record max_numbers l1 l2)
        | Tup t1, Tup t2 -> Tup (merge_tuple max_numbers t1 t2)
        | Fcn (a,b), Fcn (a',b') -> Fcn (max_numbers a a', max_numbers b b')
        | P a, P b -> P (max_numbers a b)
        | _ -> raise Not_found
    
    let get_fieldtyp field = function
        | Rec m -> begin try SMap.find field m
                   with Not_found -> Bot end
        | _ -> Bot

    let rec to_safe_type = function
        | P t -> P (to_safe_type t)
        | Fcn (a,b) -> Fcn (to_safe_type a, to_safe_type b)
        | Rec m -> Rec (SMap.map to_safe_type m)
        | Tup l -> Tup (List.map to_safe_type l)
        (* | Str -> Str *)
        | _ -> Bot

    let rec apply_fcn f xs = 
        match f, xs with
        | Fcn (a,b), [x]     when x = a || gt x a -> b
        | Fcn (a,b), x :: xs when x = a || gt x a -> apply_fcn b xs
        (* | Fcn (a,b), [x]     when a = x -> b
        | Fcn (a,b), x :: xs when a = x -> apply_fcn b xs *)
        (* | Tup l, [Int] ->  *)
        | a, [] -> a
        | _ -> Bot
    
    let rec returns = function
        | Fcn (_, b) -> returns b
        | t -> t
    
    let rec args = function
        | Fcn (a, b) -> a :: args b
        | P t -> [t]
        | _ -> []
    
    let dot t h = 
        match t with
        | Rec rs -> begin try SMap.find h rs with Not_found -> Bot end
        | _ -> Bot
    
  end

(** From Option.default *)
let default x t = 
    match x,t with
    | _, Some v -> v
    | x, None -> x
;;

let expr_type : TLAtype.t option pfuncs = Property.make "Backend.Smt.ExprType" ;;
let remove_type e = remove e expr_type ;;
let has_type e = has e expr_type ;;
let typ e = if has e expr_type then get e expr_type else None ;;
let typbot e = default Bot (typ e) ;;
let typpbot e = default (P Bot) (typ e) ;;
let typ_to_str e = match typ e with Some t -> TLAtype.to_string t | None -> "____" ;;
let assign_type e t =
(* Util.eprintf "\t %a :: %s <<< %s" (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) e (typ_to_str e) (match t with Some t -> TLAtype.to_string t | None -> "____") ; *)
(* Util.eprintf "\t ex :: %s <<< %s" (typ_to_str e) (match t with Some t -> TLAtype.to_string t | None -> "____") ; *)
    let e = remove_type e in
    assign e expr_type t ;;
let (<<<) e (* (e:Expr.T.expr) *) t = assign_type e t ;;

let is_Bool e = typbot e = Bool ;;    
let is_Int e = typbot e = Int ;;    

module TLAtypeMap = Map.Make (TLAtype)

(*** types : mapping from symbol identifiers (strings) to TLAtype.t *)
class types = object (self) 
    val mutable m : TLAtype.t SMap.t = SMap.empty
    
    method getall = m

    method setmap m' = m <- m'
    
    method find (var:string) =
        try SMap.find var m
        with Not_found -> Bot

    method exists (var:string) = SMap.mem var m

    method update (var:string) (newt:TLAtype.t) =
        let old = self#find var in
        let old, newt = match old, newt with
        | t1, t2 when t1 = t2  -> old, t2
        | Rec l1, Rec l2       -> Bot, Rec (TLAtype.merge_record TLAtype.max l1 l2)
        | Tup t1, Tup t2       -> Bot, Tup (TLAtype.merge_tuple TLAtype.max t1 t2)
        | Fcn (a,b), Fcn (c,d) -> old, Fcn (TLAtype.max a c, TLAtype.max b d)
        | s, Fcn (a,Bot)       -> old, Fcn (a,s)
        | P s, P Bot           -> old, P s
        | s, P Bot             -> old, P s
        | _                    -> old, newt
        in
        if (((newt == Bot && not (self#exists var)) ||
            (newt != Bot && TLAtype.gt newt old)))   (*** updates only if new_type > old_type *)
            then (
(* Printf.eprintf ">>> updating: %s :: %s\n" var (TLAtype.to_string newt) ; *)
                m <- SMap.add var newt m)

    method remove (var:string) = 
(* Printf.eprintf ">>> remove:   %s :: %s\n" var (TLAtype.to_string (self#find var)) ; *)
        m <- SMap.remove var m
    
    method reset = m <- SMap.empty 
    
    method sprint_all = String.concat "\n" (List.map (fun (id,typ) -> sprintf "  %s : %s" id (TLAtype.to_string typ)) (SMap.bindings m))

    (*** mapping from TLAtype to list of identifiers (like equivalence classes of types) *)
    method to_TLAtypeMap =
        let tlamap = ref TLAtypeMap.empty in
        let add_aux k t = 
            let ks = try TLAtypeMap.find t !tlamap 
                    with Not_found -> []
            in
            tlamap := TLAtypeMap.add t (ks @ [k]) (!tlamap)
        in
        SMap.iter add_aux m ;
        !tlamap
end
