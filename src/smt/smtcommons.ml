(*
 * backend/smt/smtcommons.ml --- SMT backend commons
 *
 * Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 32384 $";;

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf

open Typesystem

module B = Builtin;;

module SSet = Set.Make (String)
module SMap = Typesystem.SMap

module StringList = struct
    include List
    type t = string list
    let rec compare xs ys = 
        begin match xs, ys with
        | [], [] -> 0
        | _, [] -> 1
        | [], _ -> -1
        | x :: xs, y :: ys -> 
            let c = String.compare x y in
            if c = 0 then compare xs ys else c
        end
end ;;

module SSMap = Map.Make (StringList)

module Int = struct
    type t = int
    let compare i j = if i < j then -1 else if i = j then 0 else 1
end ;;

module ISet = Set.Make (Int)

(** Combinators *)
let ( |> ) x f = f x ;;
let ( |>> ) (x, y) f = (f x, y) ;;
let ( ||> ) (x, y) f = (x, f y) ;;
let kk x y = ignore x ; y ;;
let tap f = fun x -> (f x; x) ;;
let pairself f (x, y) = (f x, f y) ;;

type provermode = Smtlib | CVC3 | Z3 | Yices | Spass | Fof ;;
let mode = ref Smtlib ;;

let print_prop () = (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) ;;

(* exception Untyped_symbol of string
exception Unification_failed of string
exception Unsupported_type of string
exception Infer_other of string
exception No_function_domain of string
exception Unsupported_expression of Expr.T.expr *)

let filter_true es  = List.filter (fun e -> match e.core with Internal B.TRUE  -> false | _ -> true) es ;;
let filter_false es = List.filter (fun e -> match e.core with Internal B.FALSE -> false | _ -> true) es ;;

let boundvar : unit pfuncs = Property.make "Backend.Smt.boundvar"
let has_boundvar x = Property.has x boundvar ;;
let is_bvar cx n =  
    assert (n > 0 && n <= List.length cx) ;
    has_boundvar (List.nth cx (n - 1))
;;

(* FIXME
   1. This is not injective.
*)
let smt_id id =
  if id = "_" then (failwith "SMT bug: identifier \"_\"") else
  let id = if Str.string_match (Str.regexp "^[0-9].*") id 0 then "x"^id else id in
  let rep s r id = Str.global_replace (Str.regexp s) r id in
  id
  |> Tla_parser.pickle
  |> rep "'" "__"
  |> rep "^max$" "max__"        (** max is a reserved word in Z3 v4.0 *)
  |> rep "^u$" "u__"            (** c is also a sort: not allowed in CVC3 *)
  |> rep "^status$" "X__status" (** keyword in Spass *)
;;
let fof_id_vars is_bv id =
  let is_lowercase s = s.[0] = (Char.lowercase s.[0]) in
  let is_uppercase s = s.[0] = (Char.uppercase s.[0]) in
  if !mode = Fof 
  (* then (if is_bvar cx n then String.capitalize id else String.uncapitalize id)  *)
  then (if is_bv 
        then (if is_uppercase id then id else "B"^id) 
        else (if is_lowercase id then id else "x"^id)) 
  else id
;;
let lookup_id cx n =  
(* Printf.eprintf "[lookup_id %d <= %d]" n (List.length cx) ; *)
    assert (n > 0 && n <= List.length cx) ;
    let id = hyp_name (List.nth cx (n - 1)) in
    fof_id_vars (is_bvar cx n) id
;;

(* let bound_prefix = "x__" ;; *)
(* let is_bounded_var id = 
    try ((String.sub id 0 (String.length bound_prefix)) = bound_prefix) with _ -> false ;; *)

let nonbasic_prefix = "a__" ;;
let is_nonbasic_var id = 
    try ((String.sub id 0 (String.length nonbasic_prefix)) = nonbasic_prefix) with _ -> false ;;

let field_prefix = "f__" ;;
let is_field id = 
    try ((String.sub id 0 (String.length field_prefix)) = field_prefix) with _ -> false ;;

(* let quant_id id = if is_bounded_var id || is_nonbasic_var id || is_field id then id else (bound_prefix ^ (* smt_id *) id) ;; *)

let add_field_prefix s = if is_field s then s else (field_prefix ^ s) ;;

(****************************************************************************)

let applyint2u : unit pfuncs = Property.make "Backend.Smt.applyint2u"
let apply_int2u x = Property.has x applyint2u ;;

let applystr2u : unit pfuncs = Property.make "Backend.Smt.applystr2u"
let apply_str2u x = Property.has x applystr2u ;;

let applyu2bool : unit pfuncs = Property.make "Backend.Smt.applyu2bool"
let apply_u2bool x = Property.has x applyu2bool ;;

let fmtasint : unit pfuncs = Property.make "Backend.Smt.fmtasint"
let fmt_as_int x = Property.has x fmtasint ;;

let fmtasbool : unit pfuncs = Property.make "Backend.Smt.fmtasbool"
let fmt_as_bool x = Property.has x fmtasbool ;;

let isconc : unit pfuncs = Property.make "Backend.Smt.isconc" 
let is_conc x = Property.has x isconc ;;

let isFld : unit pfuncs = Property.make "Backend.Smt.isFld" 
let is_Fld x = Property.has x isFld ;;

(****************************************************************************)

let rec unditto = function
  | (_, _, Domain d) as b1 :: (h,k,Ditto) :: bs ->
      b1 :: unditto ((h,k,Domain d) :: bs)
  | b :: bs -> b :: unditto bs
  | [] -> []
;;

let add_bs_ctx bs cx : hyp list = 
  let bs = unditto bs in
  let hyps = List.mapi begin
    fun n (v, k, dom) -> 
      (* let v = assign v boundvar () in *)
      match dom with
      | No_domain -> Fresh (v, Shape_expr, k, Unbounded) @@ v
      | Domain d -> Fresh (v, Shape_expr, k, Bounded (app_expr (shift n) d, Visible)) @@ v
      | _ -> assert false
  end bs in
  List.rev hyps @ cx
;;

let rec n_to_list = function
  | 0 -> []
  | n -> (n_to_list (n-1)) @ [n] 
;;

let concat1 fmt ls = String.concat " " (List.map (sprintf fmt) ls) ;;
let concat2 fmt ls = String.concat "," (List.map (sprintf fmt) ls) ;;

let remove_repeated lst =
    let unique_set = Hashtbl.create (List.length lst) in
    List.iter (fun x -> Hashtbl.replace unique_set x ()) lst;
    Hashtbl.fold (fun x () xs -> x :: xs) unique_set [] ;;

let ctr = ref 0 ;;

let unique_id () = incr ctr ; !ctr ;;

let fresh_name () = "v" ^ string_of_int (unique_id ()) ;;
let fresh_id () = string_of_int (unique_id ()) ;;

let prime s = (* if is_bounded_var s then s else *) s ^ "_prime"
let unprime_id s = Str.replace_first (Str.regexp "_prime$") "" s

let mk_string s = "string__" ^ (smt_id s) ;;  (** a string could be the same as a variable id *)
(* let mk_string s = smt_id s ;; *)

let rec split_domain q ex bs1 bs2 = 
    match bs2 with
    | [] -> (bs1, ex)
    | (v, k, Ditto) :: bss -> split_domain q ex (bs1 @ [v, k, Ditto]) bss
    | _ -> 
        let (_, bs2) = app_bounds (shift (List.length bs1)) bs2 in
        (bs1, Quant (q, bs2, ex) @@ ex)
;;

let rec deconj e = 
    let pr ex = if is_conc e then assign ex isconc () else ex in
    match e.core with
    | Apply ({core = Internal B.Conj}, [e1 ; e2]) -> deconj (pr e1) @ deconj (pr e2)
    | List (_, [ex]) -> deconj (pr ex)
    | List ((And | Refs), ex::es) -> (deconj (pr ex)) @ deconj (List (And, es) @@ e)
    | _ -> [e]
;;

let rec dedisj e = 
    let pr ex = if is_conc e then assign ex isconc () else ex in
    match e.core with
    | Apply ({core = Internal B.Disj}, [e1 ; e2]) -> dedisj (pr e1) @ dedisj (pr e2)
    | List (_, [ex]) -> dedisj (pr ex)
    | List (Or, ex::es) -> (dedisj (pr ex)) @ dedisj (List (Or, es) @@ e)
    | _ -> [e]
;;

let rec deimpl e = 
    match e.core with
    | Apply ({core = Internal B.Implies}, [hyps ; conc]) -> 
        let (hs,c) = deimpl conc in
        (deconj (hyps) @ hs, c)
    | _ -> ([], e)
;;

let rec unroll_seq sq = match Deque.front sq.context with
  | None -> sq.active
  | Some (h, hs) ->
      let sq = { sq with context = hs } in
      begin match h.core with
        | Fresh (v, _, kn, ran) ->
        (* | Fresh (v, Shape_expr, kn, ran) -> *)
            let ran = match ran with
              | Bounded (ran, Visible) -> Domain ran
              | _ -> No_domain
            in
            Quant (Forall, [v, kn, ran], unroll_seq sq) @@ nowhere
        | Flex v ->
            let v_prime = (v.core ^ "'") @@ v in
            Quant (Forall, [ v, Constant, No_domain
                           ; v_prime, Constant, No_domain ],
                   unroll_seq (app_sequent (shift 1) sq)) @@ nowhere
        | Fact (e, Visible) ->
            List.fold_right begin
              fun e f ->
                noprops
                  (Apply begin
                     Internal B.Implies @@ nowhere,
                     [ e ; f ]
                   end)
            end (deconj e) (unroll_seq (app_sequent (shift (-1)) sq))
        | _ ->
            let opq = Opaque (hyp_name h) @@ nowhere in
            unroll_seq (app_sequent (scons opq (shift 0)) sq)
      end
;;

let map_exp_bs g cx bs = 
  List.map 
    begin function
    | (v, k, Domain d) -> (v, k, Domain (g cx d))
    | b -> b
    end 
  (unditto bs)
;;
let map_exp g cx e =
(* Util.eprintf "  map_exp: %a" (print_prop ()) (opaque cx e) ;     *)
  let mk x = { e with core = x } in
  let iter_es es = List.map (fun e -> g cx e) es in
  match e.core with
  | Quant (q, bs, ex) -> 
      let bs = map_exp_bs g cx bs in
      Quant (q, bs, g (add_bs_ctx bs cx) ex) |> mk
  | Apply (op, es) -> Apply (g cx op, iter_es es) |> mk
  | FcnApp (f, es) -> FcnApp (g cx f, iter_es es) |> mk
  | List (b, es) -> List (b, iter_es es) |> mk
  | Dot (r, h) -> Dot (g cx r, h) |> mk
  | Tuple es -> Tuple (iter_es es) |> mk
  | Record rs -> Record (List.map (fun (h,e) -> h, g cx e) rs) |> mk
  | SetOf (ex, bs) -> 
      let bs = map_exp_bs g cx bs in
      SetOf (g (add_bs_ctx bs cx) ex, bs) |> mk
  | SetSt (h, dom, ex) ->
      let dom = g cx dom in
      let cx = add_bs_ctx [h, Unknown, Domain dom] cx in
      SetSt (h, dom, g cx ex) |> mk
  | SetEnum es -> SetEnum (iter_es es) |> mk
  | Choose (h, d, ex) ->
      let (d,dom) = match d with 
      | Some d -> let d = g cx d in (Some d, Domain d)
      | None -> (None, No_domain) 
      in
      let cx = add_bs_ctx [h, Unknown, dom] cx in
      Choose (h, d, g cx ex) |> mk
  | Arrow (e1,e2) -> Arrow (g cx e1, g cx e2) |> mk
  | Expr.T.Fcn (bs, ex) -> 
      let bs = map_exp_bs g cx bs in
      Expr.T.Fcn (bs, g (add_bs_ctx bs cx) ex) |> mk
  | Except (f, exs) -> 
      let map_exp_ex = function Except_apply ea -> Except_apply (g cx ea) | Except_dot h -> Except_dot h in
      let exs = List.map (fun (es,ex) -> List.map map_exp_ex es, g cx ex) exs in
      Except (g cx f, exs) |> mk
  | Rect rs -> Rect (List.map (fun (h,e) -> h, g cx e) rs) |> mk
  | Product es -> Product (iter_es es) |> mk
  | If (c, t, f) -> If (g cx c, g cx t, g cx f) |> mk
  | Case (es, o) ->
      let es = List.map (fun (p,e) -> g cx p, g cx e) es in
      let o = match o with Some o -> Some (g cx o) | None -> None in
      Case (es, o) |> mk
  | Lambda (xs,ex) ->
      let add_to_ctx cx xs = 
        let rec new_ctx_vars = function
        | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
        | [] -> []
        in  
        List.rev (new_ctx_vars xs) @ cx
      in
      Lambda (xs, g (add_to_ctx cx xs) ex) |> mk
  | Sequent seq -> g cx (unroll_seq seq)
  | Parens (ex,_) -> g cx ex
  | _ -> e
;;

let rec opaque ?strong:(stg=false) cx e = 
(* Util.eprintf "opaque: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  match e.core with
  | Ix n -> 
      let id = lookup_id cx n in
      if (not stg) && (has_boundvar e) then e else 
        Opaque id |> mk
  | _ -> map_exp (opaque ~strong:stg) cx e
;;

(* let rec opaque ?strong:(stg=false) cx e = 
(* Util.eprintf "opaque: %a" (print_prop ()) e ; *)
    let mk x = { e with core = x } in
    let opq = opaque ~strong:stg cx in
    let opq_cx bs = opaque ~strong:stg (add_bs_ctx bs cx) in
    let opq_bs bs = List.map begin function (h, k, Domain dom) -> (h, k, Domain (opq dom)) | b -> b end bs in
    let opqs es = List.map opq es in
    let opq_ex = function Except_apply ea -> Except_apply (opq ea) | e -> e in
    let opq_exc exs = List.map (fun (eps,ex) -> List.map opq_ex eps, opq ex) exs in
    match e.core with
    | Ix n -> 
        let id = lookup_id cx n in
        if (not stg) && (has_boundvar e) then e else 
            Opaque id |> mk
    | String _ | Opaque _ | Internal _ | Num _ -> e
    | Apply (op, es)  -> Apply   (opq op, opqs es) |> mk
    | List (b, es)    -> List    (b, opqs es) |> mk
    | FcnApp (ex, es) -> FcnApp  (opq ex, opqs es) |> mk
    | Except (f, exs) -> Except  (opq f, opq_exc exs) |> mk
    | Arrow (e1,e2)   -> Arrow   (opq e1, opq e2) |> mk
    | Dot (ex, fd)    -> Dot     (opq ex, fd) |> mk
    | Record rs       -> Record  (List.map (fun (s,e) -> s, opq e) rs) |> mk
    | Rect rs         -> Rect    (List.map (fun (s,e) -> s, opq e) rs) |> mk
    | SetEnum es      -> SetEnum (opqs es) |> mk
    | Tuple es        -> Tuple   (opqs es) |> mk
    | Product es      -> Product (opqs es) |> mk
    | Quant (q, bs, ex)   -> let bs = opq_bs bs in Quant (q, bs, opq_cx bs ex) |> mk
    | Expr.T.Fcn (bs, ex) -> let bs = opq_bs bs in Expr.T.Fcn (bs, opq_cx bs ex) |> mk
    | SetOf (ex, bs)      -> let bs = opq_bs bs in SetOf (opq_cx bs ex, bs) |> mk
    | SetSt (h, dom, ex)  -> SetSt (h, opq dom, opq_cx [h, Unknown, Domain (opq dom)] ex) |> mk
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | (h,_) :: xs -> ((Flex h) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            List.rev (new_ctx_vars xs) @ cx
        in
        Lambda (xs, opaque ~strong:stg (add_to_ctx cx xs) ex) |> mk
    | If (c,t,f)     -> If (opq c, opq t, opq f) |> mk
    | Case (es, Some o) -> Case (List.map (fun (c,e) -> (opq c, opq e)) es, Some (opq o)) |> mk
    | Case (es, None)   -> Case (List.map (fun (c,e) -> (opq c, opq e)) es, None) |> mk
    | Sequent seq       -> opq (unroll_seq seq)
    | Parens (ex,_)     -> opq ex
    | Choose (h,None,ex) ->
        Choose (h, None, opaque ~strong:stg (add_bs_ctx [h,Unknown,No_domain] cx) ex) |> mk
    | Choose (h,Some dom,ex) ->
        let bs = opq_bs [h, Unknown, Domain dom] in
        Choose (h, Some (opq dom), opq_cx bs ex) |> mk
    | _ ->
        Util.eprintf ~at:e "function opaque cannot print@\n%a" (print_prop ()) e ;
        Opaque "[SMT opaque: expression not supported]" |> mk
;; *)

let fresh_bound_to_exp h dom = 
    let id = smt_id h.core in
    let dom = app_expr (shift 1) dom in
    let exp = noprops (Apply (noprops (Internal B.Mem), [Ix 1 @@ dom ; dom])) in
    let fact = Flex (id @@ h) @@ h in
    exp, fact
;;

let rec preprocess_context = function
    | hyp :: cx -> (hyp,cx) :: (preprocess_context cx)
    | [] -> []
;;

let rec proc_assumptions f = function
    | (hyp,cx) :: hs -> 
        begin match hyp.core with
        | Fact (e,Visible) -> 
            List.rev_map (fun ex -> f cx ex hs) (deconj e) @ proc_assumptions f hs
        | Fresh (h,_,_,Bounded (dom,Visible)) -> 
            let e, fact = fresh_bound_to_exp h dom in
            f (fact :: cx) e hs :: proc_assumptions f hs
        | _ -> 
            proc_assumptions f hs
        end
    | _ -> []
;;

let process_excep = function
    | Failure msg -> Util.eprintf "[TypeInfer] Failure: %s" msg
    (* | Untyped_symbol msg -> Util.eprintf "[TypeInfer Error] %s.\n" msg   *)
    (* | Unification_failed msg *)
    (* | Unsupported_type msg -> Util.eprintf "[TypeInfer Error] %s" msg   *)
    (* | Infer_other msg -> Util.eprintf "[TypeInfer] %s" msg *)
    (* | Unsupported_expression e -> Util.eprintf "[TypeInfer] Unsupported expression" *)
    | _ -> Util.eprintf "[TypeInfer] unknown exception.\n" ; assert false
;;

(************************************************************************)

let rec get_ops cx e : string list =
    let get_opss cx es = List.fold_left (fun r e -> get_ops cx e @ r) [] es in
    match e.core with
    | Ix n -> 
        begin match (List.nth cx (n - 1)).core with
        | Defn ({core = Operator (h,_)},_,_,_) -> [h.core]
        | _ -> []
        end
    | String _ | Opaque _ | Internal _ | Num _ -> 
        []
    | Apply (ex, es) | FcnApp (ex, es) -> 
        get_opss cx (ex :: es)
    | List (_, es) | Tuple es | Product es | SetEnum es -> 
        get_opss cx es
    | Quant (_, bs, ex) | Expr.T.Fcn (bs, ex) | SetOf (ex, bs) -> 
        get_ops (add_bs_ctx bs cx) ex @ get_ops_bs cx bs
    | SetSt (h, dom, ex) ->
        get_ops cx (Expr.T.Fcn ([h, Unknown, Domain dom], ex) @@ e)
    | Except (f, [([Except_apply e1],e2)]) -> 
        get_ops cx f @ get_ops cx e1 @ get_ops cx e2
    | Except (r, exs) ->
        let ops_exps = function Except_apply ea -> [get_ops cx ea] | _ -> [] in
        get_ops cx r @ List.flatten (List.map (fun (exps,ex) -> (List.flatten (List.flatten (List.map ops_exps exps))) @ (get_ops cx ex)) exs)
    | Arrow (e1,e2) -> 
        get_opss cx [e1 ; e2]
    | Dot (ex,_) | Parens (ex,_) -> 
        get_ops cx ex
    | Record rs | Rect rs -> 
        let es = List.map (fun (_,e) -> e) rs in
        get_opss cx es
    | If (c, t, f) -> 
        get_opss cx [c ; t ; f]
    | Case (es, None) ->
        let (es1,es2) = List.split es in
        get_opss cx (es1 @ es2)
    | Case (es, Some o) ->
        let (es1,es2) = List.split es in
        get_opss cx (es1 @ es2 @ [o])
    | Sequent seq ->
        get_ops cx (unroll_seq seq)
    | Choose (h, None, ex) -> 
        get_ops (add_bs_ctx [h, Unknown, No_domain] cx) ex
    | Choose (hint, Some dom, ex) -> 
        let bs = [hint, Unknown, Domain dom] in
        get_ops (add_bs_ctx bs cx) ex @ get_ops_bs cx bs
    | Lambda (vs, ex) -> 
        let vs = List.fold_right (fun (h,s) r -> match s with Shape_expr -> (h, Unknown, No_domain) :: r | Shape_op _ -> r) vs [] in
        get_ops (add_bs_ctx vs cx) ex
    | _ ->
        Util.eprintf ~at:e "function get_ops cannot print@\n%a" (print_prop ()) e ;
        (* [] *) assert false
and get_ops_bs cx bs = 
    let f cx = function
    | (_, _, Domain dom) -> get_ops cx dom
    | _ -> []
    in
    List.fold_left (fun r b -> f cx b @ r) [] bs
;;

let get_operators cx e = 
    get_ops cx e @ List.flatten (proc_assumptions (fun cx e _ -> get_ops cx e) (preprocess_context cx))
;;

(* let rec arity e = match e.core with
    | Ix _ | Opaque _ -> 0
    | Apply ({core = Ix _ | Opaque _}, args) -> List.length args
    | Apply ({core = Internal B.Prime}, [ex]) -> arity ex
    | _ -> -1
;; *)

(****************************************************************************)

let field_ids = ref SSet.empty ;;       (** Set of fields ids not collected with add_record_id *)
let add_field s = field_ids := SSet.add (add_field_prefix s) !field_ids ;;

let record_ids = ref SSMap.empty ;;
let get_recid fs = 
    (* let fs = List.map add_field_prefix fs in *)
    try SSMap.find fs !record_ids 
    with Not_found -> 
        let id = unique_id () in
        List.iter add_field fs ;
        record_ids := SSMap.add fs id !record_ids ;
        id
;;
let add_record_id fs =          (** Two records have the same type iff they have the same fields (ignoring the fields position) *)
    (* let fs = List.map add_field_prefix fs in *)
    let id = get_recid fs in
    record_ids := SSMap.add fs id !record_ids ;
    id 
;;

let tla_op_set = ref SSet.empty ;;      (** Set of operators that appear in the obligation *)
let add_tla_op op = tla_op_set := SSet.add op !tla_op_set ;;

let chooses = ref SMap.empty ;;
let add_choose s cx e = 
    match e.core with
    | Choose _ -> 
        ignore begin 
        try List.find (fun (_,(cx',e')) -> 
            Expr.Eq.expr (opaque cx e) (opaque cx' e')) (SMap.bindings !chooses)
        with Not_found ->
            chooses := SMap.add s (cx,e) !chooses ; 
            (s,(cx,e))
        end
    | _ -> ()
;;

let nonbasic_ops = ref SMap.empty ;;

(****************************************************************************)

let simplefacts = ref [] ;;

let rec is_simplefact e = 
    match e.core with
    | Quant _ 
    | Sequent _ -> false
    | _ -> true
;;

(** FIX: toplevel facts "P <=> TRUE" should be added as the simplefact "P". *)
let add_simplefact cx e = 
(* Util.eprintf "  add_simplefact: %a" (print_prop ()) (opaque cx e) ;     *)
    let es = deconj e
      |> List.filter is_simplefact
      |> List.map (fun e -> (cx,e)) 
    in
    simplefacts := es @ !simplefacts ;;

let simp_simplefacts cx e =
  let mem_sf cx e = List.fold_left 
    begin fun r (cxf,f) -> 
      (* (Expr.Eq.expr (opaque ~strong:true cx e) (opaque ~strong:true cxf f)) || r)  *)
      let d = List.length cx - List.length cxf in
      let f = if d > 0 then app_expr (shift d) f else f in
(* Util.eprintf "f: %a : %s" (print_prop ()) (opaque cx f) (typ_to_str e) ; *)
      (Expr.Eq.expr e f || r) 
    end
    false !simplefacts
  in
  e 
  |> deconj
  |> List.filter (fun e -> not (List.exists (mem_sf cx) (dedisj e)))
  (* |> fun es -> (List.iter (fun e -> Util.eprintf "  --- %a" (print_prop ()) (opaque cx e))) es ; es *)
  |> List.fold_left (fun r e -> 
      let tla_false = Internal B.FALSE @@ e in
      let neg e = Apply (Internal B.Neg @@ e, [e]) @@ e in
      match e.core with
      | Apply ({core = Internal B.Neg},[ex]) -> 
          if mem_sf cx ex then [tla_false] else r @ [e]
      | _ -> 
          if mem_sf cx (neg e) then [tla_false] else r @ [e]
      ) []
  (* |> fun es -> (List.iter (fun e -> Util.eprintf "  ''' %a" (print_prop ()) (opaque cx e))) es ; es *)
  |> fun es -> 
      match es with
      | [] -> Internal B.TRUE @@ e
      | [ex] -> if is_conc e then assign ex isconc () else ex
      | _ -> List (And, es) @@ e
;;

let remove_simplefact es =
    let rec faux xs n = match xs, n with
    | xs, 0 -> xs
    | x :: xs, n -> faux xs (n-1)
    | _ -> []
    in
    (* Printf.eprintf "====== after remove ======\n" ;
    List.iter (fun (cx,e) -> Util.eprintf "fact: %a" (print_prop ()) (opaque cx e)) !simplefacts ;
    Printf.eprintf "----------------\n" ; *)
    let es = es 
      |> List.map deconj 
      |> List.flatten 
      |> List.filter is_simplefact
    in
    let n = List.length es in
    simplefacts := faux !simplefacts n
    ;;

let rec perms xs = 
    match xs with
    | [] -> []
    | x :: xs ->
        let perm2 x ys = match ys with
        | [] -> []
        | ys -> List.map (fun y -> x,y) ys
        in
        (perm2 x xs) @ (perms xs)
;;

(** term ::= <Id/Opaque symbol> | String | Num | term(term,..,term) | Prime (term) | FcnApp (term, _) | Dot(term, _) *)
let rec is_term e =
    match e.core with
    | Ix _ | Opaque _ | String _ | Num _ -> true
    | Apply ({core = Internal B.Prime}, [ex]) -> is_term ex
    | Apply (ex, es) -> List.for_all is_term (ex :: es)
    | FcnApp (ex, _) -> is_term ex
    | Dot (ex, _) -> is_term ex
    | Internal B.Len
    | Internal B.Seq
    | Internal B.Append
    | Internal B.Tail
    | Internal B.Cat -> true
    | Tuple [] | SetEnum [] -> true
    | Internal B.Nat | Internal B.Int -> true
    | _ -> false    

(** domain ::= DOMAIN (term) *)
let rec is_domain e =
    match e.core with
    | Apply ({core = Internal B.DOMAIN}, [ex]) -> is_term ex
    | _ -> false    

let tuple_id ts = match ts with 
  | [] -> "tuple0" 
  (* | _ -> sprintf "tuple_%s" (String.concat "" (List.map (function Int -> "i" | _ -> "u") ts)) ;; *)
  | _ -> sprintf "tuple_%s" (String.concat "" (List.map (function _ -> "u") ts)) ;;

let tuples = ref [] ;;
let add_tuple ts = 
    add_tla_op (tuple_id ts) ;
    if not (List.mem ts !tuples) then tuples := ts :: !tuples ;;

(****************************************************************************)

let rec unprime cx e =
  let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
  let opq id = function [] -> Opaque id |> mc | es -> Apply (noprops (Opaque id), es) |> mc in
  let us es = List.map (unprime cx) es in
  match e.core with
  | Apply ({core = Internal B.Prime}, [ex]) -> 
      begin match ex.core with
      | Apply ({core = Ix n}, es)      -> opq (prime (lookup_id cx n)) (us es)
      | Apply ({core = Opaque id}, es) -> opq (prime id) (us es)
      | Ix n                           -> opq (prime (lookup_id cx n)) []
      | Opaque id                      -> opq (prime id) []
      | _                              -> Util.bug "src/smt/smtcommons.ml: unprime expression."
      end
  | _ -> map_exp unprime cx e
;;

let newvars = ref SMap.empty ;;
let mk_newvar_id cx e =
  try let id,_ = List.find (fun (_,(cx',e')) -> 
        Expr.Eq.expr (opaque cx e) (opaque cx' e')) (SMap.bindings !newvars)
      in id
  with Not_found -> 
    let id = fresh_id () in
    newvars := SMap.add id (cx,e) !newvars ; 
    id
;;
let unspec cx e = Opaque ("newvar__" ^ (mk_newvar_id cx e)) @@ e ;;

let rec insert_intdiv_cond cx e =
(* Util.eprintf "  insert_intdiv_cond: %a" (print_prop ()) (opaque cx e) ;     *)
  let app op x y = Apply (noprops (Internal op), [x ; y]) @@ e in
  match e.core with
  | Apply ({core = Internal (B.Quotient | B.Remainder)} as op, [x ; y]) ->
      let x = insert_intdiv_cond cx x in
      let y = insert_intdiv_cond cx y in
      let e = Apply (op, [x ; y]) @@ e in
      If (app B.Conj (app B.Mem y (noprops (Internal B.Int))) 
                     (app B.Lt (noprops (Num ("0",""))) y), e, unspec cx e) @@ e
  | _ -> map_exp insert_intdiv_cond cx e
;;

(* let rec unprime cx e =
    let mk x = { e with core = x } in
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    let opq id = function [] -> Opaque id |> mc | es -> Apply (noprops (Opaque id), es) |> mc in
    let us es = List.map (unprime cx) es in
    match e.core with
    | Apply ({core = Internal B.Prime}, [ex]) -> 
        begin match ex.core with
        | Apply ({core = Ix n}, es)      -> opq (prime (lookup_id cx n)) (us es)
        | Apply ({core = Opaque id}, es) -> opq (prime id) (us es)
        | Ix n                           -> opq (prime (lookup_id cx n)) []
        | Opaque id                      -> opq (prime id) []
        | _                              -> Util.bug "src/smt/smtcommons.ml: unprime expression."
        end
    | Quant (q, bs, ex) -> Quant (q, unprime_bs cx bs, unprime (add_bs_ctx bs cx) ex) |> mk
    | Apply (op, es) -> Apply (unprime cx op, us es) |> mk
    | FcnApp (f, es) -> FcnApp (unprime cx f, us es) |> mk
    | List (b, es) -> List (b, us es) |> mk
    | Dot (r, h) -> Dot (unprime cx r, h) |> mk
    | Tuple es -> Tuple (us es) |> mk
    | Record rs -> Record (List.map (fun (h,e) -> h, unprime cx e) rs) |> mk
    | SetOf (ex, bs) -> SetOf (unprime (add_bs_ctx bs cx) ex, unprime_bs cx bs) |> mk
    | SetSt (h, dom, ex) ->
        let dom = unprime cx dom in
        SetSt (h, dom, unprime (add_bs_ctx [h, Unknown, Domain dom] cx) ex) |> mk
    | SetEnum es -> SetEnum (us es) |> mk
    | Choose (h, d, ex) ->
        let (d,dom) = match d with 
        | Some d -> let d = unprime cx d in (Some d, Domain d)
        | None -> (None, No_domain) 
        in
        Choose (h, d, unprime (add_bs_ctx [h, Unknown, dom] cx) ex) |> mk
    | Arrow (e1,e2) -> Arrow (unprime cx e1, unprime cx e2) |> mk
    | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (unprime_bs cx bs, unprime (add_bs_ctx bs cx) ex) |> mk
    | Except (f, exs) -> 
        let unprime_ex = function Except_apply ea -> Except_apply (unprime cx ea) | Except_dot h -> Except_dot h in
        let exs = List.map (fun (es,ex) -> List.map unprime_ex es, unprime cx ex) exs in
        Except (unprime cx f, exs) |> mk
    | Rect rs -> Rect (List.map (fun (h,e) -> h,unprime cx e) rs) |> mk
    | Product es -> Product (us es) |> mk
    | If (c, t, f) -> If (unprime cx c, unprime cx t, unprime cx f) |> mk
    | Case (es, o) ->
        let es = List.map (fun (p,e) -> unprime cx p, unprime cx e) es in
        let o = match o with Some o -> Some (unprime cx o) | None -> None in
        Case (es, o) |> mk
    | Sequent seq -> unprime cx (unroll_seq seq)
    | Parens (ex,_) -> unprime cx ex
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            List.rev (new_ctx_vars xs) @ cx
        in
        unprime (add_to_ctx cx xs) ex
    | _ -> e
and unprime_bs cx bs = 
    let f = function
    | (v, k, Domain d) -> (v, k, Domain (unprime cx d))
    | b -> b
    in
    List.map f (unditto bs)
;; *)


let allids cx = 
    List.fold_left begin fun r h -> 
      match h.core with
      | Fresh (nm, _, _, _)
      | Flex nm
      | Defn ({core = Operator (nm, _) | Instance (nm, _)
                      | Bpragma(nm,_,_) | Recursive (nm, _)},
              _, _, _)
        -> SSet.add nm.core r
      | Fact (_, _) -> r
    end SSet.empty cx
;;

let rec free_vars cx e : string list =
    let free_varss cx es = List.fold_left (fun r e -> free_vars cx e @ r) [] es in
    match e.core with
    | Ix n -> 
        (* if 0 < n && n <= (List.length cx) then [] else [lookup_id cx n] *)
        if is_bvar cx n then [lookup_id cx n] else []
    | String _ | Opaque _ | Internal _ | Num _ -> 
        []
    | Apply (ex, es) | FcnApp (ex, es) -> 
        free_varss cx (ex :: es)
    | List (_, es) | Tuple es | Product es | SetEnum es -> 
        free_varss cx es
    | Quant (_, bs, ex) | Expr.T.Fcn (bs, ex) | SetOf (ex, bs) -> 
        free_vars (add_bs_ctx bs cx) ex @ free_vars_bs cx bs
    | SetSt (h, dom, ex) ->
        free_vars cx (Expr.T.Fcn ([h, Unknown, Domain dom], ex) @@ e)
    | Except (f, [([Except_apply e1],e2)]) -> 
        free_vars cx f @ free_vars cx e1 @ free_vars cx e2
    | Except (r, exs) ->
        let ops_exps = function Except_apply ea -> [free_vars cx ea] | _ -> [] in
        free_vars cx r @ List.flatten (List.map (fun (exps,ex) -> (List.flatten (List.flatten (List.map ops_exps exps))) @ (free_vars cx ex)) exs)
    | Arrow (e1,e2) -> 
        free_varss cx [e1 ; e2]
    | Dot (ex,_) | Parens (ex,_) -> 
        free_vars cx ex
    | Record rs | Rect rs -> 
        let es = List.map (fun (_,e) -> e) rs in
        free_varss cx es
    | If (c, t, f) -> 
        free_varss cx [c ; t ; f]
    | Case (es, None) ->
        let (es1,es2) = List.split es in
        free_varss cx (es1 @ es2)
    | Case (es, Some o) ->
        let (es1,es2) = List.split es in
        free_varss cx (es1 @ es2 @ [o])
    | Sequent seq ->
        free_vars cx (unroll_seq seq)
    | Choose (h, None, ex) -> 
        free_vars (add_bs_ctx [h, Unknown, No_domain] cx) ex
    | Choose (hint, Some dom, ex) -> 
        let bs = [hint, Unknown, Domain dom] in
        free_vars (add_bs_ctx bs cx) ex @ free_vars_bs cx bs
    | Lambda (vs, ex) -> 
        let vs = List.fold_right (fun (h,s) r -> match s with Shape_expr -> (h, Unknown, No_domain) :: r | Shape_op _ -> r) vs [] in
        free_vars (add_bs_ctx vs cx) ex
    | _ ->
        Util.eprintf ~at:e "function free_vars cannot print@\n%a" (print_prop ()) e ;
        (* [] *) assert false
and free_vars_bs cx bs = 
    let f cx = function
    | (_, _, Domain dom) -> free_vars cx dom
    | _ -> []
    in
    List.fold_left (fun r b -> f cx b @ r) [] bs
;;

(** rename repeated ids for bounded variables. *)
let rec renameb cx e =
(* Util.eprintf "renameb %a" (print_prop ()) e ; *)
    let mk x = { e with core = x } in
    let ren v = if SSet.mem v.core (allids cx) then (v.core^"_1") @@ v else v in
    match e.core with
    | Quant (q, bs, ex) -> 
        let bs = List.map (fun (v,k,d) -> ren v,k,d) bs in
        Quant (q, map_exp_bs renameb cx bs, renameb (add_bs_ctx bs cx) ex) |> mk
    | _ -> map_exp renameb cx e
;;

(* (** rename repeated ids for bounded variables. *)
let rec renameb cx e =
(* Util.eprintf "renameb %a" (print_prop ()) e ; *)
    let mk x = { e with core = x } in
    let us es = List.map (renameb cx) es in
    let ren v = if SSet.mem v.core (allids cx) then (v.core^"_1") @@ v else v in
    match e.core with
    | Quant (q, bs, ex) -> 
        let bs = List.map (fun (v,k,d) -> ren v,k,d) bs in
        Quant (q, renameb_bs cx bs, renameb (add_bs_ctx bs cx) ex) |> mk
    | Apply (op, es) -> Apply (renameb cx op, us es) |> mk
    | FcnApp (f, es) -> FcnApp (renameb cx f, us es) |> mk
    | List (b, es) -> List (b, us es) |> mk
    | Dot (r, h) -> Dot (renameb cx r, h) |> mk
    | Tuple es -> Tuple (us es) |> mk
    | Record rs -> Record (List.map (fun (h,e) -> h, renameb cx e) rs) |> mk
    | SetOf (ex, bs) -> SetOf (renameb (add_bs_ctx bs cx) ex, renameb_bs cx bs) |> mk
    | SetSt (h, dom, ex) ->
        let dom = renameb cx dom in
        SetSt (h, dom, renameb (add_bs_ctx [h, Unknown, Domain dom] cx) ex) |> mk
    | SetEnum es -> SetEnum (us es) |> mk
    | Choose (h, d, ex) ->
        let (d,dom) = match d with 
        | Some d -> let d = renameb cx d in (Some d, Domain d)
        | None -> (None, No_domain) 
        in
        Choose (h, d, renameb (add_bs_ctx [h, Unknown, dom] cx) ex) |> mk
    | Arrow (e1,e2) -> Arrow (renameb cx e1, renameb cx e2) |> mk
    | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (renameb_bs cx bs, renameb (add_bs_ctx bs cx) ex) |> mk
    | Except (f, exs) -> 
        let renameb_ex = function Except_apply ea -> Except_apply (renameb cx ea) | Except_dot h -> Except_dot h in
        let exs = List.map (fun (es,ex) -> List.map renameb_ex es, renameb cx ex) exs in
        Except (renameb cx f, exs) |> mk
    | Rect rs -> Rect (List.map (fun (h,e) -> h,renameb cx e) rs) |> mk
    | Product es -> Product (us es) |> mk
    | If (c, t, f) -> If (renameb cx c, renameb cx t, renameb cx f) |> mk
    | Case (es, o) ->
        let es = List.map (fun (p,e) -> renameb cx p, renameb cx e) es in
        let o = match o with Some o -> Some (renameb cx o) | None -> None in
        Case (es, o) |> mk
    | Sequent seq -> renameb cx (unroll_seq seq)
    | Parens (ex,_) -> renameb cx ex
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            List.rev (new_ctx_vars xs) @ cx
        in
        renameb (add_to_ctx cx xs) ex
    | _ -> e
and renameb_bs cx bs = 
    let f = function
    | (v, k, Domain d) -> (v, k, Domain (renameb cx d))
    | b -> b
    in
    List.map f (unditto bs)
;; *)
