(*
 * backend/smt/smtcommons.ml --- SMT backend commons
 *
 * Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 34678 $";;

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

(* open Typesystem *)

module B = Builtin;;

module SSet = Set.Make (String)
module SMap = Map.Make (String)

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

(****************************************************************************)

(** Combinators *)
let ( |> ) x f = f x ;;
let ( |>> ) (x, y) f = (f x, y) ;;
let ( ||> ) (x, y) f = (x, f y) ;;
let kk x y = ignore x ; y ;;
let tap f = fun x -> (f x; x) ;;
let pairself f (x, y) = (f x, f y) ;;

(****************************************************************************)

type provermode = Smtlib | CVC3 | Z3 | Yices | Spass | Fof ;;
let mode = ref Smtlib ;;

let filter_true es  = filter (fun e -> match e.core with Internal B.TRUE  -> false | _ -> true) es ;;
let filter_false es = filter (fun e -> match e.core with Internal B.FALSE -> false | _ -> true) es ;;

let boundvar : unit pfuncs = Property.make "Backend.Smt.boundvar"
let has_boundvar x = Property.has x boundvar ;;
let is_bvar cx n =
    assert (n > 0 && n <= length cx) ;
    has_boundvar (nth cx (n - 1))
;;

(*
  The functionality of [smt_id] is now included in [Tla_parser.pickle].
  Any keywords that clash with identifiers must be added to the [other_keys]
  list in Tla_parser.ml.
*)
let smt_id id = Tla_parser.pickle id;;

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
(* Printf.eprintf "[lookup_id %d <= %d]" n (length cx) ; *)
    assert (n > 0 && n <= length cx) ;
    let id = hyp_name (nth cx (n - 1)) in
    fof_id_vars (is_bvar cx n) id
;;

(* let bound_prefix = "x__" ;; *)
(* let is_bounded_var id =
    try ((String.sub id 0 (String.length bound_prefix)) = bound_prefix) with Invalid_argument _ -> false ;; *)

let check_prefix s pre =
  String.length s >= String.length pre
  && String.sub s 0 (String.length pre) = pre
;;

let nonbasic_prefix = "a__" ;;
let is_nonbasic_var id = check_prefix id nonbasic_prefix;;

let field_prefix = "f__" ;;
let is_field id = check_prefix id field_prefix;;

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
  let hyps = mapi begin
    fun n (v, k, dom) ->
      (* let v = assign v boundvar () in *)
      match dom with
      | No_domain -> Fresh (v, Shape_expr, k, Unbounded) @@ v
      | Domain d -> Fresh (v, Shape_expr, k, Bounded (app_expr (shift n) d, Visible)) @@ v
      | _ -> assert false
  end bs in
  rev hyps @ cx
;;

let rec n_to_list = function
  | 0 -> []
  | n -> (n_to_list (n-1)) @ [n]
;;

(* let concat1 fmt ls = String.concat " " (map (sprintf fmt) ls) ;; *)
(* let concat2 fmt ls = String.concat "," (map (sprintf fmt) ls) ;; *)

(** Fast, but it does not preserve the order *)
let remove_repeated lst =
  let unique_set = Hashtbl.create (length lst) in
  iter (fun x -> Hashtbl.replace unique_set x ()) lst;
  Hashtbl.fold (fun x () xs -> x :: xs) unique_set [] ;;

let remove_repeated_ex es =
  let e_mem e es = exists (Expr.Eq.expr e) es in
  fold_left (fun r e -> if e_mem e r then r else e :: r) [] es

let ctr = ref 0 ;;

let unique_id () = incr ctr ; !ctr ;;

let fresh_name () = "v" ^ string_of_int (unique_id ()) ;;
let fresh_id () = string_of_int (unique_id ()) ;;

let prime s = (* if is_bounded_var s then s else *) s ^ "#prime"
let unprime_id s = Str.replace_first (Str.regexp "#prime$") "" s

(** a string could be the same as a variable id *)
let mk_string s = "str_" ^ (smt_id s) ;;

let rec split_domain q ex bs1 bs2 =
    match bs2 with
    | [] -> (bs1, ex)
    | (v, k, Ditto) :: bss -> split_domain q ex (bs1 @ [v, k, Ditto]) bss
    | _ ->
        let (_, bs2) = app_bounds (shift (length bs1)) bs2 in
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
                          (* FIXME question: why not [prime v.core] ?? *)
            Quant (Forall, [ v, Constant, No_domain
                           ; v_prime, Constant, No_domain ],
                   unroll_seq (app_sequent (shift 1) sq)) @@ nowhere
        | Fact (e, Visible, _) ->
            fold_right begin
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

(****************************************************************************)

let map_exp g cx e =
(* Util.eprintf "  map_exp: %a" (print_prop ()) (opaque cx e) ;     *)
  let mk x = { e with core = x } in
  let map_exp_bs g cx bs =
    List.map
      begin function
      | (v, k, Domain d) -> (v, k, Domain (g cx d))
      | b -> b
      end
    (unditto bs)
  in
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

let e_map (ff:'a -> 'a -> 'a) (base:'a) (g:hyp list -> expr -> 'a) (cx:hyp list) (e:expr) : 'a =
(* Util.eprintf "  e_map: %a" (print_prop ()) e ; *)
  let ( $$ ) x y = ff x y in
  let flatten xs = List.fold_left (fun r e -> e $$ r) base xs in
  let map_es es = List.fold_left (fun r e -> g cx e $$ r) base es in
  let map_bs g cx bs =
    List.fold_left
      begin fun r -> function
      | (_, _, Domain d) -> d :: r
      | b -> r
      end []
    (unditto bs)
    |> map_es
  in
  match e.core with
  | Quant (q, bs, ex) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | Apply (op, es) -> map_es (op::es)
  | FcnApp (f, es) -> map_es (f::es)
  | List (b, es) -> map_es es
  | Dot (r, h) -> g cx r
  | Tuple es -> map_es es
  | Record rs -> map_es (List.map (fun (_,e) -> e) rs)
  | SetOf (ex, bs) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | SetSt (h, dom, ex) ->
      g cx dom $$ g (add_bs_ctx [h, Unknown, Domain dom] cx) ex
  | SetEnum es -> map_es es
  | Choose (h, d, ex) ->
      let (d,dom) = match d with
      | Some d -> (g cx d, Domain d)
      | None -> (base, No_domain)
      in
      d $$ g (add_bs_ctx [h, Unknown, dom] cx) ex
  | Arrow (e1,e2) -> g cx e1 $$ g cx e2
  | Expr.T.Fcn (bs, ex) ->
      map_bs g cx bs $$ g (add_bs_ctx bs cx) ex
  | Except (f, exs) ->
      let e_map_exc = function Except_apply ea -> g cx ea | Except_dot h -> base in
      g cx f $$ (flatten (List.map (fun (es,ex) -> flatten (List.map e_map_exc es) $$ g cx ex) exs))
  | Rect rs -> map_es (List.map (fun (_,e) -> e) rs)
  | Product es -> map_es es
  | If (c, t, f) -> map_es [c ; t ; f]
  | Case (es, o) ->
      (List.fold_left (fun r (p,e) -> g cx p $$ g cx e $$ r) base es)
      $$ (match o with Some o -> g cx o | None -> base)
  | Sequent seq -> g cx (unroll_seq seq)
  | Parens (ex,_) -> g cx ex
  | Lambda (xs,ex) ->
      let rec hs_to_ctx = function
      | ({core = h} as v,_) :: xs -> ((Flex (h @@ v)) @@ v) :: hs_to_ctx xs
      | [] -> []
      in
      g (List.rev (hs_to_ctx xs) @ cx) ex
  | _ -> base
;;

let map_list = e_map List.append [] ;;
let map_exists = e_map (||) false ;;
let map_forall = e_map (&&) true ;;

(****************************************************************************)

(** Do the n first variables appear in e ? *)
let rec free_n_vars n cx e : bool =
(* Util.eprintf "free_n_vars %d <= %a" n (print_prop ()) e ; *)
  match e.core with
  | Ix m -> m <= n
  | _ -> map_exists (free_n_vars n) cx e
;;

let rec opaque ?strong:(stg=false) ?min:(k=0) cx e =
(* Util.eprintf "opaque: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  match e.core with
  | Ix n when k < n ->
      if (not (n > 0 && n <= length cx))
      then  Opaque (sprintf "___%d___" n) |> mk
      else
      let id = lookup_id cx n in
      if (not stg) && (has_boundvar e) then e else
        Opaque id |> mk
  | Ix _ -> e
  | _ -> map_exp (opaque ~strong:stg) cx e
;;


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
      | Fact (e,Visible, _) ->
          rev_map (fun ex -> f cx ex hs) (deconj e) @ proc_assumptions f hs
      | Fresh (h,_,_,Bounded (dom,Visible)) ->
          let e, fact = fresh_bound_to_exp h dom in
          f (fact :: cx) e hs :: proc_assumptions f hs
      | _ ->
          proc_assumptions f hs
      end
  | _ -> []
;;

(* dead code eliminated by Damien
let process_excep = function
  | Failure msg -> Util.eprintf "[TypeInfer] Failure: %s" msg
  (* | Untyped_symbol msg -> Util.eprintf "[TypeInfer Error] %s.\n" msg   *)
  (* | Unification_failed msg *)
  (* | Unsupported_type msg -> Util.eprintf "[TypeInfer Error] %s" msg   *)
  (* | Infer_other msg -> Util.eprintf "[TypeInfer] %s" msg *)
  (* | Unsupported_expression e -> Util.eprintf "[TypeInfer] Unsupported expression" *)
  | _ -> Util.eprintf "[TypeInfer] unknown exception.\n" ; assert false
;;
*)

(****************************************************************************)
(** Printing of errors, warning and debugging *)

(** Level 0 = only errors, 1 = statistics, 2 = basic debug, 3 = full debug, ... *)
let verbosity = ref 1

let ifprint n =
  if n <= !verbosity then begin
    Format.print_flush () ;
    Format.kfprintf (fun ppf -> Format.fprintf ppf "\n%!") Format.err_formatter
  end else
    Format.ifprintf Format.err_formatter

let print_prop () = Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot) ;;
(* let pp_ex e = (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) e ;; *)

let pps_ex (cx,e) = Util.sprintf ?nonl:(Some ()) "@[%a@]" (print_prop ()) (opaque cx e)

(****************************************************************************)

let rec get_ops cx e : string list =
  (* let get_opss cx es = List.fold_left (fun r e -> get_ops cx e @ r) [] es in *)
  match e.core with
  | Ix n ->
      begin match (List.nth cx (n - 1)).core with
      | Defn ({core = Operator (h,_)},_,_,_) -> [h.core]
      | _ -> []
      end
  | _ -> map_list get_ops cx e
;;

let get_operators cx e =
    get_ops cx e @ List.flatten (proc_assumptions (fun cx e _ -> get_ops cx e) (preprocess_context cx))
;;

(* let rec arity e = match e.core with
    | Ix _ | Opaque _ -> 0
    | Apply ({core = Ix _ | Opaque _}, args) -> length args
    | Apply ({core = Internal B.Prime}, [ex]) -> arity ex
    | _ -> -1
;; *)

(****************************************************************************)

let field_ids = ref SSet.empty ;;       (** Set of fields ids not collected with add_record_id *)
let add_field s = field_ids := SSet.add (add_field_prefix s) !field_ids ;;

let record_ids = ref SSMap.empty ;;
let get_recid fs =
    (* let fs = map add_field_prefix fs in *)
    try SSMap.find fs !record_ids
    with Not_found ->
        let id = unique_id () in
        iter add_field fs ;
        record_ids := SSMap.add fs id !record_ids ;
        id
;;
let add_record_id fs =          (** Two records have the same type iff they have the same fields (ignoring the fields position) *)
    (* let fs = map add_field_prefix fs in *)
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
        try find (fun (_,(cx',e')) ->
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
  (* true *)
    match e.core with
    (* | Quant _  *)
    | If _
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
    simplefacts := es @ !simplefacts
;;

let simp_simplefacts cx e =
  let mem_sf cx e = List.fold_left
    begin fun r (cxf,f) ->
      let d = List.length cx - List.length cxf in
      let f = if d > 0 then app_expr (shift d) f else f in
(* Util.eprintf "f: %a : %s" (print_prop ()) (opaque cx f) (typ_to_str e) ; *)
      (Expr.Eq.expr e f || r)
    end
    false !simplefacts
  in
(* Printf.eprintf "-------------------\n" ; (List.iter (fun (cx,e) -> Util.eprintf "  --- %a" (print_prop ()) (opaque cx e))) !simplefacts ; *)
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
    let perm2 x ys =
      match ys with
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
    | Apply (ex, es) -> for_all is_term (ex :: es)
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

(* let tuple_id ts = match ts with
  | [] -> "tuple0"
  (* | _ -> sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) ;; *)
  | _ -> sprintf "tuple_%s" (String.concat "" (map (function _ -> "u") ts)) ;;

let tuples = ref [] ;;
let add_tuple ts =
    add_tla_op (tuple_id ts) ;
    if not (mem ts !tuples) then tuples := ts :: !tuples ;; *)

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
  try let id,_ = find (fun (_,(cx',e')) ->
        Expr.Eq.expr (opaque cx e) (opaque cx' e')) (SMap.bindings !newvars)
      in id
  with Not_found ->
    let id = fresh_id () in
    newvars := SMap.add id (cx,e) !newvars ;
    id
;;
let unspec cx e = Opaque ("newvar__" ^ (mk_newvar_id cx e)) @@ e ;;
(* let unspec cx e = Opaque ("newvar__" ^ (mk_newvar_id cx e)) |> noprops ;; *)

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

let allids cx =
    fold_left begin fun r h ->
      match h.core with
      | Fresh (nm, _, _, _)
      | Flex nm
      | Defn ({core = Operator (nm, _) | Instance (nm, _)
                      | Bpragma(nm,_,_) | Recursive (nm, _)},
              _, _, _)
        -> SSet.add nm.core r
      | Fact (_, _, _) -> r
    end SSet.empty cx
;;

let subtract xs x = fold_left (fun r a -> if x = a then r else r @ [a]) [] xs;;
let list_minus xs ys = fold_left subtract xs ys ;;

let rec free_vars cx e : string list =
(* Util.eprintf "free_vars %a" (print_prop ()) (opaque cx e) ; *)
  let free bs ex =
    let doms = fold_left (fun r (_,_,d) -> match d with Domain d -> d :: r | _ -> r) [] bs in
    let vs = map (fun (v,_,_) -> v.core) bs in
    flatten (map (free_vars cx) doms) @
    list_minus (free_vars (add_bs_ctx bs cx) ex) vs
  in
  match e.core with
  | Ix n -> [lookup_id cx n]
      (* if is_bvar cx n then [lookup_id cx n] else [] *)
  | Opaque s -> [s]
  | Quant (_,bs,ex)
  | Expr.T.Fcn (bs, ex)
  | SetOf (ex, bs) ->
      free bs ex
  | SetSt (h, dom, ex) ->
      free [h, Unknown, Domain dom] ex
  | Choose (h, d, ex) ->
      let dom = match d with
      | Some d -> Domain d
      | None -> No_domain
      in
      free [h, Unknown, dom] ex
  | _ -> map_list free_vars cx e
;;

(** rename repeated ids for bounded variables. *)
let rec renameb cx e =
(* Util.eprintf "renameb %a" (print_prop ()) e ; *)
    (* let mk x = { e with core = x } in *)
    let ren v = if SSet.mem v.core (allids cx) then (v.core^"_1") @@ v else v in
    match e.core with
    | Quant (q, bs, ex) ->
        let bs = List.map (fun (v,k,d) -> ren v,k,d) bs in
        (* Quant (q, (* map_exp_bs renameb cx *) bs, renameb (add_bs_ctx bs cx) ex) @@ e *)
        map_exp renameb cx (Quant (q, bs, ex) @@ e)
    | _ -> map_exp renameb cx e
;;


let flatten_conj e =
    let rec collect e = match e.core with
    | Apply ({core = Internal B.Conj}, [e1 ; e2]) ->
        collect e1 @ collect e2
    | List (And, es) ->
        flatten (map collect es)
    | _ -> [e]
    in
    begin match filter_true (collect e) with
    | [] -> Internal B.TRUE @@ e
    | ex :: [] -> if is_conc e then assign ex isconc () else ex
    | es -> if exists (fun e ->
                match e.core with Internal B.FALSE -> true | _ -> false) es
                then Internal B.FALSE @@ e else (List (And, es) @@ e)
    end
;;

let flatten_disj e =
    let rec collect e = match e.core with
    | Apply ({core = Internal B.Disj}, [e1 ; e2]) ->
        collect e1 @ collect e2
    | List (Or, es) ->
        flatten (map collect es)
    | _ -> [e]
    in
    begin match filter_false (collect e) with
    | [] -> Internal B.FALSE @@ e
    | [ex] -> if is_conc e then assign ex isconc () else ex
    | es -> if exists (fun e ->
                match e.core with Internal B.TRUE -> true | _ -> false) es
                then Internal B.TRUE @@ e else (List (Or, es) @@ e)
    end
;;

let reset () =
  ctr := 0;
  field_ids := SSet.empty;
  record_ids := SSMap.empty;
  tla_op_set := SSet.empty;
  chooses := SMap.empty;
  nonbasic_ops := SMap.empty;
  simplefacts := [];
  newvars := SMap.empty;
;;
