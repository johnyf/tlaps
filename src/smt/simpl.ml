(*
 * backend/smt/simpl.ml --- Simplification methods. 
 *      (1) Abstraction of non-basic operators
 *      (2) Simplification of top-level equalities
 *
 * Author: Hernán Vanzetto <hernan.vanzetto@inria.fr>
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
open Smtcommons
open Typeinfer

module B = Builtin ;;


(** From Batteries List *****************************************************)
type 'a mut_list =  {
  hd: 'a;
  mutable tl: 'a list
}

external inj : 'a mut_list -> 'a list = "%identity"

let sort_unique cmp lst =
  let sorted = List.sort ~cmp:cmp lst in
  let fold first rest = List.fold_left
    (fun (acc, last) elem ->
       if (cmp last elem) = 0 then (acc, elem)
        else (elem::acc, elem)
    )
    ([first], first)
    rest
   in
  match sorted with
   | [] -> []
   | hd::tl ->
   begin
    let rev_result, _ = fold hd tl in
    List.rev rev_result
   end

let split_at index = function
  | [] -> if index = 0 then [],[] else invalid_arg "Index past end of list"
  | (h :: t as l) ->
    if index = 0 then [],l
    else if index < 0 then invalid_arg "Negative index not allowed"
    else
      let rec loop n dst l =
        if n = 0 then l else
        match l with
        | [] -> invalid_arg "Index past end of list"
        | h :: t ->
          let r = { hd =  h; tl = [] } in
          dst.tl <- inj r;
          loop (n-1) r t
      in
      let r = { hd = h; tl = [] } in
      inj r, loop (index-1) r t
;;
(****************************************************************************)

(** bounded vs cx e : Returns true if some variable id in (cx,e) is bounded by
    one of the ids in the list vs. Expression e can be only an non-basic (that 
    is, abstracted) expression. *)
let rec bounded vs cx e =
    let boundeds vs cx es = List.exists (bounded vs cx) es in
(* Util.eprintf "bounded %d in %a" vs (print_prop ()) (opaque cx e) ; *)
    match e.core with
    | Ix n -> n <= vs
    | Internal _ | String _ | Num _ | Opaque _ -> false
    | Apply (e, es) | FcnApp (e, es) -> boundeds vs cx (e::es)
    | SetEnum es | List (_, es) | Tuple es | Product es -> boundeds vs cx es
    | Quant (_, bs, ex) | SetOf (ex, bs) | Expr.T.Fcn (bs, ex) ->  
        let rec bound_bs = function
        | (_, _, Domain d) :: bs -> bounded vs cx d || bound_bs bs
        | _ :: bs -> bound_bs bs
        | [] -> false
        in
        (* let n = List.length bs in *)
        let ex = app_expr (scons (Opaque "" @@ e) (shift 0)) ex in      (** FIX: only replaces Ix 1 by Opaque "" instead of all bs *)
(* Util.eprintf "bounded' %d in %a" vs (print_prop ()) (opaque cx ex) ; *)
        bound_bs bs || bounded vs cx ex
    | Choose (h, None, ex)   -> bounded vs (add_bs_ctx [h, Unknown, No_domain] cx) ex
    | Choose (h, Some d, ex) -> bounded vs cx d || bounded vs (add_bs_ctx [h, Unknown, Domain d] cx) ex
    | SetSt (h, d, ex)       -> bounded vs cx d || bounded vs (add_bs_ctx [h, Unknown, Domain d] cx) ex
    | Arrow (e1, e2) -> boundeds vs cx [e1;e2]
    | Dot (ex, _) -> bounded vs cx ex
    | Record rs -> List.exists (fun (_,e) -> bounded vs cx e) rs
    | Rect rs ->   List.exists (fun (_,e) -> bounded vs cx e) rs
    | Except (f, exspecs) ->
        let faux2 = function
        | Except_dot _ -> false
        | Except_apply e -> bounded vs cx e
        in
        let faux exps ex = (List.fold_left (fun r e -> faux2 e || r) false exps) || bounded vs cx ex in
        bounded vs cx f || List.fold_left (fun r (exps, ex) -> faux exps ex || r) false exspecs
    | If (c,t,f) -> boundeds vs cx [c ; t ; f]
    | _ -> false
;;

(** nonbasic_vars e: returns the list of already abstracted variables 
    (non_basic_ops) that appear in the expression e *)
let rec nonbasic_vars e : string list =
    let nbvs es = List.fold_left (fun r e -> nonbasic_vars e @ r) [] es in
    match e.core with
    | Opaque s -> if SMap.mem s !nonbasic_ops then [s] else []
    | Ix _ | Internal _ | String _ | Num _  -> []
    | Apply (e, es) | FcnApp (e, es) -> nbvs (e :: es)
    | SetEnum es | List (_, es) | Tuple es | Product es -> nbvs es
    | Quant (_, bs, ex) | SetOf (ex, bs) | Expr.T.Fcn (bs, ex) ->  
        let rec nonbasic_vars_bs = function
        | (_, _, Domain d) :: bs -> nonbasic_vars d @ nonbasic_vars_bs bs
        | _ :: bs -> nonbasic_vars_bs bs
        | [] -> []
        in
        nonbasic_vars ex @ nonbasic_vars_bs bs
    | SetSt (_, e1, e2) | Arrow (e1, e2) -> nbvs [e1 ; e2]
    | Dot (ex, _) -> nonbasic_vars ex
    | Record rs | Rect rs -> nbvs (List.map (fun (_,e) -> e) rs)
    | Except (f, exspecs) ->
        let faux2 = function
        | Except_dot _ -> []
        | Except_apply e -> nonbasic_vars e
        in
        let faux exps ex = (List.fold_left (fun r e -> faux2 e @ r) [] exps) @ nonbasic_vars ex in
        nonbasic_vars f @ List.fold_left (fun r (exps, ex) -> faux exps ex @ r) [] exspecs
    | If (c, t, f) -> nbvs [c ; t ; f]
    | _ -> []
;;

let add_nonbasic_op s cx e = 
(* Util.eprintf "++Add_nonbasic_op: %s <- %a : %s" s (print_prop ()) ((* opaque ~strong:true cx *) e) (typ_to_str e) ; *)
(* List.iter (fun (k,(cx,e)) -> Util.eprintf "  !nonbasic_op: %s -> %a : %s" k (print_prop ()) (opaque ~strong:true cx e) (typ_to_str e)) (SMap.bindings !nonbasic_ops) ; *)
  nonbasic_ops := SMap.add s (cx,e) !nonbasic_ops ;
;;
let remove_nonbasic_op s =
(* Util.eprintf "--Remove non-basic op %s" s ; *)
  nonbasic_ops := SMap.remove s !nonbasic_ops 
;;
let find_nonbasic_op_id cx e =
(* Util.eprintf ">>find_nonbasic_op_id %a" (print_prop ()) ((* opaque ~strong:true cx *) e) ; *)
(* List.iter (fun (k,(cx,e)) -> Util.eprintf " all nbop: %s -> %a : %s" k (print_prop ()) (opaque ~strong:true cx e) (typ_to_str e)) (SMap.bindings !nonbasic_ops) ; *)
  try let v,_ = 
    List.find begin fun (_,(cx',e')) ->
(* Util.eprintf "\t  nbop1: %a : %s" (print_prop ()) (opaque ~strong:true cx e) (typ_to_str e) ; *)
(* Util.eprintf "\t  nbop2: %a : %s" (print_prop ()) (opaque ~strong:true cx' e') (typ_to_str e') ; *)
      (* cx = cx' && *)
      Expr.Eq.expr (opaque ~strong:true cx e) 
                   (opaque ~strong:true cx' e')
      end (SMap.bindings !nonbasic_ops)
    in 
(* Util.eprintf "\told non-basic op id: %s" v ; *)
    v
  with Not_found -> begin
    let v = nonbasic_prefix ^ (fresh_id ()) in
    (* let v = if free_vars cx e = [] then fof_id_vars true v else v in  *)
    let fv = free_vars cx e in
    (* List.iter (fun v -> Printf.eprintf "fv: %s\n" v) fv ; *)
    let v = fof_id_vars (fv <> []) v in 
    add_nonbasic_op v cx e ;
    add_choose v cx e ;
(* Util.eprintf "\tnew non-basic op id: %s" v ; *)
    v
  end
;; 

let rec abstract cx e : Expr.T.expr =
(* Printf.eprintf "nbops: %s -- " (String.concat "." (List.map (fun (s,_) -> s) (SMap.bindings !nonbasic_ops))) ; *)
(* Util.eprintf "abstract: %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
    let mk x = { e with core = x } in
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    let mb x = x |> mc <<< Some Bool in
    let abs cx e = 
(* Util.eprintf "abs! %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
        Opaque (find_nonbasic_op_id cx e) |> mc <<< typ e in
    let abstract_bool cx e = if get_type cx e = Bool then abs cx e else abstract cx e in
    let part_nonbvars ecx ex n =
      (** ss = nonbasic vars, not repeated, and that are bounded by this quantifier *)
      nonbasic_vars ex                                                        (** ss = [a__5,a__7,...] *)
      |> remove_repeated
      |> List.map (fun s -> let cx,e = SMap.find s !nonbasic_ops in s,cx,e)   (** ss = [a__5,cx1,e1 ; a__7,cx2,e2 ; ...] *)
      |> List.partition 
          begin fun (id,cx,e) -> 
            let d = List.length cx - List.length ecx in
(* Util.eprintf "search bounded by <%d in %a" (n+d) (print_prop ()) (opaque cx e) ; *)
            bounded (n + d) cx e
          end
    in
    let mk_defs ecx ss = 
      List (And, List.map 
        begin fun (id,cx,e) -> 
          let d = List.length ecx - List.length cx in
          let e = if d > 0 then app_expr (shift d) e else e in
          Apply (Internal B.Eq |> mb, [ Opaque id |> mc <<< typ e ; (* opaque cx' *) e ]) |> mb
        end ss) |> mb 
      |> Ground.gr1 ecx
      |> fun eqs -> match eqs.core with List (And, es) -> es | _ -> [eqs]
    in
    match e.core with
    | Apply ({core = Internal (B.Cap | B.Cup | B.Setminus | B.SUBSET | B.UNION)}, _) 
    | SetOf _ | SetSt _ | SetEnum (_ :: _) 
    (** Range is not abstracted *)
    (* | Apply ({core = Internal B.Range}, _)  *)   
    | Expr.T.Fcn _ | Arrow _ | Except _
    (* | Dot _  *)
    (* | Internal B.Nat  *)
    | Rect _ | Product _ 
    | Choose _ 
    (* | Apply ({core = Internal B.Len}, _)  *)
    | Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, _)}])
    | Apply ({core = Internal B.Cat}, _) | Apply ({core = Internal B.SubSeq}, _) 
    | Lambda _ -> 
        abs cx e
    | Quant (q, bs, ex) ->
        (* let bs = abstract_bs cx bs in *)
        let ecx = add_bs_ctx bs cx in
        let ex = abstract ecx ex in
        let n = List.length bs in
        (** ss = non_basic_ops bounded by this quantifier (or without free vars) *)
        let ss,nss = part_nonbvars ecx ex n in
        (* List.iter begin fun (id,cx',e') ->
          nonbasic_ops := SMap.add (fof_id_vars true id) (cx',e') (SMap.remove id !nonbasic_ops)
          end 
        ss ; *)
        List.iter begin fun (id,cx',e') ->
          (** Shift the non_basic_ops *not* bounded by this quantifier. *)
          let (_,cx') = split_at n cx' in
          let e' = app_expr (shift (0 - n)) e' in
          nonbasic_ops := SMap.add id (cx',e') (SMap.remove id !nonbasic_ops)
          end 
        nss ;
(* List.iter (fun (k,(cx,e)) -> Util.eprintf "  [nonbasic_op: %s -> %a : %s" k (print_prop ()) (opaque ~strong:true cx e) (typ_to_str e)) (SMap.bindings !nonbasic_ops) ; *)
        let ex = if ss = [] then ex else begin
          let eqs = mk_defs ecx ss in
          List.iter (fun (s,_,_) -> remove_nonbasic_op s) ss ;
          let hs,ex = deimpl ex in
          let hs = eqs @ hs in            
          let hs = match hs with [h] -> h | _ -> List (And, hs) |> mb in
          let ss = List.map (fun (s,_,e) -> (assign (s |> mc <<< typ e) boundvar ()), Unknown, No_domain) ss in
          Apply (Internal B.Implies |> mb, [hs ; ex]) |> mb 
            |> app_expr (shift (List.length ss))
            |> fun ex -> Quant (Forall, ss, ex) |> mb
          (* let ex = Typeinfer.paint_types cx ex in *)
          end
        in 
        Quant (q, bs, ex) |> mb
    | List (b, es) ->   List (b, List.map (abstract cx) es) |> mb
    | FcnApp (f, es) -> FcnApp (abstract cx f, List.map (abstract cx) es) |> mk
    | Record rs ->      Record (List.map (fun (s,e) -> s, abstract_bool cx e) rs) |> mk
    | Tuple es ->       Tuple (List.map (abstract_bool cx) es) |> mk
    | Apply (e, es) ->  Apply (abstract cx e, List.map (abstract cx) es) |> mk
    | Dot (ex,h) ->     Dot (abstract cx ex,h) |> mk
    | If (c,t,f) ->
        begin match !mode with 
        | Spass | Fof -> abs cx e
        | _ -> If (abstract cx c, abstract cx t, abstract cx f) |> mk
        end
    | _ -> e
(* and abstract_bs cx bs =
    let f = function
    | (v, k, Domain d) -> (v, k, Domain (abstract cx d))
    | b -> b
    in List.map f bs *)
;;

(** r_term ::= <Id/Opaque symbol> | r_term(r_term,..,r_term) | Prime (r_term) | FcnApp (r_term, _) *)
let rec is_rewrite_term e =
    match e.core with
    | Ix _ | Opaque _ -> true
    (* | Apply ({core = Internal B.Prime}, [ex]) -> is_rewrite_term ex *)
    | Apply (ex, es) -> List.for_all is_rewrite_term (ex :: es)
    | FcnApp (ex, _) -> is_rewrite_term ex
    | Internal B.Prime
    | Internal B.Len
    | Internal B.Append
    | Internal B.Cat
    | Internal B.SubSeq -> true
    | _ -> false

(** rew_domain ::= DOMAIN (r_term) *)
let rec is_rewrite_domain e =
    match e.core with
    | Apply ({core = Internal B.DOMAIN}, [ex]) -> is_rewrite_term ex
    | _ -> false

let rec is_non_rewrite_expr e =
    match e.core with
    | Except _ 
    | Arrow _ 
    | Choose _ 
    | Expr.T.Fcn _ -> true
    | _ -> false


let simpl_eq cx hs = 

    (** discard: Registers if at least one replace has been made. If true, 
        then it doesn't keep the equality in the list of hypothesis. *)
    let discard = ref false in

    (** replace x by y [x <- y] in the expression cx |- e *)
    let rec replace x y cx e = 
        let mk x = { e with core = x } in
        let rep ?shift:(n=0) = replace (app_expr (shift n) x) (app_expr (shift n) y) in
        let rep_bound cx = function
        | (h, k, Domain dom) -> (h, k, Domain (rep cx dom))
        | b -> b
        in
        let rep_bs cx bs = List.map (rep_bound cx) bs in
        let reps cx es = List.map (rep cx) es in
        let rep_exspec cx exs = 
            let faux cx = function
            | Except_dot s -> Except_dot s
            | Except_apply ea -> Except_apply (rep cx ea)
            in
            List.map (fun (eps,ex) -> List.map (faux cx) eps, rep cx ex) exs
        in
        let rep_opt cx = function
        | None -> None
        | Some e -> Some (rep cx e)
        in
(* Util.eprintf "replace: %a" (print_prop ()) (opaque cx e) ; *)
        let y = if is_conc e then assign y isconc () else y in
        if is_rewrite_domain e && Expr.Eq.expr x e 
          then y
          else if Expr.Eq.expr x e 
            then (discard := true ; y)
            (* if is_rewrite_term e && Expr.Eq.expr x e 
                then (discard := true ; y)
            else if is_rewrite_domain e && Expr.Eq.expr x e 
                then y *)
            else match e.core with
            | Internal _ | String _ | Num _ -> e
            | Apply ({core = Internal B.Prime}, _) -> e
            | Apply (e,es)    -> Apply (rep cx e, reps cx es) |> mk 
            | List (b,es)     -> List (b, reps cx es) |> mk
            | Quant (q, bs, ex)   -> let bs = List.map (rep_bound cx) bs in Quant (q, bs, rep ~shift:(List.length bs) (add_bs_ctx bs cx) ex) |> mk
            | Expr.T.Fcn (bs, ex) -> let bs = List.map (rep_bound cx) bs in Expr.T.Fcn (bs, rep ~shift:(List.length bs) (add_bs_ctx bs cx) ex) |> mk
            | SetOf (ex, bs)      -> let bs = List.map (rep_bound cx) bs in SetOf (rep ~shift:(List.length bs) (add_bs_ctx bs cx) ex, bs) |> mk
            | SetSt (h, dom, ex)  -> let bs = List.map (rep_bound cx) [h, Unknown, Domain dom] in SetSt (h, rep cx dom, rep ~shift:(List.length bs) (add_bs_ctx bs cx) ex) |> mk
            | Except (f, [([Except_apply e1],e2)]) -> Except (rep cx f, [([Except_apply (rep cx e1)], (rep cx e2))]) |> mk
            | SetEnum es      -> SetEnum (reps cx es) |> mk
            | Tuple es        -> Tuple   (reps cx es) |> mk
            | Product es      -> Product (reps cx es) |> mk
            | FcnApp (ex, es) -> FcnApp  (rep cx ex, reps cx es) |> mk
            | Arrow (e1,e2)   -> Arrow   (rep cx e1, rep cx e2) |> mk
            | Except (f, exs) -> Except  (rep cx f, rep_exspec cx exs) |> mk
            | Dot (ex, fd)    -> Dot     (rep cx ex, fd) |> mk
            | Record rs       -> Record  (List.map (fun (s,e) -> s, rep cx e) rs) |> mk
            | Rect rs         -> Rect    (List.map (fun (s,e) -> s, rep cx e) rs) |> mk
            | If (c,t,f)      -> If      (rep cx c, rep cx t, rep cx f) |> mk
            | Case (es, o)    -> Case    (List.map (fun (c,e) -> (rep cx c, rep cx e)) es, rep_opt cx o) |> mk
            | Sequent seq     -> rep cx (unroll_seq seq)
            | Parens (ex,_)   -> rep cx ex
            | Choose (h,None,ex) ->
                (* add_choose (fresh_name ()) cx e ; *)
                Choose (h, None, rep ~shift:1 (add_bs_ctx [h, Unknown, No_domain] cx) ex) |> mk
            | Choose (h,Some dom,ex) ->
                let bs = rep_bs cx [h, Unknown, Domain dom] in
                Choose (h, Some (rep cx dom), rep ~shift:1 (add_bs_ctx bs cx) ex) |> mk
            | _ -> e
    in

    let rec simp hs =
        match hs with
        | [] -> []
        | h :: hs when is_conc h -> hs @ [h]
        | _ :: [] -> hs
        | e' :: hs -> 
(* Util.eprintf "simpl_eq: %a" (print_prop ()) (opaque cx e') ; *)
            begin match e'.core with
            | Apply ({core = Internal B.Eq}, [_ ; {core = Choose _}]) -> 
(* Util.eprintf "simpl_eq: %a" (print_prop ()) (opaque cx e') ; *)
                simp (hs @ [e'])
            | Apply ({core = Internal B.Eq}, [x ; y]) when is_rewrite_term x || is_rewrite_domain x ->
(* Util.eprintf "simpl_eq: %a" (print_prop ()) (opaque cx e') ; *)
                discard := false ;
                let hs = List.map (replace x y cx) hs in
                (** TODO: check that x is not a recursive definition! *)
                if (not (is_rewrite_domain x)) && is_non_rewrite_expr y 
                (* if !discard  *)
                  then simp hs
                  else simp (hs @ [e'])
            | _ ->
                simp (hs @ [e'])
            end
    in
    simp hs  
;;
