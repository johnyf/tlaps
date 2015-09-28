(*
 * backend/smt/fmt.ml --- Assign format
 *
 * Authors: Hernán Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 33161 $";;

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

(* let expr_type : TLAtype.t option pfuncs = Property.make ~uuid:"595aaaad-07ca-498b-8ebc-a473db6b0b99" "Backend.Smt.ExprType" ;;
let typ e = if has e expr_type then get e expr_type else None ;; *)
(* let typ e = Typesystem.get_type e ;; *)

let ( <<< ) (e:'a Property.wrapped) prop : 'a Property.wrapped = 
(* Util.eprintf "%a <<< %s" (print_prop ()) e prop.rep ; *)
    assign e prop () ;;

(**
- Require a Bool only when the argument of the expression allows it. For 
  example, not for the If condition. This will apply u2bool only to the 
  correct cases. No SMT term will be declared as Bool.
- Require Int only when the expression is known to be integer.
- If the expression is known to be integer, then format it as integer.
  get_type cx e = Int ---> e <<< fmtasint
*)
let rec assign_fmt req cx e : Expr.T.expr =
(* Util.eprintf "assign_fmt %s\t%a" (TLAtype.to_string req) (print_prop ()) (opaque cx e) ; *)
    let mk x = { e with core = x } in
    let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
    let apply1 op ex = Apply (Internal op |> mk, [ex]) |> mk in
    let applys op es = Apply (op, es) |> mk in
    let fcnapp f es = FcnApp (f, es) |> mk in
    (* let typ e = get_type cx e in *)
    let typ e = Option.default Bot (typ e) in
    let t = typ e in
    let is_Int e = (t = Int) in
    let fmt_term req e = 
(* Util.eprintf "\tfmt_term [%s, %s] %a\n" (TLAtype.to_string req) (TLAtype.to_string t) (print_prop ()) (opaque cx e) ; *)
        begin match t, req with
        | Int, Bot  -> e <<< fmtasint <<< applyint2u
        (* | Str, Bot  -> e <<< applystr2u *)
        | Int, Int  -> e <<< fmtasint
        (** No SMT term will be declared as Bool --> always apply u2bool when Bool is required. *)
        | _,   Bool -> e <<< applyu2bool
        | _         -> e
        end
    in
    begin match e.core with
    | Ix n                                        -> fmt_term req e
    | Opaque id                                   -> fmt_term req e
    | Apply ({core = Opaque ("isAFcn"|"isASeq"|"isFldOf")} as p, es) -> applys p (List.map (assign_fmt Bot cx) es)
    | Apply (({core = Ix _ | Opaque _} as f), es) -> fmt_term req (applys f (List.map (assign_fmt Bot cx) es))
    | FcnApp (f, es)                              -> fmt_term req (fcnapp (assign_fmt Bot cx f) (List.map (assign_fmt Bot cx) es))
    | Dot (ex, h)                                 -> fmt_term req (Dot (assign_fmt Bot cx ex, h) |> mk)
    | Apply ({core = Internal op}, es) -> 
        begin match op, es with
        | B.Mem, [x ; ({core = Internal B.Int} as y)] when is_Int x ->
            (* let x = if is_Int x then x <<< fmtasint else x in *)
            apply op (assign_fmt Int cx x) y <<< fmtasint
        | B.Eq, [{core = Internal B.TRUE | Internal B.FALSE} as e1 ; e2]
        | B.Eq, [e1 ; {core = Internal B.TRUE | Internal B.FALSE} as e2] -> 
            apply B.Equiv (assign_fmt Bool cx e1) (assign_fmt Bool cx e2)
        | B.Eq, [e1 ; e2] -> 
            let t1 = typ e1 in
            let t2 = typ e2 in
(* Util.eprintf "assign_fmt %s %a" (TLAtype.to_string req) (print_prop ()) (opaque cx e) ; *)
(* Printf.eprintf "\te1 :: %s\n" (TLAtype.to_string t1) ; *)
(* Printf.eprintf "\te2 :: %s\n" (TLAtype.to_string t2) ; *)
            begin match t1, t2 with
            | Int,  Int  -> apply op (assign_fmt Int cx e1) (assign_fmt Int cx e2)
            | Bool, Bool -> apply B.Equiv (assign_fmt Bool cx e1) (assign_fmt Bool cx e2)
            (* | Bot,  Bool -> apply B.Equiv (assign_fmt Bot cx e1 <<< applyu2bool) (assign_fmt Bool cx e2)
            | Bool, Bot  -> apply B.Equiv (assign_fmt Bool cx e1) (assign_fmt Bool cx e2 <<< applyu2bool) *)
            | _ ->          apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
            end
        | B.Conj,    [e1 ; e2]
        | B.Disj,    [e1 ; e2]
        | B.Implies, [e1 ; e2]
        | B.Equiv,   [e1 ; e2] -> 
            let e1 = assign_fmt Bool cx e1 in
            let e2 = assign_fmt Bool cx e2 in
            apply op e1 e2
        | B.Neg,    [ex]      -> apply1 op (assign_fmt Bool cx ex)
        | B.DOMAIN, [ex]      -> apply1 op (assign_fmt Bot cx ex)
        | B.Mem,    [e1 ; e2]
        | B.Range,  [e1 ; e2] -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
        | B.Lteq,   [e1 ; e2] 
        | B.Lt,     [e1 ; e2] 
        | B.Gteq,   [e1 ; e2] 
        | B.Gt,     [e1 ; e2] ->
            begin match typ e1, typ e2 with
            | Int, Int -> apply op (assign_fmt Int cx e1) (assign_fmt Int cx e2) <<< fmtasint 
            | Int, Bot -> apply op (assign_fmt Bot cx e1 <<< applyint2u) (assign_fmt Bot cx e2)
            | Bot, Int -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2 <<< applyint2u)
            | _ ->        apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
            end
        | B.Plus,      [e1 ; e2]
        | B.Minus,     [e1 ; e2] 
        | B.Times,     [e1 ; e2] 
        | B.Ratio,     [e1 ; e2] 
        | B.Quotient,  [e1 ; e2] 
        | B.Remainder, [e1 ; e2] 
        | B.Exp,       [e1 ; e2] ->
            begin match req, is_Int e1 && is_Int e2 with
            | Bot, true -> apply op (assign_fmt Int cx e1) (assign_fmt Int cx e2) <<< fmtasint <<< applyint2u
            | _,   true -> apply op (assign_fmt Int cx e1) (assign_fmt Int cx e2) <<< fmtasint
            | _         -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
            end
        | B.Uminus, [ex] -> 
            begin match req, is_Int ex with
            | Bot, true -> apply1 op (assign_fmt Int cx ex) <<< fmtasint <<< applyint2u
            | _, true   -> apply1 op (assign_fmt Int cx ex) <<< fmtasint
            | _         -> apply1 op (assign_fmt Bot cx ex)
            end
        | B.Prime, [ex] -> 
            apply1 op (assign_fmt req cx ex)
        (* | B.Prime, [{core = Ix _ | Opaque _} as ex] -> 
            apply1 op (assign_fmt req cx ex) *)

        | B.Seq,       [ex]      -> apply1 op (assign_fmt Bot cx ex)
        | B.Head,      [ex]      -> apply1 op (assign_fmt Bot cx ex)
        | B.Tail,      [ex]      -> apply1 op (assign_fmt Bot cx ex)
        | B.Len,       [ex]      -> let e = apply1 op (assign_fmt Bot cx ex) in if req = Int then e else e <<< applyint2u
        | B.BSeq,      [e1 ; e2] -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
        | B.Cat,       [e1 ; e2] -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
        | B.Append,    [e1 ; e2] -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
        | B.SelectSeq, [e1 ; e2] -> apply op (assign_fmt Bot cx e1) (assign_fmt Bot cx e2)
        | B.SubSeq,    [e1;e2;e3]-> applys (Internal op |> mk) (List.map (assign_fmt Bot cx) es)

        (* 
        | B.OneArg,    [e ; f] -> proc_out "oneArg" es
        | B.Extend,    [e ; f] -> proc_out "extend" es
        | B.Print,     [e ; v] -> proc_out "Print" es
        | B.PrintT,    [e]     -> proc_out "PrintT" es
        | B.Assert,    [e ; o] -> proc_out "Assert" es
        | B.JavaTime,  []      -> proc_out "JavaTime" es
        | B.TLCGet,    [i]     -> proc_out "TLCGet" es
        | B.TLCSet,    [i ; v] -> proc_out "TLCSet" es
        | B.Permutations, [s]  -> proc_out "Permutations" es
        | B.SortSeq,   [s ; o] -> proc_out "SortSeq" es
        | B.RandomElement, [s] -> proc_out "RandomElement" es
        | B.Any,       []      -> prefix "Any"
        | B.ToString,  [v]     -> proc_out "ToString" es *)

        | _ -> 
            Errors.set (Internal op |> mk) "fmt.ml: Arity mismatch";
            Util.eprintf ~at:(Internal op |> mk) "Arity mismatch or expression not normalized" ;
            failwith "Backend.Smt2.assign_fmt"
        end
    | Internal B.TRUE | Internal B.FALSE -> 
        (* if req = Bool then e <<< fmtasbool else e *)
        if req = Bool then e <<< applyu2bool else e
    | Num (m, "") -> if req = Int then e else e <<< applyint2u
    | Internal B.Infinity -> 
        if req = Bot then e <<< applyint2u else e
    | String _ -> e <<< applystr2u
    | If (c, t, f) ->
        let t1 = typ t in
        let t2 = typ f in
(* Util.eprintf "assign_fmt %s %a" (TLAtype.to_string req) (print_prop ()) (opaque cx e) ; *)
(* Printf.eprintf "\te1 :: %s\n" (TLAtype.to_string t1) ; *)
(* Printf.eprintf "\te2 :: %s\n" (TLAtype.to_string t2) ; *)
        let c = assign_fmt Bool cx c in
        begin match req, t1, t2 with
        | Int,  Int,  Int  -> If (c, assign_fmt Int cx t,  assign_fmt Int cx f) |> mk
        | Bot,  Int,  Int  -> If (c, assign_fmt Int cx t,  assign_fmt Int cx f) |> mk <<< applyint2u
        | Int,  Int,  Bot  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Bot,  Int,  Bot  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Int,  Bot,  Int  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Bot,  Bot,  Int  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Bool, Bool, Bool -> If (c, assign_fmt Bool cx t, assign_fmt Bool cx f) |> mk
        | _,    Bool, Bool -> If (c, assign_fmt Bool cx t, assign_fmt Bool cx f) |> mk
        | Bot,  Bot,  Bool -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Bot,  Bool, Bot  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        | Bool, Bool, Bot  -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk <<< applyu2bool
        | Bool, Bot,  Bool -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk <<< applyu2bool
        | Bool, _,    _    -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk <<< applyu2bool
        | _                -> If (c, assign_fmt Bot cx t,  assign_fmt Bot cx f) |> mk
        end
    | List (b, es) -> List (b, List.map (assign_fmt Bool cx) es) |> mk
    | Quant (q, bs, ex) ->      
        (** all Quants have No_domain after grounding *)
        Quant (q, bs, assign_fmt Bool (add_bs_ctx bs cx) ex) |> mk
    | Record es -> Record (List.map (fun (f,e) -> f, assign_fmt Bot cx e) es) |> mk
    | Tuple es -> 
        (* add_tuple (List.map (fun e -> if typ e = Int then Int else Bot) es) ; *)
        Tuple (List.map (fun e -> assign_fmt (* (if typ e = Int then Int else Bot) *)Bot cx e) es) |> mk
    | _ -> e
    end
;;
