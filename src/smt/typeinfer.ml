(*
 * backend/smt/typeinfer.ml --- Type inference
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

open Printf
open List

open Smtcommons
open Typesystem

module B = Builtin;;

let types = new Typesystem.types ;;

type inferAction = 
    | Update_fact 
    | Update_safe       (** Updates only to safe types, but returns the correct inferred type. *)
;;
let inferaction_to_string = function
    | Update_fact     -> "Update_fact"
    | Update_safe     -> "Update_safe"
;;

let rec is_safe_fact e =
    let rec arity e = 
        match e.core with
        | Ix _ | Opaque _ -> 0
        | Apply ({core = Ix _ | Opaque _}, es) -> 1(* length es *)
        | Apply ({core = Internal B.Prime}, [ex]) -> arity ex
        | _ -> -1
    in
    match e.core with
    | Apply ({core =   Internal B.Mem
                     | Internal B.Eq 
                     | Internal B.Subseteq
                     }, [e1 ; _]) 
        when arity e1 = 0 -> true
    (* | Apply ({core = Internal B.Disj}, es) | List (Or, es) -> 
        for_all is_safe_fact es && 
        for_all begin fun e -> 
            match e.core with
            | Apply ({core =   Internal B.Mem
                             | Internal B.Eq 
                             | Internal B.Subseteq
                             }, [e1 ; _]) 
            
            end *)
(* | Quant (Forall, ((v, _, Domain _) as b :: bs (* as bounds *)), 
            ({core = Apply ({core = (Internal B.Mem | 
                                     Internal B.Eq | 
                                     Internal B.Subseteq)}, [e1 ; _])} as exp))
            when arity e1 = length bs + 1 ->
        let (bounds, exp) = split_domain Forall exp [b] bs in
        let sort = ref Bot in
        let aux = function 
        | (v,_,Domain dom) -> 
            sort := TLAtype.base (type_infer Update_safe cx dom (P Bot)) ;
            types#update (quant_id v.core) !sort
        | (v,_,Ditto) -> 
            types#update (quant_id v.core) !sort
        | _ -> Util.bug "src/backend/typeinfer.ml \n"
        in            
        iter aux bounds ;
        ignore (type_infer Update_fact (add_bs_ctx bounds cx) exp Bool) ;
        iter (fun (v,_,_) -> types#remove (quant_id v.core)) bounds *)
    | _ -> false
    ;;

(*** min = Expected/Minimum type for expression e, 
     ia = inference action 
    *)
let rec type_infer (ia:inferAction) cx e (min:tlatype) : tlatype =    
(* Util.eprintf "\t%s (%s) \t%a" (inferaction_to_string ia) (TLAtype.to_string min) (print_prop ()) (opaque cx e) ; *)
    let mk x = { e with core = x } in
    let eq_type cx e1 e2 min =
        let ia1, ia2 = match ia with
        | Update_fact -> Update_fact, Update_safe
        | _ -> ia, ia
        in
        (*** First e2, just because usually(?) e2 is more complex than e1. 
             So e1's type can be better inferred. *)
        let s2 = ref (type_infer ia2 cx e2 min) in
        let s1 = ref (type_infer ia1 cx e1 !s2) in
        let s2 = ref (type_infer ia2 cx e2 !s1) in
        let s1, s2 = 
            match !s1, !s2 with
            | (Bot | Bool | Str), (Bot | Bool | Str) -> s1,s2
            | _ -> let s = TLAtype.max !s1 !s2 in (ref s, ref s)
        in
        if (not (TLAtype.eq !s1 !s2)) 
        then begin
            if (TLAtype.gt !s1 !s2)      (** try again only once *)
                then s2 := type_infer ia1 cx e2 !s1
                else s1 := type_infer ia2 cx e1 !s2 ;
            if (!s1 <> !s2) 
                then Bot
                else TLAtype.max !s1 !s2
            end
        else !s1
    in
    let process_ix id is_primed = 
        let update_ix is_primed id typ = 
            if is_primed then (
                types#update (prime id) typ ;
                (if types#exists id then types#update id typ)
            ) else (
                types#update id typ ;
                (if types#exists (prime id) then types#update (prime id) typ)
            ) ; typ
        in
        let is_unspec id = check_prefix id "unspec__" in
        if is_unspec id then update_ix is_primed id (TLAtype.max min (types#find id)) else
        begin match ia with
        | Update_fact -> 
            update_ix is_primed id (TLAtype.max min (types#find id))
        | Update_safe ->
            let t = TLAtype.max min (types#find id) in
            ignore (update_ix is_primed id (TLAtype.to_safe_type t)) ;
            t
        end
    in
    let inf min cx e = type_infer ia cx e min in
    let infi min cx e = ignore (inf min cx e) in
    let eqi min cx e1 e2 = ignore (eq_type cx e1 e2 min) in
    match e.core with
    | Ix n ->
        let id = lookup_id cx n in
        (* update_cx n ; *)
        TLAtype.max (process_ix id false) 
                    (types#find (prime id)) 
    | String str ->
        Str
    | Opaque id -> 
        (* types#find (unprime_id str) *)
        TLAtype.max (process_ix (unprime_id id) false) 
                    (types#find (prime id)) 
    | Apply ({core = Internal op}, es) ->
        begin match op, es with
        | B.Prime, [ex] ->
            inf min cx ex
        | B.Conj, _
        | B.Disj, _
        | B.Implies, _
        | B.Equiv, _ 
        | B.Neg, _ -> 
            iter (infi Bot cx) es ; Bool
        | B.Eq,  [e1 ; e2]
        | B.Neq, [e1 ; e2] ->
            eqi Bot cx e1 e2 ; Bool             
        | B.Mem,    [e1 ; e2]
        | B.Notmem, [e1 ; e2] ->
            eqi (P Bot) cx (SetEnum [e1] |> mk) e2 ; Bool
        | B.Cap,      [e1 ; e2]
        | B.Cup,      [e1 ; e2]
        | B.Setminus, [e1 ; e2] -> 
            let t1 = inf (P Bot) cx e1 in
            let t2 = inf (P Bot) cx e2 in
            begin match t1, t2 with
            | P a, P b when a = b -> t1
            | P (Int|Real), P (Int|Real) -> TLAtype.max t1 t2
            | P (Rec _), P (Rec _) -> TLAtype.max t1 t2
            | P (Tup _), P (Tup _) -> TLAtype.max t1 t2
            | P _, P _ -> P Bot
            | _ -> Util.eprintf "[TypeInfer] Warning: Set operator subexpressions are not sets in %a" 
                                (print_prop ()) (opaque cx e) ; 
                   P Bot
            end
        | B.Subseteq, [e1 ; e2] -> 
            eqi (P Bot) cx e1 e2 ; Bool
        | B.SUBSET, [ex] ->
            P (inf (P (TLAtype.base (TLAtype.base min))) cx ex)
        | B.UNION, [ex] ->
            begin match inf (P (P (TLAtype.base min))) cx ex with 
            | P (P s) -> P s
            | _ -> P Bot
            end
        | B.DOMAIN, [f] -> 
            begin match inf (Fcn (TLAtype.base min, Bot)) cx f with
            | Fcn (a,_) -> P a
            | _ -> P Bot
            end
        | B.Plus,      [e1 ; e2]
        | B.Minus,     [e1 ; e2]
        | B.Times,     [e1 ; e2]
        | B.Ratio,     [e1 ; e2]
        | B.Exp,       [e1 ; e2]
        | B.Quotient,  [e1 ; e2]
        | B.Remainder, [e1 ; e2] ->
            eq_type cx e1 e2 min
        | B.Uminus, [ex] -> 
            infi Bot cx ex ; TLAtype.max min Int
        | B.Lt,   [e1 ; e2]
        | B.Lteq, [e1 ; e2]
        | B.Gt,   [e1 ; e2]
        | B.Gteq, [e1 ; e2] -> 
            eqi Bot cx e1 e2 ; Bool
        | B.Range, [e1 ; e2] ->
            let min = TLAtype.max Int (TLAtype.base min) in
            let s1 = inf min cx e1 in
            let s2 = inf min cx e2 in
            begin match s1, s2 with
            | (Real | Int), (Real | Int) -> P (TLAtype.max s1 s2)
            | _ -> P Bot
            end
        | B.Seq,       [ex]      -> infi (P Bot) cx ex ; P (Tup [])
        | B.Len,       [ex]      -> infi Bot cx ex ; Int
        | B.BSeq,      [e1 ; e2] -> iter (infi Bot cx) es ; Bot
        | B.Cat,       [e1 ; e2] -> 
            let t1 = inf min cx e1 in
            let t2 = inf min cx e2 in
            begin match t1,t2 with
            | Tup t1, Tup t2 -> Tup (t1 @ t2)
            | _ -> Tup []
            end
        | B.Append,    [e1 ; e2] -> 
            let t1 = inf min cx e1 in
            let t2 = inf Bot cx e2 in
            begin match t1 with
            | Tup [] -> Tup [t2]
            | Tup ts -> Tup (ts @ [t2])
            | _ -> Tup []
            end
        | B.Head,      [ex]      -> 
            begin match inf Bot cx ex with
            | Tup [] -> Bot
            | Tup ts -> hd ts
            | _ -> Bot
            end
        | B.Tail,      [ex]      -> 
            begin match inf Bot cx ex with
            | Tup [] -> Bot
            | Tup ts -> Tup (tl ts)
            | _ -> Tup []
            end
        | B.SubSeq,    [e1;e2;e3]-> iter (infi Bot cx) es ; Tup []
        | B.SelectSeq, [e1 ; e2] -> iter (infi Bot cx) es ; Tup []

        | B.OneArg,    [e ; f] -> Bot
        | B.Extend,    [e ; f] -> Bot
        | B.Print,     [e ; v] -> Bot
        | B.PrintT,    [e]     -> Bot
        | B.Assert,    [e ; o] -> Bot
        | B.JavaTime,  []      -> Bot
        | B.TLCGet,    [i]     -> Bot
        | B.TLCSet,    [i ; v] -> Bot
        | B.Permutations, [s]  -> Bot
        | B.SortSeq,   [s ; o] -> Bot
        | B.RandomElement, [s] -> Bot
        | B.Any,       []      -> Bot
        | B.ToString,  [v]     -> Bot
        | B.Unprimable, [ex] -> 
            inf min cx ex
        | _ -> 
            Errors.set (Internal op |> mk) "type_infer.ml: expression not supported";
            Util.eprintf ~at:(Internal op |> mk) "Apply expression not supported" ;
            failwith "Backend.Smt.type_infer"
        end
    | Internal B.TRUE
    | Internal B.FALSE ->
        Bool
    | List (_, es) -> iter (infi Bot cx) es ; Bool
    | Quant (_, ((_, _, No_domain) :: _ as bs), ex) -> 
        let cx = add_bs_ctx bs cx in
        infer_facts_bounded cx ex ;
        infi Bot cx ex ; 
        iter (fun (v,_,_) -> types#remove ((* quant_id *) v.core)) bs ;
        Bool
    | Quant (q, ((v, _, Domain dom) as b :: bs), ex) ->
        let (bs, ex) = split_domain q ex [b] bs in
        let dom = app_expr (shift (length bs)) dom in
        let exdom = fold_left (fun r b -> (Apply (Internal B.Mem |> mk, [ Ix (length r + 1) |> mk ; dom]) |> mk) :: r) [] bs in
        let exdom = match exdom with
        | [] -> Internal B.TRUE |> mk
        | [b] -> b
        | _ -> List (And, exdom) |> mk
        in
        let ex2 = Apply (Internal B.Implies |> mk, [exdom ; ex]) |> mk in
        
        let cx = add_bs_ctx bs cx in
        infer_facts_bounded cx ex2 ;
        infi Bot cx ex ; 
        iter (fun (v,_,_) -> types#remove ((* quant_id *) v.core)) bs ;
        Bool
    | Internal B.BOOLEAN -> P Bool
    | Internal B.STRING -> P Str
    (* | SetOf (ex, ([h,_,Domain dom] as bs)) ->
        let typd = inf (P Bot) cx dom in
        types#update (quant_id h.core) (TLAtype.base typd) ;
        let typ = inf (TLAtype.base min) (add_bs_ctx bs cx) ex in
        types#remove (quant_id h.core) ;
        P typ *)
    | SetOf (ex, bs) ->
        let rec inf_bs cx = function
        | (h,_,Domain d) :: bs -> (h,TLAtype.base (inf (P Bot) cx d)) :: inf_bs cx bs
        | [] -> []
        | _ -> assert false
        in
        let tbs = inf_bs cx (unditto bs) in
        iter (fun (h,t) -> types#update ((* quant_id *) h.core) t) tbs ;
        let t = inf (TLAtype.base min) (add_bs_ctx bs cx) ex in
        iter (fun (h,_) -> types#remove ((* quant_id *) h.core)) tbs ;
        P t
    | SetSt (h, dom, ex) ->
        let typd = inf (P Bot) cx dom in
        infi Bool (add_bs_ctx [h, Unknown, Domain dom] cx) ex ;
        typd
    | SetEnum [] ->
        P (TLAtype.base min)
    | SetEnum [ex] -> 
        P (inf (TLAtype.base min) cx ex)
    | SetEnum (e1 :: elmts) -> 
        let s1 = inf (TLAtype.base min) cx e1 in
        let typ = ref s1 in
        let rec f = function
        | e :: es -> 
            let typ2 = inf (TLAtype.base min) cx e in
            typ := if !typ = typ2 then !typ else Bot ;
            f es
        | [] -> ()
        in
        f elmts ;
        P !typ
    | Choose (h, None, ex) ->
        infi Bool (add_bs_ctx [h, Unknown, No_domain] cx) ex ;
        min
    | Choose (h, Some dom, ex) ->
        infi Bool (add_bs_ctx [h, Unknown, Domain dom] cx) ex ;
        TLAtype.base (inf (P Bot) cx dom)
    | FcnApp (f, [{core = Num (n,"")}]) ->
        begin match inf Bot cx f with
        | Tup ts ->
            begin try nth ts ((int_of_string n) - 1)
            with Invalid_argument _ | Failure _ -> Bot
            end
        | Fcn ((Bot|Int|Real),b) -> b
        | t -> Bot
        end
    | FcnApp (f, [arg]) ->
        let arg_type = inf Bot cx arg in
        let f_type = inf (Fcn (arg_type, min)) cx f in
        begin match f_type, arg.core with
        | Fcn (a, b), _ -> infi a cx arg ; b
        | Tup types, Num (n,"") -> 
            let i = int_of_string n in
            (try nth types (i - 1) with Invalid_argument _ | Failure _ -> Bot)
        | Rec _, String h -> TLAtype.dot f_type h
            (* begin try SMap.find h m with Not_found -> Bot end *)
        | t, _ -> Bot
        end
    | FcnApp (f, a :: args) ->        (** f[x,y] = (f[x])[y] *)
        inf Bot cx (FcnApp (FcnApp (f,[a]) |> mk, args) |> mk)
    | Arrow (e1,e2) -> 
        let a,b = match min with
            | P (Fcn (a,b)) -> a,b
            | _ -> Bot,Bot
        in
        begin match inf (P a) cx e1, inf (P b) cx e2 with
        | P a, P b -> P (Fcn (a, b))
        | P a, _   -> P (Fcn (a, Bot))
        | _,   P b -> P (Fcn (Bot, b))
        | _        -> P (Fcn (Bot, Bot))
        end
    | Expr.T.Fcn ([v,_,Domain dom], ex) ->
        let a,b = match min with
        | Fcn (a,b) -> a,b
        | _         -> Bot,Bot
        in
        let typd = inf (P a) cx dom in
        let id = (* quant_id *) v.core in
        types#update id (TLAtype.base typd) ;
        let cx = (Flex (id |> mk) |> mk) :: cx in
        let typ = inf b cx ex in
        types#remove id ;
        Fcn (TLAtype.base typd, typ)
    | Except (f, [([Except_apply x],y)]) ->
        let a,b = match min with
        | Fcn (a,b) -> a,b
        | _         -> Bot,Bot 
        in
        let a = inf a cx x in
        let b = inf b cx y in
        let typ = inf (Fcn (a,b)) cx f in     (** updates f's type *)
        typ
    | Dot (ex, h) ->
        TLAtype.get_fieldtyp h (inf (Rec (SMap.singleton h min)) cx ex)
    | Record rs -> 
        Rec (list_to_map (map (fun (h,e) -> (h, inf (TLAtype.dot min h) cx e)) rs))
    | Rect rs ->
        (** does not consider min *)
        P (Rec (list_to_map (map (fun (h,e) -> (h, TLAtype.base (inf (P Bot) cx e))) rs)))
    | Except ({core = Ix n}, _) ->
        types#find (lookup_id cx n)
    | Except (ex, [([Except_dot h],e)]) ->
        infi (TLAtype.dot min h) cx e ;
        inf (Rec (SMap.singleton h min)) cx ex
        (* begin match ex.core with
        | Ix n -> types#find (lookup_id cx n)
        | Except _ -> TLAtype.max min (inf Bot cx ex)
        | _ -> Util.bug "src/backend/typeinfer.ml 400"
        end *)
    | Tuple es ->
        Tup (map (inf Bot cx) es)
    | Product es -> 
        (** does not consider min *)
        P (Tup (map (fun e -> TLAtype.base (inf (P Bot) cx e)) es))
    | Num (m, "") -> 
        (* if ia = Get_type_bounds then Int else *)
        begin match min with
        | Real | Int -> min
        | _ -> Int
        end
    | Num (m, n) -> Real
    | Internal B.Infinity -> Int
    | Internal B.Nat ->
        begin match min with
        | P Real | P Int -> min
        | _ -> P Int
        end
    | Internal B.Int ->
        begin match min with
        | P Real -> min
        | _ -> P Int
        end
    | Internal B.Real ->
        P Real
    | If (c,t,f) ->
        infi Bool cx c ;
        eq_type cx t f min
    | Case ((p1,e1) :: es, Some other) ->
        infi Bool cx p1 ;
        let sort1 = inf Bot cx e1 in
        iter (fun (p,e) -> infi Bot cx p ; infi sort1 cx e) es ;
        infi sort1 cx other ;
        sort1
    | Case ((p1, e1) :: es, None) ->
        infi Bool cx p1 ;
        let sort1 = inf Bot cx e1 in
        iter (fun (p,e) -> infi Bot cx p ; infi sort1 cx e) es ;
        sort1
    | Apply (pred, args) -> 
        let ptyps = TLAtype.args (inf Bot cx pred) in
        let ptyps = if length ptyps = length args then ptyps else (map (fun _ -> Bot) args) in
        let argtypes = rev_map2 (fun a b -> inf b cx a) args ptyps in
        let typ = fold_left (fun s a -> Fcn (a,s)) min argtypes in
        let typ = inf typ cx pred in
        begin match typ with
        | P _ as t -> eqi t cx pred (SetEnum args |> mk)
        | _ -> ()
        end ;
        TLAtype.returns typ
    | Sequent seq ->
        infi Bot cx (unroll_seq seq) ;
        Bool
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            rev (new_ctx_vars xs) @ cx
        in
        let t = inf Bot (add_to_ctx cx xs) ex in
        fold_left (fun r _ -> Fcn (Bot,r)) t xs
        (* Fcn (Bot, t) *)
    | Parens (ex,_) ->
        inf min cx ex
    | _ ->
        Util.eprintf ~at:e "Cannot infer type of@\n<<%a>>" (print_prop ()) e ;
        assert false
and infer_facts_bounded cx e =
    let (hyps,_) = deimpl e in
    iter (fun h -> ignore (proc_typing_hyp cx h)) hyps
and proc_typing_hyp cx e = 
    if is_safe_fact e then ignore (type_infer Update_fact cx e Bool) else () ; e
;;


(****************************************************************************)

let rec get_ids cx e : string list =
    let get_idss cx es = fold_left (fun r e -> get_ids cx e @ r) [] es in
    match e.core with
    | Ix n -> [lookup_id cx n]
        (* begin match (nth cx (n - 1)).core with
        | Defn ({core = Operator (h,_)},_,_,_) -> [h.core]
        | _ -> []
        end *)
    | String _ | Opaque _ | Internal _ | Num _ -> 
        []
    | Apply (ex, es) | FcnApp (ex, es) -> 
        get_idss cx (ex :: es)
    | List (_, es) | Tuple es | Product es | SetEnum es -> 
        get_idss cx es
    | Quant (_, bs, ex) | Expr.T.Fcn (bs, ex) | SetOf (ex, bs) -> 
        get_ids (add_bs_ctx bs cx) ex @ get_ids_bs cx bs
    | SetSt (h, dom, ex) ->
        get_ids cx (Expr.T.Fcn ([h, Unknown, Domain dom], ex) @@ e)
    | Except (f, [([Except_apply e1],e2)]) -> 
        get_ids cx f @ get_ids cx e1 @ get_ids cx e2
    | Except (r, exs) ->
        let ops_exps = function Except_apply ea -> [get_ids cx ea] | _ -> [] in
        get_ids cx r @ flatten (map (fun (exps,ex) -> (flatten (flatten (map ops_exps exps))) @ (get_ids cx ex)) exs)
    | Arrow (e1,e2) -> 
        get_idss cx [e1 ; e2]
    | Dot (ex,_) | Parens (ex,_) -> 
        get_ids cx ex
    | Record rs | Rect rs -> 
        let es = map (fun (_,e) -> e) rs in
        get_idss cx es
    | If (c, t, f) -> 
        get_idss cx [c ; t ; f]
    | Case (es, None) ->
        let (es1,es2) = split es in
        get_idss cx (es1 @ es2)
    | Case (es, Some o) ->
        let (es1,es2) = split es in
        get_idss cx (es1 @ es2 @ [o])
    | Sequent seq ->
        get_ids cx (unroll_seq seq)
    | Choose (h, None, ex) -> 
        get_ids (add_bs_ctx [h, Unknown, No_domain] cx) ex
    | Choose (hint, Some dom, ex) -> 
        let bs = [hint, Unknown, Domain dom] in
        get_ids (add_bs_ctx bs cx) ex @ get_ids_bs cx bs
    | Lambda (vs, ex) -> 
        let vs = fold_right (fun (h,s) r -> match s with Shape_expr -> (h, Unknown, No_domain) :: r | Shape_op _ -> r) vs [] in
        get_ids (add_bs_ctx vs cx) ex
    | _ ->
        Util.eprintf ~at:e "function get_ids cannot print@\n%a" (print_prop ()) e ;
        (* [] *) assert false
and get_ids_bs cx bs = 
    let f cx = function
    | (_, _, Domain dom) -> get_ids cx dom
    | _ -> []
    in
    fold_left (fun r b -> f cx b @ r) [] bs
;;

(* let get_typable_ids cx e = 
    get_ids cx e @ flatten (proc_assumptions (fun cx e _ -> get_ids cx e) (preprocess_context cx))
;; *)

(****************************************************************************)


(* type tlatype2 = Var of string | Bool2 | Int2
    | Set of tlatype2
    | Fcn2 of tlatype2 * tlatype2
    (* | Rec of tlatype SMap.t
    | Tup of tlatype list *)

    let rec to_string2 = function
        | Var id     -> sprintf "*_%s" id
        | Bool2      -> "Bool"
        | Int2       -> "Int"
        | Set x      -> sprintf "Set(%s)" (to_string x)
        | Fcn2 (x,y) -> sprintf "(%s -> %s)" (to_string x) (to_string y)
        (* | Rec map   -> sprintf "Rec_<%s>" (typeMap_to_string map)
        | Tup es    -> sprintf "Tuple_[%s]" (String.concat ";" (map (fun t -> (to_string t)) es)) *)
    (* and typeMap_to_string map = 
        String.concat "," (map (fun (f,t) -> sprintf "(%s:%s)" f (to_string t)) (SMap.bindings map)) *)
    ;;

exception Wrong_type ;;

type type_constraint = 
    | Unify tlatype tlatype 
    | IsSet tlatype 
    | IsInt tlatype
    | DomainType tlatype
;;

let rec mgu t1 t2 = 
    let id x = x in
    let rec tsubst v x = function
        | Var w when w = v -> x
        | P e -> P (tsubst v x e)
        | Fcn t1 t2 -> Fcn (tsubst v x t1) (tsubst v x t2)
        | t -> t
    in
    let ( <~ ) x y = function
        | Unify t1 t2 -> Unify (tsubst x y t1) (tsubst x y t2)
        | c -> c
    in
    match t1, t2 with
    | Var x, Var _ -> x <~ t2
    | Int, Int -> id
    | Set x, Set y -> mgu x y
    | Fcn (a,b), Fcn (c,d) -> 
        let s = mgu a c in
        fun x -> (mgu (s b) (s d)) (s x)
    | _ -> raise Wrong_type
;;

let rec solve = function
    | [] -> ()
    | Unify t1 t2 :: cs -> 
        let subst = mgu t1 t2 in
        let cs = map (fun c -> subst c) cs in
        subst :: solve cs
    | IsSet ((P _) :: cs) -> solve cs
    | IsInt (Int :: cs) -> solve cs 
    | _ -> raise Wrong_type
;;

let rec typeinf cx e = 
    let new_type () = "temp" ^ (fresh_name ()) in
    let ( minus ) a v = filter (fun (x,_) -> x <> v) a in
    let ass_freevar a v = fold_left (fun r (x,t) -> if x = v then t :: r else r) [] a in
    let check ts t = if for_all (fun x -> x = t) ts then () else raise Wrong_type in
    match e.core with
    | Ix n ->
        let id = lookup_id cx n in 
        ([(id, Var id)], [], Var id)
    (* | String _ -> ([], Str) *)
    (* | Opaque _ -> ([], [], Var (new_type ())) *)
    | Num _ -> ([], [], Int2)
    | Internal B.TRUE
    | Internal B.FALSE ->
        ([], [], Bool2)
    | FcnApp (f, [ex]) -> 
        let b = Var (new_type ()) in
        let a1,c1,t1 = typeinf cx f in
        let a2,c2,t2 = typeinf cx ex in
        (a1 @ a2, c1 @ c2 @ [Unify t1 (Fcn2 t2 b)], b)
    | Expr.T.Fcn ([v,_,Domain d] as bs, ex) ->
        let tx = Var v.core in
        let a1,c1,td = typeinf cx d in
        let a2,c2,te = typeinf (add_bs_ctx bs cx) ex in
        let c3 = map (fun t -> Unify tx t) (ass_freevar a2 v.core) in
        ((a1 @ a2) minus v.core, c1 @ c2 @ [Unify td (P tx)] @ c3, Fcn2 tx te)
    | Quant (_, ([v, _, Domain d] as bs), ex) -> 
        let tx = Var v.core in
        let a1,c1,td = typeinf cx d in
        let a2,c2,te = typeinf (add_bs_ctx bs cx) ex in
        let c3 = map (fun t -> Unify tx t) (ass_freevar a2 v.core) in
        check [te] Bool ;
        ((a1 @ a2) minus v.core, c1 @ c2 @ [Unify td (P tx)] @ c3, Bool2)
    | Quant (_, ([v, _, No_domain] as bs), ex) -> 
        let tx = Var v.core in
        let a,c,te = typeinf (add_bs_ctx bs cx) ex in
        let c2 = map (fun t -> Unify tx t) (ass_freevar a v.core) in
        check [te] Bool ;
        (a minus v.core, c @ c2, Bool2)
    | Arrow (s,t) -> 
        let a = Var (new_type ()) in
        let b = Var (new_type ()) in
        let a1,c1,t1 = typeinf cx s in
        let a2,c2,t2 = typeinf cx t in
        (a1 @ a2, c1 @ c2 @ [Unify t1 (Set a) ; Unify t2 (Set b)], Set (Fcn2 a b))
    | Apply ({core = Internal op}, [e1 ; e2]) -> 
        let a1,c1,t1 = typeinf cx e1 in
        let a2,c2,t2 = typeinf cx e2 in
        let a = a1 @ a2 in
        let c = c1 @ c2 in
        begin match op with
        | B.Conj | B.Disj | B.Implies | B.Equiv -> 
            check [t1 ; t2] Bool ;
            (a, c @ [Unify t1 Bool2 ; Unify t2 Bool2], Bool2)
        | B.Eq, B.Neq -> 
            (a, c @ [Unify t1 t2], Bool2)
        | B.Mem, B.Notmem -> 
            (a, c @ [Unify (Set t1) t2], Bool2)
        | B.Cup | B.Cap | B.Setminus -> 
            (a, c @ [Unify t1 t2 ; IsSet t1 ; IsSet t2], t1)
        | B.Subseteq -> 
            (a, c @ [Unify t1 t2 ; IsSet t1 ; IsSet t2], Bool2)
        | B.Plus | B.Minus | B.Times | B.Ratio | B.Exp | B.Quotient | B.Remainder ->
            (a, c @ [Unify t1 t2 ; IsInt t1 ; IsInt t2], t1)
        | B.Lt | B.Lteq | B.Gt | B.Gteq ->
            (a, c @ [Unify t1 t2 ; IsInt t1 ; IsInt t2], Bool2)
        | B.Range -> 
            (a, c @ [Unify t1 t2 ; IsInt t1 ; IsInt t2], Set Int2)
        (* | B.Cat ->  *)
        | _ -> 
            raise Not_found
        end
    | Apply ({core = Internal op}, [ex]) -> 
        let a,c,t = typeinf cx ex in
        begin match op with
        | B.Neg -> 
            check [t] Bool ; (a, c, Bool2)
        (* | B.Prime -> 
            (a, c, t) *)
        | B.SUBSET -> 
            (a, c, Set t)
        | B.UNION -> 
            let b = Var (new_type ()) in
            (a, c @ [IsSet t ; Unify t (Set b)], b)
        | B.DOMAIN -> 
            (a, c @ [Unify (DomainType t) b], Set b)
        | B.Uminus -> 
        (* | B.Len ->  *)
        | _ ->   
            raise Not_found
        end
    | Apply (f, es) -> 
        let c,t = typeinf ass cx f in
        let cs,ts = split (map (typeinf ass cx) es) in
        (c @ cs @ )
    (* | List (b,es) ->     *)
    | SetEnum [] -> ([], Set (Var (new_type ())))
    | SetEnum es -> 
        let cs,ts = split (map (typeinf ass cx) es) in
        (concat cs @ [fold_left (fun r t -> ) [] ts], Set (hd ts))
    | Internal B.Nat -> ([], Set Int2)
    | Internal B.Int -> ([], Set Int2)
    | If (c,t,f) -> 
        let a1,c1,tc = typeinf cx c in
        let a2,c2,tt = typeinf cx t in
        let a3,c3,tf = typeinf cx f in
        check [tc] Bool ;
        (a1 @ a2 @ a3, c1 @ c2 @ c3 @ [Unify tt tf], t2)
    (* | SetSt (h, dom, ex) ->
    | SetOf (ex, bs) -> 
    | Case ((p1,e1) :: es, Some other) ->
    | Except (f, [([Except_apply x],y)]) ->
    | Choose (v,dom,ex) ->
    | Dot (ex,_) ->
    | Tuple es -> 
    | Product es -> 
    | Record rs -> 
    | Rect rs -> 
    | Parens (ex,_) ->
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            rev (new_ctx_vars xs) @ cx
        in *)
    | _ -> 
        raise Not_found
;; *)

(****************************************************************************)
    


(*** If, while processing an hypothesis, it raises an exception, 
    then that hyp is postponed, hoping to infer the necessary types from the rest of the hyps. 
    The number of chances left to try is the last element of the tuple. *)
let rec process_hyps cx = function
    | [] -> []
    | ({core = Internal B.TRUE},_) :: hs -> 
        process_hyps cx hs
    | (ex,(0 as chances)) :: hs
    | (ex,chances) :: ([] as hs) -> 
        begin try process_hyps cx hs @ [proc_typing_hyp cx ex]
        with
        | Not_found | Invalid_argument _ | Failure _ ->
        (* with excep -> begin match excep with
            | Untyped_symbol msg 
            | Unification_failed msg
            | Unsupported_type msg -> Util.eprintf "[TypeInfer Error] %s" msg
            | Infer_other msg      -> Util.eprintf "[TypeInfer] %s" msg
            | Unsupported_expression e -> Util.eprintf "[TypeInfer] Unsupported expression"
            | _ -> failwith ("[TypeInfer] unknown exception\n")
            end ; *)
            assert (chances <> 0); []
        end
    | (ex,chances) :: hs -> 
        begin try process_hyps cx hs @ [proc_typing_hyp cx ex]
        with Not_found | Invalid_argument _ | Failure _ ->
          process_hyps cx (hs @ [ex,chances-1])
        end
;;
        
let type_inference cx all =
    let type_inf_aux es : unit =
        (*** Step 1. Assign safe types (ie: Bot, P Bot, Bot->Bot, ...) in the whole PO. *)
        iter (fun e -> try ignore (type_infer Update_safe cx e Bool)
                       with Not_found | Invalid_argument _ | Failure _ -> ())
             es ;
        (*** Step 2. Domain assignment from known facts. *)
        let hyps = filter (fun e -> not (is_conc e)) es in 
        let hyps = map (fun e -> (e,length hyps + 1)) hyps in
        ignore (process_hyps cx hyps) 
    in

    types#reset ;
    type_inf_aux all ;
    type_inf_aux all ;
    Printf.eprintf ">>> Type assignments:\n%s\n" types#sprint_all ;
    
    Printf.eprintf ">>> Unexpanded operators: %s\n\n" 
        (let ops = remove_repeated (flatten (map (get_operators cx) all)) in 
         if ops <> [] then (String.concat ", " ops) else "---") ;
    ()
;;

(** get_type : does not make unnecessary recursions. A \/ B always returns 
    Bool, so it does not evaluate the type of A and B.
    Assumptions:
      - types have already been assigned to terms
      - expression e is already grounded+abstracted *)
let rec get_type cx e : tlatype =    
(* Util.eprintf "\tget_type \t%a" (print_prop ()) (opaque cx e) ; *)
    let is_int e = get_type cx e = Int in
    match e.core with
    | Ix n      -> types#find (lookup_id cx n)
    | Opaque id -> types#find (unprime_id id)
    | Apply ({core = Internal op}, es) ->
        begin match op, es with
        | B.Conj, _ | B.Disj, _ | B.Implies, _ | B.Equiv, _ | B.Neg, _ | B.Eq, _ | B.Mem, _ 
        | B.Neq, _ | B.Notmem, _ | B.Subseteq, _
        | B.Lt, _ | B.Lteq, _ | B.Gt, _ | B.Gteq, _ ->
            Bool
        | B.Plus, _ | B.Minus, _ | B.Times, _ | B.Ratio, _
        | B.Quotient, _ | B.Remainder, _ | B.Exp, _ | B.Uminus, _ ->
            if for_all is_int es then Int else Bot
        | B.Range, _ -> 
            if for_all is_int es then P Int else P Bot
        | B.Prime, [ex] -> 
            get_type cx ex
        | B.DOMAIN, [f] ->
            begin match get_type cx f with
            | Fcn (a,_) -> P a
            | _ -> P Bot
            end            
        | B.Cup, [e1;e2] | B.Cap, [e1;e2] | B.Setminus, [e1;e2] ->
            let t1 = get_type cx e1 in
            let t2 = get_type cx e2 in
            if TLAtype.eq t1 t2 then t1 else P Bot
        | B.SUBSET, [ex] ->
            P (get_type cx ex)
        | B.UNION, [ex] ->
            TLAtype.base (get_type cx ex)
        | B.Len, _ -> Int
        | B.Head, ex :: _ -> get_type cx ex
        | B.Tail, _ :: es -> Tup (map (get_type cx) es)
        | B.Seq, _ -> P (Tup [])
        | B.BSeq, _ -> Tup []
        | B.Cat, _ -> Tup []
        | B.Append, _ -> Tup []
        | B.SubSeq, _ -> Tup []
        | B.SelectSeq, _ -> Tup []
        
        | B.Unprimable, [ex] -> 
            get_type cx ex
        | _ -> 
            Util.bug "[SMT] get_type: not supported Apply Internal"
        end
    | Apply (op, es) -> 
        TLAtype.apply_fcn (get_type cx op) (map (get_type cx) es)
    | FcnApp (f, [{core = Num (n,"")}]) ->
        begin match get_type cx f with
        | Tup ts ->
            let t =
              try nth ts ((int_of_string n) - 1)
              with Invalid_argument _ | Failure _ -> Bot
            in t
        | _ -> TLAtype.apply_fcn (get_type cx f) [Int]
        end
    | Internal B.TRUE
    | Internal B.FALSE   -> Bool
    | Internal B.Infinity -> Int
    | List _ 
    | Quant _            -> Bool
    | Internal B.BOOLEAN -> P Bool
    | Internal B.STRING  -> P Str
    | SetEnum []         -> P Bot
    | String _           -> Str
    | Num _              -> Int
    | Internal B.Nat
    | Internal B.Int     -> P Int
    | FcnApp (f, es) -> TLAtype.apply_fcn (get_type cx f) (map (get_type cx) es)
    | Dot (r, h)     -> TLAtype.get_fieldtyp h (get_type cx r)
    | Tuple es       -> Tup (map (get_type cx) es)
    | Record rs      -> Rec (list_to_map (map (fun (h,e) -> (h, get_type cx e)) rs))
    | If (_, t, f) -> 
        let t = (get_type cx t) in
        if TLAtype.eq t (get_type cx f) then t else Bot
    | Sequent _ -> Bool
    | _ -> Bot
;;

let get_all_types_fact cx e = 
    let proc_fact cx e = 
        let ia = if is_safe_fact e then Update_fact else Update_safe in
        try (ignore (type_infer ia cx e Bool))
        with Not_found | Invalid_argument _ | Failure _ -> ()
    in
    let get_facts e = 
        match e.core with
        | Apply ({core = Internal B.Implies}, [hs ; c]) -> 
            let (hs',_) = deimpl c in
            hs :: hs'
        (* | Apply ({core = Internal B.Conj}, es) 
        | List (And, es) -> 
            es *)
        (** TODO: sequents *)
        | _ -> []
    in
    let facts = flatten (map deconj (get_facts e)) in
    iter (proc_fact cx) facts
;;

(****************************************************************************)

let (<<<<) e t = 
(* Util.eprintf "\t %s ::%s <<<< %s" e.core (typ_to_str e) (match t with Some t -> TLAtype.to_string t | None -> "____") ; *)
    let e = remove_type e in
    let e = assign e boundvar () in
    assign e expr_type t ;;

let tfind3 e id = 
(* Printf.eprintf ">>> Type assignments:\n%s\n" types#sprint_all ; *)
    let t = if types#exists id then Some (types#find id) else typ e in
(* Printf.eprintf ".....tfind3 id = %s : %s\n" id (match t with Some t -> TLAtype.to_string t | None -> "____") ; *)
    t
    ;;

(** To each sub-expression e, it attaches e's type as a property. 
    A problem with attached types as properties is that they will remain after substitution.
    Note 1: Don't paint inner bounded variables because they can be 
        substituted by other expressions with different types.
*)
let rec paint_types cx e =    
(* Util.eprintf "Paint: %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
    let mk x = { e with core = x } in
    let apply1 op ex t = Apply (Internal op |> mk <<< t, [ex]) |> mk <<< t in
    let apply op es t = Apply (Internal op |> mk <<< t, es) |> mk <<< t in
    let is_int e = typ e = Some Int in
    let paint e = paint_types cx e in
    let ps es = map paint es in
    let typ_eq e1 e2 = 
        match typ e1, typ e2 with
        | Some t1, Some t2 -> TLAtype.eq t1 t2
        | _ -> false
    in
    let typbase e = TLAtype.base (typbot e) in
    match e.core with
    | Ix n -> 
        (** Don't! update type in context *)
        e <<< tfind3 e (lookup_id cx n)
    | Opaque id -> 
        e <<< tfind3 e (unprime_id id)
    | Quant (q, bs, ex) -> 
(* Util.eprintf "Paint %a" (print_prop ()) (opaque cx e) ; *)
        let bs = paint_bs cx bs in
        get_all_types_fact (add_bs_ctx bs cx) ex ;                (** assign types to quantified variables *)
        (** FIX: update only vars in bs *)
        iter (fun (v,_,_) -> types#update ((* quant_id *) v.core) (typbot v)) bs ;
        let bs = paint_bs cx bs in
        let ex = paint_types (add_bs_ctx bs cx) ex in
        iter (fun (v,_,_) -> types#remove ((* quant_id *) v.core)) bs ;      (** remove bounded variables types *)
        Quant (q, bs, ex) |> mk <<< Some Bool
    | Apply ({core = Internal op}, es) ->
        begin match op, es with
        | B.Conj, _ | B.Disj, _ 
        | B.Implies, _
        | B.Equiv, _ | B.Neg, _ 
        | B.Eq, _ | B.Neq, _ | B.Subseteq, _
        | B.Mem, _ | B.Notmem, _
        | B.Lt, _ | B.Lteq, _ | B.Gt, _ | B.Gteq, _ ->
            apply op (ps es) (Some Bool)
        | B.Plus, _ | B.Minus, _ | B.Times, _ | B.Ratio, _
        | B.Quotient, _ | B.Remainder, _ | B.Exp, _ | B.Uminus, _ ->
            let es = ps es in
            apply op es (Some (if for_all is_int es then Int else Bot))
        | B.Range, _ -> 
            let es = ps es in
            apply op es (Some (if for_all is_int es then P Int else P Bot))
        | B.Prime, [ex] -> 
            let ex = paint ex in
            apply1 op ex (typ ex)
        | B.DOMAIN, [f] ->
            let f = paint f in
            let t = match typ f with
            | Some (Fcn (a,_)) -> P a
            | _ -> P Bot
            in
            apply1 op f (Some t)
        | B.Cup, [e1;e2] | B.Cap, [e1;e2] | B.Setminus, [e1;e2] ->
            let e1 = paint e1 in
            let e2 = paint e2 in
            apply op [e1;e2] (Some (if typ_eq e1 e2 then typbot e1 else P Bot))
        | B.SUBSET, [ex] ->
            let ex = paint ex in
            apply1 op ex (Some (P (typbot ex)))
        | B.UNION, [ex] ->
            let ex = paint ex in
            apply1 op ex (Some (typbase ex))
        | B.Len, [ex] -> apply1 op (paint ex) (Some Int)
        | B.Head, ex :: es -> 
            let ex = paint ex in
            let es = ps es in
            apply op (ex :: es) (typ ex)
        | B.Tail, ex :: es -> 
            let ex = paint ex in
            let es = ps es in
            apply op (ex :: es) (Some (Tup (map typbot es)))
        | B.Seq, [ex] -> apply1 op (paint ex) (Some (P (Tup [])))
        | B.BSeq, _ -> apply op (ps es) (Some (Tup []))
        | B.Cat, _ -> apply op (ps es) (Some (Tup []))
        | B.Append, _ -> apply op (ps es) (Some (Tup []))
        | B.SubSeq, _ -> apply op (ps es) (Some (Tup []))
        | B.SelectSeq, _ -> apply op (ps es) (Some (Tup []))

        | B.OneArg,    [e ; f] -> apply op (ps es) (Some Bot)
        | B.Extend,    [e ; f] -> apply op (ps es) (Some Bot)
        | B.Print,     [e ; v] -> apply op (ps es) (Some Bot)
        | B.PrintT,    [e]     -> apply op (ps es) (Some Bot)
        | B.Assert,    [e ; o] -> apply op (ps es) (Some Bot)
        | B.JavaTime,  []      -> apply op (ps es) (Some Bot)
        | B.TLCGet,    [i]     -> apply op (ps es) (Some Bot)
        | B.TLCSet,    [i ; v] -> apply op (ps es) (Some Bot)
        | B.Permutations, [s]  -> apply op (ps es) (Some Bot)
        | B.SortSeq,   [s ; o] -> apply op (ps es) (Some Bot)
        | B.RandomElement, [s] -> apply op (ps es) (Some Bot)
        | B.Any,       []      -> apply op (ps es) (Some Bot)
        | B.ToString,  [v]     -> apply op (ps es) (Some Bot)
        | B.Unprimable, [ex] -> apply1 op (paint ex) (typ ex)
        | _ -> 
            Util.bug "[SMT] paint_types: not supported Apply Internal"
        end
    | Apply ({core = Opaque ("isAFcn"|"isASeq"|"isFldOf")} as op, es) -> 
        let es = ps es in
        Apply (op, es) |> mk <<< Some Bool
    | Apply (op, es) -> 
        let es = ps es in
        let op = paint op in
        let t = TLAtype.apply_fcn (typbot op) (map typbot es) in
        (* let top = fold_left (fun r t -> Fcn(t,r)) t (map (fun e -> typbot e) es) in *)
        Apply (op (* <<< Some top *), es) |> mk <<< Some t
    | FcnApp (f, es) -> 
        let es = ps es in
        let f = paint f in
        let t = TLAtype.apply_fcn (typbot f) (map typbot es) in
        FcnApp (f, es) |> mk <<< Some t
    | List (b, es) -> List (b, ps es) |> mk <<< Some Bool
    | Internal B.TRUE
    | Internal B.FALSE   -> e <<< Some Bool
    | Internal B.BOOLEAN -> e <<< Some (P Bool)
    | Internal B.STRING  -> e <<< Some (P Str)
    | String _           -> e <<< Some Str
    | Num _              -> e <<< Some Int
    | Internal B.Nat
    | Internal B.Int     -> e <<< Some (P Int)
    | Internal B.Infinity -> e <<< Some Int
    | Dot (r, h)     -> 
        let r = paint r in
        Dot (r, h) |> mk <<< Some (TLAtype.get_fieldtyp h (typbot r))
    | Tuple es -> 
        let es = ps es in
        Tuple es |> mk <<< Some (Tup (map typbot es))
    | Record rs -> 
        let rs = map (fun (h,e) -> h, paint e) rs in
        Record rs |> mk <<< Some (Rec (list_to_map (map (fun (h,e) -> (h, typbot e)) rs)))
    | SetOf (ex, bs) ->
        (* let typ_bs bs = 
            let rec aux = function
            | (h,_,_) :: bs -> typbot h :: aux bs
            | [] -> []
            in
            match aux bs with [t] -> t | ts -> Tup ts
        in *)
        let bs = paint_bs cx bs in
        let ex = paint_types (add_bs_ctx bs cx) ex in
        SetOf (ex, bs) |> mk <<< Some (P (typbot ex))
    | SetSt (h, dom, ex) ->
        let bs = [h, Unknown, Domain dom] in
        let bs = paint_bs cx bs in
        let ex = paint_types (add_bs_ctx bs cx) ex in
        let h,dom = match bs with [h,_,Domain d] -> h,d | _ -> assert false in
        SetSt (h, dom, ex) |> mk <<< typ dom
    | SetEnum [] -> e <<< Some (P Bot)
    | SetEnum es -> 
        let es = ps es in
        SetEnum es |> mk <<< Some (P (typbot (hd es)))
    | Choose (h, d, ex) ->
        let (d,dom) = match d with 
        | Some d -> let d = paint d in (Some d, Domain d)
        | None -> (None, No_domain) 
        in
        let bs = paint_bs cx [h, Unknown, dom] in
        let ex = paint_types (add_bs_ctx bs cx) ex in
        let h,_,_ = hd bs in
        (* Choose (h <<< Some (TLAtype.base t), d, ex) |> mk *)
        Choose (h, d, ex) |> mk <<< typ h
    | Arrow (e1,e2) -> 
        let e1 = paint e1 in
        let e2 = paint e2 in
        Arrow (e1,e2) |> mk <<< Some (P (Fcn(typbase e1,typbase e2)))
    | Expr.T.Fcn (bs, ex) ->
        let bs = paint_bs cx bs in
        let ex = paint_types (add_bs_ctx bs cx) ex in
        let tbs = map (fun (h,_,_) -> typbot h) bs in
        Expr.T.Fcn (bs, ex) |> mk <<< Some (fold_left (fun r t -> Fcn(t,r)) (typbot ex) tbs)
    | Except (f, exs) -> 
        let f = paint f in
        let paint_ex = function Except_apply ea -> Except_apply (paint ea) | Except_dot h -> Except_dot h in
        let exs = map (fun (es,ex) -> map paint_ex es, paint ex) exs in
        Except (f, exs) |> mk <<< typ f
    | Rect rs ->
        let rs = map (fun (h,e) -> h,paint e) rs in
        Rect rs |> mk <<< Some (P (Rec (list_to_map (map (fun (h,e) -> (h, typbase e)) rs))))
    | Product es -> 
        let es = ps es in
        Product es |> mk <<< Some (P (Tup (map (fun e -> typbase e) es)))
    | If (c, t, f) -> 
        let c = paint c in
        let t = paint t in
        let f = paint f in
        If (c, t, f) |> mk <<< Some (if typ_eq t f then typbot t else Bot)
    | Case (es, o) ->
        let es = map (fun (p,e) -> paint p, paint e) es in
        let o = match o with Some o -> Some (paint o) | None -> None in
        Case (es, o) |> mk
    | Sequent seq -> paint (unroll_seq seq)
    | Parens (ex,_) -> paint ex
    | Lambda (xs,ex) ->
        let add_to_ctx cx xs = 
            let rec new_ctx_vars = function
                | ({core = h},_) :: xs -> ((Flex ((* quant_id *) h |> mk)) |> mk) :: new_ctx_vars xs
                | [] -> []
            in  
            rev (new_ctx_vars xs) @ cx
        in
        Lambda (xs, paint_types (add_to_ctx cx xs) ex) |> mk
    | _ -> 
        Util.bug "[SMT] paint_types: cannot process expression"
and paint_bs cx bs = 
    let f = function
    | (v, k, Domain d) -> 
        let id = v.core in
        let d = paint_types cx d in 
        let t = match tfind3 v id, typ d with
        | Some t1, Some t2 -> Some (TLAtype.max t1 (TLAtype.base t2))
        | Some t1, None -> Some t1
        | None, Some t2 -> Some (TLAtype.base t2)
        | _ -> None
        in
        (v <<<< t, k, Domain d)
    | (v, k, d) -> 
        let t = tfind3 v ((* quant_id *) v.core) in
        (v <<<< t, k, d)
    in
    map f (unditto bs)
;;

let indent = ref 0 ;;

(* let rec typetree cx e =    
(* Util.eprintf "Paint %a" (print_prop ()) (opaque cx e) ; *)
    let styp e = match typ e with Some t -> TLAtype.to_string t | None -> "____" in
    let ps es = iter (typetree cx) es in
    let ind = String.map (fun _ -> Char.chr(32)) (String.create (!indent * 2)) in
    let inc () = indent := !indent + 1 in
    let dec () = indent := !indent - 1 in
    let typetree_bs cx bs = 
        let f = function
        | (v, k, Domain d) -> Util.eprintf "%s|  %s : %s  \\in  %a : %s" ind v.core (styp v) (print_prop ()) (opaque cx d) (styp d) ;
        | (v, _, _)        -> Util.eprintf "%s|  %s : %s" ind v.core (styp v)
        in
        iter f bs
    in
    match e.core with
    | Ix n      -> 
        (* Printf.eprintf ">>> Type assignments:\n%s\n" types#sprint_all ; *)
        Util.eprintf "%s%a  : %s -- id=%s : %s  (ix)" ind (print_prop ()) (opaque cx e) (styp e) (lookup_id cx n) (TLAtype.to_string (types#find (lookup_id cx n)))
    | Opaque id -> Util.eprintf "%s%a  : %s : %s  (opq)" ind (print_prop ()) (opaque cx e) (styp e) (TLAtype.to_string (types#find (unprime_id id)))
    | _ -> 
        Util.eprintf "%s%a  : %s" ind (print_prop ()) (opaque cx e) (styp e) ;
        begin match e.core with
        | Quant (q, bs, ex)          -> 
            inc () ; 
            typetree_bs cx bs ;
            iter (fun (v,_,_) -> types#update ((* quant_id *) v.core) (typbot v)) bs ;
            typetree (add_bs_ctx bs cx) ex ;
            iter (fun (v,_,_) -> types#remove ((* quant_id *) v.core)) bs ;
            dec ()
        | Apply (f, es) 
        | FcnApp (f, es)             -> inc () ; ps (f :: es) ; dec ()
        | List (_, es) | Tuple es 
        | Product es | SetEnum es    -> inc () ; ps es ; dec ()
        | Arrow (e1,e2)              -> inc () ; ps [e1;e2] ; dec ()
        | Dot (ex,_) | Parens (ex,_) -> inc () ; ps [ex] ; dec ()
        | Record rs | Rect rs        -> inc () ; ps (map (fun (_,e) -> e) rs) ; dec ()
        | If (c, t, f)               -> inc () ; ps [c;t;f] ; dec ()
        | Case (es, o) ->
            let (es1,es2) = split es in
            inc () ; ps (es1 @ es2 @ (match o with Some o -> [o] | _ -> [])) ; dec ()
        | Expr.T.Fcn (bs, ex) ->
            inc () ; typetree_bs cx bs ; typetree (add_bs_ctx bs cx) ex ; dec ()
        | Except (r, exs) ->
            let tree_exps = function Except_apply ea -> [ea] | _ -> [] in
            ps (r :: (flatten (map (fun (exps,ex) -> flatten (map tree_exps exps) @ [ex]) exs)))
        | SetSt (h, dom, ex) ->
            let bs = [h, Unknown, Domain dom] in
            inc () ; typetree_bs cx bs ; typetree (add_bs_ctx bs cx) ex ; dec ()
        | SetOf (ex, bs) ->
            inc () ; typetree (add_bs_ctx bs cx) ex ; typetree_bs cx bs ; dec ()
        | Choose (h, None, ex) -> 
            inc () ; typetree (add_bs_ctx [h, Unknown, No_domain] cx) ex ; dec ()
        | Choose (h, Some dom, ex) -> 
            let bs = [h, Unknown, Domain dom] in
            inc () ; typetree_bs cx bs ; typetree (add_bs_ctx bs cx) ex ; dec ()
        | Sequent seq ->
            typetree cx (unroll_seq seq)
        | Lambda (vs, ex) -> 
            let vs = fold_right (fun (h,s) r -> match s with Shape_expr -> (h, Unknown, No_domain) :: r | Shape_op _ -> r) vs [] in
            typetree (add_bs_ctx vs cx) ex
        | _ -> 
            ()
        end
;; *)

(****************************************************************************)

let ( <<< ) (e:'a Property.wrapped) prop : 'a Property.wrapped = 
(* Util.eprintf "%a <<< %s" (print_prop ()) e prop.rep ; *)
    assign e prop () ;;

let rec boolify e =
(* Util.eprintf "## boolify: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  begin match e.core with
  | Ix _ | Opaque _ -> 
      (* Printf.eprintf "-- boolified!\n"; *)
      e <<< applyu2bool
  | Apply ({core = Ix _ | Opaque _} as f, es) ->    (** FIX primes *)
      (* Printf.eprintf "-- boolified!\n"; *)
      Apply (nboo f, map nboo es) |> mk <<< applyu2bool
  | FcnApp (f,es) -> 
      (* Printf.eprintf "-- boolified!\n"; *)
      FcnApp (nboo f, map nboo es) |> mk <<< applyu2bool
  | Dot (r, h) -> 
      (* Printf.eprintf "-- boolified!\n"; *)
      Dot (nboo r, h) |> mk <<< applyu2bool
  | Choose (h, d, ex) -> 
      (* Printf.eprintf "-- boolified!\n"; *)
      Choose (h, Option.map nboo d, boolify ex) |> mk <<< applyu2bool
  | Except (f, exs) -> 
      (* Printf.eprintf "-- boolified!\n"; *)
      let boo_ex = function Except_apply ea -> Except_apply (nboo ea) | Except_dot h -> Except_dot h in
      let exs = map (fun (es,ex) -> map boo_ex es, boolify ex) exs in
      Except (nboo f, exs) |> mk <<< applyu2bool
  | Apply ({core = Internal o} as op, es) -> 
      begin match o with
      | B.Conj | B.Disj | B.Implies | B.Equiv | B.Neg ->
          Apply (op, map boolify es) |> mk
      | B.Mem | B.Notmem | B.Eq | B.Neq ->
          Apply (op, map nboo es) |> mk
      | B.Subseteq | B.Lteq | B.Lt | B.Gteq | B.Gt -> 
          Apply (op, map nboo es) |> mk
      | _ -> 
          failwith "Trying to boolify a non Boolean operator."
      end
  | List (q, es) -> 
      List (q, map boolify es) |> mk
  | Quant (q, bs, ex) -> 
      Quant (q, nboobs bs, boolify ex) |> mk
  | Internal B.TRUE | Internal B.FALSE -> e

  | If (c, t, f) -> If (boolify c, boolify t, boolify f) |> mk
  | Case (es, o) ->
      let es = map (fun (p,e) -> boolify p, boolify e) es in
      Case (es, Option.map boolify o) |> mk
  | Lambda (xs,ex) -> Lambda (xs, boolify ex) |> mk
  | Sequent seq -> boolify (unroll_seq seq)
  | Parens (ex,_) -> boolify ex
  (* | Apply (op, es) -> Apply (nboo op, map nboo es) |> mk *)
  | _ -> 
     failwith "Trying to boolify a non Boolean operator."
  end
and nboo e =
(* Util.eprintf "## not-a-boolean: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  begin match e.core with
  | Ix _ | Opaque _ -> e
  | FcnApp (f, es) -> FcnApp (nboo f, map nboo es) |> mk
  | Dot (r, h) -> Dot (nboo r, h) |> mk
  | Apply ({core = Internal o} as op, es) -> 
      begin match o with
      | B.Conj | B.Disj | B.Implies | B.Equiv | B.Neg 
      | B.Mem | B.Notmem | B.Eq | B.Neq
      | B.Subseteq | B.Lteq | B.Lt | B.Gteq | B.Gt -> 
          (* failwith "not expected Boolean" *)
          boolify e
      | B.Range -> 
          Apply (op, map nboo es) |> mk
      | _ -> 
          Apply (nboo op, map nboo es) |> mk
      end
  | Apply (op, es) -> Apply (nboo op, map nboo es) |> mk
  | Choose (h, d, ex) -> Choose (h, Option.map nboo d, boolify ex) |> mk
  | Tuple es -> Tuple (map nboo es) |> mk
  | Record rs -> Record (map (fun (h,e) -> h, nboo e) rs) |> mk
  | SetOf (ex, bs) -> SetOf (nboo ex, nboobs bs) |> mk
  | SetSt (h, dom, ex) -> SetSt (h, nboo dom, boolify ex) |> mk
  | SetEnum es -> SetEnum (map nboo es) |> mk
  | Arrow (e1,e2) -> Arrow (nboo e1, nboo e2) |> mk
  | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (nboobs bs, nboo ex) |> mk
  | Except (f, exs) -> 
      let boo_ex = function Except_apply ea -> Except_apply (nboo ea) | Except_dot h -> Except_dot h in
      let exs = map (fun (es,ex) -> map boo_ex es, nboo ex) exs in
      Except (nboo f, exs) |> mk
  | Rect rs -> Rect (map (fun (h,e) -> h, nboo e) rs) |> mk
  | Product es -> Product (map nboo es) |> mk
  | If (c, t, f) -> If (boolify c, nboo t, nboo f) |> mk
  | Case (es, o) ->
      let es = map (fun (p,e) -> boolify p, nboo e) es in
      Case (es, Option.map nboo o) |> mk
  | Lambda (xs,ex) -> Lambda (xs, boolify ex) |> mk
  | Parens (ex,_) -> nboo ex
  | Internal B.TRUE | Internal B.FALSE -> e
  | Internal B.Int | Internal B.Nat | Internal B.Real -> e
  | Internal B.Len | Internal B.Seq | Internal B.Append | Internal B.Tail | Internal B.Cat -> e

  | List (q, es) -> 
      List (q, map boolify es) |> mk
  | Quant (q, bs, ex) -> 
      Quant (q, nboobs bs, boolify ex) |> mk
  | _ -> 
     (* failwith "not expected Boolean" *)
     e
  end
and nboobs bs = 
  map 
    begin function
    | (v, k, Domain d) -> (v, k, Domain (nboo d))
    | b -> b
    end 
  (unditto bs)
