(*
 * backend/smt/ground.ml --- Normalize to basic expressions.
 *
 * Author: Hernán Vanzetto <hernan.vanzetto@inria.fr>
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

open Typesystem
open Smtcommons
open Typeinfer

module B = Builtin ;;

let is_set e = 
  match e.core with
  | Apply ({core = Internal B.Cup | Internal B.Cap | Internal B.Setminus
                 (* | Internal B.Range *)
                 | Internal B.SUBSET | Internal B.UNION}, _)
                 | SetOf _ | SetSt _ | SetEnum _ | Rect _ | Product _ 
                 | Arrow _
                 | Internal B.Nat | Internal B.Seq
      -> true
  | _ -> false
;;

let is_Bool e = typbot e = Bool ;;    
let is_Int e = typbot e = Int ;;    

let rec choose k l =
  if k = 0 then [ [] ]
  else
    let len = length l in
    if len < k then []
    else if k = len then [ l ]
         else
         match l with
         h :: t ->
            let starting_with_h =
                (map (fun sublist -> h :: sublist) (choose (pred k) t))
            in
            let not_starting_with_h = choose k t in
            starting_with_h @ not_starting_with_h
         | [] -> assert false
;;

let all_perms xs = flatten (mapi (fun i _ -> choose i xs) xs) @ [xs] ;;

(****************************************************************************)

(* let flatten_conj e = 
    let rec collect_conj e = match e.core with
    | Apply ({core = Internal B.Conj}, [e1 ; e2]) -> 
        collect_conj e1 @ collect_conj e2
    | List (And, es) -> 
        flatten (map collect_conj es)
    | _ -> [e]
    in
    match e.core with
    | List (And, _) | Apply ({core = Internal B.Conj}, _) -> 
        begin match filter_true (collect_conj e) with
        | [] -> Internal B.TRUE @@ e
        | ex :: [] -> if is_conc e then assign ex isconc () else ex
        | es -> if exists (fun e -> 
                    match e.core with Internal B.FALSE -> true | _ -> false) es 
                    then Internal B.FALSE @@ e else (List (And, es) @@ e)
        end
    | _ -> e
;;

let flatten_disj e = 
    let rec collect_disj e = match e.core with
    | Apply ({core = Internal B.Disj}, [e1 ; e2]) -> 
        collect_disj e1 @ collect_disj e2
    | List (Or, es) -> 
        flatten (map collect_disj es)
    | _ -> [e]
    in
    match e.core with
    | List (Or, _) | Apply ({core = Internal B.Disj}, _) -> 
        begin match filter_false (collect_disj e) with
        | [] -> Internal B.FALSE @@ e
        | ex :: [] -> if is_conc e then assign ex isconc () else ex
        | es -> if exists (fun e -> 
                    match e.core with Internal B.TRUE -> true | _ -> false) es 
                    then Internal B.TRUE @@ e else (List (Or, es) @@ e)
        end
    | _ -> e
;; *)

let str_is_int x =
  try ignore (int_of_string x); true with Invalid_argument _ -> false
;;

(** Simplify trivialities, flatten conj/disjunctions *)
let rec gr0 e = 
(* Util.eprintf "Simplify %a : %s" (print_prop ()) e (typ_to_str e) ; *)
    let mk x = { e with core = x } in    
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    let build ex = match ex.core with a -> a |> mk in    (** mantains e's original properties, especially the isconc property *)
    let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
    (* let apply1 op ex = Apply (Internal op |> mk, [ex]) |> mk in *)
    let tla_true  = Internal B.TRUE |> mc <<< Some Bool in
    let tla_false = Internal B.FALSE |> mc <<< Some Bool in
    let lAnd es = flatten_conj (List (And, es) |> mk) in
    let lOr es = flatten_disj (List (Or, es) |> mk) in
    let apply1b op ex    = Apply (Internal op |> mc <<< Some Bool, [ex]) |> mc <<< Some Bool in
    let apply2b op e1 e2 = Apply (Internal op |> mc <<< Some Bool, [e1 ; e2]) |> mc  <<< Some Bool in
    let eq x y      = apply2b B.Eq x y in
    let neg x       = apply1b B.Neg x in
    let str_is_nat x =
      try int_of_string x >= 0 with Invalid_argument _ -> false
    in
    let mk_num n = Num (string_of_int n,"") |> mc <<< Some Int in
    let rec range2set a b = if a <= b then (Num (string_of_int a,"") |> mc <<< Some Int) :: range2set (a+1) b else [] in
    let setminus x y = Apply (Internal B.Setminus |> mc, [x ; y]) |> mk in
    let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in
    let zero = Num ("0","") |> mc <<< Some Int in
    match e.core with
    | List (_, [e]) -> gr0 (build e)
    | List (And, es) -> lAnd (map gr0 es)
    | List (Or, es) -> lOr (map gr0 es)
    | Apply ({core = Internal op}, [x ; y]) -> 
        let x = gr0 x in
        let y = gr0 y in
        begin match op, x.core, y.core with
        | B.Implies, Internal B.FALSE, _ -> tla_true
        | B.Implies, Internal B.TRUE, _  -> build y
        | B.Implies, _, Internal B.TRUE  -> tla_true
        (* | B.Implies, _, Internal B.FALSE -> apply1 B.Neg x *)
        | B.Implies, _, _ -> apply B.Implies x y
        | B.Conj, _, _ -> lAnd [x ; y]
        | B.Disj, _, _ -> lOr [x ; y]
        | B.Mem, Internal (B.TRUE | B.FALSE), Internal B.BOOLEAN -> tla_true
        | B.Cup, _, SetEnum [] -> x
        | B.Cup, SetEnum [], _ -> y
        | B.Cup, SetEnum es, SetEnum fs -> SetEnum (remove_repeated (es @ fs)) |> mk
        | B.Cap, _, SetEnum [] -> y
        | B.Cap, SetEnum [], _ -> x
        | B.Cap, SetEnum es, SetEnum fs -> 
            SetEnum (fold_left (fun r e -> if exists (Expr.Eq.expr e) fs then e :: r else r) [] es) |> mk
        | B.Setminus, _, SetEnum [] -> x
        | B.Setminus, SetEnum [], _ -> x
        | B.Setminus, SetEnum a, SetEnum b -> 
            let a_cap_b = fold_left (fun r e -> if exists (Expr.Eq.expr e) b then e :: r else r) [] a in
            let a = fold_left (fun r e -> if exists (Expr.Eq.expr e) a_cap_b then r else e :: r) [] a in
            let b = fold_left (fun r e -> if exists (Expr.Eq.expr e) a_cap_b then r else e :: r) [] b in
            (if b = [] then SetEnum a |> mk else setminus (SetEnum a |> mk) (SetEnum b |> mk))
        | B.Setminus, Apply ({core = Internal B.Setminus}, [({core = SetEnum _} as x) ; s]), SetEnum _ -> 
            setminus (gr0 (setminus x y)) s
        | B.Mem, Num (m,""), Internal B.Int when str_is_int m -> tla_true
        | B.Mem, Num (m,""), Internal B.Nat when str_is_nat m -> tla_true
        | (B.Eq | B.Equiv), _, _ when Expr.Eq.expr x y -> tla_true
        | (B.Eq | B.Equiv), _, Internal B.TRUE  when is_Bool x -> build x
        | (B.Eq | B.Equiv), Internal B.TRUE, _  when is_Bool y -> build y
        | (B.Eq | B.Equiv), _, Internal B.FALSE when is_Bool x -> gr0 (neg x)
        | (B.Eq | B.Equiv), Internal B.FALSE, _ when is_Bool y -> gr0 (neg y)
        | B.Eq, Num (n,""), Num (m,"") -> if n = m then tla_true else tla_false 
        | B.Eq, String s1, String s2 -> if s1 = s2 then tla_true else tla_false
        | B.Eq, Tuple t1, Tuple t2 (* when length t1 = length t2 *) -> 
            (* let l = try combine t1 t2 with Invalid_argument _ -> [tla_true,tla_false] in *)
            (* let l = combine t1 t2 in
            lAnd (map (fun (x,y) -> eq x y) l) *)
            begin try lAnd (map (fun (x,y) -> eq x y) (combine t1 t2))
            with Invalid_argument _ -> tla_false
            end
        (* | B.Eq, _, (Ix _ | Apply ({core = Internal B.Prime}, [{core = Ix _}])) 
            when (match x.core with Ix _ | Apply ({core = Internal B.Prime}, [{core = Ix _}]) -> false | _ -> true) -> eq y x *)

        (** Trivial arithmetic rules, no context needed *)
        | B.Plus,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) + (int_of_string y))
        | B.Minus,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) - (int_of_string y))
        | B.Times,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) * (int_of_string y))
        | B.Quotient,  Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 -> 
                                                                                   mk_num ((int_of_string x) / (int_of_string y)) (* integer division *)
        | B.Remainder, Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 -> 
                                                                                   mk_num ((int_of_string x) mod (int_of_string y))
        | B.Ratio,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y <> 0 ->
                                                                                   Num (string_of_float' ((float_of_string x) /. (float_of_string y)),"") |> mk
        | B.Exp,       Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> Num (string_of_float' ((float_of_string x) ** (float_of_string y)),"") |> mk
        | B.Lt,        Num (x,""), Num (y,"") when str_is_int x && str_is_int y
        -> if (int_of_string x) <  (int_of_string y)
           then tla_true else tla_false
        | B.Lteq,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y
        -> if (int_of_string x) <= (int_of_string y)
           then tla_true else tla_false
        | B.Gt,        Num (x,""), Num (y,"") when str_is_int x && str_is_int y
        -> if (int_of_string y) <  (int_of_string x)
           then tla_true else tla_false
        | B.Gteq,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y
        -> if (int_of_string y) <= (int_of_string x)
           then tla_true else tla_false

        (** Repeated in gr_arith ; for Fof use *)
        | (B.Plus | B.Minus), _, Num ("0","") when is_Int x -> build x
        | B.Plus, Num ("0",""), _ when is_Int y -> build y
        | B.Minus, Num ("0",""), _ when is_Int y -> Apply (Internal B.Uminus |> mc, [y]) |> mk
        | B.Minus, _, _ when is_Int x && is_Int y && Expr.Eq.expr x y -> zero
        | B.Lteq, _, _  when is_Int x && is_Int y && Expr.Eq.expr x y -> tla_true
        | B.Gteq, _, _  when is_Int x && is_Int y && Expr.Eq.expr x y -> tla_true

        | B.Subseteq, _, _  when Expr.Eq.expr x y -> tla_true
        | B.Range, Num (a,""), Num (b,"") -> gr0 (SetEnum (range2set (int_of_string a) (int_of_string b)) |> mk)
        | B.Range, _, _ when Expr.Eq.expr x y -> SetEnum [x] |> mk
        | B.Gteq, _, _ -> apply B.Lteq y x
        | B.Gt, _, _ -> apply B.Lt y x
        | B.Cat, _, Tuple []    -> gr0 x
        | B.Cat, Tuple [], _    -> gr0 y
        | B.Append, Tuple [], _ -> gr0 (Tuple [y] |> mk)
        | _ -> e
        end
    | Apply ({core = Internal op} as o, [ex]) -> 
        let ex = gr0 ex in
        begin match op, ex.core with
        | B.Neg, Internal B.TRUE  -> tla_false
        | B.Neg, Internal B.FALSE -> tla_true
        | B.Neg, Apply ({core = Internal B.Neg}, [x]) when is_Bool x -> build x
        | B.Uminus, Num (n,"") -> Num ("-"^n,"") @@ ex
        | B.Tail, Tuple [] -> Tuple [] |> mk
        (* | B.SUBSET, SetEnum es -> SetEnum (map (fun xs -> SetEnum xs |> mk) (all_perms es)) |> mk *)
        | _ -> Apply (o, [ex]) |> mk
        end
    | Apply (f, es) -> 
        Apply (gr0 f, map gr0 es) |> mk
    | Quant (q, bs, ex) -> 
        let ex = gr0 ex in
        begin match q, bs, ex.core with
        | Forall, _,                      Internal B.TRUE  -> tla_true
        | Forall, (_, _, No_domain) :: _, Internal B.FALSE -> tla_false
        | Exists, _,                      Internal B.FALSE -> tla_false
        | Exists, (_, _, No_domain) :: _, Internal B.TRUE  -> tla_true
        | _ -> Quant (q, gr0_bs bs, gr0 ex) |> mk
        end
    | If (c, t, f) -> 
        let c = gr0 c in
        let t = gr0 t in
        let f = gr0 f in
        if Expr.Eq.expr t f then build t else
        begin match c.core with
        | Internal B.TRUE -> build t
        | Internal B.FALSE -> build f
        | _ -> If (c,t,f) |> mk
        end
    | FcnApp (f, es)    -> FcnApp (gr0 f, map gr0 es) |> mk
    | Dot (r, h)        -> Dot (gr0 r, h) |> mk
    | Tuple es          -> Tuple (map gr0 es) |> mk
    | Record rs         -> Record (map (fun (h,e) -> h, gr0 e) rs) |> mk
    | SetOf (ex, bs)    -> SetOf (gr0 ex, gr0_bs bs) |> mk
    | SetSt (h, dom, p) -> SetSt (h, gr0 dom, gr0 p) |> mk
    | SetEnum es        -> SetEnum (map gr0 es) |> mk
    | Arrow (x, y)      -> Arrow (gr0 x, gr0 y) |> mk
    | Rect es           -> Rect (map (fun (h,e) -> h, gr0 e) es) |> mk
    | Product es        -> Product (map gr0 es) |> mk
    | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (gr0_bs bs, gr0 ex) |> mk
    | Except (f, exs) ->
        let gr0_ex = function Except_apply ea -> Except_apply (gr0 ea) | Except_dot h -> Except_dot h in
        let exs = map (fun (es,ex) -> map gr0_ex es, gr0 ex) exs in
        Except (gr0 f, exs) |> mk
    | Sequent seq -> gr0 (unroll_seq seq)
    | Parens (ex,_) -> gr0 (build ex)
    | Choose (h, Some d, ex) -> Choose (h, Some (gr0 d), gr0 ex) |> mk
    | Choose (h, None, ex) -> Choose (h, None, gr0 ex) |> mk
    | Case (es, o) ->
        let es = map (fun (p,e) -> gr0 p, gr0 e) es in
        let o = match o with Some o -> Some (gr0 o) | None -> None in
        Case (es, o) |> mk
    | Lambda (xs, ex) -> Lambda (xs, gr0 ex) |> mk
    | _ -> e
and gr0_bs bs =
    let faux = function
    | (v, k, Domain d) -> (v, k, Domain (gr0 d))
    | b -> b
    in map faux bs
;;

(** Arithmetic *)
let rec gr_arith e =
(* Util.eprintf "gr_arith: %a" (print_prop ()) e ; *)
    let mk x = { e with core = x } in    
    let build ex = match ex.core with a -> a |> mk in    (** mantains e's original properties, especially the isconc property *)
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    (* let lAnd es = List (And, es) |> mc <<< Some Bool in *)
    let tla_true  = Internal B.TRUE |> mc <<< Some Bool in
    let apply2' op e1 e2 = Apply (op, [e1;e2]) |> mc in
    (* let mem x y     = apply2' (Internal B.Mem |> mc <<< Some Bool) x y <<< Some Bool in *)
    let leq x y     = apply2' (Internal B.Lteq |> mc <<< Some Bool) x y <<< Some Bool in
    let lt x y      = apply2' (Internal B.Lt |> mc <<< Some Bool) x y <<< Some Bool in
    let plus x y    = apply2' (Internal B.Plus |> mc <<< Some Int) x y <<< Some Int in
    let minus x y   = apply2' (Internal B.Minus |> mc <<< Some Int) x y <<< Some Int in
    let zero = Num ("0","") |> mc <<< Some Int in
    let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in
    match e.core with
    | Apply ({core = Internal op} as o, [x ; y]) -> 
        let x = gr_arith x in
        let y = gr_arith y in
        let is_neg n = n.[0] = '-' in
        let mk_num n = Num (string_of_int n,"") |> mc <<< Some Int in
        let abs n = if is_neg n then Num (String.sub n 1 ((String.length n) - 1),"") |> mc <<< Some Int else mk_num (int_of_string n) in
        begin match op, x.core, y.core with
        | (B.Plus | B.Minus), _, Num ("0","") when is_Int x -> build x
        | B.Plus, Num ("0",""), _ when is_Int y -> build y
        | B.Minus, Num ("0",""), _ when is_Int y -> Apply (Internal B.Uminus |> mc, [y]) |> mk

        (** Trivial arithmetic rules, no context needed *)
        | B.Plus,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) + (int_of_string y))
        | B.Minus,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) - (int_of_string y))
        | B.Times,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) * (int_of_string y))
        | B.Quotient,  Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 -> 
                                                                                   mk_num ((int_of_string x) / (int_of_string y)) (* integer division *)
        | B.Remainder, Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 -> 
                                                                                   mk_num ((int_of_string x) mod (int_of_string y))
        | B.Ratio,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y <> 0 ->
                                                                                   Num (string_of_float' ((float_of_string x) /. (float_of_string y)),"") |> mk
        | B.Exp,       Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> Num (string_of_float' ((float_of_string x) ** (float_of_string y)),"") |> mk


        | B.Minus, _, _ when is_Int x && is_Int y && Expr.Eq.expr x y -> zero
        | B.Lteq, _, _  when is_Int x && is_Int y && Expr.Eq.expr x y -> tla_true
        | B.Gteq, _, _  when is_Int x && is_Int y && Expr.Eq.expr x y -> tla_true

        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w]) 
            when for_all is_Int [x;y;z;w] && Expr.Eq.expr x z -> leq y w
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w]) 
            when for_all is_Int [x;y;z;w] && Expr.Eq.expr y w -> leq x z
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w]) 
            when for_all is_Int [x;y;z;w] && Expr.Eq.expr x w -> leq y z
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w]) 
            when for_all is_Int [x;y;z;w] && Expr.Eq.expr y z -> leq x w

        (** algebraic manipulation, recursive *)
        | (B.Lteq | B.Gteq), _, Apply ({core = Internal B.Minus}, [z ; w]) 
            when for_all is_Int [x;z;w] -> gr_arith (Apply (o, [plus x w ; z]) @@ e)
        | (B.Lteq | B.Gteq), Apply ({core = Internal B.Minus}, [z ; w]), _ 
            when for_all is_Int [y;z;w] -> gr_arith (Apply (o, [z ; plus y w]) @@ e)

        (* | B.Plus, x, y -> 
            let uminus1 e = match e.core with
            | Apply ({core = Internal B.Uminus}, [e]) -> e
            | Num (n,"") when is_neg n -> abs n
            | Num (n,"") -> Num ("-"^n,"") |> mc <<< Some Int
            | _ -> Apply (Internal B.Uminus, [e]) |> mk
            in
            let uminus es = map uminus1 es in
            let rec to_add e = 
              match e.core with
              | Apply ({core = Internal o}, [x ; y]) -> 
                  begin match o, x.core, y.core with
                  | B.Plus, x, y  -> to_add x @ to_add y
                  | B.Minus, x, y -> to_add x @ uminus (to_add y)
                  | _ -> [e]
                  end
              | _ -> [e]
            in
           
            let xs = to_add e in
            let nums,xs = partition (fun e -> match e.core with Num _ -> true | _ -> false) xs in
            let xs = order xs in
            let xs = simplify xs in
            to_expr xs *)

        | B.Minus, Apply ({core = Internal B.Plus},  [x ; z]), _ when for_all is_Int [x;y;z] && Expr.Eq.expr x y -> gr_arith z
        | B.Minus, Apply ({core = Internal B.Plus},  [z ; x]), _ when for_all is_Int [x;y;z] && Expr.Eq.expr x y -> gr_arith z
        | B.Plus,  Apply ({core = Internal B.Minus}, [x ; z]), _ when for_all is_Int [x;y;z] && Expr.Eq.expr z y -> gr_arith x
        | B.Plus,  _, Apply ({core = Internal B.Minus}, [y ; z]) when for_all is_Int [x;y;z] && Expr.Eq.expr x z -> gr_arith y

        (** number simpl *)
        | B.Plus,  Apply ({core = Internal B.Plus}, [ex ; ({core = Num _} as x)]), Num _
        | B.Plus,  Apply ({core = Internal B.Plus}, [({core = Num _} as x) ; ex]), Num _ when is_Int ex -> gr_arith (plus ex (gr_arith (plus x y)))
        | B.Plus,  Num _, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as y)])
        | B.Plus,  Num _, Apply ({core = Internal B.Plus},  [({core = Num _} as y) ; ex]) when is_Int ex -> gr_arith (plus ex (gr_arith (plus x y)))

        | B.Plus,  Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as x)]), Num _ when is_Int ex -> gr_arith (plus ex (gr_arith (minus y x)))
        | B.Plus,  Apply ({core = Internal B.Minus}, [({core = Num _} as x) ; ex]), Num _ when is_Int ex -> gr_arith (minus (gr_arith (plus y x)) ex)
        | B.Minus, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as x)]), Num _
        | B.Minus, Apply ({core = Internal B.Plus},  [({core = Num _} as x) ; ex]), Num _ when is_Int ex -> gr_arith (plus ex (gr_arith (minus x y)))
        | B.Minus, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as x)]), Num _ when is_Int ex -> gr_arith (minus ex (gr_arith (plus x y)))
        | B.Minus, Apply ({core = Internal B.Minus}, [({core = Num _} as x) ; ex]), Num _ when is_Int ex -> gr_arith (minus (gr_arith (minus x y)) ex)

        (* | B.Plus,  Num _, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as y)]) -> gr_arith (plus ex (gr_arith (minus x y))) *)
        (* | B.Plus,  Num _, Apply ({core = Internal B.Minus}, [({core = Num _} as y) ; ex]) -> gr_arith (minus (gr_arith (plus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as y)]) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Plus},  [({core = Num _} as y) ; ex]) -> gr_arith (minus (gr_arith (minus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as y)]) -> gr_arith (minus (gr_arith (plus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Minus}, [({core = Num _} as y) ; ex]) -> gr_arith (plus ex (gr_arith (minus x y))) *)

        (** structural *)
        | B.Plus,  _, Apply ({core = Internal B.Minus}, [y ; z]) when is_Int x && is_Int y && is_Int z -> gr_arith (minus (plus x y) z)
        | B.Plus,  Apply ({core = Internal B.Minus}, [x ; z]), _ when is_Int x && is_Int y && is_Int z -> gr_arith (minus (plus x y) z)
        | B.Minus, _, Apply ({core = Internal B.Plus},  [y ; z]) when is_Int x && is_Int y && is_Int z -> gr_arith (minus (minus x y) z)
        | B.Minus, _, Apply ({core = Internal B.Minus}, [y ; z]) when is_Int x && is_Int y && is_Int z -> gr_arith (minus (plus x z) y)

        (* | B.Plus,  Apply ({core = Internal B.Minus}, [ex ; x]), _ -> gr_arith (plus ex (minus y x)) *)
        (* | B.Minus, Apply ({core = Internal B.Plus},  [ex ; x]), _ -> gr_arith (plus ex (gr_arith (minus x y))) *)
        (* | B.Minus, Apply ({core = Internal B.Minus}, [ex ; x]), _ -> gr_arith (minus ex (plus x y)) *)
        
        | B.Plus, _, Num (n,"")  when is_Int x && is_neg n -> gr_arith (minus x (abs n) )
        | B.Plus, Num (n,""), _  when is_Int y && is_neg n -> gr_arith (minus y (abs n) )
        | B.Minus, _, Num (n,"") when is_Int x && is_neg n -> gr_arith (plus  x (abs n) )

(*         | B.Mem, Apply ({core = Internal B.Plus}, [a ; b]), (Internal B.Int | Internal B.Nat) -> 
            gr_arith (lAnd [mem a y ; mem b y])
        | B.Mem, Apply ({core = Internal (B.Minus | B.Times | B.Exp) }, [a ; b]), Internal B.Int -> 
            gr_arith (lAnd [mem a y ; mem b y])
 *)
        | _ -> Apply (o, [x ; y]) |> mk
        end
    | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Lteq}, [x ; y])}]) -> lt y x |> gr_arith
    | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Lt},   [x ; y])}]) -> leq y x |> gr_arith
    | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Gteq}, [x ; y])}]) -> lt x y |> gr_arith
    | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Gt},   [x ; y])}]) -> leq x y |> gr_arith
    | Quant (q, bs, ex)  -> Quant (q, gr_arith_bs bs, gr_arith ex) |> mk
    | Apply (f, es)      -> Apply (gr_arith f, map gr_arith es) |> mk
    | List (b, es)       -> List (b, map gr_arith es) |> mk
    | If (c, t, f)       -> If (gr_arith c, gr_arith t, gr_arith f) |> mk 
    | FcnApp (f, es)     -> FcnApp (gr_arith f, map gr_arith es) |> mk
    | Dot (r, h)         -> Dot (gr_arith r, h) |> mk
    | Tuple es           -> Tuple (map gr_arith es) |> mk
    | Record rs          -> Record (map (fun (h,e) -> h, gr_arith e) rs) |> mk
    | SetOf (ex, bs)     -> SetOf (gr_arith ex, gr_arith_bs bs) |> mk
    | SetSt (h, dom, p)  -> SetSt (h, gr_arith dom, gr_arith p) |> mk
    | SetEnum es         -> SetEnum (map gr_arith es) |> mk
    | Arrow (x, y)       -> Arrow (gr_arith x, gr_arith y) |> mk
    | Rect es            -> Rect (map (fun (h,e) -> h, gr_arith e) es) |> mk
    | Product es         -> Product (map gr_arith es) |> mk
    | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (gr_arith_bs bs, gr_arith ex) |> mk
    | Except (f, exs) ->
        let gr_arith_ex = function Except_apply ea -> Except_apply (gr_arith ea) | Except_dot h -> Except_dot h in
        let exs = map (fun (es,ex) -> map gr_arith_ex es, gr_arith ex) exs in
        Except (gr_arith f, exs) |> mk
    | Sequent seq -> gr_arith (unroll_seq seq)
    | Parens (ex,_) -> gr_arith (build ex)
    | Choose (h, Some d, ex) -> Choose (h, Some (gr_arith d), gr_arith ex) |> mk
    | Choose (h, None, ex) -> Choose (h, None, gr_arith ex) |> mk
    | Case (es, o) ->
        let es = map (fun (p,e) -> gr_arith p, gr_arith e) es in
        let o = match o with Some o -> Some (gr_arith o) | None -> None in
        Case (es, o) |> mk
    | Lambda (xs, ex) -> Lambda (xs, gr_arith ex) |> mk
    | _ -> e
and gr_arith_bs bs =
    let f = function
    | (v, k, Domain d) -> (v, k, Domain (gr_arith d))
    | b -> b
    in map f bs
;;

(****************************************************************************)

(** unbound bs *)
let rec unb bs = 
    let mc x = noprops x in
    let mb x = noprops x <<< Some Bool in
    (* let lAnd = function [e] -> e | es -> List (And, es) |> mb in *)
    let mem x y = Apply (Internal B.Mem |> mb, [x ; y]) |> mb in
    match bs with
    | (_, _, Domain d) as b1 :: (h,k,Ditto) :: bs ->
        unb (b1 :: (h,k,Domain d) :: bs)
    | (v, k, Domain dom) :: bs -> 
        let n = (length bs) + 1 in
        let _, bs = app_bounds (shift 1) bs in
        let bs,ds = unb bs in 
        let ex = mem (Ix n |> mc <<< typ v) (app_expr (shift n) dom) in
        (v, k, No_domain) :: bs, (ex :: ds)
    | (v, k, No_domain) :: bs -> 
        let bs,ds = unb bs in 
        (v, k, No_domain) :: bs, ds
    | [] -> [],[]
    | _ -> assert false
;;

let is_true e = Expr.Eq.expr e (noprops (Internal B.TRUE)) ;;

let rec gr1 cx e : Expr.T.expr =
(* Util.eprintf "Rewriting: %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
    let mk x = { e with core = x } in
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    let mb x = if is_conc e then assign (noprops x <<< Some Bool) isconc () else noprops x <<< Some Bool in
    let build ex = if is_conc e then assign ex isconc () else ex (* match ex.core with a -> a |> mk *) in    (** mantains e's original properties, especially the isconc property *)
    let apply   op es    = Apply (op, es) |> mk in
    (* let apply'  op es    = Apply (op, es) |> mc in *)
    let apply2' op e1 e2 = Apply (op, [e1;e2]) |> mc in
    let apply1b op ex    = Apply (Internal op |> mc <<< Some Bool, [ex]) |> mc <<< Some Bool in
    let apply2b op e1 e2 = Apply (Internal op |> mc <<< Some Bool, [e1 ; e2]) |> mc  <<< Some Bool in
    (* let apply   op e1 e2 = Apply (noprops (Internal op), [e1 ; e2]) |> mc in *)
    (* let apply1  op ex    = Apply (noprops (Internal op), [ex]) |> mc in *)
    let opq id = function [] -> Opaque id |> mc | es -> Apply (noprops (Opaque id), es) |> mc in
    let fcnapp f x = FcnApp (f, [x]) |> mc in
    let dot r h = Dot (r, h) |> mc in
    let ix1 = noprops (Ix 1) in
    let sh1 e = app_expr (shift 1) e in
    let ( <~ ) ex y = app_expr (scons y (shift 0)) ex in      (***  substitutes Ix 1 by y in ex *)
    let quant q h dom ex = 
        let dom = match dom with
            | Some d -> 
                let t = TLAtype.base (typpbot d) in
                types#update ((* quant_id *) h.core) t ;
                let h = assign h boundvar () in                
                [h <<< Some t, Unknown, Domain d]
            | None -> [h, Unknown, No_domain]
        in
        Quant (q, dom, ex) |> mb in
        (* Quant (q, [h, Unknown, No_domain], ex) |> mb in *)
    let forall ?id:(h=fresh_name () |> mc) ?dom ex = quant Forall h dom ex in
    let exists ?id:(h=fresh_name () |> mc) ?dom ex = quant Exists h dom ex in
    let lAnd es = List (And, es) |> mb in
    let lAndx = function [e] -> e | es -> List (And, es) |> mb in
    let lOr es = List (Or, es) |> mb in
    let domain ex   = Apply (Internal B.DOMAIN |> mc, [ex]) |> mc in
    let mem x y     = apply2b B.Mem x y in
    let implies x y = apply2b B.Implies x y in
    let eq x y      = apply2b B.Eq x y in
    let conj x y    = apply2b B.Conj x y in
    let disj x y    = apply2b B.Disj x y in
    let equiv x y   = apply2b B.Equiv x y in
    let neg x       = apply1b B.Neg x in
    let len x       = apply (Internal B.Len |> mc <<< Some Int) [x] in
    let range x y   = apply2' (Internal B.Range |> mc <<< Some (P Int)) x y <<< Some (P Int) in
    let plus x y    = apply2' (Internal B.Plus |> mc <<< Some Int) x y <<< Some Int in
    let minus x y   = apply2' (Internal B.Minus |> mc <<< Some Int) x y <<< Some Int in
    let lt x y      = apply2' (Internal B.Lt |> mc <<< Some Bool) x y <<< Some Bool in
    let isAFcn x  = 
        types#update "isAFcn" (Fcn(Fcn(Bot,Bot),Bool)) ;
        (* noprops (Apply (noprops (Opaque "isAFcn"), [x])) <<< Some Bool *) 
        opq "isAFcn" [x] in
    (* let isASeq x  = 
        types#update "isASeq" (Fcn(Fcn(Bot,Bot),Bool)) ;
        opq "isASeq" [x] in *)
    let str s     = noprops (String s) <<< Some Str in
    let fld f     = assign f isFld () in
    let isFldOf f r = opq "isFldOf" [fld f ; r] in
    let ifte c t f = If (c,t,f) |> mc <<< typ e in
    let ifte_bool c t f = 
      ifte c t f
      (* let c = simp_simplefacts cx c in
      if is_true c then t else begin
      match !mode with | Spass | Fof -> conj (implies c t) (implies (neg c) f)
                       | _ -> ifte c t f <<< Some Bool end  *)
    in
    (* let ifte_eq p c t f = if mem_simplefacts cx c then p t else forall (implies (ifte (sh1 c) (eq ix1 (sh1 t)) (eq ix1 (sh1 f))) (sh1 (p (Ix 0 |> mk)))) in *)
    let tla_true  = Internal B.TRUE  |> mb in
    let tla_false = Internal B.FALSE |> mb in
    let zero = Num ("0","") |> mc <<< Some Int in
    let one = Num ("1","") |> mc <<< Some Int in
    let ints = Internal B.Int |> mc <<< Some (P Int) in 
    let nats = Internal B.Nat |> mc <<< Some (P Int) in 
    let leq x y = apply2b B.Lteq x y in
    let mk_num n = Num (string_of_int n,"") |> mc <<< Some Int in
    (* let str_is_nat x = try int_of_string x >= 0 with Invalid_argument _ -> false in *)
    (* let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in *)
    let rec range2set a b = if a <= b then (Num (string_of_int a,"") |> mc <<< Some Int) :: range2set (a+1) b else [] in
    let get_exp_seq_func e = 
      match e.core with
      | Expr.T.Fcn ([h,_,Domain ({core = Apply ({core = Internal B.Range}, [{core = Num ("1","")} ; n])} as dom)], ex) -> Some (h,n,dom,ex)
      | Expr.T.Fcn ([h,_,Domain ({core = SetEnum es} as dom)], ex) -> 
        let n' = length es in
        let n = Num (string_of_int n',"") |> mc <<< Some Int in
        if es = range2set 1 n' then Some (h,n,dom,ex) else None
      | _ -> None
    in
    let is_exp_seq_func e = get_exp_seq_func e <> None in
    let p e = paint_types cx e in
    let gr1p cx e = gr1 cx (p e) in
    let gr1s = map (gr1 cx) in
(* typetree cx e ; *)
    let e = gr0 e in
    let e = if !mode = Fof then e else gr_arith e in
    match e.core with
    | If (c,t,f) when (!mode = Spass || !mode = Fof) && is_Bool c && is_Bool t && is_Bool f -> 
        let c = simp_simplefacts cx c in
        if is_true c then t else conj (implies c t) (implies (neg c) f)
    | Internal B.BOOLEAN -> SetEnum [tla_true ; tla_false] |> mc <<< Some (P Bool)
    | Apply ({core = Internal B.Neq}, ([x ; {core = SetEnum []}] 
                                     | [{core = SetEnum []} ; x])) when is_conc e -> 
        implies (eq x (SetEnum [] |> mc)) tla_false |> gr1p cx
    | Apply ({core = Internal B.Neq}, ([x ; {core = SetEnum []}] 
                                     | [{core = SetEnum []} ; x])) -> 
        exists ~dom:x tla_true |> gr1p cx
    | Apply ({core = Internal op} as o, [x ; y]) -> 
        let x = gr1 cx x in
        let y = gr1 cx y in
        begin match op, x.core, y.core with
        | B.Mem, _, If (c,t,f) when is_term x || is_set x -> ifte c (mem x t) (mem x f) |> gr1 cx
        | B.Mem, If (c,t,f), _ when is_term y || is_set y -> ifte c (mem t y) (mem f y) |> gr1 cx
        (* | B.Mem, _, If (c,t,f) when is_term x || is_set x -> ifte_bool c (mem x t) (mem x f) |> gr1 cx
        | B.Mem, If (c,t,f), _ when is_term y || is_set y -> ifte_bool c (mem t y) (mem f y) |> gr1 cx *)
        (* | B.Mem, _, If (c,t,f) -> gr1 cx (ifte_eq (mem x) c t f)
        | B.Mem, If (c,t,f), _ -> gr1 cx (ifte_eq (fun x -> mem x y) c t f) *)

        | B.Mem, _, Apply ({core = Internal op2}, [ex]) -> 
            begin match op2, ex.core with
            | B.SUBSET, _ -> gr1 cx (apply2b B.Subseteq x ex)
            | B.UNION, SetEnum es                   -> gr1 cx (lOr (map (mem x) es))
            | B.UNION, SetOf (ex, ([v,_,Domain s])) -> gr1p cx (exists ~dom:s (mem (sh1 x) ex))
            | B.UNION, SetSt (v, s, p)              -> gr1p cx (exists ~dom:s (lAnd [p ; mem (sh1 x) ix1]))
            | B.UNION, _                            -> gr1p cx (exists ~dom:ex (mem (sh1 x) ix1))
            | B.Seq, _ ->
                begin match x.core with
                | Tuple [] -> tla_true
                | Tuple es -> lAnd (map (fun e -> mem e ex) es) |> gr1 cx
                | _ when is_exp_seq_func x -> 
                    let h,n,dom,ex1 = Option.get (get_exp_seq_func x) in
                    if is_Int n 
                    then gr1 cx (forall ~id:h ~dom:dom (mem ex1 (sh1 ex)))
                    else mem (gr1 cx x) (gr1 cx y)
                (* | Expr.T.Fcn ([h,_,Domain ({core = Apply ({core = Internal B.Range}, [{core = Num ("1","")} ; n])} as dom)], ex1) when is_Int n -> 
                    gr1 cx (forall ~id:h ~dom:dom (mem ex1 (sh1 ex))) *)
                    (** FIX: mem n nats is a condition *)
                    (* gr1 cx (lAnd [mem n nats ; forall ~id:h ~dom:dom (mem ex1 (sh1 ex))]) *)
                | Apply ({core = Internal B.Tail}, [t])           -> gr1 cx (lAnd [neg (eq t (Tuple [] |> mc)) ; mem t y])
                | Apply ({core = Internal B.Append}, [t ; e])     -> gr1 cx (lAnd [mem t y ; mem e ex])
                | Apply ({core = Internal B.Cat}, [r ; t])        -> gr1 cx (lAnd [mem r y ; mem t y])
                | Apply ({core = Internal B.SubSeq}, [s ; m ; n]) -> gr1 cx (lAnd [mem s y ; mem m ints ; mem n ints])
                | Except (s, [([Except_apply a], b)]) -> gr1 cx (lAnd [mem s y ; mem a (range one (len s)) ; mem b ex])
                (* | _ -> 
                    gr1 cx (mem x (Apply (Internal B.UNION |> mc, [SetOf (Arrow (range one ix1, sh1 s) |> mc, ([fresh_name () |> mc,Unknown,Domain nats])) |> mc]) |> mc)) *)
                (* | _ ->
                    let dom = range one ix1 in
                    gr1 cx (lAnd [isAFcn x ; exists ~dom:nats 
                                (lAnd [mem ix1 nats ; 
                                       eq (domain (sh1 x)) dom ;
                                       (* eq ix1 (len (sh1 x)) ; *)
                                       forall ~dom:dom (implies (mem ix1 (sh1 dom)) (mem (fcnapp (sh1 (sh1 x)) ix1) (sh1 (sh1 s))))
                                       ])]) *)
                | _ -> mem (gr1 cx x) (gr1 cx y)
                end            
            | _ -> mem (gr1 cx x) (gr1 cx y)
            end
        | B.Mem, _, Apply ({core = Internal op2}, [e1 ; e2]) -> 
            let e1 = gr1 cx e1 in
            let e2 = gr1 cx e2 in
            begin match op2, e1.core, e2.core with
            | B.Cup, _, _ -> gr1 cx (disj (mem x e1) (mem x e2))
            | B.Cap, _, _ -> gr1 cx (conj (mem x e1) (mem x e2))
            | B.Setminus, _, _ -> gr1 cx (conj (mem x e1) (neg (mem x e2)))
            | B.Range, _, _ -> gr1 cx (lAnd [mem x (Internal B.Int |> mc <<< Some (P Int)) ; leq e1 x ; leq x e2])
            | _ -> mem (gr1 cx x) (gr1 cx y)
            end
        | B.Mem, _, SetEnum []        -> tla_false
        | B.Mem, _, SetEnum es        -> gr1 cx (lOr (map (eq x) es))
        | B.Mem, _, SetOf (ex, bs)    -> gr1 cx (Quant (Exists, bs, eq (app_expr (shift (length bs)) x) ex) |> mb)
        | B.Mem, _, SetSt (_, dom, p) -> gr1 cx (conj (mem x dom) (p <~ x))
        | B.Mem, _, Product es -> gr1 cx (lAnd ([ eq (domain x) (range one (mk_num (length es))) ] @ 
                                       (mapi (fun i e -> mem (fcnapp x (mk_num (i+1))) e) es)))
        | B.Mem, _, Internal B.BOOLEAN when is_Bool (gr1 cx x) -> tla_true
        | B.Mem, Apply ({core = Internal B.Len}, [_]), Internal B.Nat -> tla_true

        | B.Mem, Except (f, [([Except_apply a], b)]), Arrow (s, t) ->
            let es = [ isAFcn f ;
                       eq (domain f) s ;
                       mem a s ; mem b t ;
                       forall ~dom:(apply2' (Internal B.Setminus |> mc) s (SetEnum [a] |> mc)) (mem (fcnapp (sh1 f) ix1) (sh1 t))
                       ] in
            let es = gr1s es in
            gr1p cx (lAnd es)

        | B.Mem, _, Arrow (s, t) ->
            let es = [ isAFcn x ;
                       (* forall (equiv (mem ix1 (domain (sh1 x))) (mem ix1 (sh1 s))) ; *)
                       eq (domain x) s ;
                       (* forall ~dom:(domain x) (mem (fcnapp (sh1 x) ix1) (sh1 t)) *)
                       forall ~dom:s (mem (fcnapp (sh1 x) ix1) (sh1 t))
                       (* forall ~dom:s (implies (mem ix1 (domain (sh1 x))) (mem (fcnapp (sh1 x) ix1) (sh1 t)))      *)
                       (* forall ~dom:s (implies (disj (mem ix1 (domain (sh1 x))) (mem ix1 (sh1 s))) (mem (fcnapp (sh1 x) ix1) (sh1 t)))      *)
                                (** No typing hypotheses!! *)
                       ] in
            let es = gr1s es in
            gr1p cx (lAnd es)
        
        (* | _, Internal B.Int when typ x = Some Int -> tla_true *)
        | B.Mem, _, Internal B.Nat -> 
            gr1 cx (conj (mem x (Internal B.Int |> mc <<< Some (P Int))) 
                        (leq (Num ("0","") |> mc <<< Some Int) x))
        | B.Mem, _, Rect rs ->
            let (fs,_) = split rs in
            iter add_tla_op (sprintf "record__%d" (add_record_id fs) :: fs) ;
            gr1p cx (lAnd ((map (fun (f,_) -> isFldOf (str f) x) rs) @ 
                           (map (fun (f,e) -> mem (dot x f) e) rs)))

        | B.Mem, _, _ -> 
            mem (gr1 cx x) (gr1 cx y)

        | (B.Eq | B.Equiv), _, Choose (h, None, ex) ->
(* Util.eprintf "Choo: %a : %s" (print_prop ()) (sh1 (sh1 ex)) (typ_to_str e) ; *)
            add_choose (fresh_name ()) cx x ; 
            gr1p cx (implies (exists ~id:h ex) (ex <~ x))
        | (B.Eq | B.Equiv), Choose _, _ ->
            gr1 cx (Apply (o, [y ; x]) |> mk)

        | B.Eq, Apply ({core = Internal B.DOMAIN}, [f]), SetEnum []
        | B.Eq, SetEnum [], Apply ({core = Internal B.DOMAIN}, [f]) ->
            gr1 cx (eq f (Tuple [] |> mc))

        (* | _, Apply ({core = Internal B.DOMAIN}, [{core = Apply ({core = Internal B.Tail}, [s])}]) ->
            gr1 cx (implies (neg (eq s (Tuple [] |> mc))) (eq x (range one (minus (len s) one) )))
        | Apply ({core = Internal B.DOMAIN}, [{core = Apply ({core = Internal B.Tail}, [s])}]), _ ->
            gr1 cx (Apply (o, [y ; x]) |> mk) *)

        | B.Eq, Apply ({core = Internal B.DOMAIN}, _), _
        | B.Eq, _, Apply ({core = Internal B.DOMAIN}, _) ->
            (* apply2' o x y *)
            Apply (o, [x ; y]) |> mk      (** This rules keep the domain definitions *)

        | B.Eq, SetEnum [], Arrow (s,t)
        | B.Eq, Arrow (s,t), SetEnum [] -> 
            lAnd [apply2b B.Neq s (SetEnum [] |> mc) ; eq t (SetEnum [] |> mc)] |> gr1 cx
        | B.Eq, _, SetEnum [] ->
            gr1p cx (forall (neg (mem ix1 (sh1 x))))        (*** Unbounded quantifier! *)
        | B.Eq, SetEnum [], _ -> 
            gr1 cx (Apply (o, [y ; x]) |> mk)
        | B.Eq, _, _ when is_set x || is_set y -> 
            p (gr1 cx (forall (equiv (mem ix1 (sh1 x)) (mem ix1 (sh1 y)))))      (*** Unbounded quantifier! *)
        | B.Eq, _, Tuple es when is_exp_seq_func x ->
            let h,_,dom,ex = Option.get (get_exp_seq_func x) in
            gr1 cx (forall ~id:h ~dom:dom (eq ex (fcnapp (sh1 y) ix1))) 
        | B.Eq, Tuple es, _ when is_exp_seq_func y ->
            let h,_,dom,ex = Option.get (get_exp_seq_func y) in
            gr1 cx (forall ~id:h ~dom:dom (eq ex (fcnapp (sh1 x) ix1))) 
        | B.Eq, _, Expr.T.Fcn ([_,_,Domain dom] as bs, ex) when is_term x ->
            (** TODO: bs with more than one element *)
            let ex = lAnd [ isAFcn x ;
                            eq (domain x) dom ;
                            Quant (Forall, bs, eq (fcnapp (sh1 x) ix1) ex) |> mk ] in
            gr1p cx ex
        | B.Eq, Expr.T.Fcn _, _ when is_term y ->
            gr1 cx (Apply (o, [y ; x]) |> mk)

        | B.Eq, Apply ({core = Internal B.Range}, [a ; b]), Apply ({core = Internal B.Range}, [a' ; c]) 
          when is_Int a && is_Int b && is_Int a' && is_Int c && Expr.Eq.expr a a' -> 
            gr1 cx (lOr [eq b c ; lAnd [lt b a ; lt c a]])

        | B.Eq, _, Except ({core = Except (f, exs1)}, exs2) when is_term x -> 
            gr1 cx (Apply (o, [x ; Except (f, exs1 @ exs2) @@ y]) |> mk)

        | B.Eq, _, Except (f, ((([Except_apply _], _) :: _ ) as exs)) when is_term x -> 
            let exs = map (fun (exp,b) -> match exp with [Except_apply a] -> a,b | _ -> assert false) exs in
            let zs,_ = split exs in
            lAnd [ isAFcn x ; 
                   eq (domain x) (domain f) ;
                   lAndx (map (fun (a,b) -> eq (fcnapp x a) b) exs) ;
                   forall ~dom:(apply2' (Internal B.Setminus |> mc) (domain f) (SetEnum zs |> mc)) 
                           (eq (fcnapp (sh1 f) ix1) (fcnapp (sh1 x) ix1)) 
                 ] |> gr1p cx
            (* p ex   (** We don't normalize now. We give this equality another chance to be `simplified'. *) *)
        | B.Eq, _, Except (r, [([Except_dot h], b)]) when is_term x ->
            let f_id = add_field_prefix (fresh_name ()) in
            let h = add_field_prefix h in
            let ex = lAnd [ forall ~id:(fld (f_id |> mk)) (equiv (isFldOf ix1 (sh1 x)) (isFldOf ix1 (sh1 r))) ;         (*** Unbounded quantifier! *)
                            forall ~id:(fld (f_id |> mk)) (implies (isFldOf ix1 (sh1 r))                                (*** Unbounded quantifier! *)
                                                      (ifte_bool (eq ix1 (fld (str h))) 
                                                                 (eq (dot (sh1 x) f_id) (sh1 b)) 
                                                                 (eq (dot (sh1 x) f_id) (dot (sh1 r) f_id)))) ] in
            (* gr1p cx ex *)
            p ex
        | B.Eq, Except _, _ when is_term y ->
            gr1 cx (Apply (o, [y ; x]) |> mk)

        | B.Eq, Expr.T.Fcn ([_,_,Domain s], e1), Expr.T.Fcn ([_,_,Domain t], e2) ->
            gr1p cx (lAnd [ eq s t ; forall ~dom:s (eq e1 e2)])
        | B.Eq, Except (f, [([Except_apply a], e1)]), Except (g, [([Except_apply b], e2)]) ->
            gr1p cx (lAnd [ eq (domain f) (domain g) ;
                            forall ~dom:(domain f) (eq 
                                    (ifte (eq ix1 (sh1 a)) (sh1 e1) (fcnapp (sh1 f) ix1))
                                    (ifte (eq ix1 (sh1 b)) (sh1 e2) (fcnapp (sh1 g) ix1)))])

        | B.Eq, _, Record es when is_term x -> 
            gr1p cx (lAnd ((map (fun (h,_) -> isFldOf (str h) x) es) @ (map (fun (h,e) -> eq (dot x h) e) es)))
        | B.Eq, Record _, _ when is_term y -> 
            gr1 cx (Apply (o, [y ; x]) |> mk)
        (* | _, Tuple es -> lAnd (mapi (fun i e -> eq (fcnapp x (Num (string_of_int (i+1),"") |> mk)) e) es)
        | Tuple es, _ -> lAnd (mapi (fun i e -> eq (fcnapp y (Num (string_of_int (i+1),"") |> mk)) e) es) *)

        | (B.Eq | B.Equiv), If (c1,t1,f1), If (c2,t2,f2) -> apply2b op x y
        (* | If (c1,t1,f1), If (c2,t2,f2) -> gr1 cx (lAnd [implies c1 (conj (implies c2 (eq t1 t2))
                                                                         (implies (neg c2) (eq t1 f2))) ;
                                                        implies (neg c1) (conj (implies c2 (eq f1 t2))
                                                                               (implies (neg c2) (eq f1 f2)))]) *)

        | B.Equiv, _, If (c,t,f) when is_term x -> gr1 cx (ifte_bool c (equiv x t) (equiv x f))
        | B.Equiv, If (c,t,f), _ when is_term y -> gr1 cx (ifte_bool c (equiv t y) (equiv f y))
        | B.Eq, _, If (c,t,f) when is_term x -> gr1 cx (ifte c (eq x t) (eq x f))
        | B.Eq, If (c,t,f), _ when is_term y -> gr1 cx (ifte c (eq t y) (eq f y))

        | B.Eq, Num _, Apply ({core = Internal B.Minus}, [n ; ({core = Num _} as y)]) -> gr1 cx (eq n (plus x y))
        | B.Eq, Apply ({core = Internal B.Minus}, [n ; ({core = Num _} as x)]), Num _ -> gr1 cx (eq n (plus x y))

        | B.Eq, Expr.T.Fcn ([_,_,Domain s], _), Tuple [] -> 
            gr1 cx (eq s (SetEnum [] |> mc))

        | B.Eq, Apply ({core = Internal B.Cat}, [s ; t]), Tuple [] -> 
            gr1 cx (lAnd [eq s y ; eq t y])
        | B.Eq, Apply ({core = Internal B.SubSeq}, [s ; m ; n]), Tuple [] -> 
            gr1 cx (lOr [eq s (Tuple [] |> mc) ; eq (range one (minus (plus one n) m)) (SetEnum [] |> mc)])
            
        (* | _, Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]) -> 
            gr1 cx (implies (neg (eq s (Tuple [] |> mc))) 
                            (eq x (minus (len s) one)) )  *)
        | B.Eq, _, Apply ({core = Internal B.Len}, [s]) -> 
            gr1 cx (lAnd [mem x nats ; eq (domain s) (range one x)])
            (* gr1 cx (implies (isASeq s)
                            (lAnd [mem x nats ; eq (domain s) (range one x)])) *)
            (* gr1 cx (implies (exists ~dom:nats (eq (domain (sh1 s)) (range one ix1)))
                            (lAnd [mem x nats ; eq (domain s) (range one x)])) *)
        | B.Eq, _, Apply ({core = Internal B.Append}, [s ; ex]) -> 
            let dom1 = range one (len s) in
            gr1 cx (lAnd [ isAFcn x ;
                           eq (domain x) (range one (plus (len s) one)) ;
                           forall ~dom:dom1 (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) ix1)) ;
                           eq (fcnapp x (plus (len s) one)) ex ])
        | B.Eq, _, Apply ({core = Internal B.Tail}, [s]) ->
            let dom = range one (minus (len s) one) in 
            gr1 cx (implies (neg (eq s (Tuple [] |> mc))) 
                            (lAnd [ isAFcn x ;
                                    eq (domain x) dom ;
                                    forall ~dom:dom (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) (plus ix1 one))) ]))
        | B.Eq, _, Apply ({core = Internal B.Cat}, [s ; t]) -> 
            let dom = range one (plus (len s) (len t)) in 
            gr1 cx (lAnd [ isAFcn x ;
                           eq (domain x) dom ;
                           (* forall ~dom:dom (eq (fcnapp (sh1 x) ix1) 
                                              (ifte (leq one (len (sh1 s))) (fcnapp (sh1 s) ix1) (fcnapp (sh1 t) (minus ix1 (len (sh1 s))))) )  *)
                           forall ~dom:(range one (len s)) (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) ix1)) ;
                           forall ~dom:(range (plus (len s) one) (plus (len s) (len t))) (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 t) (minus ix1 (len (sh1 s)))))
                            ])
        | B.Eq, _, Apply ({core = Internal B.SubSeq}, [s ; m ; n]) -> 
            let dom = range one (minus (plus one n) m) in 
            gr1 cx (lAnd [ isAFcn x ;
                           eq (domain x) dom ;
                           (* forall ~dom:dom (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) (minus (plus ix1 (sh1 m)) one)))  *)
                           forall ~dom:(range m n) (eq (fcnapp (sh1 x) (minus (plus one ix1) (sh1 m))) (fcnapp (sh1 s) ix1)) 
                           ])
        | B.Eq, Apply ({core = Internal B.Len 
                       | Internal B.Append 
                       | Internal B.Tail 
                       | Internal B.Cat
                       | Internal B.SubSeq}, _), _ ->
            gr1 cx (Apply (o, [y ; x]) |> mk)
        | B.Eq, Tuple [], _ -> 
            gr1 cx (Apply (o, [y ; x]) |> mk)

        | B.Eq, Opaque _, Lambda (vs, ex) -> 
            let vs = fold_right (fun (h,s) r -> match s with Shape_expr -> (Opaque h.core |> mk) :: r | Shape_op _ -> r) vs [] in
            let ex = fold_right (fun v e -> e <~ v) vs ex in
            (* let x = Apply (x, vs) |> mk in *)
            let x = FcnApp (x, vs) |> mk in
            gr1p cx (eq x ex)

        | B.Subseteq, SetEnum es, _ -> 
            gr1 cx (lAnd (map (fun e -> mem e y) es))
        | (B.Gt | B.Gteq | B.Lt | B.Lteq), _, If (c,t,f) when is_term x -> gr1 cx (ifte_bool c (apply2' o x t <<< typ o) (apply2' o x f <<< typ o))
        | (B.Gt | B.Gteq | B.Lt | B.Lteq), If (c,t,f), _ when is_term y -> gr1 cx (ifte_bool c (apply2' o t y <<< typ o) (apply2' o f y <<< typ o))
        | (B.Plus | B.Minus | B.Times | B.Exp), _, If (c,t,f) when is_term x -> gr1 cx (ifte c (apply2' o x t <<< typ o) (apply2' o x f <<< typ o))
        | (B.Plus | B.Minus | B.Times | B.Exp), If (c,t,f), _ when is_term y -> gr1 cx (ifte c (apply2' o t y <<< typ o) (apply2' o f y <<< typ o))

        | (B.Gt | B.Gteq | B.Lt | B.Lteq), If (c1,t1,f1), If (c2,t2,f2) when Expr.Eq.expr c1 c2 ->
            gr1 cx (ifte_bool c1 (Apply (o, [t1 ; t2]) @@ e) (Apply (o, [f1 ; f2]) @@ e))
        | (B.Plus | B.Minus | B.Times | B.Exp), If (c1,t1,f1), If (c2,t2,f2) when Expr.Eq.expr c1 c2 ->
            gr1 cx (ifte c1 (Apply (o, [t1 ; t2]) @@ e) (Apply (o, [f1 ; f2]) @@ e))

        (* | (B.Gt | B.Gteq | B.Lt | B.Lteq), _, Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]) ->
            gr1 cx (lAnd [neg (eq x (Tuple [] |> mc)) ; Apply (o, [x ; minus (len s) one]) |> mk])
        | (B.Gt | B.Gteq | B.Lt | B.Lteq), Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]), _ ->
            gr1 cx (lAnd [neg (eq y (Tuple [] |> mc)) ; Apply (o, [minus (len s) one ; y]) |> mk]) *)

        | B.Conj, _, _ -> lAnd [x ; y]
        | B.Disj, _, _ -> lOr [x ; y]
        | B.Implies, _, _ when is_true (simp_simplefacts cx y) -> tla_true
        | B.Implies, _, _ when is_true (simp_simplefacts cx x) -> build y
        | B.Implies, _, _ -> gr0 (Apply (o, [simp_simplefacts cx x ; y]) |> mk)
        | B.Neq, _, _ -> neg (gr1 cx (eq x y))
        | B.Notmem, _, _ -> neg (gr1 cx (mem x y))
        | B.Subseteq, _, _ ->
            gr1p cx (forall ~dom:x (implies (mem ix1 (sh1 x)) (mem ix1 (sh1 y))))
        (* | B.BSeq, _, _          -> opq "BSeq"      (gr1s [x ; y])
        | B.Cat, _, _           -> opq "Cat"       (gr1s [x ; y])
        | B.Append, _, _        -> gr1 cx (apply B.Cat x (Tuple [y] |> mk))
        | B.SelectSeq, _, _     -> opq "SelectSeq" (gr1s [x ; y]) *)

        | B.OneArg, _, _  -> opq "OneArg"  (gr1s [x ; y])
        | B.Extend, _, _  -> opq "Extend"  (gr1s [x ; y])
        | B.Print, _, _   -> opq "Print"   (gr1s [x ; y])
        | B.Assert, _, _  -> opq "Assert"  (gr1s [x ; y])
        | B.TLCSet, _, _  -> opq "TLCSet"  (gr1s [x ; y])
        | B.SortSeq, _, _ -> opq "SortSeq" (gr1s [x ; y])
        | _ -> 
            Apply (o, [x ; y]) |> mk
        end
    | Apply ({core = Internal op} as o, [ex]) -> 
        let ex = gr1 cx ex in
        begin match op, ex.core with
        | _, If (c,t,f) -> gr1 cx (ifte c (apply o [t]) (apply o [f]))
        | B.Neg, _ -> neg (gr1 cx ex)
        | B.DOMAIN, _ ->
            begin match ex.core with
            | Expr.T.Fcn (bs,_) ->
                let rec unditto = function
                    | (_, _, Domain d) as b1 :: (h,k,Ditto) :: bs ->
                        b1 :: unditto ((h,k,Domain d) :: bs)
                    | b :: bs -> b :: unditto bs
                    | [] -> []
                in
                let bs = unditto bs in
                let rec doms = function
                | (_,_,Domain d) :: bs -> d :: doms bs
                | [] -> []
                | _ -> assert false
                in
                begin match doms bs with
                | [] -> assert false
                | [ex] -> gr1p cx ex
                | exs -> gr1p cx (Tuple exs |> mc <<< Some (Tup (map typbot exs)))
                end
            | Tuple [] -> SetEnum [] |> mc
            | Tuple es -> range one (Num (string_of_int (length es), "") |> mk)
            | Except (f,_) -> 
                apply o [gr1 cx f]
            | Apply ({core = Internal B.Tail}, [s]) ->
                gr1 cx (ifte (eq s (Tuple [] |> mc)) (SetEnum [] |> mc) (range one (minus (len s) one)))
            | Apply ({core = Internal B.Append}, [s ; _]) ->
                gr1 cx (range one (plus (len s) one))
            | _ -> 
                (* apply o [gr1 cx ex] *)
                Apply (o, [gr1 cx ex]) |> mk
            end
        | B.SUBSET, _ -> apply o [gr1 cx ex]
        | B.UNION, _  -> apply o [gr1 cx ex]
        | B.Uminus, _ -> apply o [gr1 cx ex]
        (* | B.Prime, _  -> apply1 B.Prime  (gr1 cx ex) *)
        (* | B.Prime, _ ->
            begin match ex.core with
            | Apply ({core = Ix n}, es)      -> gr1 cx (opq (prime (lookup_id cx n)) es <<< typ e)
            | Apply ({core = Opaque id}, es) -> gr1 cx (opq (prime id) es <<< typ e)
            | Ix n                           -> gr1 cx (opq (prime (lookup_id cx n)) [] <<< typ e)
            | Opaque id                      -> gr1 cx (opq (prime id) [] <<< typ e)
            | _                              -> Util.bug "src/backend/ground.ml. Prime expression."
            end *)
        | B.Unprimable, _ -> gr1 cx ex
        | B.Irregular, _ -> gr1 cx ex
        | B.Head, _ -> fcnapp ex one
        (* | B.Seq, _  -> opq "Seq"  [gr1 cx ex] *)
        (* | B.Seq, _  -> apply1 B.UNION (SetOf (Arrow (apply B.Range one ix1, (sh1 ex)) |> mk, [fresh_name () |> mk, Unknown, Domain nats]) |> mk) *)
        | B.Len, Tuple es -> Num (string_of_int (length es), "") |> mk
        | B.Len, Apply ({core = Internal B.Tail}, [s]) -> gr1 cx (ifte (eq s (Tuple [] |> mc)) zero (minus (len s) one))
        | B.Len, Apply ({core = Internal B.Append}, [ex ; _]) -> gr1 cx (plus (len ex) one)
        | B.Len, Apply ({core = Internal B.Cat}, [x ; y])   -> gr1 cx (plus (len x) (len y))
        | B.Len, Apply ({core = Internal B.SubSeq}, [s ; m ; n])   -> 
            (* gr1 cx (plus (minus n m) one)        (** FIX: only when 1 \leq m  /\  n \leq Len(s) *) *)
            (* gr1 cx (ifte (lAnd [leq one m ; leq n (len s)]) (plus (minus n m) one) (unspec cx e)) *)
            (* gr1 cx (ifte (lAnd [leq one m ; leq n (len s)]) (ifte (leq m n) (plus (minus n m) one) zero) (unspec cx e)) *)
            let dom = range one (len s) in
            gr1 cx (ifte (lAnd [mem m dom ; mem n dom]) (ifte (leq m n) (plus (minus n m) one) zero) (unspec cx e))

        | B.Len, _ when is_exp_seq_func ex -> 
            let h,n,dom,ex = Option.get (get_exp_seq_func ex) in
        (* | B.Len, Expr.T.Fcn ([_,_,Domain ({core = Apply ({core = Internal B.Range}, [{core = Num ("1","")} ; n])} as dom)], _) ->  *)
            gr1 cx (ifte (eq dom (SetEnum [] |> mc)) zero (ifte (mem n nats) n (unspec cx e)))

        | B.Len, Except (s,_) -> gr1 cx (len s)
        | B.Tail, Tuple (_ :: es) -> Tuple (gr1s es) |> mk
        (* | B.Len, _  -> opq "Len"  [gr1 cx ex] *)
        (* | B.Tail, _ -> opq "Tail" [gr1 cx ex] *)
            
        | B.PrintT, _        -> opq "PrintT"        [gr1 cx ex]
        | B.TLCGet, _        -> opq "TLCGet"        [gr1 cx ex]
        | B.Permutations, _  -> opq "Permutations"  [gr1 cx ex]
        | B.RandomElement, _ -> opq "RandomElement" [gr1 cx ex]
        | B.ToString, _      -> opq "ToString"      [gr1 cx ex]
        | _ -> apply o [gr1 cx ex]
        end
    | Apply ({core = Internal op}, es) -> 
        begin match op, es with
        | B.JavaTime,  []      -> opq "JavaTime" []
        | B.Any,       []      -> opq "Ant" []
        | B.SubSeq, [s ; n ; m] when Expr.Eq.expr n m -> gr1 cx (Tuple [fcnapp s n] |> mc)
        | _ -> Apply (Internal op |> mk, gr1s es) |> mk
        end
    | Apply ({core = Opaque "isAFcn"}, [ex]) -> 
        let ex = gr1 cx ex in
        begin match ex.core with
        | Expr.T.Fcn _ -> tla_true
        | Tuple _ -> tla_true
        | Record _ -> tla_true
        | Except _ -> tla_true
        | Apply ({core = Internal B.Append}, _)
        | Apply ({core = Internal B.Cat}, _)
        | Apply ({core = Internal B.Tail}, _)
        | Apply ({core = Internal B.SubSeq}, _)
        | Apply ({core = Internal B.SelectSeq}, _) -> tla_true
        | If (c,t,f) -> gr1 cx (ifte_bool c (isAFcn t) (isAFcn f))
        | _ -> Apply (opq "isAFcn" [], [ex]) |> mk
        end
    | Apply ({core = Opaque "isFldOf"}, [h ; ex]) ->
        let ex = gr1 cx ex in
        begin match h.core, ex.core with
        | String h, Record rs -> 
            let (hs,_) = List.split rs in if List.mem h hs then tla_true else tla_false
        | _, Except (r,_) -> gr1 cx (isFldOf h r)
        | _, If (c,t,f) -> 
            ifte_bool c (isFldOf h t) (isFldOf h f) |> gr1 cx
        | _ -> Apply (opq "isFldOf" [], [h;ex]) |> mb
        end
    | Apply (e, es) -> 
        Apply (gr1 cx e, gr1s es) |> mk

    | FcnApp (f, es) -> 
        let f = gr1 cx f in
        let es = gr1s es in
(* Util.eprintf "Rewriting: %a : %s" (print_prop ()) (opaque cx (FcnApp (f, es) |> mk)) (typ_to_str e) ; *)
        begin match f.core, es with
        | Expr.T.Fcn ([_,_,Domain dom], ex), [x] -> 
            let ex = (ex <~ x) <<< typ e in
            let c = mem x dom
              |> simp_simplefacts cx
            in
(* Util.eprintf "--- %a : %s" (print_prop ()) (opaque cx c) (typ_to_str c) ; *)
            if is_true c then ex else ifte c ex (unspec cx e) |> gr1p cx
        | Except (f, [([Except_apply y], ex)]), [x] -> 
            let c1 = mem x (domain f) 
              |> gr1p cx
              |> simp_simplefacts cx
            in
            let c2 = eq x y 
              |> gr1p cx
              |> simp_simplefacts cx
            in
            if is_true c1 then 
              if is_true c2 then ex <<< typ e |> gr1 cx
              else ifte c2 (ex <<< typ e) (fcnapp f x <<< typ e) |> gr1p cx
            else 
              ifte c1 (ifte c2 (ex <<< typ e) (fcnapp f x <<< typ e)) (unspec cx e) |> gr1p cx
        | If (c,t,f), es ->
            gr1 cx (ifte c (FcnApp (t, es) |> mk) (FcnApp (f, es) |> mk))
        | Tuple ts, [{core = Num (i,"")}] when 1 <= int_of_string i && int_of_string i <= length ts ->
            gr1 cx (nth ts ((int_of_string i) - 1))
        | Apply ({core = Internal B.Append}, [s ; ex]), [i] -> 
            gr1 cx (ifte (mem i (range one (len s))) (fcnapp s i) (ifte (eq i (plus (len s) one)) ex (unspec cx e)))
        | Apply ({core = Internal B.Tail}, [s]), [i] -> 
            gr1 cx (ifte (mem i (range one (minus (len s) one))) (fcnapp s (plus i one)) (unspec cx e))
        | Apply ({core = Internal B.SubSeq}, [s ; m ; n]), [i] -> 
            gr1 cx (ifte (mem i (range one (minus (plus one n) m))) (fcnapp s (minus (plus i m) one)) (unspec cx e))
        | Apply ({core = Internal B.Cat}, [s ; t]), [i] -> 
            gr1 cx (ifte (mem i (range one (len s))) 
                         (fcnapp s i) 
                         (ifte (mem i (range (plus (len s) one) (plus (len s) (len t)))) 
                               (fcnapp t (minus i (len s))) 
                               (unspec cx e)))
        | _ -> FcnApp (f, es) |> mk
        end

    | Dot ({core = Except (r, [([Except_dot f], ex)])}, h) -> 
        gr1 cx (ifte (conj (eq (str f) (str h)) (isFldOf (str f) r)) ex (dot r h <<< typ e))
    | Dot ({core = Record rs}, h) ->
        begin try let (_,ex) = find (fun (h',_) -> h = h') rs in ex
        with Not_found -> (* add_field h ; dot (gr1 cx r) h *) unspec cx e
        end
    | Dot ({core = If (c,t,f)}, h) -> gr1 cx (ifte c (dot t h <<< typ e) (dot f h <<< typ e))
    | Dot (ex, h) -> add_field h ; dot (gr1 cx ex) (* add_field_prefix *) h <<< typ e

    | Case ([(c, ex)], None) -> 
        let c = c
          |> gr1 cx
          |> simp_simplefacts cx
        in
        let ex = gr1 cx ex in
        if is_true c then build ex else ifte c ex (unspec cx e <<< typ ex) |> gr1 cx
    | Case ([(c, ex)], Some o) -> gr1p cx (ifte c ex o)
    (* | Case ((c, ex) :: es, None) -> (* gr1 cx (ifte c ex (Case (es, None) |> mk)) *) *)
    (* | Case (es, None) -> 
        let (cs,es) = split es in
        let p = lAnd (hd cs :: (map neg (tl cs))) in
        gr1 cx (ifte p (hd es) (Case (combine (tl cs) (tl es), None) |> mk)) *)
    | Case (es, other) ->
        let cs,es = split es in
        let c,cs = hd cs, tl cs in
        let e,es = hd es, tl es in
        gr1 cx (ifte (lAnd (c :: (map neg cs))) e (Case (combine cs es, other) |> mk))

    | List ((And | Refs), es) -> lAnd (gr1s es)
    | List (Or, es) -> lOr (gr1s es)

    | Quant (q1, ((_, _, No_domain) :: _ as bs1), 
       {core = Quant (q2, ((_, _, No_domain) :: _ as bs2), ex)}) when q1 = q2 ->
        Quant (q1, bs1 @ bs2, ex) |> mk 
    | Quant (q, ((_, _, No_domain) :: _ as bs), ex) ->
        let ex = match q with 
        | Forall -> 
            let cx = add_bs_ctx bs cx in
            let hs,ex = deimpl ex
              |>> gr1s
              |>> map deconj
              |>> concat
            in
            iter (add_simplefact cx) hs ;
            ex 
            |> gr1 cx 
            |> simp_simplefacts cx
            |> kk (remove_simplefact hs)
            |> fun ex ->
                begin match hs, ex.core with 
                | _, Internal B.TRUE -> tla_true
                | [], _ -> ex
                | [h], _ -> implies h ex  
                | _ -> implies (lAnd hs) ex  
                end 
        | Exists -> 
            (** TODO: add (some) conjuncts as facts *)
            gr1 (add_bs_ctx bs cx) ex
        in
        Quant (q, bs, ex) |> mk
    | Quant (q, bs, ex) ->
(* Util.eprintf "Rewriting: %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
        let _,ds = unb bs in
(* iter (fun e -> Util.eprintf "dom: %a" (print_prop ()) (opaque (add_bs_ctx bs cx) e)) ds ; *)
        let bs = gr1_bs cx bs in
        (* let bs = unditto bs in *)
        let v, k, dom = hd bs in
        let dom = match dom with Domain d -> d | _ -> assert false in
        iter (add_simplefact (add_bs_ctx bs cx)) ds ;
        let e = match dom.core with 
        | SetEnum es -> 
            let ex = match bs with
            | _ :: [] -> ex
            | _ :: bs -> 
                let _, bs = app_bounds (shift 1) bs in
                Quant (q, bs, ex) |> mk
            | [] -> assert false
            in
            let ex = map (fun a -> ex <~ a) es in
            let ex = match ex, q with 
            | [ex], _ -> ex 
            | _, Forall -> lAnd ex
            | _, Exists -> lOr ex
            in 
            gr1 cx ex
        | Apply ({core = Internal B.Setminus}, [(* {core = SetEnum _} as *) s ; t]) -> 
            let bs = (v, k, Domain s) :: tl bs in
            let st = neg (mem (Ix 1 |> mc <<< typ v) (app_expr (shift 1) t)) in
            let ex = match q with Forall -> implies st ex | Exists -> conj st ex in
            gr1 cx (Quant (q, bs, gr1 (add_bs_ctx bs cx) ex) |> mk)
        | _ -> 
            Quant (q, bs, gr1 (add_bs_ctx bs cx) ex) |> mk
        in
        remove_simplefact ds ;
        e
    | SetOf (ex, bs)    -> SetOf (gr1 (add_bs_ctx bs cx) ex, gr1_bs cx bs) |> mk
    | SetSt (h, dom, p) -> SetSt (h, gr1 cx dom, gr1 (add_bs_ctx [h, Unknown, Domain dom] cx) p) |> mk
    | SetEnum es        -> SetEnum (gr1s es) |> mk
    | Arrow (x, y)      -> Arrow (gr1 cx x, gr1 cx y) |> mk
    | Except ({core = If (c,t,f)}, exs) ->
        let exc f = Except (f, exs) |> mk in
        If (c, exc t, exc f) |> mk
    | Except (f, [[Except_apply a],b]) ->
        Except (gr1 cx f, [[Except_apply (gr1 cx a)], gr1 cx b]) |> mk
    | Expr.T.Fcn (bs, ex) ->
        Expr.T.Fcn (gr1_bs cx bs, gr1 (add_bs_ctx bs cx) ex) |> mk
    | Record es         -> Record (map (fun (h,e) -> h, gr1 cx e) es) |> mk
    | Rect es           -> Rect (map (fun (h,e) -> h, gr1 cx e) es) |> mk
    | Tuple es          -> Tuple (gr1s es) |> mk
    (* | Product es -> 
        let ebs = mapi (fun i e -> Ix (i+1) |> mk, ((fresh_name ()) |> mk, Unknown, Domain e)) es in
        let (es,bs) = split ebs in
        gr1 cx (SetOf (Tuple (rev es) |> mk, bs) |> mk) *)
    | If (c,t,f) -> 
(* Util.eprintf "Grounding: %a : %s" (print_prop ()) (opaque cx e) (typ_to_str e) ; *)
        let c = c 
          |> gr1 cx 
          |> simp_simplefacts cx
        in
        let (t,f) = (t,f)
          |> pairself build
          |> pairself (gr1 cx)
        in
        (* let t = gr1 cx (build t) in
        let f = gr1 cx (build f) in *)
(* Util.eprintf "\tc: %a : %s" (print_prop ()) (opaque cx c) (typ_to_str c) ; *)
        if is_true c then t else begin  
            let c = if is_Bool c then c else eq c tla_true in
            let t = add_simplefact cx c ; let t = gr1 cx t in remove_simplefact [c] ; t in
            (* let t = gr1 cx (build t) in *)
            (* let f = gr1 cx (build f) in *)
            if is_Bool t || is_Bool f 
                then ifte_bool c t f
                else ifte c t f
        end
    | Choose (h, None, ex) -> 
        Choose (h, None, gr1 (add_bs_ctx [h, Unknown, No_domain] cx) ex) |> mk
    | Choose (h, Some dom, ex) -> 
        (*** Note: Don't attach types to h or ix1. They will be later substituted by other expressions with (maybe) other types.  *)
        let e = (Choose (h, None, conj (mem (ix1 (* <<< typ h *)) (sh1 dom)) ex) |> mk) in
        gr1p cx e
    | Sequent seq -> 
        (*** TODO: quantify new variables *)
        gr1 cx (unroll_seq seq)
    | Parens (ex,_) -> gr1 cx (build ex)
    | _ -> e
and gr1_bs cx bs =
  bs
  |> map 
    begin function
    | (v, k, Domain dom) -> (v, k, Domain (gr1 cx dom))
    | b -> b
    end

let gr1 cx e =
  e
  |> gr1 cx
  |> gr0
  |> fun ee -> if is_conc e then assign ee isconc () else ee
;;

(** Unbounds quantifiers *)
let rec unbound cx e =
(* Util.eprintf "unbound: %a" (print_prop ()) (opaque cx e) ; *)
    let mk x = { e with core = x } in    
    let build ex = match ex.core with a -> a |> mk in    (** mantains e's original properties, especially the isconc property *)
    let lAnd es = flatten_conj (List (And, es) |> mk) in
    let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in
    let apply2b op e1 e2 = Apply (Internal op |> mc <<< Some Bool, [e1 ; e2]) |> mc  <<< Some Bool in
    (* let mem x y     = apply2b B.Mem x y in *)
    let implies x y = apply2b B.Implies x y in
    let conj x y    = apply2b B.Conj x y in
    match e.core with
    | Quant (q, (((_, _, No_domain) :: _) as bs), ex) ->
        Quant (q, unbound_bs cx bs, unbound (add_bs_ctx bs cx) ex) |> mk
    | Quant (q, bs, ex) ->
        let bs,ds = bs
          |> unbound_bs cx 
          |> unditto
          |> unb
          ||> (fun ds -> match ds with [b] -> b | _ -> lAnd ds)
          (* let ds = paint_types (add_bs_ctx bs cx) ds in *)
          ||> gr1 (add_bs_ctx bs cx)
        in
        let ex = ex
          |> unbound (add_bs_ctx bs cx)
          |> fun ex -> match q with Forall -> implies ds ex | Exists -> conj ds ex
        in
        Quant (q, bs, ex) |> mk
    | Apply (f, es)     -> Apply (unbound cx f, map (unbound cx) es) |> mk
    | List (b, es)      -> List (b, map (unbound cx) es) |> mk
    | If (c, t, f)      -> If (unbound cx c, unbound cx t, unbound cx f) |> mk 
    | FcnApp (f, es)    -> FcnApp (unbound cx f, map (unbound cx) es) |> mk
    | Dot (r, h)        -> Dot (unbound cx r, h) |> mk
    | Tuple es          -> Tuple (map (unbound cx) es) |> mk
    | Record rs         -> Record (map (fun (h,e) -> h, unbound cx e) rs) |> mk
    | SetOf (ex, bs)    -> SetOf (unbound (add_bs_ctx bs cx) ex, unbound_bs cx bs) |> mk
    | SetSt (h, dom, p) -> SetSt (h, unbound cx dom, unbound (add_bs_ctx [h,Unknown,Domain dom] cx) p) |> mk
    | SetEnum es        -> SetEnum (map (unbound cx) es) |> mk
    | Arrow (x, y)      -> Arrow (unbound cx x, unbound cx y) |> mk
    | Rect es           -> Rect (map (fun (h,e) -> h, unbound cx e) es) |> mk
    | Product es        -> Product (map (unbound cx) es) |> mk
    | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (unbound_bs cx bs, unbound (add_bs_ctx bs cx) ex) |> mk
    | Except (f, exs) ->
        let unbound_ex = function Except_apply ea -> Except_apply (unbound cx ea) | Except_dot h -> Except_dot h in
        let exs = map (fun (es,ex) -> map unbound_ex es, unbound cx ex) exs in
        Except (unbound cx f, exs) |> mk
    | Sequent seq -> unbound cx (unroll_seq seq)
    | Parens (ex,_) -> unbound cx (build ex)
    | Choose (h, Some d, ex) -> Choose (h, Some (unbound cx d), unbound (add_bs_ctx [h,Unknown,Domain d] cx) ex) |> mk
    | Choose (h, None, ex) -> Choose (h, None, unbound (add_bs_ctx [h,Unknown,No_domain] cx) ex) |> mk
    | Case (es, o) ->
        let es = map (fun (p,e) -> unbound cx p, unbound cx e) es in
        let o = match o with Some o -> Some (unbound cx o) | None -> None in
        Case (es, o) |> mk
    | Lambda (xs, ex) -> Lambda (xs, unbound cx ex) |> mk
    | _ -> e
and unbound_bs cx bs =
    let f = function
    | (v, k, Domain d) -> (v, k, Domain (unbound cx d))
    | b -> b
    in map f bs
;;
