(*
 * backend/smt/smt2.ml --- SMT backend using an untyped encoding.
 *
 * Author: Hern�n Vanzetto <hernan.vanzetto@inria.fr>
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

open Smtcommons
open Typesystem
open Typeinfer

module B = Builtin;;

module SSet = Smtcommons.SSet
module SMap = Smtcommons.SMap


(* let rec fcnapp_check cx e =
(* Util.eprintf "fcnapp_check: %a" (print_prop ()) (opaque cx e) ; *)
    let mk x = { e with core = x } in
    let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
    let apply1 op ex = Apply (Internal op |> mk, [ex]) |> mk in
    let lAnd es = Ground.gr0 (List (And, es) |> mk) in
    let ifte c t f = If (c,t,f) |> mk in
    let mem x = apply B.Mem x in
    let facs cx es = Ground.gr0 (lAnd (map (fcnapp_check cx) es)) in
    match e.core with
    | FcnApp (f, es) ->
        let x = match es with [e] -> e | _ -> Tuple es |> mk in
        lAnd [facs cx (f :: es) ; mem x (apply1 B.DOMAIN f) ]
    | Quant (q, bs, ex) ->
        begin match fcnapp_check (add_bs_ctx bs cx) ex with
        | {core = Internal B.TRUE} -> lAnd (facs_bs cx bs)      (** Attention: this discards expressions \E x \in S : TRUE on purpose *)
        | ex -> lAnd ((Quant (q, bs, ex) |> mk) :: facs_bs cx bs)
        end
    | Apply ({core = Internal B.Implies}, [e1 ; e2]) ->
        Ground.gr0 (apply B.Implies (lAnd [e1 ; fcnapp_check cx e1]) (fcnapp_check cx e2))
    | If (c, t, f) ->
        let t = fcnapp_check cx t in
        let f = fcnapp_check cx f in
        if Expr.Eq.expr t f then Internal B.TRUE |> mk else
        ifte (lAnd [c ; fcnapp_check cx c]) t f
    | Ix _ | String _ | Opaque _ | Internal _ | Num _ ->
        Internal B.TRUE |> mk
    | Apply (ex, es) ->
        facs cx (ex :: es)
    | List (_, es) | Tuple es | Product es | SetEnum es ->
        facs cx es
    | Expr.T.Fcn (bs, ex) | SetOf (ex, bs) ->
        lAnd ((fcnapp_check (add_bs_ctx bs cx) ex) :: facs_bs cx bs)
    | SetSt (h, dom, ex) ->
        fcnapp_check cx (Expr.T.Fcn ([h, Unknown, Domain dom], ex) |> mk)
    | Except (r, exs) ->
        let expoints_ex = function Except_apply ea -> [ea] | _ -> [] in
        let exspec eps = fold_left (fun r b -> (expoints_ex b) @ r) [] eps in
        facs cx (r :: (flatten (map (fun (eps,ex) -> ex :: exspec eps) exs)))
    | Arrow (e1, e2) ->
        facs cx [e1 ; e2]
    | Dot (ex,_) | Parens (ex,_) ->
        fcnapp_check cx ex
    | Record rs | Rect rs ->
        let es = map (fun (_,e) -> e) rs in
        facs cx es
    | Case (es, None) ->
        let es1,es2 = split es in
        facs cx (es1 @ es2)
    | Case (es, Some o) ->
        let es1,es2 = split es in
        facs cx (es1 @ es2 @ [o])
    | Sequent seq ->
        fcnapp_check cx (unroll_seq seq)
    | Choose (h, None, ex) ->
        fcnapp_check (add_bs_ctx [h, Unknown, No_domain] cx) ex
    | Choose (h, Some dom, ex) ->
        let bs = [h, Unknown, Domain dom] in
        lAnd [fcnapp_check (add_bs_ctx bs cx) ex ; fcnapp_check cx dom]
    | Lambda (vs, ex) ->
        let vs = fold_right (fun (h,s) r -> match s with Shape_expr -> (h, Unknown, No_domain) :: r | Shape_op _ -> r) vs [] in
        fcnapp_check (add_bs_ctx vs cx) ex
    | _ ->
        Util.eprintf ~at:e "function fcnapp_check cannot process@\n%a" (print_prop ()) e ;
        assert false
and facs_bs cx bs =
    let f = function
    | (_, _, Domain dom) -> [fcnapp_check cx dom]
    | _ -> []
    in
    fold_left (fun r b -> (f b) @ r) [] bs
;;

let fcnapp_obl cx e =
    let mk x = { e with core = x } in
    let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
    (* (* let glue e1 e2 = if is_conc e2 then apply B.Conj e1 e2 else apply B.Implies e1 e2 in *)
    let glue c e = if is_conc e then c else apply B.Implies c e in *)

    let is_conc = is_conc e in
    let rec glue cx e =
      match e.core with
      | Quant (q,bs,ex) -> Quant (q, bs, glue (add_bs_ctx bs cx) ex) |> mk
      | List (b,es) -> List (b, map (glue cx) es) |> mk
      | _ ->
        let c = fcnapp_check cx e in
        if is_conc then c else apply B.Implies c e
    in
(* Util.eprintf "CHECK: %a" (print_prop ()) (opaque cx c) ; *)
    (if is_conc then fcnapp_check cx e else glue cx e) |> Ground.gr0
;;

let fcnapp_obl_all cx e = Ground.gr0 (fcnapp_check cx e) ;; *)

(****************************************************************************)

let rec domains cx e =
  let mk x = { e with core = x } in
  let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
  let apply1 op ex = Apply (Internal op |> mk, [ex]) |> mk in
  let tla_true = Internal B.TRUE |> mk in
  match e.core with
  | Apply ({core = Internal B.Mem}, [x ; {core = Arrow (s,_)}]) ->
      apply B.Eq (apply1 B.DOMAIN x) s
  | _ -> tla_true
;;


type smtsort = U (* TLA+ universal sort *) | SBool | SInt | SStr | SField | SOp;;
let type_to_SMTsort = function
  | Bool -> SBool
  | Int -> SInt
  | Str -> SStr
  | Rec _ -> SField
  | _ -> U
;;

let extrasorts = ref (SSet.singleton "u") ;;
let add_extrasort s = extrasorts := SSet.add s !extrasorts ;;

let strings = ref SSet.empty ;;
let add_string str =
  add_extrasort "str" ;
  strings := SSet.add str !strings ;;

let nums = ref SSet.empty ;;
let add_num n =
  nums := SSet.add n !nums ;;

let tuple_id ts = match ts with
  | [] -> "tuple0"
  (* | _ -> sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) ;; *)
  | _ -> sprintf "tuple_%s" (String.concat "" (map (function _ -> "u") ts)) ;;

let tuples = ref [] ;;
let add_tuple ts =
    add_tla_op (tuple_id ts) ;
    if not (mem ts !tuples) then tuples := ts :: !tuples ;;

(* terms == symbols or n-ary operators *)
let terms = ref SMap.empty ;;
let add_term id arity ret_sort =
    (* if isbv || is_field id then () else  *)
    begin
    let _,t = try SMap.find id !terms with Not_found -> (arity,U) in
    (* let t = if TLAtype.gt ret_sort t then ret_sort else t in *)
    let t = if t = U then ret_sort else t in
    terms := SMap.add id (arity,t) !terms
    end ;;

(* funs_x == function symbols that return a x-sorted element, where x in {U,SInt,SStr} *)
let funs_u = ref ISet.empty ;;
let funs_i = ref ISet.empty ;;
let funs_s = ref ISet.empty ;;
let add_fun arity t = match arity, t with
    | 1, SInt  -> add_tla_op "fcnapp1_i"
    | 1, SStr  -> add_tla_op "fcnapp1_s"
    | 1, _     -> add_tla_op "fcnapp1_u"
    | _, SInt  -> funs_i := ISet.add arity !funs_i
    | _, SStr  -> funs_s := ISet.add arity !funs_s
    | _        -> funs_u := ISet.add arity !funs_u
    ;;

let ops_u = ref ISet.empty ;;
let ops_s = ref ISet.empty ;;
let ops_i = ref ISet.empty ;;
let add_op_app arity t = match arity, t with
    | 1, SInt  -> add_tla_op "op_app1_i"
    | 1, SStr  -> add_tla_op "op_app1_s"
    | 1, _     -> add_tla_op "op_app1_u"
    | _, SInt  -> ops_i := ISet.add arity !ops_i
    | _, SStr  -> ops_i := ISet.add arity !ops_s
    | _        -> ops_u := ISet.add arity !ops_u
    ;;

type t_map = {
    op :     Builtin.builtin -> string ;
    print_sort : smtsort -> string ;
    apply :  string -> string -> string list -> string ;
    quant :  Expr.T.quantifier -> (string * smtsort) list -> string -> string ;
    ite :    string option ;
    uminus : string -> string ;
}

let smtlib_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "=>"
    | B.Equiv   -> "="
    | B.Eq      -> "="
    | B.Neg     -> "not"
    | B.Plus    -> "+"
    | B.Minus   -> "-"
    | B.Times   -> "*"
    | B.Ratio   -> "/"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "*"
    | B.Lt      -> "<"
    | B.Lteq    -> "<="
    | B.Gt      -> ">"
    | B.Gteq    -> ">="
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | U      -> "u"
    | SBool  -> "Bool"
    | SInt   -> "Int"
    | SStr   -> "str"
    | SField -> "tla_Field"
    | SOp    -> "tla_Op"
    end ;
  apply = (fun f s es -> sprintf "(%s %s)" f (String.concat (" "^s) es)) ;
  ite = Some "ite" ;
  quant = begin fun q vs ex -> sprintf "(%s (%s) \n\t\t%s)"
    (match q with Forall -> "forall" | Exists -> "exists")
    (vs |> map (fun (v,t) -> sprintf "(%s %s)" v
            (match t with SInt -> "Int" | SStr -> "str" | SField -> "tla_Field" | _ -> "u"))
        |> String.concat " ")
    ex end ;
  uminus = sprintf "(- %s)" ;
} ;;

let yices_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "=>"
    | B.Equiv   -> "="
    | B.Eq      -> "="
    | B.Neg     -> "not"
    | B.Plus    -> "+"
    | B.Minus   -> "-"
    | B.Times   -> "*"
    | B.Ratio   -> "/"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "*"
    | B.Lt      -> "<"
    | B.Lteq    -> "<="
    | B.Gt      -> ">"
    | B.Gteq    -> ">="
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | U      -> "u"
    | SBool  -> "bool"
    | SInt   -> "int"
    | SStr   -> "str"
    | SField -> "tla_Field"
    | SOp    -> "tla_Op"
    end ;
  apply = (fun f s es -> sprintf "(%s %s)" f (String.concat (" "^s) es)) ;
  ite = Some "ite" ;
  quant = begin fun q vs ex -> sprintf "(%s (%s) \n\t\t%s)"
    (match q with Forall -> "forall" | Exists -> "exists")
    (vs |> map (fun (v,t) -> sprintf "%s::%s" v
            (match t with SInt -> "int" | SStr -> "str" | SField -> "tla_Field" | _ -> "u"))
        |> String.concat " ")
    ex end ;
  uminus = sprintf "-%s" ;
} ;;

let dfg_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "implies"
    | B.Equiv   -> "equiv"
    | B.Eq      -> "equal"
    | B.Neg     -> "not"
    | B.Plus    -> "plus"
    | B.Minus   -> "minus"
    | B.Times   -> "mult"
    | B.Ratio   -> "fract"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "exp"
    | B.Lt      -> "ls"
    | B.Lteq    -> "le"
    | B.Gt      -> "gs"
    | B.Gteq    -> "ge"
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | SInt   -> ":Integer"
    | _ -> ""
    end ;
  apply = (fun f s es -> sprintf "%s(%s)" f (String.concat (","^s) es)) ;
  ite = None ;
  quant = begin fun q vs ex -> sprintf "%s([%s], \n\t\t%s)"
    (match q with Forall -> "forall" | Exists -> "exists")
    (* (String.concat "," (map (fun (v,s) -> sprintf "%s%s" v (print_sort s)) vs)) *)
    (vs |> map (fun (v,s) -> sprintf "%s%s" v (match s with SInt -> ":Integer" | _ -> ""))
        |> String.concat ",")
    ex end ;
  uminus = sprintf "-%s" ;
} ;;

type fixity_type = Nonfix | Prefix | Infix

(* Only for TPTP-Fof. Disequalities and Arith are Prefix because are not supported by Fof. *)
let fixity = function
  | B.TRUE | B.FALSE -> Nonfix
  | B.Conj | B.Disj | B.Implies | B.Equiv | B.Eq -> Infix
  | B.Neg | B.Uminus -> Prefix
  | B.Plus | B.Minus | B.Times | B.Ratio | B.Quotient | B.Remainder | B.Exp -> Prefix
  | B.Lt | B.Lteq | B.Gt | B.Gteq -> Prefix
  | _ -> Nonfix
  ;;

let fof_map : t_map = {
  op = begin function
    | B.TRUE    -> "$true"
    | B.FALSE   -> "$false"
    | B.Conj    -> " & "
    | B.Disj    -> " | "
    | B.Implies -> " => "
    | B.Equiv   -> " <=> "
    | B.Eq      -> " = "
    | B.Neg     -> "~"
    | B.Plus    -> "tptp_plus"
    | B.Minus   -> "tptp_minus"
    | B.Times   -> "tptp_times"
    | B.Ratio   -> "tptp_ratio"
    | B.Quotient -> "tptp_div"
    | B.Remainder -> "tptp_mod"
    | B.Exp     -> "tptp_exp"
    | B.Lt      -> "tptp_ls"
    | B.Lteq    -> "tptp_le"
    | B.Gt      -> "tptp_gs"
    | B.Gteq    -> "tptp_ge"
    | B.Uminus  -> "tptp_uminus"
    | e ->
      Util.eprintf "Expr: %a" (print_prop ()) (noprops (Internal e)) ;
      Printf.eprintf "FOF unsupported builtin expression\n" ; assert false
    end ;
  print_sort = begin function
    | _ -> ""
    end ;
  apply = (fun f s es -> sprintf "%s(%s)" f (String.concat (","^s) es)) ;
  ite = None ;
  quant = begin fun q vs ex -> sprintf "(%s [%s] :\n\t %s)"
    (match q with Forall -> "!" | Exists -> "?")
    (String.concat "," (map (fun (v,_) -> sprintf "%s" v) vs))
    ex end ;
  uminus = sprintf "uminus(%s)"
} ;;

let rec to_smt cx e : string =
(* Util.eprintf "Expr: %a" (print_prop ()) (opaque cx e) ; *)
    let m = match !mode with Yices -> yices_map | Spass -> dfg_map | Fof -> fof_map | _ -> smtlib_map in
    let intify e = if !mode = Spass || !mode = Fof then e else begin
                   let e' = m.apply "int2u" "" [e] in
                   if try Str.first_chars e 6 = Str.first_chars e' 6
                      with Invalid_argument _ -> false
                   then e else (add_tla_op "int2u" ; e') end in
    let strify e = if !mode = Spass || !mode = Fof then e else begin
                   let e' = m.apply "str2u" "" [e] in
                   if try Str.first_chars e 6 = Str.first_chars e' 6
                      with Invalid_argument _ -> false
                   then e else (add_tla_op "str2u" ; e') end in
    let boolify e = if !mode = Spass (* || !mode = Fof *) then e else begin
                    let e' = m.apply "u2bool" "" [e] in
                    if try Str.first_chars e 7 = Str.first_chars e' 7
                       with Invalid_argument _ -> false
                    then e else (add_tla_op "u2bool" ; e') end in
    let output s = if apply_int2u e then intify s else (
                   if apply_str2u e then strify s else (
                   if apply_u2bool e then boolify s else (
                   if is_Fld e then add_field_prefix s else s))) in
    let unop cx op e = m.apply op "" [to_smt cx e] in
    (* let binop cx op e1 e2 = m.apply op "" [to_smt cx e1 ; to_smt cx e2] in *)
    (* let naryop ?sep:(s="") op es = m.apply op s (map (to_smt cx) es) in *)
    let apply ?sep:(s="") op es = m.apply op s (map (to_smt cx) es) in
    let naryop ?sep:(s="") op es =
      if !mode = Fof && fixity op = Infix
      then sprintf "(%s)" (String.concat (s^(m.op op)) (map (to_smt cx) es))
      else apply ~sep:s (m.op op) es
    in
    let proc_op op es = add_tla_op op ; apply op es in
    let arith_op op es =
        let op_tla =
            begin match op with
            | B.Plus      -> "tla_plus"
            | B.Minus     -> "tla_minus"
            | B.Times     -> "tla_times"
            | B.Exp       -> "tla_exp"
            | B.Ratio     -> "tla_ratio"
            | B.Quotient  -> "tla_div"
            | B.Remainder -> "tla_mod"
            | B.Lt        -> "tla_lt"
            | B.Lteq      -> "tla_leq"
            | B.Gt        -> "tla_gt"
            | B.Gteq      -> "tla_geq"
            | _ -> assert false
            end
        in
        (* let op = if fmt_as_int e then m.op op else (add_tla_op op_tla ; op_tla) in output (naryop op es) *)
        if fmt_as_int e then output (naryop op es) else (add_tla_op op_tla ; output (apply op_tla es))
    in
    let e_id e =
      match e.core with
      | Ix n
      | Apply ({ core = Ix n }, _) -> smt_id (lookup_id cx n)
      | Opaque id
      | Apply ({ core = Opaque id }, _) -> smt_id id
      | _ -> assert false
    in
    let is_ix_bvar cx e =
      match e.core with
      | Ix n -> is_bvar cx n
      | _ -> false
    in
    let proc_id cx e =
        let id = e_id e in
        (if has_boundvar e || is_ix_bvar cx e || is_Fld e then () else
            (if fmt_as_int e then add_term id 0 SInt
                             else add_term id 0 U)) ;
        output id
    in
    let proc_id_es cx e es =
      let id = e_id e in
      if has_boundvar e || is_ix_bvar cx e then () else begin
        add_term id (length es) U end ;
      output (apply id es)
    in
    match e.core with
    | Ix n -> proc_id cx e
    | Opaque (("isAFcn"|"isASeq"|"isFldOf") as s) -> s
    | Opaque id -> proc_id cx e
    | Apply ({ core = Opaque (("isAFcn"|"isASeq"|"isFldOf") as id) }, es) -> add_tla_op id ; apply id es

    | Apply ({ core = Ix n }, es)      -> proc_id_es cx e es
    | Apply ({ core = Opaque id }, es) -> proc_id_es cx e es
    (* | Apply (({ core = Ix _ | Opaque _ } as f), es) when fmt_as_int e -> let n = length es in add_op_app n SInt ; output (apply (sprintf "op_app%d_i" n) (f::es))
    | Apply (({ core = Ix _ | Opaque _ } as f), es)                   -> let n = length es in add_op_app n U ; output (apply (sprintf "op_app%d_u" n) (f::es)) *)
    (* | Apply (({ core = Ix _ | Opaque _ } as f), es) | FcnApp (f, es) when fmt_as_int e -> let n = length es in add_fun n SInt ; output (apply (sprintf "fcnapp%d_i" n) (f::es))
    | Apply (({ core = Ix _ | Opaque _ } as f), es) | FcnApp (f, es)                   -> let n = length es in add_fun n U ; output (apply (sprintf "fcnapp%d_u" n) (f::es)) *)

    | FcnApp (f, es) ->
        let t,s = if fmt_as_int e then SInt,"i" else U,"u" in
        let n = length es in
        add_fun n t ;
        output (apply (sprintf "fcnapp%d_%s" n s) (f::es))
    (* | FcnApp (f, es) when fmt_as_int e -> let n = length es in add_fun n SInt ; output (apply (sprintf "fcnapp%d_i" n) (f::es))
    | FcnApp (f, es)                   -> let n = length es in add_fun n U ;    output (apply (sprintf "fcnapp%d_u" n) (f::es)) *)
    | Dot (ex, h) ->
        let app = if fmt_as_int e then "tla_dot_i"
                  else                 "tla_dot_u" in
        let h = add_field_prefix h in
        add_extrasort "tla_Field" ; add_tla_op app ; add_tla_op h ;
        output (m.apply app "" [to_smt cx ex ; h])
    | Apply ({core = Internal op}, es) ->
        begin match op, es with
        | B.Mem,       [x ; { core = Internal B.Int }] when !mode <> Fof && (fmt_as_int e || typ x = Some Int) ->
            m.op B.TRUE
        | B.Mem,       [x ; { core = Internal B.Int }] ->
            proc_op "isint" [x]
        | B.Conj,      [e1 ; e2]
        | B.Disj,      [e1 ; e2]
        | B.Equiv,     [e1 ; e2]
        | B.Eq,        [e1 ; e2] -> naryop op es
        | B.Implies,   [e1 ; e2] -> naryop op es ~sep:"\n\t\t"
        | B.Neg,       [ex]      -> naryop op es
        | B.Mem,       [e1 ; e2] -> proc_op "tla_in" es
        | B.DOMAIN,    [f]       -> proc_op "tla_domain" es

        | B.Plus,      [e1 ; e2]
        | B.Minus,     [e1 ; e2]
        | B.Times,     [e1 ; e2]
        | B.Exp,       [e1 ; e2]
        (* | B.Ratio,     [e1 ; e2]  *)
        | B.Lt,        [e1 ; e2]
        | B.Lteq,      [e1 ; e2]
        | B.Gt,        [e1 ; e2]
        | B.Gteq,      [e1 ; e2] -> arith_op op es
        (* | B.Quotient,  [e1 ; e2] -> add_tla_op (m.op op) ; arith_op op es *)
        (* | B.Remainder, [e1 ; e2] -> add_tla_op (m.op op) ; arith_op op es *)
        | B.Quotient,  [e1 ; e2] -> add_tla_op (m.op op) ; arith_op op es
        | B.Remainder, [e1 ; e2] -> add_tla_op (m.op op) ;
            (* If (noprops (List (And, [Apply (noprops (Internal B.Mem), [e1 ; (noprops Internal B.Int)]) ;
                                     Apply (noprops (Internal B.Mem), [e2 ; (noprops Internal B.Int)])])),
                e,) *)
                arith_op op es
        | B.Range,     [e1 ; e2] -> proc_op "tla_range" es
        | B.Uminus,    [ex] when fmt_as_int e -> output (m.uminus (to_smt cx ex))
        | B.Uminus,    [ex] -> add_tla_op "tla_uminus" ; output (unop cx "tla_uminus" ex)

        | B.Seq,       [ex]     -> proc_op "Seq" es
        | B.Len,       [ex]     -> output (proc_op "Len" es)
        | B.SubSeq,    [ex;m;n] -> proc_op "SubSeq" es
        | B.Head,      [ex]     -> proc_op "Head" es
        | B.Tail,      [ex]     -> proc_op "Tail" es
        | B.BSeq,      [ex]     -> proc_op "BSeq" es
        | B.Cat,       [e1;e2]  -> proc_op "Cat" es
        | B.Append,    [e1;e2]  -> proc_op "Append" es
        | B.SelectSeq, [e1;e2]  -> proc_op "SelectSeq" es

        | _ ->
            Errors.set (Internal op @@ e) "smt2.ml: Arity mismatch";
            Util.eprintf ~at:(Internal op @@ e) "Arity mismatch" ;
            failwith "Backend.Smt.Smt.to_smt"
        end
    | String s when is_Fld e -> add_field s ; add_field_prefix s
    | String s -> add_string s ; add_tla_op "str2u" ; strify (mk_string s)
    | Internal B.TRUE  -> m.op B.TRUE
    | Internal B.FALSE -> m.op B.FALSE
    | List (And, es) -> naryop B.Conj es ~sep:"\n\t"
    | List (Or, es)  -> naryop B.Disj es ~sep:"\n\t"
    | Quant (q, ((_, _, No_domain) :: _ as bs), ex) ->
        let bs = map (fun (h, k, d) -> (fof_id_vars true h.core) @@ h, k, d) bs in
        m.quant q (map
          begin fun (v,_,_) ->
            smt_id v.core,
            if (* fmt_as_int v || *) typ v = Some Int then SInt
            else (if is_Fld v then SField else U)
          end
          bs) (to_smt (add_bs_ctx bs cx) ex)
    | SetEnum [] -> add_tla_op "emptyset" ; "emptyset"
    | Record ses ->
        let fs,es = split ses in
        let id = sprintf "record__%d" (add_record_id fs) in
        iter add_tla_op (id :: fs) ;
        apply id es
    | Tuple [] -> add_tla_op "tuple0" ; "tuple0"
    | Tuple es ->
        (* let n = length es in *)
        (* add_tuple n ; *)
        (* apply ("tuple"^(string_of_int n)) es *)
        add_tuple (map (fun e -> if typbot e = Int then Int else Bot) es) ;
        apply (tuple_id (map (fun e -> if fmt_as_int e then Int else Bot) es)) es
    | Num (n, "") ->
        let n' = int_of_string n in
        let n = if n' < 0 then m.uminus (string_of_int (n'*(-1))) else n in
        add_num n ;
        output n
    | Internal B.Nat -> add_tla_op "tla_Nat" ; "tla_Nat"
    | Internal B.Int -> add_tla_op "tla_Int" ; "tla_Int"
    | Internal B.Infinity -> add_tla_op "tla_Infinity" ;
        if apply_int2u e
        then (add_tla_op "int2u" ; m.apply "int2u" "" ["tla_Infinity"])
        else "tla_Infinity"
    | If (c, t, f) ->
        let op = match m.ite with
        | Some s -> s
        | None -> Util.eprintf ~at:e "SMT backend translation error. Cannot process the IF-THEN-ELSE expression@\n%a"
	        (print_prop ()) e ; assert false
        in
        output (apply op [c ; t ; f] ~sep:"\n\t")
    | _ ->
        Util.eprintf ~at:e "SMT backend translation error. Cannot process the expression@\n%a" (print_prop ()) e ;
        assert false
;;

let build_tla_ops smap tuples record_ids =
    (* let smap = match !mode with Yices -> yices_map | Spass -> dfg_map | Fof -> fof_map | _ -> smtlib_map in *)
    (* let op o = smap.op o in *)
    let app op es = smap.apply op "" es in
    let nop op es =
      if !mode = Fof && fixity op = Infix
      then sprintf "(%s)" (String.concat (smap.op op) es)
      else app (smap.op op) es
    in
    let app1 op x = smap.apply op "" [x] in
    let app2 op x y = smap.apply op "" [x ; y] in
    let app2_op o x y = app2 (smap.op o) x y in
    let mem x y     = app "tla_in" [x ; y] in
    let implies x y = nop B.Implies [x ; y] in
    let eq x y      = nop B.Eq [x ; y] in
    let equiv x y   = nop B.Equiv [x ; y] in
    let lt x y      = nop B.Lt [x ; y] in
    let leq x y     = nop B.Lteq [x ; y] in
    let lAnd xs     = nop B.Conj xs in
    let isint x     = app "isint" [x] in
    let int2u x     = if !mode = Spass || !mode = Fof then x else app "int2u" [x] in
    let str2u x     = if !mode = Spass || !mode = Fof then x else app "str2u" [x] in
    let fcnapp1 f x = app2 "fcnapp1_u" f x in
    let dom e       = smap.apply "tla_domain" "" [e] in
    let forall      = smap.quant Forall in
    let exists      = smap.quant Exists in
    let pattern e ps = match !mode with Spass | Fof | Yices -> e | _ -> sprintf "(! %s :pattern (%s))" e (String.concat " " ps) in
    (* let pattern e ps = e in *)
    let m = "M_"^fresh_id () in
    let n = "N_"^fresh_id () in
    let x = "X_"^fresh_id () in
    let y = "Y_"^fresh_id () in
    let z = "Z_"^fresh_id () in
    let s = "S_"^fresh_id () in
    let t = "T_"^fresh_id () in
    let i = "I_"^fresh_id () in

    let cond_arith_op      sop top = forall [x,U ; y,U] (implies (lAnd [isint x ; isint y]) (eq    (app2 sop x y) (app2_op top x y))) in
    let cond_arith_op_bool sop top = forall [x,U ; y,U] (implies (lAnd [isint x ; isint y]) (equiv (app2 sop x y) (app2_op top x y))) in
    let tla_ops_fof = [
        "tla_Int",   [], U,    [ forall [x,U] (implies (mem x "tla_Int") (isint x)) ], ["tla_in";"isint"] ;
        "tla_Nat",   [], U,    [ forall [x,U] (implies (mem x "tla_Nat") (lAnd [isint x ; leq "0" x])) ], ["tla_in";"isint"] ;
        "tla_plus",  [U;U], U, [ cond_arith_op "tla_plus"  B.Plus ], [] ;
        "tla_minus", [U;U], U, [ cond_arith_op "tla_minus" B.Minus ], [] ;
        "tla_times", [U;U], U, [ cond_arith_op "tla_times" B.Times ], [] ;
        "tla_exp",   [U;U], U, [ cond_arith_op "tla_exp"   B.Exp ], [] ;
        "tla_div",   [U;U], U, [ cond_arith_op "tla_div"   B.Quotient ], [smap.op B.Quotient] ;
        "tla_mod",   [U;U], U, [ cond_arith_op "tla_mod"   B.Remainder ], [smap.op B.Remainder] ;
        "tla_lt",    [U;U], SBool, [ cond_arith_op_bool "tla_lt"  B.Lt ], [] ;
        "tla_leq",   [U;U], SBool, [ cond_arith_op_bool "tla_leq" B.Lteq ], [] ;
        "tla_gt",    [U;U], SBool, [ cond_arith_op_bool "tla_gt"  B.Gt ], [] ;
        "tla_geq",   [U;U], SBool, [ cond_arith_op_bool "tla_geq" B.Gteq ], [] ;
        "tla_range", [U;U], U, [ forall [m,U ; n,U ; x,U]
					  (equiv (mem x (app2 "tla_range" m n))
					         (implies (lAnd [isint m ; isint n]) (lAnd [isint x ; leq m x ; leq x n]))) ], ["tla_in";"isint";"tla_range"] ;
        "tla_uminus",[U], U,   [ forall [n,U] (implies (isint n) (eq (app1 "tla_uminus" n) (smap.uminus n))) ], [] ;
        "div",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt ; z,SInt]
					  (implies (lt "0" y)
					           (equiv (eq (smap.apply "div" "" [x ; y]) z)
                            (lAnd [ leq (app2_op B.Times y z) x ;
                                        leq x (app2_op B.Times y (app2_op B.Plus z "1"))]))) ], [] ;
        "mod",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt]
					  (implies (lt "0" y)
					           (eq (smap.apply "mod" "" [x ; y])
					               (app2_op B.Minus x (app2_op B.Times (smap.apply "div" "" [x ; y]) y)) )) ], ["div"] ;
    ] in

    let tla_ops_spass = [
        "isint",     [U], SBool,[ forall [n,SInt] (isint n) ], ["tla_in"] ;
        "int2u",     [SInt], U, [ forall [x,SInt ; y,SInt] (implies (eq (int2u x) (int2u y)) (eq x y)) ], [] ;
        "str2u",     [SStr], U, [ forall [x,SStr ; y,SStr] (implies (eq (str2u x) (str2u y)) (eq x y)) ], [] ;
    ] @ tla_ops_fof
    in

    let int_lift sop top =
      forall [m,SInt ; n,SInt] (pattern
        (eq (app2 sop (int2u m) (int2u n))
            (int2u (app2_op top m n)))
        [app2 sop (int2u m) (int2u n)])
    in
    let int_lift2 sop top =
      forall [m,SInt ; n,SInt] (pattern
        (implies (lt "0" n)
          (eq (app2 sop (int2u m) (int2u n))
              (int2u (app2_op top m n))))
        [app2 sop (int2u m) (int2u n)])
    in
    let int_lift_bool sop top =
      forall [m,SInt ; n,SInt] (pattern
        (equiv (app2 sop (int2u m) (int2u n))
               (app2_op top m n))
        [app2 sop (int2u m) (int2u n)])
    in
    let tla_ops_smtlib = [
        "tla_Int",   [], U, [ forall [x,U] (pattern (implies (mem x "tla_Int") (exists [n,SInt] (eq x (int2u n))))  [mem x "tla_Int"]) ], ["tla_in";"int2u"] ;
        "tla_Nat",   [], U, [ forall [x,U] (pattern (implies (mem x "tla_Nat") (exists [n,SInt] (lAnd [eq x (int2u n) ; leq "0" n])))  [mem x "tla_Nat"]) ], ["tla_in";"int2u"] ;
        "tla_plus",  [U;U], U,     [ int_lift "tla_plus"  B.Plus ], ["int2u"] ;
        "tla_minus", [U;U], U,     [ int_lift "tla_minus" B.Minus ], ["int2u"] ;
        "tla_times", [U;U], U,     [ int_lift "tla_times" B.Times ], ["int2u"] ;
        "tla_exp",   [U;U], U,     [ int_lift "tla_exp"   B.Exp ], ["int2u"] ;
        "tla_div",   [U;U], U,     [ int_lift2 "tla_div"  B.Quotient ], ["int2u" ; smap.op B.Quotient] ;
        "tla_mod",   [U;U], U,     [ int_lift2 "tla_mod"  B.Remainder ], ["int2u" ; smap.op B.Remainder] ;
        "tla_lt",    [U;U], SBool, [ int_lift_bool "tla_lt"    B.Lt ],  ["int2u"] ;
        "tla_leq",   [U;U], SBool, [ int_lift_bool "tla_leq"   B.Lteq ],  ["int2u"] ;
        "tla_gt",    [U;U], SBool, [ int_lift_bool "tla_gt"    B.Gt ],  ["int2u"] ;
        "tla_geq",   [U;U], SBool, [ int_lift_bool "tla_gteq"  B.Gteq ],  ["int2u"] ;
        "tla_range", [U;U], U,  [ forall [m,SInt ; n,SInt ; z,U]
					  (implies (mem z (app2 "tla_range" (int2u m) (int2u n)))
					           (exists [x,SInt] (lAnd [eq z (int2u x) ; leq m x ; leq x n]))) ], ["tla_in";"int2u"] ;
        "tla_uminus",[U], U,      [ forall [n,SInt] (eq (app1 "tla_uminus" (int2u n)) (int2u (smap.uminus n))) ], ["int2u"] ;
        "isint",     [U], SBool,[ forall [n,SInt] (isint (int2u n)) ] @
                                [ forall [x,U] (pattern (implies (isint x) (exists [n,SInt] (eq x (int2u n)))) [isint x]) ],
                                (* [ forall [x,U] (implies (isint x) (exists [n,SInt] (eq x (int2u n)))) ],  (** CHECK: the pattern seems to choke the solver *) *)
                                    ["tla_in";"int2u"] ;
        "int2u",     [SInt], U, [ forall [x,SInt ; y,SInt] (implies (eq (int2u x) (int2u y)) (eq x y)) ], [] ;
        "str2u",     [SStr], U, [ forall [x,SStr ; y,SStr] (implies (eq (str2u x) (str2u y)) (eq x y)) ], [] ;
    ] @
    if !mode <> Z3 then begin [
        "div",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt ; z,SInt]
					  (implies (lt "0" y)
					           (equiv (eq (smap.apply "div" "" [x ; y]) z)
                            (lAnd [ leq (app2_op B.Times y z) x ;
                                        app (smap.op B.Lt) [x ; app2_op B.Times y (app2_op B.Plus z "1")]]))) ], [] ;
        "mod",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt]
					  (implies (lt "0" y)
					           (eq (smap.apply "mod" "" [x ; y])
					               (app2_op B.Minus x (app2_op B.Times (smap.apply "div" "" [x ; y]) y)) )) ], ["div"] ;
				] end else []
    in

    let tla_ops =
      (match !mode with Spass -> tla_ops_spass | Fof -> tla_ops_fof | _ -> tla_ops_smtlib) @ [
        (***  Operator name  X  argument sort list  X  return sort  X  associated axioms  X  dependent ops  *)
        "u2bool",    [U],   SBool, [], [] ;
        "tla_in",    [U;U], SBool, [], [] ;
        (* "tla_in",    [U;U], SBool, [ forall [s,U ; t,U] (implies (forall [x,U] (equiv (mem x s) (mem x t))) (eq s t)) ], [] ;   (** set extensionality *) *)
        "emptyset",  [],  U,     [ forall [x,U] (implies (mem x "emptyset") (smap.op B.FALSE)) ], ["tla_in"] ;
        "isAFcn",    [U], SBool, [
          forall [x,U ; y,U] (implies (lAnd [ app1 "isAFcn" y ; eq x y ]) (app1 "isAFcn" x)) ;
          forall [x,U ; y,U] (implies (lAnd [ app1 "isAFcn" x ; app1 "isAFcn" y ; eq x y ])
                                      (lAnd [ eq (dom x) (dom y) ;
                                              forall [z,U] (implies (mem z (dom x))
                                                                    (eq (fcnapp1 x z) (fcnapp1 y z))) ])) ], ["tla_domain";"fcnapp1_u"] ;
        "tla_domain",    [U],   U,  [ forall [s,U ; t,U] (implies (eq (dom s) t) (forall [x,U] (equiv (mem x (dom s)) (mem x t)))) ], ["tla_in"] ;
        "fcnapp1_u", [U;U], U,  [], [] ;
        "fcnapp1_s", [U;U], SStr,  [], [] ;
        (* "fcnapp1_u",  [U;U], U,  [ forall [x,U ; y,U] (lAnd [ eq (dom x) (dom y) ; forall [z,U] (implies (mem z (dom x)) (eq (fcnapp1 x z) (fcnapp1 y z)))]) ], ["tla_domain"] ;   (** function extensionatlity *) *)
        (* "fcnapp1_i", [U;U], SInt, [], [] ; *)
        "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U] (implies (exists [n,SInt] (eq (app2 "fcnapp1_i" x y) n)) (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y))) ], ["isint";"fcnapp1_u";"int2u"] ;
        (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U ; n,SInt] (implies (eq (app2 "fcnapp1_i" x y) n) (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y))) ], ["isint";"fcnapp1_u";"int2u"] ; *)
        (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U] (implies (isint ((app2 "fcnapp1_i" x y))) (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y))) ], ["isint";"fcnapp1_u";"int2u"] ; *)
        (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U] (eq (fcnapp1 x y) (int2u (app2 "fcnapp1_i" x y))) ], ["fcnapp1_u";"int2u"] ; *)
        "op_app1_u", [U;U], U,  [], [] ;
        "op_app1_i", [U;U], SInt,  [], [] ;
        "op_app1_s", [U;U], SStr,  [], [] ;
        "tla_dot_u", [U;SField], U, [], [] ;
        "tla_dot_i", [U;SField], SInt, [], [] ;
        "tla_dot_s", [U;SField], SStr, [], [] ;
        "isFldOf",   [SField;U], SBool, [ forall [m,SField ; x,U ; y,U] (implies (lAnd [ app2 "isFldOf" m y ; eq x y ]) (app2 "isFldOf" m x))  ], [] ;
        (* "tla_dot_b", [U;SField], SBool, [], [] ; *)
        "tuple0",    [],  U, [ forall [s,U] (equiv (eq s "tuple0") (eq (dom s) "emptyset")) ;
                               forall [s,U] (equiv (eq s "tuple0") (eq (app "Len" [s]) "0")) ;
                               ], ["tla_in";"tla_domain";"emptyset";"Len"] ;
        (* "Len",       [U], SInt, [ ], [] ; *)
        (* "Seq",       [U], U, [ forall [s,U ; x,U] (equiv (mem x (app1 "Seq" s))
                                                         (exists [n,SInt] (lAnd [
                                                                              eq n (app "Len" [s]) ;
                                                                              leq "0" n ;
                                                                              app1 "isAFcn" x ;
                                                                              eq (dom x) (app2 "tla_range" (int2u "1") (int2u n)) ;
                                                                              (* eq (dom x) (app2 "tla_range" (int2u "1") (int2u (app "Len" [s]))) ; *)
                                                                              (* forall [i,SInt] (implies (lAnd [leq "1" i ; leq i (app "Len" [s])]) (mem (fcnapp1 x (int2u i)) s)) ; *)
                                                                              forall [i,U] (implies (mem i (dom x)) (mem (fcnapp1 x i) s))
                                                                              ]))) ], ["tla_domain";"fcnapp1_u";"int2u";"isAFcn";"tla_range";"Len"] ; *)
        "Seq",       [U], U, [ (* forall [s,U ; t,U] (implies (mem s (app1 "Seq" t)) (eq (dom s) (app2 "tla_range" (int2u "1") (int2u (app "Len" [s]))))) ; *)
                               forall [s,U ; t,U] (equiv (mem s (app1 "Seq" t))
                                                          (lAnd [ leq "0" (app1 "Len" s) ;
                                                                  app1 "isAFcn" s ;
                                                                  (* app1 "isASeq" s ; *)
                                                                  eq (dom s) (app2 "tla_range" (int2u "1") (int2u (app "Len" [s]))) ;
                                                                  forall [i,SInt] (implies (lAnd [leq "1" i ; leq i (app "Len" [s])]) (mem (fcnapp1 s (int2u i)) t)) ;
                                                                  ])) ], ["Len";"tla_domain";"fcnapp1_u";"int2u";"isAFcn";(* "isASeq"; *)"tla_range"] ;

        "isASeq",    [U], SBool, [ forall [x,U ; y,U] (implies (lAnd [ app1 "isASeq" y ; eq x y ]) (app1 "isASeq" x)) ;
                                   forall [x,U] (implies (app1 "isASeq" x) (app1 "isAFcn" x)) ;
                                   forall [x,U] (implies (app1 "isASeq" x) (exists [n,SInt] (eq (dom x) (app2 "tla_range" (int2u "1") (int2u n))))) ;
                                   (* forall [x,U] (implies (app1 "isASeq" x)
                                        (lAnd [app1 "isAFcn" x ;
                                               exists [n,SInt] (eq (dom x) (app2 "tla_range" (int2u "1") (int2u n)))])) ; *)
                                   (* forall [x,U ; y,U] (implies (lAnd [ app1 "isASeq" x ; app1 "isASeq" y ; eq x y ])
                                                               (lAnd [ eq (dom x) (dom y) ;
                                                                       forall [z,U] (implies (mem z (dom x)) (eq (fcnapp1 x z) (fcnapp1 y z))) ]))  *)
                                  ],
                                 ["tla_domain";"tla_range";"fcnapp1_u"] ;

        "Len",       [U], SInt, [ forall [s,U;n,SInt] (implies (leq "0" n) (equiv (eq (dom s) (app2 "tla_range" (int2u "1") (int2u n)))
                                                                                  (eq (app1 "Len" s) n))) ;
                                  forall [s,U] (leq "0" (app1 "Len" s))
                                                            ], ["tla_domain";"tla_range";"int2u"] ;

        (* "Len",       [U], SInt, [ forall [x,U;s,U] (implies (eq x (app1 "Len" s))
                                                        (implies (exists [n,SInt] (lAnd [ leq "0" n ; eq (domain s)]))
                                                            (lAnd [ isint x ; leq (int2u "0") x ; eq (domain s) ...range... ])))
                                                            ], ["Seq";"tla_domain";"fcnapp1_u";"int2u"] ; *)
        (* "Len",       [U], SInt, [ forall [n,SInt ; s,U] (equiv (eq (app1 "Len" s) n)
                                                                 (lAnd [ leq "0" n ;
                                                                         forall [i,SInt] (equiv (mem (int2u i) (dom s)) (lAnd [leq "1" i ; leq i n ])) ])) ;
                                   (* forall [s,U ; x,U] (implies (mem x (app1 "Seq" s))
                                                                   (lAnd [ leq "0" (app1 "Len" x) ;
                                                                           forall [y,SInt] (equiv (mem (int2u y) (dom x)) (lAnd [leq "1" y ; leq y (app1 "Len" x)])) ;
                                                                           forall [i,SInt] (implies (lAnd [ leq "1" i ; leq i (app1 "Len" x) ])
                                                                                                   (mem (fcnapp1 x (int2u i)) s))])) *)
                                    ], ["Seq";"tla_domain";"fcnapp1_u";"int2u"] ; *)
        "SubSeq",    [U;U;U], U, [], [] ;
        (* "SubSeq",    [U;U;U], U, [ forall [s,U ; m,SInt ; n,SInt] (lAnd [
            forall [t,U] (implies (mem s (app1 "Seq" t)) (mem (app "SubSeq" [s ; int2u m ; int2u n]) (app1 "Seq" t))) ;
            forall [i,SInt] (equiv (mem (int2u i) (dom (app "SubSeq" [s ; int2u m ; int2u n])))
                                  (lAnd [leq "1" i ; leq i (app2_op B.Plus "1" (app2_op B.Minus n m)) ])) ;
            forall [i,SInt] (implies (mem (int2u i) (dom (app "SubSeq" [s ; int2u m ; int2u n])))
                                    (eq (fcnapp1 (app "SubSeq" [s ; int2u m ; int2u n]) (int2u i))
                                        (fcnapp1 s (int2u (app2_op B.Plus i (app2_op B.Minus m "1"))))))]) ], ["Seq";"tla_domain";"fcnapp1_u";"int2u"] ; *)
        "Head",      [U], U, [], [] ;
        "Tail",      [U], U, [], [] ;
        "BSeq",      [U], U, [], [] ;
        "Cat",       [U;U], U, [], [] ;
        "Append",    [U;U], U, [], [] ;
        "SelectSeq", [U;U], U, [], [] ;
        "tla_Infinity", [], SInt, [], [] ;
        ] @
        map (fun ts ->
            let mki i = "X__"^(string_of_int (i+1)) in
            let vs = mapi (fun i _ -> mki i, U) ts in
            (* let nts = combine ns ts in *)
            let t_id = sprintf "tuple_%s" (String.concat "" (map (function _ -> "u") ts)) in
            (* let t_id = sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) in *)
            (* let vs = map (fun (i,t) -> "x__"^i, t) nts in *)
            let es = mapi (fun i _ -> mki i) ts in
            (* let es2 = map (fun (i,t) -> if t = SInt then int2u ("x__"^i) else "x__"^i) nts in *)
            (* let nts = filter (fun (_,t) -> match t with SInt -> true | _ -> false) nts in *)
                t_id,
                (* ts,  *) map (fun _ -> U) ts,
                U,
                mapi (fun i _ -> forall vs (eq (mki i) (fcnapp1 (app t_id es) (int2u (string_of_int (i+1)))))) ts
                (* map (fun (i,t) -> forall vs (eq ("x__"^i) (app2 (match t with SInt -> "fcnapp1_i" | _ -> "fcnapp1_u") (app t_id es) (int2u i)))) nts, *)
                @ begin if !mode = Spass then
                mapi (fun i t ->
                    forall vs (eq (mki i)
                                  begin match t with Int -> int2u (app2 "fcnapp1_i" (app t_id es) (int2u (string_of_int (i+1))))
                                                   | _ -> "" (* app2 "fcnapp1_u" (app t_id es) (int2u i) *) end)) ts
                  else [] end
                ,
                ["int2u";"fcnapp1_u"] @ (if !mode = Spass then ["fcnapp1_i"] else []) )
            tuples
        (* @
        map (fun ts ->
            let n = length ts in
            let ns = map string_of_int (n_to_list n) in
            (* let vs = map (fun i -> "x__"^i, U) ns in *)
            let nts = combine ns ts in
            let t_id = sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) in
            let vs = map (fun (i,t) -> "x__"^i, type_to_SMTsort t) nts in
            (* let es = map (fun i -> "x__"^i) ns in *)
            let es2 = map (fun (i,t) -> if t = Int then int2u ("x__"^i) else "x__"^i) nts in
            (* let nts = filter (fun (_,t) -> match t with SInt -> true | _ -> false) nts in *)
                t_id,
                (* ts,  *) map (fun _ -> U) (n_to_list n),
                U,
                (* map (fun i -> forall vs (eq ("x__"^i) (fcnapp1 (app t_id es) (int2u i)))) ns @ *)
                (* map (fun (i,t) -> forall vs (eq ("x__"^i) (app2 (match t with SInt -> "fcnapp1_i" | _ -> "fcnapp1_u") (app t_id es) (int2u i)))) nts, *)
                (* map (fun (i,t) -> forall vs (eq ("x__"^i)
                                            begin match t with SInt -> int2u (app2 "fcnapp1_i" (app t_id es) (int2u i))
                                                              | _ -> app2 "fcnapp1_u" (app t_id es) (int2u i) end)) nts @ *)
                map (fun (i,t) -> forall vs (eq (if t = Int then int2u ("x__"^i) else "x__"^i)
                                                     (app2 "fcnapp1_u" (app t_id es2) (int2u i)))) nts,
                ["int2u";"fcnapp1_u";"fcnapp1_i"])
            tuples  *)
        @
        (* map (fun n ->
            let t_id = sprintf "tuple%d" n in
            let ns = map string_of_int (n_to_list n) in
            let vs = map (fun n -> "x__"^n, U) ns in
            let es = map (fun n -> "x__"^n) ns in
                t_id,
                map (fun _ -> U) (n_to_list n),
                U,
                map (fun i -> forall vs (eq ("x__"^i) (fcnapp1 (app t_id es) (int2u i)))) ns
                (* @ map (fun i -> forall vs (eq ("x__"^i) (int2u (app2 "fcnapp1_i" (app t_id es) (int2u i))))) ns *),
                ["int2u";"fcnapp1_u";"fcnapp1_i"])
            tuples
        @ *)
        concat
        (map (fun (fields,id) ->
            let mkf f = "X__"^f in
            let id = get_recid fields in
            let r_id = sprintf "record__%d" id in
            let fields = map add_field_prefix fields in
            let vs = map (fun f -> mkf f, U) fields in
            let es = map mkf fields in
            add_extrasort "tla_Field" ;
            [r_id, mapi (fun _ _ -> U) fields, U, [
                (* forall ((x,U)::vs) (equiv (eq x (app r_id es)) (lAnd (map (fun f -> eq (app "tla_dot_u" [x ; f]) ("x__"^f)) fields)))   (*** record extensionality *) *)
                ], ["tla_dot_u"]] @
            map (fun f ->
                f, [], SField,
                [ forall vs (eq (app "tla_dot_u" [app r_id es ; f]) (mkf f)) ],
                ["tla_dot_u"]
                ) fields
            ) (SSMap.bindings record_ids))
    in
    (* iter (fun o ->
        let deps = flatten (map (fun (o',_,_,_,deps) -> if o = o' then deps else []) tla_ops) in
        iter add_tla_op deps) (SSet.elements !tla_op_set) ; *)
    let rec fixp_add_deps () =
        let ops = SSet.elements !tla_op_set in
        iter (fun o ->
            let deps = flatten (map (fun (o',_,_,_,deps) -> if o = o' then deps else []) tla_ops) in
            iter add_tla_op deps)
            ops ;
        let ops' = SSet.elements !tla_op_set in
        if ops' <> ops then fixp_add_deps ()
    in
    fixp_add_deps () ;
    let tla_ops = filter (fun (id,_,_,_,_) -> List.mem id (SSet.elements !tla_op_set)) tla_ops in
    tla_ops
;;


(** Skolemization rule 1 (exists in hypothesis) *)
let rec deqexis cx hs c =
  let allbs h =
    match h.core with
    | Quant (Exists, ((_,_,No_domain) :: _ as bs), _) ->
        map (function (v,k,d) -> (remove (("sk_"^v.core) @@ v) boundvar, k, d)) bs
    | _ -> []
  in
  let bs = fold_left (fun bs h -> bs @ allbs h) [] hs in
  let n = length bs in
  let f h =
    match h.core with
    | Quant (Exists, ((_,_,No_domain) :: _ as bs'), ex) ->
        app_expr (shift (n - length bs')) ex
    | _ -> app_expr (shift n) h
  in
  let hs = hs
    |> fold_left (fun hs h -> (f h) :: hs) []
    |> rev in
  let c = c |> app_expr (shift n) in
  (add_bs_ctx bs cx, hs, c)
;;

(** Skolemization rule 2 (forall in conclusion) *)
let rec dequniv cx hs c =
  match c.core with
  | Quant (Forall, bs, c) ->
    (** "skc_" for name clash with other quantifiers in hyps *)
    let bs = bs |> map (function (v,k,dom) -> (remove (("skc_"^v.core) @@ v) boundvar, k, dom)) in
    let hs = hs |> map (app_expr (shift (length bs))) in
    let hs',c = deimpl c in
    dequniv (add_bs_ctx bs cx) (hs @ hs') c
  | _ -> cx, hs, c
;;

let rec proc_conc cx hs c =
  let pp c =
    let apply op e1 e2 = Apply (Internal op @@ c, [e1 ; e2]) @@ c in
    let eq e1 e2 = apply B.Eq e1 e2 in
    let implies e1 e2 = apply B.Implies e1 e2 in
    let tla_false = Internal B.FALSE @@ c in
    match c.core with
    | Apply ({core = Internal B.Neq}, ([x ; {core = SetEnum []}]
                                     | [{core = SetEnum []} ; x])) ->
        implies (eq x (noprops (SetEnum []))) tla_false
    | _ -> c
  in

  (* let hs,c = c
    |> deimpl
    |>> fun hs' -> hs @ hs'
  in *)
  let hs',c = deimpl c in
  let hs = hs @ hs' in
  let c = pp c in

  let hs',c = deimpl c in
  let hs = hs @ hs' in
  (* let cx,hs,c = proc_conc cx hs c in *)

  let cx,hs,c = dequniv cx hs c in
  (cx,hs,c)
;;

let preprocess_ob cx e =
  let get_assumptions ps =
    let rec proc_assumptions = function
      | (hyp,cx) :: hs ->
        begin match hyp.core with
        | Fact (e,Visible, _) ->
          (* rev *) (map (fun e -> (cx,e,length hs + 1)) (deconj e))
          @ proc_assumptions hs
        | Fresh (h,_,_,Bounded (dom,Visible)) ->
          let e, fact = fresh_bound_to_exp h dom in
          ((fact :: cx),e,length hs) :: proc_assumptions hs
        | _ -> proc_assumptions hs
        end
      | _ -> []
    in
    ps
    |> rev
    |> proc_assumptions
    |> rev
  in
  let cx,hyps,conc = proc_conc cx [] e in
  let prems = get_assumptions (preprocess_context cx)
    |> rev
    |> map (fun (cx,e,sh) -> app_expr (shift sh) e)
  in
  let hs,conc = (prems @ hyps, conc)
    |>> map (renameb cx)
    ||> renameb cx
    |>> map deconj
    |>> concat
  in

  let cx,hs,conc = deqexis cx hs conc in
  let hs = hs
    |> map begin fun e ->
         if is_term e then
           let e = assign e applyu2bool () in
           let e = assign_type e (Some Bool) in
           e
           (* Apply (noprops (Internal B.Equiv),
                  [e ; noprops (Internal B.TRUE)]) @@ e  *)
         else e
       end
  in

(* Printf.eprintf "================ 1 ==============\n" ;
iter (fun e -> (Printf.eprintf (if is_conc e then "CONC: " else "/\\    "));
  Util.eprintf "%a" (print_prop ()) (opaque cx e)) (hs @ [assign conc isconc ()]) ;
Printf.eprintf "----------------------------------\n" ; *)

  cx, hs @ [assign conc isconc ()]
;;

let process_excep excep cx e =
  let fst,msg,snd = begin match excep with
    | Failure msg              -> "Failure: ", msg,""
    | _                        -> "Error: ","unknown exception"," in"
    end in
  Util.eprintf "\n[SMT] %s %s %s \n %s" fst msg snd
    (Expr.Fmt.string_of_expr Deque.empty (opaque cx e))
;;

let rec fix ?feq:(xeq=Expr.Eq.expr) c f xs =
  let rec eqq xs ys = match xs, ys with
  | x :: xs, y :: ys -> if xeq x y then eqq xs ys else false
  | [], [] -> true
  | _ -> false
  in
  if c = 0 then (failwith "[SMT] Cannot reach fixpoint.\n") else
  (let ys = f xs in if eqq xs ys then xs else fix (c-1) f ys)
;;

(* let rec fixc c f x =
  (* let rec eq xs ys = match xs, ys with
  | x :: xs, y :: ys -> if Smtcommons.TC.eq x y then eq xs ys else false
  | [], [] -> true
  | _ -> false
  in *)
  if c = 0 then (failwith "[SMT] Cannot reach fixpoint.\n") else
  (let y = f x in if Typ_c.eq x y then x else fixc (c-1) f y)
;; *)

let apply_proc cx proc es : 'a list = es
  |> map (proc cx)
  |> filter Option.is_some
  |> map Option.get
;;

let normalize cx all : expr list =
  let proc_normalize cx e : expr option =
    try
(* Util.eprintf "Exp: %a" (print_prop ()) (opaque cx e) ; *)
    let e = Ground.gr1 cx e in
(* Util.eprintf "Gr0: %a" (print_prop ()) (opaque cx e) ; *)
    Some e
    with Failure _ as exc -> process_excep exc cx e ; None
  in
  all
  |> map (fun e -> if is_conc e then [e] else deconj e)
  |> concat
  |> map Ground.gr0
(* |> fun all -> iter (fun e -> Util.eprintf "---: %a" (print_prop ()) (opaque cx e)) all ; all *)
  |> kk (simplefacts := [])
  |> tap (iter (fun e -> if is_conc e then () else add_simplefact cx e))
  (* |> map (fun e -> if is_conc e then simp_simplefacts cx e else e) *)
  |> apply_proc cx proc_normalize
  |> map (fun e -> if is_conc e then [e] else deconj e)
  |> concat
;;

let abstract cx all =
  let all = map (Simpl.abstract cx) all in
  let nonb_ops = map
    begin fun (s,(cx',e)) ->
      (* let mc x = if is_conc e then assign (noprops x) isconc () else noprops x in *)
      let mc x = noprops x in
      let mb x = x |> mc <<< Some Bool in
      let d = length cx - length cx' in
      let e = if d > 0 then app_expr (shift d) e else e in
      let e = Apply (Internal B.Eq |> mb, [Opaque s |> mc <<< typ e ; (* opaque cx *) e]) |> mb in
      match (fix 10 (normalize cx) [e]) with [e] -> e | es -> List (And, es) |> mb
    end (SMap.bindings !nonbasic_ops)
  in
  (* let nonb_ops = map (Typeinfer.paint_types cx) nonb_ops in *)
  SMap.iter (fun k _ -> add_term k 0 U) !nonbasic_ops ;
  nonbasic_ops := SMap.empty ;
  (* all @ nonb_ops *)
  nonb_ops @ all
;;

let choose_det_axioms chooses =
    let chooses = map begin fun (v,(cx,e)) ->
        match e.core with
        | Choose (h,None,ex) -> v, (add_bs_ctx [h, Unknown, No_domain] cx,ex)
        | _ -> assert false
        end (SMap.bindings chooses)
    in
    map begin fun ((v1,(cx1,p1)),(v2,(cx2,p2))) ->
            let mk x = { p1 with core = x } in
            let p1 = opaque ~strong:true cx1 p1 in
            let p2 = opaque ~strong:true cx2 p2 in
            Apply (Internal B.Implies |> mk,
                   [ Quant (Forall, [fresh_name () |> mk, Unknown, No_domain],
                        Apply (Internal B.Equiv |> mk, [ Ground.gr1 cx1 p1 ; Ground.gr1 cx2 p2]) |> mk) |> mk ;
                     Apply (Internal B.Eq |> mk, [Opaque v1 |> mk ; Opaque v2 |> mk]) |> mk]) |> mk
        end (perms chooses)
;;

let assign_fmt cx all =
  let proc_assign_fmt cx e =
    if is_conc e then Some (Fmt.assign_fmt Bool cx e) else
    try Some (Fmt.assign_fmt Bool cx e)
    with Not_found | Invalid_argument _ | Failure _ ->
      Util.eprintf "[SMT Warning] Discarding hypothesis. You can provide a typing hypothesis for: %s\n"
        (Expr.Fmt.string_of_expr Deque.empty (opaque cx e)) ; None
  in
  all
  |> map (proc_assign_fmt cx)
  |> fun all -> (fold_right (fun e r -> match e with Some e -> (e::r) | None -> r) all [])
;;

let translate solver_map cx all =
  let proc_trans cx e =
    if is_conc e then
      try Some (to_smt cx e)
      with Failure _ as exc ->
        process_excep exc cx e ; failwith "SMT backend: wrong conclusion"
    else
      try Some (to_smt cx e)
      with Failure _ as exc -> process_excep exc cx e ; None
  in
  partition (fun e -> not (is_conc e)) all
  |>> apply_proc cx proc_trans
  |>> filter (fun x -> not (x = "true" || x = ""))
  ||> (fun cs -> if cs = [] then [assign (noprops (Internal B.TRUE)) isconc ()] else cs)
  ||> apply_proc cx proc_trans
;;

let fmt_expr ?fcncheck solver_map cx e =
  let fcncheck = match fcncheck with Some x -> x | _ -> false in
  ignore (fcncheck) ;

  (*** 1. Preprocess obligation 'e' where e == ASSUME assumps PROVE hyps => conc *)
  let cx,all = preprocess_ob cx e in

  (** [Experimental] New type inference algorithm. *)
  (* let tx = Sys.time () in
  ignore (Typ_system.solve cx all) ;
  ifprint 1 "** Total time: %5.3fs.\n" (Sys.time() -. tx) ; *)

(* let hyps,conc = [],["true"] in *)

  (*** 2. First type-inference, before the typing hypotheses are normalized *)
  (* let all = map Typ_system.boolify all in
  ignore (Typeinfer.type_inference cx all) ; *)

  let hyps,conc = all
    (* |> map (Smtcommons.unprime cx) *)
    |> map Typeinfer.boolify
    |> (fun all -> ignore (Typeinfer.type_inference cx all) ; all)
    |> map (Smtcommons.insert_intdiv_cond cx)
    |> map (Typeinfer.paint_types cx)
  (*** 2. Change to mode 'function application check' if asked *)
    (* |> map Ground.gr0 *)
    (* |> fun all -> if fcncheck then (map (fcnapp_obl cx) all) @ all else all *)
    (* |> fun all -> (map (fcnapp_obl cx) all) @ all
    |> fun all -> (let cs,all = partition is_conc all in
      assign
      begin match cs with
      | [] -> Internal B.TRUE |> noprops
      | [ex] -> assign ex isconc ()
      | _ -> List (And, cs) |> noprops
      end isconc () :: all) *)
  (*** 3. Simplify top-level equalities + Ground + deconj *)
    (* |> fun all -> begin
      Printf.eprintf "============== original proof obligation ============\n" ;
      iter (fun e -> Util.eprintf "%s%a" (if is_conc e then "CONC: " else "/\\    ")
            (print_prop ()) (opaque (* ~strong:true *) cx e)) all ;
      Printf.eprintf "-----------------------------------------------------\n" ;
      end ; all *)
    (* |> fix 10 (Simpl.simpl_eq cx) *)
    (* |> fix 10 (normalize cx) *)
    |> fix 10 (fun es -> normalize cx (Simpl.simpl_eq cx es))
  (*** 4. Expand bounded quantifiers + normalize *)
    |> fix 10 (map (Ground.unbound cx))
    |> fix 10 (fun es -> normalize cx (Simpl.simpl_eq cx es))
  (*** 5. Remove remaining non-basic operators *)
    |> fix 10 (abstract cx)
    |> fix 10 (map (Ground.unbound cx))
    |> fix 10 (fun es -> normalize cx (Simpl.simpl_eq cx es))
  (*** 6. Add choose determinacy axioms *)
    |> fun xs -> xs @ fix 10 (normalize cx) (choose_det_axioms !chooses)
    (* |> fun all -> begin
      ifprint 1 "============= normalized proof obligation ===========\n" ;
      iter (fun e -> ifprint 1 "%s%a" (if is_conc e then "=>  " else "/\\  ")
            (print_prop ()) (opaque (* ~strong:true *) cx e)) all ;
      ifprint 1 "-----------------------------------------------------\n" ;
      end ; all *)
  (*** 7. Type inference of normalized formulas, to assign types to new symbols like the unspecs *)
    |> map (Typeinfer.paint_types cx)
  (*** 8. Assign formatting properties to each expression *)
    |> assign_fmt cx
  (*** 9. Translate *)
    |> translate solver_map cx
  in

  let tla_ops = build_tla_ops solver_map !tuples !record_ids in
  let strings = map mk_string (SSet.elements !strings) in
  let fields = filter
    begin fun id -> not (mem id (map (fun (n,_,_,_,_) -> n) tla_ops)) end
    (SSet.elements !field_ids)
  in
  ( SSet.elements !extrasorts,
    sort ~cmp:(fun (x,_,_) (y,_,_) -> String.compare x y)
    (remove_repeated begin
      map (fun (id,sort,ret,_,_) -> id,sort,ret) tla_ops @
      map (fun id -> add_extrasort "tla_Field" ; id, [], SField) fields @
      map (fun (id,(ar,sort)) -> id, map (fun _ -> U) (n_to_list ar), sort) (SMap.bindings !terms) @
      map (fun n -> sprintf "fcnapp%d_u" n, map (fun _ -> U) (n_to_list (n+1)), U)    (ISet.elements !funs_u) @
      map (fun n -> sprintf "fcnapp%d_i" n, map (fun _ -> U) (n_to_list (n+1)), SInt) (ISet.elements !funs_i) @
      map (fun n -> sprintf "op_app%d_u" n, map (fun _ -> U) (n_to_list (n+1)), U)    (ISet.elements !ops_u) @
      map (fun n -> sprintf "op_app%d_i" n, map (fun _ -> U) (n_to_list (n+1)), SInt) (ISet.elements !ops_i) @
      map (fun s -> s, [], SStr) strings
    end),
    concat (map (fun (_,_,_,a,_) -> a) tla_ops),
    strings (* @ (SSet.elements !naryids) *),
    SSet.elements !nums,
    hyps,
    conc )
;;

let reset () =
  Smtcommons.reset ();
  terms        := SMap.empty ;
  funs_u       := ISet.empty ;
  funs_i       := ISet.empty ;
  ops_i        := ISet.empty ;
  ops_u        := ISet.empty ;
  strings      := SSet.empty ;
  nums         := SSet.empty ;
  extrasorts := SSet.singleton "u";
  tuples := [];
  funs_s := ISet.empty;
  ops_s := ISet.empty;
;;

let _fmt_smtlib fc cx e =
  reset () ;
  mode := Smtlib ;
  let sorts,functions,axioms,distincts,_,hyps,conc = fmt_expr ~fcncheck:fc smtlib_map cx e in
  let to_sort = smtlib_map.print_sort in
  String.concat "\n" begin
    [ "(set-logic AUFNIRA)" ] @
    map (sprintf "(declare-sort %s 0)") sorts @
    [";; Declaration of terms, predicates and strings"] @
    map (fun (f,xs,r) -> sprintf "(declare-fun %s (%s) %s)" f (String.concat " " (map to_sort xs)) (to_sort r)) functions @
    [";; Axioms"] @
    map (sprintf "(assert %s)") axioms @
    (if length distincts > 1 then [sprintf "(assert (distinct %s))" (String.concat " " distincts)] else []) @
    [";; Conclusion"] @
    map (sprintf "(assert (not %s))") conc @
    [";; Main assertions from the proof obligation"] @
    map (sprintf "(assert %s)") hyps @
    [ "(check-sat)" ;
      (* "(get-model)" ; *)
      "(exit)" ]
  end
;;
let fmt_smtlib cx e = _fmt_smtlib false cx e ;;   (** TESTING *)
let fmt_smtlib_fcncheck cx e = _fmt_smtlib true cx e ;;

let _fmt_z3 fc cx e =
  reset () ;
  mode := Z3 ;
  let sorts,functions,axioms,distincts,_,hyps,conc = fmt_expr ~fcncheck:fc smtlib_map cx e in
  let to_sort = smtlib_map.print_sort in
  String.concat "\n" begin
    [ "(set-option :print-success false)" ;
      (* "(set-option :print-warning false)" ; *)
      "(set-option :produce-models true)" ;
      (* "(set-option :produce-proofs true)" ; *)
      "(set-option :smt.pull-nested-quantifiers true)" ;
      "(set-option :auto-config false) " ;  (* disable automatic self configuration *)
      (*** Proving mode *)
      "(set-option :smt.mbqi true) " ; (* when true, enables model-based quantifier instantiation ; disables patterns *)
      (* "(set-option :smt.mbqi.max-iterations 1000)" ; *)
      (* "(set-option :relevancy 2)" ;   (** 0=disabled, use when searching counterexamples. *) *)
      (* "(set-option :ematching true)" ; *)
      (*** Model generation mode *)
      (* "(set-option :smt.mbqi false) " ; (* when true, enables model-based quantifier instantiation ; disables patterns *) *)
      (* "(set-option :model-compact true)" ; *)
       ] @
    map (sprintf "(declare-sort %s 0)") sorts @
    [";; Declaration of terms, predicates and strings"] @
    map (fun (id,xs,r) -> sprintf "(declare-fun %s (%s) %s)" id (String.concat " " (map to_sort xs)) (to_sort r)) functions @
    [";; Axioms"] @
    map (sprintf "(assert %s)") axioms @
    (if length distincts > 1 then [sprintf "(assert (distinct %s))" (String.concat " " distincts)] else []) @
    [";; Conclusion"] @
    map (sprintf "(assert (not %s))") conc @
    [";; Main assertions from the proof obligation"] @
    map (sprintf "(assert %s)") hyps @
    [ "(check-sat)" ;
      "(get-model)" ;
      "(exit)" ]
  end
;;
let fmt_z3 cx e = _fmt_z3 false cx e ;;
let fmt_z3_fcncheck cx e = _fmt_z3 true cx e ;;

let _fmt_yices fc cx e =
    reset () ;
    mode := Yices ;
    let sorts,functions,axioms,distincts,_,hyps,conc = fmt_expr ~fcncheck:fc yices_map cx e in
    let to_sort = yices_map.print_sort in
    String.concat "\n" begin
        (* [ "(reset)" ] @ *)
        map (sprintf "(define-type %s)") sorts @
        [";; Declaration of terms, predicates and strings"] @
        map (fun (id,xs,r) ->
            let s = map to_sort (xs @ [r]) in
            let s = if length s > 1 then sprintf "(-> %s)" (String.concat " " s) else String.concat " " s in
            sprintf "(define %s::%s)" id s) functions @
        [";; Axioms"] @
        map (sprintf "(assert %s)") axioms @
        map (sprintf "(assert %s)") (map (fun (x,y) -> sprintf "(not (= %s %s))" x y) (perms distincts)) @
        [";; Conclusion"] @
        map (sprintf "(assert (not %s))") conc @
        [";; Main assertions from the proof obligation"] @
        map (sprintf "(assert %s)") hyps @
        [ "(check)" ]
    end
;;
let fmt_yices cx e = _fmt_yices false cx e ;;
let fmt_yices_fcncheck cx e = _fmt_yices true cx e ;;

let _fmt_spass fc cx e =
    reset () ;
    mode := Spass ;
    let _,functions,axioms,distincts,_,hyps,conc = fmt_expr ~fcncheck:fc dfg_map cx e in
    let preds,funcs = partition (fun (_,_,r) -> r = SBool) functions in
    let axioms = axioms @ hyps @ map (fun (x,y) -> sprintf "not(equal(%s,%s))" x y) (perms distincts) in
    let tostr fs = fs
      |> map (fun (id,xs,_) -> sprintf "(%s,%d)" id (length xs))
      |> String.concat ", "
    in
    String.concat "\n" begin
        [ "begin_problem(foo)." ;
          "list_of_descriptions." ;
          "name({* bar *})." ;
          "author({* TLA+ Proof Manager *})." ;
          "status(unknown)." ;
          "description({* --- *})." ;
          "end_of_list." ;
          "" ;
          "list_of_symbols." ;
          ] @
        (if funcs <> [] then [ sprintf "functions[%s]."  (tostr funcs) ] else []) @
        (if preds <> [] then [ sprintf "predicates[%s]." (tostr preds) ] else []) @
        [ "end_of_list." ;
          "" ] @
        [ "list_of_formulae(axioms)." ] @
        (if axioms <> [] then map (sprintf "formula(%s).") axioms else []) @
        [ "end_of_list." ;
          "" ] @
        [ "list_of_formulae(conjectures)." ] @
        (if conc <> [] then map (sprintf "formula(%s).") conc else ["formula(true)."]) @
        [ "end_of_list." ;
          "" ;
          "end_problem." ]
    end
;;
let fmt_spass cx e = _fmt_spass false cx e ;;
let fmt_spass_fcncheck cx e = _fmt_spass true cx e ;;

let _fmt_tptp fc cx e =
    reset () ;
    mode := Fof ;
    let _,_,axioms,distincts,nums,hyps,conc = fmt_expr ~fcncheck:fc fof_map cx e in
    let axioms = axioms @ hyps @ map (fun (x,y) -> sprintf "%s != %s" x y) (perms distincts) in
    String.concat "\n" begin
        [ "% Author : TLA+ Proof Manager." ;
          ] @
        (if nums <> [] then mapi (fun i e -> sprintf "fof(n%d,axiom,isint(%s))." i e) nums else []) @
        (if axioms <> [] then mapi (fun i e -> sprintf "fof(a%d,axiom,%s)." i e) axioms else []) @
        (if conc <> [] then map (sprintf "fof(conc,conjecture,%s).") conc else ["fof(conc,conjucture,true)."])
    end
;;
let fmt_tptp cx e = _fmt_tptp false cx e ;;
let fmt_tptp_fcncheck cx e = _fmt_tptp true cx e ;;
