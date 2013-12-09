(*
 * frontend/action.ml
 * The action frontend is responsible on transforming obligations containing
 * actions to purely first-order obligations
 * 1) expend definitions of UNCHANGED, [A]_v and <<A>>_v
 * 2) distribute primes over constant operators
 * 3) for a leibniz non-constant operator op, distribute primes over hash(op) (we
 * treat all non-constant operators right now, see comment below)
 * 4) primed atoms: constant atoms -> a, else -> hash(a)
 * 5) coalesce all non-leibniz operators and primed non-leibniz operators
 * (postponed, see comment below).
 *
 * comment:
 * this will be done only after we integrate the SANY parser to TLAPM as we dont
 * have the leibnizicy information right now in TLAPM.

 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 32093 $";;

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Proof.T
open Expr.Subst

module B = Builtin

let prime e = { e with core = Apply ({ e with core = Internal B.Prime }, [e]) }

let safe_prime e =
  match e.core with
    | Apply (op,l) ->
        begin match op.core with
          | Internal B.Prime ->   Errors.set e "commuting prime to the argument of a constant operator produced double priming";
              Util.eprintf ~at:e "commuting prime to the argument of a constant operator produced double priming";
              failwith "doubleprime"
          | _ -> prime e
        end
    | _ -> prime e

let prime_commute =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
    method expr scx e = match e.core with
      | Internal (B.Prime | B.Leadsto | B.ENABLED
                  | B.UNCHANGED | B.Cdot | B.Actplus
                  | B.Box _ | B.Diamond ) -> failwith
                  "Frontend.Action.prime_commute: primed temporal expression"
      | Opaque _ ->
          prime e
      | Ix n ->
          if n > Deque.size (snd scx) then
            Errors.bug ~at:e "Expr.Elab.prime_commute: unknown bound variable"
          else begin
            match Deque.nth ~backwards:true (snd scx) (n - 1) with
              | Some {core = Fresh (name, _, Constant, _)} -> e
              | Some {core = Fresh (name,_,_,_)} -> prime e
              | Some {core = Flex name} -> prime e
              | Some {core = Defn (df, _, _, _)} -> begin
                  match df.core with
                    | Operator (_, op) when Expr.Constness.is_const op ->
                        e
                    | _ ->
                        prime e
                end
              | Some h ->
                  Util.eprintf ~debug:"elab" ~at:h
                    "@[<v2>bad_hyp == @,%t@]@."
                    (fun ff -> ignore (Expr.Fmt.pp_print_hyp (snd scx, Ctx.dot) ff h)) ;
                  Errors.bug ~at:h
                    "Expr.Elab.prime_commute: invalid bound reference"
              | _ -> Errors.bug ~at:e "Expr.Elab.prime_commute: invalid bound reference"
          end
      (* in case he operand is non-temporal right now we propagate the primes to both since
       * we cannot get liebnizity information. When that information is
       * available, we would need to deal with this case here and do possibly coalescing
      | Apply (op, args) -> *)
      | Lambda _ ->
          Errors.bug ~at:e "Frontend.Action.prime_commute: encountered a naked LAMBDA"
      | ( Sequent _ | Let _ | Tquant _ | Tsub _ | Fair _ )
        -> prime e
      | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e

let prime_normalize =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
    method expr scx e = match e.core with
      | Apply ({ core = Internal B.Prime }, [e]) ->
          let e2 = prime_commute scx e in
          begin
            match e2.core with
              | Apply ({ core = Internal B.Prime }, _) -> e2
              | _ -> self#expr scx e2
          end
      | _ -> super#expr scx e

  end in
  fun scx e ->
    let ret = try visitor#expr scx e with
    | Failure msg ->
        Util.eprintf ~at:e
          "@[<v2>offending expr =@,%t@]@."
          (fun ff -> Expr.Fmt.pp_print_expr ((snd scx), Ctx.dot) ff e) ;
          prerr_string "Message: "; prerr_string msg;
        failwith msg
    in
    ret

type ctx = int Ctx.ctx
let dot : ctx = Ctx.dot
let bump : ctx -> ctx = Ctx.bump
let length : ctx -> int = Ctx.length



let cook x = "is" ^ pickle x

let adj cx v =
  let cx = Ctx.push cx (pickle v.core) in
  (cx, pickle (Ctx.string_of_ident (fst (Ctx.top cx))))

let rec adjs cx = function
  | [] -> (cx, [])
  | v :: vs ->
      let (cx, v) = adj cx v in
      let (cx, vs) = adjs cx vs in
      (cx, v :: vs)

let lookup_id cx n =
  assert (n > 0 && n <= Ctx.length cx) ;
  let id = Ctx.string_of_ident (fst (Ctx.index cx n)) in
  id

let crypthash (cx : ctx) e =
  let s =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    Expr.Fmt.pp_print_expr (Deque.empty, cx) fmt e ;
    Format.pp_print_flush fmt () ;
    Buffer.contents b
  in
  "hash'" ^ Digest.to_hex (Digest.string s)

(* TODO: we use _prime in order to name new variables but we need to use
 * a namespace mechanism for the generation of new names.
 * there is such a mechanism in the code but is not working well enough*)
let prime_replace str = Opaque (str ^ "_prime")

let eliminate_primes =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
    method expr scx e = match e.core with
      | Apply ({ core = (Internal B.Prime | Internal B.StrongPrime) }, args) ->
          let e2 = List.hd args in begin
        match args with
          | [{core = Ix n}] -> begin
            match Deque.nth ~backwards:true (snd scx) (n - 1) with
            | Some {core = Fresh (name,_,_,_)} -> {e2 with core = prime_replace
            name.core}
            | Some {core = Flex {core = name}} -> {e2 with core = prime_replace  name}
            | Some {core = Defn ({core = Operator (name,_)},_,_,_)} -> {e2 with core =
              prime_replace name.core }
            | _ -> failwith "Action.eliminate_primes: cannot find DB index"
          end
            (* TODO:
            since we cannot distinguish between leibniz and non-leibniz
            operators, we treat all of them as leibniz and we cannot obtain a
            primed application. We need to change distribute_primes to check for
            leibnizity and in case of non-leibniz, instead of prime-distribute,
            we jst need to return the primed application. In the prime
            elimination we need to coalesce the application
            *)
          | [{ core = Apply (op, args)}] -> failwith "Action.eliminate_primes: \
            should be impossible for now, see comment in code"
          | _ -> failwith "Action.eliminate_primes: unknown arguments for Prime"
      end
      | _ -> super#expr scx e

  end in
  fun scx e ->
    let ret = try visitor#expr scx e with
    | Failure msg ->
        Util.eprintf ~at:e
          "@[<v2>offending expr =@,%t@]@."
          (fun ff -> Expr.Fmt.pp_print_expr ((snd scx), Ctx.dot) ff e) ;
          prerr_string "Message: "; prerr_string msg;
        failwith msg
    in
    ret

let expand_prime_defs scx ob =
  let ob = Tla_norm.action_normalize scx ob in
  let ob = Tla_norm.unchanged_normalize scx ob in
  ob

let translate_primes scx ob =
  let ob = Expr.Constness.propagate#expr scx ob in
  let ob = prime_normalize scx ob in
  eliminate_primes scx ob

let coalesce_non_leibniz ob = ob

let process_eob ob =
  let cx = Deque.empty in
  let scx = ((),cx) in
  let ob = expand_prime_defs scx ob in
  let ob = translate_primes scx ob in
  let ob = coalesce_non_leibniz ob in
  ob

let process_obligation ob =
  match (process_eob (noprops (Sequent ob.obl.core))).core
  with
  | Sequent sq -> { ob with obl = { ob.obl with core = sq } }
  | _ -> failwith "Proof_prep.normalize"
