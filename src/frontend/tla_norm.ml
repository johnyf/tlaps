(*
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

open Ext
open Format
open Tla_parser
open Property

open Expr.T
module B = Builtin

let rec tuple_flatten e = match e.core with
  | Tuple es ->
      List.concat (List.map tuple_flatten es)
  | _ -> [e]

let unchanged e =
  let dest = e in
  Apply (Internal B.Eq @@ dest, [ Apply (Internal B.Prime @@ dest, [e]) @@ dest ; e ]) @@ dest

let rewrite_unch e =
  let dest = e in
  match tuple_flatten e with
    | [] -> Internal B.TRUE @@ dest
    | [e] -> unchanged e
    | es -> List (And, List.map unchanged es) @@ dest

let unchanged_normalize =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
    method expr scx e = match e.core with
      | Apply ({ core = Internal B.UNCHANGED }, [e]) ->
          rewrite_unch e
      | _ -> super#expr scx e
  end in
  fun scx e ->
    visitor#expr scx e

let action_normalize =
  let visitor = object (self : 'self)

    inherit [unit] Expr.Visit.map as super
    method expr scx e =
      let dest = e in
      match e.core with
        | Sub (Box, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply begin
              Internal B.Disj @@ dest,
              [ e ; Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest ]
            end @@ dest
        | Sub (Dia, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply begin
              Internal B.Conj @@ dest,
              [ e ;
                Apply begin
                  Internal B.Neg @@ dest,
                  [Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest]
                end @@ dest ;
              ]
            end @@ dest
        | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e
