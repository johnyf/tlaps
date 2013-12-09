(*
 * fmtutil.ml --- format utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 30204 $";;

open Format

let pp_print_commasp ff () =
  pp_print_string ff "," ;
  pp_print_space ff ()

let rec pp_print_delimited ?(sep=pp_print_commasp) fmt ff = function
  | [] -> ()
  | [x] -> fmt ff x
  | x :: xs ->
      fmt ff x ;
      sep ff () ;
      pp_print_delimited ~sep:sep fmt ff xs

let rec pp_print_delimited_fold ?(sep=pp_print_commasp) fmt v ff = function
  | [] -> v
  | [x] -> fmt v ff x
  | x :: xs ->
      let v = fmt v ff x in
        sep ff () ;
        pp_print_delimited_fold ~sep:sep fmt v ff xs

let pp_print_with_parens af ff a =
  pp_print_string ff "(" ;
  af ff a ;
  pp_print_string ff ")"

module type Minimal_sig = sig

  module Prec : Pars.Intf.Prec  (* The functor's argument: precedences *)

  (** Associativity *)
  type assoc = Left | Right | Non

  (** Operators are an abstract representation of the operator
      component of a minimally parenthesized expression *)
  type op =
    | Infix of assoc * exp * exp
    | Prefix of exp
    | Postfix of exp

  (** The expression "view" contains enough information to produce a
      minimal parenthesization. Both [Big] and [Atm] are "atoms", but
      [Big] atoms are always parenthesized when they are operands of
      an operator. *)
  and exp =
    | Atm of fmt
    | Big of fmt
    | Op of fmt * Prec.prec * op

  and fmt = formatter -> unit

  (** Parenthesize the given [exp] on the given [formatter]. *)
  val pp_print_minimal : formatter -> exp -> unit
end

module  Minimal (Prec : Pars.Intf.Prec) = struct

  module Prec = Prec

  open Prec

  type assoc = Left | Right | Non

  type op =
    | Infix of assoc * exp * exp
    | Prefix of exp
    | Postfix of exp

  and exp =
    | Atm of fmt
    | Big of fmt
    | Op of fmt * prec * op

  and fmt = formatter -> unit

  let above p = function
    | Op (_, q, _) -> Prec.below q p
    | Big _ -> true
    | Atm _ -> false

  let overlaps p = function
    | Op (_, q, _) -> Prec.conflict p q
    | Big _ -> false
    | Atm _ -> false

  let assoc_of = function
    | Op (_, _, Infix (a, _, _)) -> a
    | _ -> Non

  let is_prefix = function
    | Op (_, _, Prefix _) -> true
    | _ -> false

  let is_postfix = function
    | Op (_, _, Postfix _) -> true
    | _ -> false

  let rec pp_print_minimal ff : exp -> unit =
    let go = function
      | Atm af -> af ff
      | Big af -> af ff
      | Op (af, ap, skel) -> begin
          match skel with
            | Prefix b ->
                pp_open_hbox ff () ;
                af ff ;
                (* pp_print_cut ff () ; *)
                if above ap b && not (is_prefix b) then
                  pp_print_with_parens pp_print_minimal ff b
                else
                  pp_print_minimal ff b ;
                pp_close_box ff ()
            | Infix (ass, b, c) ->
                pp_open_box ff 0 ;
                if above ap b || (overlaps ap b && not ((assoc_of b = Left) && (ass = Left))) then
                  pp_print_with_parens pp_print_minimal ff b
                else
                  pp_print_minimal ff b ;
                (* pp_print_space ff () ; *)
                 pp_print_space ff () ;
                af ff ;
                 pp_print_space ff () ;
                if above ap c || (overlaps ap c && not ((assoc_of c = Right) && (ass = Right))) then
                  pp_print_with_parens pp_print_minimal ff c
                else
                  pp_print_minimal ff c ;
                pp_close_box ff ()
            | Postfix b ->
                pp_open_hbox ff () ;
                if above ap b && not (is_postfix b) then
                  pp_print_with_parens pp_print_minimal ff b
                else
                  pp_print_minimal ff b ;
                af ff ;
                pp_close_box ff ()
        end
    in
      go
end
