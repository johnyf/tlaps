(*
 * Copyright (C) 2008-2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 32507 $";;

let default_zenon_timeout = 10.
let default_isabelle_timeout = 30.
let default_isabelle_tactic = "auto";;
let default_yices_timeout = 30.
let default_z3_timeout = 5.
let default_cvc3_timeout = 5.
let default_smt_timeout = 5.
let default_smt2_timeout = 5.
let default_spass_timeout = 5.
let default_tptp_timeout = 5.

type t =
  | Isabelle of float * string
  | Zenon of float
  | SmtT of float
  | YicesT of float
  | Z3T of float
  | Cooper
  | Fail
  | Cvc3T of float
  | Smt2lib of float
  | Smt2z3 of float
  | Smt3 of float
  | Z33 of float
  | Cvc33 of float
  | Yices3 of float
  | Verit of float
  | Spass of float
  | Tptp of float
;;

let timeout m =
  match m with
  | Zenon f -> f
  | Isabelle (f, _) -> f
  | SmtT f -> f
  | Cvc3T f -> f
  | YicesT f -> f
  | Z3T f -> f
  | Smt2lib f -> f
  | Smt2z3 f -> f
  | Cooper | Fail -> infinity
  | Smt3 f -> f
  | Z33 f -> f
  | Cvc33 f -> f
  | Yices3 f -> f
  | Verit f -> f
  | Spass f -> f
  | Tptp f -> f

let scale_time m s =
  match m with
  | Zenon f -> Zenon (f *. s)
  | Isabelle (f, t) -> Isabelle (f *. s, t)
  | SmtT f -> SmtT (f *. s)
  | Cvc3T f -> Cvc3T (f *. s)
  | YicesT f -> YicesT (f *. s)
  | Z3T f -> Z3T (f *. s)
  | Smt2lib f -> Smt2lib (f *. s)
  | Smt2z3 f -> Smt2z3 (f *. s)
  | Cooper -> Cooper
  | Fail -> Fail
  | Smt3 f -> Smt3 (f *. s)
  | Z33 f -> Z33 (f *. s)
  | Cvc33 f -> Cvc33 (f *. s)
  | Yices3 f -> Yices3 (f *. s)
  | Verit f -> Verit (f *. s)
  | Spass f -> Spass (f *. s)
  | Tptp f -> Tptp (f *. s)
;;

open Format

let pp_print_tactic ff m =
  match m with
  | Isabelle (tmo, tac) -> fprintf ff "(isabelle %s %g)" tac tmo
  | Zenon f -> fprintf ff "(zenon %g s)" f
  | SmtT f -> fprintf ff "(smt %g s)" f
  | Cvc3T f -> fprintf ff "(cvc3 %g s)" f
  | YicesT f -> fprintf ff "(yices %g s)" f
  | Z3T f -> fprintf ff "(z3 %g s)" f
  | Smt2lib f -> fprintf ff "(smt2lib %g s)" f
  | Smt2z3 f -> fprintf ff "(smt2z3 %g s)" f
  | Smt3 f -> fprintf ff "(smt3 %g s)" f
  | Z33 f -> fprintf ff "(z33 %g s)" f
  | Cvc33 f -> fprintf ff "(cvc33 %g s)" f
  | Yices3 f -> fprintf ff "(yices3 %g s)" f
  | Verit f -> fprintf ff "(verit %g s)" f
  | Spass f -> fprintf ff "(spass %g s)" f
  | Tptp f -> fprintf ff "(tptp %g s)" f
  | Cooper -> fprintf ff "(cooper)"
  | Fail -> fprintf ff "(fail)"
;;

let pp_print_method ff meth =
  fprintf ff "@[<h>(*{ by %a }*)@]" pp_print_tactic meth
;;

let prover_meth_of_tac tac =
  match tac with
    | Isabelle (_, tac) -> (Some "isabelle", Some tac)
    | Zenon f -> (Some "zenon", None)
    | SmtT f -> (Some "smt", None)
    | Cvc3T f -> (Some "cvc3", None)
    | YicesT f -> (Some "yices", None)
    | Z3T f -> (Some "z3", None)
    | Smt2lib f -> (Some "smt2lib", None)
    | Smt2z3 f -> (Some "smt2z3", None)
    | Smt3 f -> (Some "smt3", None)
    | Z33 f -> (Some "z33", None)
    | Cvc33 f -> (Some "cvc33", None)
    | Yices3 f -> (Some "yices3", None)
    | Verit f -> (Some "verit", None)
    | Spass f -> (Some "spass", None)
    | Tptp f -> (Some "tptp", None)
    | Cooper -> (Some "cooper", None)
    | Fail -> (Some "fail", None)

type result =
  | Proved of string
  | Failed of string
  | Timedout
  | Interrupted
  | NotTried of string
;;
