(*
 * module/gen.ml --- generation of obligations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 31530 $";;

open Ext
open Property

open Expr.T
open Expr.Subst
open Proof.T

open M_t

(*let debug = Printf.eprintf;;*)

let rec generate cx m =
  let obs : obligation list ref = ref [] in
  let emit ob = obs := ob :: !obs in
  let rsumm : summary ref = ref empty_summary in
  let fincx = ref Deque.empty in
  let rec visit cx mus = match mus with
    | [] ->
        fincx := cx ; []
    | mu :: mus -> begin
        match mu.core with
          | Theorem (nm, sq, naxs, prf, prf_orig, _) ->
             let cx = match nm with
                | Some nm ->
                    Deque.snoc cx (Defn (Operator (nm, exprify_sequent sq @@ nm) @@ mu, Proof, Visible, Export) @@ mu)
                | _ ->
                    cx
              in
              let prf, summ =
                let psq = if nm = None then sq else app_sequent (shift 1) sq in
                let psq = { psq with context = Deque.append cx psq.context } in
                Proof.Gen.reset_stats () ;
                let prf = Proof.Gen.generate psq prf in
                let (obs, prf) = Proof.Gen.collect prf in
                let sts = Proof.Gen.get_stats () in
                let summ = { sum_total = sts.Proof.Gen.total
                           ; sum_absent = (List.length sts.Proof.Gen.absent, sts.Proof.Gen.absent)
                           ; sum_omitted = (List.length sts.Proof.Gen.omitted, sts.Proof.Gen.omitted)
                           ; sum_suppressed = (List.length sts.Proof.Gen.suppressed, sts.Proof.Gen.suppressed)
                           } in
                  List.iter emit obs ;
                  prf, summ in
                rsumm := cat_summary !rsumm summ ;
                let mu = { mu with core = Theorem (nm, sq, naxs, prf, prf_orig, summ) } in
                let he = if nm = None then exprify_sequent sq else Ix 1 in
                let cx = Deque.snoc cx (Fact (he @@ mu, Hidden) @@ mu) in
                  mu :: visit cx mus
          | Submod m ->
              let (m, obs, summ) = generate cx m in
                List.iter emit obs ;
                rsumm := cat_summary !rsumm summ ;
                (Submod m @@ mu) :: visit cx mus
          | Mutate (uh, us) ->
              let (cx, obs) = Proof.Gen.mutate cx uh (us @@ mu) in
                List.iter emit obs ;
                mu :: visit cx mus
          | Anoninst _ ->
              Errors.bug ~at:mu "Module.Gen.generate: unnamed INSTANCE"
          | _ ->
              let cx = Deque.append_list cx (hyps_of_modunit mu) in
                mu :: visit cx mus
      end
  in
  let body = visit cx m.core.body in
    ({ m with core = { m.core with body = body } }, List.rev (!obs), !rsumm)
