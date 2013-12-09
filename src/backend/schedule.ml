(*
 * Copyright (C) 2012  Inria and Microsoft Corporation
 *)

(* scheduler for back-end provers *)

Revision.f "$Rev: 28687 $";;

open Unix;;

type task = int * (unit -> computation) list

and computation =
  | Immediate of bool    (* already computed, argument is success *)
  | Todo of command      (* must launch process *)

and command = {
  line : string;         (* shell command line *)
  timeout : float;       (* delay before running timec *)
  timec : timeout_cont;  (* function to call after timeout *)
  donec : result -> float -> bool;
    (* function to call when finished; float is time used; returns success *)
}

and timeout_cont = unit -> continue

and continue =
  | Timeout
  | Continue of timeout_cont * float

and result =
  | Finished
  | Stopped_kill
  | Stopped_timeout
;;

type process = {
  refid : int;
  pid : int;
  ofd : file_descr;
  start_time : float;
  dl : float;
  tc : timeout_cont;
  dc : result -> float -> bool;
  rest : (unit -> computation) list;
};;

let temp_buf = String.create 4096;;
let read_to_stdout fd =
  try
    let r = Unix.read fd temp_buf 0 (String.length temp_buf) in
    if r = 0 then raise End_of_file;
    output Pervasives.stdout temp_buf 0 r;
    flush Pervasives.stdout;
  with Unix_error _ -> raise End_of_file
;;

(* Take a computation, launch the process and return the corresponding
   [process] record. *)
let launch refid cmd t =
  System.harvest_zombies ();
  let (pid, out_read) = System.launch_process cmd.line in
  let start_time = gettimeofday () in
  {
    refid = refid;
    pid = pid;
    ofd = out_read;
    start_time = start_time;
    dl = start_time +. cmd.timeout;
    tc = cmd.timec;
    dc = cmd.donec;
    rest = t;
  }
;;

(* Launch the first process of [comps], if any. *)
let rec start_process refid comps =
  match comps with
  | [] -> []
  | comp :: t ->
     begin match comp () with
     | Immediate false -> start_process refid t
     | Immediate true -> []
     | Todo cmd -> [launch refid cmd t]
     end
;;

(* Kill the process (or not, if reason = Finished) and return the success
   code from its "done" continuation. *)
let kill_process now reason d =
  if reason <> Finished then System.kill_tree d.pid;
  close d.ofd;
  d.dc reason (now -. d.start_time)
;;

let kill_and_start_next now reason d =
  let success = kill_process now reason d in
  if success then [] else start_process d.refid d.rest
;;

let is_cc_in cc l =
  match cc with
  | [] -> false
  | [x] -> List.mem x l
  | _ -> assert false
;;

(* This function launches the proof tasks and calls their continuation
   functions when their deadlines expire and when they terminate.

   Note that this uses lists and is inefficient if there are
   many processes.  Optimize it if you have max_threads > 100.
*)
let run max_threads control tl =
  assert (max_threads >= 1);
  assert (max_threads < 100);
  let (cc, ccbuf) =
    match control with
    | None -> ([], System.make_line_buffer Unix.stdin)
    | Some fd -> ([fd], System.make_line_buffer fd)
  in
  let rec spin running tl cc =
    if tl <> [] && List.length running < max_threads then begin
      match tl with
      | [] -> assert false
      | (refid, comps) :: t -> spin (start_process refid comps @ running) t cc
    end else if running <> [] then begin
      let outs = List.map (fun x -> x.ofd) running in
      let dl = List.fold_left (fun x y -> min x y.dl) infinity running in
      let delay = max 0.0 (min (dl -. Unix.gettimeofday ()) 60.0) in
      let (ready, _, _) = Unix.select (cc @ outs) [] [] delay in
      let now = Unix.gettimeofday () in

      (* toolbox commands *)
      let tb_commands =
        if is_cc_in cc ready then System.read_toolbox_commands ccbuf else []
      in
      let rec f (r, c) cmds =
        match cmds with
        | [] -> (r, c)
        | System.Eof :: _ -> (r, [])
        | System.Killall :: _ ->
           List.iter (fun d -> ignore (kill_process now Stopped_kill d)) r;
           raise Exit;
        | System.Kill id :: rest ->
           let g d =
             if d.refid = id then
               kill_and_start_next now Stopped_kill d
             else
               [d]
           in
           let rr = List.flatten (List.map g r) in
           f (rr, c) rest
      in
      let (running, cc) = f (running, cc) tb_commands in

      (* deadlines *)
      let f d =
        if now >= d.dl then begin
          match d.tc () with
          | Timeout -> kill_and_start_next now Stopped_timeout d
          | Continue (tc, tmo) ->
             [ { d with tc = tc; dl = tmo +. d.start_time } ]
        end else
          [d]
      in
      let running = List.flatten (List.map f running) in

      (* outputs *)
      let f d =
        if List.mem d.ofd ready then begin
          try
            read_to_stdout d.ofd;
            [d]
          with End_of_file -> kill_and_start_next now Finished d
        end else
          [d]
      in
      let running = List.flatten (List.map f running) in

      spin running tl cc;
    end (* else we are done. *)
  in
  try
    spin [] tl cc;
    System.harvest_zombies ();
    false
  with Exit ->
    System.harvest_zombies ();
    true
;;
