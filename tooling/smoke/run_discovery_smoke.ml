(** Daemon-discovery smoke. Exercises the three lock states:
    - clean acquire when no pid file exists,
    - acquire on a stale pid file (dead pid) → cleans + takes it,
    - acquire when a live pid owns the file → returns Already_running.

    Uses a unique [label] per run so concurrent test invocations and
    real ecd daemons don't collide. *)

open Ecd_core

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

(* Produce a guaranteed-dead pid: fork a child that exits immediately,
   reap it, hand back its pid. The kernel may eventually recycle it,
   but for the test window it's reliably dead. *)
let dead_pid () =
  match Unix.fork () with
  | 0 -> exit 0
  | child ->
    let _ = Unix.waitpid [] child in
    child

let () =
  let label =
    Printf.sprintf "smoke-%d-%d" (Unix.getpid ())
      (int_of_float (Unix.gettimeofday ()))
  in
  let cleanup () = Daemon_discovery.release ~label () in
  at_exit cleanup;

  (* Always start clean. *)
  cleanup ();

  let socket_path = "/tmp/easycrypt-discovery-smoke.sock" in

  (* Case 1: no pid file. *)
  (match Daemon_discovery.acquire ~label ~socket_path () with
   | Acquired { pid_file; socket_path = sp } ->
     check "case 1 — clean acquire returns Acquired" true "";
     check "case 1 — pid file exists" (Sys.file_exists pid_file)
       (Printf.sprintf "expected %s to exist" pid_file);
     check "case 1 — socket round-trips" (sp = socket_path) sp
   | Already_running _ ->
     check "case 1 — clean acquire returns Acquired" false
       "got Already_running on a fresh label");

  (* Case 2: same process re-acquires → Already_running with our pid. *)
  (match Daemon_discovery.acquire ~label ~socket_path () with
   | Acquired _ ->
     check "case 2 — re-acquire by self returns Already_running" false
       "got Acquired despite live pid file"
   | Already_running { pid; socket } ->
     check "case 2 — re-acquire by self returns Already_running" true "";
     check "case 2 — reported pid is current process"
       (pid = Unix.getpid ())
       (Printf.sprintf "got pid=%d, expected %d" pid (Unix.getpid ()));
     check "case 2 — reported socket round-trips"
       (socket = Some socket_path)
       (match socket with
        | Some s -> Printf.sprintf "got %s" s
        | None -> "got None"));

  cleanup ();

  (* Case 3: stale pid file. Plant one with a dead pid, then acquire. *)
  let pf = Daemon_discovery.pid_file ~label () in
  let dead = dead_pid () in
  let oc = open_out pf in
  Printf.fprintf oc "%d\n%s\n" dead "/tmp/old.sock";
  close_out oc;
  check "case 3 — planted dead pid is recognized as not alive"
    (not (Daemon_discovery.pid_alive dead))
    (Printf.sprintf "pid_alive said true for pid %d" dead);
  (match Daemon_discovery.acquire ~label ~socket_path () with
   | Acquired { pid_file = pf'; _ } ->
     check "case 3 — stale acquire returns Acquired" true "";
     check "case 3 — pid file replaced"
       (Sys.file_exists pf')
       (Printf.sprintf "expected %s to exist" pf');
     (match Daemon_discovery.read ~label () with
      | Some (pid, sock) ->
        check "case 3 — file now records our pid"
          (pid = Unix.getpid ())
          (Printf.sprintf "got pid=%d" pid);
        check "case 3 — file now records new socket"
          (sock = Some socket_path)
          (match sock with Some s -> s | None -> "None")
      | None ->
        check "case 3 — file readable after acquire" false "read returned None")
   | Already_running { pid; _ } ->
     check "case 3 — stale acquire returns Acquired" false
       (Printf.sprintf "got Already_running pid=%d on stale file" pid));

  cleanup ();

  (* Case 4: pid_alive reports current process as alive. *)
  check "case 4 — pid_alive on self returns true"
    (Daemon_discovery.pid_alive (Unix.getpid ()))
    "self pid reported dead";
  check "case 4 — pid_alive on negative pid returns false"
    (not (Daemon_discovery.pid_alive (-1))) "rejected non-positive";

  Printf.printf "\n== discovery smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
