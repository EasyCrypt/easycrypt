(** Phase 2.5 smoke. Spawns `ecd daemon` as a subprocess and
    exercises:
    - clean startup: pid file written; socket bound and accepts.
    - already-running rejection: second daemon with same label fails.
    - SIGTERM graceful shutdown: pid file removed; subprocess exits 0.
    - SIGKILL stale-cleanup: pid file remains; next daemon starts
      cleanly (Daemon_discovery.acquire detects stale and takes
      over).

    Self-contained: doesn't require ec llm binary. Tests the
    discovery + signal lifecycle in isolation. *)

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

let ecd_path () =
  (* Resolve to the in-tree _build path; falls back to PATH. *)
  let candidate =
    Filename.concat (Sys.getcwd ()) "_build/default/tooling/daemon/main.exe"
  in
  if Sys.file_exists candidate then candidate
  else begin
    let ic = Unix.open_process_in "command -v ecd 2>/dev/null" in
    let line = try Some (input_line ic) with End_of_file -> None in
    let _ = Unix.close_process_in ic in
    match line with
    | Some p when p <> "" -> p
    | _ ->
      Printf.eprintf "run_daemon_subcommand_smoke: cannot find ecd binary\n";
      exit 2
  end

let unique_label =
  Printf.sprintf "smoke-daemon-%d-%d"
    (Unix.getpid ())
    (int_of_float (Unix.gettimeofday ()))

let runtime_dir () =
  match Sys.getenv_opt "XDG_RUNTIME_DIR" with
  | Some d -> Filename.concat d "easycrypt-daemon"
  | None ->
    let tmp = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
    let uid = Unix.getuid () in
    Filename.concat tmp (Printf.sprintf "easycrypt-daemon-%d" uid)

let pid_file_for label =
  Filename.concat (runtime_dir ()) (label ^ ".pid")

let read_pid_file path =
  try
    let ic = open_in path in
    let line = input_line ic in
    close_in ic;
    Some (int_of_string (String.trim line))
  with _ -> None

let read_socket_from_pid_file path =
  try
    let ic = open_in path in
    let _ = input_line ic in
    let sock = input_line ic in
    close_in ic;
    Some (String.trim sock)
  with _ -> None

let socket_exists_via_pid_file label =
  match read_socket_from_pid_file (pid_file_for label) with
  | Some sock when sock <> "" ->
    (* AF_UNIX sockets show up via Sys.file_exists. *)
    Sys.file_exists sock
  | _ -> false

let wait_for cond ~deadline_s =
  let started = Unix.gettimeofday () in
  let rec loop () =
    if cond () then true
    else if Unix.gettimeofday () -. started > deadline_s then false
    else begin
      Unix.sleepf 0.05;
      loop ()
    end
  in
  loop ()

let spawn_ecd_daemon label =
  let bin = ecd_path () in
  Unix.create_process bin
    [| bin; "daemon"; "--label"; label |]
    Unix.stdin Unix.stdout Unix.stderr

let cleanup label =
  (* Try to remove the socket recorded in the pid file before
     removing the pid file itself. *)
  (match read_socket_from_pid_file (pid_file_for label) with
   | Some sock when sock <> "" -> (try Sys.remove sock with _ -> ())
   | _ -> ());
  (try Sys.remove (pid_file_for label) with _ -> ())

let () =
  let label = unique_label in
  at_exit (fun () -> cleanup label);

  Printf.printf "== Phase 2.5 ecd daemon smoke ==\n%!";

  (* Case 1 — clean startup. *)
  let pid1 = spawn_ecd_daemon label in
  let started =
    wait_for (fun () ->
      Sys.file_exists (pid_file_for label)
      && socket_exists_via_pid_file label)
      ~deadline_s:5.0
  in
  check "case 1 — daemon writes pid + socket files within 5s" started
    "files did not appear";
  let recorded_pid = read_pid_file (pid_file_for label) in
  check "case 1 — pid file holds spawned process pid"
    (recorded_pid = Some pid1)
    (Printf.sprintf "got %s, expected %d"
       (match recorded_pid with Some n -> string_of_int n | None -> "None")
       pid1);

  (* Case 2 — already-running rejection. *)
  let pid2 = spawn_ecd_daemon label in
  (* Wait for it to exit (should reject quickly). *)
  let _, status =
    let rec wait () =
      try Unix.waitpid [] pid2
      with Unix.Unix_error (Unix.EINTR, _, _) -> wait ()
    in
    wait ()
  in
  check "case 2 — second daemon exits"
    (match status with WEXITED _ | WSIGNALED _ -> true | WSTOPPED _ -> false)
    "second daemon did not exit";
  check "case 2 — second daemon exits with non-zero status"
    (match status with WEXITED n -> n <> 0 | _ -> true)
    "second daemon exited 0 — should have rejected";
  check "case 2 — original daemon's pid file still present"
    (Sys.file_exists (pid_file_for label)) "pid file gone after second start";

  (* Case 3 — SIGTERM graceful shutdown. *)
  Unix.kill pid1 Sys.sigterm;
  let exited =
    wait_for (fun () ->
      try
        let r, _ = Unix.waitpid [Unix.WNOHANG] pid1 in
        r <> 0
      with _ -> true)
      ~deadline_s:5.0
  in
  check "case 3 — SIGTERM causes exit within 5s" exited
    "daemon did not exit";
  check "case 3 — pid file cleaned up by atexit"
    (not (Sys.file_exists (pid_file_for label)))
    "pid file remained after graceful shutdown";

  (* Case 4 — SIGKILL leaves stale pid file; next daemon recovers. *)
  let pid3 = spawn_ecd_daemon label in
  let started3 =
    wait_for (fun () -> Sys.file_exists (pid_file_for label))
      ~deadline_s:5.0
  in
  check "case 4 — daemon restarts cleanly" started3 "pid file did not appear";
  Unix.kill pid3 Sys.sigkill;
  (* SIGKILL doesn't run atexit; pid file should remain. *)
  let _ =
    try ignore (Unix.waitpid [] pid3)
    with _ -> ()
  in
  Unix.sleepf 0.1;
  check "case 4 — SIGKILL leaves pid file (no graceful cleanup)"
    (Sys.file_exists (pid_file_for label))
    "pid file disappeared after SIGKILL";
  (* Spawn a fourth daemon; should detect stale + take over. *)
  let pid4 = spawn_ecd_daemon label in
  let started4 =
    wait_for (fun () ->
      Sys.file_exists (pid_file_for label)
      && (read_pid_file (pid_file_for label) = Some pid4))
      ~deadline_s:5.0
  in
  check "case 4 — fourth daemon takes over stale pid file" started4
    "fourth daemon did not claim the pid file";
  Unix.kill pid4 Sys.sigterm;
  let _ = wait_for (fun () ->
    try
      let r, _ = Unix.waitpid [Unix.WNOHANG] pid4 in
      r <> 0
    with _ -> true) ~deadline_s:5.0 in

  Printf.printf "\n== ecd daemon smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
