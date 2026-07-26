type acquired = {
  pid_file : string;
  socket_path : string;
}

type acquire_result =
  | Acquired of acquired
  | Already_running of { pid : int; socket : string option }

let runtime_dir () =
  let base =
    match Sys.getenv_opt "XDG_RUNTIME_DIR" with
    | Some d -> Filename.concat d "easycrypt-daemon"
    | None ->
      let tmp =
        try Sys.getenv "TMPDIR" with Not_found -> "/tmp"
      in
      let uid = Unix.getuid () in
      Filename.concat tmp (Printf.sprintf "easycrypt-daemon-%d" uid)
  in
  (try Unix.mkdir base 0o700
   with Unix.Unix_error (EEXIST, _, _) -> ());
  base

let pid_file ?(label = "default") () =
  Filename.concat (runtime_dir ()) (label ^ ".pid")

let pid_alive pid =
  if pid <= 0 then false
  else
    try Unix.kill pid 0; true
    with
    | Unix.Unix_error (Unix.ESRCH, _, _) -> false
    (* EPERM means the process exists but we don't have permission to
       signal it — treat as alive for discovery purposes. *)
    | Unix.Unix_error (Unix.EPERM, _, _) -> true
    | Unix.Unix_error (_, _, _) -> false

let read ?(label = "default") () =
  let pf = pid_file ~label () in
  if not (Sys.file_exists pf) then None
  else
    try
      let ic = open_in pf in
      let line1 = input_line ic in
      let line2 =
        try Some (input_line ic) with End_of_file -> None
      in
      close_in ic;
      let pid = int_of_string (String.trim line1) in
      let sock =
        match line2 with
        | Some s ->
          let s = String.trim s in
          if s = "" then None else Some s
        | None -> None
      in
      Some (pid, sock)
    with _ -> None

let write_atomic path ~pid ~socket =
  let tmp = path ^ ".tmp" in
  let oc =
    open_out_gen
      [ Open_wronly; Open_creat; Open_trunc ] 0o600 tmp
  in
  output_string oc (Printf.sprintf "%d\n%s\n" pid socket);
  close_out oc;
  Sys.rename tmp path

let release ?(label = "default") () =
  let pf = pid_file ~label () in
  try Sys.remove pf with _ -> ()

let acquire ?(label = "default") ~socket_path () =
  let pf = pid_file ~label () in
  match read ~label () with
  | Some (pid, sock) when pid_alive pid ->
    Already_running { pid; socket = sock }
  | _ ->
    (* No file, malformed file, or stale (dead) pid: take it. *)
    write_atomic pf ~pid:(Unix.getpid ()) ~socket:socket_path;
    Acquired { pid_file = pf; socket_path }
