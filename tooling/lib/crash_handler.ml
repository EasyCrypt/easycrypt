let dir_ref = ref None

let default_dir () =
  let home =
    try Sys.getenv "HOME"
    with Not_found -> "/tmp"
  in
  let xdg_cache =
    match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some d -> d
    | None -> Filename.concat home ".cache"
  in
  Filename.concat xdg_cache "easycrypt-daemon-crashes"

let crash_dir () =
  match !dir_ref with
  | Some d -> d
  | None -> default_dir ()

let ensure_dir d =
  let rec mkdir_p path =
    if Sys.file_exists path then ()
    else begin
      mkdir_p (Filename.dirname path);
      try Unix.mkdir path 0o700
      with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
    end
  in
  try mkdir_p d
  with _ -> ()

let signal_to_name n =
  if      n = Sys.sigsegv then "SIGSEGV"
  else if n = Sys.sigabrt then "SIGABRT"
  else if n = Sys.sigfpe  then "SIGFPE"
  else if n = Sys.sigbus  then "SIGBUS"
  else if n = Sys.sigill  then "SIGILL"
  else Printf.sprintf "signal:%d" n

let timestamp_str () =
  let t = Unix.gettimeofday () in
  let tm = Unix.gmtime t in
  Printf.sprintf "%04d%02d%02dT%02d%02d%02dZ"
    (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday
    tm.tm_hour tm.tm_min tm.tm_sec

let write_crash_log signum =
  let dir = crash_dir () in
  ensure_dir dir;
  let path =
    Filename.concat dir
      (Printf.sprintf "%s-pid%d.log" (timestamp_str ()) (Unix.getpid ()))
  in
  try
    let oc =
      open_out_gen [ Open_wronly; Open_creat; Open_excl ] 0o600 path
    in
    Printf.fprintf oc "easycrypt-daemon crash\n";
    Printf.fprintf oc "  pid:        %d\n" (Unix.getpid ());
    Printf.fprintf oc "  timestamp:  %s\n" (timestamp_str ());
    Printf.fprintf oc "  signal:     %s\n" (signal_to_name signum);
    Printf.fprintf oc "  backtrace:\n";
    let bt = Printexc.get_callstack 100 in
    Printf.fprintf oc "%s\n" (Printexc.raw_backtrace_to_string bt);
    close_out oc;
    Printf.eprintf "easycrypt-daemon: crash log written to %s\n%!" path
  with _ ->
    (* Best effort; if log-write fails we still want to die cleanly. *)
    Printf.eprintf
      "easycrypt-daemon: crash (signal %s); could not write log to %s\n%!"
      (signal_to_name signum) path

let crash_signals = [
  Sys.sigsegv;
  Sys.sigabrt;
  Sys.sigfpe;
  Sys.sigbus;
  Sys.sigill;
]

let install ?dir () =
  Printexc.record_backtrace true;
  (match dir with
   | Some d -> dir_ref := Some d
   | None -> if !dir_ref = None then dir_ref := Some (default_dir ()));
  ensure_dir (crash_dir ());
  List.iter (fun signum ->
    let handler = Sys.Signal_handle (fun n ->
      write_crash_log n;
      (* Re-raise: reset to default and re-raise so the process
         actually dies with the original signal. *)
      Sys.set_signal n Sys.Signal_default;
      Unix.kill (Unix.getpid ()) n)
    in
    try Sys.set_signal signum handler
    with _ -> ())
    crash_signals
