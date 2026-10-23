(* -------------------------------------------------------------------- *)
(* The session multiplexer behind [easycrypt mcp -sessions]. See
   [ecMcpMux.mli].

   One process, no engine: the multiplexer speaks MCP to the client and
   forwards every tool call to a child [easycrypt mcp] -- the
   single-engine server of [EcMcp], unchanged -- chosen by the
   [session] argument the call names. The first call naming a session
   starts its child; the children are independent engines, so agents
   work in parallel, each with its own loaded file, uuids and
   checkpoints.

   Why processes and not several [EcLlmCore] states in one process:
   the engine is single-threaded (one agent loading a large file would
   block every other session), the loader cache, prover configuration
   and Why3 processes are global, and a loaded engine holds memory that
   only a process exit gives back.

   Requests are served concurrently, one thread each. The threads do
   I/O and JSON and nothing else, so the runtime lock costs nothing:
   the invariants are one mutex per child (a child is synchronous, so
   calls to the same session serialise on it), one mutex for the
   client's stdout, and one for the session table. *)

module J = Yojson.Safe

open EcMcp

(* -------------------------------------------------------------------- *)
(* Session names double as log-file names, and travel to the child as
   nothing (the name is stripped before forwarding). A restricted
   alphabet keeps a name from being a path. *)
let valid_name (name : string) =
  name <> ""
  && String.length name <= 64
  && String.for_all
       (fun c ->
         (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
         || (c >= '0' && c <= '9') || c = '_' || c = '-' || c = '.')
       name

(* Raised while talking to a child that is gone, or going: the session
   is dropped and the caller told to start over. *)
exception Child_gone of string

(* -------------------------------------------------------------------- *)
(* One child engine. Every field but [last_used] and [dead] is set at
   spawn time; those two, and the channels, are touched under [lock]
   only -- except by [kill], which is the point of no return anyway. *)
type session = {
  name       : string;
  pid        : int;
  to_child   : out_channel;
  from_child : in_channel;
  log        : Unix.file_descr;
  lock       : Mutex.t;
  mutable last_used : float;
  mutable next_id   : int;
  mutable dead      : bool;      (* exit observed and reaped *)
}

(* The child's command line: our own executable, our own arguments
   minus the multiplexer's, so that loader and prover options reach the
   engine as they reached us. [Arg] accepts both [-idle 5] and
   [-idle=5]; strip both spellings. *)
let child_argv () : string array =
  let rec strip = function
    | [] -> []
    | "-sessions" :: rest -> strip rest
    | ("-idle" | "-logdir") :: _ :: rest -> strip rest
    | arg :: rest
      when String.starts_with ~prefix:"-idle=" arg
        || String.starts_with ~prefix:"-logdir=" arg -> strip rest
    | arg :: rest -> arg :: strip rest
  in
  match Array.to_list Sys.argv with
  | [] -> [| Sys.executable_name; "mcp" |]
  | _ :: args -> Array.of_list (Sys.executable_name :: strip args)

let now () = Unix.gettimeofday ()

(* Talking to a child. The caller holds [s.lock]. A child is
   synchronous, so the reply to a request is the next line carrying its
   id; anything else on the way (there should be nothing) is skipped. *)
let write_child (s : session) (msg : J.t) =
  try Wire.writer s.to_child msg with
  | Sys_error e -> raise (Child_gone e)
  | Unix.Unix_error (e, _, _) -> raise (Child_gone (Unix.error_message e))

let notify_child (s : session) (meth : string) =
  write_child s (`Assoc [("jsonrpc", `String "2.0"); ("method", `String meth)])

let request_child (s : session) (meth : string) (params : J.t) : J.t =
  let id = s.next_id in
  s.next_id <- id + 1;
  write_child s (`Assoc [
    ("jsonrpc", `String "2.0");
    ("id", `Int id);
    ("method", `String meth);
    ("params", params);
  ]);
  let rec read () =
    let line =
      try input_line s.from_child with
      | End_of_file -> raise (Child_gone "the engine exited")
      | Sys_error e -> raise (Child_gone e)
    in
    if String.trim line = "" then read ()
    else
      match J.from_string line with
      | exception _ -> read ()
      | `Assoc fields as reply ->
        (match List.assoc_opt "id" fields with
         | Some (`Int i) when i = id -> reply
         | _ -> read ())
      | _ -> read ()
  in
  read ()

(* Reap without blocking; once reaped, a child stays dead. *)
let alive (s : session) =
  if s.dead then false
  else
    match Unix.waitpid [Unix.WNOHANG] s.pid with
    | (0, _) -> true
    | _ -> s.dead <- true; false
    | exception Unix.Unix_error _ -> s.dead <- true; false

let kill (s : session) =
  let quietly f = try f () with _ -> () in
  quietly (fun () -> Unix.kill s.pid Sys.sigkill);
  quietly (fun () -> close_out s.to_child);
  quietly (fun () -> close_in s.from_child);
  quietly (fun () -> Unix.close s.log);
  if not s.dead then begin
    (* SIGKILL cannot be caught, so this returns at once. *)
    quietly (fun () -> ignore (Unix.waitpid [] s.pid));
    s.dead <- true
  end

(* Start the process and the pipes; the handshake is the caller's, so
   that it can run under the session's lock rather than the table's. *)
let spawn ~(logdir : string) (name : string) : session =
  let (child_in, our_out) = Unix.pipe ~cloexec:true () in
  let (our_in, child_out) = Unix.pipe ~cloexec:true () in
  let log =
    Unix.openfile
      (Filename.concat logdir (Printf.sprintf "ec-mcp-%s.log" name))
      [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND; Unix.O_CLOEXEC] 0o644
  in
  let pid =
    try
      Unix.create_process Sys.executable_name (child_argv ())
        child_in child_out log
    with e ->
      List.iter Unix.close [child_in; our_out; our_in; child_out; log];
      raise e
  in
  Unix.close child_in;
  Unix.close child_out;
  { name; pid; log;
    to_child   = Unix.out_channel_of_descr our_out;
    from_child = Unix.in_channel_of_descr our_in;
    lock       = Mutex.create ();
    last_used  = now ();
    next_id    = 1;
    dead       = false; }

let handshake (s : session) =
  let params =
    `Assoc [
      ("protocolVersion", `String protocol_latest);
      ("capabilities", `Assoc []);
      ("clientInfo", `Assoc [
         ("name", `String (server_name ^ "-sessions"));
         ("version", `String server_version);
       ]);
    ]
  in
  ignore (request_child s "initialize" params);
  notify_child s "notifications/initialized"

(* -------------------------------------------------------------------- *)
(* The multiplexer's own tools, appended to the child's table. *)
let mux_tools : J.t list = [
  `Assoc [
    ("name", `String "ec_sessions");
    ("description",
     `String "List the live EasyCrypt engine sessions of this server: \
              one line per session with its name, pid and idle time. \
              Sessions are created by the first tool call that names \
              them and killed by ec_close or after the idle timeout.");
    ("inputSchema", Schema.obj []);
    ("annotations", `Assoc [("readOnlyHint", `Bool true)]);
  ];
  `Assoc [
    ("name", `String "ec_close");
    ("description",
     `String "Kill the engine of the named session and forget it. Its \
              memory is released; the next call naming that session \
              starts a fresh engine, which needs an ec_load. Close your \
              own session when you are done with it, never another \
              agent's.");
    ("inputSchema",
     Schema.obj ~required:["session"] [
       ("session", Schema.str ~description:"the session to close" ());
     ]);
  ];
]

let tools : J.t list = tools_with_session @ mux_tools

(* -------------------------------------------------------------------- *)
let run (mcpopts : EcOptions.mcp_option) =
  if mcpopts.EcOptions.mcpo_help then begin
    print_usage ();
    exit 0
  end;

  let idle =
    60. *. float_of_int (Option.value mcpopts.EcOptions.mcpo_idle ~default:180)
  in
  let logdir =
    match mcpopts.EcOptions.mcpo_logdir with
    | Some dir -> dir
    | None ->
      match Sys.getenv_opt "TMPDIR" with
      | Some dir when dir <> "" -> dir
      | _ -> "/tmp"
  in

  (* A child that died between two of our writes must surface as an
     [EPIPE] we can report on that session, not as a signal that takes
     the whole server down. *)
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;

  let wire = wire_stdout () in
  let out_lock = Mutex.create () in
  let module Wire = Wire.Over (struct
    let send msg = Mutex.protect out_lock (fun () -> Wire.writer wire msg)
  end) in

  (* ------------------------------------------------------------------ *)
  (* The session table. *)
  let sessions : (string, session) Hashtbl.t = Hashtbl.create 8 in
  let table_lock = Mutex.create () in
  let with_table f = Mutex.protect table_lock f in

  (* Drop [s] if it is still the session registered under its name: a
     name can have been closed and re-created while a call on the old
     child was in flight, and that call must not take the new one down. *)
  let drop (s : session) =
    with_table (fun () ->
      match Hashtbl.find_opt sessions s.name with
      | Some s' when s' == s -> Hashtbl.remove sessions s.name
      | _ -> ());
    kill s
  in

  let close (name : string) =
    match with_table (fun () ->
        let s = Hashtbl.find_opt sessions name in
        Option.iter (fun _ -> Hashtbl.remove sessions name) s;
        s)
    with
    | None -> false
    | Some s -> kill s; true
  in

  (* Runs on the way out, possibly from a signal handler in a thread
     that holds the table lock: no lock here, the process is ending and
     a torn snapshot costs at most a child the pipe closes anyway. *)
  let kill_all () =
    let all = try Hashtbl.fold (fun _ s acc -> s :: acc) sessions [] with _ -> [] in
    List.iter kill all
  in

  (* Find the session, or start it. The table lock covers the lookup
     and the process start only; the handshake, which waits for the
     child to be ready, runs under the session's own lock so that a
     second call on the same new name queues behind it rather than
     stalling every other session. *)
  let get (name : string) : session =
    let (s, fresh) =
      with_table (fun () ->
        match Hashtbl.find_opt sessions name with
        | Some s when alive s -> (s, false)
        | stale ->
          Option.iter kill stale;
          let s = spawn ~logdir name in
          Hashtbl.replace sessions name s;
          Mutex.lock s.lock;
          (s, true))
    in
    if fresh then begin
      (* We hold [s.lock] from inside the table section above. *)
      match handshake s with
      | () -> Mutex.unlock s.lock
      | exception e -> Mutex.unlock s.lock; drop s; raise e
    end;
    s
  in

  (* ------------------------------------------------------------------ *)
  (* Children must not outlive us: on any exit we can see coming, kill
     them; on the ones we cannot (SIGKILL), they read EOF on their stdin
     and stop once their current command completes. *)
  at_exit kill_all;
  List.iter
    (fun signal ->
      Sys.set_signal signal (Sys.Signal_handle (fun _ -> exit 0)))
    [Sys.sigterm; Sys.sigint; Sys.sighup];

  (* The idle reaper: a session unused for [idle] and not mid-call. *)
  if idle > 0. then
    ignore (Thread.create (fun () ->
      while true do
        Thread.delay 60.;
        let stale =
          with_table (fun () ->
            Hashtbl.fold (fun name s acc ->
              if now () -. s.last_used > idle && Mutex.try_lock s.lock
              then (Mutex.unlock s.lock; name :: acc)
              else acc)
              sessions [])
        in
        List.iter (fun name -> ignore (close name)) stale
      done) ());

  (* ------------------------------------------------------------------ *)
  (* Tool results of our own. *)
  let text_result ?(is_error = false) text : J.t =
    `Assoc ([
      ("content", `List [`Assoc [("type", `String "text");
                                 ("text", `String text)]]);
    ] @ (if is_error then [("isError", `Bool true)] else []))
  in

  let list_sessions () =
    let rows =
      with_table (fun () ->
        Hashtbl.fold (fun name s acc -> (name, s) :: acc) sessions [])
      |> List.sort (fun (a, _) (b, _) -> compare a b)
      |> List.map (fun (name, s) ->
           Printf.sprintf "%s  pid %d  idle %ds%s" name s.pid
             (int_of_float (now () -. s.last_used))
             (if alive s then "" else "  (dead)"))
    in
    text_result (if rows = [] then "no live session" else String.concat "\n" rows)
  in

  (* A forwarded call. The child's [result] or [error] comes back to
     the client under the client's id; a child that dies under us is
     dropped, and the caller told so in a tool-level error. *)
  let forward id (tool : string) (args : (string * J.t) list) =
    let name =
      match List.assoc_opt "session" args with
      | Some (`String s) when String.trim s <> "" -> String.trim s
      | _ ->
        Wire.result id (text_result ~is_error:true
          "missing `session': name your own engine session (e.g. your \
           agent tag) in every call");
        raise Exit
    in
    if not (valid_name name) then begin
      Wire.result id (text_result ~is_error:true
        (Printf.sprintf
           "invalid session name `%s': use letters, digits, `_', `-' and \
            `.' only (at most 64 characters)" name));
      raise Exit
    end;
    let args = List.filter (fun (k, _) -> k <> "session") args in
    let params =
      `Assoc [("name", `String tool); ("arguments", `Assoc args)] in
    match
      let s = get name in
      Mutex.protect s.lock (fun () ->
        s.last_used <- now ();
        match request_child s "tools/call" params with
        | reply -> s.last_used <- now (); reply
        | exception e -> s.last_used <- now (); drop s; raise e)
    with
    | `Assoc fields ->
      (match List.assoc_opt "result" fields, List.assoc_opt "error" fields with
       | Some result, _ -> Wire.result id result
       | None, Some (`Assoc err) ->
         let code =
           match List.assoc_opt "code" err with
           | Some (`Int c) -> c | _ -> -32603
         and message =
           match List.assoc_opt "message" err with
           | Some (`String m) -> m | _ -> "error"
         in
         Wire.error ?data:(List.assoc_opt "data" err) id code message
       | _ ->
         Wire.result id (text_result ~is_error:true
           (Printf.sprintf "session `%s': malformed reply from the engine"
              name)))
    | _ -> assert false
    | exception Child_gone reason ->
      Wire.result id (text_result ~is_error:true
        (Printf.sprintf
           "session `%s': %s (the session was dropped; the next call \
            starts a fresh engine, ec_load again)" name reason))
    | exception Unix.Unix_error (e, fn, arg) ->
      Wire.result id (text_result ~is_error:true
        (Printf.sprintf "session `%s': cannot start the engine: %s (%s %s)"
           name (Unix.error_message e) fn arg))
  in

  let call_tool id (params : J.t option) =
    let name =
      match List.assoc_opt "name" (Args.of_params params) with
      | Some (`String s) -> s
      | Some _ -> raise (Invalid_params "`name' must be a string")
      | None   -> raise (Invalid_params "missing tool `name'")
    in
    let args = Args.arguments params in
    match name with
    | "ec_sessions" ->
      Wire.result id (list_sessions ())
    | "ec_close" ->
      (match List.assoc_opt "session" args with
       | Some (`String n) when close (String.trim n) ->
         Wire.result id (text_result (Printf.sprintf "closed %s" (String.trim n)))
       | Some (`String n) ->
         Wire.result id (text_result (Printf.sprintf "no session `%s'" (String.trim n)))
       | Some _ -> raise (Invalid_params "ec_close: `session' must be a string")
       | None ->
         raise (Invalid_params "ec_close: missing required argument `session'"))
    | _ ->
      (try forward id name args with Exit -> ())
  in

  (* ------------------------------------------------------------------ *)
  let request id (meth : string) (params : J.t option) =
    try
      match meth with
      | "initialize" -> Wire.result id (initialize_result params)
      | "ping"       -> Wire.result id (`Assoc [])
      | "tools/list" -> Wire.result id (`Assoc [("tools", `List tools)])
      | "tools/call" -> call_tool id params
      | _ ->
        Wire.error id e_method_not_found
          (Printf.sprintf "method not found: %s" meth)
    with
    | Invalid_params msg -> Wire.error id e_invalid_params msg
    | e ->
      (* A request thread must always answer: an exception that escaped
         everything above becomes an internal error, not a client that
         waits forever. *)
      Wire.error id (-32603)
        (Printf.sprintf "internal error: %s" (Printexc.to_string e))
  in

  let dispatch (msg : J.t) =
    match msg with
    | `List _ ->
      Wire.error `Null e_invalid_request
        "JSON-RPC batches are not supported by this protocol revision"
    | `Assoc fields ->
      let params = List.assoc_opt "params" fields in
      let id =
        match List.assoc_opt "id" fields with
        | None | Some `Null -> None
        | Some id           -> Some id
      in
      begin match List.assoc_opt "method" fields, id with
      | Some (`String meth), Some id ->
        ignore (Thread.create (fun () -> request id meth params) ())
      | Some (`String _), None -> ()      (* notifications *)
      | Some _, Some id ->
        Wire.error id e_invalid_request "`method' must be a string"
      | Some _, None -> ()
      | None, Some id ->
        Wire.error id e_invalid_request "missing `method'"
      | None, None -> ()
      end
    | _ ->
      Wire.error `Null e_invalid_request
        "a JSON-RPC message must be an object"
  in

  (* ------------------------------------------------------------------ *)
  begin try while true do
    let line = input_line stdin in
    if String.trim line <> "" then
      match J.from_string line with
      | exception _ ->
        Wire.error `Null e_parse_error "invalid JSON"
      | msg -> dispatch msg
  done with End_of_file -> () end;

  (* The client is gone: take the engines with us. [exit] runs
     [kill_all] through [at_exit]. *)
  exit 0
