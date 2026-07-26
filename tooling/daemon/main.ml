(** `ecd` CLI — the tooling daemon's executable front-end. Phase 1
    currently ships a [drive] subcommand that exercises the session
    backend end-to-end against a real EasyCrypt file; later phases add
    LSP / MCP servers, pool management, and discovery wiring. *)

open Ecd_core

let version = "0.0.0+dev"

(* ---------------------------------------------------------------- *)
(* Helpers                                                            *)
(* ---------------------------------------------------------------- *)

let read_file path =
  let ic = open_in path in
  let n  = in_channel_length ic in
  let s  = really_input_string ic n in
  close_in ic;
  s

(* ---------------------------------------------------------------- *)
(* `ecd drive FILE`                                                   *)
(* ---------------------------------------------------------------- *)

let drive_file ~bin ~extra_args ~transcript_path file =
  let content = read_file file in
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let transcript =
    match transcript_path with
    | None -> Transcript.to_channel stderr
    | Some p ->
      let oc = open_out_gen [ Open_creat; Open_append; Open_wronly ] 0o644 p in
      at_exit (fun () -> try close_out oc with _ -> ());
      Transcript.to_channel oc
  in
  Transcript.configure transcript;
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin ~extra_args ();
  let s = Ec_llm_session.start ~sw ~label:"drive" in
  (* 1. Split the document into sentences via PARSE-JSON. *)
  let sentences =
    match Ec_llm_session.parse_source s content with
    | Ok ss -> ss
    | Error e ->
      Printf.eprintf "parse failed: %s\n%!" (Error.to_string e);
      exit 1
  in
  Printf.printf "drive: %s (%d sentences)\n%!" file (List.length sentences);
  (* 2. Step through each executable sentence, reporting class/uuid. *)
  let open Ec_llm_session in
  let exec_count = ref 0 in
  let first_ok_sid = ref None in
  List.iter
    (fun ps ->
       if ps.cls = `Meta then ()
       else
         let cls : [`Executable | `Doc_comment | `Directive] =
           match ps.cls with
           | `Executable -> `Executable
           | `Doc_comment -> `Doc_comment
           | `Directive -> `Directive
           | `Meta -> assert false
         in
         let corr =
           Correlation.of_client
             (Printf.sprintf "drive-%d" (!exec_count + 1))
         in
         match
           Ec_llm_session.exec s ~corr ~sentence_class:cls ~source:ps.src
         with
         | Ok ok ->
           incr exec_count;
           if Option.is_none !first_ok_sid then
             first_ok_sid := Some ok.sentence_id;
           Printf.printf
             "[%03d] %-11s %-14s uuid=%d%s\n%!"
             !exec_count
             (match cls with
              | `Executable -> "executable"
              | `Doc_comment -> "doc_comment"
              | `Directive -> "directive")
             ps.kind
             ok.replied_uuid
             (if ok.restarted then "  [restarted]" else "")
         | Error e ->
           Printf.eprintf "[%03d] FAIL %s: %s\n%!"
             (!exec_count + 1) ps.kind (Error.to_string e);
           exit 1)
    sentences;
  (* 3. Print final goals, then revert to the first executable
     sentence as a smoke of the revert path. *)
  (match Ec_llm_session.goals s with
   | Ok g -> Printf.printf "\nfinal goals payload: %d chars\n%!" (String.length g)
   | Error e ->
     Printf.eprintf "goals failed: %s\n%!" (Error.to_string e));
  (match !first_ok_sid with
   | None -> ()
   | Some sid ->
     match Ec_llm_session.revert_to s sid with
     | Ok () ->
       Printf.printf "revert to first sentence (%s) ok\n%!"
         (Sentence_id.to_string sid)
     | Error e ->
       Printf.eprintf "revert failed: %s\n%!" (Error.to_string e));
  Ec_llm_session.close s

(* ---------------------------------------------------------------- *)
(* Cmdliner plumbing                                                  *)
(* ---------------------------------------------------------------- *)

open Cmdliner

let default_bin () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> p
  | None ->
    let candidate = Filename.concat (Sys.getcwd ())
                      "_build/default/src/ec.exe" in
    if Sys.file_exists candidate then candidate else "easycrypt"

let bin_arg =
  let doc = "Path to the easycrypt binary with `llm` subcommand. Defaults \
             to $EC_LLM_BIN, the in-tree _build path, or `easycrypt` on \
             PATH — in that order." in
  Arg.(value
       & opt string (default_bin ())
       & info ["bin"] ~docv:"PATH" ~doc)

let idir_arg =
  let doc = "Extra -I load-path entries forwarded to ec llm (repeatable)." in
  Arg.(value
       & opt_all string []
       & info ["I"] ~docv:"DIR" ~doc)

let transcript_arg =
  let doc = "Append the structured JSON-per-line transcript to PATH \
             instead of stderr." in
  Arg.(value
       & opt (some string) None
       & info ["transcript"] ~docv:"PATH" ~doc)

let file_arg =
  let doc = "EasyCrypt source file to drive through." in
  Arg.(required
       & pos 0 (some file) None
       & info [] ~docv:"FILE" ~doc)

let drive_cmd =
  let info = Cmd.info "drive" ~doc:"Split an EC file and step through it." in
  let action bin idirs transcript file =
    let extra_args =
      List.concat_map (fun d -> ["-I"; d]) idirs
    in
    drive_file ~bin ~extra_args ~transcript_path:transcript file
  in
  Cmd.v info
    Term.(const action
          $ bin_arg
          $ idir_arg
          $ transcript_arg
          $ file_arg)

let repl_cmd =
  let info =
    Cmd.info "repl"
      ~doc:"Interactive REPL: load, step, reload after edits, direct feed."
  in
  let action bin idirs =
    let extra_args = List.concat_map (fun d -> ["-I"; d]) idirs in
    Repl.run ~bin ~extra_args
  in
  Cmd.v info Term.(const action $ bin_arg $ idir_arg)

let tui_file_arg =
  let doc = "Optional EC file to load on startup (equivalent to typing \
             `:load FILE` after launch). Repeat-friendly for iterative \
             demo/dev." in
  Arg.(value
       & pos 0 (some file) None
       & info [] ~docv:"FILE" ~doc)

let tui_cmd =
  let info =
    Cmd.info "tui"
      ~doc:"TUI driver — same commands as `ecd repl`, with panes for \
            source / goals / log and keybinds mapped to REPL commands."
  in
  let action bin idirs file =
    let extra_args = List.concat_map (fun d -> ["-I"; d]) idirs in
    Tui.run ?load_file:file ~bin ~extra_args ()
  in
  Cmd.v info Term.(const action $ bin_arg $ idir_arg $ tui_file_arg)

(* ---------------------------------------------------------------- *)
(* `ecd replay FILE`                                                  *)
(* ---------------------------------------------------------------- *)

let replay_transcript ~bin ~extra_args ~strict_body path =
  Eio_main.run @@ fun env ->
  (* Replay itself should not pollute any external transcript — point
     the global singleton at devnull for the duration. *)
  Transcript.configure (Transcript.devnull ());
  let process_mgr = Eio.Stdenv.process_mgr env in
  Ec_llm_session.configure ~process_mgr ~executable:bin ~extra_args ();
  let options = { Replay.strict_body } in
  let results = Replay.run ~env ~options path in
  let total_execs, total_mismatches =
    List.fold_left
      (fun (e, m) (r : Replay.session_result) ->
         e + r.execs, m + List.length r.mismatches)
      (0, 0) results
  in
  List.iter
    (fun (r : Replay.session_result) ->
       Printf.printf "session %s: %d/%d matched\n"
         r.label r.matches r.execs;
       List.iter
         (fun (m : Replay.mismatch) ->
            Printf.printf "  [%d] expected: %s\n       got: %s\n"
              m.seq m.expected m.got)
         r.mismatches)
    results;
  Printf.printf "%s: %d execs, %d mismatches\n%!"
    (if total_mismatches = 0 then "OK" else "FAIL")
    total_execs total_mismatches;
  if total_mismatches <> 0 then exit 1

let strict_body_arg =
  let doc = "Also require reply bodies to match the recorded transcript \
             (default: compare uuid + restart-flag + status only)." in
  Arg.(value & flag & info ["strict-body"] ~doc)

let replay_file_arg =
  let doc = "Transcript file (JSON-per-line) to replay." in
  Arg.(required
       & pos 0 (some file) None
       & info [] ~docv:"TRANSCRIPT" ~doc)

let replay_cmd =
  let info =
    Cmd.info "replay"
      ~doc:"Replay a recorded JSON-per-line transcript against a fresh \
            ec llm backend and assert replies match."
  in
  let action bin idirs strict_body path =
    let extra_args = List.concat_map (fun d -> ["-I"; d]) idirs in
    replay_transcript ~bin ~extra_args ~strict_body path
  in
  Cmd.v info
    Term.(const action
          $ bin_arg
          $ idir_arg
          $ strict_body_arg
          $ replay_file_arg)

(* ---------------------------------------------------------------- *)
(* `ecd daemon` long-running mode                                     *)
(* ---------------------------------------------------------------- *)

(* Phase 2.5 deliverable. Wires Daemon_discovery (Phase 2 library)
   into a real persistent process. Stage 3 of the VSCode-first plan
   fills in the per-connection handler with LSP routing.

   Two transport modes: socket (default; long-running daemon, multiple
   editor clients attach over a Unix socket) and stdio (Stage 4 of the
   VSCode-first plan; one LSP connection over stdin/stdout, daemon
   lifetime = client subprocess lifetime — used by editor extensions
   like vscode-languageclient). *)

(* Per-connection LSP setup. Spawns analyze session, wires the
   debouncer + publishDiagnostics flow, registers methods, runs the
   inbound packet loop until shutdown. *)
let serve_lsp_connection ~env ~conn_label ~source ~sink =
  Eio.Switch.run @@ fun conn_sw ->
  let io = Lsp_io.of_flows ~source ~sink in
  let workspace = Workspace.make ~load_path:[] in
  let publish, _publish_state = Stub_publish.make () in
  let server = Lsp_server.create ~workspace ~publish in
  (* UPSTREAM § 14 — per-project session keying. The manager
     spawns one (proof_state, analyze_session) pair per project
     root (= directory of the closest [easycrypt.project], or the
     file's containing directory for synthetic-project files).
     Sessions live under [conn_sw] and are closed on connection
     teardown. *)
  let manager =
    Session_manager.create ~sw:conn_sw ~connection_label:conn_label
  in
  (* Debouncer's [process] callback resolves the analyze session
     per-URI through the manager — different projects' diagnostics
     stay isolated. *)
  let process (uri, source, _version) =
    let analyze_session =
      Session_manager.analyze_session_for manager ~sw:conn_sw ~uri
    in
    Lsp_methods.publish_diagnostics server ~io ~uri ~source
      ~analyze_session
  in
  let clock = Eio.Stdenv.clock env in
  let debouncer =
    Debouncer.create ~sw:conn_sw ~clock
      ~delay:(float_of_int
                (Configuration.debounce_ms (Configuration.current ()))
              /. 1000.0)
      ~process
  in
  let doc_sources : (string, string) Hashtbl.t = Hashtbl.create 4 in
  Lsp_methods.register_all server ~io ~manager ~debouncer
    ~sw:conn_sw ~doc_sources;
  Log.info "%s: LSP methods registered, running" conn_label;
  (try Lsp_server.run server ~io ~sw:conn_sw
   with exn ->
     Log.err "%s: server.run raised %s"
       conn_label (Printexc.to_string exn));
  (* Close ALL sessions (proof + analyze for every project) before
     conn_sw exits. Without this, an in-flight debouncer fiber
     processing a slow document keeps the switch alive until the
     analyze completes; explicit teardown sends QUIT + SIGTERM and
     returns promptly. *)
  Session_manager.close manager;
  Log.info "%s closed" conn_label

let run_daemon ~label ~socket_override ~log_path ~stdio ~ec_bin =
  (* Configure Log first so subsequent failures can surface. *)
  let log_sink =
    match log_path with
    | None -> Log.to_channel ~level:`Info stderr
    | Some p ->
      let oc = open_out_gen [ Open_creat; Open_append; Open_wronly ] 0o600 p in
      at_exit (fun () -> try close_out oc with _ -> ());
      Log.to_channel ~level:`Info oc
  in
  Log.configure log_sink;
  Crash_handler.install ();
  Log.info "ecd daemon starting (label=%s, stdio=%b)" label stdio;

  if stdio then begin
    (* Stdio mode: skip discovery + socket; serve one LSP connection
       over stdin/stdout. Editor extensions (e.g. vscode-languageclient)
       spawn the daemon as a subprocess and speak LSP on stdio. The
       daemon process lives only as long as that one connection.

       Important: stdout is the LSP wire — never write to it directly.
       Logs default to stderr (vscode shows that in the Output panel);
       --log redirects elsewhere if needed. *)
    Eio_main.run @@ fun env ->
    Eio.Switch.run @@ fun _sw ->
    (* [~fs] is the filesystem-root capability used by
       [Ec_llm_session.start_in_dir] to construct an Eio.Path for
       per-project session CWDs. UPSTREAM § 14′. *)
    Ec_llm_session.configure
      ~process_mgr:(Eio.Stdenv.process_mgr env)
      ~fs:(Eio.Stdenv.fs env)
      ~executable:ec_bin
      ();
    Log.info "Ec_llm_session configured: bin=%s" ec_bin;
    serve_lsp_connection ~env ~conn_label:"stdio"
      ~source:(Eio.Stdenv.stdin env)
      ~sink:(Eio.Stdenv.stdout env);
    Log.info "ecd daemon exited cleanly (stdio)"
  end
  else
  let socket_path =
    match socket_override with
    | Some p -> p
    | None ->
      (* AF_UNIX path limit is ~104 bytes on macOS/BSD; the runtime
         dir (especially under dune sandbox) can exceed that. Use a
         hashed short path under /tmp for the socket; the pid file
         (in runtime_dir) records this path so clients still find it. *)
      let hash = Digest.to_hex (Digest.string label) in
      let short = String.sub hash 0 16 in
      let uid = Unix.getuid () in
      Printf.sprintf "/tmp/ec-daemon-%d-%s.sock" uid short
  in

  match Daemon_discovery.acquire ~label ~socket_path () with
  | Already_running { pid; socket } ->
    let sock_str =
      match socket with Some s -> s | None -> "(unknown)"
    in
    Printf.eprintf
      "ecd daemon: already running (pid=%d socket=%s)\n%!" pid sock_str;
    Log.err "discovery: already running pid=%d" pid;
    exit 1
  | Acquired { pid_file; socket_path = sp } ->
    Log.info "discovery: acquired pid_file=%s socket=%s" pid_file sp;
    (* Remove any leftover socket file from a previous unclean exit. *)
    (try Sys.remove sp with _ -> ());
    let shutdown_requested = Atomic.make false in
    let request_shutdown () = Atomic.set shutdown_requested true in
    (* Install signal handlers for graceful shutdown. The handler sets
       the flag; the accept loop polls it. *)
    let install_sig signum =
      try Sys.set_signal signum
            (Sys.Signal_handle (fun _ -> request_shutdown ()))
      with _ -> ()
    in
    install_sig Sys.sigterm;
    install_sig Sys.sigint;

    Eio_main.run @@ fun env ->
    Eio.Switch.run @@ fun sw ->
    let net = Eio.Stdenv.net env in
    let listener =
      try
        Eio.Net.listen ~sw ~backlog:8 ~reuse_addr:false net
          (`Unix sp)
      with exn ->
        Log.err "listen on %s failed: %s" sp (Printexc.to_string exn);
        Daemon_discovery.release ~label ();
        raise exn
    in
    Log.info "listening on %s" sp;
    Printf.eprintf "ecd daemon: listening on %s (pid=%d)\n%!"
      sp (Unix.getpid ());

    (* Cleanup on exit. *)
    at_exit (fun () ->
      Log.info "ecd daemon shutting down";
      Daemon_discovery.release ~label ();
      try Sys.remove sp with _ -> ());

    (* Accept loop. Polls shutdown flag between accepts via a short
       timeout to stay responsive to signals without busy-looping. *)
    let conn_count = ref 0 in
    let on_error exn =
      Log.warn "connection handler error: %s" (Printexc.to_string exn)
    in
    (* Configure Ec_llm_session for analyze/proof work. The analyze
       session is created lazily per-connection (each LSP client gets
       its own analyze session); a future optimization shares one.
       [~fs] enables [Ec_llm_session.start_in_dir] for per-project
       CWDs (UPSTREAM § 14′). *)
    Ec_llm_session.configure
      ~process_mgr:(Eio.Stdenv.process_mgr env)
      ~fs:(Eio.Stdenv.fs env)
      ~executable:ec_bin
      ();
    Log.info "Ec_llm_session configured: bin=%s" ec_bin;

    let handle_connection (flow : _ Eio.Net.stream_socket) (addr : Eio.Net.Sockaddr.stream) =
      incr conn_count;
      let n = !conn_count in
      let conn_label = Printf.sprintf "connection %d" n in
      Log.info "%s from %s" conn_label
        (Format.asprintf "%a" Eio.Net.Sockaddr.pp addr);
      serve_lsp_connection ~env ~conn_label
        ~source:flow ~sink:flow
    in
    let clock = Eio.Stdenv.mono_clock env in
    let rec accept_loop () =
      if Atomic.get shutdown_requested then begin
        Log.info "shutdown requested; stopping accept loop";
        ()
      end
      else begin
        (* Race accept against a short timeout so we poll the
           shutdown flag periodically. *)
        let outcome =
          Eio.Fiber.first
            (fun () ->
              Eio.Net.accept_fork ~sw listener ~on_error handle_connection;
              `Accepted)
            (fun () ->
              Eio.Time.Mono.sleep clock 0.5;
              `Tick)
        in
        ignore outcome;
        accept_loop ()
      end
    in
    (try accept_loop ()
     with Eio.Cancel.Cancelled _ ->
       Log.info "accept loop cancelled");
    Log.info "ecd daemon exited cleanly";
    Eio.Flow.close listener

(* ---------------------------------------------------------------- *)
(* `ecd mcp` — Model Context Protocol server over stdio.             *)

let run_mcp ~ec_bin =
  Transcript.configure (Transcript.to_channel stderr);
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  Ec_llm_session.configure
    ~process_mgr:(Eio.Stdenv.process_mgr env)
    ~fs:(Eio.Stdenv.fs env)
    ~executable:ec_bin ();
  Mcp_server.run ~sw
    ~stdin:(Eio.Stdenv.stdin env)
    ~stdout:(Eio.Stdenv.stdout env)

let mcp_cmd =
  let info =
    Cmd.info "mcp"
      ~doc:"Serve the Model Context Protocol over stdin/stdout \
            (agents-first surface). Tools multiplex named EC proof \
            sessions — open_file, exec, goals, tree, focus, \
            try_tactic, commit_proof, analyze_file — so parallel \
            agents each hold a coherent state. Stdout is the MCP \
            wire; logs and transcripts go to stderr."
  in
  let action ec_bin = run_mcp ~ec_bin in
  Cmd.v info Term.(const action $ bin_arg)

let label_arg =
  let doc = "Discovery label (default: \"default\")." in
  Arg.(value & opt string "default" & info ["label"] ~docv:"NAME" ~doc)

let socket_arg =
  let doc = "Override socket path (default: derived from runtime dir + label)." in
  Arg.(value & opt (some string) None & info ["socket"] ~docv:"PATH" ~doc)

let log_arg =
  let doc = "Append structured JSONL log to PATH (default: stderr)." in
  Arg.(value & opt (some string) None & info ["log"] ~docv:"PATH" ~doc)

let stdio_arg =
  let doc = "Serve one LSP connection over stdin/stdout (used by editor \
             extensions that spawn the daemon as a subprocess); skip \
             discovery + socket bind. Stdout is the LSP wire — logs \
             default to stderr; --log redirects elsewhere if needed." in
  Arg.(value & flag & info ["stdio"] ~doc)

let daemon_cmd =
  let info =
    Cmd.info "daemon"
      ~doc:"Run as a long-lived daemon process. Default: listen on a \
            Unix socket and accept multiple LSP/MCP clients. With \
            --stdio: serve a single LSP connection over stdin/stdout."
  in
  let action label socket log stdio ec_bin =
    run_daemon ~label ~socket_override:socket ~log_path:log ~stdio ~ec_bin
  in
  Cmd.v info
    Term.(const action $ label_arg $ socket_arg $ log_arg $ stdio_arg $ bin_arg)

let root_info =
  Cmd.info "ecd" ~version
    ~doc:"EasyCrypt tooling daemon (PoC)."

let () =
  exit
    (Cmd.eval
       (Cmd.group root_info
          [ drive_cmd; repl_cmd; tui_cmd; replay_cmd; daemon_cmd;
            mcp_cmd ]))
