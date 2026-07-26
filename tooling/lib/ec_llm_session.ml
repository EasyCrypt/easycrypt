(** Session backend that talks to an [ec llm] subprocess over stdin/stdout.
    Implements the line protocol defined in [doc/tooling-protocol.md] § 2.1:

    - Replies framed by `OK [uuid:N] [tags]` / `ERROR [uuid:N] [tags]` and
      terminated by a literal `<END>` line.
    - Out-of-band `NOTICE: <line>` events may appear anywhere.
    - Error replies carry an `ERROR-JSON: { ... }` line right after the
      header (addition 8).
    - OK replies carry an `OK-JSON: { ... }` line right after the header
      (addition 15). v0 payload is `{}`; addition 9 will populate.
    - `[restarted]` tag on any reply signals an implicit restart
      (addition 4).

    PoC scope: one [ec llm] subprocess per session; cancellation is
    SIGKILL on the child (pool-replace wiring lives one layer up).
    [Configure] must be called once at daemon startup — it closes over
    the Eio process manager so [start] can spawn without threading env
    through the [Session.BACKEND] signature. *)

open Eio.Std

(* ---------------------------------------------------------------- *)
(* Configuration                                                     *)
(* ---------------------------------------------------------------- *)

type config = {
  process_mgr : [ `Generic | `Unix ] Eio.Process.mgr_ty r;
  executable  : string;
  (** Path to the [ec llm]-capable easycrypt binary. *)
  extra_args  : string list;
  (** Extra CLI arguments appended after "llm" (e.g. ["-I"; "..."]). *)
  min_proto   : int;
  (** Minimum protocol version accepted from the subprocess (addition 6).
      Handshake fails with [Protocol_mismatch] below this. *)
  fs          : Eio.Fs.dir_ty Eio.Path.t option;
  (** Filesystem root used to construct an [Eio.Path.t] when
      [start ?cwd] is given an absolute directory. Typically
      [Some (Eio.Stdenv.fs env)]. Optional — when [None],
      [start ?cwd] silently falls back to the daemon's CWD (with a
      log warning). UPSTREAM § 14′: per-project sessions need their
      own CWD so EC's [easycrypt.project] upward walk finds the
      right one. *)
}

let cfg : config option ref = ref None

let configure
    ?(extra_args = []) ?(min_proto = 1) ?fs
    ~process_mgr ~executable () =
  cfg := Some { process_mgr; executable; extra_args; min_proto; fs }

(* Per-session supervisor callback. Invoked by the daemon fiber forked
   in [start] when the subprocess exits without [close]/[cancel] having
   requested it. The daemon wires this to its central publish point so
   surfaces emit [server/restarted] / pool slots get replaced without
   waiting for the next caller's [exec] to discover the dead pipe.
   Default: no-op. *)
let on_crash_cb : (label:string -> exit_kind:string -> unit) ref =
  ref (fun ~label:_ ~exit_kind:_ -> ())

let configure_on_crash f = on_crash_cb := f

(* OCaml's [Sys.sig*] constants are negative integers internal to the
   runtime; converting to POSIX numbers keeps [exit_kind] meaningful
   on the wire. Unknown signals fall through to the OCaml value
   (caller should treat negatives as opaque). *)
let posix_signal_of_ocaml n =
  if      n = Sys.sigkill then 9
  else if n = Sys.sigterm then 15
  else if n = Sys.sigsegv then 11
  else if n = Sys.sigabrt then 6
  else if n = Sys.sigint  then 2
  else if n = Sys.sighup  then 1
  else if n = Sys.sigpipe then 13
  else if n = Sys.sigbus  then 7
  else if n = Sys.sigfpe  then 8
  else if n = Sys.sigill  then 4
  else if n = Sys.sigquit then 3
  else if n = Sys.sigusr1 then 10
  else if n = Sys.sigusr2 then 12
  else if n = Sys.sigalrm then 14
  else n

let current_config () =
  match !cfg with
  | None -> failwith "Ec_llm_session: configure must be called before start"
  | Some c -> c

(* ---------------------------------------------------------------- *)
(* Reply parser                                                      *)
(* ---------------------------------------------------------------- *)

type tag = { name : string; value : string option }

type reply = {
  status   : [ `Ok | `Error ];
  uuid     : int;
  tags     : tag list;
  notices  : string list;
  body     : string list;
  (** Body lines (between header and <END>, excluding
      NOTICE:/ERROR-JSON:/OK-JSON:). *)
  error_json : string option;
  (** Raw JSON payload from [ERROR-JSON:] if present (addition 8). *)
  ok_json : string option;
  (** Raw JSON payload from [OK-JSON:] if present (addition 15).
      PoC payload is always `{}`; wiring is in place so addition 9
      can populate it without a daemon-side parser change. *)
}

let has_tag (r : reply) name =
  List.exists (fun t -> t.name = name) r.tags

(* Parse a bracketed tag like "[restarted]" or "[loaded:foo.ec:3]". *)
let parse_tag_token (tok : string) : tag option =
  let n = String.length tok in
  if n < 2 || tok.[0] <> '[' || tok.[n - 1] <> ']' then None
  else
    let inner = String.sub tok 1 (n - 2) in
    match String.index_opt inner ':' with
    | None -> Some { name = inner; value = None }
    | Some i ->
      Some {
        name  = String.sub inner 0 i;
        value = Some (String.sub inner (i + 1) (String.length inner - i - 1));
      }

(* Parse the header line "OK [uuid:N] [t1] [t2:v]" or the ERROR variant. *)
let parse_header (line : string) : ([ `Ok | `Error ] * int * tag list) option =
  let parts = String.split_on_char ' ' line in
  match parts with
  | status :: uuid_tok :: rest when status = "OK" || status = "ERROR" ->
    let st : [ `Ok | `Error ] = if status = "OK" then `Ok else `Error in
    (* uuid_tok should be "[uuid:N]". *)
    (match parse_tag_token uuid_tok with
     | Some { name = "uuid"; value = Some v } ->
       (try
          let uuid = int_of_string v in
          let tags = List.filter_map parse_tag_token rest in
          Some (st, uuid, tags)
        with Failure _ -> None)
     | _ -> None)
  | _ -> None

(** Result of [read_line_cancellable] below. *)
type line_read = [ `Line of string | `Eof | `Cancelled ]

(** Read one line from [buf], but if [cancel_p] resolves first
    return [`Cancelled]. On pipe EOF or a synchronous [End_of_file]
    from [Buf_read.line], return [`Eof]. *)
let read_line_cancellable (buf : Eio.Buf_read.t)
    (cancel_p : unit Eio.Promise.t) : line_read =
  match
    Eio.Fiber.first
      (fun () -> (try `Line (Eio.Buf_read.line buf)
                  with End_of_file -> `Eof))
      (fun () -> Eio.Promise.await cancel_p; `Cancelled)
  with
  | v -> v
  | exception End_of_file -> `Eof

(** Read the full subprocess output until the next <END> sentinel,
    collecting NOTICE events alongside the reply body. Returns [None]
    on EOF or when the caller's cancel promise resolves. *)
let read_reply_with_cancel
    (buf : Eio.Buf_read.t) (cancel_p : unit Eio.Promise.t) : reply option =
  let notices = ref [] in
  let body    = ref [] in
  let header  = ref None in
  let error_json = ref None in
  let ok_json    = ref None in
  let finished = ref false in
  let bailed   = ref false in
  while not !finished do
    match read_line_cancellable buf cancel_p with
    | `Eof | `Cancelled -> bailed := true; finished := true
    | `Line "<END>" -> finished := true
    | `Line line when String.length line > 8
                   && String.sub line 0 8 = "NOTICE: " ->
      notices :=
        String.sub line 8 (String.length line - 8) :: !notices
    | `Line line when !header = None ->
      (match parse_header line with
       | Some h -> header := Some h
       | None -> body := line :: !body)
    | `Line line when String.length line > 12
                   && String.sub line 0 12 = "ERROR-JSON: " ->
      error_json := Some (String.sub line 12 (String.length line - 12))
    | `Line line when String.length line > 9
                   && String.sub line 0 9 = "OK-JSON: " ->
      ok_json := Some (String.sub line 9 (String.length line - 9))
    | `Line line ->
      body := line :: !body
  done;
  if !bailed then None
  else match !header with
    | None -> None
    | Some (status, uuid, tags) ->
      Some {
        status; uuid; tags;
        notices = List.rev !notices;
        body    = List.rev !body;
        error_json = !error_json;
        ok_json    = !ok_json;
      }

(* ---------------------------------------------------------------- *)
(* Session state                                                     *)
(* ---------------------------------------------------------------- *)

type t = {
  label : string;
  mutable proc       : [ `Generic | `Unix ] Eio.Process.ty r;
  mutable stdin      : [ `Flow | `W | `Close ] r;
  mutable stdout_src : [ `Flow | `R | `Close ] r;
  mutable stdout_buf : Eio.Buf_read.t;
  mutable uuid       : int;
  mutable proto      : int;
  mutable closed     : bool;
  mutable cancelled  : bool;
  mutable termination_requested : bool;
  (** Set by [close] / [cancel] (user-initiated teardown). The
      supervisor fiber checks this to suppress [session.crashed] when
      the proc exits because we asked it to. EOF-mid-exec sets
      [cancelled] but NOT this flag — the supervisor surfaces those
      as crashes so the publish point can fan them out. *)
  mutable executed_list : (Sentence_id.t * int) list;
  (** Time-ordered (newest-first) list of [(sid, replied_uuid)]
      pairs. [revert_to] resolves a sid to the NEWEST matching
      entry — needed because content-addressed sids collide when
      the document repeats a sentence (e.g. two `smt().` calls),
      and a Hashtbl-keyed map would lose the earlier entry once
      the later one reverted. Cleared on [restarted] replies per
      protocol § 10.3. *)
  cancel_promise  : unit Eio.Promise.t;
  cancel_resolver : unit Eio.Promise.u;
  (** Cancellation channel. An [Eio.Fiber.first] wraps every
      [Buf_read.line] with [Promise.await cancel_promise], so when
      [cancel] (or [close]) resolves the promise from another fiber,
      any in-flight read returns promptly rather than blocking on a
      pipe that Eio hasn't yet noticed is dead. SIGKILL + pipe close
      alone don't reliably propagate EOF on all platforms. *)
}

(* ---------------------------------------------------------------- *)
(* Handshake                                                         *)
(* ---------------------------------------------------------------- *)

(* Parse "READY [uuid:N] [proto:M]" and return (uuid, proto). Unknown
   tags are ignored. Missing `[proto:...]` is treated as v0 (< any
   sane min_proto) so old binaries without addition 6 get rejected. *)
let parse_ready (line : string) : (int * int) option =
  let parts = String.split_on_char ' ' line in
  match parts with
  | "READY" :: rest ->
    let tags = List.filter_map parse_tag_token rest in
    let find name =
      List.find_opt (fun t -> t.name = name) tags
      |> Option.map (fun t -> t.value)
      |> Option.join
    in
    (match find "uuid" with
     | None -> None
     | Some uuid_s ->
       (try
          let uuid = int_of_string uuid_s in
          let proto =
            match find "proto" with
            | None -> 0
            | Some p -> (try int_of_string p with Failure _ -> 0)
          in
          Some (uuid, proto)
        with Failure _ -> None))
  | _ -> None

(* Drain everything from the buffer up to and including the next
   `<END>` line, ignoring NOTICEs. Used after READY to absorb the
   handshake's terminating <END>. *)
let drain_to_end buf =
  let rec go () =
    match Eio.Buf_read.line buf with
    | exception End_of_file -> ()
    | "<END>" -> ()
    | _ -> go ()
  in
  go ()

(* ---------------------------------------------------------------- *)
(* Session lifecycle                                                 *)
(* ---------------------------------------------------------------- *)

(* Internal — [start ~sw ~label] dispatches here with [cwd=None];
   [start_in_dir] dispatches with the project's directory. EC's
   [easycrypt.project] discovery walks up from CWD; per-project
   session keying needs each project's EC to see its own .project
   file. Fall back silently (with a log warning) when [fs] wasn't
   configured — the cwd then inherits from the parent (typically
   the daemon's launch directory). *)
let start_aux ~cwd ~sw ~label =
  let c = current_config () in
  let stdin_src,  stdin_snk  = Eio.Process.pipe ~sw c.process_mgr in
  let stdout_src, stdout_snk = Eio.Process.pipe ~sw c.process_mgr in
  let cwd_path : _ Eio.Path.t option =
    match cwd, c.fs with
    | Some s, Some fs -> Some Eio.Path.(fs / s)
    | Some s, None ->
      Transcript.record_g Transcript.Log_warn
        (`Assoc [
           "label", `String label;
           "msg", `String "cwd requested but fs capability not configured";
           "cwd", `String s;
         ]);
      None
    | None, _ -> None
  in
  let proc =
    Eio.Process.spawn ~sw c.process_mgr ?cwd:cwd_path
      ~stdin:stdin_src ~stdout:stdout_snk
      (c.executable :: "llm" :: c.extra_args)
  in
  (* Close the ends the parent doesn't need — the child holds the
     reading end of stdin_src and the writing end of stdout_snk. *)
  Eio.Flow.close stdin_src;
  Eio.Flow.close stdout_snk;
  let buf = Eio.Buf_read.of_flow ~max_size:(1 lsl 24) stdout_src in
  (* Consume the READY handshake. *)
  let (uuid, proto) =
    match Eio.Buf_read.line buf with
    | exception End_of_file ->
      failwith "Ec_llm_session: subprocess closed before READY"
    | line ->
      match parse_ready line with
      | None ->
        failwith (Printf.sprintf
                    "Ec_llm_session: malformed READY: %S" line)
      | Some (u, p) -> (u, p)
  in
  drain_to_end buf;
  if proto < c.min_proto then begin
    Eio.Process.signal proc Sys.sigkill;
    Transcript.record_g Transcript.Log_error
      (`Assoc [
         "label", `String label;
         "proto", `Int proto;
         "min_proto", `Int c.min_proto;
         "detail", `String "protocol mismatch";
       ]);
    failwith
      (Printf.sprintf
         "Ec_llm_session: protocol mismatch: subprocess proto=%d, min=%d"
         proto c.min_proto)
  end;
  Transcript.record_g Transcript.Session_spawn
    (`Assoc [
       "label", `String label;
       "pid",   `Int (Eio.Process.pid proc);
       "proto", `Int proto;
     ]);
  let (cancel_promise, cancel_resolver) = Eio.Promise.create () in
  let t = {
    label;
    proc;
    stdin      = stdin_snk;
    stdout_src;
    stdout_buf = buf;
    uuid;
    proto;
    closed     = false;
    cancelled  = false;
    termination_requested = false;
    executed_list = [];
    cancel_promise;
    cancel_resolver;
  } in
  (* Supervisor fiber. Awaits the subprocess; on exit when the user
     hasn't asked for termination, records [session.crashed] and
     invokes the global on-crash callback. Fires for EOF-mid-exec
     too — the publish point fans those out so other surfaces
     observe the death without waiting for their own [exec]. *)
  Eio.Fiber.fork_daemon ~sw (fun () ->
    let status =
      try Some (Eio.Process.await proc)
      with Eio.Cancel.Cancelled _ -> None
    in
    (match status with
     | None -> ()
     | Some st when t.termination_requested -> ignore st
     | Some st ->
       let exit_kind =
         match st with
         | `Exited n -> Printf.sprintf "exit:%d" n
         | `Signaled n -> Printf.sprintf "signal:%d" (posix_signal_of_ocaml n)
       in
       Transcript.record_g Transcript.Session_crashed
         (`Assoc [
            "label",     `String label;
            "exit_kind", `String exit_kind;
          ]);
       (try !on_crash_cb ~label ~exit_kind with _ -> ()));
    `Stop_daemon);
  t

(* Public entry — [start ~sw ~label] inherits the daemon's CWD.
   Backward-compatible with the BACKEND signature. *)
let start ~sw ~label = start_aux ~cwd:None ~sw ~label

(* Public entry for per-project sessions — spawns the EC subprocess
   with [~cwd:project_root] so EC's [easycrypt.project] discovery
   finds the right .project file. UPSTREAM § 14′. *)
let start_in_dir ~cwd ~sw ~label = start_aux ~cwd:(Some cwd) ~sw ~label

let signal_cancel t =
  if not (Eio.Promise.is_resolved t.cancel_promise) then
    Eio.Promise.resolve t.cancel_resolver ()

let close t =
  if not t.closed then begin
    t.closed <- true;
    t.termination_requested <- true;
    (try Eio.Flow.copy_string "QUIT\n" t.stdin with _ -> ());
    signal_cancel t;
    (try Eio.Flow.close t.stdin with _ -> ());
    (try Eio.Flow.close t.stdout_src with _ -> ());
    (try Eio.Process.signal t.proc Sys.sigterm with _ -> ());
    ()
  end

(* ---------------------------------------------------------------- *)
(* Reply-handling helpers                                            *)
(* ---------------------------------------------------------------- *)

(* Map an ERROR-JSON payload to an [Error.t]. Best-effort: falls back
   to [Internal] if parsing fails. *)
let error_of_json (raw : string) : Error.t =
  let default = Error.Internal { detail = raw } in
  match Yojson.Safe.from_string raw with
  | exception _ -> default
  | json ->
    let open Yojson.Safe.Util in
    let code = try json |> member "code" |> to_string with _ -> "Internal" in
    let detail = try json |> member "detail" |> to_string with _ -> raw in
    (match code with
     | "ParseError"    -> Error.Parse_error    { detail }
     | "TypeError"     -> Error.Type_error     { detail }
     | "TacticFailure" -> Error.Tactic_failure { detail }
     | _               -> Error.Internal       { detail })

(* Send an input line (appends newline) and read the next reply. *)
let send_and_read t (line : string) : reply option =
  Eio.Flow.copy_string line t.stdin;
  if not (String.length line > 0 && line.[String.length line - 1] = '\n') then
    Eio.Flow.copy_string "\n" t.stdin;
  read_reply_with_cancel t.stdout_buf t.cancel_promise

(* Send a multi-line EasyCrypt sentence via <BEGIN>/<DONE>. *)
let send_multi_and_read t (source : string) : reply option =
  Eio.Flow.copy_string "<BEGIN>\n" t.stdin;
  Eio.Flow.copy_string source t.stdin;
  if not (String.length source > 0 && source.[String.length source - 1] = '\n') then
    Eio.Flow.copy_string "\n" t.stdin;
  Eio.Flow.copy_string "<DONE>\n" t.stdin;
  read_reply_with_cancel t.stdout_buf t.cancel_promise

(* ---------------------------------------------------------------- *)
(* BACKEND operations                                                *)
(* ---------------------------------------------------------------- *)

let exec t ~corr ~sentence_class ~source =
  if t.cancelled then
    Error (Error.Cancelled { reason = "session cancelled" })
  else if t.closed then
    Error (Error.Internal { detail = "session closed" })
  else
    let pre_uuid = t.uuid in
    let class_str =
      match sentence_class with
      | `Executable -> "executable"
      | `Doc_comment -> "doc_comment"
      | `Directive -> "directive"
    in
    (* Transcript payload includes [source] verbatim so the replay
       driver can re-drive a fresh backend; [source_len] stays for
       human-readable browsing. *)
    Transcript.record_g ~corr Transcript.Session_exec
      (`Assoc [
         "label", `String t.label;
         "pre_uuid", `Int pre_uuid;
         "class", `String class_str;
         "source", `String source;
         "source_len", `Int (String.length source);
       ]);
    let json_body body =
      `List (List.map (fun s -> `String s) body)
    in
    let json_opt_str = function
      | None -> `Null
      | Some s -> `String s
    in
    match send_multi_and_read t source with
    | None ->
      t.cancelled <- true;
      Transcript.record_g ~corr Transcript.Session_restart
        (`Assoc [
           "label", `String t.label;
           "reason", `String "subprocess-eof";
         ]);
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      if has_tag r "restarted" then t.uuid <- r.uuid;
      Transcript.record_g ~corr Transcript.Session_reply
        (`Assoc [
           "label",   `String t.label;
           "status",  `String "error";
           "uuid",    `Int r.uuid;
           "restarted", `Bool (has_tag r "restarted");
           "body",    json_body r.body;
           "error_json", json_opt_str r.error_json;
           "ok_json",    json_opt_str r.ok_json;
         ]);
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None ->
         let detail = String.concat "\n" r.body in
         Error (Error.Internal { detail }))
    | Some r ->
      let restarted = has_tag r "restarted" in
      let expected_uuid =
        match sentence_class with
        | `Executable | `Doc_comment -> pre_uuid + 1
        | `Directive -> pre_uuid
      in
      if restarted then begin
        t.uuid <- r.uuid;
        (* Per protocol § 10.3: drop the exec history on restart; all
           pre-restart sentence ids are stale. *)
        t.executed_list <- [];
        Transcript.record_g ~corr Transcript.Session_restart
          (`Assoc [
             "label",    `String t.label;
             "reason",   `String "explicit-or-load";
             "new_uuid", `Int r.uuid;
             "body",     json_body r.body;
             "ok_json",  json_opt_str r.ok_json;
           ]);
        let sid = Sentence_id.of_source source in
        t.executed_list <- (sid, r.uuid) :: t.executed_list;
        Ok Session.{
            sentence_id  = sid;
            replied_uuid = r.uuid;
            notices      = r.notices;
            restarted    = true;
            output       = String.concat "\n" r.body;
          }
      end
      else if r.uuid <> expected_uuid then begin
        t.cancelled <- true;
        Transcript.record_g ~corr Transcript.Invariant_uuid_mismatch
          (`Assoc [
             "label",    `String t.label;
             "expected", `Int expected_uuid;
             "got",      `Int r.uuid;
             "class",    `String class_str;
           ]);
        Error (Error.Session_restarted {
          reason =
            Printf.sprintf
              "invariant-violation: expected uuid %d for class %s, got %d"
              expected_uuid class_str r.uuid
        })
      end
      else begin
        t.uuid <- r.uuid;
        let sid = Sentence_id.of_source source in
        t.executed_list <- (sid, r.uuid) :: t.executed_list;
        Transcript.record_g ~corr Transcript.Session_reply
          (`Assoc [
             "label",  `String t.label;
             "status", `String "ok";
             "uuid",   `Int r.uuid;
             "restarted", `Bool false;
             "notices_count", `Int (List.length r.notices);
             "sentence_id", `String (Sentence_id.to_string sid);
             "body",    json_body r.body;
             "ok_json", json_opt_str r.ok_json;
           ]);
        Ok Session.{
            sentence_id  = sid;
            replied_uuid = r.uuid;
            notices      = r.notices;
            restarted    = false;
            output       = String.concat "\n" r.body;
          }
      end

(* Addition 13: EXEC-JSON pass-through. Sends a single-line
   [EXEC-JSON <payload>] request and handles the reply. Unlike text
   [exec], v0 doesn't enforce a strict uuid invariant: a command's
   kind (tactic vs directive) could be inspected from the JSON to
   determine whether uuid should advance, but deferring to the
   server's reported post_uuid is simpler and keeps this
   backend-level helper free of schema knowledge. Invariant-aware
   dispatch can land in v1 if needed. *)
let exec_json t ~corr ~command_json =
  if t.cancelled then
    Error (Error.Cancelled { reason = "session cancelled" })
  else if t.closed then
    Error (Error.Internal { detail = "session closed" })
  else
    let pre_uuid = t.uuid in
    let json_body body = `List (List.map (fun s -> `String s) body) in
    let json_opt_str = function None -> `Null | Some s -> `String s in
    Transcript.record_g ~corr Transcript.Session_exec
      (`Assoc [
         "label", `String t.label;
         "pre_uuid", `Int pre_uuid;
         "class", `String "exec-json";
         "source", `String command_json;
         "source_len", `Int (String.length command_json);
         "exec_json", `Bool true;
       ]);
    match send_and_read t ("EXEC-JSON " ^ command_json) with
    | None ->
      t.cancelled <- true;
      Transcript.record_g ~corr Transcript.Session_restart
        (`Assoc [ "label", `String t.label;
                  "reason", `String "subprocess-eof" ]);
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      if has_tag r "restarted" then t.uuid <- r.uuid;
      Transcript.record_g ~corr Transcript.Session_reply
        (`Assoc [
           "label",   `String t.label;
           "status",  `String "error";
           "uuid",    `Int r.uuid;
           "restarted", `Bool (has_tag r "restarted");
           "body",    json_body r.body;
           "error_json", json_opt_str r.error_json;
           "ok_json",    json_opt_str r.ok_json;
           "exec_json", `Bool true;
         ]);
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None ->
         let detail = String.concat "\n" r.body in
         Error (Error.Internal { detail }))
    | Some r ->
      let restarted = has_tag r "restarted" in
      let sid = Sentence_id.of_source command_json in
      t.uuid <- r.uuid;
      if restarted then begin
        t.executed_list <- [];
        Transcript.record_g ~corr Transcript.Session_restart
          (`Assoc [
             "label",    `String t.label;
             "reason",   `String "explicit-or-load";
             "new_uuid", `Int r.uuid;
             "body",     json_body r.body;
             "ok_json",  json_opt_str r.ok_json;
             "exec_json", `Bool true;
           ])
      end
      else if r.uuid > pre_uuid then
        t.executed_list <- (sid, r.uuid) :: t.executed_list;
      if not restarted then
        Transcript.record_g ~corr Transcript.Session_reply
          (`Assoc [
             "label",  `String t.label;
             "status", `String "ok";
             "uuid",   `Int r.uuid;
             "restarted", `Bool false;
             "notices_count", `Int (List.length r.notices);
             "sentence_id", `String (Sentence_id.to_string sid);
             "body",    json_body r.body;
             "ok_json", json_opt_str r.ok_json;
             "exec_json", `Bool true;
           ]);
      Ok Session.{
          sentence_id  = sid;
          replied_uuid = r.uuid;
          notices      = r.notices;
          restarted;
          output       = String.concat "\n" r.body;
        }

(* Resolve [sid] to the NEWEST matching entry in the exec history and
   issue REVERT. Newest-first lookup handles duplicate-content
   sentences correctly (e.g. two `smt().` calls with the same sid):
   the caller always means "the occurrence most recently fed" for
   any sid still reachable through st.executed in the REPL. *)
let revert_to t sid =
  match List.find_opt (fun (s, _) -> Sentence_id.equal s sid) t.executed_list with
  | None ->
    Error (Error.Unknown_sentence_id { id = Sentence_id.to_string sid })
  | Some (_, target) ->
    let cmd = Printf.sprintf "REVERT %d" target in
    match send_and_read t cmd with
    | None ->
      t.cancelled <- true;
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None ->
         let detail = String.concat "\n" r.body in
         Error (Error.Internal { detail }))
    | Some r ->
      t.uuid <- r.uuid;
      (* Keep only the exec history at or before the target uuid.
         Because the list is newest-first, dropping from the front
         until we pass entries with uuid > target gives exactly
         that suffix. *)
      t.executed_list <-
        List.filter (fun (_, u) -> u <= target) t.executed_list;
      Ok ()

(* Revert directly to a raw uuid, bypassing the sid map. Needed by
   [Speculation]: the capture happens before a candidate exec runs,
   so there's no post-exec sid to key revert_to on. Using uuid is
   safe because the session tracks its own uuid monotonically and
   the REVERT protocol command accepts it natively. *)
let revert_to_uuid t ~target =
  if t.cancelled || t.closed then
    Error (Error.Cancelled { reason = "session unavailable" })
  else
    let cmd = Printf.sprintf "REVERT %d" target in
    match send_and_read t cmd with
    | None ->
      t.cancelled <- true;
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None ->
         let detail = String.concat "\n" r.body in
         Error (Error.Internal { detail }))
    | Some r ->
      t.uuid <- r.uuid;
      t.executed_list <-
        List.filter (fun (_, u) -> u <= target) t.executed_list;
      Ok ()

let current_uuid t = t.uuid

(* Accessor used by Proof_state to track the head of the exec
   history without exposing the mutable list directly. *)
let executed_top t =
  match t.executed_list with
  | [] -> None
  | (sid, uuid) :: _ -> Some (sid, uuid)

(* Prefer GOALS-JSON when the subprocess speaks proto >= 1 (addition 3);
   the daemon will parse the JSON at the next layer. *)
let goals ?(structured = true) t =
  if t.closed || t.cancelled then
    Error (Error.Cancelled { reason = "session unavailable" })
  else
    let cmd = if structured && t.proto >= 1 then "GOALS-JSON" else "GOALS" in
    match send_and_read t cmd with
    | None ->
      t.cancelled <- true;
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None ->
         let detail = String.concat "\n" r.body in
         Error (Error.Internal { detail }))
    | Some r ->
      Ok (String.concat "\n" r.body)

(* ---------------------------------------------------------------- *)
(* Parsing a document via the addition-1 PARSE-BEGIN/PARSE-DONE frame *)
(* ---------------------------------------------------------------- *)

type parsed_sentence = {
  cls       : [ `Executable | `Doc_comment | `Directive | `Meta ];
  kind      : string;
  start_line : int;
  start_col  : int;
  end_line   : int;
  end_col    : int;
  start_offset : int;
  end_offset   : int;
  src        : string;
}

let parse_class_of_string = function
  | "executable"  -> `Executable
  | "doc_comment" -> `Doc_comment
  | "directive"   -> `Directive
  | "meta"        -> `Meta
  | other -> failwith ("Ec_llm_session: unknown parse class: " ^ other)

let parse_source t source =
  if t.cancelled || t.closed then
    Error (Error.Cancelled { reason = "session unavailable" })
  else begin
    Eio.Flow.copy_string "<PARSE-BEGIN>\n" t.stdin;
    Eio.Flow.copy_string source t.stdin;
    if not (String.length source > 0
            && source.[String.length source - 1] = '\n') then
      Eio.Flow.copy_string "\n" t.stdin;
    Eio.Flow.copy_string "<PARSE-DONE>\n" t.stdin;
    match read_reply_with_cancel t.stdout_buf t.cancel_promise with
    | None ->
      t.cancelled <- true;
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None -> Error (Error.Internal { detail = String.concat "\n" r.body }))
    | Some r ->
      let body = String.concat "\n" r.body in
      match Yojson.Safe.from_string body with
      | exception _ ->
        Error (Error.Internal { detail = "malformed PARSE-JSON: " ^ body })
      | json ->
        let open Yojson.Safe.Util in
        let parse_one obj =
          let g fld = member fld obj in
          {
            cls         = parse_class_of_string (g "class" |> to_string);
            kind        = g "kind" |> to_string;
            start_line  = g "start_line" |> to_int;
            start_col   = g "start_col"  |> to_int;
            end_line    = g "end_line"   |> to_int;
            end_col     = g "end_col"    |> to_int;
            start_offset = g "start_offset" |> to_int;
            end_offset   = g "end_offset"   |> to_int;
            src         = g "src" |> to_string;
          }
        in
        (try
           let items = json |> member "sentences" |> to_list in
           Ok (List.map parse_one items)
         with
         | Yojson.Safe.Util.Type_error (msg, _) ->
           Error (Error.Internal { detail = "PARSE-JSON shape: " ^ msg })
         | Failure msg ->
           Error (Error.Internal { detail = msg }))
  end

(* Addition 14: ANALYZE-JSON. Returns the raw JSON envelope
   ({sentences, diagnostics}) for the daemon to decode. Stateless on
   the EC side — runs against a fresh scope, so the live primary's
   state is untouched. *)
let analyze_source t ~source =
  if t.cancelled || t.closed then
    Error (Error.Cancelled { reason = "session unavailable" })
  else begin
    Eio.Flow.copy_string "<ANALYZE-BEGIN>\n" t.stdin;
    Eio.Flow.copy_string source t.stdin;
    if not (String.length source > 0
            && source.[String.length source - 1] = '\n') then
      Eio.Flow.copy_string "\n" t.stdin;
    Eio.Flow.copy_string "<ANALYZE-DONE>\n" t.stdin;
    match read_reply_with_cancel t.stdout_buf t.cancel_promise with
    | None ->
      t.cancelled <- true;
      Error (Error.Session_restarted { reason = "subprocess EOF" })
    | Some r when r.status = `Error ->
      (match r.error_json with
       | Some raw -> Error (error_of_json raw)
       | None -> Error (Error.Internal { detail = String.concat "\n" r.body }))
    | Some r ->
      Ok (String.concat "\n" r.body)
  end

let cancel t ~corr =
  if not t.cancelled then begin
    t.cancelled <- true;
    t.termination_requested <- true;
    Transcript.record_g ~corr Transcript.Session_kill
      (`Assoc [ "label", `String t.label; "reason", `String "cancel" ]);
    (* Order matters: resolve the cancel promise first so any fiber
       blocked in [Buf_read.line] via [read_reply_with_cancel] wakes
       immediately. Then SIGKILL the child and drop our pipe ends so
       the kernel side is torn down too. *)
    signal_cancel t;
    (try Eio.Process.signal t.proc Sys.sigkill with _ -> ());
    (try Eio.Flow.close t.stdin with _ -> ());
    (try Eio.Flow.close t.stdout_src with _ -> ())
  end

let is_alive t = not (t.cancelled || t.closed)

let pid t = Eio.Process.pid t.proc

(* Send SIGINT to the EC subprocess to trigger the in-process
   [EcCancel] flag (see UPSTREAM § 25 / doc/cancellation.md).
   Unlike [cancel], the session is NOT marked terminated — the
   subprocess catches SIGINT, replies "canceled" to whatever
   command is in flight, and stays alive for further requests.
   Tolerant of an already-dead pid. *)
let send_sigint t =
  try Eio.Process.signal t.proc Sys.sigint with _ -> ()

(* Module-time check that we match the [BACKEND] signature.
   Per-project CWD is exposed via the separate [start_in_dir] —
   not part of BACKEND, since that contract abstracts over
   single-session backends like the stub. *)
let () =
  let module _ : Session.BACKEND = struct
    type nonrec t = t
    let start = start
    let exec = exec
    let revert_to = revert_to
    let goals t = goals t
    let cancel = cancel
    let close = close
  end in
  ()
