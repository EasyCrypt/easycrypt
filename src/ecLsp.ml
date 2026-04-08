open Lwt.Syntax

module Json = Yojson.Safe
module J = Yojson.Safe.Util

module Lsp_io =
  Lsp.Io.Make
    (struct
      type 'a t = 'a Lwt.t

      let return = Lwt.return
      let raise = Lwt.fail

      module O = struct
        let ( let+ ) x f = Lwt.map f x
        let ( let* ) x f = Lwt.bind x f
      end
    end)
    (struct
      type input = Lwt_io.input_channel
      type output = Lwt_io.output_channel

      let read_line ic = Lwt_io.read_line_opt ic

      let read_exactly ic len =
        let rec loop acc remaining =
          if remaining <= 0 then
            Lwt.return (Some (Buffer.contents acc))
          else
            Lwt.bind (Lwt_io.read ~count:remaining ic) (fun s ->
              if s = "" then
                Lwt.return None
              else (
                Buffer.add_string acc s;
                loop acc (remaining - String.length s)
              ))
        in
        loop (Buffer.create len) len

      let write oc chunks =
        Lwt.bind (Lwt_list.iter_s (Lwt_io.write oc) chunks) (fun () ->
          Lwt_io.flush oc)
    end)

let setup_logging () : unit =
  let reporter =
    match Sys.getenv_opt "EASYCRYPT_LSP_LOG" with
    | None -> Logs_fmt.reporter ()
    | Some path -> (
        try
          let oc =
            open_out_gen [ Open_creat; Open_text; Open_append ] 0o644 path
          in
          Logs_fmt.reporter ~dst:(Format.formatter_of_out_channel oc) ()
        with e ->
          prerr_endline ("[easycrypt-lsp] failed to open log file: " ^ Printexc.to_string e);
          Logs_fmt.reporter ())
  in
  Logs.set_reporter reporter;
  Logs.set_level (Some Logs.Info)

let log (fmt : ('a, Format.formatter, unit, unit) format4) =
  Format.kasprintf (fun msg -> Logs.info (fun m -> m "%s" msg)) fmt

module Easycrypt_cli = struct
  type session = {
    proc : Lwt_process.process;
    mutable uuid : int;
    mutable mode : string;
    mutable last_output : string;
    root_uuid : int;
  }

  type config = {
    mutable cli_path : string;
    mutable cli_args : string list;
  }

  let prompt_re : Pcre2.regexp =
    Pcre2.regexp "\\[([0-9]+)\\|([^\\]]+)\\]>"

  let parse_prompt (line : string) : (int * string) option =
    try
      let subs = Pcre2.exec ~rex:prompt_re line in
      let uuid_str = Pcre2.get_substring subs 1 in
      let mode = Pcre2.get_substring subs 2 in
      Some (int_of_string uuid_str, mode)
    with
    | Not_found -> None
    | Pcre2.Error _ -> None

  let default_cli_path () : string =
    if Sys.file_exists "ec.native" then
      "./ec.native"
    else
      "easycrypt"

  let read_until_prompt (sess : session) : string Lwt.t =
    let buf = Buffer.create 256 in
    let rec loop () =
      let* line_opt = Lwt_io.read_line_opt sess.proc#stdout in
      match line_opt with
      | None -> Lwt.return (Buffer.contents buf)
      | Some line ->
          log "cli<line %s" (String.escaped line);
          (match parse_prompt line with
           | Some (uuid, mode) ->
               sess.uuid <- uuid;
               sess.mode <- mode;
               Lwt.return (Buffer.contents buf)
           | None ->
               Buffer.add_string buf line;
               Buffer.add_char buf '\n';
               loop ())
    in
    loop ()

  let start_session (cfg : config) : session Lwt.t =
    let argv =
      let args = "cli" :: "-emacs" :: cfg.cli_args in
      Array.of_list (cfg.cli_path :: args)
    in
    let proc = Lwt_process.open_process (cfg.cli_path, argv) in
    let sess =
      { proc
      ; uuid = 0
      ; mode = ""
      ; last_output = ""
      ; root_uuid = 0
      }
    in
    let* _initial_output = read_until_prompt sess in
    Lwt.return { sess with root_uuid = sess.uuid }

  let send_command ?(record_last_output = true) (sess : session) (text : string) : string Lwt.t =
    log "cli> %s" (String.trim text);
    let write =
      if String.ends_with ~suffix:"\n" text then
        Lwt_io.write sess.proc#stdin text
      else
        Lwt_io.write_line sess.proc#stdin text
    in
    let* () = write in
    let* () = Lwt_io.flush sess.proc#stdin in
    let* output = read_until_prompt sess in
    if record_last_output then
      sess.last_output <- output;
    let preview =
      if String.length output = 0 then "<empty>"
      else if String.length output <= 200 then String.escaped output
      else String.escaped (String.sub output 0 200) ^ "..."
    in
    log "cli< (%d bytes) %s" (String.length output) preview;
    Lwt.return output

  let send_undo (sess : session) (target_uuid : int) : string Lwt.t =
    let cmd = Printf.sprintf "undo %d." target_uuid in
    send_command sess cmd

  let stop_session (sess : session) : unit Lwt.t =
    let close_chan ch = Lwt.catch (fun () -> Lwt_io.close ch) (fun _ -> Lwt.return_unit) in
    let* () = close_chan sess.proc#stdin in
    let* () = close_chan sess.proc#stdout in
    sess.proc#terminate;
    let* _status = sess.proc#status in
    Lwt.return_unit

end

type doc_state = {
  mutable text : BatText.t;
  mutable last_offset : int;
  mutable history : (int * int) list;
  mutable session : Easycrypt_cli.session option;
}

let doc_states : (string, doc_state) Hashtbl.t = Hashtbl.create 16

let get_doc_state (uri : string) : doc_state =
  match Hashtbl.find_opt doc_states uri with
  | Some state -> state
  | None ->
      let created = { text = BatText.empty; last_offset = 0; history = []; session = None } in
      Hashtbl.add doc_states uri created;
      created

let error_tag_re : Pcre2.regexp =
  Pcre2.regexp "\\[error-\\d+-\\d+\\]"

let output_has_error (output : string) : bool =
  Pcre2.pmatch ~rex:error_tag_re output

let find_next_sentence
    (text : BatText.t)
    (start : int) : (string * int * int) option =
  EcIo.next_sentence_from (BatText.to_string text) start

let position_to_offset (text : BatText.t) (pos : Lsp.Types.Position.t) : int =
  let len = BatText.length text in
  let target_line = pos.Lsp.Types.Position.line in
  let target_col = pos.Lsp.Types.Position.character in
  let newline = BatUChar.of_char '\n' in
  let rec find_line_start line current =
    if line <= 0 then
      current
    else
      try
        let idx = BatText.index_from text current newline in
        find_line_start (line - 1) (min (idx + 1) len)
      with
      | Not_found -> len
      | BatText.Out_of_bounds -> len
  in
  let line_start = find_line_start target_line 0 in
  if line_start >= len then
    len
  else
    let offset = line_start + target_col in
    if offset > len then len else offset

let apply_change
    (text : BatText.t)
    (change : Lsp.Types.TextDocumentContentChangeEvent.t) : BatText.t * int =
  match change.Lsp.Types.TextDocumentContentChangeEvent.range with
  | None ->
      BatText.of_string change.Lsp.Types.TextDocumentContentChangeEvent.text, 0
  | Some range ->
      let start_offset = position_to_offset text range.Lsp.Types.Range.start in
      let end_offset = position_to_offset text range.Lsp.Types.Range.end_ in
      let len = BatText.length text in
      let start_offset = max 0 (min start_offset len) in
      let end_offset = max start_offset (min end_offset len) in
      let removed = BatText.remove start_offset (end_offset - start_offset) text in
      let inserted = BatText.of_string change.Lsp.Types.TextDocumentContentChangeEvent.text in
      (BatText.insert start_offset inserted removed, start_offset)

let json_of_proof_response
    ~(sess : Easycrypt_cli.session)
    ~(doc : doc_state)
    ?sentence
    (output : string) : Json.t =
  let sentence_start, sentence_end =
    match sentence with
    | None -> (`Null, `Null)
    | Some (start, end_) -> (`Int start, `Int end_)
  in
  `Assoc
    [ ("output", `String output)
    ; ("uuid", `Int sess.uuid)
    ; ("mode", `String sess.mode)
    ; ("processedEnd", `Int doc.last_offset)
    ; ("sentenceStart", sentence_start)
    ; ("sentenceEnd", sentence_end)
    ]

let json_of_query_response (output : string) : Json.t =
  `Assoc [ ("output", `String output) ]

let json_of_proof_result (result : EcProofCore.proof_response) : Json.t =
  let sentence_start, sentence_end =
    match result.sentence_start, result.sentence_end with
    | Some start_, Some end_ -> (`Int start_, `Int end_)
    | _ -> (`Null, `Null)
  in
  `Assoc
    [ ("output", `String result.output)
    ; ("uuid", `Int result.uuid)
    ; ("mode", `String result.mode)
    ; ("processedEnd", `Int result.processed_end)
    ; ("sentenceStart", sentence_start)
    ; ("sentenceEnd", sentence_end)
    ]

let json_of_query_result (result : EcProofCore.query_response) : Json.t =
  json_of_query_response result.output

let core_position_of_lsp (pos : Lsp.Types.Position.t) : EcProofCore.position =
  { EcProofCore.line = pos.line; character = pos.character }

let core_change_of_lsp
    (change : Lsp.Types.TextDocumentContentChangeEvent.t) : EcProofCore.text_change =
  let range =
    Option.map
      (fun range ->
         { EcProofCore.start_ = core_position_of_lsp range.Lsp.Types.Range.start
         ; end_ = core_position_of_lsp range.Lsp.Types.Range.end_
         })
      change.Lsp.Types.TextDocumentContentChangeEvent.range
  in
  { EcProofCore.range; text = change.Lsp.Types.TextDocumentContentChangeEvent.text }

let rstrip (s : string) : string =
  let rec find i =
    if i < 0 then
      -1
    else
      match s.[i] with
      | ' ' | '\t' | '\r' | '\n' -> find (i - 1)
      | _ -> i
  in
  let last = find (String.length s - 1) in
  if last < 0 then "" else String.sub s 0 (last + 1)

let strip_trailing_goal (output : string) (goal : string) : string =
  let output_trimmed = rstrip output in
  let goal_trimmed = rstrip goal in
  if goal_trimmed = "" || output_trimmed = goal_trimmed then
    output_trimmed
  else if String.ends_with ~suffix:goal_trimmed output_trimmed then
    let prefix_len = String.length output_trimmed - String.length goal_trimmed in
    rstrip (String.sub output_trimmed 0 prefix_len)
  else
    output_trimmed

type proof_command_kind =
  | Proof_next
  | Proof_step
  | Proof_jump_to of int
  | Proof_back
  | Proof_restart
  | Proof_goals
  | Query_print of string
  | Query_locate of string
  | Query_search of string

type proof_command =
  { uri : string
  ; cmd : proof_command_kind
  }

let proof_command_of_request (meth : string) (params : Json.t option) :
    (proof_command, string) result =
  let get_uri json =
    match J.member "uri" json with
    | `String uri -> uri
    | _ -> ""
  in
  let get_query json =
    match J.member "query" json with
    | `String query -> String.trim query
    | _ -> ""
  in
  match meth, params with
    | "easycrypt/proof/next", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        if uri = "" then Error "missing uri" else Ok { uri; cmd = Proof_next }
    | "easycrypt/proof/step", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        if uri = "" then Error "missing uri" else Ok { uri; cmd = Proof_step }
    | "easycrypt/proof/jumpTo", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        let target =
          try J.member "target" json |> J.to_int with _ -> -1
        in
        if uri = "" || target < 0 then
          Error "missing uri or target"
        else
          Ok { uri; cmd = Proof_jump_to target }
    | "easycrypt/proof/back", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        if uri = "" then Error "missing uri" else Ok { uri; cmd = Proof_back }
    | "easycrypt/proof/restart", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        if uri = "" then Error "missing uri" else Ok { uri; cmd = Proof_restart }
    | "easycrypt/proof/goals", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        if uri = "" then Error "missing uri" else Ok { uri; cmd = Proof_goals }
    | "easycrypt/query/print", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        let query = get_query json in
        if uri = "" || query = "" then
          Error "missing uri or query"
        else
          Ok { uri; cmd = Query_print query }
    | "easycrypt/query/locate", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        let query = get_query json in
        if uri = "" || query = "" then
          Error "missing uri or query"
        else
          Ok { uri; cmd = Query_locate query }
    | "easycrypt/query/search", Some (`Assoc _ as json) ->
        let uri = get_uri json in
        let query = get_query json in
        if uri = "" || query = "" then
          Error "missing uri or query"
        else
          Ok { uri; cmd = Query_search query }
    | _ -> Error "Method not found"

let rewind_to_offset
    (doc : doc_state)
    (sess : Easycrypt_cli.session)
    (target : int) : string option Lwt.t =
  if target >= doc.last_offset then
    Lwt.return_none
  else
    let rec last_before acc = function
      | [] -> acc
      | (offset, uuid) :: rest ->
          let acc = if offset <= target then Some (offset, uuid) else acc in
          last_before acc rest
    in
    let target_entry = last_before None doc.history in
    let target_uuid, new_offset =
      match target_entry with
      | None -> sess.root_uuid, 0
      | Some (offset, uuid) -> uuid, offset
    in
    doc.history <- List.filter (fun (offset, _) -> offset <= new_offset) doc.history;
    doc.last_offset <- new_offset;
    let* output = Easycrypt_cli.send_undo sess target_uuid in
    Lwt.return (Some output)

let send_packet (oc : Lwt_io.output_channel) (packet : Jsonrpc.Packet.t) : unit Lwt.t =
  Lsp_io.write oc packet

let send_response (oc : Lwt_io.output_channel) (id : Jsonrpc.Id.t) (result : Jsonrpc.Json.t) :
    unit Lwt.t =
  let response = Jsonrpc.Response.ok id result in
  send_packet oc (Jsonrpc.Packet.Response response)

let send_typed_response
    (oc : Lwt_io.output_channel)
    (id : Jsonrpc.Id.t)
    (req : 'a Lsp.Client_request.t)
    (result : 'a) : unit Lwt.t =
  let payload = Lsp.Client_request.yojson_of_result req result in
  send_response oc id payload

let send_error
    (oc : Lwt_io.output_channel)
    (id : Jsonrpc.Id.t)
    (code : Jsonrpc.Response.Error.Code.t)
    (message : string) : unit Lwt.t =
  let error =
    Jsonrpc.Response.Error.make
      ~code
      ~message
      ()
  in
  let response = Jsonrpc.Response.error id error in
  send_packet oc (Jsonrpc.Packet.Response response)

let send_notification (oc : Lwt_io.output_channel) (method_ : string) (params : Jsonrpc.Json.t) :
    unit Lwt.t =
  let params_struct = Jsonrpc.Structured.t_of_yojson params in
  let notif = Jsonrpc.Notification.create ~params:params_struct ~method_ () in
  send_packet oc (Jsonrpc.Packet.Notification notif)

let run () : unit =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  setup_logging ();
  log "argv=%s" (String.concat " " (Array.to_list Sys.argv));
  log "server start";
  let run_lwt () : unit Lwt.t =
    let argv = Array.to_list Sys.argv in
    let cli_path =
      match argv with
      | prog :: _ -> prog
      | [] -> Easycrypt_cli.default_cli_path ()
    in
    let proof = EcProofCore.create ~log:(fun msg -> log "%s" msg) ~cli_path ~cli_args:[] () in
    let ic = Lwt_io.of_fd ~mode:Lwt_io.input Lwt_unix.stdin in
    let oc = Lwt_io.of_fd ~mode:Lwt_io.output Lwt_unix.stdout in
    let shutdown = ref false in
    let pending : (Jsonrpc.Id.t * proof_command) Queue.t = Queue.create () in
    let current : unit Lwt.t option ref = ref None in

    let handle_initialize id (params : Lsp.Types.InitializeParams.t) : unit Lwt.t =
      log "initialize";
      let capabilities =
        Lsp.Types.ServerCapabilities.create
          ~textDocumentSync:(`TextDocumentSyncKind Lsp.Types.TextDocumentSyncKind.Incremental)
          ()
      in
      let result = Lsp.Types.InitializeResult.create ~capabilities () in
      send_typed_response oc id (Lsp.Client_request.Initialize params) result
    in

    let handle_proof_next id uri : unit Lwt.t =
      log "proof next";
      let* result = EcProofCore.proof_next proof ~uri in
      send_response oc id (json_of_proof_result result)
    in

    let handle_proof_exec id uri : unit Lwt.t =
      log "proof exec";
      let* result = EcProofCore.proof_step proof ~uri in
      send_response oc id (json_of_proof_result result)
    in

    let handle_proof_jump id uri target : unit Lwt.t =
      log "proof jump";
      let* result = EcProofCore.proof_jump_to proof ~uri ~target in
      send_response oc id (json_of_proof_result result)
    in

    let handle_proof_back id uri : unit Lwt.t =
      log "proof back";
      let* result = EcProofCore.proof_back proof ~uri in
      send_response oc id (json_of_proof_result result)
    in

    let handle_proof_restart id uri : unit Lwt.t =
      log "proof restart";
      let* result = EcProofCore.proof_restart proof ~uri in
      send_response oc id (json_of_proof_result result)
    in

    let handle_proof_goals id uri : unit Lwt.t =
      log "proof goals";
      let* result = EcProofCore.proof_goals proof ~uri in
      send_response oc id (json_of_proof_result result)
    in

    let handle_query id uri keyword query : unit Lwt.t =
      log "query %s" keyword;
      let kind =
        match keyword with
        | "print" -> `Print
        | "locate" -> `Locate
        | "search" -> `Search
        | _ -> invalid_arg "unknown query kind"
      in
      let* result = EcProofCore.query proof ~uri ~kind ~query in
      send_response oc id (json_of_query_result result)
    in

    let execute_proof_command (id : Jsonrpc.Id.t) (cmd : proof_command) : unit Lwt.t =
      match cmd.cmd with
      | Proof_next -> handle_proof_next id cmd.uri
      | Proof_step -> handle_proof_exec id cmd.uri
      | Proof_jump_to target -> handle_proof_jump id cmd.uri target
      | Proof_back -> handle_proof_back id cmd.uri
      | Proof_restart -> handle_proof_restart id cmd.uri
      | Proof_goals -> handle_proof_goals id cmd.uri
      | Query_print query -> handle_query id cmd.uri "print" query
      | Query_locate query -> handle_query id cmd.uri "locate" query
      | Query_search query -> handle_query id cmd.uri "search" query
    in

    let start_proof (id : Jsonrpc.Id.t) (cmd : proof_command) : unit Lwt.t =
      Lwt.catch
        (fun () -> execute_proof_command id cmd)
        (fun e ->
           log "proof command error: %s" (Printexc.to_string e);
           send_error oc id Jsonrpc.Response.Error.Code.InternalError "proof command failed")
    in

    let pop_pending () =
      if Queue.is_empty pending then None else Some (Queue.take pending)
    in

    let handle_request req : unit Lwt.t =
      match Lsp.Client_request.of_jsonrpc req with
      | Error message ->
            send_error oc req.id Jsonrpc.Response.Error.Code.InvalidParams message
      | Ok (Lsp.Client_request.E r) -> (
          match r with
          | Lsp.Client_request.Initialize params ->
              handle_initialize req.id params
          | Lsp.Client_request.Shutdown ->
              shutdown := true;
              send_typed_response oc req.id r ()
          | Lsp.Client_request.UnknownRequest { meth; params } -> (
              let params = Option.map Jsonrpc.Structured.yojson_of_t params in
              match proof_command_of_request meth params with
              | Ok cmd ->
                  (match !current with
                   | None ->
                       let task = start_proof req.id cmd in
                       current := Some task;
                       Lwt.return_unit
                   | Some _ ->
                       Queue.push (req.id, cmd) pending;
                       Lwt.return_unit)
              | Error "Method not found" ->
                  send_error oc req.id Jsonrpc.Response.Error.Code.MethodNotFound "Method not found"
              | Error message ->
                  send_error oc req.id Jsonrpc.Response.Error.Code.InvalidParams message)
          | _ ->
              send_error oc req.id Jsonrpc.Response.Error.Code.MethodNotFound "Method not found")
    in

    let handle_notification_packet notif : unit Lwt.t =
      match Lsp.Client_notification.of_jsonrpc notif with
      | Error _ -> Lwt.return_unit
      | Ok notification -> (
          match notification with
          | Lsp.Client_notification.Initialized -> Lwt.return_unit
          | Lsp.Client_notification.Exit -> shutdown := true; Lwt.return_unit
          | Lsp.Client_notification.TextDocumentDidOpen params ->
              let uri =
                Lsp.Types.DocumentUri.to_string
                  params.Lsp.Types.DidOpenTextDocumentParams.textDocument.uri
              in
              EcProofCore.did_open proof ~uri
                ~text:params.Lsp.Types.DidOpenTextDocumentParams.textDocument.text;
              Lwt.return_unit
          | Lsp.Client_notification.TextDocumentDidChange params ->
              let uri =
                Lsp.Types.DocumentUri.to_string
                  params.Lsp.Types.DidChangeTextDocumentParams.textDocument.uri
              in
              let changes =
                List.map core_change_of_lsp
                  params.Lsp.Types.DidChangeTextDocumentParams.contentChanges
              in
              EcProofCore.did_change proof ~uri changes
          | Lsp.Client_notification.TextDocumentDidClose params ->
              let uri =
                Lsp.Types.DocumentUri.to_string
                  params.Lsp.Types.DidCloseTextDocumentParams.textDocument.uri
              in
              EcProofCore.did_close proof ~uri
          | _ -> Lwt.return_unit)
    in

    let rec loop () : unit Lwt.t =
      if !shutdown then
        Lwt.return_unit
      else
        let read_p = Lsp_io.read ic |> Lwt.map (fun p -> `Packet p) in
        let waiters =
          match !current with
          | None -> [ read_p ]
          | Some cmd_p -> [ read_p; (cmd_p |> Lwt.map (fun () -> `Cmd_done)) ]
        in
        let* ev = Lwt.pick waiters in
        match ev with
        | `Cmd_done ->
            current := None;
            (match pop_pending () with
             | None -> ()
             | Some (id, cmd) -> current := Some (start_proof id cmd));
            loop ()
        | `Packet None ->
            log "stdin closed";
            shutdown := true;
            Lwt.return_unit
        | `Packet (Some packet) ->
            let* () =
              match packet with
              | Jsonrpc.Packet.Request req ->
                  log "recv request %s" req.Jsonrpc.Request.method_;
                  handle_request req
              | Jsonrpc.Packet.Notification notif ->
                  log "recv notification %s" notif.Jsonrpc.Notification.method_;
                  handle_notification_packet notif
              | Jsonrpc.Packet.Batch_call calls ->
                  Lwt_list.iter_s
                    (function
                      | `Request req -> handle_request req
                      | `Notification notif -> handle_notification_packet notif)
                    calls
              | Jsonrpc.Packet.Response _ -> Lwt.return_unit
              | Jsonrpc.Packet.Batch_response _ -> Lwt.return_unit
            in
      let* () = loop () in
      EcProofCore.close proof
    in
    loop ()
  in
  Lwt_main.run (run_lwt ())
