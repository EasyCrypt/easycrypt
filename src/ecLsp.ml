open Lwt.Syntax

module Json = Yojson.Safe
module J = Yojson.Safe.Util

module Lsp_io =
  Lsp.Io.Make
    (struct
      type 'a t = 'a

      let return x = x
      let raise = Stdlib.raise

      module O = struct
        let ( let+ ) x f = f x
        let ( let* ) x f = f x
      end
    end)
    (struct
      type input = in_channel
      type output = out_channel

      let read_line ic =
        try Some (input_line ic) with End_of_file -> None

      let read_exactly ic len =
        try Some (really_input_string ic len) with End_of_file -> None

      let write oc chunks =
        List.iter (output_string oc) chunks;
        flush oc
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

  let start_session_lwt (cfg : config) : session Lwt.t =
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

  let start_session (cfg : config) : session =
    Lwt_main.run (start_session_lwt cfg)

  let send_command_lwt (sess : session) (text : string) : string Lwt.t =
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
    sess.last_output <- output;
    let preview =
      if String.length output = 0 then "<empty>"
      else if String.length output <= 200 then String.escaped output
      else String.escaped (String.sub output 0 200) ^ "..."
    in
    log "cli< (%d bytes) %s" (String.length output) preview;
    Lwt.return output

  let send_command (sess : session) (text : string) : string =
    Lwt_main.run (send_command_lwt sess text)

  let send_undo_lwt (sess : session) (target_uuid : int) : string Lwt.t =
    let cmd = Printf.sprintf "undo %d." target_uuid in
    send_command_lwt sess cmd

  let send_undo (sess : session) (target_uuid : int) : string =
    Lwt_main.run (send_undo_lwt sess target_uuid)

  let stop_session_lwt (sess : session) : unit Lwt.t =
    let close_chan ch = Lwt.catch (fun () -> Lwt_io.close ch) (fun _ -> Lwt.return_unit) in
    let* () = close_chan sess.proc#stdin in
    let* () = close_chan sess.proc#stdout in
    sess.proc#terminate;
    let* _status = sess.proc#status in
    Lwt.return_unit

  let stop_session (sess : session) : unit =
    Lwt_main.run (stop_session_lwt sess)
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

type proof_command_kind =
  | Proof_next
  | Proof_step
  | Proof_jump_to of int
  | Proof_back
  | Proof_restart
  | Proof_goals

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
    | _ -> Error "Method not found"

let rewind_to_offset
    (doc : doc_state)
    (sess : Easycrypt_cli.session)
    (target : int) : string option =
  if target >= doc.last_offset then
    None
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
    Some (Easycrypt_cli.send_undo sess target_uuid)

let send_packet (oc : out_channel) (packet : Jsonrpc.Packet.t) =
  Lsp_io.write oc packet

let send_response (oc : out_channel) (id : Jsonrpc.Id.t) (result : Jsonrpc.Json.t) =
  let response = Jsonrpc.Response.ok id result in
  send_packet oc (Jsonrpc.Packet.Response response)

let send_typed_response
    (oc : out_channel)
    (id : Jsonrpc.Id.t)
    (req : 'a Lsp.Client_request.t)
    (result : 'a) =
  let payload = Lsp.Client_request.yojson_of_result req result in
  send_response oc id payload

let send_error
    (oc : out_channel)
    (id : Jsonrpc.Id.t)
    (code : Jsonrpc.Response.Error.Code.t)
    (message : string) =
  let error =
    Jsonrpc.Response.Error.make
      ~code
      ~message
      ()
  in
  let response = Jsonrpc.Response.error id error in
  send_packet oc (Jsonrpc.Packet.Response response)

let send_notification (oc : out_channel) (method_ : string) (params : Jsonrpc.Json.t) =
  let params_struct = Jsonrpc.Structured.t_of_yojson params in
  let notif = Jsonrpc.Notification.create ~params:params_struct ~method_ () in
  send_packet oc (Jsonrpc.Packet.Notification notif)

let run () : unit =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  setup_logging ();
  log "argv=%s" (String.concat " " (Array.to_list Sys.argv));
  log "server start";
  let argv = Array.to_list Sys.argv in
  let cli_path =
    match argv with
    | prog :: _ -> prog
    | [] -> Easycrypt_cli.default_cli_path ()
  in
  let cfg : Easycrypt_cli.config = { cli_path; cli_args = []; } in
  let ic = stdin in
  let oc = stdout in
  let shutdown = ref false in

  let get_session_for_doc (doc : doc_state) : Easycrypt_cli.session =
    match doc.session with
    | Some sess -> sess
    | None ->
        let sess = Easycrypt_cli.start_session cfg in
        doc.session <- Some sess;
        sess
  in

  let handle_initialize id (params : Lsp.Types.InitializeParams.t) =
    log "initialize";
    let capabilities =
      Lsp.Types.ServerCapabilities.create
        ~textDocumentSync:(`TextDocumentSyncKind Lsp.Types.TextDocumentSyncKind.Incremental)
        ()
    in
    let result = Lsp.Types.InitializeResult.create ~capabilities () in
    send_typed_response oc id (Lsp.Client_request.Initialize params) result
  in

  let handle_proof_next id uri =
    log "proof next";
    let doc = get_doc_state uri in
    let sess = get_session_for_doc doc in
    match find_next_sentence doc.text doc.last_offset with
    | None ->
        send_response oc id (json_of_proof_response ~sess ~doc sess.last_output)
    | Some (_text, start, end_) ->
        send_response oc id (json_of_proof_response ~sess ~doc ~sentence:(start, end_) sess.last_output)
  in

  let handle_proof_exec id uri =
    log "proof exec";
    let doc = get_doc_state uri in
    match find_next_sentence doc.text doc.last_offset with
    | None ->
        let sess = get_session_for_doc doc in
        send_response oc id (json_of_proof_response ~sess ~doc sess.last_output)
    | Some (text, start, end_) -> (
        let previous_offset = doc.last_offset in
        try
          let rec run ~retry =
            let sess = get_session_for_doc doc in
            try (sess, Easycrypt_cli.send_command sess text) with
            | Sys_error msg when retry && String.lowercase_ascii msg = "broken pipe" ->
                log "cli broken pipe; restarting session";
                doc.session <- None;
                run ~retry:false
          in
          let sess, output = run ~retry:true in
          if output_has_error output then (
            doc.last_offset <- previous_offset;
            send_response oc id
              (json_of_proof_response ~sess ~doc ~sentence:(start, end_) output))
          else (
            doc.last_offset <- end_;
            doc.history <- doc.history @ [ (doc.last_offset, sess.uuid) ];
            send_response oc id
              (json_of_proof_response ~sess ~doc ~sentence:(start, end_) output))
        with e ->
          log "proof exec error: %s" (Printexc.to_string e);
          send_error oc id Jsonrpc.Response.Error.Code.InternalError "proof exec failed")
  in

  let handle_proof_jump id uri target =
    log "proof jump";
    let doc = get_doc_state uri in
    let sess = get_session_for_doc doc in
    let text_len = BatText.length doc.text in
    let target = max 0 (min target text_len) in
    let respond ?sentence output =
      send_response oc id (json_of_proof_response ~sess ~doc ?sentence output)
    in
    if target < doc.last_offset then (
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
      let output = Easycrypt_cli.send_undo sess target_uuid in
      respond output)
    else if target = doc.last_offset then
      respond sess.last_output
    else (
      let rec loop last_output =
        if doc.last_offset >= target then
          respond last_output
        else
          match find_next_sentence doc.text doc.last_offset with
          | None -> respond last_output
          | Some (text, start, end_) ->
              if end_ > target then
                respond last_output
              else
                let previous_offset = doc.last_offset in
                let output = Easycrypt_cli.send_command sess text in
                if output_has_error output then (
                  doc.last_offset <- previous_offset;
                  respond ~sentence:(start, end_) output)
                else (
                  doc.last_offset <- end_;
                  doc.history <- doc.history @ [ (doc.last_offset, sess.uuid) ];
                  loop output)
      in
      loop sess.last_output)
  in

  let handle_proof_back id uri =
    log "proof back";
    let doc = get_doc_state uri in
    let sess = get_session_for_doc doc in
    match List.rev doc.history with
    | [] ->
        send_response oc id (json_of_proof_response ~sess ~doc sess.last_output)
    | _last :: rest_rev ->
        let target_uuid, new_offset =
          match rest_rev with
          | [] -> sess.root_uuid, 0
          | (offset, uuid) :: _ -> uuid, offset
        in
        let output = Easycrypt_cli.send_undo sess target_uuid in
        doc.history <- List.rev rest_rev;
        doc.last_offset <- new_offset;
        send_response oc id (json_of_proof_response ~sess ~doc output)
  in

  let handle_proof_restart id uri =
    log "proof restart";
    let doc = get_doc_state uri in
    let sess = get_session_for_doc doc in
    let output = Easycrypt_cli.send_undo sess sess.root_uuid in
    doc.history <- [];
    doc.last_offset <- 0;
    send_response oc id (json_of_proof_response ~sess ~doc output)
  in

  let handle_proof_goals id uri =
    log "proof goals";
    let doc = get_doc_state uri in
    let sess = get_session_for_doc doc in
    send_response oc id (json_of_proof_response ~sess ~doc sess.last_output)
  in

  let execute_proof_command (id : Jsonrpc.Id.t) (cmd : proof_command) =
    match cmd.cmd with
    | Proof_next -> handle_proof_next id cmd.uri
    | Proof_step -> handle_proof_exec id cmd.uri
    | Proof_jump_to target -> handle_proof_jump id cmd.uri target
    | Proof_back -> handle_proof_back id cmd.uri
    | Proof_restart -> handle_proof_restart id cmd.uri
    | Proof_goals -> handle_proof_goals id cmd.uri
  in

  let handle_request req =
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
            | Ok cmd -> execute_proof_command req.id cmd
            | Error "Method not found" ->
                send_error oc req.id Jsonrpc.Response.Error.Code.MethodNotFound "Method not found"
            | Error message ->
                send_error oc req.id Jsonrpc.Response.Error.Code.InvalidParams message)
        | _ ->
            send_error oc req.id Jsonrpc.Response.Error.Code.MethodNotFound "Method not found")
  in

  let handle_notification_packet notif =
    match Lsp.Client_notification.of_jsonrpc notif with
    | Error _ -> ()
    | Ok notification -> (
        match notification with
        | Lsp.Client_notification.Initialized -> ()
        | Lsp.Client_notification.Exit -> shutdown := true
        | Lsp.Client_notification.TextDocumentDidOpen params ->
            let uri =
              Lsp.Types.DocumentUri.to_string
                params.Lsp.Types.DidOpenTextDocumentParams.textDocument.uri
            in
            let doc = get_doc_state uri in
            doc.text <- BatText.of_string params.Lsp.Types.DidOpenTextDocumentParams.textDocument.text;
            doc.last_offset <- 0;
            doc.history <- [];
            doc.session <- None
        | Lsp.Client_notification.TextDocumentDidChange params ->
            let uri =
              Lsp.Types.DocumentUri.to_string
                params.Lsp.Types.DidChangeTextDocumentParams.textDocument.uri
            in
            let doc = get_doc_state uri in
            let earliest = ref max_int in
            let updated = ref doc.text in
            List.iter
              (fun change ->
                 let text, start_offset = apply_change !updated change in
                 updated := text;
                 if start_offset < !earliest then earliest := start_offset)
              params.Lsp.Types.DidChangeTextDocumentParams.contentChanges;
            doc.text <- !updated;
            if !earliest < doc.last_offset then
              let sess = get_session_for_doc doc in
              ignore (rewind_to_offset doc sess !earliest)
        | Lsp.Client_notification.TextDocumentDidClose params ->
            let uri =
              Lsp.Types.DocumentUri.to_string
                params.Lsp.Types.DidCloseTextDocumentParams.textDocument.uri
            in
            (match Hashtbl.find_opt doc_states uri with
             | Some doc -> Option.iter Easycrypt_cli.stop_session doc.session
             | None -> ());
            Hashtbl.remove doc_states uri
        | _ -> ())
  in

  while not !shutdown do
    match Lsp_io.read ic with
    | None ->
        log "stdin closed";
        shutdown := true
    | Some packet ->
        (try
           match packet with
           | Jsonrpc.Packet.Request req ->
               log "recv request %s" req.Jsonrpc.Request.method_;
               handle_request req
           | Jsonrpc.Packet.Notification notif ->
               log "recv notification %s" notif.Jsonrpc.Notification.method_;
               handle_notification_packet notif
           | Jsonrpc.Packet.Batch_call calls ->
               List.iter
                 (function
                   | `Request req -> handle_request req
                   | `Notification notif -> handle_notification_packet notif)
                 calls
           | Jsonrpc.Packet.Response _ -> ()
           | Jsonrpc.Packet.Batch_response _ -> ()
         with e ->
           log "error: %s" (Printexc.to_string e))
  done
