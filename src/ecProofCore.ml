open Lwt.Syntax

type position = {
  line : int;
  character : int;
}

type range = {
  start_ : position;
  end_ : position;
}

type text_change = {
  range : range option;
  text : string;
}

type proof_response = {
  output : string;
  uuid : int;
  mode : string;
  processed_end : int;
  sentence_start : int option;
  sentence_end : int option;
}

type query_kind = [ `Print | `Locate | `Search ]

type query_response = {
  output : string;
}

type logger = string -> unit

let noop_log _ = ()

let logf (log : logger) fmt =
  Format.kasprintf log fmt

module Easycrypt_cli = struct
  type session = {
    proc : Lwt_process.process;
    mutable uuid : int;
    mutable mode : string;
    mutable last_output : string;
    root_uuid : int;
  }

  type config = {
    cli_path : string;
    cli_args : string list;
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

  let read_until_prompt ~(log : logger) (sess : session) : string Lwt.t =
    let buf = Buffer.create 256 in
    let rec loop () =
      let* line_opt = Lwt_io.read_line_opt sess.proc#stdout in
      match line_opt with
      | None -> Lwt.return (Buffer.contents buf)
      | Some line ->
          logf log "cli<line %s" (String.escaped line);
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

  let start_session ~(log : logger) (cfg : config) : session Lwt.t =
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
    let* _ = read_until_prompt ~log sess in
    Lwt.return { sess with root_uuid = sess.uuid }

  let send_command
      ~(log : logger)
      ?(record_last_output = true)
      (sess : session)
      (text : string) : string Lwt.t =
    logf log "cli> %s" (String.trim text);
    let write =
      if String.ends_with ~suffix:"\n" text then
        Lwt_io.write sess.proc#stdin text
      else
        Lwt_io.write_line sess.proc#stdin text
    in
    let* () = write in
    let* () = Lwt_io.flush sess.proc#stdin in
    let* output = read_until_prompt ~log sess in
    if record_last_output then
      sess.last_output <- output;
    let preview =
      if String.length output = 0 then "<empty>"
      else if String.length output <= 200 then String.escaped output
      else String.escaped (String.sub output 0 200) ^ "..."
    in
    logf log "cli< (%d bytes) %s" (String.length output) preview;
    Lwt.return output

  let send_undo ~(log : logger) (sess : session) (target_uuid : int) : string Lwt.t =
    let cmd = Printf.sprintf "undo %d." target_uuid in
    send_command ~log sess cmd

  let stop_session (sess : session) : unit Lwt.t =
    let close_chan ch = Lwt.catch (fun () -> Lwt_io.close ch) (fun _ -> Lwt.return_unit) in
    let* () = close_chan sess.proc#stdin in
    let* () = close_chan sess.proc#stdout in
    sess.proc#terminate;
    let* _ = sess.proc#status in
    Lwt.return_unit
end

type doc_state = {
  mutable text : BatText.t;
  mutable last_offset : int;
  mutable history : (int * int) list;
  mutable session : Easycrypt_cli.session option;
}

type t = {
  log : logger;
  cfg : Easycrypt_cli.config;
  docs : (string, doc_state) Hashtbl.t;
}

let create ?(log = noop_log) ~cli_path ~cli_args () =
  { log
  ; cfg = { Easycrypt_cli.cli_path; cli_args }
  ; docs = Hashtbl.create 16
  }

let get_doc_state (state : t) (uri : string) : doc_state =
  match Hashtbl.find_opt state.docs uri with
  | Some doc -> doc
  | None ->
      let created = { text = BatText.empty; last_offset = 0; history = []; session = None } in
      Hashtbl.add state.docs uri created;
      created

let error_tag_re : Pcre2.regexp =
  Pcre2.regexp "\\[error-\\d+-\\d+\\]"

let output_has_error (output : string) : bool =
  Pcre2.pmatch ~rex:error_tag_re output

let find_next_sentence (text : BatText.t) (start : int) : (string * int * int) option =
  EcIo.next_sentence_from (BatText.to_string text) start

let position_to_offset (text : BatText.t) (pos : position) : int =
  let len = BatText.length text in
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
  let line_start = find_line_start pos.line 0 in
  if line_start >= len then
    len
  else
    min len (line_start + pos.character)

let apply_change (text : BatText.t) (change : text_change) : BatText.t * int =
  match change.range with
  | None ->
      BatText.of_string change.text, 0
  | Some range ->
      let start_offset = position_to_offset text range.start_ in
      let end_offset = position_to_offset text range.end_ in
      let len = BatText.length text in
      let start_offset = max 0 (min start_offset len) in
      let end_offset = max start_offset (min end_offset len) in
      let removed = BatText.remove start_offset (end_offset - start_offset) text in
      let inserted = BatText.of_string change.text in
      (BatText.insert start_offset inserted removed, start_offset)

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

let response_of_doc ~(sess : Easycrypt_cli.session) ~(doc : doc_state) ?sentence output =
  let sentence_start, sentence_end =
    match sentence with
    | None -> (None, None)
    | Some (start_, end_) -> (Some start_, Some end_)
  in
  { output
  ; uuid = sess.uuid
  ; mode = sess.mode
  ; processed_end = doc.last_offset
  ; sentence_start
  ; sentence_end
  }

let ensure_session (state : t) (doc : doc_state) : Easycrypt_cli.session Lwt.t =
  match doc.session with
  | Some sess -> Lwt.return sess
  | None ->
      let* sess = Easycrypt_cli.start_session ~log:state.log state.cfg in
      doc.session <- Some sess;
      Lwt.return sess

let with_session_retry
    (state : t)
    (doc : doc_state)
    (f : Easycrypt_cli.session -> 'a Lwt.t) : 'a Lwt.t =
  let rec run ~retry =
    let* sess = ensure_session state doc in
    Lwt.catch
      (fun () -> f sess)
      (function
        | Sys_error msg when retry && String.lowercase_ascii msg = "broken pipe" ->
            logf state.log "cli broken pipe; restarting session";
            doc.session <- None;
            run ~retry:false
        | e -> Lwt.fail e)
  in
  run ~retry:true

let rewind_to_offset (state : t) (doc : doc_state) (sess : Easycrypt_cli.session) (target : int) :
    string option Lwt.t =
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
      | Some (offset, uuid) -> (uuid, offset)
    in
    doc.history <- List.filter (fun (offset, _) -> offset <= new_offset) doc.history;
    doc.last_offset <- new_offset;
    let* output = Easycrypt_cli.send_undo ~log:state.log sess target_uuid in
    Lwt.return (Some output)

let did_open (state : t) ~(uri : string) ~(text : string) : unit =
  let doc = get_doc_state state uri in
  doc.text <- BatText.of_string text;
  doc.last_offset <- 0;
  doc.history <- [];
  doc.session <- None

let did_change (state : t) ~(uri : string) (changes : text_change list) : unit Lwt.t =
  let doc = get_doc_state state uri in
  let earliest = ref max_int in
  let updated = ref doc.text in
  List.iter
    (fun change ->
       let text, start_offset = apply_change !updated change in
       updated := text;
       if start_offset < !earliest then earliest := start_offset)
    changes;
  doc.text <- !updated;
  if !earliest < doc.last_offset then
    let* sess = ensure_session state doc in
    let* _ = rewind_to_offset state doc sess !earliest in
    Lwt.return_unit
  else
    Lwt.return_unit

let did_close (state : t) ~(uri : string) : unit Lwt.t =
  let* () =
    match Hashtbl.find_opt state.docs uri with
    | Some doc -> (
        match doc.session with
        | Some sess -> Easycrypt_cli.stop_session sess
        | None -> Lwt.return_unit)
    | None -> Lwt.return_unit
  in
  Hashtbl.remove state.docs uri;
  Lwt.return_unit

let close (state : t) : unit Lwt.t =
  let sessions =
    Hashtbl.to_seq_values state.docs
    |> List.of_seq
    |> List.filter_map (fun doc -> doc.session)
  in
  Lwt_list.iter_s Easycrypt_cli.stop_session sessions

let proof_next (state : t) ~(uri : string) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  match find_next_sentence doc.text doc.last_offset with
  | None -> Lwt.return (response_of_doc ~sess ~doc sess.last_output)
  | Some (_, start_, end_) ->
      Lwt.return (response_of_doc ~sess ~doc ~sentence:(start_, end_) sess.last_output)

let proof_step (state : t) ~(uri : string) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  match find_next_sentence doc.text doc.last_offset with
  | None ->
      let* sess = ensure_session state doc in
      Lwt.return (response_of_doc ~sess ~doc sess.last_output)
  | Some (text, start_, end_) ->
      let previous_offset = doc.last_offset in
      let* sess, output =
        with_session_retry state doc (fun sess ->
            let* output = Easycrypt_cli.send_command ~log:state.log sess text in
            Lwt.return (sess, output))
      in
      if output_has_error output then (
        doc.last_offset <- previous_offset;
        Lwt.return (response_of_doc ~sess ~doc ~sentence:(start_, end_) output))
      else (
        doc.last_offset <- end_;
        doc.history <- doc.history @ [ (doc.last_offset, sess.uuid) ];
        Lwt.return (response_of_doc ~sess ~doc ~sentence:(start_, end_) output))

let proof_jump_to (state : t) ~(uri : string) ~(target : int) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  let text_len = BatText.length doc.text in
  let target = max 0 (min target text_len) in
  let respond ?sentence output =
    Lwt.return (response_of_doc ~sess ~doc ?sentence output)
  in
  if target < doc.last_offset then (
    let* output =
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
        | Some (offset, uuid) -> (uuid, offset)
      in
      doc.history <- List.filter (fun (offset, _) -> offset <= new_offset) doc.history;
      doc.last_offset <- new_offset;
      Easycrypt_cli.send_undo ~log:state.log sess target_uuid
    in
    respond output)
  else if target = doc.last_offset then
    respond sess.last_output
  else
    let rec loop last_output =
      if doc.last_offset >= target then
        respond last_output
      else
        match find_next_sentence doc.text doc.last_offset with
        | None -> respond last_output
        | Some (text, start_, end_) ->
            if end_ > target then
              respond last_output
            else
              let previous_offset = doc.last_offset in
              let* output = Easycrypt_cli.send_command ~log:state.log sess text in
              if output_has_error output then (
                doc.last_offset <- previous_offset;
                respond ~sentence:(start_, end_) output)
              else (
                doc.last_offset <- end_;
                doc.history <- doc.history @ [ (doc.last_offset, sess.uuid) ];
                loop output)
    in
    loop sess.last_output

let proof_back (state : t) ~(uri : string) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  match List.rev doc.history with
  | [] -> Lwt.return (response_of_doc ~sess ~doc sess.last_output)
  | _last :: rest_rev ->
      let target_uuid, new_offset =
        match rest_rev with
        | [] -> (sess.root_uuid, 0)
        | (offset, uuid) :: _ -> (uuid, offset)
      in
      let* output = Easycrypt_cli.send_undo ~log:state.log sess target_uuid in
      doc.history <- List.rev rest_rev;
      doc.last_offset <- new_offset;
      Lwt.return (response_of_doc ~sess ~doc output)

let proof_restart (state : t) ~(uri : string) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  let* output = Easycrypt_cli.send_undo ~log:state.log sess sess.root_uuid in
  doc.history <- [];
  doc.last_offset <- 0;
  Lwt.return (response_of_doc ~sess ~doc output)

let proof_goals (state : t) ~(uri : string) : proof_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  Lwt.return (response_of_doc ~sess ~doc sess.last_output)

let normalize_query_command (kind : query_kind) (query : string) : string =
  let keyword =
    match kind with
    | `Print -> "print"
    | `Locate -> "locate"
    | `Search -> "search"
  in
  let query = String.trim query in
  if query = "" then
    invalid_arg "empty query"
  else
    let query =
      if String.ends_with ~suffix:"." query then
        String.sub query 0 (String.length query - 1)
      else
        query
    in
    Printf.sprintf "%s %s." keyword query

let query (state : t) ~(uri : string) ~(kind : query_kind) ~(query : string) : query_response Lwt.t =
  let doc = get_doc_state state uri in
  let* sess = ensure_session state doc in
  let command = normalize_query_command kind query in
  let* output =
    Easycrypt_cli.send_command ~log:state.log ~record_last_output:false sess command
  in
  Lwt.return { output = strip_trailing_goal output sess.last_output }
