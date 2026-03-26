open Lwt.Syntax

module Json = Yojson.Safe
module J = Yojson.Safe.Util

module Rpc_io =
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

let send_packet (oc : Lwt_io.output_channel) (packet : Jsonrpc.Packet.t) : unit Lwt.t =
  Rpc_io.write oc packet

let send_response (oc : Lwt_io.output_channel) (id : Jsonrpc.Id.t) (result : Json.t) : unit Lwt.t =
  let response = Jsonrpc.Response.ok id result in
  send_packet oc (Jsonrpc.Packet.Response response)

let send_error
    (oc : Lwt_io.output_channel)
    (id : Jsonrpc.Id.t)
    (code : Jsonrpc.Response.Error.Code.t)
    (message : string) : unit Lwt.t =
  let error = Jsonrpc.Response.Error.make ~code ~message () in
  let response = Jsonrpc.Response.error id error in
  send_packet oc (Jsonrpc.Packet.Response response)

let text_result ?(is_error = false) (text : string) : Json.t =
  `Assoc
    [ ("content", `List [ `Assoc [ ("type", `String "text"); ("text", `String text) ] ])
    ; ("isError", `Bool is_error)
    ]

let protocol_version = "2024-11-05"

let initialize_result (client_version : string option) : Json.t =
  let protocol_version = Option.value ~default:protocol_version client_version in
  `Assoc
    [ ("protocolVersion", `String protocol_version)
    ; ("capabilities", `Assoc [ ("tools", `Assoc [ ("listChanged", `Bool false) ]) ])
    ; ("serverInfo", `Assoc [ ("name", `String "easycrypt"); ("version", `String EcVersion.hash) ])
    ]

let query_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("uri", `Assoc [ ("type", `String "string") ])
         ; ("query", `Assoc [ ("type", `String "string") ])
         ])
    ; ("required", `List [ `String "uri"; `String "query" ])
    ]

let uri_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties", `Assoc [ ("uri", `Assoc [ ("type", `String "string") ]) ])
    ; ("required", `List [ `String "uri" ])
    ]

let jump_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("uri", `Assoc [ ("type", `String "string") ])
         ; ("target", `Assoc [ ("type", `String "integer") ])
         ])
    ; ("required", `List [ `String "uri"; `String "target" ])
    ]

let open_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("uri", `Assoc [ ("type", `String "string") ])
         ; ("text", `Assoc [ ("type", `String "string") ])
         ])
    ; ("required", `List [ `String "uri"; `String "text" ])
    ]

let position_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("line", `Assoc [ ("type", `String "integer") ])
         ; ("character", `Assoc [ ("type", `String "integer") ])
         ])
    ; ("required", `List [ `String "line"; `String "character" ])
    ]

let range_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("start", position_schema)
         ; ("end", position_schema)
         ])
    ; ("required", `List [ `String "start"; `String "end" ])
    ]

let change_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("range", range_schema)
         ; ("text", `Assoc [ ("type", `String "string") ])
         ])
    ; ("required", `List [ `String "text" ])
    ]

let apply_changes_schema : Json.t =
  `Assoc
    [ ("type", `String "object")
    ; ("properties",
       `Assoc
         [ ("uri", `Assoc [ ("type", `String "string") ])
         ; ("changes", `Assoc [ ("type", `String "array"); ("items", change_schema) ])
         ])
    ; ("required", `List [ `String "uri"; `String "changes" ])
    ]

let tools_list_result : Json.t =
  `Assoc
    [ ("tools",
       `List
         [ `Assoc
             [ ("name", `String "open_document")
             ; ("title", `String "Open Document")
             ; ("description", `String "Register or replace a document in EasyCrypt proof state")
             ; ("inputSchema", open_schema)
             ]
         ; `Assoc
             [ ("name", `String "apply_changes")
             ; ("title", `String "Apply Changes")
             ; ("description", `String "Apply text changes to a document")
             ; ("inputSchema", apply_changes_schema)
             ]
         ; `Assoc
             [ ("name", `String "close_document")
             ; ("title", `String "Close Document")
             ; ("description", `String "Close a document and stop its EasyCrypt session")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_next")
             ; ("title", `String "Proof Next")
             ; ("description", `String "Preview the next EasyCrypt sentence")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_step")
             ; ("title", `String "Proof Step")
             ; ("description", `String "Execute the next EasyCrypt sentence")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_jump_to")
             ; ("title", `String "Proof Jump To")
             ; ("description", `String "Execute EasyCrypt sentences up to a target offset")
             ; ("inputSchema", jump_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_back")
             ; ("title", `String "Proof Back")
             ; ("description", `String "Undo one processed EasyCrypt sentence")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_restart")
             ; ("title", `String "Proof Restart")
             ; ("description", `String "Restart the EasyCrypt proof state")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "proof_goals")
             ; ("title", `String "Proof Goals")
             ; ("description", `String "Return the current EasyCrypt goals output")
             ; ("inputSchema", uri_schema)
             ]
         ; `Assoc
             [ ("name", `String "query_print")
             ; ("title", `String "Query Print")
             ; ("description", `String "Run EasyCrypt print in the current proof session")
             ; ("inputSchema", query_schema)
             ]
         ; `Assoc
             [ ("name", `String "query_locate")
             ; ("title", `String "Query Locate")
             ; ("description", `String "Run EasyCrypt locate in the current proof session")
             ; ("inputSchema", query_schema)
             ]
         ; `Assoc
             [ ("name", `String "query_search")
             ; ("title", `String "Query Search")
             ; ("description", `String "Run EasyCrypt search in the current proof session")
             ; ("inputSchema", query_schema)
             ]
         ])
    ]

let proof_text (result : EcProofCore.proof_response) : string =
  let sentence =
    match result.sentence_start, result.sentence_end with
    | Some start_, Some end_ ->
        Printf.sprintf "sentenceStart=%d\nsentenceEnd=%d\n" start_ end_
    | _ -> ""
  in
  Printf.sprintf
    "uuid=%d\nmode=%s\nprocessedEnd=%d\n%s%s"
    result.uuid result.mode result.processed_end sentence result.output

let get_uri json =
  match J.member "uri" json with
  | `String uri when uri <> "" -> Ok uri
  | _ -> Error "missing uri"

let get_query json =
  match J.member "query" json with
  | `String query when String.trim query <> "" -> Ok (String.trim query)
  | _ -> Error "missing query"

let get_target json =
  try Ok (J.member "target" json |> J.to_int) with _ -> Error "missing target"

let get_text json =
  match J.member "text" json with
  | `String text -> Ok text
  | _ -> Error "missing text"

let get_position json =
  try
    Ok
      { EcProofCore.line = J.member "line" json |> J.to_int
      ; character = J.member "character" json |> J.to_int
      }
  with _ -> Error "invalid position"

let get_range json =
  match J.member "range" json with
  | `Null -> Ok None
  | `Assoc _ as range_json ->
      begin
        match get_position (J.member "start" range_json), get_position (J.member "end" range_json) with
        | Ok start_, Ok end_ -> Ok (Some { EcProofCore.start_; end_ })
        | Error msg, _ | _, Error msg -> Error msg
      end
  | _ -> Error "invalid range"

let get_changes json =
  match J.member "changes" json with
  | `List changes ->
      let rec loop acc = function
        | [] -> Ok (List.rev acc)
        | (`Assoc _ as change_json) :: rest ->
            begin
              match get_range change_json, J.member "text" change_json with
              | Ok range, `String text ->
                  loop ({ EcProofCore.range; text } :: acc) rest
              | Error msg, _ -> Error msg
              | _, _ -> Error "invalid change text"
            end
        | _ -> Error "invalid changes"
      in
      loop [] changes
  | _ -> Error "missing changes"

let handle_tool_call
    (proof : EcProofCore.t)
    (name : string)
    (arguments : Json.t option) : Json.t Lwt.t =
  let args = Option.value ~default:(`Assoc []) arguments in
  let invalid msg = Lwt.fail (Invalid_argument msg) in
  let open Result in
  match name with
  | "open_document" ->
      begin
        match get_uri args, get_text args with
        | Ok uri, Ok text ->
            EcProofCore.did_open proof ~uri ~text;
            Lwt.return (text_result "Document opened.")
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | "apply_changes" ->
      begin
        match get_uri args, get_changes args with
        | Ok uri, Ok changes ->
            let* () = EcProofCore.did_change proof ~uri changes in
            Lwt.return (text_result "Changes applied.")
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | "close_document" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* () = EcProofCore.did_close proof ~uri in
            Lwt.return (text_result "Document closed.")
        | Error msg -> invalid msg
      end
  | "proof_next" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* result = EcProofCore.proof_next proof ~uri in
            Lwt.return (text_result (proof_text result))
        | Error msg -> invalid msg
      end
  | "proof_step" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* result = EcProofCore.proof_step proof ~uri in
            Lwt.return (text_result (proof_text result))
        | Error msg -> invalid msg
      end
  | "proof_jump_to" ->
      begin
        match get_uri args, get_target args with
        | Ok uri, Ok target ->
            let* result = EcProofCore.proof_jump_to proof ~uri ~target in
            Lwt.return (text_result (proof_text result))
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | "proof_back" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* result = EcProofCore.proof_back proof ~uri in
            Lwt.return (text_result (proof_text result))
        | Error msg -> invalid msg
      end
  | "proof_restart" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* result = EcProofCore.proof_restart proof ~uri in
            Lwt.return (text_result (proof_text result))
        | Error msg -> invalid msg
      end
  | "proof_goals" ->
      begin
        match get_uri args with
        | Ok uri ->
            let* result = EcProofCore.proof_goals proof ~uri in
            Lwt.return (text_result (proof_text result))
        | Error msg -> invalid msg
      end
  | "query_print" ->
      begin
        match get_uri args, get_query args with
        | Ok uri, Ok query ->
            let* result = EcProofCore.query proof ~uri ~kind:`Print ~query in
            Lwt.return (text_result result.output)
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | "query_locate" ->
      begin
        match get_uri args, get_query args with
        | Ok uri, Ok query ->
            let* result = EcProofCore.query proof ~uri ~kind:`Locate ~query in
            Lwt.return (text_result result.output)
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | "query_search" ->
      begin
        match get_uri args, get_query args with
        | Ok uri, Ok query ->
            let* result = EcProofCore.query proof ~uri ~kind:`Search ~query in
            Lwt.return (text_result result.output)
        | Error msg, _ | _, Error msg -> invalid msg
      end
  | _ ->
      Lwt.fail (Invalid_argument "unknown tool")

let run () : unit =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let run_lwt () =
    let argv = Array.to_list Sys.argv in
    let cli_path =
      match argv with
      | prog :: _ -> prog
      | [] -> "easycrypt"
    in
    let proof = EcProofCore.create ~cli_path ~cli_args:[] () in
    let ic = Lwt_io.of_fd ~mode:Lwt_io.input Lwt_unix.stdin in
    let oc = Lwt_io.of_fd ~mode:Lwt_io.output Lwt_unix.stdout in
    let shutdown = ref false in

    let handle_request (req : Jsonrpc.Request.t) : unit Lwt.t =
      let params = Option.map Jsonrpc.Structured.yojson_of_t req.params in
      match req.method_, params with
      | "initialize", params ->
          let client_version =
            match params with
            | Some (`Assoc _ as json) -> (match J.member "protocolVersion" json with `String v -> Some v | _ -> None)
            | _ -> None
          in
          send_response oc req.id (initialize_result client_version)
      | "ping", _ ->
          send_response oc req.id (`Assoc [])
      | "tools/list", _ ->
          send_response oc req.id tools_list_result
      | "tools/call", Some (`Assoc _ as json) ->
          let name =
            match J.member "name" json with
            | `String name -> name
            | _ -> ""
          in
          let arguments = J.member "arguments" json in
          let arguments = match arguments with `Null -> None | x -> Some x in
          Lwt.catch
            (fun () ->
               let* result = handle_tool_call proof name arguments in
               send_response oc req.id result)
            (function
              | Invalid_argument msg ->
                  send_error oc req.id Jsonrpc.Response.Error.Code.InvalidParams msg
              | e ->
                  send_error oc req.id Jsonrpc.Response.Error.Code.InternalError
                    (Printexc.to_string e))
      | "tools/call", _ ->
          send_error oc req.id Jsonrpc.Response.Error.Code.InvalidParams "missing tool call params"
      | _ ->
          send_error oc req.id Jsonrpc.Response.Error.Code.MethodNotFound "Method not found"
    in

    let handle_notification (notif : Jsonrpc.Notification.t) : unit Lwt.t =
      match notif.method_ with
      | "notifications/initialized"
      | "initialized" -> Lwt.return_unit
      | "notifications/cancelled" -> Lwt.return_unit
      | "exit" ->
          shutdown := true;
          Lwt.return_unit
      | _ -> Lwt.return_unit
    in

    let rec loop () =
      if !shutdown then
        Lwt.return_unit
      else
        let* packet_opt = Rpc_io.read ic in
        match packet_opt with
        | None ->
            shutdown := true;
            Lwt.return_unit
        | Some packet ->
            let* () =
              match packet with
              | Jsonrpc.Packet.Request req -> handle_request req
              | Jsonrpc.Packet.Notification notif -> handle_notification notif
              | Jsonrpc.Packet.Response _ -> Lwt.return_unit
              | Jsonrpc.Packet.Batch_call _
              | Jsonrpc.Packet.Batch_response _ -> Lwt.return_unit
            in
            loop ()
    in
    let* () = loop () in
    EcProofCore.close proof
  in
  Lwt_main.run (run_lwt ())
