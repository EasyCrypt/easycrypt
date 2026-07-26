(** MCP (Model Context Protocol) server — the agents-first surface.

    JSON-RPC 2.0 over stdio, one JSON object per line (the MCP stdio
    transport). Serves `initialize` / `tools/list` / `tools/call` /
    `ping`; capabilities declare tools only.

    Tools multiplex NAMED proof sessions (label → [Ec_llm_session]):
    parallel subagents each hold a coherent EC state by using their
    own session label, which is the mechanism behind
    parallel-per-lemma dispatch (doc/ecllm-compat.md agenda §9).
    Every tool result is a JSON payload serialized into a single
    text content block, so agents parse rather than scrape.

    v1 scope notes:
    - Session bootstrap is [open_file] (EcLlm's LOAD under the hood,
      with `-nosmt` weak-check available for fast prefixes).
    - [try_tactic] is capture → exec → goals → revert-to-uuid on the
      labeled session; the session's real state is never left moved.
    - No server-initiated messages, no resources/prompts, no
      cancellation (EcCancel is deferred from pass 1). *)

let server_version = "0.1.0"

(* ---------------------------------------------------------------- *)
(* Server state                                                       *)
(* ---------------------------------------------------------------- *)

type entry = {
  session : Ec_llm_session.t;
  file    : string;
}

type t = {
  sw       : Eio.Switch.t;
  sessions : (string, entry) Hashtbl.t;
}

let default_label = "main"

let label_of_args args =
  match Yojson.Safe.Util.member "session" args with
  | `String s when s <> "" -> s
  | _ -> default_label

let find_session t args =
  let label = label_of_args args in
  match Hashtbl.find_opt t.sessions label with
  | Some e -> Ok (label, e)
  | None ->
    Error
      (Printf.sprintf
         "no session '%s' — call open_file first (optionally with a \
          {\"session\": \"<label>\"} argument to run parallel \
          sessions)" label)

(* ---------------------------------------------------------------- *)
(* Small JSON helpers                                                 *)
(* ---------------------------------------------------------------- *)

let str_arg args name =
  match Yojson.Safe.Util.member name args with
  | `String s -> Some s
  | _ -> None

let int_arg args name =
  match Yojson.Safe.Util.member name args with
  | `Int n -> Some n
  | _ -> None

let bool_arg args name =
  match Yojson.Safe.Util.member name args with
  | `Bool b -> b
  | _ -> false

(* Best-effort embed: parse [s] as JSON so the payload nests
   structurally; fall back to the raw string. *)
let json_or_string s =
  try Yojson.Safe.from_string s with _ -> `String s

let goals_json session : Yojson.Safe.t =
  match Ec_llm_session.goals ~structured:true session with
  | Error e -> `Assoc [ "error", `String (Error.to_string e) ]
  | Ok raw -> json_or_string raw

(* ---------------------------------------------------------------- *)
(* Tool implementations                                               *)
(* ---------------------------------------------------------------- *)

(* Each handler: t -> arguments -> (payload, error-text) result. *)

let absolute path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path
  else path

let tool_open_file t args =
  match str_arg args "path" with
  | None -> Error "open_file: missing required argument 'path'"
  | Some path ->
    let path = absolute path in
    if not (Sys.file_exists path) then
      Error (Printf.sprintf "open_file: no such file: %s" path)
    else begin
      let label = label_of_args args in
      (* Replace an existing session under this label. *)
      (match Hashtbl.find_opt t.sessions label with
       | Some e ->
         (try Ec_llm_session.close e.session with _ -> ());
         Hashtbl.remove t.sessions label
       | None -> ());
      let session =
        Ec_llm_session.start_in_dir
          ~cwd:(Filename.dirname path) ~sw:t.sw
          ~label:(Printf.sprintf "mcp-%s" label)
      in
      let load_cmd =
        let upto =
          match int_arg args "upto_line" with
          | Some n -> Printf.sprintf " %d" n
          | None -> ""
        in
        let nosmt = if bool_arg args "nosmt" then " -nosmt" else "" in
        Printf.sprintf "LOAD \"%s\"%s%s" path upto nosmt
      in
      match Ec_llm_session.raw_command session load_cmd with
      | Error e ->
        (try Ec_llm_session.close session with _ -> ());
        Error (Printf.sprintf "open_file: LOAD failed: %s"
                 (Error.to_string e))
      | Ok (body, _notices) ->
        Hashtbl.replace t.sessions label { session; file = path };
        Ok (`Assoc [
          "session", `String label;
          "file", `String path;
          "uuid", `Int (Ec_llm_session.current_uuid session);
          "load_output", `String body;
          "goals", goals_json session;
        ])
    end

let tool_exec t args =
  match str_arg args "text" with
  | None -> Error "exec: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let corr = Correlation.of_client "mcp-exec" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:text
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          Ok (`Assoc [
            "session", `String label;
            "uuid", `Int ok.replied_uuid;
            "restarted", `Bool ok.restarted;
            "notices", `List (List.map (fun n -> `String n) ok.notices);
            "goals", goals_json e.session;
          ])))

let tool_query t args =
  match str_arg args "text" with
  | None -> Error "query: missing required argument 'text'"
  | Some text ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let corr = Correlation.of_client "mcp-query" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Directive ~source:text
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          let output =
            String.concat "\n"
              (ok.notices @ (if ok.output = "" then [] else [ ok.output ]))
          in
          Ok (`Assoc [
            "session", `String label;
            "output", `String output;
          ])))

let tool_search t args =
  match str_arg args "pattern" with
  | None -> Error "search: missing required argument 'pattern'"
  | Some pattern ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let strict = bool_arg args "strict" in
       let verb = if strict then "search" else "searchall" in
       let pattern =
         let p = String.trim pattern in
         if String.length p > 0 && p.[String.length p - 1] = '.'
         then String.sub p 0 (String.length p - 1)
         else p
       in
       let limit =
         match int_arg args "limit" with
         | Some n when n > 0 -> n
         | _ -> 50
       in
       let source = Printf.sprintf "%s %s." verb pattern in
       let corr = Correlation.of_client "mcp-search" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Directive ~source
        with
        | Error err -> Error (Error.to_string err)
        | Ok ok ->
          let hits = Search_result.of_notices ok.notices in
          let total = List.length hits in
          let shown = List.filteri (fun i _ -> i < limit) hits in
          Ok (`Assoc [
            "session", `String label;
            "mode", `String verb;
            "total_hits", `Int total;
            "truncated", `Bool (total > limit);
            "hits",
            `List
              (List.map
                 (fun (h : Search_result.hit) ->
                    `Assoc [
                      "qname", `String h.qname;
                      "kind", `String h.kind;
                      "short_name", `String h.short_name;
                      "signature", `String h.signature;
                    ])
                 shown);
          ])))

let tool_goals t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    Ok (`Assoc [
      "session", `String label;
      "uuid", `Int (Ec_llm_session.current_uuid e.session);
      "goals", goals_json e.session;
    ])

let tool_tree t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    (match Ec_llm_session.raw_command e.session "TREE" with
     | Error err -> Error (Error.to_string err)
     | Ok (body, _) ->
       Ok (`Assoc [ "session", `String label; "tree", `String body ]))

let tool_focus t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    let cmd =
      match str_arg args "path" with
      | None | Some "" | Some "next" -> "NEXT"
      | Some p -> "FOCUS " ^ p
    in
    (match Ec_llm_session.raw_command e.session cmd with
     | Error err -> Error (Error.to_string err)
     | Ok (_, _) ->
       Ok (`Assoc [
         "session", `String label;
         "uuid", `Int (Ec_llm_session.current_uuid e.session);
         "goals", goals_json e.session;
       ]))

let tool_try_tactic t args =
  match str_arg args "tactic" with
  | None -> Error "try_tactic: missing required argument 'tactic'"
  | Some tactic ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let pre = Ec_llm_session.current_uuid e.session in
       let corr = Correlation.of_client "mcp-try" in
       (match
          Ec_llm_session.exec e.session ~corr
            ~sentence_class:`Executable ~source:tactic
        with
        | Error err ->
          (* A failed tactic leaves uuid unmoved; nothing to revert. *)
          Ok (`Assoc [
            "session", `String label;
            "outcome", `String "err";
            "error", `String (Error.to_string err);
          ])
        | Ok _ ->
          let goals_after = goals_json e.session in
          (match
             Ec_llm_session.revert_to_uuid e.session ~target:pre
           with
           | Ok () ->
             Ok (`Assoc [
               "session", `String label;
               "outcome", `String "ok";
               "goals_after", goals_after;
               "reverted_to", `Int pre;
             ])
           | Error err ->
             (* State is now past the candidate — surface loudly. *)
             Error
               (Printf.sprintf
                  "try_tactic: candidate applied but revert failed \
                   (%s); session '%s' state has ADVANCED"
                  (Error.to_string err) label))))

let tool_revert t args =
  match int_arg args "uuid" with
  | None -> Error "revert: missing required argument 'uuid' (int)"
  | Some target ->
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       (match Ec_llm_session.revert_to_uuid e.session ~target with
        | Error err -> Error (Error.to_string err)
        | Ok () ->
          Ok (`Assoc [
            "session", `String label;
            "uuid", `Int (Ec_llm_session.current_uuid e.session);
            "goals", goals_json e.session;
          ])))

let tool_commit_proof t args =
  match find_session t args with
  | Error e -> Error e
  | Ok (label, e) ->
    (match Ec_llm_session.raw_command e.session "COMMIT" with
     | Error err -> Error (Error.to_string err)
     | Ok (body, _) ->
       Ok (`Assoc [ "session", `String label; "proof", `String body ]))

let tool_analyze_file t args =
  match str_arg args "path" with
  | None -> Error "analyze_file: missing required argument 'path'"
  | Some path ->
    let path = absolute path in
    (match find_session t args with
     | Error e -> Error e
     | Ok (label, e) ->
       let cmd = Printf.sprintf "ANALYZE-JSON \"%s\"" path in
       (match Ec_llm_session.raw_command e.session cmd with
        | Error err -> Error (Error.to_string err)
        | Ok (body, _) ->
          Ok (`Assoc [
            "session", `String label;
            "file", `String path;
            "analysis", json_or_string body;
          ])))

let tool_list_sessions t _args =
  let rows =
    Hashtbl.fold
      (fun label e acc ->
         `Assoc [
           "session", `String label;
           "file", `String e.file;
           "uuid", `Int (Ec_llm_session.current_uuid e.session);
         ] :: acc)
      t.sessions []
  in
  Ok (`Assoc [ "sessions", `List rows ])

let tool_close_session t args =
  let label = label_of_args args in
  match Hashtbl.find_opt t.sessions label with
  | None -> Error (Printf.sprintf "close_session: no session '%s'" label)
  | Some e ->
    (try Ec_llm_session.close e.session with _ -> ());
    Hashtbl.remove t.sessions label;
    Ok (`Assoc [ "closed", `String label ])

(* ---------------------------------------------------------------- *)
(* Tool registry                                                      *)
(* ---------------------------------------------------------------- *)

let schema ?(required = []) props : Yojson.Safe.t =
  `Assoc [
    "type", `String "object";
    "properties",
    `Assoc
      (List.map
         (fun (name, ty, doc) ->
            name, `Assoc [ "type", `String ty;
                           "description", `String doc ])
         props);
    "required", `List (List.map (fun s -> `String s) required);
  ]

let session_prop =
  ("session", "string",
   "Session label (default \"main\"). Use distinct labels to run \
    parallel sessions, e.g. one per lemma/agent.")

let tools :
  (string * string * Yojson.Safe.t
   * (t -> Yojson.Safe.t -> (Yojson.Safe.t, string) result)) list = [
  "open_file",
  "Open an EasyCrypt file in a (new) proof session: spawns an EC \
   subprocess with its working directory at the file's directory \
   (easycrypt.project is honored) and loads the file, optionally \
   only up to a line. Use nosmt=true to weak-check the prefix fast \
   (safe when the prefix is already verified). Replaces any \
   existing session under the same label.",
  schema ~required:[ "path" ] [
    ("path", "string", "Path to the .ec/.eca file.");
    ("upto_line", "integer",
     "Stop loading after the sentence ending on this line \
      (1-based). Omit to load the whole file.");
    ("nosmt", "boolean",
     "Weak-check the loaded prefix (skip SMT). Default false.");
    session_prop;
  ],
  tool_open_file;

  "exec",
  "Execute EasyCrypt input (tactics or declarations, '.'-terminated; \
   multi-sentence allowed) in the session, advancing its state. \
   Returns the new uuid and the structured goals after execution.",
  schema ~required:[ "text" ] [
    ("text", "string", "EasyCrypt source to execute.");
    session_prop;
  ],
  tool_exec;

  "query",
  "Run a read-only directive (print / search / locate ...) without \
   moving proof state. Returns its textual output.",
  schema ~required:[ "text" ] [
    ("text", "string",
     "Directive, '.'-terminated, e.g. \"print List.map.\" or \
      \"search (_ + _).\"");
    session_prop;
  ],
  tool_query;

  "search",
  "Search for lemmas / operators / axioms matching a pattern, \
   returning structured hits (qname, kind, signature). Default mode \
   is overload-tolerant (searchall): untyped patterns like \
   \"(_ <= _)\" work without type ascriptions, unioning all \
   operator overloads. strict=true uses EC's plain typed search.",
  schema ~required:[ "pattern" ] [
    ("pattern", "string",
     "Search pattern, e.g. \"(_ <= _)\" or \"(_ + _)\"; trailing \
      '.' optional.");
    ("strict", "boolean",
     "Use strict typed search instead of searchall. Default false.");
    ("limit", "integer", "Max hits returned (default 50).");
    session_prop;
  ],
  tool_search;

  "goals",
  "Structured view of the current proof state (GOALS-JSON): subgoal \
   count, hypotheses, conclusion trees (PHL judgments carry \
   structured program statements).",
  schema [ session_prop ],
  tool_goals;

  "tree",
  "Render the open-subgoal tree with dotted-path labels (matching \
   what focus accepts) and the focused goal marked.",
  schema [ session_prop ],
  tool_tree;

  "focus",
  "Rotate focus to a subgoal: path is a dotted tree path from \
   `tree` (e.g. \"2\" or \"1.2\"), or \"next\" to rotate to the \
   next open goal. Undoable (advances uuid).",
  schema [
    ("path", "string",
     "Dotted path from `tree`, or \"next\" (default).");
    session_prop;
  ],
  tool_focus;

  "try_tactic",
  "Speculatively run a tactic: executes it, captures the resulting \
   goals, then reverts — the session state is left unchanged. Use \
   for exploring candidate steps cheaply before committing with \
   exec.",
  schema ~required:[ "tactic" ] [
    ("tactic", "string", "Tactic source, '.'-terminated.");
    session_prop;
  ],
  tool_try_tactic;

  "revert",
  "Revert the session to an earlier uuid (as reported by exec / \
   goals).",
  schema ~required:[ "uuid" ] [
    ("uuid", "integer", "Target uuid to revert to.");
    session_prop;
  ],
  tool_revert;

  "commit_proof",
  "Emit the session's successfully-executed proof phrases as a \
   bullet-structured proof body (safe under +strict_bullets) — the \
   bridge from session-first exploration back into document text.",
  schema [ session_prop ],
  tool_commit_proof;

  "analyze_file",
  "Whole-file batch diagnostics (stateless; the session's state is \
   untouched): parse/type/tactic errors with positions, sentence \
   classes and enclosing-scope tags.",
  schema ~required:[ "path" ] [
    ("path", "string", "Path to the .ec/.eca file to analyze.");
    session_prop;
  ],
  tool_analyze_file;

  "list_sessions",
  "List open proof sessions (label, file, uuid).",
  schema [],
  tool_list_sessions;

  "close_session",
  "Close a proof session and release its EC subprocess.",
  schema [ session_prop ],
  tool_close_session;
]

let tools_list_json () : Yojson.Safe.t =
  `Assoc [
    "tools",
    `List
      (List.map
         (fun (name, desc, sch, _) ->
            `Assoc [
              "name", `String name;
              "description", `String desc;
              "inputSchema", sch;
            ])
         tools);
  ]

(* ---------------------------------------------------------------- *)
(* JSON-RPC plumbing                                                  *)
(* ---------------------------------------------------------------- *)

let write_json ~stdout (j : Yojson.Safe.t) =
  Eio.Flow.copy_string (Yojson.Safe.to_string j ^ "\n") stdout

let respond ~stdout ~id result =
  write_json ~stdout
    (`Assoc [ "jsonrpc", `String "2.0"; "id", id; "result", result ])

let respond_error ~stdout ~id code message =
  write_json ~stdout
    (`Assoc [
       "jsonrpc", `String "2.0";
       "id", id;
       "error", `Assoc [ "code", `Int code; "message", `String message ];
     ])

let tool_result_json payload ~is_error : Yojson.Safe.t =
  let text =
    match payload with
    | `String s -> s
    | j -> Yojson.Safe.to_string j
  in
  `Assoc [
    "content",
    `List [ `Assoc [ "type", `String "text"; "text", `String text ] ];
    "isError", `Bool is_error;
  ]

let handle_tools_call t ~stdout ~id params =
  let name =
    match str_arg params "name" with Some n -> n | None -> ""
  in
  let args =
    match Yojson.Safe.Util.member "arguments" params with
    | `Assoc _ as a -> a
    | _ -> `Assoc []
  in
  match
    List.find_opt (fun (n, _, _, _) -> n = name) tools
  with
  | None ->
    respond_error ~stdout ~id (-32602)
      (Printf.sprintf "unknown tool: %s" name)
  | Some (_, _, _, handler) ->
    let result =
      try handler t args
      with exn ->
        Error
          (Printf.sprintf "internal error in tool %s: %s" name
             (Printexc.to_string exn))
    in
    (match result with
     | Ok payload ->
       respond ~stdout ~id (tool_result_json payload ~is_error:false)
     | Error msg ->
       respond ~stdout ~id
         (tool_result_json (`String msg) ~is_error:true))

let handle_initialize ~stdout ~id params =
  let proto =
    match str_arg params "protocolVersion" with
    | Some v -> v
    | None -> "2024-11-05"
  in
  respond ~stdout ~id
    (`Assoc [
       "protocolVersion", `String proto;
       "capabilities",
       `Assoc [ "tools", `Assoc [ "listChanged", `Bool false ] ];
       "serverInfo",
       `Assoc [
         "name", `String "ecd-mcp";
         "version", `String server_version;
       ];
       "instructions",
       `String
         "EasyCrypt proof sessions over MCP. Start with open_file \
          (optionally upto_line + nosmt for a fast prefix), inspect \
          with goals/tree, explore with try_tactic (state-neutral), \
          advance with exec, and extract the finished script with \
          commit_proof. Pass a distinct {\"session\": label} per \
          agent to work multiple proofs in parallel without \
          conflicts.";
     ])

let handle_message t ~stdout (msg : Yojson.Safe.t) =
  let member = Yojson.Safe.Util.member in
  let id = member "id" msg in
  let meth =
    match member "method" msg with `String m -> m | _ -> ""
  in
  let params =
    match member "params" msg with
    | `Assoc _ as p -> p
    | _ -> `Assoc []
  in
  match id, meth with
  (* Notifications (no id): nothing to answer. *)
  | `Null, _ -> ()
  | _, "initialize" -> handle_initialize ~stdout ~id params
  | _, "ping" -> respond ~stdout ~id (`Assoc [])
  | _, "tools/list" -> respond ~stdout ~id (tools_list_json ())
  | _, "tools/call" -> handle_tools_call t ~stdout ~id params
  | _, m ->
    respond_error ~stdout ~id (-32601)
      (Printf.sprintf "method not found: %s" m)

(* ---------------------------------------------------------------- *)
(* Main loop                                                          *)
(* ---------------------------------------------------------------- *)

let run ~sw ~stdin ~stdout =
  let t = { sw; sessions = Hashtbl.create 4 } in
  let buf = Eio.Buf_read.of_flow ~max_size:(1 lsl 24) stdin in
  let rec loop () =
    match Eio.Buf_read.line buf with
    | exception End_of_file -> ()
    | line ->
      let line = String.trim line in
      if line = "" then loop ()
      else begin
        (match Yojson.Safe.from_string line with
         | exception _ ->
           respond_error ~stdout ~id:`Null (-32700) "parse error"
         | msg -> handle_message t ~stdout msg);
        loop ()
      end
  in
  loop ();
  (* EOF: release every EC subprocess before returning. *)
  Hashtbl.iter
    (fun _ e -> try Ec_llm_session.close e.session with _ -> ())
    t.sessions;
  Hashtbl.reset t.sessions
