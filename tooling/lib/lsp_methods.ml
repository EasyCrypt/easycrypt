(* Default LSP method handlers.

   Method namespace: easycrypt/proof/* (per doc/lsp-schema.md § 1).
   Single proof_ns constant for cheap future flipping. *)

let proof_ns = "easycrypt/proof"
let proof_method suffix = proof_ns ^ "/" ^ suffix

(* JSON helpers for typed access to params. *)

let opt_field key = function
  | `Assoc kvs -> List.assoc_opt key kvs
  | _ -> None

let req_field key obj =
  match opt_field key obj with
  | Some v -> v
  | None ->
    raise
      (Jsonrpc.Response.Error.E
         (Jsonrpc.Response.Error.make
            ~code:Jsonrpc.Response.Error.Code.InvalidParams
            ~message:(Printf.sprintf "missing field: %s" key)
            ()))

let opt_string key obj =
  match opt_field key obj with
  | Some (`String s) -> Some s
  | _ -> None

let req_string key obj =
  match req_field key obj with
  | `String s -> s
  | other ->
    raise
      (Jsonrpc.Response.Error.E
         (Jsonrpc.Response.Error.make
            ~code:Jsonrpc.Response.Error.Code.InvalidParams
            ~message:(Printf.sprintf "field %s expected string, got %s"
                        key (Yojson.Safe.to_string other))
            ()))

let req_int key obj =
  match req_field key obj with
  | `Int n -> n
  | other ->
    raise
      (Jsonrpc.Response.Error.E
         (Jsonrpc.Response.Error.make
            ~code:Jsonrpc.Response.Error.Code.InvalidParams
            ~message:(Printf.sprintf "field %s expected int, got %s"
                        key (Yojson.Safe.to_string other))
            ()))

(* ---------------------------------------------------------------- *)
(* Lifecycle                                                          *)
(* ---------------------------------------------------------------- *)

let initialize_response : Yojson.Safe.t =
  `Assoc [
    "capabilities", `Assoc [
      "textDocumentSync", `Int 1;  (* full-document sync *)
      (* Diagnostics use the push model: didChange → debouncer →
         ANALYZE-JSON → publishDiagnostics. Do NOT advertise
         `diagnosticProvider` (LSP 3.17 pull model) — clients that
         see it issue textDocument/diagnostic requests we don't
         answer. *)
      "hoverProvider", `Bool false;
      "definitionProvider", `Bool false;
      "documentSymbolProvider", `Bool false;
    ];
    "serverInfo", `Assoc [
      "name", `String "easycrypt-daemon";
      "version", `String "0.0.0+dev";
    ];
    "proofCapabilities", `Assoc [
      "serverVersion", `String "0.0.0+dev";
      "supportedRecoveryStrategies",
        `List [ `String "halt"; `String "best_effort_admit" ];
      "supportedCachePolicies",
        `List [ `String "lax"; `String "strict" ];
      "minClientVersion", `String "0.0.0";
      "currentSession", `Assoc [
        "label", `String "primary";
        "uuid", `Int 0;
        "currentSentenceId", `Null;
        "cas", `String "00000000000000000000000000000000";
        "casPolicy", `String "lax";
      ];
    ];
  ]

let register_lifecycle server =
  Lsp_server.register_request server "initialize"
    (fun (_req : Jsonrpc.Request.t) ->
      Log.info "initialize received";
      Ok initialize_response);
  Lsp_server.register_notification server "initialized"
    (fun _ -> Log.info "initialized notification");
  Lsp_server.register_request server "shutdown"
    (fun (_req : Jsonrpc.Request.t) ->
      (* Per LSP spec: reply OK and wait for `exit`. Do NOT trigger
         loop termination here — racing the loop's shutdown check
         against this handler's write_packet would silently drop the
         shutdown response. *)
      Log.info "shutdown received";
      Ok `Null)
  (* exit notification handled in Lsp_server core. *)

(* ---------------------------------------------------------------- *)
(* publishDiagnostics                                                 *)
(* ---------------------------------------------------------------- *)

(* Convert a single ANALYZE-JSON diagnostic to an LSP Diagnostic. *)
let lsp_diagnostic_of_analyze_diag ~source diag : Yojson.Safe.t option =
  let open Yojson.Safe.Util in
  try
    (* Diag carries optional location { file?, start_line, start_col,
       end_line, end_col }; if absent, attach a 0:0-0:1 placeholder. *)
    let location =
      try Some (member "location" diag)
      with _ -> None
    in
    let pos l c = `Assoc [
      "line", `Int (max 0 (l - 1));      (* LSP is 0-based, EC is 1-based *)
      "character", `Int (max 0 (c - 1));
    ] in
    let range =
      match location with
      | Some (`Assoc _ as loc) ->
        let sl = try member "start_line" loc |> to_int with _ -> 1 in
        let sc = try member "start_col"  loc |> to_int with _ -> 1 in
        let el = try member "end_line"   loc |> to_int with _ -> sl in
        let ec = try member "end_col"    loc |> to_int with _ -> sc + 1 in
        `Assoc [ "start", pos sl sc; "end", pos el ec ]
      | _ ->
        (* Fallback: range covers the whole document if no location. *)
        let _ = source in
        `Assoc [ "start", pos 1 1; "end", pos 1 2 ]
    in
    let code = try member "code" diag |> to_string with _ -> "Internal" in
    let detail = try member "detail" diag |> to_string with _ -> "" in
    let phase = try member "phase" diag |> to_string with _ -> "unknown" in
    let sentence_id =
      try Some (member "sentence_id" diag)
      with _ -> None
    in
    let sentence_index =
      try Some (member "sentence_index" diag |> to_int)
      with _ -> None
    in
    (* enclosing_scope (UPSTREAM addition 14, scope-tagging extension):
       transparent forward — the daemon does no detection, just lifts
       the field from the ANALYZE-JSON envelope into Diagnostic.data. *)
    let scope =
      try
        match member "enclosing_scope" diag with
        | `Null -> None
        | other -> Some other
      with _ -> None
    in
    let data : Yojson.Safe.t = `Assoc (List.filter_map (fun x -> x) [
      Some ("phase", `String phase);
      Option.map (fun sid -> "sentence_id", sid) sentence_id;
      Option.map (fun n -> "sentence_index", `Int n) sentence_index;
      Option.map (fun s -> "scope", s) scope;
    ]) in
    Some (`Assoc [
      "range", range;
      "severity", `Int 1;  (* LSP DiagnosticSeverity.Error *)
      "code", `String code;
      "source", `String "easycrypt";
      "message", `String detail;
      "data", data;
    ])
  with _ ->
    Log.warn "lsp_diagnostic_of_analyze_diag: malformed diag %s"
      (Yojson.Safe.to_string diag);
    None

let publish_diagnostics server ~io ~uri ~source ~analyze_session =
  Log.info "publish_diagnostics: dispatching analyze for %s (len=%d)"
    uri (String.length source);
  match Ec_llm_session.analyze_source analyze_session ~source with
  | Error e ->
    Log.warn "publish_diagnostics: analyze_source failed: %s"
      (Error.to_string e);
    (* Send empty diagnostics so client clears stale ones. *)
    Lsp_server.send_notification server ~io
      ~method_:"textDocument/publishDiagnostics"
      ~params:(`Assoc [
        "uri", `String uri;
        "diagnostics", `List [];
      ]) ()
  | Ok raw_json ->
    let diagnostics =
      match Yojson.Safe.from_string raw_json with
      | exception _ -> []
      | json ->
        let open Yojson.Safe.Util in
        try
          json |> member "diagnostics" |> to_list
          |> List.filter_map (lsp_diagnostic_of_analyze_diag ~source)
        with _ ->
          Log.warn "publish_diagnostics: failed to parse analyze envelope";
          []
    in
    Log.info "publish_diagnostics: emitting %d diagnostic(s) for %s"
      (List.length diagnostics) uri;
    Lsp_server.send_notification server ~io
      ~method_:"textDocument/publishDiagnostics"
      ~params:(`Assoc [
        "uri", `String uri;
        "diagnostics", `List diagnostics;
      ]) ()

(* ---------------------------------------------------------------- *)
(* Text document lifecycle                                            *)
(* ---------------------------------------------------------------- *)

(* Extract textDocument fields from a notification's params. *)
let text_document_fields params =
  let td = req_field "textDocument" params in
  let uri = req_string "uri" td in
  let version =
    try req_int "version" td
    with _ -> 0
  in
  let text =
    match opt_string "text" td with
    | Some s -> Some s
    | None -> None
  in
  uri, version, text

(* For didChange, content sync = full means a single ContentChangeEvent
   with the full text in `text`. *)
let did_change_text params =
  let changes = req_field "contentChanges" params in
  match changes with
  | `List ((`Assoc _ as ch) :: _) ->
    (* Full sync: take the `text` field of the first change event. *)
    req_string "text" ch
  | _ ->
    raise
      (Jsonrpc.Response.Error.E
         (Jsonrpc.Response.Error.make
            ~code:Jsonrpc.Response.Error.Code.InvalidParams
            ~message:"didChange requires non-empty contentChanges"
            ()))

(* stateChanged emit helpers — used by both didChange auto-reconcile
   (Slice D) and the proof-method handlers (Slice A). Pre-Stage-5
   the cas field is always zero; cache substrate fills it in. *)

let zero_cas = "00000000000000000000000000000000"

let state_seq = ref 0
let next_seq () = incr state_seq; !state_seq

let sid_to_json = function
  | None -> `Null
  | Some sid -> `String (Sentence_id.to_string sid)

let state_changed_params ~uri ~current_sid ~current_end ~corr_id =
  let end_json =
    match current_end with
    | None -> `Null
    | Some (line, character) ->
      `Assoc [
        "line", `Int line;
        "character", `Int character;
      ]
  in
  `Assoc [
    "uri", `String uri;
    "sessionLabel", `String "primary";
    "currentSentenceId", sid_to_json current_sid;
    "currentEndPosition", end_json;
    "cas", `String zero_cas;
    "seq", `Int (next_seq ());
    "origin", `Assoc [
      "kind", `String "lsp";
      "correlationId", `String corr_id;
    ];
  ]

(* Compute (current_sid, current_end) at a given sentence index.
   Pure read of [Proof_state.sentences], no mutex acquisition.
   Safe inside or outside the proof_state lock. *)
let pos_at_index proof_state index =
  if index < 0 then None, None
  else
    let arr = Proof_state.sentences proof_state in
    if index >= Array.length arr then None, None
    else
      let s = arr.(index) in
      let sid = Some (Sentence_id.of_source s.src) in
      (* PARSE-JSON gives 1-based EC line/col; LSP wants 0-based. *)
      let pos = Some (s.end_line - 1, s.end_col - 1) in
      (sid, pos)

(* Emit stateChanged using a caller-supplied index. Does not call
   [Proof_state.snapshot], so it is safe inside the proof_state
   mutex (e.g. from [exec_walk_unlocked]'s [on_step] callback)
   where calling snapshot would deadlock the non-reentrant
   Eio.Mutex.

   seq ASSIGNMENT and the socket write happen under one dedicated
   mutex: params used to take their seq before the write, and a
   write is a suspension point — a second fiber could take the next
   seq and reach the socket first, inverting seq order on the wire
   (the historic proof-flow-smoke flake). Lock order is
   proof_state → emit_mutex → write_mutex, never the reverse. *)
let emit_mutex = Eio.Mutex.create ()

let emit_state_changed_at server ~io ~uri ~proof_state ~corr_id ~index =
  let current_sid, current_end = pos_at_index proof_state index in
  Eio.Mutex.use_rw ~protect:false emit_mutex (fun () ->
    Lsp_server.send_notification server ~io
      ~method_:(proof_method "stateChanged")
      ~params:(state_changed_params
                 ~uri ~current_sid ~current_end ~corr_id) ())

(* Emit stateChanged based on the current index — acquires the
   proof_state mutex via snapshot. DO NOT call from inside a
   with_lock / exec_walk_unlocked path; use [emit_state_changed_at]
   instead in those contexts. *)
let emit_state_changed server ~io ~uri ~proof_state ~corr_id =
  let snap = Proof_state.snapshot proof_state in
  emit_state_changed_at server ~io ~uri ~proof_state ~corr_id
    ~index:snap.current_index

let register_text_document server ~io ~manager ~sw ~debouncer
    ~doc_sources =
  let _ = sw in
  Lsp_server.register_notification server "textDocument/didOpen"
    (fun (notif : Jsonrpc.Notification.t) ->
      match notif.params with
      | None ->
        Log.warn "didOpen: missing params"
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        let uri, version, text =
          try text_document_fields params
          with _ ->
            Log.warn "didOpen: malformed textDocument";
            "", 0, None
        in
        match text with
        | None ->
          Log.warn "didOpen: missing text"
        | Some source ->
          Log.info "didOpen %s (version=%d)" uri version;
          Hashtbl.replace doc_sources uri source;
          Debouncer.trigger debouncer (uri, source, version));

  Lsp_server.register_notification server "textDocument/didChange"
    (fun (notif : Jsonrpc.Notification.t) ->
      match notif.params with
      | None ->
        Log.warn "didChange: missing params"
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        try
          let uri, version, _ = text_document_fields params in
          let source = did_change_text params in
          Log.info "didChange %s (version=%d, len=%d)"
            uri version (String.length source);
          Hashtbl.replace doc_sources uri source;
          Debouncer.trigger debouncer (uri, source, version);
          (* Slice D — auto-reconcile the URI's project session
             against the new source. UPSTREAM § 14: route via the
             [Session_manager] so a didChange in project A doesn't
             touch project B's session. If the divergence sits
             inside the locked region, the primary is reverted to
             the last common-prefix sentence. We emit
             easycrypt/proof/stateChanged with the new endpoint so
             the client's locked-region decoration retracts
             immediately. *)
          let proof_state =
            Session_manager.proof_state_for manager ~sw ~uri
          in
          (match Proof_state.reconcile proof_state ~uri ~source with
           | Ok (`Reconciled _) ->
             Log.info "didChange %s: reconciled (retraction)" uri;
             emit_state_changed server ~io ~uri ~proof_state
               ~corr_id:"didChange"
           | Ok `Unchanged | Ok `Not_bound -> ()
           | Error e ->
             Log.warn "didChange %s: reconcile failed: %s" uri
               (Error.to_string e))
        with _ ->
          Log.warn "didChange: malformed params");

  Lsp_server.register_notification server "textDocument/didClose"
    (fun (notif : Jsonrpc.Notification.t) ->
      match notif.params with
      | None -> Log.warn "didClose: missing params"
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        try
          let uri, _, _ = text_document_fields params in
          Log.info "didClose %s" uri;
          Hashtbl.remove doc_sources uri;
          (* Send empty diagnostics to clear any active markers. *)
          Lsp_server.send_notification server ~io
            ~method_:"textDocument/publishDiagnostics"
            ~params:(`Assoc [
              "uri", `String uri;
              "diagnostics", `List [];
            ]) ()
        with _ ->
          Log.warn "didClose: malformed params");

  ignore manager

(* ---------------------------------------------------------------- *)
(* Proof methods                                                      *)
(* ---------------------------------------------------------------- *)

(* Drives the per-connection Proof_state to provide a Proof-General-
   style workflow. Pre-Stage-5: provenance always "fresh", CAS
   always zero — the cache substrate fills in real values without a
   wire bump. *)

let lsp_error_of code msg =
  Jsonrpc.Response.Error.make ~code ~message:msg ()

let invalid_params msg =
  lsp_error_of Jsonrpc.Response.Error.Code.InvalidParams msg

let internal_error_resp msg =
  lsp_error_of Jsonrpc.Response.Error.Code.InternalError msg

(* Resolve an LSP request's target (sentence_id | position) into a
   sentence index in the proof_state's cached parse. *)
let resolve_target proof_state target_obj =
  let open Yojson.Safe.Util in
  let by_sid =
    try
      match member "sentence_id" target_obj with
      | `String s ->
        (* Map sid → index by linear scan; n is small in PoC. *)
        let want = Sentence_id.of_string s in
        let arr = Proof_state.sentences proof_state in
        let n = Array.length arr in
        let rec find i =
          if i >= n then None
          else if Sentence_id.equal
                    (Sentence_id.of_source arr.(i).Ec_llm_session.src)
                    want
          then Some i
          else find (i + 1)
        in
        find 0
      | _ -> None
    with _ -> None
  in
  match by_sid with
  | Some idx -> Ok idx
  | None ->
    (try
       match member "position" target_obj with
       | `Assoc _ as p ->
         let line = p |> member "line" |> to_int in
         let character = p |> member "character" |> to_int in
         Ok (Proof_state.sentence_index_at_position proof_state
               ~line ~character)
       | _ ->
         Error "target must contain sentence_id or position"
     with _ -> Error "malformed target")

(* Load the document source from the source cache (filled by didOpen
   / didChange), then bind it to the proof state's primary session. *)
let bind_doc proof_state doc_sources ~sw ~uri =
  match Hashtbl.find_opt doc_sources uri with
  | None ->
    Error (Printf.sprintf "no source cached for %s; client must \
                            send textDocument/didOpen first" uri)
  | Some source ->
    (match Proof_state.ensure_doc proof_state ~sw ~uri ~source with
     | Ok () -> Ok ()
     | Error e -> Error (Error.to_string e))

let register_proof_methods server ~io ~sw ~manager ~doc_sources =
  (* UPSTREAM § 14 / doc/session-model.md — every URI-bearing
     handler resolves [proof_state] via [Session_manager.proof_state_for]
     so each project gets its own primary EC subprocess. The
     resolver itself is allocation-light (one Hashtbl lookup per
     call after the first); the FIRST call for a given project
     pays a cold-spawn cost of ~1-2s while EC loads its prelude. *)
  let resolve_ps uri = Session_manager.proof_state_for manager ~sw ~uri in
  let with_uri req params_field handler =
    match req.Jsonrpc.Request.params with
    | None -> Error (invalid_params "missing params")
    | Some structured ->
      let params = (structured :> Yojson.Safe.t) in
      let uri =
        try Some (Yojson.Safe.Util.member "uri" params
                  |> Yojson.Safe.Util.to_string)
        with _ -> None
      in
      (match uri with
       | None -> Error (invalid_params "params.uri required")
       | Some uri -> handler params uri params_field)
  in
  let _ = with_uri in
  let read_uri req =
    match req.Jsonrpc.Request.params with
    | None -> Error "missing params"
    | Some structured ->
      let params = (structured :> Yojson.Safe.t) in
      try Ok ((Yojson.Safe.Util.member "uri" params
               |> Yojson.Safe.Util.to_string), params)
      with _ -> Error "params.uri required"
  in

  (* easycrypt/proof/goals — read-only. Degrades to an "inactive"
     stub when no document is bound (e.g. client polls before
     didOpen) so smokes and exploratory clients don't hard-fail. *)
  let inactive_goals : Yojson.Safe.t =
    `Assoc [
      "active", `Bool false;
      "subgoal_count", `Int 0;
      "current_index", `Int 0;
      "subgoals", `List [];
      "provenance", `String "fresh";
      "cas", `String zero_cas;
    ]
  in
  Lsp_server.register_request server (proof_method "goals")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        (match Hashtbl.find_opt doc_sources uri with
         | None -> Ok inactive_goals
         | Some _ ->
           let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
           | Error msg -> Error (internal_error_resp msg)
           | Ok () ->
             (match Proof_state.goals proof_state with
              | Error e -> Error (internal_error_resp (Error.to_string e))
              | Ok raw ->
                (* GOALS-JSON returns the inner shape; wrap with our
                   provenance/cas envelope. *)
                let inner =
                  try Yojson.Safe.from_string raw
                  with _ -> `Assoc []
                in
                let extra : (string * Yojson.Safe.t) list = [
                  "provenance", `String "fresh";
                  "cas", `String zero_cas;
                ] in
                let merged =
                  match inner with
                  | `Assoc kvs -> `Assoc (kvs @ extra)
                  | other -> `Assoc (("raw", other) :: extra)
                in
                Ok merged)));

  (* easycrypt/proof/execToPoint — mutating *)
  Lsp_server.register_request server (proof_method "execToPoint")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, params) ->
        let target_obj =
          try Yojson.Safe.Util.member "target" params
          with _ -> `Null
        in
        let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
        | Error msg -> Error (internal_error_resp msg)
        | Ok () ->
          (match resolve_target proof_state target_obj with
           | Error msg -> Error (invalid_params msg)
           | Ok target_idx ->
             let before = Proof_state.current_index proof_state in
             let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
             (* PG-style progressive lock: emit one stateChanged per
                successful sentence so the client's locked-tint
                advances in step with the daemon, instead of jumping
                from start to final at request completion. The
                queued amber the client painted before the request
                stays put — client clears it when this response
                returns. *)
             (* on_step runs inside Proof_state's with_lock — must
                NOT acquire that lock again. Use the lockless _at
                variant which reads sentences[idx] directly. *)
             let on_step idx _sid =
               emit_state_changed_at server ~io ~uri ~proof_state
                 ~corr_id ~index:idx
             in
             let outcome =
               Proof_state.exec_to ~on_step proof_state
                 ~target_index:target_idx
             in
             let advanced_idx, executed, diags =
               match outcome with
               | Ok new_idx -> new_idx, max 0 (new_idx - before), []
               | Error (last_idx, e) ->
                 last_idx, max 0 (last_idx - before),
                 [`Assoc [
                    "code", `String "TacticFailure";
                    "phase", `String "tactic";
                    "detail", `String (Error.to_string e);
                  ]]
             in
             let advanced_to =
               if advanced_idx < 0 then `Null
               else
                 let s = (Proof_state.sentences proof_state).(advanced_idx) in
                 `String (Sentence_id.to_string
                            (Sentence_id.of_source s.src))
             in
             Ok (`Assoc [
               "advancedTo", advanced_to;
               "newCas", `String zero_cas;
               "executedSentences", `Int executed;
               "skippedSentences", `Int 0;
               "diagnostics", `List diags;
             ])));

  (* easycrypt/proof/execAll — mutating. Targets the last sentence
     in the cached parse; halts on the first non-Meta error and
     surfaces it as a TacticFailure diagnostic. Inherits
     cancellation from C1+C2+C3 (proof/cancel rolls back to the
     last-executed sentence). Per beta-prep point 4. *)
  Lsp_server.register_request server (proof_method "execAll")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
        | Error msg -> Error (internal_error_resp msg)
        | Ok () ->
          let snap = Proof_state.snapshot proof_state in
          let target_idx = snap.sentence_count - 1 in
          if target_idx < 0 then
            (* Empty document — nothing to execute. *)
            Ok (`Assoc [
              "advancedTo", `Null;
              "newCas", `String zero_cas;
              "executedSentences", `Int 0;
              "skippedSentences", `Int 0;
              "diagnostics", `List [];
            ])
          else
            let before = snap.current_index in
            let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
            let on_step idx _sid =
              emit_state_changed_at server ~io ~uri ~proof_state
                ~corr_id ~index:idx
            in
            let outcome =
              Proof_state.exec_to ~on_step proof_state
                ~target_index:target_idx
            in
            let advanced_idx, executed, diags =
              match outcome with
              | Ok new_idx -> new_idx, max 0 (new_idx - before), []
              | Error (last_idx, e) ->
                last_idx, max 0 (last_idx - before),
                [`Assoc [
                   "code", `String "TacticFailure";
                   "phase", `String "tactic";
                   "detail", `String (Error.to_string e);
                 ]]
            in
            let advanced_to =
              if advanced_idx < 0 then `Null
              else
                let s = (Proof_state.sentences proof_state).(advanced_idx) in
                `String (Sentence_id.to_string
                           (Sentence_id.of_source s.src))
            in
            Ok (`Assoc [
              "advancedTo", advanced_to;
              "newCas", `String zero_cas;
              "executedSentences", `Int executed;
              "skippedSentences", `Int 0;
              "diagnostics", `List diags;
              "atEndOfDocument", `Bool (advanced_idx = target_idx);
            ]));

  (* easycrypt/proof/revertToPoint — mutating *)
  Lsp_server.register_request server (proof_method "revertToPoint")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, params) ->
        let target_obj =
          try Yojson.Safe.Util.member "target" params
          with _ -> `Null
        in
        let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
        | Error msg -> Error (internal_error_resp msg)
        | Ok () ->
          (match resolve_target proof_state target_obj with
           | Error msg -> Error (invalid_params msg)
           | Ok target_idx ->
             match Proof_state.revert_to proof_state ~target_index:target_idx with
             | Error e -> Error (internal_error_resp (Error.to_string e))
             | Ok () ->
               let cur = Proof_state.current_index proof_state in
               let reverted_to =
                 if cur < 0 then `Null
                 else
                   let s = (Proof_state.sentences proof_state).(cur) in
                   `String (Sentence_id.to_string
                              (Sentence_id.of_source s.src))
               in
               let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
               emit_state_changed server ~io ~uri ~proof_state ~corr_id;
               Ok (`Assoc [
                 "revertedTo", reverted_to;
                 "newCas", `String zero_cas;
               ])));

  let opt_count req =
    match req.Jsonrpc.Request.params with
    | None -> 1
    | Some structured ->
      let params = (structured :> Yojson.Safe.t) in
      (match Yojson.Safe.Util.member "count" params with
       | `Int n when n > 0 -> n
       | _ -> 1)
  in

  (* easycrypt/proof/step — atomic single or N-sentence advance.
     count defaults to 1; >1 loops step_one until At_end / Failed /
     count exhausted. Aggregates the results into the v0 response
     envelope (advancedTo = last successful sid). Coalescing rapid
     keypresses into one count-batched request keeps the daemon's
     request queue from ballooning under hold-key auto-repeat. *)
  Lsp_server.register_request server (proof_method "step")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
        | Error msg -> Error (internal_error_resp msg)
        | Ok () ->
          let count = opt_count req in
          let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
          let executed = ref 0 in
          let last_sid = ref None in
          let at_end = ref false in
          let last_error = ref None in
          let advanced_at_least_once = ref false in
          let rec loop n =
            if n <= 0 then ()
            else
              match Proof_state.step_one proof_state with
              | `At_end -> at_end := true
              | `Advanced (_, sid) ->
                advanced_at_least_once := true;
                incr executed;
                last_sid := sid;
                (* PG-style: emit per-step so the locked tint
                   advances incrementally under a count-batched
                   request, instead of jumping at the end. *)
                emit_state_changed server ~io ~uri ~proof_state ~corr_id;
                loop (n - 1)
              | `Failed (_, sid, e) ->
                advanced_at_least_once := true;
                last_sid := sid;
                last_error := Some e;
                emit_state_changed server ~io ~uri ~proof_state ~corr_id
                (* don't continue past a failure *)
          in
          loop count;
          let _ = advanced_at_least_once in
          let cur_sid =
            match !last_sid with
            | Some _ -> !last_sid
            | None -> (Proof_state.snapshot proof_state).current_sentence_id
          in
          (match !last_error with
           | None ->
             Ok (`Assoc [
               "advancedTo", sid_to_json cur_sid;
               "newCas", `String zero_cas;
               "executedSentences", `Int !executed;
               "skippedSentences", `Int 0;
               "diagnostics", `List [];
               "atEndOfDocument", `Bool !at_end;
             ])
           | Some e ->
             Ok (`Assoc [
               "advancedTo", sid_to_json cur_sid;
               "newCas", `String zero_cas;
               "executedSentences", `Int !executed;
               "skippedSentences", `Int 0;
               "diagnostics", `List [
                 `Assoc [
                   "code", `String "TacticFailure";
                   "phase", `String "tactic";
                   "detail", `String (Error.to_string e);
                 ]
               ];
               "atEndOfDocument", `Bool false;
             ])));

  (* easycrypt/proof/back — atomic single or N-sentence revert.
     Symmetric to step. count defaults to 1. *)
  Lsp_server.register_request server (proof_method "back")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
        | Error msg -> Error (internal_error_resp msg)
        | Ok () ->
          let count = opt_count req in
          let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
          let last_sid = ref None in
          let reverted_at_least_once = ref false in
          let last_failed = ref None in
          let rec loop n =
            if n <= 0 then ()
            else
              match Proof_state.back_one proof_state with
              | `At_start -> ()
              | `Reverted (_, sid) ->
                reverted_at_least_once := true;
                last_sid := sid;
                loop (n - 1)
              | `Failed e -> last_failed := Some e
          in
          loop count;
          if !reverted_at_least_once then
            emit_state_changed server ~io ~uri ~proof_state ~corr_id;
          (match !last_failed with
           | Some e -> Error (internal_error_resp (Error.to_string e))
           | None ->
             Ok (`Assoc [
               "revertedTo", sid_to_json !last_sid;
               "newCas", `String zero_cas;
             ])));

  (* easycrypt/proof/restart — tear down + respawn primary session
     for the URI's project. Other projects' sessions (in the same
     connection) untouched. *)
  Lsp_server.register_request server (proof_method "restart")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        let proof_state = resolve_ps uri in
        Proof_state.restart proof_state ~sw;
        let corr_id = string_of_int (Jsonrpc.Id.hash req.id) in
        emit_state_changed server ~io ~uri ~proof_state ~corr_id;
        Ok (`Assoc [
          "newCas", `String zero_cas;
          "currentSentenceId", `Null;
        ]));

  (* easycrypt/proof/cancel — interrupt the in-flight tactic on the
     primary session via SIGINT. Returns immediately; the in-flight
     request (e.g. execToPoint, tryTactic) surfaces "canceled" as a
     normal error response on its own fiber. The handler does NOT
     take the proof-state mutex — by design, the in-flight request
     holds it, and interrupting the holder is the whole point.
     Params: { uri }. The optional `seq` param described in
     doc/lsp-schema.md is not yet wired (per-request seq IDs are
     deferred to a polish pass — current scope: cancel ALL
     in-flight work on this connection's primary session).

     UPSTREAM § 25 / doc/cancellation.md C3. *)
  Lsp_server.register_request server (proof_method "cancel")
    (fun (req : Jsonrpc.Request.t) ->
      match read_uri req with
      | Error msg -> Error (invalid_params msg)
      | Ok (uri, _) ->
        (* UPSTREAM § 14: route cancel via the manager — only the
           URI's project session gets SIGINT'd; other projects'
           in-flight tactics in the same connection stay
           untouched. *)
        Session_manager.cancel_in_flight manager ~uri;
        Ok (`Assoc [ "canceled", `Bool true ]));

  (* easycrypt/proof/tryTactic — speculative one-shot trial.
     Captures the primary's uuid, executes [source] as Executable,
     captures goals, rolls back. Primary state unchanged. Holds the
     proof_state mutex across capture/exec/rollback (via
     [Proof_state.with_session]) so other handlers don't race. *)
  Lsp_server.register_request server (proof_method "tryTactic")
    (fun (req : Jsonrpc.Request.t) ->
      match req.params with
      | None -> Error (invalid_params "missing params")
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        (try
           let uri = Yojson.Safe.Util.member "uri" params
                     |> Yojson.Safe.Util.to_string in
           let source = Yojson.Safe.Util.member "source" params
                        |> Yojson.Safe.Util.to_string in
           let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
           | Error msg -> Error (internal_error_resp msg)
           | Ok () ->
             (* Capture pre-count BEFORE the speculation so we can
                report whether the FOCUSED subgoal closed (count
                delta), not just whether the whole proof closed
                (count == 0). Same semantics as suggest_closers. *)
             let count_before, outcome =
               Proof_state.with_session proof_state (fun s ->
                 let pre = Proof_speculation.goal_count_now s in
                 let r = Proof_speculation.try_tactic s ~source in
                 (pre, r))
             in
             (match outcome with
              | Proof_speculation.Trial_ok { goals; body } ->
                let goals_json =
                  match goals with
                  | None -> `Null
                  | Some gv ->
                    (* Match the proof/goals envelope: clients render
                       the same shape for both. provenance="speculation"
                       distinguishes from "fresh" (real state). *)
                    (match Goal_view.to_json gv with
                     | `Assoc kvs ->
                       `Assoc (kvs @ [
                         "provenance", `String "speculation";
                         "cas", `String zero_cas;
                       ])
                     | other -> other)
                in
                let count_after =
                  match goals with
                  | None -> None
                  | Some gv -> Some gv.subgoal_count
                in
                let closed_focused =
                  match count_before, count_after with
                  | _, Some 0 -> true
                  | Some before, Some after when after < before -> true
                  | _ -> false
                in
                Ok (`Assoc [
                  "outcome", `String "ok";
                  "body", `String body;
                  "goalsAfter", goals_json;
                  "closedFocused", `Bool closed_focused;
                  "error", `Null;
                  "newCas", `String zero_cas;
                ])
              | Proof_speculation.Trial_err detail ->
                Ok (`Assoc [
                  "outcome", `String "err";
                  "body", `Null;
                  "goalsAfter", `Null;
                  "closedFocused", `Bool false;
                  "error", `String detail;
                  "newCas", `String zero_cas;
                ]))
         with
         | Yojson.Safe.Util.Type_error (msg, _) ->
           Error (invalid_params msg)
         | exn ->
           Error (internal_error_resp (Printexc.to_string exn))));

  (* easycrypt/proof/suggestClosers — sweep the curated closer list
     speculatively and return per-candidate outcomes. Stops early
     on first closer. Holds the proof_state mutex across the whole
     sweep so other handlers don't race. PoC stopgap: no per-
     candidate timeout (proof/cancel rework gates that). *)
  Lsp_server.register_request server (proof_method "suggestClosers")
    (fun (req : Jsonrpc.Request.t) ->
      match req.params with
      | None -> Error (invalid_params "missing params")
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        (try
           let uri = Yojson.Safe.Util.member "uri" params
                     |> Yojson.Safe.Util.to_string in
           let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
           | Error msg -> Error (internal_error_resp msg)
           | Ok () ->
             let result =
               Proof_state.with_session proof_state (fun s ->
                 Proof_speculation.suggest_closers s ())
             in
             (match result with
              | Error e ->
                Error (internal_error_resp (Error.to_string e))
              | Ok rows ->
                let row_json (r : Proof_speculation.suggest_row) =
                  match r.outcome with
                  | Proof_speculation.Suggest_closes ->
                    `Assoc [
                      "src", `String r.src;
                      "label", `String r.label;
                      "outcome", `String "closes";
                    ]
                  | Proof_speculation.Suggest_open n ->
                    `Assoc [
                      "src", `String r.src;
                      "label", `String r.label;
                      "outcome", `String "open";
                      "subgoalCount", `Int n;
                    ]
                  | Proof_speculation.Suggest_err msg ->
                    `Assoc [
                      "src", `String r.src;
                      "label", `String r.label;
                      "outcome", `String "err";
                      "detail", `String msg;
                    ]
                in
                Ok (`Assoc [
                  "rows", `List (List.map row_json rows);
                  "newCas", `String zero_cas;
                ]))
         with
         | Yojson.Safe.Util.Type_error (msg, _) ->
           Error (invalid_params msg)
         | exn ->
           Error (internal_error_resp (Printexc.to_string exn))));

  (* easycrypt/proof/searchLemmas — dispatch an EC `search` directive
     (read-only, doesn't advance uuid per addition 7) and return the
     parsed hits. Caller (VSCode lemma picker) supplies the search
     pattern as a complete EC source string (with parens applied,
     trailing dot, etc.); daemon runs it via Proof_speculation.query
     and parses the resulting NOTICE: lines via Search_result.of_notices.

     Used by the parity Phase 4 lemma picker (apply / rewrite). *)
  Lsp_server.register_request server (proof_method "searchLemmas")
    (fun (req : Jsonrpc.Request.t) ->
      match req.params with
      | None -> Error (invalid_params "missing params")
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        (try
           let uri = Yojson.Safe.Util.member "uri" params
                     |> Yojson.Safe.Util.to_string in
           let source = Yojson.Safe.Util.member "source" params
                        |> Yojson.Safe.Util.to_string in
           let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
           | Error msg -> Error (internal_error_resp msg)
           | Ok () ->
             let result =
               Proof_state.with_session proof_state (fun s ->
                 Proof_speculation.query s ~source)
             in
             (match result with
              | Error e ->
                (* EC's search command can return a TypeError when the
                   pattern is ambiguous; surface that to the caller as
                   a structured error. *)
                Ok (`Assoc [
                  "hits", `List [];
                  "error", `String (Error.to_string e);
                ])
              | Ok q ->
                let hits = Search_result.of_notices q.notices in
                let hit_json (h : Search_result.hit) =
                  `Assoc [
                    "qname", `String h.qname;
                    "kind", `String h.kind;
                    "short_name", `String h.short_name;
                    "signature", `String h.signature;
                  ]
                in
                Ok (`Assoc [
                  "hits", `List (List.map hit_json hits);
                  "error", `Null;
                ]))
         with
         | Yojson.Safe.Util.Type_error (msg, _) ->
           Error (invalid_params msg)
         | exn ->
           Error (internal_error_resp (Printexc.to_string exn))));

  (* easycrypt/proof/print — dispatch any read-only EC directive
     (`print foo.`, `print theory T.`, `locate qname.`, etc.) and
     return its captured pp-text output. Caller supplies a complete
     directive source (with trailing dot). Read-only by addition 7,
     so no state mutation. Used by the VSCode print command. *)
  Lsp_server.register_request server (proof_method "print")
    (fun (req : Jsonrpc.Request.t) ->
      match req.params with
      | None -> Error (invalid_params "missing params")
      | Some structured ->
        let params = (structured :> Yojson.Safe.t) in
        (try
           let uri = Yojson.Safe.Util.member "uri" params
                     |> Yojson.Safe.Util.to_string in
           let source = Yojson.Safe.Util.member "source" params
                        |> Yojson.Safe.Util.to_string in
           let proof_state = resolve_ps uri in
        match bind_doc proof_state doc_sources ~sw ~uri with
           | Error msg -> Error (internal_error_resp msg)
           | Ok () ->
             let result =
               Proof_state.with_session proof_state (fun s ->
                 Proof_speculation.query s ~source)
             in
             (match result with
              | Error e ->
                Ok (`Assoc [
                  "output", `String "";
                  "error", `String (Error.to_string e);
                ])
              | Ok q ->
                (* Concatenate body + notices: most prints land in
                   body, but some directives also stream NOTICE lines. *)
                let combined =
                  let nb = String.concat "\n" q.notices in
                  if q.body = "" then nb
                  else if nb = "" then q.body
                  else q.body ^ "\n" ^ nb
                in
                Ok (`Assoc [
                  "output", `String combined;
                  "error", `Null;
                ]))
         with
         | Yojson.Safe.Util.Type_error (msg, _) ->
           Error (invalid_params msg)
         | exn ->
           Error (internal_error_resp (Printexc.to_string exn))));

  Lsp_server.register_request server (proof_method "checkpoint")
    (fun (_req : Jsonrpc.Request.t) ->
      Error (lsp_error_of
               Jsonrpc.Response.Error.Code.MethodNotFound
               "checkpoint not implemented (deferred to v1)"));

  Lsp_server.register_request server (proof_method "revertCheckpoint")
    (fun (_req : Jsonrpc.Request.t) ->
      Error (lsp_error_of
               Jsonrpc.Response.Error.Code.MethodNotFound
               "revertCheckpoint not implemented (deferred to v1)"));

  Lsp_server.register_request server (proof_method "refreshDeps")
    (fun (_req : Jsonrpc.Request.t) ->
      Ok (`Assoc [
        "invalidatedFiles", `List [];
        "invalidatedEntries", `Int 0;
      ]))

(* ---------------------------------------------------------------- *)
(* Composition                                                        *)
(* ---------------------------------------------------------------- *)

let register_all server ~io ~manager ~debouncer
    ~sw ~doc_sources =
  register_lifecycle server;
  register_text_document server ~io ~manager ~sw ~debouncer
    ~doc_sources;
  register_proof_methods server ~io ~sw ~manager ~doc_sources
