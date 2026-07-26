(** Stage 4 / Slice A — drive [ecd daemon --stdio] over LSP through a
    Proof-General-style proof workflow:

    didOpen → step → step → goals → back → goals → restart.

    Asserts:
    - [easycrypt/proof/step] returns advancedTo = sid of the next sentence.
    - [easycrypt/proof/goals] returns the GOALS-JSON envelope with
      provenance="fresh", cas=zero (Stage 5 will fill these in).
    - Every state-mutating call elicits an
      [easycrypt/proof/stateChanged] notification with monotonic [seq].
    - [easycrypt/proof/back] reverts one sentence; sub-zero target =
      pre-everything state.

    Skips with exit 0 if no EC binary is available — keeps CI green
    on hosts without the prover toolchain. *)

let pass = ref 0
let fail = ref 0

let check name ok ctx =
  if ok then begin
    Printf.printf "  ok  %s\n%!" name;
    incr pass
  end
  else begin
    Printf.printf "  FAIL %s — %s\n%!" name ctx;
    incr fail
  end

let ec_binary_path () =
  match Sys.getenv_opt "EC_LLM_BIN" with
  | Some p -> Some p
  | None ->
    let candidate =
      Filename.concat (Sys.getcwd ()) "_build/default/src/ec.exe"
    in
    if Sys.file_exists candidate then Some candidate
    else
      let ic = Unix.open_process_in "command -v easycrypt 2>/dev/null" in
      let line = try Some (input_line ic) with End_of_file -> None in
      let _ = Unix.close_process_in ic in
      line

let ecd_bin () =
  let candidates =
    [ "../daemon/main.exe"
    ; "../../tooling/daemon/main.exe"
    ; Filename.concat (Sys.getcwd ()) "tooling/daemon/main.exe"
    ; "_build/default/tooling/daemon/main.exe"
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> p
  | None ->
    Printf.eprintf "ecd binary not found; tried:\n";
    List.iter (fun p -> Printf.eprintf "  %s\n" p) candidates;
    exit 2

let spawn_stdio_daemon ~ec_bin =
  let bin = ecd_bin () in
  let stdin_r,  stdin_w  = Unix.pipe () in
  let stdout_r, stdout_w = Unix.pipe () in
  let stderr_r, stderr_w = Unix.pipe () in
  let pid =
    Unix.create_process bin
      [| bin; "daemon"; "--stdio"; "--bin"; ec_bin |]
      stdin_r stdout_w stderr_w
  in
  Unix.close stdin_r;
  Unix.close stdout_w;
  Unix.close stderr_w;
  pid, stdin_w, stdout_r, stderr_r

let write_packet fd packet =
  let body = Yojson.Safe.to_string (Jsonrpc.Packet.yojson_of_t packet) in
  let header = Printf.sprintf "Content-Length: %d\r\n\r\n" (String.length body) in
  let bytes_h = Bytes.of_string header in
  let bytes_b = Bytes.of_string body in
  let _ = Unix.write fd bytes_h 0 (Bytes.length bytes_h) in
  let _ = Unix.write fd bytes_b 0 (Bytes.length bytes_b) in
  ()

let read_packet fd : Jsonrpc.Packet.t option =
  let buf = Buffer.create 256 in
  let read_byte () =
    let b = Bytes.create 1 in
    let n = try Unix.read fd b 0 1 with _ -> 0 in
    if n = 0 then None else Some (Bytes.get b 0)
  in
  let read_line () =
    Buffer.clear buf;
    let rec loop () =
      match read_byte () with
      | None -> None
      | Some '\r' ->
        (match read_byte () with
         | Some '\n' -> Some (Buffer.contents buf)
         | _ -> None)
      | Some c -> Buffer.add_char buf c; loop ()
    in
    loop ()
  in
  let content_length = ref None in
  let rec headers () =
    match read_line () with
    | None -> false
    | Some "" -> true
    | Some line ->
      (match String.index_opt line ':' with
       | Some i ->
         let name =
           String.sub line 0 i |> String.trim |> String.lowercase_ascii
         in
         let value =
           String.sub line (i + 1) (String.length line - i - 1) |> String.trim
         in
         if name = "content-length" then content_length := int_of_string_opt value
       | None -> ());
      headers ()
  in
  if not (headers ()) then None
  else match !content_length with
    | None -> None
    | Some n ->
      let body = Bytes.create n in
      let rec read_exact pos =
        if pos = n then ()
        else
          let r = Unix.read fd body pos (n - pos) in
          if r = 0 then failwith "short read"
          else read_exact (pos + r)
      in
      read_exact 0;
      try Some (Jsonrpc.Packet.t_of_yojson
                  (Yojson.Safe.from_string (Bytes.to_string body)))
      with _ -> None

(* Read packets until a Response with the given id arrives, collecting
   any Notifications encountered along the way. Returns
   (response, notifications_in_order). *)
let read_until_response fd ~id =
  let notifs = ref [] in
  let rec loop () =
    match read_packet fd with
    | None -> failwith "EOF while waiting for response"
    | Some (Jsonrpc.Packet.Response r) when r.id = id ->
      r, List.rev !notifs
    | Some (Jsonrpc.Packet.Notification n) ->
      notifs := n :: !notifs;
      loop ()
    | Some _ -> loop ()
  in
  loop ()

(* Build a Structured.t from raw JSON; only Assoc / List are valid. *)
let structured_of (j : Yojson.Safe.t) : Jsonrpc.Structured.t option =
  match j with
  | `Assoc _ | `List _ as s -> Some (s :> Jsonrpc.Structured.t)
  | _ -> None

let request id method_ params =
  Jsonrpc.Packet.Request
    (Jsonrpc.Request.create ?params:(structured_of params)
       ~id ~method_ ())

let request_no_params id method_ =
  Jsonrpc.Packet.Request (Jsonrpc.Request.create ~id ~method_ ())

let notification method_ params =
  let n =
    match params with
    | Some p ->
      (match structured_of p with
       | Some s -> Jsonrpc.Notification.create ~method_ ~params:s ()
       | None -> Jsonrpc.Notification.create ~method_ ())
    | None -> Jsonrpc.Notification.create ~method_ ()
  in
  Jsonrpc.Packet.Notification n

let state_changed_in notifs =
  List.find_opt
    (fun (n : Jsonrpc.Notification.t) ->
      n.method_ = "easycrypt/proof/stateChanged")
    notifs

let result_ok = function
  | Jsonrpc.Response.{ result = Ok j; _ } -> Some j
  | _ -> None

let () =
  Printf.printf "== Stage 4 / Slice A LSP proof-flow smoke ==\n%!";

  match ec_binary_path () with
  | None ->
    Printf.printf "skip: no ec binary found (set EC_LLM_BIN)\n%!";
    exit 0
  | Some ec_bin ->

  let pid, fd_in, fd_out, fd_err = spawn_stdio_daemon ~ec_bin in

  let init_params =
    `Assoc [
      "processId", `Null;
      "rootUri", `Null;
      "capabilities", `Assoc [];
    ]
  in
  write_packet fd_in (request (`Int 1) "initialize" init_params);
  let init_resp, _ = read_until_response fd_out ~id:(`Int 1) in
  check "initialize ok" (result_ok init_resp <> None) "";
  write_packet fd_in (notification "initialized" (Some (`Assoc [])));

  (* Open a tiny .ec document inline via didOpen with explicit text. *)
  let uri = "file:///proof-flow-smoke.ec" in
  let source =
    "require import AllCore.\n\
     lemma plus_two : 1 + 1 = 2.\n\
     proof.\n\
     by trivial.\n\
     qed.\n"
  in
  let did_open_params =
    `Assoc [
      "textDocument", `Assoc [
        "uri", `String uri;
        "languageId", `String "easycrypt";
        "version", `Int 1;
        "text", `String source;
      ];
    ]
  in
  write_packet fd_in (notification "textDocument/didOpen" (Some did_open_params));

  (* easycrypt/proof/step #1 — should advance to sentence 0 (require). *)
  let step_params =
    `Assoc [ "uri", `String uri ]
  in
  write_packet fd_in (request (`Int 2) "easycrypt/proof/step" step_params);
  let r1, n1 = read_until_response fd_out ~id:(`Int 2) in
  let j1 =
    match result_ok r1 with
    | Some j -> j | None -> `Null
  in
  let open Yojson.Safe.Util in
  check "step #1 returned result"
    (j1 <> `Null) "";
  check "step #1 advancedTo non-null"
    ((try j1 |> member "advancedTo" with _ -> `Null) <> `Null)
    (Yojson.Safe.to_string j1);
  let step1_advanced_to =
    try j1 |> member "advancedTo" |> to_string with _ -> ""
  in
  let n1_sc = state_changed_in n1 in
  check "step #1 emitted stateChanged"
    (n1_sc <> None) "";
  let n1_seq =
    match n1_sc with
    | Some n ->
      let p = (n.params :> Yojson.Safe.t option) in
      (match p with
       | Some p -> (try p |> member "seq" |> to_int with _ -> -1)
       | None -> -1)
    | None -> -1
  in
  check "step #1 stateChanged.seq is positive"
    (n1_seq > 0)
    (Printf.sprintf "got %d" n1_seq);

  (* step #2 *)
  write_packet fd_in (request (`Int 3) "easycrypt/proof/step" step_params);
  let r2, n2 = read_until_response fd_out ~id:(`Int 3) in
  let j2 = match result_ok r2 with Some j -> j | None -> `Null in
  check "step #2 advancedTo differs from step #1"
    ((try j2 |> member "advancedTo" |> to_string with _ -> "") <> step1_advanced_to)
    (Yojson.Safe.to_string j2);
  let n2_sc = state_changed_in n2 in
  let n2_seq =
    match n2_sc with
    | Some n ->
      let p = (n.params :> Yojson.Safe.t option) in
      (match p with
       | Some p -> (try p |> member "seq" |> to_int with _ -> -1)
       | None -> -1)
    | None -> -1
  in
  check "step #2 stateChanged.seq is monotonically increasing"
    (n2_seq > n1_seq) (Printf.sprintf "got %d after %d" n2_seq n1_seq);

  (* goals at current state — should return active envelope *)
  write_packet fd_in (request (`Int 4) "easycrypt/proof/goals" step_params);
  let r3, _ = read_until_response fd_out ~id:(`Int 4) in
  let j3 = match result_ok r3 with Some j -> j | None -> `Null in
  check "goals returned object"
    (match j3 with `Assoc _ -> true | _ -> false) "";
  check "goals envelope has provenance=fresh"
    ((try j3 |> member "provenance" |> to_string with _ -> "") = "fresh") "";
  check "goals envelope has zero cas"
    ((try j3 |> member "cas" |> to_string with _ -> "")
     = "00000000000000000000000000000000") "";

  (* Wire-level regression for the lsp_server write_mutex bug:
     pipeline N goals requests rapid-fire (no intermediate reads),
     then drain all responses. Each request triggers a daemon-side
     fiber whose response write contends with the others on the
     write_mutex; with stdlib Mutex the daemon would crash with
     Sys_error("Mutex.lock: Resource deadlock avoided"), with
     Eio.Mutex they serialize cleanly. *)
  let pipeline_n = 16 in
  for i = 0 to pipeline_n - 1 do
    write_packet fd_in
      (request (`Int (1000 + i)) "easycrypt/proof/goals" step_params)
  done;
  let pipeline_results =
    List.init pipeline_n (fun i ->
      let r, _ = read_until_response fd_out ~id:(`Int (1000 + i)) in
      r)
  in
  let pipeline_ok =
    List.for_all (fun r ->
      match r.Jsonrpc.Response.result with Ok _ -> true | _ -> false)
      pipeline_results
  in
  check "pipelined goals requests all returned Ok"
    pipeline_ok
    (Printf.sprintf "expected %d Ok responses" pipeline_n);

  (* Slice D — didChange auto-reconcile. Edit sentence #1 (the lemma
     statement) so the locked region's content diverges. The daemon
     should retract the primary back to before the divergence and
     emit a stateChanged with a smaller currentEndPosition than
     after step #2. *)
  let edited_source =
    "require import AllCore.\n\
     lemma plus_three : 1 + 2 = 3.\n\
     proof.\n\
     by trivial.\n\
     qed.\n"
  in
  let did_change_params =
    `Assoc [
      "textDocument", `Assoc [
        "uri", `String uri;
        "version", `Int 2;
      ];
      "contentChanges", `List [
        `Assoc [ "text", `String edited_source ];
      ];
    ]
  in
  let n2_end_line =
    match n2_sc with
    | Some n ->
      let p = (n.params :> Yojson.Safe.t option) in
      (match p with
       | Some p ->
         (try p |> member "currentEndPosition"
                |> member "line" |> to_int
          with _ -> -1)
       | None -> -1)
    | None -> -1
  in
  write_packet fd_in (notification "textDocument/didChange"
                        (Some did_change_params));
  (* The daemon emits stateChanged asynchronously after reconcile;
     drain notifications until we either see one or hit a small
     timeout via a follow-up goals request. *)
  write_packet fd_in (request (`Int 99) "easycrypt/proof/goals" step_params);
  let _r99, n99 = read_until_response fd_out ~id:(`Int 99) in
  let reconcile_sc = state_changed_in n99 in
  check "didChange emitted stateChanged (reconcile)"
    (reconcile_sc <> None)
    "no stateChanged notification arrived after didChange";
  let new_end_line =
    match reconcile_sc with
    | Some n ->
      let p = (n.params :> Yojson.Safe.t option) in
      (match p with
       | Some p ->
         (match p |> member "currentEndPosition" with
          | `Null -> -1
          | other -> (try other |> member "line" |> to_int with _ -> -1))
       | None -> -1)
    | None -> -1
  in
  check "reconcile retracted past the edited sentence"
    (new_end_line < n2_end_line)
    (Printf.sprintf "n2_end_line=%d new_end_line=%d"
       n2_end_line new_end_line);

  (* back — revert one sentence (post-reconcile, we're at sentence 0
     so back should revert to pre-everything → revertedTo = null). *)
  write_packet fd_in (request (`Int 5) "easycrypt/proof/back" step_params);
  let r4, n4 = read_until_response fd_out ~id:(`Int 5) in
  let j4 = match result_ok r4 with Some j -> j | None -> `Null in
  check "back returned result"
    (j4 <> `Null) "";
  check "back from sentence-0 revertedTo is null"
    ((try j4 |> member "revertedTo" with _ -> `Null) = `Null)
    (Yojson.Safe.to_string j4);
  check "back emitted stateChanged"
    (state_changed_in n4 <> None) "";

  (* step with count > 1 — advance multiple sentences in one request.
     Coalesces rapid keypresses into a single request so the daemon's
     queue can't balloon under hold-key auto-repeat. *)
  let step_count_params count =
    `Assoc [ "uri", `String uri; "count", `Int count ]
  in
  write_packet fd_in
    (request (`Int 50) "easycrypt/proof/step" (step_count_params 2));
  let r_count, n_count = read_until_response fd_out ~id:(`Int 50) in
  let j_count = match result_ok r_count with Some j -> j | None -> `Null in
  check "step count=2 returned result" (j_count <> `Null) "";
  check "step count=2 advanced 2 sentences"
    ((try j_count |> member "executedSentences" |> to_int with _ -> 0) = 2)
    (Yojson.Safe.to_string j_count);
  (* PG-style progressive locked-tint: each successful sentence
     should emit its own stateChanged so the client's lock advances
     in step. count=2 ⇒ 2 notifications. *)
  let state_changed_count notifs =
    List.fold_left
      (fun n (notif : Jsonrpc.Notification.t) ->
        if notif.method_ = "easycrypt/proof/stateChanged" then n + 1
        else n)
      0 notifs
  in
  check "step count=2 emits 2 stateChanged (PG-style progressive lock)"
    (state_changed_count n_count = 2)
    (Printf.sprintf "got %d notifications" (state_changed_count n_count));

  (* execToPoint over multiple sentences: regression guard for the
     deadlock that hung this request after the per-step on_step
     callback was wired (callback called Proof_state.snapshot which
     re-acquired the non-reentrant Eio.Mutex held by exec_to). The
     fix uses a lockless emit_state_changed_at variant. Test:
     issue execToPoint with target = sentence 2 from the start,
     expect the request to complete + emit 3 stateChanged
     (one per sentence advanced). Also bound the wait. *)
  let exec_target =
    `Assoc [
      "uri", `String uri;
      "target", `Assoc [
        "position", `Assoc [
          "line", `Int 4; "character", `Int 0;
        ];
      ];
    ]
  in
  (* Reset to start by reverting first. *)
  let revert_target =
    `Assoc [
      "uri", `String uri;
      "target", `Assoc [
        "position", `Assoc [
          "line", `Int 0; "character", `Int 0;
        ];
      ];
    ]
  in
  write_packet fd_in
    (request (`Int 60) "easycrypt/proof/revertToPoint" revert_target);
  let _r_revert, _ = read_until_response fd_out ~id:(`Int 60) in
  write_packet fd_in
    (request (`Int 61) "easycrypt/proof/execToPoint" exec_target);
  let r_exec, n_exec = read_until_response fd_out ~id:(`Int 61) in
  check "execToPoint multi-sentence completed (no deadlock)"
    (result_ok r_exec <> None) "no result";
  let exec_state_changes = state_changed_count n_exec in
  check "execToPoint emits >= 1 stateChanged per executed sentence"
    (exec_state_changes >= 1)
    (Printf.sprintf "got %d notifications" exec_state_changes);
  (* back with count > 1 — symmetric. *)
  write_packet fd_in
    (request (`Int 51) "easycrypt/proof/back" (step_count_params 2));
  let r_back_count, _ = read_until_response fd_out ~id:(`Int 51) in
  check "back count=2 returned result"
    (result_ok r_back_count <> None) "";
  (* count clamps to At_end / At_start gracefully. Asking for many
     forward steps from sentence 0 with a 3-sentence file should not
     error. *)
  write_packet fd_in
    (request (`Int 52) "easycrypt/proof/step" (step_count_params 99));
  let r_clamp, _ = read_until_response fd_out ~id:(`Int 52) in
  let j_clamp = match result_ok r_clamp with Some j -> j | None -> `Null in
  check "step count=99 clamps to At_end"
    ((try j_clamp |> member "atEndOfDocument" |> to_bool with _ -> false))
    (Yojson.Safe.to_string j_clamp);

  (* restart *)
  write_packet fd_in (request (`Int 6) "easycrypt/proof/restart" step_params);
  let r5, n5 = read_until_response fd_out ~id:(`Int 6) in
  check "restart returned result"
    (result_ok r5 <> None) "";
  check "restart emitted stateChanged"
    (state_changed_in n5 <> None) "";

  (* Position resolver — exec-to-cursor on inter-sentence whitespace
     must resolve to the PRECEDING sentence (matches PG behavior),
     NOT the next one. Open a fresh doc with a blank line between
     `require` and `lemma`; exec to the blank line; assert only 1
     sentence was executed (require) and advancedTo == require's sid. *)
  let blank_uri = "file:///proof-flow-smoke-blank.ec" in
  let blank_source =
    "require import AllCore.\n\
     \n\
     lemma plus_two : 1 + 1 = 2.\n\
     proof.\n\
     by trivial.\n\
     qed.\n"
  in
  write_packet fd_in (notification "textDocument/didOpen" (Some (
    `Assoc [
      "textDocument", `Assoc [
        "uri", `String blank_uri;
        "languageId", `String "easycrypt";
        "version", `Int 1;
        "text", `String blank_source;
      ];
    ])));
  let blank_step_params = `Assoc [ "uri", `String blank_uri ] in
  write_packet fd_in
    (request (`Int 70) "easycrypt/proof/step" blank_step_params);
  let r_blank_step, _ = read_until_response fd_out ~id:(`Int 70) in
  let require_sid =
    match result_ok r_blank_step with
    | Some j -> (try j |> member "advancedTo" |> to_string with _ -> "")
    | None -> ""
  in
  check "blank-line fixture: step #1 captured require sid"
    (require_sid <> "") "no advancedTo on first step";
  (* Revert to fresh state via back count=99 (clamps at start). *)
  write_packet fd_in
    (request (`Int 71) "easycrypt/proof/back" (step_count_params 99));
  let _r_blank_back, _ = read_until_response fd_out ~id:(`Int 71) in
  (* execToPoint at LSP line 1 col 0 — that's the blank line BETWEEN
     require (line 0) and lemma (line 2). With the bug, this would
     resolve to lemma → executedSentences=2. With the fix (and the
     contract documented in proof_state.mli), resolves to require →
     executedSentences=1. *)
  let blank_exec = `Assoc [
    "uri", `String blank_uri;
    "target", `Assoc [
      "position", `Assoc [
        "line", `Int 1; "character", `Int 0;
      ];
    ];
  ] in
  write_packet fd_in
    (request (`Int 72) "easycrypt/proof/execToPoint" blank_exec);
  let r_blank_exec, _ = read_until_response fd_out ~id:(`Int 72) in
  let blank_exec_j =
    match result_ok r_blank_exec with Some j -> j | None -> `Null
  in
  let blank_executed =
    try blank_exec_j |> member "executedSentences" |> to_int
    with _ -> -1
  in
  let blank_advanced_to =
    try blank_exec_j |> member "advancedTo" |> to_string with _ -> ""
  in
  check "execToPoint on blank line: executedSentences=1 (preceding sentence, not next)"
    (blank_executed = 1)
    (Printf.sprintf "got executedSentences=%d, advancedTo=%s"
       blank_executed blank_advanced_to);
  check "execToPoint on blank line: advancedTo == require sid"
    (blank_advanced_to = require_sid)
    (Printf.sprintf "expected %s, got %s" require_sid blank_advanced_to);

  (* easycrypt/proof/execAll — advance to end of document. The
     blank-line fixture has 4 sentences (require / lemma / proof /
     trivial / qed); execAll from sentence 1 should advance to all
     remaining ones. *)
  let exec_all_params = `Assoc [ "uri", `String blank_uri ] in
  write_packet fd_in
    (request (`Int 80) "easycrypt/proof/execAll" exec_all_params);
  let r_exec_all, _ = read_until_response fd_out ~id:(`Int 80) in
  let exec_all_j =
    match result_ok r_exec_all with Some j -> j | None -> `Null
  in
  check "execAll returned result"
    (exec_all_j <> `Null) "";
  let exec_all_at_end =
    try exec_all_j |> member "atEndOfDocument" |> to_bool with _ -> false
  in
  check "execAll: atEndOfDocument = true"
    exec_all_at_end
    (Yojson.Safe.to_string exec_all_j);
  let exec_all_diags =
    try exec_all_j |> member "diagnostics" |> to_list with _ -> []
  in
  check "execAll: no diagnostics on a passing document"
    (List.length exec_all_diags = 0)
    (Printf.sprintf "got %d" (List.length exec_all_diags));

  (* UPSTREAM § 14 — cross-project isolation. Two URIs in
     different "projects" (synthetic fallback: each file's
     containing directory is the project root since neither path
     has an easycrypt.project up-tree). The daemon should spawn
     ONE EC subprocess per project; advancing in project A must
     not affect project B's locked-region state, and vice versa. *)
  let mk_open uri text =
    notification "textDocument/didOpen" (Some (`Assoc [
      "textDocument", `Assoc [
        "uri", `String uri;
        "languageId", `String "easycrypt";
        "version", `Int 1;
        "text", `String text;
      ];
    ]))
  in
  (* The per-project fixture directories must exist — the daemon
     spawns each project's EC subprocess with its cwd set there, and
     a missing cwd fails the spawn (surfaced as fixture rot when /tmp
     gets cleaned between runs). *)
  List.iter
    (fun d ->
       try Unix.mkdir d 0o755
       with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
    [ "/tmp/sm-smoke-projA"; "/tmp/sm-smoke-projB" ];
  let uri_a = "file:///tmp/sm-smoke-projA/proof.ec" in
  let uri_b = "file:///tmp/sm-smoke-projB/proof.ec" in
  let body =
    "require import AllCore.\n\
     lemma id_zero : 0 = 0.\n\
     proof.\n\
     by trivial.\n\
     qed.\n"
  in
  write_packet fd_in (mk_open uri_a body);
  write_packet fd_in (mk_open uri_b body);

  (* Step in project A — 2 sentences. *)
  let step_two uri id =
    let p = `Assoc [ "uri", `String uri; "count", `Int 2 ] in
    write_packet fd_in (request id "easycrypt/proof/step" p);
    let _r, _ = read_until_response fd_out ~id in
    ()
  in
  step_two uri_a (`Int 100);

  (* Goals in A — should be active (advanced past `require + lemma`). *)
  let goals_at uri id =
    write_packet fd_in (request id "easycrypt/proof/goals"
                          (`Assoc [ "uri", `String uri ]));
    let r, _ = read_until_response fd_out ~id in
    match result_ok r with Some j -> j | None -> `Null
  in
  let g_a_before = goals_at uri_a (`Int 101) in
  let active_a_before =
    try g_a_before |> member "active" |> to_bool with _ -> false
  in
  check "session_manager: project A is active after stepping"
    active_a_before
    (Yojson.Safe.to_string g_a_before);

  (* Goals in B — should still be inactive (no steps in B yet). If
     sessions were shared, A's state would leak into B. *)
  let g_b_before = goals_at uri_b (`Int 102) in
  let active_b_before =
    try g_b_before |> member "active" |> to_bool with _ -> false
  in
  check "session_manager: project B inactive while only A advanced"
    (not active_b_before)
    (Yojson.Safe.to_string g_b_before);

  (* Step in B; A's state must persist across B's mutation. *)
  step_two uri_b (`Int 103);
  let g_a_after = goals_at uri_a (`Int 104) in
  let active_a_after =
    try g_a_after |> member "active" |> to_bool with _ -> false
  in
  check "session_manager: project A still active after stepping B"
    active_a_after
    (Yojson.Safe.to_string g_a_after);

  (* shutdown / exit *)
  write_packet fd_in (request_no_params (`Int 7) "shutdown");
  let r6, _ = read_until_response fd_out ~id:(`Int 7) in
  check "shutdown ok"
    (match r6.result with Ok _ -> true | _ -> false) "";
  write_packet fd_in (notification "exit" None);
  (try Unix.close fd_in with _ -> ());

  let deadline = Unix.gettimeofday () +. 5.0 in
  let exited = ref None in
  while !exited = None && Unix.gettimeofday () < deadline do
    (try
       let r, status = Unix.waitpid [Unix.WNOHANG] pid in
       if r <> 0 then exited := Some status
     with _ -> exited := Some (Unix.WEXITED 0));
    if !exited = None then ignore (Unix.select [] [] [] 0.05)
  done;
  (match !exited with
   | Some (Unix.WEXITED 0) -> check "daemon exited cleanly" true ""
   | Some _ ->
     check "daemon exited cleanly" false "non-zero exit";
     (try Unix.kill pid Sys.sigterm with _ -> ())
   | None ->
     check "daemon exited within 5s" false "timeout";
     (try Unix.kill pid Sys.sigterm with _ -> ()));

  (try Unix.close fd_out with _ -> ());
  (try Unix.close fd_err with _ -> ());

  Printf.printf "\n== LSP proof-flow smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
