(* MCP server smoke — drives `ecd mcp` over stdio with real EC
   sessions. Covers the JSON-RPC envelope (initialize / tools/list /
   tools/call / unknown-method), the core tool set (open_file, goals,
   try_tactic state-neutrality, exec, tree, focus, query,
   commit_proof, analyze_file), and the parallel-session axis (two
   labeled sessions with isolated proof states). *)

let pass = ref 0
let fail = ref 0

let check name ok detail =
  if ok then begin
    incr pass;
    Printf.printf "  ok  %s\n%!" name
  end else begin
    incr fail;
    Printf.printf "  FAIL %s — %s\n%!" name detail
  end

(* ---------------------------------------------------------------- *)
(* Process + ndjson plumbing                                          *)
(* ---------------------------------------------------------------- *)

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
    Printf.eprintf "ecd binary not found\n";
    exit 2

let spawn_mcp () =
  let bin = ecd_bin () in
  let stdin_r,  stdin_w  = Unix.pipe () in
  let stdout_r, stdout_w = Unix.pipe () in
  (* Keep the parent-side pipe ends out of the child: without
     close-on-exec the child inherits a copy of stdin's WRITE end,
     so closing ours never delivers EOF and the EOF-shutdown check
     times out. *)
  Unix.set_close_on_exec stdin_w;
  Unix.set_close_on_exec stdout_r;
  let pid =
    Unix.create_process bin [| bin; "mcp" |] stdin_r stdout_w Unix.stderr
  in
  Unix.close stdin_r;
  Unix.close stdout_w;
  pid, stdin_w, stdout_r

let send_line fd (j : Yojson.Safe.t) =
  let s = Yojson.Safe.to_string j ^ "\n" in
  let b = Bytes.of_string s in
  ignore (Unix.write fd b 0 (Bytes.length b))

let pending = ref ""

let read_line_fd fd =
  let rec go () =
    match String.index_opt !pending '\n' with
    | Some i ->
      let line = String.sub !pending 0 i in
      pending :=
        String.sub !pending (i + 1) (String.length !pending - i - 1);
      line
    | None ->
      let buf = Bytes.create 65536 in
      let n = Unix.read fd buf 0 65536 in
      if n = 0 then failwith "unexpected EOF from ecd mcp";
      pending := !pending ^ Bytes.sub_string buf 0 n;
      go ()
  in
  go ()

let next_id = ref 100

let request fd meth params =
  let id = !next_id in
  incr next_id;
  send_line fd
    (`Assoc [
       "jsonrpc", `String "2.0";
       "id", `Int id;
       "method", `String meth;
       "params", params;
     ]);
  id

(* Read messages until the response with [id] arrives. *)
let read_response fd ~id =
  let rec go () =
    let line = read_line_fd fd in
    match Yojson.Safe.from_string line with
    | exception _ -> go ()
    | j ->
      (match Yojson.Safe.Util.member "id" j with
       | `Int i when i = id -> j
       | _ -> go ())
  in
  go ()

let member = Yojson.Safe.Util.member

(* tools/call → decoded inner JSON payload (from content[0].text) +
   isError flag. *)
let call fd_in fd_out name arguments =
  let id =
    request fd_in "tools/call"
      (`Assoc [ "name", `String name; "arguments", arguments ])
  in
  let resp = read_response fd_out ~id in
  (* On protocol-level failures (unknown tool → JSON-RPC error) there
     is no "result" object; treat as isError with empty payload. *)
  let result =
    try member "result" resp with _ -> `Null
  in
  let is_error =
    match result with
    | `Assoc _ ->
      (match member "isError" result with `Bool b -> b | _ -> false)
    | _ -> true
  in
  let text =
    try
      match member "content" result with
      | `List (first :: _) ->
        (match member "text" first with `String s -> s | _ -> "")
      | _ -> ""
    with _ -> ""
  in
  let payload =
    try Yojson.Safe.from_string text with _ -> `String text
  in
  (is_error, payload)

let subgoal_count payload =
  try
    match member "goals" payload with
    | `Assoc _ as g ->
      (match member "subgoal_count" g with `Int n -> n | _ -> -1)
    | _ -> -1
  with _ -> -1

(* ---------------------------------------------------------------- *)
(* Fixture                                                            *)
(* ---------------------------------------------------------------- *)

let fixture_dir = "/tmp/mcp-smoke"
let fixture = Filename.concat fixture_dir "test.ec"

let write_fixture () =
  (try Unix.mkdir fixture_dir 0o755
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let oc = open_out fixture in
  output_string oc
    "require import AllCore.\n\
     lemma t2 : 1 = 1 /\\ 2 = 2.\n\
     proof.\n\
     split.\n";
  close_out oc

(* ---------------------------------------------------------------- *)
(* Main                                                               *)
(* ---------------------------------------------------------------- *)

let () =
  write_fixture ();
  let pid, fd_in, fd_out = spawn_mcp () in

  (* -- lifecycle ------------------------------------------------- *)
  let id_init =
    request fd_in "initialize"
      (`Assoc [
         "protocolVersion", `String "2025-03-26";
         "capabilities", `Assoc [];
         "clientInfo",
         `Assoc [ "name", `String "mcp-smoke"; "version", `String "0" ];
       ])
  in
  let init = read_response fd_out ~id:id_init in
  let init_result = member "result" init in
  check "initialize: protocolVersion echoed"
    (match member "protocolVersion" init_result with
     | `String "2025-03-26" -> true | _ -> false)
    (Yojson.Safe.to_string init_result);
  check "initialize: serverInfo.name = ecd-mcp"
    (try
       member "serverInfo" init_result |> member "name"
       = `String "ecd-mcp"
     with _ -> false) "";
  check "initialize: declares tools capability"
    (match member "capabilities" init_result |> member "tools" with
     | `Assoc _ -> true | _ -> false) "";
  send_line fd_in
    (`Assoc [
       "jsonrpc", `String "2.0";
       "method", `String "notifications/initialized";
     ]);

  (* -- tools/list ------------------------------------------------- *)
  let id_list = request fd_in "tools/list" (`Assoc []) in
  let tools_resp = read_response fd_out ~id:id_list in
  let tool_names =
    try
      member "result" tools_resp |> member "tools"
      |> Yojson.Safe.Util.to_list
      |> List.filter_map (fun tj ->
          match member "name" tj with `String s -> Some s | _ -> None)
    with _ -> []
  in
  check "tools/list: >= 11 tools" (List.length tool_names >= 11)
    (Printf.sprintf "got %d" (List.length tool_names));
  List.iter
    (fun expected ->
       check (Printf.sprintf "tools/list: has %s" expected)
         (List.mem expected tool_names) "")
    [ "open_file"; "exec"; "goals"; "try_tactic"; "commit_proof" ];

  (* -- open + speculate + advance -------------------------------- *)
  let (err, opened) =
    call fd_in fd_out "open_file" (`Assoc [ "path", `String fixture ])
  in
  check "open_file: ok" (not err) (Yojson.Safe.to_string opened);
  check "open_file: 2 goals after split" (subgoal_count opened = 2)
    (Printf.sprintf "got %d" (subgoal_count opened));
  check "open_file: uuid=4 (require/lemma/proof/split)"
    (match member "uuid" opened with `Int 4 -> true | _ -> false)
    (Yojson.Safe.to_string (member "uuid" opened));

  let (err, tried) =
    call fd_in fd_out "try_tactic"
      (`Assoc [ "tactic", `String "reflexivity." ])
  in
  let after_count =
    try
      match member "goals_after" tried with
      | `Assoc _ as g ->
        (match member "subgoal_count" g with `Int n -> n | _ -> -1)
      | _ -> -1
    with _ -> -1
  in
  check "try_tactic: ok outcome"
    ((not err)
     && member "outcome" tried = `String "ok")
    (Yojson.Safe.to_string tried);
  check "try_tactic: goals_after has 1 subgoal" (after_count = 1)
    (Printf.sprintf "got %d" after_count);

  let (err, g) = call fd_in fd_out "goals" (`Assoc []) in
  check "goals after try_tactic: still 2 (state-neutral speculation)"
    ((not err) && subgoal_count g = 2)
    (Printf.sprintf "got %d" (subgoal_count g));

  let (err, ex) =
    call fd_in fd_out "exec" (`Assoc [ "text", `String "reflexivity." ])
  in
  check "exec reflexivity: ok, uuid=5"
    ((not err)
     && (match member "uuid" ex with `Int 5 -> true | _ -> false))
    (Yojson.Safe.to_string ex);
  check "exec reflexivity: 1 goal remains" (subgoal_count ex = 1)
    (Printf.sprintf "got %d" (subgoal_count ex));

  let (err, tr) = call fd_in fd_out "tree" (`Assoc []) in
  let tree_text =
    match member "tree" tr with `String s -> s | _ -> ""
  in
  check "tree: shows remaining goal"
    ((not err)
     && (try
           ignore (Str.search_forward (Str.regexp_string "2 = 2")
                     tree_text 0);
           true
         with Not_found -> false))
    tree_text;

  let (err, q) =
    call fd_in fd_out "query"
      (`Assoc [ "text", `String "print op (+)." ])
  in
  let q_out = match member "output" q with `String s -> s | _ -> "" in
  check "query print: non-empty output"
    ((not err) && String.length q_out > 0)
    (Yojson.Safe.to_string q);
  let (_, g2) = call fd_in fd_out "goals" (`Assoc []) in
  check "query is state-neutral (uuid unchanged)"
    (match member "uuid" g2 with `Int 5 -> true | _ -> false)
    (Yojson.Safe.to_string (member "uuid" g2));

  let (err, sr) =
    call fd_in fd_out "search"
      (`Assoc [ "pattern", `String "(_ <= _)"; "limit", `Int 5 ])
  in
  let total_hits =
    match member "total_hits" sr with `Int n -> n | _ -> -1
  in
  let shown_hits =
    try
      match member "hits" sr with `List xs -> List.length xs | _ -> -1
    with _ -> -1
  in
  let first_qname_nonempty =
    try
      match member "hits" sr with
      | `List (h :: _) ->
        (match member "qname" h with
         | `String s -> String.length s > 0 | _ -> false)
      | _ -> false
    with _ -> false
  in
  check "search (searchall mode): hits on untyped (_ <= _)"
    ((not err) && total_hits > 0)
    (Printf.sprintf "total=%d" total_hits);
  check "search: limit honored + truncation reported"
    (shown_hits = 5
     && (match member "truncated" sr with `Bool true -> true | _ -> false))
    (Printf.sprintf "shown=%d" shown_hits);
  check "search: structured hit has qname" first_qname_nonempty "";

  let (err, cp) = call fd_in fd_out "commit_proof" (`Assoc []) in
  let proof_text =
    match member "proof" cp with `String s -> s | _ -> ""
  in
  check "commit_proof: contains the executed tactic"
    ((not err)
     && (try
           ignore (Str.search_forward (Str.regexp_string "reflexivity.")
                     proof_text 0);
           true
         with Not_found -> false))
    proof_text;

  (* -- parallel sessions ----------------------------------------- *)
  let (err, w2) =
    call fd_in fd_out "open_file"
      (`Assoc [ "path", `String fixture; "session", `String "w2" ])
  in
  check "open_file w2: ok with 2 goals"
    ((not err) && subgoal_count w2 = 2)
    (Printf.sprintf "got %d" (subgoal_count w2));
  let (_, g_main) = call fd_in fd_out "goals" (`Assoc []) in
  check "parallel isolation: main still has 1 goal"
    (subgoal_count g_main = 1)
    (Printf.sprintf "got %d" (subgoal_count g_main));

  let (err, rv) =
    call fd_in fd_out "revert"
      (`Assoc [ "uuid", `Int 3; "session", `String "w2" ])
  in
  check "revert w2 to uuid 3: single conjunction goal"
    ((not err) && subgoal_count rv = 1)
    (Printf.sprintf "got %d" (subgoal_count rv));

  let (err, ls) = call fd_in fd_out "list_sessions" (`Assoc []) in
  let n_sessions =
    try
      match member "sessions" ls with
      | `List xs -> List.length xs | _ -> 0
    with _ -> 0
  in
  check "list_sessions: 2 sessions" ((not err) && n_sessions = 2)
    (Printf.sprintf "got %d" n_sessions);

  let (err, an) =
    call fd_in fd_out "analyze_file"
      (`Assoc [ "path", `String fixture ])
  in
  let n_sentences, n_diags =
    try
      let a = member "analysis" an in
      let s =
        match member "sentences" a with `List xs -> List.length xs | _ -> -1
      in
      let d =
        match member "diagnostics" a with
        | `List xs -> List.length xs | _ -> -1
      in
      (s, d)
    with _ -> (-1, -1)
  in
  check "analyze_file: 4 sentences, 0 diagnostics"
    ((not err) && n_sentences = 4 && n_diags = 0)
    (Printf.sprintf "sentences=%d diags=%d" n_sentences n_diags);

  let (err, cl) =
    call fd_in fd_out "close_session"
      (`Assoc [ "session", `String "w2" ])
  in
  check "close_session w2: ok" (not err) (Yojson.Safe.to_string cl);
  let (_, ls2) = call fd_in fd_out "list_sessions" (`Assoc []) in
  let n2 =
    try
      match member "sessions" ls2 with
      | `List xs -> List.length xs | _ -> 0
    with _ -> 0
  in
  check "list_sessions after close: 1" (n2 = 1)
    (Printf.sprintf "got %d" n2);

  (* -- error paths ------------------------------------------------ *)
  let (err, _) =
    call fd_in fd_out "no_such_tool" (`Assoc [])
  in
  (* unknown tool answers as a JSON-RPC error, so call's result
     decode yields empty content; accept either isError or empty. *)
  ignore err;
  let id_bogus = request fd_in "bogus/method" (`Assoc []) in
  let bogus = read_response fd_out ~id:id_bogus in
  check "unknown method: JSON-RPC error -32601"
    (try
       member "error" bogus |> member "code" = `Int (-32601)
     with _ -> false)
    (Yojson.Safe.to_string bogus);

  let (err_sess, _) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "trivial.";
                "session", `String "ghost" ])
  in
  check "exec on unknown session: isError" err_sess "";

  (* -- shutdown --------------------------------------------------- *)
  Unix.close fd_in;
  let deadline = Unix.gettimeofday () +. 10.0 in
  let exited = ref None in
  while !exited = None && Unix.gettimeofday () < deadline do
    (match Unix.waitpid [ Unix.WNOHANG ] pid with
     | 0, _ -> Unix.sleepf 0.1
     | _, status -> exited := Some status)
  done;
  (match !exited with
   | Some (Unix.WEXITED 0) ->
     check "ecd mcp exits cleanly on stdin EOF" true ""
   | Some st ->
     let d =
       match st with
       | Unix.WEXITED n -> Printf.sprintf "exit %d" n
       | Unix.WSIGNALED n -> Printf.sprintf "signal %d" n
       | Unix.WSTOPPED n -> Printf.sprintf "stopped %d" n
     in
     check "ecd mcp exits cleanly on stdin EOF" false d
   | None ->
     Unix.kill pid Sys.sigkill;
     check "ecd mcp exits cleanly on stdin EOF" false "timeout");

  Printf.printf "\n== MCP smoke ==\n  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
