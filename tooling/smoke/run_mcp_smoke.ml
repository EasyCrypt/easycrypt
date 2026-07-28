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
     lemma t1 : 0 = 0.\n\
     proof.\n\
     trivial.\n\
     qed.\n\
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
    [ "open_file"; "exec"; "goals"; "try_tactic"; "commit_proof";
      "define" ];

  (* -- open (proof mode, claiming t2) + speculate + advance ------- *)
  let (err, opened) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String fixture;
         "mode", `String "proof";
         "lemmas", `List [ `String "t2" ];
       ])
  in
  check "open_file: ok" (not err) (Yojson.Safe.to_string opened);
  check "open_file: 2 goals after split" (subgoal_count opened = 2)
    (Printf.sprintf "got %d" (subgoal_count opened));
  check "open_file: uuid=8 (both lemmas' sentences)"
    (match member "uuid" opened with `Int 8 -> true | _ -> false)
    (Yojson.Safe.to_string (member "uuid" opened));
  let claim0 =
    try
      match member "claims" opened with
      | `List (c :: _) -> c
      | _ -> `Null
    with _ -> `Null
  in
  check "open_file: claim resolved to t2's region (lines 6..8)"
    (member "lemma" claim0 = `String "t2"
     && member "start_line" claim0 = `Int 6
     && member "end_line" claim0 = `Int 8)
    (Yojson.Safe.to_string claim0);

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
  check "exec reflexivity: ok, uuid=9"
    ((not err)
     && (match member "uuid" ex with `Int 9 -> true | _ -> false))
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
    (match member "uuid" g2 with `Int 9 -> true | _ -> false)
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

  (* -- lock discipline ------------------------------------------- *)
  let (err, conflict) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String fixture;
         "session", `String "w2";
         "mode", `String "proof";
         "lemmas", `List [ `String "t2" ];
       ])
  in
  let conflict_text = Yojson.Safe.to_string conflict in
  check "proof mode: overlapping lemma claim refused"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "claim conflict")
                     conflict_text 0);
           true
         with Not_found -> false))
    conflict_text;

  let (err, unknown) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String fixture;
         "session", `String "w3";
         "mode", `String "proof";
         "lemmas", `List [ `String "ghost_lemma" ];
       ])
  in
  check "proof mode: unknown lemma claim refused"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "not found")
                     (Yojson.Safe.to_string unknown) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string unknown);

  let (err, blocked) =
    call fd_in fd_out "open_file"
      (`Assoc [ "path", `String fixture; "session", `String "editor" ])
  in
  check "statement mode (default): refused while proof session holds file"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "exclusive")
                     (Yojson.Safe.to_string blocked) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string blocked);

  (* -- parallel sessions (disjoint claims) ------------------------ *)
  let (err, w2) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String fixture;
         "session", `String "w2";
         "mode", `String "proof";
         "lemmas", `List [ `String "t1" ];
       ])
  in
  check "open_file w2 (disjoint claim t1): ok with 2 goals"
    ((not err) && subgoal_count w2 = 2)
    (Printf.sprintf "got %d" (subgoal_count w2));
  let (_, g_main) = call fd_in fd_out "goals" (`Assoc []) in
  check "parallel isolation: main still has 1 goal"
    (subgoal_count g_main = 1)
    (Printf.sprintf "got %d" (subgoal_count g_main));

  let (err, rv) =
    call fd_in fd_out "revert"
      (`Assoc [ "uuid", `Int 7; "session", `String "w2" ])
  in
  check "revert w2 to uuid 7: single conjunction goal"
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
  let main_row =
    try
      match member "sessions" ls with
      | `List xs ->
        List.find_opt
          (fun r -> member "session" r = `String "main")
          xs
        |> Option.value ~default:`Null
      | _ -> `Null
    with _ -> `Null
  in
  check "list_sessions: main row carries mode + claims"
    (member "mode" main_row = `String "proof"
     && (match member "claims" main_row with
         | `List (_ :: _) -> true | _ -> false))
    (Yojson.Safe.to_string main_row);

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
  check "analyze_file: 8 sentences, 0 diagnostics"
    ((not err) && n_sentences = 8 && n_diags = 0)
    (Printf.sprintf "sentences=%d diags=%d" n_sentences n_diags);

  (* -- refactoring loop: check_script / stale / resync / replace -- *)
  let (err, cs) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "split.\ntrivial.\ntrivial.\nqed.";
         "session", `String "w2";
       ])
  in
  check "check_script: 4 sentences, ok, closes"
    ((not err)
     && (match member "checked" cs with `Int 4 -> true | _ -> false)
     && member "ok" cs = `Bool true
     && member "closes" cs = `Bool true)
    (Yojson.Safe.to_string cs);
  check "check_script: state restored (uuid back to 7)"
    (member "restore" cs = `String "restored"
     && member "uuid" cs = `Int 7)
    (Yojson.Safe.to_string (member "restore" cs));

  (* Edit the file on disk: complete t2's proof. *)
  let oc = open_out_gen [ Open_append ] 0o644 fixture in
  output_string oc "trivial.\ntrivial.\nqed.\n";
  close_out oc;

  let (err, g) =
    call fd_in fd_out "goals" (`Assoc [ "session", `String "w2" ])
  in
  check "stale flag set after on-disk edit"
    ((not err) && member "stale" g = `Bool true)
    (Yojson.Safe.to_string (member "stale" g));

  let (err, rp0) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "t1";
         "script", `String "proof.\nby trivial.\nqed.";
         "session", `String "w2";
       ])
  in
  check "replace_proof: stale-gated before resync"
    (err
     && (try
           ignore (Str.search_forward (Str.regexp_string "resync")
                     (Yojson.Safe.to_string rp0) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string rp0);

  let (err, rs) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "w2" ])
  in
  check "resync_file: appended completion classifies additive"
    ((not err)
     && member "changed" rs = `Bool true
     (* round 4: completing a previously-open proof ADDS the lemma
        to the environment — that is additive, not body-only. *)
     && member "classification" rs = `String "additive"
     && (match member "tail_executed" rs with
         | `Int 3 -> true | _ -> false)
     && member "tail_skipped" rs = `Int 0
     && member "ok" rs = `Bool true)
    (Yojson.Safe.to_string rs);

  let (err, rp1) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "t1";
         "script", `String "proof.\nby trivial.\nqed.";
         "session", `String "w2";
       ])
  in
  check "replace_proof: verified + written"
    ((not err) && member "ok" rp1 = `Bool true
     && member "file_written" rp1 = `Bool true)
    (Yojson.Safe.to_string rp1);
  let rp1v = member "verification" rp1 in
  check "replace_proof: certificate skips the unchanged tail (P5)"
    (member "classification" rp1v = `String "proof-body-only"
     && member "tail_skipped" rp1v = `Int 6
     && (match member "note" rp1v with `String _ -> true | _ -> false))
    (Yojson.Safe.to_string rp1v);
  let read_fixture () =
    let ic = open_in fixture in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s
  in
  check "replace_proof: file carries the new body"
    (try
       ignore (Str.search_forward (Str.regexp_string "by trivial.")
                 (read_fixture ()) 0);
       true
     with Not_found -> false)
    "";

  let (err, rp2) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "t1";
         "script", `String "proof.\napply nonexistent_lemma_xyz.\nqed.";
         "session", `String "w2";
       ])
  in
  check "replace_proof: failing script restores the file"
    ((not err) && member "ok" rp2 = `Bool false
     && member "file_restored" rp2 = `Bool true
     && (try
           ignore (Str.search_forward (Str.regexp_string "by trivial.")
                     (read_fixture ()) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string rp2);

  let (err, rp3) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "t2";
         "script", `String "proof.\nqed.";
         "session", `String "w2";
       ])
  in
  check "replace_proof: unclaimed lemma refused"
    (err
     && (try
           ignore (Str.search_forward (Str.regexp_string "not claimed")
                     (Yojson.Safe.to_string rp3) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string rp3);

  (* -- strategy layer: outline / profile / skeleton / claims ------ *)
  let (err, ol) =
    call fd_in fd_out "proof_outline"
      (`Assoc [ "lemma", `String "t2"; "session", `String "w2" ])
  in
  let n_obl =
    try
      match member "obligations" ol with
      | `List l -> List.length l
      | _ -> -1
    with _ -> -1
  in
  check "proof_outline t2: 1 split point, 2 obligations"
    ((not err)
     && member "ok" ol = `Bool true
     && member "split_points" ol = `Int 1
     && n_obl = 2)
    (Yojson.Safe.to_string ol);

  let (err, pf) =
    call fd_in fd_out "proof_profile"
      (`Assoc [ "lemma", `String "t2"; "session", `String "w2" ])
  in
  check "proof_profile t2: aggregates, no smt/admit"
    ((not err)
     && member "ok" pf = `Bool true
     && member "total_smt" pf = `Int 0
     && member "total_admits" pf = `Int 0
     && (match member "branches" pf with
         | `List (_ :: _) -> true
         | _ -> false))
    (Yojson.Safe.to_string pf);

  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "w2"; "upto_line", `Int 7 ])
  in
  check "resync to line 7 (t2 open, pre-split)" (not err) "";

  let (err, sk) =
    call fd_in fd_out "check_skeleton"
      (`Assoc [
         "script", `String "split.\nadmit.\nadmit.\nqed.";
         "session", `String "w2";
       ])
  in
  let hole0_path =
    try
      match member "holes" sk with
      | `List (h :: _) -> member "path" h
      | _ -> `Null
    with _ -> `Null
  in
  check "check_skeleton: 2 holes with paths, closes, restored"
    ((not err)
     && member "ok" sk = `Bool true
     && member "closes_with_holes" sk = `Bool true
     && (match member "holes" sk with
         | `List l -> List.length l = 2
         | _ -> false)
     && hole0_path = `String "1"
     && member "restore" sk = `String "restored")
    (Yojson.Safe.to_string sk);

  (* -- B5: exec is strictly per-sentence ------------------------- *)
  let (err, em) =
    call fd_in fd_out "exec"
      (`Assoc [
         "text", `String "split.\ntrivial.";
         "session", `String "w2";
       ])
  in
  let em_goals =
    try
      match member "goals" em with
      | `Assoc _ as g -> member "subgoal_count" g
      | _ -> `Null
    with _ -> `Null
  in
  check "B5: exec runs ALL sentences (split+trivial -> 1 goal)"
    ((not err)
     && member "ok" em = `Bool true
     && member "executed" em = `Int 2
     && em_goals = `Int 1)
    (Yojson.Safe.to_string em);
  check "P3: no net goal growth -> no auto-tree"
    (member "tree" em = `Null) (Yojson.Safe.to_string em);
  let (err, _) =
    call fd_in fd_out "revert"
      (`Assoc [ "uuid", `Int 7; "session", `String "w2" ])
  in
  check "revert after exec-multi" (not err) "";

  let (err, pe) =
    call fd_in fd_out "exec"
      (`Assoc [
         "text", `String "split.\nbogus_tactic_xyz.";
         "session", `String "w2";
       ])
  in
  check "B5b: parse error in input refuses ATOMICALLY (nothing ran)"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "parse error")
                     (Yojson.Safe.to_string pe) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string pe);

  let (err, ef) =
    call fd_in fd_out "exec"
      (`Assoc [
         "text", `String "split.\napply bogus_lemma_xyz.\ntrivial.";
         "session", `String "w2";
       ])
  in
  let ef_gaf =
    try
      match member "goals_at_failure" ef with
      | `Assoc _ as g -> member "subgoal_count" g
      | _ -> `Null
    with _ -> `Null
  in
  check "B5: mid-sequence failure reported, prefix committed"
    ((not err)
     && member "ok" ef = `Bool false
     && member "executed" ef = `Int 1
     && ef_gaf = `Int 2
     && member "goals" ef = `Null)
    (Yojson.Safe.to_string ef);
  let (err, _) =
    call fd_in fd_out "revert"
      (`Assoc [ "uuid", `Int 7; "session", `String "w2" ])
  in
  check "revert after exec-multi failure" (not err) "";

  let (err, gc) =
    call fd_in fd_out "goals"
      (`Assoc [
         "session", `String "w2"; "goal_detail", `String "counts";
       ])
  in
  let gc_body =
    try member "goals" gc with _ -> `Null
  in
  check "F5: goal_detail=counts — conclusions only, no subgoals"
    ((not err)
     && (match member "conclusions" gc_body with
         | `List [ `String _ ] -> true
         | _ -> false)
     && member "subgoals" gc_body = `Null)
    (Yojson.Safe.to_string gc);

  (* -- round 4: auto-tree on growth + smt_timeout ----------------- *)
  let (err, tt2) =
    call fd_in fd_out "try_tactic"
      (`Assoc [ "tactic", `String "split."; "session", `String "w2" ])
  in
  let tt2_tree =
    match member "tree" tt2 with `String s -> s | _ -> ""
  in
  check "P3: try_tactic split attaches compact tree (pre-revert)"
    ((not err)
     && member "outcome" tt2 = `String "ok"
     && (try
           ignore (Str.search_forward (Str.regexp_string "2 = 2")
                     tt2_tree 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string tt2);
  let (_, g_tt2) =
    call fd_in fd_out "goals" (`Assoc [ "session", `String "w2" ])
  in
  check "P3: try_tactic still state-neutral with tree capture"
    (member "uuid" g_tt2 = `Int 7)
    (Yojson.Safe.to_string (member "uuid" g_tt2));

  let (err, st0) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "split.\ntrivial.\ntrivial.";
         "smt_timeout", `Int 5;
         "session", `String "w2";
       ])
  in
  check "P4: smt_timeout applied transactionally and echoed"
    ((not err)
     && member "ok" st0 = `Bool true
     && member "smt_timeout" st0 = `Int 5
     && member "restore" st0 = `String "restored"
     && member "uuid" st0 = `Int 7)
    (Yojson.Safe.to_string st0);
  let (err, st1) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "trivial.";
         "smt_timeout", `Int 0;
         "session", `String "w2";
       ])
  in
  check "P4: smt_timeout 0 refused"
    (err
     && (try
           ignore (Str.search_forward (Str.regexp_string "positive")
                     (Yojson.Safe.to_string st1) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string st1);

  let (err, exsp) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "split."; "session", `String "w2" ])
  in
  check "exec split (2 goals for claims)" (not err) "";
  check "P3: exec goal growth attaches compact tree"
    (match member "tree" exsp with
     | `String s ->
       (try
          ignore (Str.search_forward (Str.regexp_string "[") s 0);
          true
        with Not_found -> false)
     | _ -> false)
    (Yojson.Safe.to_string exsp);

  let (err, cl) =
    call fd_in fd_out "claim_subgoal"
      (`Assoc [ "path", `String "2"; "session", `String "w2" ])
  in
  check "claim_subgoal 2: remaining=1 with entry hash"
    ((not err)
     && member "remaining_in_subtree" cl = `Int 1
     && (match member "entry_hash" cl with
         | `String h -> String.length h > 0
         | _ -> false))
    (Yojson.Safe.to_string cl);

  let (err, ei0) =
    call fd_in fd_out "exec_in"
      (`Assoc [ "text", `String "qed."; "session", `String "w2" ])
  in
  check "exec_in: closer refused inside claim"
    (err
     && (try
           ignore (Str.search_forward (Str.regexp_string "not allowed")
                     (Yojson.Safe.to_string ei0) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string ei0);

  (* `cycle` is not a tactic, so a bulleted `+ cycle.` is an EC
     parse error — refused upstream of the gate, nothing runs. The
     keyword gate remains as defense-in-depth. *)
  let (err, eib) =
    call fd_in fd_out "exec_in"
      (`Assoc [ "text", `String "+ cycle."; "session", `String "w2" ])
  in
  check "B6-audit: bulleted cycle cannot advance a claimed session"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp "not allowed\\|nothing ran")
                     (Yojson.Safe.to_string eib) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string eib);

  let (err, ei1) =
    call fd_in fd_out "exec_in"
      (`Assoc [ "text", `String "trivial."; "session", `String "w2" ])
  in
  check "exec_in trivial: subtree closed, transcript returned"
    ((not err)
     && member "subtree_closed" ei1 = `Bool true
     && (match member "transcript" ei1 with
         | `List [ `String "trivial." ] -> true
         | _ -> false))
    (Yojson.Safe.to_string ei1);

  let (err, cl2) =
    call fd_in fd_out "claim_subgoal"
      (`Assoc [ "path", `String "9"; "session", `String "w2" ])
  in
  check "claim_subgoal: unknown path refused"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "no open subtree")
                     (Yojson.Safe.to_string cl2) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string cl2);

  (* -- banner-comment declarations + stateless analyze ------------ *)
  let cmt = Filename.concat fixture_dir "cmt.ec" in
  let oc = open_out cmt in
  output_string oc
    "require import AllCore.\n\
     (* banner: house style *)\n\
     lemma banner : 2 + 2 = 4.\n\
     proof.\n\
     trivial.\n\
     qed.\n";
  close_out oc;
  let (err, bo) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String cmt;
         "session", `String "w9";
         "mode", `String "proof";
         "lemmas", `List [ `String "banner" ];
       ])
  in
  let bclaim =
    try
      match member "claims" bo with `List (c :: _) -> c | _ -> `Null
    with _ -> `Null
  in
  check "banner-comment lemma claimable (field-report bug)"
    ((not err)
     && member "lemma" bclaim = `String "banner"
     && member "decl_end_line" bclaim = `Int 3
     && member "end_line" bclaim = `Int 6)
    (Yojson.Safe.to_string bo);
  let (err, _) =
    call fd_in fd_out "close_session"
      (`Assoc [ "session", `String "w9" ])
  in
  check "close w9" (not err) "";

  let (err, an) =
    call fd_in fd_out "analyze_file"
      (`Assoc [ "path", `String cmt; "session", `String "ephemeral-x" ])
  in
  check "analyze_file: session-free (ephemeral spawn)"
    ((not err)
     && member "session" an = `String "(ephemeral)"
     && (match member "analysis" an with `Assoc _ -> true | _ -> false))
    (Yojson.Safe.to_string an);

  (* -- field-report round 2: B2 / at_lemma / fast-forward / F3 ---- *)
  let b2f = Filename.concat fixture_dir "b2.ec" in
  let write_b2 body =
    let oc = open_out b2f in
    output_string oc
      ("require import AllCore.\n\
        lemma p1 : 1 = 1.\n\
        proof. trivial. qed.\n\
        lemma p2 : 2 = 2.\n" ^ body);
    close_out oc
  in
  write_b2 "proof. trivial. qed.\n";
  let (err, _) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String b2f; "session", `String "wb";
         "nosmt", `Bool true;
       ])
  in
  check "b2 fixture open (packed lines)" (not err) "";
  write_b2 "proof. by trivial. qed.\n";
  let (err, rs) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wb"; "nosmt", `Bool false ])
  in
  check "B2: resync into a packed-line proof body"
    ((not err)
     && member "ok" rs = `Bool true
     && member "classification" rs = `String "proof-body-only")
    (Yojson.Safe.to_string rs);

  let (err, al) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wb"; "at_lemma", `String "p2" ])
  in
  let al_goals =
    try
      match member "goals" al with
      | `Assoc _ as g -> member "subgoal_count" g
      | _ -> `Null
    with _ -> `Null
  in
  check "at_lemma p2: positioned inside the proof (1 goal)"
    ((not err)
     && member "ok" al = `Bool true
     && member "classification" al = `String "reposition"
     && al_goals = `Int 1)
    (Yojson.Safe.to_string al);

  let (err, ff) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wb" ])
  in
  check "fast-forward: unchanged file, forward target, no reload"
    ((not err)
     && member "fast_forward" ff = `Bool true
     && member "ok" ff = `Bool true)
    (Yojson.Safe.to_string ff);

  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wb"; "at_lemma", `String "p2" ])
  in
  check "reposition back to p2" (not err) "";
  let (err, cs2) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "apply nonexistent_xyz.";
         "session", `String "wb";
       ])
  in
  let gaf =
    try
      match member "goals_at_failure" cs2 with
      | `Assoc _ as g -> member "subgoal_count" g
      | _ -> `Null
    with _ -> `Null
  in
  check "F3: goals_at_failure carries the state entering the failure"
    ((not err) && member "ok" cs2 = `Bool false && gaf = `Int 1
     && member "goals_at_end" cs2 = `Null)
    (Yojson.Safe.to_string cs2);

  (* -- B4: non-lemma declaration forms, from the AST -------------- *)
  let kinds = Filename.concat fixture_dir "kinds.ec" in
  let oc = open_out kinds in
  output_string oc
    "require import AllCore.\n\
     module M = { proc f() : int = { return 1; } }.\n\
     (* banner *)\n\
     hoare h_plain : M.f : true ==> true.\n\
     proof.\n\
     proc.\n\
     auto.\n\
     qed.\n";
  close_out oc;
  let (err, ko) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String kinds;
         "session", `String "wk";
         "mode", `String "proof";
         "lemmas", `List [ `String "h_plain" ];
         "nosmt", `Bool true;
       ])
  in
  let kclaim =
    try
      match member "claims" ko with `List (c :: _) -> c | _ -> `Null
    with _ -> `Null
  in
  check "B4: hoare declaration claimable via AST name (with banner)"
    ((not err) && member "lemma" kclaim = `String "h_plain")
    (Yojson.Safe.to_string ko);
  let (err, ka) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wk"; "at_lemma", `String "h_plain" ])
  in
  let ka_goals =
    try
      match member "goals" ka with
      | `Assoc _ as g -> member "subgoal_count" g
      | _ -> `Null
    with _ -> `Null
  in
  check "B4: at_lemma positions on a hoare declaration"
    ((not err) && member "ok" ka = `Bool true && ka_goals = `Int 1)
    (Yojson.Safe.to_string ka);
  let (err, _) =
    call fd_in fd_out "close_session"
      (`Assoc [ "session", `String "wk" ])
  in
  check "close wk" (not err) "";
  let (err, us) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wb"; "upto_sentence", `Int 8 ])
  in
  let us_goals =
    try
      match member "goals" us with
      | `Assoc _ as g -> member "active" g
      | _ -> `Null
    with _ -> `Null
  in
  check "upto_sentence 8: mid-packed-line boundary (after by trivial.)"
    ((not err)
     && member "ok" us = `Bool true
     && member "target_sentences" us = `Int 8
     && member "fast_forward" us = `Bool true
     && us_goals = `Bool false)
    (Yojson.Safe.to_string us);
  let (err, _) =
    call fd_in fd_out "close_session" (`Assoc [ "session", `String "wb" ])
  in
  check "close wb" (not err) "";

  (* -- ergonomic landing: iterate call = landing call ------------- *)
  let (err, _) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String b2f; "session", `String "wc";
         "mode", `String "proof";
         "lemmas", `List [ `String "p2" ];
         "nosmt", `Bool true;
       ])
  in
  check "wc open (landing tests)" (not err) "";
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wc"; "at_lemma", `String "p2" ])
  in
  check "wc at p2" (not err) "";
  let (err, cc) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "trivial.\nqed.";
         "on_close", `String "commit";
         "lemma", `String "p2";
         "session", `String "wc";
       ])
  in
  check "on_close=commit: passing script LANDS in the same call"
    ((not err)
     && member "closes" cc = `Bool true
     && member "restore" cc = `String "committed"
     && member "file_written" cc = `Bool true)
    (Yojson.Safe.to_string cc);

  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wc"; "at_lemma", `String "p2" ])
  in
  check "wc back at p2" (not err) "";
  let (err, ex2) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "by trivial."; "session", `String "wc" ])
  in
  check "exec closing step: proof_complete hint"
    ((not err)
     && member "ok" ex2 = `Bool true
     && member "proof_complete" ex2 = `Bool true)
    (Yojson.Safe.to_string ex2);
  let (err, cp) =
    call fd_in fd_out "commit_proof"
      (`Assoc [
         "lemma", `String "p2"; "write", `Bool true;
         "session", `String "wc";
       ])
  in
  check "commit_proof write: transcript lands verified"
    ((not err)
     && member "ok" cp = `Bool true
     && member "file_written" cp = `Bool true)
    (Yojson.Safe.to_string cp);
  let b2_final =
    let ic = open_in b2f in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic; s
  in
  check "landed body present in file"
    (try
       ignore (Str.search_forward
                 (Str.regexp_string "by trivial.") b2_final 0);
       true
     with Not_found -> false)
    b2_final;
  let (err, _) =
    call fd_in fd_out "close_session" (`Assoc [ "session", `String "wc" ])
  in
  check "close wc" (not err) "";

  (* -- admit visibility ------------------------------------------- *)
  let admf = Filename.concat fixture_dir "adm.ec" in
  let oc = open_out admf in
  output_string oc
    "require import AllCore.\n\
     lemma la : 1 = 1 /\\ 2 = 2.\n\
     proof.\n\
     split.\n\
     trivial.\n\
     admit.\n\
     qed.\n\
     lemma lb : 3 = 3.\n\
     proof.\n\
     admit.\n\
     qed.\n";
  close_out oc;
  let (err, _) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String admf; "session", `String "wd";
         "nosmt", `Bool true;
       ])
  in
  check "wd open (admit fixture)" (not err) "";
  let (err, ag) =
    call fd_in fd_out "admitted_goals"
      (`Assoc [ "session", `String "wd" ])
  in
  let first_admit_goal =
    try
      match member "admitted" ag with
      | `List (a :: _) ->
        (match member "goal" a with `String s -> s | _ -> "")
      | _ -> ""
    with _ -> ""
  in
  check "admitted_goals: both admits audited with their goals"
    ((not err)
     && member "admit_count" ag = `Int 2
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "2 = 2") first_admit_goal 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string ag);
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wd"; "at_lemma", `String "lb" ])
  in
  check "wd at lb" (not err) "";
  let (err, ea) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "admit."; "session", `String "wd" ])
  in
  check "exec admit: live admitted capture"
    ((not err)
     && (match member "admitted" ea with
         | `List [ a ] ->
           (match member "hash" a with
            | `String h -> String.length h > 0
            | _ -> false)
         | _ -> false))
    (Yojson.Safe.to_string ea);
  let (err, _) =
    call fd_in fd_out "close_session" (`Assoc [ "session", `String "wd" ])
  in
  check "close wd" (not err) "";

  (* -- round 4: certificate / comment-blind identity / define ----- *)
  let certf = Filename.concat fixture_dir "cert.ec" in
  let write_cert ~banner ~c1_line4 ~c2_body =
    let oc = open_out certf in
    output_string oc
      ("require import AllCore.\n" ^ banner
       ^ "lemma c1 : 1 = 1.\n" ^ c1_line4
       ^ "lemma c2 : 2 = 2.\nproof.\n" ^ c2_body ^ "qed.\n");
    close_out oc
  in
  write_cert ~banner:"(* banner one *)\n"
    ~c1_line4:"proof. trivial. qed.\n" ~c2_body:"trivial.\n";
  let (err, co) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String certf; "session", `String "wce";
         "mode", `String "proof";
         "lemmas", `List [ `String "c2" ];
         "nosmt", `Bool true;
       ])
  in
  check "cert fixture open (proof mode, c2 claimed)" (not err)
    (Yojson.Safe.to_string co);
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wce"; "at_lemma", `String "c1" ])
  in
  check "wce at c1" (not err) "";
  (* Edit BELOW the session position: the widened fast gate replays
     forward from the current state — no prefix reload. *)
  write_cert ~banner:"(* banner one *)\n"
    ~c1_line4:"proof. trivial. qed.\n" ~c2_body:"by trivial.\n";
  let (err, wf) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wce" ])
  in
  check "P5: below-position edit fast-forwards (no reload)"
    ((not err)
     && member "ok" wf = `Bool true
     && member "changed" wf = `Bool true
     && member "fast_forward" wf = `Bool true
     && member "classification" wf = `String "proof-body-only"
     && member "tail_executed" wf = `Int 6)
    (Yojson.Safe.to_string wf);
  (* qed -> abort changes what the environment CONTAINS: the
     certificate must refuse it (no proof-body-only label). *)
  write_cert ~banner:"(* banner one *)\n"
    ~c1_line4:"proof. trivial. abort.\n" ~c2_body:"by trivial.\n";
  let (err, ab) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wce" ])
  in
  check "P5: qed->abort fails the certificate (statement-changing)"
    ((not err)
     && member "ok" ab = `Bool true
     && member "classification" ab = `String "statement-changing"
     && (match member "warning" ab with `String _ -> true | _ -> false))
    (Yojson.Safe.to_string ab);
  write_cert ~banner:"(* banner one *)\n"
    ~c1_line4:"proof. trivial. qed.\n" ~c2_body:"by trivial.\n";
  let (err, _) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wce" ])
  in
  check "cert restored (qed back)" (not err) "";
  (* Comment-only edit: snapshot swap, zero execution, position
     preserved, claim regions remapped to the shifted lines. *)
  write_cert ~banner:"(* banner one *)\n(* banner two *)\n"
    ~c1_line4:"proof. trivial. qed.\n" ~c2_body:"by trivial.\n";
  let (err, fo) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wce" ])
  in
  let fo_claim0 =
    try
      match member "claims" fo with `List (c :: _) -> c | _ -> `Null
    with _ -> `Null
  in
  check "P6: comment-only edit is formatting-only, zero-cost"
    ((not err)
     && member "ok" fo = `Bool true
     && member "changed" fo = `Bool true
     && member "classification" fo = `String "formatting-only"
     && member "tail_executed" fo = `Int 0
     && member "prefix_time_ms" fo = `Int 0
     && member "synced_upto" fo = `Int 9
     && (match member "note" fo with `String _ -> true | _ -> false))
    (Yojson.Safe.to_string fo);
  check "P6: claim regions remapped to shifted lines"
    (member "lemma" fo_claim0 = `String "c2"
     && member "start_line" fo_claim0 = `Int 6)
    (Yojson.Safe.to_string fo_claim0);

  (* define: bind once, reference everywhere, expanded text is what
     runs and what lands. *)
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wce"; "at_lemma", `String "c2" ])
  in
  check "wce at c2" (not err) "";
  let (err, df) =
    call fd_in fd_out "define"
      (`Assoc [
         "name", `String "inv"; "text", `String "1 = 1";
         "session", `String "wce";
       ])
  in
  check "P1: define binds on the session"
    ((not err)
     && (match member "defines" df with
         | `List [ d ] -> member "name" d = `String "inv"
         | _ -> false))
    (Yojson.Safe.to_string df);
  let (err, dcs) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script", `String "have H : $inv.\ntrivial.\nby trivial.";
         "session", `String "wce";
       ])
  in
  let dcs_exp =
    match member "src_expanded" dcs with `String s -> s | _ -> ""
  in
  check "P1: $inv expands before parsing; src_expanded echoes"
    ((not err)
     && member "ok" dcs = `Bool true
     && member "closes" dcs = `Bool true
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "have H : 1 = 1") dcs_exp 0);
           true
         with Not_found -> false)
     && not (try
               ignore (Str.search_forward
                         (Str.regexp_string "$inv") dcs_exp 0);
               true
             with Not_found -> false))
    (Yojson.Safe.to_string dcs);
  let (err, qg) =
    call fd_in fd_out "query"
      (`Assoc [
         "text", `String "(* y <$x *) print op (+).";
         "session", `String "wce";
       ])
  in
  check "P1: <$ never starts a reference (sampling guard)"
    ((not err) && member "src_expanded" qg = `Null)
    (Yojson.Safe.to_string qg);
  let (err, rpd) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "c2";
         "script",
         `String "proof.\nhave H : $inv.\ntrivial.\nby trivial.\nqed.";
         "session", `String "wce";
       ])
  in
  check "P1: replace_proof lands EXPANDED text"
    ((not err) && member "ok" rpd = `Bool true)
    (Yojson.Safe.to_string rpd);
  let cert_text =
    let ic = open_in certf in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic; s
  in
  check "P1: file carries expanded EC, no $names"
    ((try
        ignore (Str.search_forward
                  (Str.regexp_string "have H : 1 = 1") cert_text 0);
        true
      with Not_found -> false)
     && not (try
               ignore (Str.search_forward
                         (Str.regexp_string "$inv") cert_text 0);
               true
             with Not_found -> false))
    cert_text;
  let (err, du) =
    call fd_in fd_out "exec"
      (`Assoc [
         "text", `String "have J : $nope.";
         "session", `String "wce";
       ])
  in
  check "P1: undefined $-reference is a hard error naming defines"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "undefined")
                     (Yojson.Safe.to_string du) 0);
           ignore (Str.search_forward
                     (Str.regexp_string "inv")
                     (Yojson.Safe.to_string du) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string du);
  let (err, dd) =
    call fd_in fd_out "define"
      (`Assoc [ "name", `String "inv"; "session", `String "wce" ])
  in
  check "P1: define {name} alone deletes the binding"
    ((not err)
     && (match member "defines" dd with `List [] -> true | _ -> false))
    (Yojson.Safe.to_string dd);
  let (err, _) =
    call fd_in fd_out "close_session"
      (`Assoc [ "session", `String "wce" ])
  in
  check "close wce" (not err) "";

  (* -- round 5 (B6): bulleted admits are debt too ------------------ *)
  let adm2 = Filename.concat fixture_dir "adm2.ec" in
  let oc = open_out adm2 in
  output_string oc
    "require import AllCore.\n\
     lemma sole : 1 = 1.\n\
     proof.\n\
     admit.\n\
     qed.\n\
     lemma seq_unbulleted : 1 = 1.\n\
     proof.\n\
     have h : 2 = 2 by trivial.\n\
     admit.\n\
     qed.\n\
     lemma bulleted : 1 = 1 /\\ 2 = 2.\n\
     proof.\n\
     split.\n\
     + admit.\n\
     + admit.\n\
     qed.\n";
  close_out oc;
  let (err, _) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String adm2; "session", `String "we";
         "nosmt", `Bool true;
       ])
  in
  check "adm2 fixture open (B6 repro)" (not err) "";
  let (err, ag2) =
    call fd_in fd_out "admitted_goals"
      (`Assoc [ "session", `String "we" ])
  in
  let ag2_s = Yojson.Safe.to_string ag2 in
  check "B6: admitted_goals counts bulleted admits (4/4, 3 lemmas)"
    ((not err)
     && member "admit_count" ag2 = `Int 4
     && (match member "lemmas_scanned" ag2 with
         | `List l -> List.length l = 3
         | _ -> false)
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "\"bulleted\"") ag2_s 0);
           ignore (Str.search_forward
                     (Str.regexp_string "2 = 2") ag2_s 0);
           true
         with Not_found -> false))
    ag2_s;
  let (err, ol2) =
    call fd_in fd_out "proof_outline"
      (`Assoc [ "lemma", `String "bulleted"; "session", `String "we" ])
  in
  let ol2_admit_paths =
    try
      match member "admitted" ol2 with
      | `List l ->
        List.filter_map
          (fun a ->
             match member "path" a with `String p -> Some p | _ -> None)
          l
      | _ -> []
    with _ -> []
  in
  check "B6: outline attributes bulleted admits to branch paths"
    ((not err) && ol2_admit_paths = [ "1"; "2" ])
    (Yojson.Safe.to_string ol2);
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "we"; "at_lemma", `String "bulleted" ])
  in
  check "we at bulleted" (not err) "";
  let (err, _) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "split."; "session", `String "we" ])
  in
  check "we split" (not err) "";
  let (err, ba) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "+ admit."; "session", `String "we" ])
  in
  check "B6: live admitted capture sees a bulleted admit"
    ((not err)
     && (match member "admitted" ba with
         | `List [ a ] ->
           (match member "goal" a with
            | `Assoc _ | `String _ -> true
            | _ -> false)
         | _ -> false))
    (Yojson.Safe.to_string ba);
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "we"; "at_lemma", `String "bulleted" ])
  in
  check "we back at bulleted" (not err) "";
  let (err, sk2) =
    call fd_in fd_out "check_skeleton"
      (`Assoc [
         "script", `String "split.\n+ admit.\n+ admit.\nqed.";
         "session", `String "we";
       ])
  in
  check "B6: check_skeleton reports bulleted holes"
    ((not err)
     && member "closes_with_holes" sk2 = `Bool true
     && (match member "holes" sk2 with
         | `List l -> List.length l = 2
         | _ -> false))
    (Yojson.Safe.to_string sk2);
  let (err, _) =
    call fd_in fd_out "close_session" (`Assoc [ "session", `String "we" ])
  in
  check "close we" (not err) "";

  (* -- round 6: document-mode bullets / transcript / define ------- *)
  let sb2 = Filename.concat fixture_dir "sb2.ec" in
  let write_sb2 () =
    let oc = open_out sb2 in
    output_string oc
      "require import AllCore.\n\
       pragma +strict_bullets.\n\
       lemma s1 : (1 = 1 /\\ 2 = 2) /\\ 3 = 3.\n\
       proof.\n\
       admit.\n\
       qed.\n";
    close_out oc
  in
  write_sb2 ();
  let (err, _) =
    call fd_in fd_out "open_file"
      (`Assoc [
         "path", `String sb2; "session", `String "wf";
         "nosmt", `Bool true;
       ])
  in
  check "sb2 fixture open (strict_bullets)" (not err) "";
  (* B7: a bullet-REUSING body must be refused by verification —
     document text is checked under the file's own rules. *)
  let (err, b7bad) =
    call fd_in fd_out "replace_proof"
      (`Assoc [
         "lemma", `String "s1";
         "script",
         `String
           "proof.\nsplit.\n+ split.\n  + trivial.\n  + trivial.\n\
            + trivial.\nqed.";
         "session", `String "wf";
       ])
  in
  check "B7: strict-bullet violation refused, file restored"
    ((not err)
     && member "ok" b7bad = `Bool false
     && member "file_restored" b7bad = `Bool true
     && (try
           ignore (Str.search_forward (Str.regexp_string "bullet")
                     (Yojson.Safe.to_string b7bad) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string b7bad);
  (* Same parity one tool earlier: check_script sees the violation. *)
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wf"; "at_lemma", `String "s1" ])
  in
  check "wf at s1" (not err) "";
  let (err, b7cs) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script",
         `String
           "split.\n+ split.\n  + trivial.\n  + trivial.\n+ trivial.";
         "session", `String "wf";
       ])
  in
  check "B7: check_script enforces the file's bullet rules"
    ((not err)
     && member "ok" b7cs = `Bool false
     && (try
           ignore (Str.search_forward (Str.regexp_string "bullet")
                     (Yojson.Safe.to_string b7cs) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string b7cs);
  let (err, b7ok) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script",
         `String
           "split.\n- split.\n  + trivial.\n  + trivial.\n- trivial.";
         "session", `String "wf";
       ])
  in
  check "B7: correctly-bulleted body closes under strict rules"
    ((not err)
     && member "ok" b7ok = `Bool true
     && member "closes" b7ok = `Bool true)
    (Yojson.Safe.to_string b7ok);
  (* B8: author bullet-free semantics through exec (typed bullets are
     ignored AND stripped from the record); COMMIT owns presentation
     and the landed body satisfies the strict file. *)
  let (err, _) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "split."; "session", `String "wf" ])
  in
  check "wf split" (not err) "";
  let (err, _) =
    call fd_in fd_out "exec"
      (`Assoc [ "text", `String "+ split."; "session", `String "wf" ])
  in
  check "wf nested split (typed bullet ignored)" (not err) "";
  let (err, _) =
    call fd_in fd_out "exec"
      (`Assoc [
         "text", `String "+ trivial.\n+ trivial.\n+ trivial.";
         "session", `String "wf";
       ])
  in
  check "wf close all three leaves" (not err) "";
  let (err, cb) =
    call fd_in fd_out "commit_proof"
      (`Assoc [ "session", `String "wf" ])
  in
  let cb_body =
    match member "proof" cb with `String s -> s | _ -> ""
  in
  check "B8: COMMIT body has single clean bullets (no '- +')"
    ((not err)
     && (try
           ignore (Str.search_forward (Str.regexp_string "- split.")
                     cb_body 0);
           true
         with Not_found -> false)
     && not (try
               ignore (Str.search_forward (Str.regexp_string "- +")
                         cb_body 0);
               true
             with Not_found -> false)
     && not (try
               ignore (Str.search_forward (Str.regexp_string "+ split.")
                         cb_body 0);
               true
             with Not_found -> false))
    cb_body;
  let (err, cw) =
    call fd_in fd_out "commit_proof"
      (`Assoc [
         "lemma", `String "s1"; "write", `Bool true;
         "session", `String "wf";
       ])
  in
  check "B8: COMMIT body lands verified on the strict file"
    ((not err)
     && member "ok" cw = `Bool true
     && member "file_written" cw = `Bool true)
    (Yojson.Safe.to_string cw);
  (* Document replay is not authoring: after a full resync the
     transcript is empty — read-only says so, write refuses. *)
  let (err, _) =
    call fd_in fd_out "resync_file" (`Assoc [ "session", `String "wf" ])
  in
  check "wf full resync" (not err) "";
  let (err, ce) =
    call fd_in fd_out "commit_proof"
      (`Assoc [ "session", `String "wf" ])
  in
  check "B8: empty transcript is explained on read"
    ((not err)
     && member "proof" ce = `String ""
     && (match member "note" ce with `String _ -> true | _ -> false))
    (Yojson.Safe.to_string ce);
  let (err, cwe) =
    call fd_in fd_out "commit_proof"
      (`Assoc [
         "lemma", `String "s1"; "write", `Bool true;
         "session", `String "wf";
       ])
  in
  check "B8: empty transcript refuses to land"
    (err
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "nothing to land")
                     (Yojson.Safe.to_string cwe) 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string cwe);
  (* B9: define expansion is code-only — $refs inside comments are
     neither expanded nor errors. *)
  let (err, _) =
    call fd_in fd_out "define"
      (`Assoc [
         "name", `String "inv2"; "text", `String "3 = 3";
         "session", `String "wf";
       ])
  in
  check "wf define inv2" (not err) "";
  let (err, _) =
    call fd_in fd_out "resync_file"
      (`Assoc [ "session", `String "wf"; "at_lemma", `String "s1" ])
  in
  check "wf back at s1" (not err) "";
  let (err, b9) =
    call fd_in fd_out "check_script"
      (`Assoc [
         "script",
         `String
           "(* about $inv2 and $undefined_xyz *)\nsplit.\n\
            - split.\n  + trivial.\n  + trivial.\n- trivial.";
         "session", `String "wf";
       ])
  in
  check "B9: $names inside comments untouched (no expansion, no error)"
    ((not err)
     && member "ok" b9 = `Bool true
     && member "src_expanded" b9 = `Null)
    (Yojson.Safe.to_string b9);
  let (err, _) =
    call fd_in fd_out "close_session" (`Assoc [ "session", `String "wf" ])
  in
  check "close wf" (not err) "";

  let (err, ex) =
    call fd_in fd_out "extract_lemma"
      (`Assoc [ "name", `String "aux_x"; "session", `String "w2" ])
  in
  let cand =
    match member "candidate" ex with `String s -> s | _ -> ""
  in
  check "extract_lemma: candidate for remaining goal 1 = 1"
    ((not err)
     && (try
           ignore (Str.search_forward
                     (Str.regexp_string "lemma aux_x") cand 0);
           ignore (Str.search_forward
                     (Str.regexp_string "1 = 1") cand 0);
           true
         with Not_found -> false))
    (Yojson.Safe.to_string ex);

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
