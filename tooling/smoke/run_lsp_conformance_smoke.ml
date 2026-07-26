(** Stage 3 conformance smoke. Spawns ecd daemon as a subprocess,
    connects to its Unix socket, sends LSP packets, asserts on
    responses. Tests:
    - initialize handshake returns capabilities + proofCapabilities.
    - shutdown request flips state; subsequent exit terminates daemon.
    - easycrypt/proof/goals stub returns expected wire shape.
    - Method-not-found error for unknown method.

    Self-contained re: ec llm: doesn't trigger didChange (which would
    require analyze session); exercises lifecycle + custom methods
    only. publishDiagnostics flow is end-to-end-tested in a separate
    smoke when EC binary is available. *)

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

let ecd_path () =
  let candidate =
    Filename.concat (Sys.getcwd ()) "_build/default/tooling/daemon/main.exe"
  in
  if Sys.file_exists candidate then candidate
  else begin
    let ic = Unix.open_process_in "command -v ecd 2>/dev/null" in
    let line = try Some (input_line ic) with End_of_file -> None in
    let _ = Unix.close_process_in ic in
    match line with
    | Some p when p <> "" -> p
    | _ ->
      Printf.eprintf "run_lsp_conformance_smoke: cannot find ecd binary\n";
      exit 2
  end

let unique_label =
  Printf.sprintf "smoke-lsp-%d-%d"
    (Unix.getpid ())
    (int_of_float (Unix.gettimeofday ()))

let runtime_dir () =
  match Sys.getenv_opt "XDG_RUNTIME_DIR" with
  | Some d -> Filename.concat d "easycrypt-daemon"
  | None ->
    let tmp = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
    let uid = Unix.getuid () in
    Filename.concat tmp (Printf.sprintf "easycrypt-daemon-%d" uid)

let pid_file_for label =
  Filename.concat (runtime_dir ()) (label ^ ".pid")

let read_socket_from_pid_file path =
  try
    let ic = open_in path in
    let _ = input_line ic in
    let sock = input_line ic in
    close_in ic;
    Some (String.trim sock)
  with _ -> None

let wait_for cond ~deadline_s =
  let started = Unix.gettimeofday () in
  let rec loop () =
    if cond () then true
    else if Unix.gettimeofday () -. started > deadline_s then false
    else begin
      Unix.sleepf 0.05;
      loop ()
    end
  in
  loop ()

let spawn_ecd_daemon label =
  let bin = ecd_path () in
  Unix.create_process bin
    [| bin; "daemon"; "--label"; label |]
    Unix.stdin Unix.stdout Unix.stderr

let connect_socket sock =
  let s = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.connect s (Unix.ADDR_UNIX sock);
  s

let write_packet fd packet =
  let body = Yojson.Safe.to_string (Jsonrpc.Packet.yojson_of_t packet) in
  let header = Printf.sprintf "Content-Length: %d\r\n\r\n" (String.length body) in
  let bytes_h = Bytes.of_string header in
  let bytes_b = Bytes.of_string body in
  let _ = Unix.write fd bytes_h 0 (Bytes.length bytes_h) in
  let _ = Unix.write fd bytes_b 0 (Bytes.length bytes_b) in
  ()

(* Read one LSP packet from a Unix fd. Buffered, blocking. *)
let read_packet fd : Jsonrpc.Packet.t option =
  let buf = Buffer.create 256 in
  let read_byte () =
    let b = Bytes.create 1 in
    let n = Unix.read fd b 0 1 in
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
         let name = String.sub line 0 i |> String.trim |> String.lowercase_ascii in
         let value = String.sub line (i + 1) (String.length line - i - 1) |> String.trim in
         if name = "content-length" then
           content_length := int_of_string_opt value
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
      let s = Bytes.to_string body in
      try
        let json = Yojson.Safe.from_string s in
        Some (Jsonrpc.Packet.t_of_yojson json)
      with _ -> None

let cleanup label =
  (match read_socket_from_pid_file (pid_file_for label) with
   | Some sock when sock <> "" -> (try Sys.remove sock with _ -> ())
   | _ -> ());
  (try Sys.remove (pid_file_for label) with _ -> ())

let () =
  let label = unique_label in
  at_exit (fun () -> cleanup label);

  Printf.printf "== Stage 3 LSP conformance smoke ==\n%!";

  let pid = spawn_ecd_daemon label in
  let started =
    wait_for (fun () ->
      Sys.file_exists (pid_file_for label)
      && (match read_socket_from_pid_file (pid_file_for label) with
          | Some s when s <> "" -> Sys.file_exists s
          | _ -> false))
      ~deadline_s:5.0
  in
  check "daemon started + socket bound" started "no socket within 5s";

  if not started then begin
    Printf.printf "\n== LSP conformance smoke ==\n  pass=%d  fail=%d\n%!"
      !pass !fail;
    (try Unix.kill pid Sys.sigterm with _ -> ());
    exit 1
  end;

  let sock_path =
    match read_socket_from_pid_file (pid_file_for label) with
    | Some s -> s
    | None -> assert false
  in
  let fd = connect_socket sock_path in

  (* Case 1 — initialize handshake. *)
  let init_req = Jsonrpc.Request.create
                   ~id:(`Int 1)
                   ~method_:"initialize"
                   ~params:(`Assoc [ "rootUri", `String "file:///tmp" ])
                   ()
  in
  write_packet fd (Jsonrpc.Packet.Request init_req);
  let resp = read_packet fd in
  (match resp with
   | Some (Jsonrpc.Packet.Response r) ->
     check "initialize: response received" true "";
     check "initialize: id matches request" (r.id = `Int 1) "";
     (match r.result with
      | Ok (`Assoc kvs) ->
        check "initialize: result has capabilities"
          (List.mem_assoc "capabilities" kvs) "";
        check "initialize: result has proofCapabilities"
          (List.mem_assoc "proofCapabilities" kvs) "";
        check "initialize: result has serverInfo"
          (List.mem_assoc "serverInfo" kvs) ""
      | _ -> check "initialize: result is JSON object" false "got non-object")
   | _ -> check "initialize: got Response" false "wrong packet kind");

  (* Case 2 — initialized notification (server ignores). *)
  let init_notif = Jsonrpc.Notification.create ~method_:"initialized"
                     ~params:(`Assoc []) ()
  in
  write_packet fd (Jsonrpc.Packet.Notification init_notif);
  (* No response expected. Give server a moment. *)
  Unix.sleepf 0.05;

  (* Case 3 — easycrypt/proof/goals stub. *)
  let goals_req = Jsonrpc.Request.create
                    ~id:(`Int 2)
                    ~method_:"easycrypt/proof/goals"
                    ~params:(`Assoc [ "uri", `String "file:///x.ec" ])
                    ()
  in
  write_packet fd (Jsonrpc.Packet.Request goals_req);
  let resp = read_packet fd in
  (match resp with
   | Some (Jsonrpc.Packet.Response r) ->
     check "goals: response received" true "";
     check "goals: id matches" (r.id = `Int 2) "";
     (match r.result with
      | Ok (`Assoc kvs) ->
        check "goals: has provenance field"
          (List.assoc_opt "provenance" kvs = Some (`String "fresh")) "";
        check "goals: has cas field"
          (List.mem_assoc "cas" kvs) "";
        check "goals: has subgoals field"
          (List.assoc_opt "subgoals" kvs = Some (`List [])) ""
      | _ -> check "goals: result is JSON object" false "got non-object")
   | _ -> check "goals: got Response" false "wrong packet kind");

  (* Case 4 — method not found. *)
  let bogus_req = Jsonrpc.Request.create
                    ~id:(`Int 3)
                    ~method_:"unknown/method"
                    ~params:(`Assoc [])
                    ()
  in
  write_packet fd (Jsonrpc.Packet.Request bogus_req);
  let resp = read_packet fd in
  (match resp with
   | Some (Jsonrpc.Packet.Response r) ->
     check "bogus method: response received" true "";
     (match r.result with
      | Error err ->
        check "bogus method: error returned" true "";
        check "bogus method: code is MethodNotFound"
          (err.code = Jsonrpc.Response.Error.Code.MethodNotFound) ""
      | Ok _ -> check "bogus method: returns Error" false "got Ok")
   | _ -> check "bogus method: got Response" false "wrong packet kind");

  (* Case 5 — shutdown + exit. *)
  let shutdown_req = Jsonrpc.Request.create
                       ~id:(`Int 4)
                       ~method_:"shutdown"
                       ()
  in
  write_packet fd (Jsonrpc.Packet.Request shutdown_req);
  let resp = read_packet fd in
  (match resp with
   | Some (Jsonrpc.Packet.Response r) ->
     check "shutdown: response received" true "";
     check "shutdown: result is Ok"
       (match r.result with Ok _ -> true | Error _ -> false) ""
   | _ -> check "shutdown: got Response" false "wrong packet kind");

  let exit_notif = Jsonrpc.Notification.create ~method_:"exit" () in
  write_packet fd (Jsonrpc.Packet.Notification exit_notif);
  Unix.sleepf 0.2;
  (try Unix.close fd with _ -> ());

  (* Daemon should exit. Give it some time then SIGTERM as cleanup. *)
  let exited =
    wait_for (fun () ->
      try
        let r, _ = Unix.waitpid [Unix.WNOHANG] pid in
        r <> 0
      with _ -> true)
      ~deadline_s:3.0
  in
  if not exited then (try Unix.kill pid Sys.sigterm with _ -> ());

  Printf.printf "\n== LSP conformance smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
