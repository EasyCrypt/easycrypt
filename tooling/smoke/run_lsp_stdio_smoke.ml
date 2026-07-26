(** Stage 4 (VSCode-first) smoke: drive `ecd daemon --stdio` end-to-end
    with a scripted LSP client over the daemon's stdin/stdout.

    Mirrors run_lsp_conformance_smoke (socket mode) but exercises the
    stdio transport path used by editor extensions like the
    vscode-languageclient port under [vscode/]. *)

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

(* Locate the ecd binary (built with dune; the (deps (alias_rec
   ../daemon/all)) clause ensures it's in _build by the time this
   smoke runs). *)
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

(* Spawn the daemon with --stdio; return (pid, stdin_fd, stdout_fd,
   stderr_fd). *)
let spawn_stdio_daemon () =
  let bin = ecd_bin () in
  let stdin_r,  stdin_w  = Unix.pipe () in
  let stdout_r, stdout_w = Unix.pipe () in
  let stderr_r, stderr_w = Unix.pipe () in
  let pid =
    Unix.create_process bin
      [| bin; "daemon"; "--stdio" |]
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
         let name =
           String.sub line 0 i |> String.trim |> String.lowercase_ascii
         in
         let value =
           String.sub line (i + 1) (String.length line - i - 1) |> String.trim
         in
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
      try Some (Jsonrpc.Packet.t_of_yojson
                  (Yojson.Safe.from_string (Bytes.to_string body)))
      with _ -> None

let () =
  Printf.printf "== Stage 4 LSP stdio smoke ==\n%!";

  let pid, fd_in, fd_out, fd_err = spawn_stdio_daemon () in

  (* initialize *)
  let init_req = Jsonrpc.Request.create
                   ~id:(`Int 1)
                   ~method_:"initialize"
                   ~params:(`Assoc [
                     "processId", `Null;
                     "rootUri", `Null;
                     "capabilities", `Assoc [];
                   ])
                   ()
  in
  write_packet fd_in (Jsonrpc.Packet.Request init_req);
  (match read_packet fd_out with
   | Some (Jsonrpc.Packet.Response r) ->
     check "initialize: response received" true "";
     check "initialize: id matches" (r.id = `Int 1) "";
     (match r.result with
      | Ok (`Assoc kvs) ->
        check "initialize: result has capabilities"
          (List.mem_assoc "capabilities" kvs) "";
        check "initialize: result has proofCapabilities"
          (List.mem_assoc "proofCapabilities" kvs) ""
      | _ -> check "initialize: result is Assoc" false "wrong result shape")
   | _ -> check "initialize: got Response" false "wrong packet kind");

  (* initialized *)
  let init_notif = Jsonrpc.Notification.create
                     ~method_:"initialized"
                     ~params:(`Assoc [])
                     ()
  in
  write_packet fd_in (Jsonrpc.Packet.Notification init_notif);

  (* easycrypt/proof/goals (stub) *)
  let goals_req = Jsonrpc.Request.create
                    ~id:(`Int 2)
                    ~method_:"easycrypt/proof/goals"
                    ~params:(`Assoc [
                      "uri", `String "file:///stdio-smoke.ec";
                    ])
                    ()
  in
  write_packet fd_in (Jsonrpc.Packet.Request goals_req);
  (match read_packet fd_out with
   | Some (Jsonrpc.Packet.Response r) ->
     check "goals: response received" true "";
     (match r.result with
      | Ok (`Assoc kvs) ->
        check "goals: has provenance" (List.mem_assoc "provenance" kvs) "";
        check "goals: has cas"        (List.mem_assoc "cas" kvs) ""
      | _ -> check "goals: result Assoc" false "wrong result shape")
   | _ -> check "goals: got Response" false "wrong packet kind");

  (* shutdown — must reply OK and NOT close before reply *)
  let shutdown_req = Jsonrpc.Request.create
                       ~id:(`Int 3)
                       ~method_:"shutdown"
                       ()
  in
  write_packet fd_in (Jsonrpc.Packet.Request shutdown_req);
  (match read_packet fd_out with
   | Some (Jsonrpc.Packet.Response r) ->
     check "shutdown: response received" true "";
     check "shutdown: result is Ok"
       (match r.result with Ok _ -> true | Error _ -> false) ""
   | _ -> check "shutdown: got Response" false "wrong packet kind");

  (* exit — daemon should exit cleanly within a few seconds *)
  let exit_notif = Jsonrpc.Notification.create ~method_:"exit" () in
  write_packet fd_in (Jsonrpc.Packet.Notification exit_notif);
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
   | Some (Unix.WEXITED 0) ->
     check "exit: daemon exited cleanly with code 0" true ""
   | Some (Unix.WEXITED n) ->
     check "exit: daemon exited 0" false (Printf.sprintf "exit code %d" n)
   | Some _ ->
     check "exit: daemon exited cleanly" false "killed by signal"
   | None ->
     (try Unix.kill pid Sys.sigterm with _ -> ());
     check "exit: daemon exited within 5s" false "timeout");

  (try Unix.close fd_out with _ -> ());
  (try Unix.close fd_err with _ -> ());

  Printf.printf "\n== LSP stdio smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
