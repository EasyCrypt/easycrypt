(** Native Eio LSP framing smoke. Round-trips JSON-RPC packets
    through Lsp_io's read+write to verify Content-Length parsing,
    body extraction, and JSON encoding/decoding are byte-correct.

    Uses Eio in-memory pipes (Eio_unix.Net) — no real socket
    needed. *)

open Ecd_core

let pass = ref 0
let fail = ref 0
let check label cond detail =
  if cond then begin incr pass; Printf.printf "  ok  %s\n%!" label end
  else begin incr fail; Printf.printf "  FAIL %s — %s\n%!" label detail end

(* Build a packet from raw bytes using a Buf_read backed by a
   Cstruct or string. We write the bytes to a flow-pair via
   Eio.Flow.string_source / sink-buffer. *)

let read_packet_from_string s : Jsonrpc.Packet.t option =
  Eio_main.run @@ fun env ->
  let _ = env in
  let source = Eio.Flow.string_source s in
  let sink_buf = Buffer.create 64 in
  let sink = Eio.Flow.buffer_sink sink_buf in
  let io = Lsp_io.of_flows ~source ~sink in
  Lsp_io.read io

let bytes_of_write packet : string =
  Eio_main.run @@ fun env ->
  let _ = env in
  let source = Eio.Flow.string_source "" in
  let sink_buf = Buffer.create 256 in
  let sink = Eio.Flow.buffer_sink sink_buf in
  let io = Lsp_io.of_flows ~source ~sink in
  Lsp_io.write io packet;
  Buffer.contents sink_buf

let roundtrip packet =
  let encoded = bytes_of_write packet in
  read_packet_from_string encoded

let () =
  Printf.printf "== Lsp_io framing smoke ==\n%!";

  (* Case 1 — single notification. *)
  let notif = Jsonrpc.Notification.create
                ~method_:"foo"
                ~params:(`Assoc [ "x", `Int 42 ])
                ()
  in
  let packet1 = Jsonrpc.Packet.Notification notif in
  let encoded1 = bytes_of_write packet1 in
  check "case 1 — encoded starts with Content-Length:"
    (String.length encoded1 > 16
     && String.sub encoded1 0 15 = "Content-Length:")
    (Printf.sprintf "got %S" (String.sub encoded1 0 (min 30 (String.length encoded1))));
  check "case 1 — encoded contains CRLF CRLF separator"
    (try
       let i = String.index encoded1 '\r' in
       let s = String.sub encoded1 i 4 in
       s = "\r\n\r\n"
     with _ -> false)
    "no CRLF CRLF found";

  (match roundtrip packet1 with
   | None -> check "case 1 — roundtrip decodes" false "got None"
   | Some (Jsonrpc.Packet.Notification n) ->
     check "case 1 — roundtrip decodes as Notification" true "";
     check "case 1 — method preserved" (n.method_ = "foo")
       (Printf.sprintf "got %S" n.method_);
     check "case 1 — params preserved"
       (match n.params with
        | Some (`Assoc [ "x", `Int 42 ]) -> true
        | _ -> false)
       "params didn't roundtrip"
   | Some _ ->
     check "case 1 — roundtrip decodes as Notification" false
       "decoded but as non-Notification");

  (* Case 2 — request with id + method + params. *)
  let req = Jsonrpc.Request.create
              ~id:(`Int 7)
              ~method_:"easycrypt/proof/goals"
              ~params:(`Assoc [ "uri", `String "file:///x.ec";
                                "sentence_id", `String "abc" ])
              ()
  in
  let packet2 = Jsonrpc.Packet.Request req in
  (match roundtrip packet2 with
   | Some (Jsonrpc.Packet.Request r) ->
     check "case 2 — request roundtrip method" (r.method_ = "easycrypt/proof/goals") "";
     check "case 2 — request roundtrip id" (r.id = `Int 7) "";
     check "case 2 — request roundtrip params"
       (match r.params with
        | Some (`Assoc kvs) -> List.assoc_opt "uri" kvs = Some (`String "file:///x.ec")
        | _ -> false)
       ""
   | _ -> check "case 2 — request roundtrips" false "");

  (* Case 3 — response with result. *)
  let resp = Jsonrpc.Response.ok (`Int 7) (`Assoc [ "ok", `Bool true ]) in
  let packet3 = Jsonrpc.Packet.Response resp in
  (match roundtrip packet3 with
   | Some (Jsonrpc.Packet.Response r) ->
     check "case 3 — response roundtrip id" (r.id = `Int 7) "";
     check "case 3 — response roundtrip is Ok"
       (match r.result with Ok _ -> true | Error _ -> false) ""
   | _ -> check "case 3 — response roundtrips" false "");

  (* Case 4 — back-to-back packets in the same stream. *)
  let two_encoded = bytes_of_write packet1 ^ bytes_of_write packet2 in
  Eio_main.run (fun _ ->
    let source = Eio.Flow.string_source two_encoded in
    let sink_buf = Buffer.create 64 in
    let sink = Eio.Flow.buffer_sink sink_buf in
    let io = Lsp_io.of_flows ~source ~sink in
    let p1 = Lsp_io.read io in
    let p2 = Lsp_io.read io in
    let p3 = Lsp_io.read io in
    check "case 4 — first packet decoded" (p1 <> None) "got None";
    check "case 4 — second packet decoded" (p2 <> None) "got None";
    check "case 4 — EOF after two packets" (p3 = None)
      "expected None, got Some");

  (* Case 5 — malformed Content-Length raises Framing_error. *)
  let bad = "Content-Length: oops\r\n\r\n{}" in
  (try
     let _ = read_packet_from_string bad in
     check "case 5 — bad Content-Length raises" false
       "no exception raised"
   with
   | Lsp_io.Framing_error _ ->
     check "case 5 — bad Content-Length raises Framing_error" true ""
   | other ->
     check "case 5 — raises Framing_error specifically" false
       (Printexc.to_string other));

  (* Case 6 — missing Content-Length header. *)
  let bad2 = "X-Foo: bar\r\n\r\n{}" in
  (try
     let _ = read_packet_from_string bad2 in
     check "case 6 — missing Content-Length raises" false
       "no exception raised"
   with
   | Lsp_io.Framing_error _ ->
     check "case 6 — missing Content-Length raises Framing_error" true ""
   | other ->
     check "case 6 — raises Framing_error specifically" false
       (Printexc.to_string other));

  (* Case 7 — concurrent writes to a single Lsp_server.t must not
     deadlock. Regression for stdlib-Mutex misuse: stdlib Mutex.t
     trips its same-OS-thread re-lock detector (Sys_error
     "Mutex.lock: Resource deadlock avoided") when a fiber yields
     inside the critical section and a second fiber on the same OS
     thread (Eio multiplexes fibers on one thread) attempts to
     acquire. Eio.Mutex is fiber-aware and serializes.

     The bug requires copy_string to yield WHILE the mutex is
     held. A plain buffer_sink doesn't yield (in-memory write), so
     we wrap it in a yielding adapter that forces an
     Eio.Fiber.yield per single_write — emulates the real-world
     case of an LSP write to a kernel pipe that yields under
     contention. *)
  let module Yielding_sink = struct
    type t = Buffer.t
    let single_write t bufs =
      (* Force a yield BEFORE the actual write so any other fiber
         queued on the lock has a chance to run while we're still
         inside our with_write_lock critical section. *)
      Eio.Fiber.yield ();
      let total =
        List.fold_left (fun acc cs ->
          Buffer.add_string t (Cstruct.to_string cs);
          acc + Cstruct.length cs) 0 bufs
      in
      total
    let copy t ~src = Eio.Flow.Pi.simple_copy ~single_write t ~src
  end in
  let yielding_sink_ops = Eio.Flow.Pi.sink (module Yielding_sink) in
  let make_yielding_sink () =
    let buf = Buffer.create 4096 in
    buf, Eio.Resource.T (buf, yielding_sink_ops)
  in
  Eio_main.run (fun env ->
    let _ = env in
    Eio.Switch.run @@ fun sw ->
    let workspace = Workspace.make ~load_path:[] in
    let publish, _ps = Stub_publish.make () in
    let server = Lsp_server.create ~workspace ~publish in
    let sink_buf, sink = make_yielding_sink () in
    let source = Eio.Flow.string_source "" in
    let io = Lsp_io.of_flows ~source ~sink in
    let n_writers = 16 in
    let crashed = ref None in
    let promises = List.init n_writers (fun i ->
      Eio.Fiber.fork_promise ~sw (fun () ->
        try
          Lsp_server.send_notification server ~io
            ~method_:"test/notif"
            ~params:(`Assoc [ "i", `Int i ]) ()
        with exn ->
          (match !crashed with
           | None -> crashed := Some (Printexc.to_string exn)
           | Some _ -> ())))
    in
    List.iter (fun p ->
      try Eio.Promise.await_exn p
      with exn ->
        (match !crashed with
         | None -> crashed := Some (Printexc.to_string exn)
         | Some _ -> ()))
      promises;
    check "case 7 — concurrent writers do not deadlock"
      (!crashed = None)
      (Option.value !crashed ~default:"");
    let count_substring s sub =
      let len = String.length sub in
      let n = String.length s in
      let rec scan i acc =
        if i + len > n then acc
        else if String.sub s i len = sub then scan (i + 1) (acc + 1)
        else scan (i + 1) acc
      in
      scan 0 0
    in
    let cl_count =
      count_substring (Buffer.contents sink_buf) "Content-Length:"
    in
    check "case 7 — all concurrent writes hit the sink"
      (cl_count = n_writers)
      (Printf.sprintf "expected %d Content-Length headers, got %d"
         n_writers cl_count));

  Printf.printf "\n== Lsp_io smoke ==\n";
  Printf.printf "  pass=%d  fail=%d\n%!" !pass !fail;
  exit (if !fail = 0 then 0 else 1)
