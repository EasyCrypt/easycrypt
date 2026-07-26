(* LSP server top-level. Native Eio implementation.

   Inbound flow: read packet → dispatch by method → for requests,
   spawn a fiber under the server's switch and race the handler
   against a cancel promise from Request_registry; for
   notifications, dispatch synchronously (special-case
   $/cancelRequest to look up the request id and cancel via
   Request_registry).

   Outbound flow: serialize all writes through a write_mutex so
   handler fibers, the inbound loop, and notification senders
   don't race on the io. *)

type request_handler =
  Jsonrpc.Request.t ->
  (Yojson.Safe.t, Jsonrpc.Response.Error.t) result

type notification_handler =
  Jsonrpc.Notification.t -> unit

type t = {
  workspace : Workspace.t;
  publish   : Publish.t;
  request_registry : Request_registry.t;
  request_handlers : (string, request_handler) Hashtbl.t;
  notification_handlers : (string, notification_handler) Hashtbl.t;
  (* Serializes all outbound writes to [io]. MUST be Eio.Mutex (not
     stdlib Mutex.t): the critical section calls Eio.Flow.copy_string
     which yields to the scheduler, and Eio multiplexes fibers on a
     single OS thread, so a second fiber attempting to acquire would
     trip stdlib's same-thread deadlock detector and abort with
     Sys_error("Mutex.lock: Resource deadlock avoided"). *)
  write_mutex : Eio.Mutex.t;
  mutable shutdown_requested : bool;
}

let create ~workspace ~publish =
  { workspace;
    publish;
    request_registry = Request_registry.create ();
    request_handlers = Hashtbl.create 32;
    notification_handlers = Hashtbl.create 32;
    write_mutex = Eio.Mutex.create ();
    shutdown_requested = false;
  }

let register_request t name handler =
  Hashtbl.replace t.request_handlers name handler

let register_notification t name handler =
  Hashtbl.replace t.notification_handlers name handler

let workspace t = t.workspace
let publish t = t.publish
let request_registry t = t.request_registry

let request_shutdown t = t.shutdown_requested <- true

(* Serialize all writes. Handler fibers, the inbound loop, and
   notification senders all go through this. *)
let with_write_lock t f =
  Eio.Mutex.use_rw ~protect:false t.write_mutex f

let write_packet t io packet =
  with_write_lock t (fun () -> Lsp_io.write io packet)

let send_notification t ~io ~method_ ?params () =
  let params =
    match params with
    | None -> None
    | Some p ->
      (match p with
       | `Assoc _ | `List _ as s -> Some (s : Jsonrpc.Structured.t)
       | _ ->
         Log.warn
           "send_notification %s: params must be Assoc or List; dropping" method_;
         None)
  in
  let notif = Jsonrpc.Notification.create ?params ~method_ () in
  write_packet t io (Jsonrpc.Packet.Notification notif)

(* Method-not-found error helper. *)
let method_not_found name =
  Jsonrpc.Response.Error.make
    ~code:Jsonrpc.Response.Error.Code.MethodNotFound
    ~message:(Printf.sprintf "method not found: %s" name)
    ()

let internal_error msg =
  Jsonrpc.Response.Error.make
    ~code:Jsonrpc.Response.Error.Code.InternalError
    ~message:msg
    ()

let request_cancelled =
  Jsonrpc.Response.Error.make
    ~code:Jsonrpc.Response.Error.Code.RequestCancelled
    ~message:"request cancelled by client"
    ()

(* Handle one inbound request. Spawn a fiber so the inbound loop
   isn't blocked. The fiber races the handler against a cancel
   promise from Request_registry; if cancelled, replies with
   RequestCancelled error. *)
let handle_request t ~io ~sw (req : Jsonrpc.Request.t) =
  let corr = Correlation.of_client (Jsonrpc.Id.hash req.id |> string_of_int) in
  let cancel_p = Request_registry.register t.request_registry corr in
  Eio.Fiber.fork ~sw (fun () ->
    Fun.protect
      ~finally:(fun () -> Request_registry.unregister t.request_registry corr)
      (fun () ->
        let outcome =
          Eio.Fiber.first
            (fun () ->
              match Hashtbl.find_opt t.request_handlers req.method_ with
              | None ->
                Log.info ~corr "request %s: method not found" req.method_;
                `Reply (Jsonrpc.Response.error req.id (method_not_found req.method_))
              | Some h ->
                Log.info ~corr "request %s: dispatching" req.method_;
                let t0 = Unix.gettimeofday () in
                let outcome =
                  match
                    try Ok (h req)
                    with exn ->
                      Log.err ~corr "request %s: handler raised %s"
                        req.method_ (Printexc.to_string exn);
                      Error (internal_error (Printexc.to_string exn))
                  with
                  | Ok (Ok json) ->
                    `Reply (Jsonrpc.Response.ok req.id json)
                  | Ok (Error err) ->
                    `Reply (Jsonrpc.Response.error req.id err)
                  | Error err ->
                    `Reply (Jsonrpc.Response.error req.id err)
                in
                let elapsed_ms = (Unix.gettimeofday () -. t0) *. 1000.0 in
                Log.info ~corr "request %s: completed in %.0fms"
                  req.method_ elapsed_ms;
                outcome)
            (fun () ->
              Eio.Promise.await cancel_p;
              Log.info ~corr "request %s: cancelled" req.method_;
              `Reply (Jsonrpc.Response.error req.id request_cancelled))
        in
        match outcome with
        | `Reply resp -> write_packet t io (Jsonrpc.Packet.Response resp)))

(* Built-in handler for $/cancelRequest. Looks up the request id in
   Request_registry and cancels its fiber. *)
let handle_cancel_request t (params : Jsonrpc.Structured.t option) =
  match params with
  | Some (`Assoc kvs) ->
    (match List.assoc_opt "id" kvs with
     | Some json ->
       (* JSON-RPC id is either string or int; both hash. *)
       let id_hash =
         match json with
         | `Int i -> i
         | `String _ -> Jsonrpc.Id.hash (`String (Yojson.Safe.to_string json))
         | _ ->
           Log.warn "$/cancelRequest: malformed id %s"
             (Yojson.Safe.to_string json);
           0
       in
       let corr = Correlation.of_client (string_of_int id_hash) in
       Request_registry.cancel t.request_registry corr
     | None ->
       Log.warn "$/cancelRequest: missing id in params")
  | _ ->
    Log.warn "$/cancelRequest: missing or non-object params"

let handle_notification t (notif : Jsonrpc.Notification.t) =
  Log.info "notification %s" notif.method_;
  match notif.method_ with
  | "$/cancelRequest" -> handle_cancel_request t notif.params
  | "exit" ->
    Log.info "exit notification received; flagging shutdown";
    request_shutdown t
  | name ->
    (match Hashtbl.find_opt t.notification_handlers name with
     | None -> Log.info "notification %s: no handler registered" name
     | Some h ->
       try h notif
       with exn ->
         Log.err "notification %s: handler raised %s"
           name (Printexc.to_string exn))

let run t ~io ~sw =
  Log.info "Lsp_server.run: starting inbound loop";
  let rec loop () =
    if t.shutdown_requested then begin
      Log.info "Lsp_server.run: shutdown requested; stopping";
      ()
    end
    else begin
      match
        try Lsp_io.read io
        with Lsp_io.Framing_error msg ->
          Log.err "Lsp_server.run: framing error: %s; aborting" msg;
          None
      with
      | None ->
        Log.info "Lsp_server.run: io EOF; stopping";
        ()
      | Some (Jsonrpc.Packet.Request req) ->
        handle_request t ~io ~sw req;
        loop ()
      | Some (Jsonrpc.Packet.Notification notif) ->
        handle_notification t notif;
        loop ()
      | Some (Jsonrpc.Packet.Response _) ->
        Log.warn "Lsp_server.run: ignoring inbound Response packet";
        loop ()
      | Some (Jsonrpc.Packet.Batch_response _ | Jsonrpc.Packet.Batch_call _) ->
        Log.warn "Lsp_server.run: batch packets not supported";
        loop ()
    end
  in
  loop ();
  Log.info "Lsp_server.run: cancelling in-flight requests";
  Request_registry.cancel_all t.request_registry;
  Lsp_io.close io;
  Log.info "Lsp_server.run: exited"
