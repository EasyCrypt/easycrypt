(** LSP server top-level. Owns the inbound packet loop, dispatches
    each request/notification through a registry, writes responses
    back via [Lsp_io].

    **Lifecycle**: blocks until [exit] notification or io EOF.
    **Concurrency**: per-request handlers run in fibers under the
    server's switch; cancellation propagates via [Request_registry].
    Outbound writes are serialized via internal mutex.
    **Status**: implemented (Phase 5-core / VSCode-first Stage 3). *)

type t

(** Handler signatures. Methods with id are requests (must reply);
    notifications (no id) return unit. *)

type request_handler =
  Jsonrpc.Request.t ->
  (Yojson.Safe.t, Jsonrpc.Response.Error.t) result

type notification_handler =
  Jsonrpc.Notification.t -> unit

val create :
  workspace:Workspace.t ->
  publish:Publish.t ->
  t

(** {2 Method registration} *)

val register_request : t -> string -> request_handler -> unit
(** Register a request handler for [method_]. Replaces any prior
    registration. *)

val register_notification : t -> string -> notification_handler -> unit
(** Register a notification handler for [method_]. *)

(** {2 Lifecycle} *)

val run :
  t ->
  io:Lsp_io.t ->
  sw:Eio.Switch.t ->
  unit
(** Blocking loop. Reads packets via [io], dispatches via the
    registry, writes responses back. Returns on graceful shutdown
    (LSP [exit] notification) or io EOF. The switch bounds the
    lifetime of per-request fibers; closing it cancels in-flight
    work. *)

val request_shutdown : t -> unit
(** Trigger graceful shutdown from inside a handler (e.g. on a
    [shutdown] request). The next [exit] notification finalizes. *)

(** {2 Accessors for handlers} *)

val workspace : t -> Workspace.t
val publish : t -> Publish.t
val request_registry : t -> Request_registry.t

(** {2 Outbound notification helpers} *)

val send_notification :
  t ->
  io:Lsp_io.t ->
  method_:string ->
  ?params:Yojson.Safe.t ->
  unit ->
  unit
(** Send a server-initiated notification (e.g.,
    `textDocument/publishDiagnostics`,
    `easycrypt/proof/stateChanged`). Thread-safe. *)
