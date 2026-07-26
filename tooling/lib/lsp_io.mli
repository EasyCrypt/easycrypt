(** LSP framing on Eio. Reads/writes [Jsonrpc.Packet.t] over an Eio
    flow pair using the LSP `Content-Length:` header convention.

    **Option 2 commitment** (per [doc/tooling-poc-plan.md] Phase 5):
    Eio-native; the [lsp] opam package is consumed for types only
    ([Lsp.Types], [Lsp.Header], [Jsonrpc.*]). No Lwt; no
    [lwt_eio] bridge. The [Lsp.Io] functor (which is Lwt-based) is
    not used.

    **Status**: implemented (Phase 5-core / VSCode-first Stage 3).
    Uses [Lsp.Io.Make] functor instantiated with an Eio adapter.
    Read/write are blocking; the surrounding [Lsp_server]
    serializes inbound reads on a dedicated fiber and serializes
    outbound writes via a mutex / mailbox. *)

exception Framing_error of string
(** Raised on malformed Content-Length headers, missing
    Content-Length, short body reads, or JSON-RPC decode failures. *)

type t

val of_flows :
  source:[> Eio.Flow.source_ty ] Eio.Resource.t ->
  sink:[> Eio.Flow.sink_ty ] Eio.Resource.t ->
  t
(** Wrap an Eio source/sink pair (typically stdin/stdout from
    [Eio.Stdenv]) into an LSP packet codec. *)

val read : t -> Jsonrpc.Packet.t option
(** Read the next packet. Returns [None] on EOF. Raises on framing
    errors (malformed Content-Length header, truncated body). *)

val write : t -> Jsonrpc.Packet.t -> unit
(** Encode and write a packet. Flushes on each call so clients see
    notifications without buffering. Concurrent writers must
    serialize externally — this is a Phase 5 surface concern; the
    server's central event loop drives all writes. *)

val close : t -> unit
(** Idempotent; closes the underlying flows. *)
