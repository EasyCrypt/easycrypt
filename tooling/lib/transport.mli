(** Abstract byte-stream transport for LSP / MCP. PoC ships stdio only;
    TCP/socket/WASM are drop-in later without registry changes. *)

module type TRANSPORT = sig
  type t

  val read_message : t -> string
  (** Read one framed message as a string payload. Blocks. *)

  val write_message : t -> string -> unit

  val close : t -> unit
end
