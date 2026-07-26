(** Surface-plugin module types. [LSP_FEATURE] and [MCP_TOOL] are
    registered at daemon startup; the core dispatches through them only.
    Stateless — any session-adjacent state lives in the pool or overlay
    stack, reached via [Surface_ctx]. See plan § "Extension points". *)

module Make (B : Session.BACKEND) : sig
  module Ctx : module type of Surface_ctx.Make (B)

  module type LSP_FEATURE = sig
    val method_ : string
    (** LSP method name, e.g. ["proof/execToPoint"]. *)

    val handle : Ctx.t -> Yojson.Safe.t -> (Yojson.Safe.t, Error.t) result
    (** Handler: receives the LSP request params, returns the response
        result or a typed error. *)
  end

  module type MCP_TOOL = sig
    val name : string
    (** MCP tool name, e.g. ["get_goals"]. *)

    val schema : Yojson.Safe.t
    (** JSON Schema for the tool inputs; returned to MCP clients via
        [tools/list]. *)

    val invoke : Ctx.t -> Yojson.Safe.t -> (Yojson.Safe.t, Error.t) result
  end
end
