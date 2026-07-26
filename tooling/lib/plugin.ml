module Make (B : Session.BACKEND) = struct
  module Ctx = Surface_ctx.Make (B)

  module type LSP_FEATURE = sig
    val method_ : string
    val handle : Ctx.t -> Yojson.Safe.t -> (Yojson.Safe.t, Error.t) result
  end

  module type MCP_TOOL = sig
    val name : string
    val schema : Yojson.Safe.t
    val invoke : Ctx.t -> Yojson.Safe.t -> (Yojson.Safe.t, Error.t) result
  end
end
