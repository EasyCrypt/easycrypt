(** Request context passed to every surface-plugin handler
    ([LSP_FEATURE], [MCP_TOOL]). *)

module Make (B : Session.BACKEND) : sig
  module P : module type of Pool.Make (B)

  type t = {
    correlation : Correlation.t;
    switch : Eio.Switch.t;
      (** The handler's structured-concurrency switch. Failing the switch
          propagates cancellation to any fibers forked for this request. *)
    deadline : float option;
    pool : P.t;
    publish : Publish.t;
  }
end
