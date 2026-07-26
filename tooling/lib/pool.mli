(** Session pool. Owns live [SESSION_BACKEND] instances, enforces per-kind
    fairness, and returns them to the pool on release (or discards them
    if dirty). PoC layout: 1 primary per document + K scratch, bounded +
    LRU, with [K_lsp], [K_mcp], [K_spec] reserved slots. See plan §
    "Speculative state" and § "Fairness". *)

module Make (B : Session.BACKEND) : sig
  type t

  type kind = [ `Lsp | `Mcp | `Spec ]

  type config = {
    pool_size : int;
    k_lsp : int;
    k_mcp : int;
    k_spec : int; (** always 0 in PoC; reserved for v1 speculative
                     background compilation *)
  }

  val make : sw:Eio.Switch.t -> config -> t

  val acquire_scratch :
    t -> kind:kind -> corr:Correlation.t -> (B.t, Error.t) result
  (** Acquire a scratch session for the given requester kind. Fails with
      [Pool_exhausted] if the kind's reservation is saturated. *)

  val release : t -> B.t -> unit

  val close_all : t -> unit
end
