(** Single internal publish point for state-change notifications.
    PoC: single-client-per-surface. The publish point is the v1
    multi-client extension seam. See [doc/tooling-protocol.md] § 12. *)

type event =
  | State_changed of {
      document_uri : string;
      cas : string;
      current_sentence : Sentence_id.t;
      seq : int;
      origin_correlation : Correlation.t option;
    }
  | Server_restarted of {
      document_uri : string;
      new_cas : string;
      reason : string;
      seq : int;
    }
  | Session_crashed of {
      label : string;
      exit_kind : string;
      (** ["exit:N"] for non-zero exit, ["signal:N"] for signal-terminated.
          Stringly-typed so the protocol-doc enumeration stays open-ended. *)
      seq : int;
    }
  (** Published by the per-session supervisor fiber when an [ec llm]
      subprocess exits unexpectedly (not via [Ec_llm_session.close] or
      [cancel]). Lets the pool replace the slot and lets surfaces emit
      [server/restarted] without waiting for the next caller's [exec]
      to discover the dead pipe. *)

type snapshot = {
  cas : string;
  current_sentence : Sentence_id.t option;
  overlay_stack : string list;
}

(** Publish-point interface values. Consumers call [t.publish],
    [t.snapshot], [t.subscribe]. Exactly one internal publish
    implementation is expected to exist at daemon startup; it is shared
    by every surface plugin via [Surface_ctx]. *)
type t = {
  publish : event -> unit;
  snapshot : unit -> snapshot;
  subscribe : (event -> unit) -> unit;
}

(** Module-type view for implementers that carry their own state. *)
module type POINT = sig
  type state
  val publish : state -> event -> unit
  val snapshot : state -> snapshot
  val subscribe : state -> (event -> unit) -> unit
end

val of_impl : (module POINT with type state = 'a) -> 'a -> t
(** Pack a [POINT] module together with its state into a publish-point
    interface value. *)
