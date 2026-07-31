(** SESSION_BACKEND module type: how the daemon talks to an `ec llm`
    subprocess (or, later, an in-process kernel backend). One impl in
    PoC: subprocess-over-ec-llm. See [doc/tooling-protocol.md] § 2.1. *)

(** Per-exec outcome: the new sentence id assigned by the backend, plus
    the replied uuid for invariant checking, plus any notices emitted.
    [restarted] is [true] when the reply carried a `[restarted]` event
    tag (addition 4) — the session was reset mid-exec, so the caller
    must invalidate its sentence→uuid map and any overlay/scratch
    state keyed off this session. Distinct from the [Error.t]
    [Session_restarted] variant, which is reserved for *forced*
    restarts that also invalidate the exec (e.g. uuid-invariant
    violation, subprocess EOF). *)
type exec_ok = {
  sentence_id : Sentence_id.t;
  replied_uuid : int;
  notices : string list;
  restarted : bool;
  output : string;
  (** Reply body from EC (everything after the `OK [uuid:…]` header,
      excluding `NOTICE:`/`ERROR-JSON:` lines and the trailing
      `<END>`). Non-empty for directive/query forms like `print`,
      `search`, `locate` where EC's response carries content; empty
      for state-advancing sentences whose only signal is the uuid. *)
  smt_calls : int;
  (** SMT solver invocations this sentence triggered — RUNTIME
      truth, counted at EC's prover choke point and reported as a
      per-phrase delta. Catches `by smt` closers, the `/#` view,
      tacticals, and any future surface form by construction;
      0 for backends without the telemetry. *)
}

module type BACKEND = sig
  type t
  (** A live backend session. *)

  val start : sw:Eio.Switch.t -> label:string -> t
  (** Start a new session. The switch bounds its lifetime. *)

  val exec :
    t ->
    corr:Correlation.t ->
    sentence_class:[ `Executable | `Doc_comment | `Directive ] ->
    source:string ->
    (exec_ok, Error.t) result
  (** Feed a single sentence. Half-duplex: the caller fiber must not
      issue another [exec] until this returns. *)

  val revert_to : t -> Sentence_id.t -> (unit, Error.t) result
  (** Revert to the state the primary was in after executing the given
      sentence. *)

  val goals : t -> (string, Error.t) result
  (** Current goals as a string (PoC: falls back to pretty-printed text
      if EC addition (3) hasn't landed; else structured JSON). *)

  val cancel : t -> corr:Correlation.t -> unit
  (** Cancel an in-flight exec. Realised as SIGKILL + Cancel.cancel on
      the session's switch (see plan § Correlation, cancellation, CAS). *)

  val close : t -> unit
end
