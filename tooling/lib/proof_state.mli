(** Per-LSP-connection primary-session execution state, used by the
    {!Lsp_methods} proof methods to back a Proof-General-style
    workflow:

    - Track which document the primary session is currently driving
      (PoC: one document at a time per connection; switching docs
      restarts the primary session).
    - Cache the latest parse of that document.
    - Translate (line, character) positions and sentence_ids to a
      sentence index, then walk the session's [exec] / [revert_to]
      operations to advance / rewind to that index.

    State sync to clients via [easycrypt/proof/stateChanged] is the
    caller's responsibility. *)

type t

(** Allocate a fresh proof-state with a primary session bound to it.
    [sw] is the connection switch — the primary session lives under
    it and is closed when the switch ends. [cwd], when [Some path],
    spawns the EC subprocess with that working directory so EC's
    [easycrypt.project] discovery walks from there (UPSTREAM § 14′).
    [None] inherits the daemon's CWD. The cwd is cached and reused
    by [restart] / the [ensure_doc] uri-switch respawn. *)
val create
  :  cwd:string option
  -> sw:Eio.Switch.t
  -> primary_label:string
  -> t

(** Close the underlying primary session. After [close], all other
    operations return [Error]. *)
val close : t -> unit

(** Bind the primary session to [uri] with the given [source]. If
    [uri] differs from the currently-bound document, restart the
    primary session (closing the old subprocess and spawning a fresh
    one). Re-parses [source] into the cached sentence list whenever
    the source hash changes. *)
val ensure_doc
  :  t
  -> sw:Eio.Switch.t
  -> uri:string
  -> source:string
  -> (unit, Error.t) result

(** Currently-bound URI, [None] if nothing has been driven yet. *)
val current_uri : t -> string option

(** Cached sentence list from the last successful parse of the
    current source. *)
val sentences : t -> Ec_llm_session.parsed_sentence array

(** Index of the highest executed sentence in the current cache, or
    [-1] if nothing has been executed (or the executed sid no longer
    matches any sentence in the cached parse). *)
val current_index : t -> int

(** Sentence id at [current_index], or [None] if nothing executed. *)
val current_sentence_id : t -> Sentence_id.t option

(** Find the index of the sentence covering [(line, character)]
    (LSP 0-based). Returns the immediately-preceding sentence if the
    position falls in inter-sentence whitespace. Returns [-1] if the
    document is empty. *)
val sentence_index_at_position
  :  t
  -> line:int
  -> character:int
  -> int

(** Execute up to (and including) [target_index], halting on the
    first error. On success returns the new current index; on error
    returns the index of the last successfully executed sentence + the
    typed error. Skips sentences with class [`Meta].

    [on_step], if provided, is invoked after EACH successful sentence
    exec with the new [current_index] and its [sentence_id]. Used by
    LSP handlers to stream per-sentence [stateChanged] notifications
    (PG-style progressive locked-region tinting). The callback runs
    inside [with_session]'s mutex — must not perform blocking I/O on
    the proof_state itself, but writes to a separately-locked output
    stream are fine. *)
val exec_to
  :  ?on_step:(int -> Sentence_id.t option -> unit)
  -> t
  -> target_index:int
  -> (int, int * Error.t) result

(** Revert back so the new current index is [target_index]. Pass
    [-1] to revert to the fresh (pre-everything) state. No-op if the
    target is at or past the current index. *)
val revert_to
  :  t
  -> target_index:int
  -> (unit, Error.t) result

(** Restart the primary session (close + spawn fresh). Clears all
    state. *)
val restart : t -> sw:Eio.Switch.t -> unit

(** Raw GOALS-JSON output at the current state. *)
val goals : t -> (string, Error.t) result

(** Atomic single-sentence advance. Skips Meta-class sentences. *)
val step_one
  :  t
  -> [ `At_end
     | `Advanced of int * Sentence_id.t option
     | `Failed of int * Sentence_id.t option * Error.t ]

(** Atomic single-sentence revert. *)
val back_one
  :  t
  -> [ `At_start
     | `Reverted of int * Sentence_id.t option
     | `Failed of Error.t ]

(** Atomic state snapshot — returns a consistent view of
    (current_index, current_sentence_id, sentence_count). Use
    instead of separate [current_index] / [sentences] reads when
    a handler needs them coherently. *)
type snapshot = {
  current_index : int;
  current_sentence_id : Sentence_id.t option;
  sentence_count : int;
}

val snapshot : t -> snapshot

(** Reconcile against an updated document source. If the source
    diverges within the locked region (common-prefix sentence index
    < current_index + 1), revert the primary to the last common-
    prefix sentence; update cache; emit nothing — caller decides
    whether to broadcast a [stateChanged].

    Returns the post-reconcile snapshot of state — caller compares
    [current_index] to the pre-call value to decide whether
    anything actually changed. Errors from parse / revert
    propagate. *)
val reconcile
  :  t
  -> uri:string
  -> source:string
  -> ([ `Not_bound | `Unchanged | `Reconciled of snapshot ], Error.t) result

(** Send SIGINT to the primary session's EC subprocess to abort the
    in-flight tactic (UPSTREAM § 25 / doc/cancellation.md). Does
    NOT take the proof-state mutex — by design: the in-flight
    request holds the mutex, and the whole point of cancel is to
    interrupt it. The EC subprocess's signal handler converts the
    SIGINT into an [EcCancel.Abort] that the in-flight LSP method
    surfaces as a "canceled" error. Idempotent / tolerant of an
    already-dead session. *)
val cancel_in_flight : t -> unit

(** Run [f] with exclusive access to the underlying primary session.
    Holds the proof-state mutex for the duration of [f] — other
    handlers (step / back / goals / exec) block until it returns.

    Used by [Proof_speculation] callers (tryTactic / suggestClosers /
    previewApply) that need to capture-try-rollback safely against
    other in-flight LSP requests. The locking discipline matches the
    Cross-cutting commitments § "Correlation, cancellation, CAS":
    each session is driven half-duplex by its owning fiber. *)
val with_session : t -> (Ec_llm_session.t -> 'a) -> 'a
