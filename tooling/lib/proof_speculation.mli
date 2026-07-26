(** Daemon-side proof-interaction primitives — capture / try / commit
    / discard, plus one-shot lemma preview, closer-suggester sweep, and
    read-only directive query.

    The intent is one canonical implementation of "rollback first, then
    exec" and one error-propagation rule, shared by every surface:

    - TUI semantic-mode pickers (apply-hyp, move-intros, rewrite,
      apply-lemma, rewrite-lemma, suggest-closers).
    - LSP [easycrypt/proof/{tryTactic, suggestClosers, previewApply,
      searchLemmas}] (parity-plan Phases 3-4).
    - MCP [try_tactic] (Phase 6).
    - REPL [:try] (currently bypasses; can be retargeted later).

    Three locked-in design decisions (per HANDOFF-VSCODE-FIRST.md):

    1. [on_progress] is invoked AFTER per-candidate rollback in
       [suggest_closers], so the session state is consistent across the
       callback boundary. Lock-down for the TUI's progressive ordering;
       LSP wraps the same hook with [$/progress].
    2. Rollback errors propagate as [Result], never swallowed. Callers
       (TUI keep best-effort, LSP propagates as InternalError with
       [data.rollbackDetail]) decide policy at the call site.
    3. Cumulative-handle session is the only API. One-shot probes (LSP
       [tryTactic], MCP [try_tactic]) are sugar — see [try_tactic].

    Locking. This module operates on a raw [Ec_llm_session.t]. LSP
    callers that drive a session via [Proof_state.t] are responsible
    for serializing access through the proof_state mutex (held across
    the full begin / try* / commit-or-discard lifecycle). TUI and REPL
    are single-threaded. *)

(* --- Tactic catalog ------------------------------------------------- *)

type tactic =
  | Apply_hyp
  | Move_intros
  | Rewrite
  | Apply_lemma
  | Rewrite_lemma
  | Suggest_closers

val tactic_catalog : tactic list
val tactic_label : tactic -> string

(* --- Pure source builders ------------------------------------------ *)

val verb_keyword : [ `Apply | `Rewrite ] -> string
val apply_hyp_source : Goal_view.hypothesis -> string
val move_cumulative_source : string list -> string
val rewrite_cumulative_source : string list -> string
val lemma_picker_source
  :  verb:[ `Apply | `Rewrite ]
  -> Search_result.hit
  -> string

(* --- Cumulative-handle session API --------------------------------- *)

type session

type trial_outcome =
  | Trial_ok of { goals : Goal_view.t option; body : string }
  | Trial_err of string

val begin_session : Ec_llm_session.t -> session
(** Capture the session's current uuid. *)

val try_ : session -> source:string -> trial_outcome
(** Roll back to the captured state, then exec [source] as
    [`Executable]. On rollback failure, returns [Trial_err] with the
    rollback detail (so the caller sees one error path). On exec
    failure, returns [Trial_err] with the exec error string. *)

val commit : session -> (unit, Error.t) result
(** Drop the rollback right. Session stays in whatever state the last
    [try_] left it. No-op on the underlying session today; the result
    type is preserved for future invariant checks. *)

val discard : session -> (unit, Error.t) result
(** Roll back to the captured state. Surfaces rollback errors as
    [Error] — callers decide whether to swallow (TUI best-effort) or
    propagate (LSP InternalError). *)

val captured_uuid : session -> int
(** Captured uuid for logging / transcript attribution. *)

(* --- One-shot helpers (sugar over the session API) ----------------- *)

val try_tactic : Ec_llm_session.t -> source:string -> trial_outcome
(** [let s = begin_session t in
        let r = try_ s ~source in
        let _ = discard s in r]
    — convenience for LSP one-shot [tryTactic] and MCP [try_tactic]. *)

(* --- Read-only directive query ------------------------------------- *)

type query_result = {
  body : string;          (** pp-text body — search hits, print output, … *)
  notices : string list;  (** [NOTICE:] lines streamed during dispatch. *)
}

val query : Ec_llm_session.t -> source:string -> (query_result, Error.t) result
(** Run a read-only directive ([search …], [print …], [locate …],
    [pragma …]) and capture its output. Directives don't advance uuid
    (UPSTREAM addition 7), so no speculation handle is needed. Caller
    is responsible for ensuring [source] is class [`Directive]; passing
    an executable will trip the uuid invariant on the session.

    Used by the LSP/MCP lemma-search dispatch (parity Phase 4): the
    InputBox sends a syntax-checked pattern, the daemon dispatches
    [search (…).], [Search_result.of_notices] parses the result. *)

(* --- Lemma preview (rolling speculation) --------------------------- *)

type lemma_preview =
  | Preview_ok of { goals_after : Goal_view.t option; body : string }
  | Preview_err of string

val preview_lemma
  :  Ec_llm_session.t
  -> verb:[ `Apply | `Rewrite ]
  -> ?prev:session
  -> Search_result.hit
  -> (lemma_preview * session, Error.t) result
(** Roll back any [prev] preview, then capture and apply/rewrite [hit].
    Returns the preview outcome and the new speculation session — caller
    is responsible for [discard]ing it on exit (cursor move, focus
    leave, picker close).

    Rollback errors on [prev] surface as [Error]; per-call exec failures
    are encoded as [Preview_err] so the surface can render them
    in-line. *)

(* --- Closer suggester ---------------------------------------------- *)

type suggest_outcome =
  | Suggest_closes      (** subgoal count → 0. *)
  | Suggest_open of int (** N subgoals remain. *)
  | Suggest_err of string

type suggest_row = {
  src : string;     (** EC source including trailing [.]. *)
  label : string;   (** human-friendly display label. *)
  outcome : suggest_outcome;
}

val sort_suggest_rows : suggest_row list -> suggest_row list
(** Stable sort: [Suggest_closes] first, then [Suggest_open], then
    [Suggest_err]. Preserves input order within each bucket. *)

val default_closer_candidates : (string * string) list
(** [(label, src)] pairs in heuristic ascending runtime order:
    [reflexivity], [trivial], [assumption], [by done], [by auto],
    [smt()]. *)

val goal_count_now : Ec_llm_session.t -> int option
(** Read the session's current subgoal count via GOALS-JSON, returning
    [None] on fetch / parse failure. Used by callers that need the
    count delta semantics ("did the focused subgoal close?") for
    speculative tactics — see [tryTactic.closedFocused] in the LSP
    handler and [suggest_closers]'s internal classification. *)

val suggest_closers
  :  Ec_llm_session.t
  -> ?candidates:(string * string) list
  -> ?before_candidate:(label:string -> remaining:int -> unit)
  -> ?on_progress:(suggest_row -> remaining:int -> unit)
  -> unit
  -> (suggest_row list, Error.t) result
(** Try each closer candidate speculatively. Stops early on the first
    candidate that fully closes the goal. Returns rows in the order
    they were tried; caller [sort_suggest_rows] for display.

    Two callback hooks, both invoked at session-state-stable points:

    - [before_candidate ~label ~remaining] fires immediately before
      [Speculation.capture] for the next candidate. The session is at
      the captured base state (just like after the previous candidate's
      rollback). [remaining] is the count of candidates still to try
      including this one. Surfaces use this for "trying X…" frames
      (TUI) or [$/progress] [Begin]/[Report] (LSP).
    - [on_progress ~row ~remaining] fires once per candidate AFTER its
      rollback (decision 1). [remaining] is the count of candidates
      still to try AFTER this one (excludes the early-stop case — when
      a closer is found, [remaining] reaches 0 and the loop exits).

    Both callbacks see a session at base uuid, so reads are coherent.
    Decision (1) generalizes: callbacks fire only at rollback-stable
    boundaries, never mid-exec.

    Per-candidate exec failures are encoded as [Suggest_err] outcomes
    in the returned rows. The function returns [Error] only when a
    rollback itself fails (decision 2). *)
