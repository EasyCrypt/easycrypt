(** Submit-revert-commit primitive for interactive speculation.

    The pattern: capture a session's uuid before trying a command,
    execute the command, inspect the result, decide to keep it
    (commit — no-op) or undo it (rollback — REVERT back to the
    captured uuid).

    Consumers that call this primitive:
    - Semantic-TUI picker — builds cumulative intro patterns token
      by token, rolling back each token to try the next variant.
    - MCP `try_tactic` tool (Phase 6) — LLM-submitted candidates on
      a scratch, revert on rejection.
    - LSP `proof/overlay/{set,clear}` (Phase 5) — overlays land as
      speculations on scratch sessions.
    - LLM "close this subgoal with budget" (v1 roadmap) — same
      shape, just wrapped in a deadline. *)

type handle

(** Capture the session's current uuid. Pair with a subsequent
    [rollback] to return to exactly this state. Multiple captures
    on the same session are independent; [rollback] on any one
    reverts to that capture's uuid. *)
val capture : Ec_llm_session.t -> handle

(** Revert the session to the state at [capture] time.
    Idempotent-ish: if the session is already at or behind the
    captured uuid, REVERT is still issued (server responds with the
    same uuid); harmless. *)
val rollback : Ec_llm_session.t -> handle -> (unit, Error.t) result

(** Commit the speculation: a no-op returning the handle's captured
    uuid. Exposed for symmetry so callers can write
    [match decision with `Keep -> commit _ | `Undo -> rollback _].
    Does not modify session state. *)
val commit : handle -> int

(** Raw captured uuid, for logging / transcript attribution. *)
val captured_uuid : handle -> int
