# Cancellation — `proof/cancel` v1 design

Companion design doc for UPSTREAM addition 25 (`EcCancel` module +
`Cancel.check` instrumentation) and the `easycrypt/proof/cancel`
LSP method (`doc/lsp-schema.md § 6`). Pinned 2026-04-28 as point 1
of the 14-point beta-prep priority list. Beta-1 gate.

## Problem

`tryTactic` (and other state-mutating proof methods) runs
synchronously on the daemon's primary session against the user's
current proof state. Looping rewrites + slow SMT calls block EC's
REPL loop. Subsequent requests queue. No interrupt mechanism
exists today — the editor locks until the user kills the entire
LSP server.

Concrete trigger cases:
- `rewrite ! L` where the lemma's pattern keeps producing more
  matches (e.g., `0 → 0 + 0 → 0 + 0 + 0 + 0 → …`).
- `move => /#` triggering an SMT call that runs for tens of
  seconds.
- Closer-sweep `smt()` candidate at sweep tail.
- Rewrite-builder `/#` SMT expansion.

## v1 design — polling-flag + signal handler + subprocess kill

### EcCancel module (ec-core)

New module `src/ecCancel.ml` (+ `.mli`). Owns:

```ocaml
(** Cancellation flag — set by SIGINT handler, cleared at safe
    points after [Abort] is raised. Module-internal mutex-free
    bool ref (signal-safe; OCaml runtime guarantees atomic
    bool-ref reads/writes in async-signal contexts). *)
val cancel_requested : bool ref

(** Exception raised by [check ()] when the cancel flag is set.
    Tactic combinators catch this like any other tactic failure
    and roll back to the pre-tactic state. *)
exception Abort

(** Check the cancel flag; raise [Abort] if set. Cheap (single
    bool read in the common case). Call at safe points
    throughout the tactic eval loop — combinator boundaries,
    iteration helpers, pattern walks. *)
val check : unit -> unit

(** Install the SIGINT handler. Idempotent. Called at EC startup
    in the LLM REPL entry point (NOT in batch mode — batch
    needs SIGINT to terminate the process, not abort the
    current tactic). *)
val install_signal_handler : unit -> unit

(** Reset the cancel flag. Called by the LLM REPL after sending
    the cancel-acknowledgment reply (so the next tactic starts
    in a clean state). *)
val clear : unit -> unit
```

### Instrumentation points

`Cancel.check ()` calls placed at `~5-10` strategic points in
shared infrastructure. Individual tactics inherit cancellation
through these — no per-tactic instrumentation:

- `EcCoreGoal.FApi`:
  - `t_seq` — between the two combined tactics.
  - `t_first` — before each of the alternative tactics.
  - `t_or` — before each alternative.
  - `t_seqs` — between each list element.
  - `t_repeat` — at each iteration's start.
  - `t_do` — at each iteration's start.
- `EcHiGoal.LowRewrite`:
  - `find_rewrite_patterns` — at each pattern-walk recursion
    step.
- (Anywhere else surfaced as a cancel-blind hot loop during
  beta — instrument as discovered.)

Latency target: 90th percentile abort < 100ms for typical
tactics; < 500ms for SMT-bound aborts (one Why3 re-spawn).

### Why3 / SMT subprocess handling

EC's prover bridge spawns Why3 server (persistent, one per EC
process) and/or per-call SMT subprocesses. When a tactic invokes
SMT, EC blocks waiting for Why3's reply. SIGINT to EC alone
doesn't stop Why3.

Plan:
- Cancel handler sends `SIGTERM` to the Why3 child PID.
- Why3 dies; EC's pipe-read returns ECONNRESET → bridge raises
  a tactic abort (`EcCancel.Abort` or a similar exception).
- **Background respawn fiber**: the cancel response returns
  immediately. A separate fiber spawns a fresh Why3 server. The
  next SMT call awaits the spawn — typically already complete
  by the time it's needed; otherwise <500ms latency.

### Daemon-side LSP method

`easycrypt/proof/cancel { uri, seq? }`:
- Resolve URI → project session (per `doc/session-model.md`).
- Set the EC subprocess's `cancel_requested` flag (via SIGINT —
  EC's signal handler sets the flag; signal handler is the
  bridge from OS to OCaml runtime).
- If `seq` provided: only cancel if the in-flight request
  matches that seq.
- Return `{ canceled: true | false }` immediately. The actual
  tactic abort completes asynchronously (next safe point in EC).

### VSCode preview-cancel dispatch

`vscode/src/extension.ts` adds a `proof/cancel` dispatch:
- On every preview tryTactic, capture the request seq + start
  time.
- Timeout (default 3000ms, `easycrypt-tooling.preview.timeoutMs`
  setting): if the response hasn't arrived by then, send
  `proof/cancel { uri, seq }` and clear the preview.
- On supersede (newer keystroke arrives before the prior
  preview returned), send cancel for the prior seq.
- Cancel button in the goal-pane title: explicit user-initiated
  cancel (sends cancel for the current in-flight seq).

## Bound corner cases (accepted in v1)

- **OCaml runtime calls** (large `Hashtbl.add` during massive
  normalization, GC pauses): `Cancel.check ()` is checked between
  combinator boundaries; can't interrupt mid-runtime-call. Latency
  spikes possible but bounded by individual call duration.
- **Custom C-stubs (Why3, Zarith)**: opaque to OCaml's signal
  machinery. Why3 handled separately via subprocess kill (see
  above). Zarith calls are typically short.
- **Tactics with hand-rolled iteration loops bypassing FApi**:
  rare; instrument as discovered.

## Rollback boundary

**No runtime feature flag.** Rely on commit-based rollback. Each
layer in its own commit:

- **C1 (ec-core)**: `EcCancel` module + `Cancel.check ()` call
  sites in shared infrastructure.
- **C2 (ec-core)**: prover-bridge subprocess kill + Why3
  background-respawn fiber.
- **C3 (daemon)**: `easycrypt/proof/cancel` LSP method + URI →
  project session resolution.
- **C4 (vscode)**: preview-cancel dispatch + timeout setting +
  Cancel button.

Reverting any one commit cleanly removes that layer. The future
fiber rework (see below) replaces C1 + C2 with a different
mechanism — those commits are the rollback target. C3 + C4 stay
(the protocol surface doesn't change).

A runtime flag adds 3 LoC of overhead but doesn't help with the
rearchitecting goal — that's a code rewrite, not a feature
toggle. Skip.

## Future supersession — full cancellable-fiber rework

The polling-flag + safe-points approach has known bounded
latency but isn't ASAP-optimal. A proper fiber-based execution
model (similar to async/await or coroutines) would let EC yield
explicitly at each tactic step, so cancel becomes a single
fiber-cancel-token check instead of polling at instrumented
points.

**Scope** (post-beta re-architecture, `ec-core-critical:`
territory):
- Restructure `FApi` to thread an explicit cancellation token
  through every tactic combinator.
- Introduce a yield primitive that combinators call between
  inner steps (effectively an explicit `Cancel.check ()` but
  enforced by the type system rather than convention).
- Why3 calls go through a `Why3.with_cancel` wrapper that
  registers the cancel token before blocking.
- Replace polling with token-based wait — the OS's `pselect` /
  `poll` interrupted by cancel-fd signal.

**Discussion needed with EC devs** before pursuing — touches the
core tactic eval loop. Pin in `doc/tooling-poc-plan.md § Open
Architectural Points`.

## Rearchitecting checklist (when v1 → v2 fiber rework)

1. Remove `EcCancel` module + signal handler.
2. Remove `Cancel.check ()` call sites in shared infrastructure
   (mechanical: grep for `EcCancel.check` and delete; the new
   yield primitive replaces them).
3. Replace prover-bridge SIGTERM-on-cancel with the `with_cancel`
   wrapper (token-passing).
4. Daemon `proof/cancel` keeps its LSP method shape but routes
   to the new fiber-cancel-token instead of SIGINT.
5. Vscode-side dispatch is unchanged — protocol is stable.

History prior to the rework remains as the v1 fallback if the
new model needs adjustment. The v1 commits (C1-C2) become the
revert target if the fiber rework needs to be rolled back.

## Tests

- Cancel mid-tactic returns `{ canceled: true }` within budget
  (3s timeout client-side, 100ms abort latency server-side for
  pure-OCaml tactics).
- After cancel, subsequent tryTactic against the same session
  succeeds (no stale state).
- Why3 background-respawn doesn't block other operations during
  the spawn window.
- SIGINT during a pure-OCaml computation is delivered at the
  next combinator boundary (instrument with a delay-tactic that
  loops without yielding to FApi → assert cancel doesn't return
  until it hits the next combinator).
- Cancel of a request whose response had already started flushing
  doesn't corrupt the response stream (race-condition test).

Each test lives in `tooling/smoke/run_lsp_cancel_smoke.ml` (new
smoke).
