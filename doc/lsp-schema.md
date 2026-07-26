# LSP Schema — EasyCrypt Tooling Daemon

Wire-level specification for the LSP surface served by the daemon.
Companion to `doc/tooling-protocol.md` (subprocess wire to `ec llm`)
and `doc/tooling-poc-plan.md` (phase / scope).

**This document is normative.** Both the daemon (server) and clients
(VSCode extension, future Neovim plugin, etc.) adhere to it. We
control both sides; atomic flips are possible. When the wire shape
changes, both sides update in the same release.

**Status (2026-04-26):** MVP version. Cache-aware fields pinned
upfront so cache-substrate (Phase 5.0) addition doesn't require a
wire bump. Some method handlers ship as null/stub-returning until
cache substrate lands; the wire shape doesn't change.

## 1. Method Namespace

All custom proof methods use the `easycrypt/proof/*` namespace.
Standard LSP methods (`initialize`, `textDocument/didChange`, etc.)
keep their LSP-spec namespaces.

**Namespace constant in implementation:**

```ocaml
let proof_ns = "easycrypt/proof"
let method_name suffix = proof_ns ^ "/" ^ suffix
```

Single point of change for the namespace. Server defines all
methods via `method_name "..."`; client mirrors. Atomic flip costs
one constant edit per side.

**Choice rationale**: `easycrypt/proof/*` matches the namespace
established by upstream EC's `vscode` branch (see `VSCODE_LSP.md`).
Adopting their convention means their VSCode extension can serve as
a starting point for our port with minimal method-name plumbing
changes.

## 2. Initialize / Capability Handshake

### 2.1 `initialize` request (client → server)

Standard LSP `initialize` plus our `initializationOptions.proof`
extension:

```json
{
  "method": "initialize",
  "params": {
    "processId": ...,
    "rootUri": "file:///path/to/workspace",
    "capabilities": { ... standard LSP ... },
    "initializationOptions": {
      "proof": {
        "clientVersion": "1.0.0",
        "supportsRecoveryStrategy": ["halt", "best_effort_admit"],
        "supportsCachePolicy": ["lax", "strict"],
        "supportsLongRunningProgress": true,
        "supportsExecutingRangeNotification": true
      }
    }
  }
}
```

**`initializationOptions.proof` fields (all optional; absence =
"client doesn't support this surface"):**

- `clientVersion` — semver string. Server can fail with
  `IncompatibleClient` if too old.
- `supportsRecoveryStrategy` — array of recovery strategies the
  client knows about. Server uses to decide which it can offer.
- `supportsCachePolicy` — array of cache policies the client
  recognizes for `proof.cachePolicy` workspace setting.
- `supportsLongRunningProgress` — boolean. Whether client renders
  `$/progress` notifications usefully.
- `supportsExecutingRangeNotification` — boolean. Whether client
  renders the custom `easycrypt/proof/executingRange` notification
  for sentence-level highlighting.

### 2.2 `initialize` response (server → client)

```json
{
  "result": {
    "capabilities": {
      "textDocumentSync": { ... },
      "diagnosticProvider": { ... },
      "hoverProvider": false,         // Phase 4-dependent; false in PoC
      "definitionProvider": false,    // Phase 4-dependent
      "documentSymbolProvider": false // Phase 4-dependent
    },
    "serverInfo": {
      "name": "easycrypt-daemon",
      "version": "..."
    },
    "proofCapabilities": {
      "serverVersion": "...",
      "supportedRecoveryStrategies": ["halt", "best_effort_admit"],
      "supportedCachePolicies": ["lax", "strict"],
      "minClientVersion": "1.0.0",
      "currentSession": {
        "label": "primary",
        "uuid": 0,
        "currentSentenceId": null,
        "cas": "00000000000000000000000000000000",
        "casPolicy": "lax"
      }
    }
  }
}
```

**`proofCapabilities` fields:**

- `serverVersion` — daemon binary version.
- `supportedRecoveryStrategies` — strategies the server supports.
- `supportedCachePolicies` — cache policies the server supports.
- `minClientVersion` — server fails handshake if client below this.
- `currentSession` — the session this connection is bound to (see
  § 7 Session Linkage).

### 2.3 `initialized` notification

Standard LSP. No extensions.

### 2.4 `shutdown` request / `exit` notification

Standard LSP. Server cancels in-flight requests via the request
registry (see § 8), drains, releases resources, exits cleanly.

## 3. TextDocument Lifecycle

Standard LSP methods, full-document sync (PoC). Incremental sync is
a v1+ optimization; not yet supported.

### 3.1 `textDocument/didOpen`

Standard. Server registers document in workspace; spawns / reuses
session for the workspace.

### 3.2 `textDocument/didChange`

Standard, full-document sync only (`textDocumentSync.change = 1`).

Server-side handling:
- Update document content in workspace.
- Trigger debounced (default 200ms; `proof.debounceMs` workspace
  setting) re-analysis.
- Re-analysis: dispatch ANALYZE-JSON for the document; emit
  `publishDiagnostics`.
- **Auto-reconcile against the primary session** (Slice D): the
  daemon parses the new source, computes the longest sentence-
  source common prefix against the cached parse, and if the
  divergence sits inside the locked region (common_prefix - 1 <
  current_index) reverts the primary session to the last
  common-prefix sentence. On retraction, emits an
  `easycrypt/proof/stateChanged` notification (§ 5.1) with the
  post-retraction `currentEndPosition` so the client can shrink
  its locked-region rendering immediately. Controlled by
  `proof.autoReconcile` (default `true`).

### 3.3 `textDocument/didClose`

Standard. Server removes document from workspace; tears down
associated state (session if no other doc in same workspace; cache
entries; recovery scratch).

### 3.4 `textDocument/publishDiagnostics` (server → client)

Standard LSP shape. Diagnostics derived from ANALYZE-JSON output.

Each `Diagnostic`:
- `range` — line:col converted from sentence-id range.
- `severity` — `Error | Warning | Information | Hint`.
- `code` — string code from ERROR-JSON taxonomy (`ParseError`,
  `TypeError`, `TacticFailure`, `Internal`).
- `source` — `"easycrypt"`.
- `message` — pretty-printed `detail` from ERROR-JSON.
- `data` — extension carrying:
  - `sentence_id` — opaque string.
  - `phase` — `parse | typecheck | tactic | protocol | unknown`.
  - `scope?` — `{ kind: "proof"|"theory"|"section",
    opener_sentence_index: N }`. Textual scope the diagnostic sits
    in, lifted directly from ANALYZE-JSON's `enclosing_scope`
    field. Absent when the diagnostic is at top level. Clients can
    collapse all diagnostics sharing the same `opener_sentence_index`
    into a single squiggle on the opener line plus a folded list,
    instead of N separate squiggles. Stack tracks textual structure,
    not EC's accept/reject — a failed `qed.` still ends the proof
    scope for attribution.
  - `cascade_of?` — sentence_id of the upstream failure if this is
    a cascade (per ANALYZE-JSON v1 deferral; null in v0).

## 4. Custom Proof Methods

All custom methods under `easycrypt/proof/*`.

### Invariant: state-mutating methods emit document text

Every state-mutating method (`step` / `back` / `execToPoint` /
`revertToPoint` / `execAll` / `restart` / new methods that
operate on proof state) corresponds to a stock-EC sentence
sequence that gets executed against the bound EC subprocess.
The full proof script must remain stock-EC-checkable offline —
i.e., re-running the file through `ec` (without the daemon)
must reproduce the same proof traversal.

Implications:
- Daemon-only ephemeral state shifts are NOT permitted as
  state-mutating methods. Any operation that changes proof
  focus / progress / hypothesis context must have a stock-EC
  tactic-source serialization.
- UI-only operations that don't change proof state are exempt
  (e.g., displayed-subgoal cycling via Cmd/Ctrl+Alt+]/[ shifts
  only the displayed index, not EC's `current_index` — no
  document mutation).
- New "focus current goal" command (point 4 of beta-prep)
  computes `delta = displayed_index - current_index` and emits
  `cycle <delta>.` into the document at the cursor — preserves
  offline checkability.

### 4.1 `easycrypt/proof/execToPoint` — request, mutating

```json
{
  "method": "easycrypt/proof/execToPoint",
  "params": {
    "uri": "file:///...",
    "target": {
      // One of: sentence_id form OR position form
      "sentence_id": "..." | undefined,
      "position": { "line": N, "character": N } | undefined
    },
    "expectedCas": "..." | null,
    "recoveryStrategy": "halt" | "best_effort_admit",
    "cachePolicy": "lax" | "strict" | null  // null = use workspace default
  }
}
```

Response:

```json
{
  "result": {
    "advancedTo": "<sentence_id>",
    "newCas": "...",
    "executedSentences": N,
    "skippedSentences": N,    // when recoveryStrategy = best_effort_admit
    "diagnostics": [ <Diagnostic>, ... ]  // failures encountered (best-effort mode)
  }
}
```

Errors:
- `StaleCas { server_cas }` — `expectedCas` didn't match current.
- `UnknownSentenceId { sentence_id }` — target sentence_id not in
  document.
- `Cancelled { reason }` — request cancelled via `$/cancelRequest`.

**`recoveryStrategy: "halt"`** (default for safety): execute
serially; first failure halts; advance to last-good sid; return.
For CI-style usage; mirrors current REPL behavior.

**`recoveryStrategy: "best_effort_admit"`**: execute serially; on
failure, apply daemon-internal recovery (structural-recovery
catalog when EXEC-JSON v0.1 lands; focused-admit fallback). Continue
to target. Return diagnostics for each recovered/failed sentence.
For interactive editor usage.

### 4.2 `easycrypt/proof/revertToPoint` — request, mutating

```json
{
  "method": "easycrypt/proof/revertToPoint",
  "params": {
    "uri": "file:///...",
    "target": { "sentence_id" or "position" },
    "expectedCas": "..." | null
  }
}
```

Response:

```json
{
  "result": {
    "revertedTo": "<sentence_id>",
    "newCas": "..."
  }
}
```

Errors: `StaleCas`, `UnknownSentenceId`, `Cancelled`.

### 4.3 `easycrypt/proof/goals` — request, read-only

```json
{
  "method": "easycrypt/proof/goals",
  "params": {
    "uri": "file:///...",
    "sentence_id": "..." | undefined,  // null = current
    "position": { ... } | undefined
  }
}
```

Response:

```json
{
  "result": {
    "active": true,
    "subgoal_count": N,
    "current_index": N,
    "subgoals": [ ... GOALS-JSON shape ... ],
    "provenance": "fresh" | "cached" | "lax_admitted",
    "cas": "..."
  }
}
```

`provenance` field pinned upfront (Phase 5.0 cache fills it):
- `fresh` — re-executed on demand.
- `cached` — served from Goals_cache (Phase 5.0+).
- `lax_admitted` — cached entry from a lax-admitted execution; the
  goal state reflects admit-taint (Phase 5.0+).

In PoC pre-cache, server always returns `provenance: "fresh"`.

### 4.4 `easycrypt/proof/step` — request, mutating (convenience)

Atomic single-sentence advance. Skips Meta-class sentences. Sugar
over `execToPoint` aimed at PG-style step keybindings.

```json
{
  "method": "easycrypt/proof/step",
  "params": {
    "uri": "file:///...",
    "count": N | undefined  // default 1; reserved for parity-plan Phase 1
  }
}
```

Response:

```json
{
  "result": {
    "advancedTo": "<sentence_id>" | null,
    "newCas": "...",
    "executedSentences": N,
    "skippedSentences": 0,
    "diagnostics": [ <Diagnostic>, ... ],  // when the underlying exec failed
    "atEndOfDocument": false | true
  }
}
```

`atEndOfDocument: true` indicates no executable sentence remains
past the current position; `executedSentences` is then `0`.

### 4.5 `easycrypt/proof/back` — request, mutating (convenience)

Atomic single-sentence revert. Sugar over `revertToPoint`.

```json
{
  "method": "easycrypt/proof/back",
  "params": {
    "uri": "file:///...",
    "count": N | undefined  // default 1; reserved for parity-plan Phase 1
  }
}
```

Response:

```json
{
  "result": {
    "revertedTo": "<sentence_id>" | null,  // null when reverted to fresh state
    "newCas": "..."
  }
}
```

### 4.5b `easycrypt/proof/execAll` — request, mutating

Advance the primary session through every remaining non-Meta
sentence in the document. Stops on first non-Meta error
(matches PG's "process to end" UX). Emits `stateChanged` per
sentence advanced (existing infra).

```json
{
  "method": "easycrypt/proof/execAll",
  "params": { "uri": "file:///..." }
}
```

Response:

```json
{
  "result": {
    "advancedTo":      "<sentence_id>" | null,
    "atEndOfDocument": true | false,
    "stoppedAtError":  "<diagnostic>" | null,
    "newCas":          "..."
  }
}
```

`stoppedAtError` is non-null when a non-Meta sentence raised an
error; `atEndOfDocument` is true when the last sentence advanced
without error. Cancellable via `easycrypt/proof/cancel` — rolls
back to the last successfully-advanced sentence.

### 4.6 `easycrypt/proof/restart` — request, mutating

Tear down the per-connection primary session and respawn fresh.
Resets state to "no document bound, current_index = -1".

```json
{
  "method": "easycrypt/proof/restart",
  "params": { "uri": "file:///..." }
}
```

Response:

```json
{
  "result": {
    "newCas": "...",
    "currentSentenceId": null
  }
}
```

Emits `easycrypt/proof/stateChanged` with reset state.

### 4.7 `easycrypt/proof/tryTactic` — request, read-only (speculative)

One-shot speculative tactic trial. Captures the primary session's
current uuid, runs `source` as an `Executable` sentence, captures
goals, then rolls back to the captured uuid. Primary session ends in
the same state it started; CAS unchanged.

Sugar over `Proof_speculation.try_tactic` (parity Phase 0 lift). LSP
holds the proof_state mutex across capture/exec/rollback so other
handlers don't race.

```json
{
  "method": "easycrypt/proof/tryTactic",
  "params": {
    "uri": "file:///...",
    "source": "apply foo.",
    "expectedCas": "..." | null
  }
}
```

Response:

```json
{
  "result": {
    "outcome": "ok" | "err",
    "body": "<EC reply body>" | null,
    "goalsAfter": { ... GOALS-JSON ... } | null,
    "closedFocused": true | false,
    "error": "<error detail>" | null,
    "newCas": "..."
  }
}
```

- `outcome: "ok"`: tactic ran without error. `body` is the EC reply
  body, `goalsAfter` is the GOALS-JSON envelope (same shape as
  `easycrypt/proof/goals`) *as if the tactic were applied* — captured
  speculatively, then rolled back before the response returns so
  primary state stays put. `error` is null.
- `outcome: "err"`: tactic failed (parse error, type error, tactic
  failure, rollback error). `error` carries the detail; `body` and
  `goalsAfter` are null. `closedFocused` is `false`.
- `closedFocused`: `true` iff the focused subgoal was discharged by
  the tactic (post-tactic subgoal count is 0, OR is strictly less
  than the pre-tactic count — meaning the focused goal closed even
  if other unrelated subgoals from prior splits remain). Use this
  for the "★ closes the goal" UI rendering rather than checking
  `goalsAfter.subgoal_count == 0`, which only flags whole-proof
  completion. Same closer-detection semantics as
  `easycrypt/proof/suggestClosers`.

`newCas` matches the pre-call CAS — speculative trial doesn't mutate.

Errors: `StaleCas`, `Internal`.

### 4.8 `easycrypt/proof/suggestClosers` — request, read-only (sweep)

Iterate a curated list of closer-tactic candidates speculatively
against the current goal. Returns rows in input order; client renders
"closes / opens N subgoals / errors" per candidate. Sweep stops early
on the first candidate that fully closes the goal.

Sugar over `Proof_speculation.suggest_closers` (parity Phase 0 lift).
LSP holds the proof_state mutex across the entire sweep.

```json
{
  "method": "easycrypt/proof/suggestClosers",
  "params": {
    "uri": "file:///...",
    "expectedCas": "..." | null
  }
}
```

Response:

```json
{
  "result": {
    "rows": [
      { "src": "reflexivity.", "label": "reflexivity",
        "outcome": "closes" },
      { "src": "trivial.",     "label": "trivial",
        "outcome": "open", "subgoalCount": 2 },
      { "src": "smt().",       "label": "smt()",
        "outcome": "err", "detail": "<error text>" }
    ],
    "newCas": "..."
  }
}
```

`outcome` is `"closes" | "open" | "err"`. `subgoalCount` is present
when `outcome == "open"`; `detail` is present when `outcome == "err"`.
Rows are returned in the order tried (caller sorts for display).

`newCas` matches the pre-call CAS — speculative sweep doesn't mutate.

**PoC stopgap**: no per-candidate timeout. If `smt()` hangs (known
in-demo trigger), the sweep blocks until EC returns. Hard timeout
arrives with the cancellable-fiber rework / `proof/cancel` (open
architectural point #3). Workaround: avoid `smt()`-heavy goals when
sweeping; or trim the candidate list daemon-side.

Errors: `StaleCas`, `Internal`.

### 4.9 `easycrypt/proof/searchLemmas` — request, read-only (directive)

Dispatch an EC `search` directive (or any read-only directive that
emits hits as `NOTICE:` lines) and return parsed `Search_result.hit`
records. Used by the parity Phase 4 lemma picker (apply / rewrite).

```json
{
  "method": "easycrypt/proof/searchLemmas",
  "params": {
    "uri": "file:///...",
    "source": "search (_ <= _)."
  }
}
```

`source` is a complete EC source string — caller wraps the user's
pattern with parens and adds the trailing `.` before sending. Daemon
runs it via `Proof_speculation.query` (sentence_class = directive,
doesn't advance uuid per UPSTREAM addition 7) and parses the
resulting `NOTICE:` frames via `Search_result.of_notices`.

Response:

```json
{
  "result": {
    "hits": [
      { "qname": "Int.lez_total",
        "kind": "lemma",
        "short_name": "lez_total",
        "signature": "lemma lez_total: forall (x y : int), x <= y \\/ y <= x" },
      ...
    ],
    "error": null | "<error detail>"
  }
}
```

- `hits[]` may be empty if the pattern matched nothing or the
  directive errored. Inspect `error` to distinguish "no matches" from
  "directive failed."
- `error` non-null means the directive itself failed (e.g.,
  `TypeError` for ambiguous pattern). UI should surface so the user
  can refine.

Caller-side parens responsibility: clients should auto-wrap the
user's pattern with `(...)` before dispatching, since EC's `search`
parses without the wrapping in a quirky way for operator patterns
like `_ <= _`. Wire shape doesn't enforce this — daemon dispatches
verbatim.

### 4.10 `easycrypt/proof/checkpoint` / `easycrypt/proof/revertCheckpoint`

Sugar over named sentence_ids. Implementation deferred to v1; PoC
returns `MethodNotImplemented`.

```json
{
  "method": "easycrypt/proof/checkpoint",
  "params": { "uri": "...", "name": "before-smt" }
}
```

```json
{
  "method": "easycrypt/proof/revertCheckpoint",
  "params": { "uri": "...", "name": "before-smt", "expectedCas": "..." }
}
```

### 4.11 `easycrypt/proof/refreshDeps` — request, side-effecting

Manual cache invalidation trigger. Re-stat all tracked files for the
workspace; invalidate cache entries depending on changed files.

```json
{
  "method": "easycrypt/proof/refreshDeps",
  "params": { "uri": "file:///..." | null }  // null = all docs
}
```

Response:

```json
{
  "result": {
    "invalidatedFiles": [ "file:///..." ],
    "invalidatedEntries": N
  }
}
```

## 5. Server Notifications

### 5.1 `easycrypt/proof/stateChanged` — server → client

Emitted on every primary-session state advance or revert.

```json
{
  "method": "easycrypt/proof/stateChanged",
  "params": {
    "uri": "file:///...",
    "sessionLabel": "primary",
    "currentSentenceId": "..." | null,
    "currentEndPosition": { "line": N, "character": N } | null,
    "cas": "...",
    "seq": N,
    "origin": {
      "kind": "lsp" | "mcp" | "daemon",
      "correlationId": "..."
    }
  }
}
```

`currentEndPosition` is the 0-based LSP position immediately after
the end of the most-recently-executed sentence, derived from the
daemon's cached PARSE-JSON. Clients use it to render the locked
region as a range from `(0,0)` to `currentEndPosition` without
having to parse the document themselves. `null` when nothing has
been executed.

### 5.2 `easycrypt/server/restarted` — server → client

Emitted on session restart (subprocess died, explicit `pragma
restart`, dependency invalidation).

```json
{
  "method": "easycrypt/server/restarted",
  "params": {
    "uri": "file:///...",
    "sessionLabel": "primary",
    "reason": "user-requested" | "invariant-violation" | "session-crash" | "dependency-invalidation",
    "triggeredBy": [ "file:///..." ] | null,  // for dependency-invalidation
    "newCas": "...",
    "seq": N,
    "clientMustReplay": true
  }
}
```

### 5.3 `easycrypt/proof/executingRange` — server → client

Sentence-level highlighting hint for the editor. Emitted at
boundary transitions during multi-sentence operations.

```json
{
  "method": "easycrypt/proof/executingRange",
  "params": {
    "uri": "file:///...",
    "sentence_id": "...",
    "state": "starting" | "executing" | "complete" | "failed"
  }
}
```

Editor renders highlighting (e.g., gutter color, line background).
Client opt-in via `supportsExecutingRangeNotification` capability.

### 5.4 `easycrypt/proof/externalDrift` — server → client

Emitted when daemon detects on-disk content for a tracked file
differs from the loaded version (file-mode `preservation` or
`realtime` with `prompt` sub-mode).

```json
{
  "method": "easycrypt/proof/externalDrift",
  "params": {
    "uri": "file:///...",
    "kind": "modified" | "deleted",
    "sessionLabel": "primary"
  }
}
```

Client renders a banner + offers `proof/saveMemoryVersion` /
`proof/takeDiskVersion` (custom commands; daemon-side equivalents
TBD; deferred to v1).

### 5.5 `$/progress` — server → client (LSP standard)

For long-running operations. Server emits `WorkDoneProgressBegin`,
`WorkDoneProgressReport`, `WorkDoneProgressEnd` per LSP spec. Used
by `easycrypt/proof/execToPoint` over multi-sentence ranges, by
ANALYZE-JSON re-analysis on big files, by cache replay-to-sid.

Client opt-in via `supportsLongRunningProgress` capability.

## 6. Cancellation

Two cancellation surfaces, both routed to the same `EcCancel`
flag in the EC subprocess (see `doc/cancellation.md` for the
EC-side design):

### 6.1 LSP standard `$/cancelRequest` notification

```json
{
  "method": "$/cancelRequest",
  "params": { "id": <request_id> }
}
```

Server-side: look up request id in `Request_registry`; cancel the
fiber + send SIGINT to the bound EC subprocess. Fiber catches
`Cancelled` exception; tactic raises `EcCancel.Abort` at the next
safe point (combinator boundary, `t_repeat`/`t_do` iteration, or
`find_rewrite_patterns` walk). Server emits LSP error response
with code `-32800` (RequestCancelled).

### 6.2 `easycrypt/proof/cancel` — request, side-effecting

Application-level cancel (independent of LSP `$/cancelRequest`).
Used by the VSCode preview-cancel dispatch (timeout, supersede,
user-clicks-cancel-button).

```json
{
  "method": "easycrypt/proof/cancel",
  "params": {
    "uri":  "file:///path/to/foo.ec",
    "seq":  42
  }
}
```

- `uri` (required): identifies which session's in-flight tactic
  to cancel. URI → project session resolution (see
  `doc/session-model.md`).
- `seq` (optional): the per-request seq ID returned by a prior
  request. When provided, cancels ONLY the request with that
  seq. When omitted, cancels the session's current in-flight
  request.

Response:

```json
{ "result": { "canceled": true | false } }
```

`canceled: false` means the request had already completed by the
time the cancel arrived (race; benign).

**Why3 / SMT subprocess handling**: the cancel SIGINTs EC; if EC
is blocked on a Why3 child, EC's prover bridge SIGTERM'd the
child + spawns a replacement in a background fiber (so the
cancel response returns immediately). The next SMT call awaits
the spawn (typically already complete; otherwise <500ms).

Reusable across LSP and MCP — same `Request_registry` module.

**Convenience wrappers** (planned): `easycrypt/proof/cancelAll
{ uri }` cancels all in-flight requests for the URI's session;
`easycrypt/proof/cancelAllAcrossSessions {}` cancels everything
across all sessions for the connection. Built on top of `cancel`
with a seq-list traversal.

## 7. Session Linkage (Multi-Instance)

The daemon supports multi-instance per-surface via per-connection
spawning. LSP and MCP are independent surfaces; each accepts
multiple connections. PoC ships single-LSP + single-MCP per session
by default; multi-client per surface lifts trivially (each
connection = own instance).

### 7.1 `attachTo` parameter on `initialize`

```json
{
  "initializationOptions": {
    "proof": {
      "attachTo": "primary" | "<session_label>" | null
    }
  }
}
```

- `null` (default): server creates / joins the workspace's primary
  session.
- `"primary"`: explicit alias for the workspace's most-recently-active
  session.
- `<session_label>`: attach to a specific session (e.g., one created
  via `easycrypt/proof/forkSession`).

Failure: server returns `SessionNotFound { label }` if requested
session doesn't exist.

### 7.2 Cross-surface attachment

LSP user editing in VSCode + MCP-driven Claude both attaching to
`"primary"` is the design intent. Both observe the same primary
state; CAS arbitrates state-mutating writes.

### 7.3 Session discovery

`easycrypt/proof/listSessions` — request, read-only.

```json
{
  "method": "easycrypt/proof/listSessions"
}
```

Response:

```json
{
  "result": {
    "sessions": [
      {
        "label": "primary",
        "name": null,
        "uuid": 42,
        "workspaceUri": "file:///...",
        "documentCount": 3,
        "lastActiveAt": "2026-04-26T12:34:56Z",
        "attachedInstances": [ "lsp:...", "mcp:..." ]
      }
    ]
  }
}
```

### 7.4 Session naming

`easycrypt/proof/nameSession` — request.

```json
{
  "method": "easycrypt/proof/nameSession",
  "params": { "label": "primary", "name": "main-edit" }
}
```

Names are sugar over labels; unique per daemon. `attachTo` accepts
either label or name.

### 7.5 Session forking

`easycrypt/proof/forkSession` — request.

```json
{
  "method": "easycrypt/proof/forkSession",
  "params": { "from": "primary", "name": "alt-attempt" }
}
```

Response:

```json
{
  "result": { "label": "session-abc123", "name": "alt-attempt" }
}
```

Creates a new session sharing the source's workspace + load path +
document set initial state, with independent uuid/CAS lineage onward.

### 7.6 Session promotion

`easycrypt/proof/promoteSession` — request.

```json
{
  "method": "easycrypt/proof/promoteSession",
  "params": { "label": "session-abc123" }
}
```

Makes the named session the canonical primary for its workspace.
Other sessions detach and tear down.

## 8. CAS — Compare-and-Swap

CAS = BLAKE2b-128 fingerprint of `(statement_hash, proof_hash)`
sequence on primary session since last Restart.

- 32-character hex string.
- Returned in every state-mutating method's response.
- Carried in `easycrypt/proof/stateChanged` notification.
- Optional `expectedCas` parameter on state-mutating methods;
  mismatch → `StaleCas { server_cas }` error; client refreshes from
  the error payload and retries.

PoC pre-cache: server returns the empty/zero CAS
(`"00000000000000000000000000000000"`). Client honors but no real
arbitration. Phase 5.0 cache substrate populates real values.

## 9. File Modes

Workspace setting `proof.fileMode: "preservation" | "realtime"`.
Default `preservation`.

### 9.1 Preservation mode (default)

Daemon's loaded version is canonical for the current proof state.
On detected disk drift (lazy-poll on next exec, or future watcher),
daemon emits `easycrypt/proof/externalDrift` (§ 5.4).

Client offers user actions (custom commands; daemon implementations
deferred to v1):
- `easycrypt/proof/saveMemoryVersion` — write daemon's loaded
  version to disk.
- `easycrypt/proof/takeDiskVersion` — reload from disk; reconcile
  primary session.
- `easycrypt/proof/openMergeTool` — write both to temp files;
  client launches mergetool; daemon takes merged result.

### 9.2 Real-time mode

External changes picked up automatically. Sub-config
`proof.realTimeReload: "instant" | "prompt"`:
- `instant` (default in real-time mode): immediately reload +
  reconcile.
- `prompt`: emit `externalDrift` notification; client offers
  reload button.

## 10. Cache Policy (Phase 5.0)

Workspace setting `proof.cachePolicy: "lax" | "strict"`. Default
`lax` for interactive sessions; strict recommended for CI.

- **`lax`**: failing proof invalidates only its own entry;
  downstream entries depending on the failed proof's
  `statement_hash` stay valid (admit-taint propagates but
  doesn't invalidate).
- **`strict`**: failing proof invalidates its entry AND cascades
  through downstream entries depending on it.

Client-visible effect: `easycrypt/proof/goals { sid }` for an entry
that depends on a currently-failing upstream proof returns the
cached value with `provenance: "lax_admitted"` under lax;
`provenance: "fresh"` (with potentially-stale-warning) or no result
under strict.

Mode switch:
- `lax → strict`: server revalidates all entries; cascading
  invalidations may take time; client receives standard
  `publishDiagnostics` updates as state churns.
- `strict → lax`: cheap; just changes future invalidation policy.

## 11. Recovery Strategy

Per-`execToPoint` parameter `recoveryStrategy`:

- **`halt`** (default): stop at first failure; advance to last-good
  sid; return.
- **`best_effort_admit`**: continue past failures; apply daemon-side
  recovery:
  - **Structural-recovery catalog** (when EXEC-JSON v0.1 lands):
    inline-atomic patterns rewritten via AST-level transformation.
    E.g., `have h : Foo by smt` failing → `have h : Foo by admit`
    dispatched to scratch; downstream sees `h` introduced as
    admitted.
  - **Focused-admit fallback**: when catalog doesn't match, daemon
    issues `admit.` against current focused subgoal; advance.
  - **Cascade tagging** (when ANALYZE-JSON v1 cascade tagging
    lands): downstream failures referencing intended-but-not-introduced
    binders get `cascade_of: <sentence_id>` in their diagnostic.

PoC pre-EXEC-JSON-v0.1: catalog is empty; recovery = focused-admit
only. Still useful for sentence-level advance-past-failure;
limitation documented.

## 12. Undo & Reconciliation

`didChange` is the unifying signal — undo, redo, manual edit all
arrive as `didChange` notifications. Server-side reconciliation:

1. Compute `Document.diff` (sentence-level common-prefix split).
2. Determine divergence sentence_id.
3. **`proof.autoReconcile: true | false`** workspace setting (default
   `true`):
   - `true`: revert primary to last common-prefix sentence_id; drop
     map entries past it; emit `easycrypt/proof/stateChanged`.
   - `false`: leave primary state put; emit
     `easycrypt/proof/diverged` notification (§ 12.1) so editor can
     render diverged-state highlighting; user reconciles
     explicitly via context menu.

### 12.1 `easycrypt/proof/diverged` — server → client

Emitted when `autoReconcile: false` and a `didChange` invalidates
state ahead of cursor.

```json
{
  "method": "easycrypt/proof/diverged",
  "params": {
    "uri": "file:///...",
    "ranges": [
      { "start_sentence_id": "...", "end_sentence_id": "...",
        "divergence_kind": "edit" | "insert" | "delete" }
    ]
  }
}
```

Editor renders background tint on diverged ranges; right-click
context menu offers `proof/reconcile` (revert to common prefix) or
`proof/continue` (dismiss banner; state remains diverged until next
edit clears it).

## 13. Multi-Document Workspaces

PoC: single workspace folder. Multi-folder logical-merge (single
workspace per daemon, all folders' load paths concatenated) is v1.
Per-folder isolation (cross-folder sessions) is v1+ when EC packages
land.

Server declares in `initialize` response:

```json
"workspace": {
  "workspaceFolders": {
    "supported": false,
    "changeNotifications": false
  }
}
```

Client offering multiple folders gets only the first one
recognized; others silently ignored. v1 lifts this.

## 14. Errors

LSP-standard error responses; code mapping for our typed errors:

| Code | Numeric | Use |
|---|---|---|
| `RequestCancelled` | -32800 | Cancelled via `$/cancelRequest` |
| `MethodNotFound` | -32601 | Unknown method (LSP standard) |
| `InvalidParams` | -32602 | Bad params (LSP standard) |
| `StaleCas` | -32001 | CAS mismatch on mutating op |
| `UnknownSentenceId` | -32002 | Target sentence_id not in document |
| `LaxRangeInvalid` | -32003 | Lax mode validation failure (post-PoC) |
| `SessionNotFound` | -32004 | `attachTo` referenced unknown session |
| `BusyExclusive` | -32005 | Per-surface single-client constraint hit (PoC) |
| `IncompatibleClient` | -32006 | Client version below `minClientVersion` |
| `BudgetExceeded` | -32007 | Per-request budget exhausted |
| `Internal` | -32603 | Bug; paired with transcript event |

Error `data` carries the typed payload from `doc/tooling-protocol.md`
§ 6.

## 15. Workspace Configuration

Client provides via LSP `workspace/configuration` request.

| Setting | Type | Default | Notes |
|---|---|---|---|
| `proof.fileMode` | string | `"preservation"` | preservation \| realtime |
| `proof.realTimeReload` | string | `"instant"` | instant \| prompt; only when fileMode=realtime |
| `proof.cachePolicy` | string | `"lax"` | lax \| strict |
| `proof.goalsCacheBudgetMB` | int | 64 | Per-workspace cache budget |
| `proof.recoveryStrategy` | string | `"halt"` | Default for `execToPoint` if unspecified |
| `proof.autoReconcile` | bool | `true` | Auto-revert on didChange divergence |
| `proof.debounceMs` | int | 200 | didChange→ANALYZE-JSON debounce |
| `proof.maxExecMsPerSentence` | int \| null | null | Daemon-wide per-sentence time budget; null = unbounded |
| `proof.speculation` | bool | `true` | Phase 5.5 speculative compilation |
| `proof.speculationBudgetMs` | int | 100 | Phase 5.5 |
| `proof.bulletSemantics` | string | `"lenient"` | strict \| lenient \| off (when EC-core bullets land) |

## 16. Capability Reservation (Schema Slots Pinned, Impl Deferred)

Pinning here prevents wire churn when these features land:

- **Diagnostic.cascade_of** — pinned; populated when ANALYZE-JSON
  v1 cascade tagging lands.
- **`proof/goals` provenance field** — pinned with values
  `fresh | cached | lax_admitted`; cache fills when Phase 5.0 ships.
- **CAS field on all state-mutating responses** — pinned;
  populated when Cas module lands.
- **`recoveryStrategy` parameter** — pinned; `best_effort_admit`
  uses focused-admit-only until EXEC-JSON v0.1 enables structural
  catalog.
- **`easycrypt/proof/admitChain`** notification (post-Phase-4):
  ```json
  {
    "method": "easycrypt/proof/admitChain",
    "params": {
      "uri": "...",
      "admittedSid": "...",
      "dependents": [ { "sid": "...", "lemmaName": "..." } ],
      "blastRadiusKnown": false
    }
  }
  ```
  Pre-Phase-4: best-effort textual reference search;
  `blastRadiusKnown: false`. Post-addition-2: real reverse-ref data;
  `blastRadiusKnown: true`.

## 17. Future Methods (Reserved, Not in PoC)

Pinned schema; implementation deferred:

- `easycrypt/proof/refreshDeps` — § 4.5 (ships in PoC).
- `easycrypt/proof/admitInPlace` — convert lax-admitted sentence to
  literal source `admit.` (v1+).
- `easycrypt/proof/saveMemoryVersion`,
  `easycrypt/proof/takeDiskVersion`,
  `easycrypt/proof/openMergeTool` — file-mode preservation actions
  (v1+).
- `easycrypt/proof/getDaemonState` — diagnostic snapshot (v1+).
- `easycrypt/proof/forceRecheck` — manual cache invalidation
  (v1+).

Standard LSP, deferred to Phase 5-full (depends on Phase 4):
- `textDocument/hover` — addition 10 dependent.
- `textDocument/definition` — single-file via PARSE-JSON; addition
  9 for cross-file.
- `textDocument/documentSymbol` — file-local via PARSE-JSON; full
  workspace via addition 2.

Cut for PoC entirely:
- `workspace/symbol` — addition 2 dependent.
- `textDocument/rename`.
- `textDocument/typeDefinition`.
- `textDocument/references`.
- `textDocument/semanticTokens`.

## 18. Conformance

Conformance suite (`tooling/conformance/`) drives the daemon over
the wire with a scripted LSP client. Coverage at Phase 5-core
acceptance:
- `initialize` handshake (capability negotiation correct).
- `didChange` → `publishDiagnostics` round-trip via ANALYZE-JSON.
- `easycrypt/proof/execToPoint` advance + state notification.
- `easycrypt/proof/revertToPoint` reverse + state notification.
- `easycrypt/proof/goals` query at known sentence_id.
- `$/cancelRequest` cancels in-flight `execToPoint`.
- `easycrypt/proof/stateChanged` ordering invariants.
- `easycrypt/server/restarted` after pragma restart.

Coverage extends per Phase as features land.
