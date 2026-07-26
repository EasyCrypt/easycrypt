# Session model — per-project sessions + multi-session axis

Companion design doc for the multi-session architecture. Pinned
2026-04-28 as point 14 of the 14-point beta-prep priority list.
Beta-1 gate.

## Problem

Today's `tooling/lib/proof_state.ml` is per-LSP-connection: one
primary `Ec_llm_session`, one document cache, one locked-region,
one current-sentence-id. This breaks for users who work on
multiple EC projects in a single VSCode window — opening a file
from Project B with Project A's load-paths active means failed
imports + broken proof state.

Plus the existing protocol commitments (multi-instance per
surface, `attachTo` for shared sessions) need to compose with
per-project sessions cleanly.

## Design — per-project keying as a sub-axis under per-connection

Each LSP / MCP connection owns a map of
`(project_root → ProofSession)`. A `ProofSession` is what was
previously the per-connection `Proof_state` — single primary
`Ec_llm_session`, locked region, current-sentence-id.

```
LSPConnection (or MCPConnection)
├── map: project_root → ProofSession
│   ├── /home/user/project_A/  →  ProofSession_A (one EC subprocess)
│   ├── /home/user/project_B/  →  ProofSession_B (one EC subprocess)
│   └── …
├── label-attached sessions (via `attachTo` parameter on
│   `initialize`): bypass per-project keying; all attached
│   connections see the labeled session's state regardless of
│   which project's file each has open.
└── document cache (URI → source/version), shared across sessions
    (URIs are global within the connection)
```

Combinations this supports:

| Scenario | Sessions |
|---|---|
| LSP1 + LSP2 on same file in same project | 2 independent (each connection has its own A-session) |
| LSP1 + LSP2 on different files in different projects | 4 (each connection has A-session + B-session) |
| LSP1 + MCP both attached to label `pair-debug` | 1 shared (via attachTo; project keying bypassed) |
| Single LSP, multiple files across A and B | 2 sessions in one connection's map |

## Module layout

- `tooling/lib/proof_session.ml{,i}` (renamed from `proof_state.ml`):
  the single-session struct — owns one `Ec_llm_session`, locked
  region, current sentence id, executed list, document
  subscriptions for the project's URIs.
- `tooling/lib/session_manager.ml{,i}` (new): the multi-session
  manager. Owns the `(project_root → ProofSession)` map per
  connection. Resolves URI → project_root via EC's auto-discovery
  (walks up looking for `easycrypt.project`); caches the
  resolution. Spawns / evicts sessions per the lifecycle policy
  below. `attachTo`-labeled sessions live in a parallel map.
- `tooling/daemon/lsp_server.ml`: per-connection switch hosts a
  `Session_manager.t`. Routes incoming requests by URI →
  session_manager → proof_session.

## Key resolution

- **Project root**: discovered via EC's existing
  `easycrypt.project` auto-discovery (walks up from the file's
  directory). Canonicalized via `Unix.realpath` to resolve
  symlinks + `.`/`..`. Cached.
- **URI → project_root cache**: invalidated on:
  - `easycrypt.project` file change (file-watcher).
  - File move (`didChangeWatchedFiles`).
  - Cache miss → re-walk.
- **Label keys (`attachTo`)**: bare strings, no canonicalization.
  Label maps in a separate `labeled_sessions: (string → ProofSession)`
  table. Connection's URI lookups check this table first if the
  connection was created with `attachTo: <label>`.

## Lifecycle

Configurable via `easycrypt-tooling.session.*` settings:

| Trigger | Action | Default | Setting |
|---|---|---|---|
| LSP connection close | drop all sessions for connection | always | n/a |
| Idle timeout | per-session, all docs closed for that project for >Tms | 2min | `idleTimeoutMs` |
| Soft cap exceeded | LRU evict on overflow | 4 active per connection | `maxActive` |
| Master toggle | disable eviction entirely (always-on) | false | `disableEviction` |
| Hot reload | `easycrypt.project` change → kill + respawn that project's session | always | n/a |

Hot-reload mechanism: file-watcher (using vscode's
`FileSystemWatcher` for the client side; daemon-side uses
`inotify` / `kqueue` if needed for non-vscode clients) watching
discovered `easycrypt.project` files. On change, the
`Session_manager` kills the corresponding session's EC subprocess
and respawns. Active session emits `stateChanged` + re-publishes
diagnostics. UI shows a "load-path changed, reloading…" toast.

## Cancellation interaction

Per `doc/cancellation.md § 6.2`: `easycrypt/proof/cancel { uri,
seq? }` resolves URI → project session → SIGINT to that session's
EC subprocess. Other projects' sessions unaffected. `seq` (if
provided) is request-id-scoped within that session's request log.

## File-switch latency

- **Cold spawn** (first open of a file in a previously-uncached
  project): ~1-2s as EC spawns + loads stdlib + project's
  declared imports. UI shows "loading project…" toast.
- **Warm switch** (file in already-cached project): instant
  (cached session).
- **Pre-warming**: post-beta optimization; not implemented for
  v1.

## Diagnostics

Published per-URI by the URI's owning session. URI partition
prevents cross-project bleed. Multi-root workspaces work
naturally — each root's project is independently sessioned;
diagnostics for a root's URIs come from that root's session.

## EC stdlib resolution

The bundled `theories/` location is conventionally relative to
the EC binary. EC's own self-discovery handles this. For the
`.vsix` packaging:
- **Auto-detect**: ec.native's startup discovery (current
  behavior).
- **Fallback setting**: `easycrypt-tooling.stdlibPath` if
  discovery fails (unusual install layouts, custom builds).

## Concurrent edits across projects

`didChange` is per-session: a change to a document in Project A
only triggers reconcile in Project A's session. Project B's
session is unaffected.

`didSave` cross-project interaction is **deferred** — the
question of whether saving a file in Project A should trigger
re-analysis in Project B (e.g., if B imports from A) is a
cross-project dependency-tracking concern that we don't address
in v1. Pinned for follow-up.

## Cross-project goal pane

The goal pane is bound to one URI at a time (existing
`goalsForUri`). URI → project_root → session resolution gives
the right session's goals. No cross-project bleed; no new wiring.

## Multi-session axis (`attachTo`)

The protocol's existing `attachTo` parameter on `initialize` (per
`doc/lsp-schema.md § 7`) bypasses per-project keying. When a
connection attaches to a labeled session:
- All requests from that connection route to the labeled session,
  regardless of the URI's project root.
- The labeled session is shared across all attached connections
  (pair-debugging, LSP+MCP collaboration, etc.).
- The connection's own per-project map is empty — labels take
  precedence.

This composes cleanly because `attachTo` is checked first in the
URI-resolution chain. Connections that don't pass `attachTo` get
the per-project default behavior.

## Deferred for post-beta

### (b) Reconnect-survival

Today, EC subprocesses are killed when the LSP connection closes.
A transient disconnect (network hiccup, client crash, restart)
loses the entire proof state — replay-from-scratch on reconnect.

Reconnect-survival would let the EC subprocess outlive the
connection: a `Session_pool` keyed by `(client_id, project_root)`
where `client_id` is a stable identifier surviving disconnects.
On reconnect, the new connection looks up the existing session
and re-attaches.

Significant lifecycle rework: pool ownership, persistence keys,
GC discipline (sessions outliving forever?), security
(authentication on reattach). Pinned post-beta.

### (c) Cross-connection sharing

Today, two LSP connections to the same project each get their
own session. For multi-client collaboration (LSP1 + LSP2 + MCP
all on the same proof, real-time co-editing), they'd want a
shared session with conflict resolution + concurrent-mutation
semantics.

The `attachTo` mechanism handles the EXPLICIT-share case (clients
opt in via label). Cross-connection AUTO-sharing — same project,
implicit share — needs:
- Conflict resolution policy (last-write-wins? operational
  transform? CRDT?).
- Per-client cursor / selection state vs shared proof state.
- Notification routing across attached clients.

Big design effort. Pinned post-beta.

## Test plan

- Open files in two distinct projects → verify each gets its own
  session (separate EC processes via `ps`).
- Edit `easycrypt.project` in project A → verify project A's
  session restarts; project B's untouched.
- Hit the soft cap (open files in 5 projects with `maxActive: 4`)
  → verify the LRU project's session evicts.
- Idle timeout → verify a session whose project's docs are all
  closed gets evicted after `idleTimeoutMs`.
- `attachTo` label sharing across two LSPs → verify both see
  the same state mutations.
- Cross-project diagnostic isolation → an error in project A
  doesn't appear on a project B URI.
