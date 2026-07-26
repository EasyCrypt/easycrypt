# Tooling Protocol Specification (Phase 0b deliverable)

Wire-level specification for the tooling daemon's LSP and MCP surfaces,
the `ec llm` REPL additions that support them, and the invariants every
client and server fiber must honor. Companion to
`doc/tooling-poc-plan.md` and `doc/tooling-roadmap.md`.

This document is normative where the plan is commitments: if the two
disagree, the plan states the commitment, this document states how to
satisfy it; divergence = bug.

**Status.** Living draft. Section headers present for every Phase 0b
deliverable. Empty sections carry `TODO:` with what remains.

---

## 1. Overview

The daemon (`ecd`) wraps one or more `ec llm` subprocesses and serves
two surfaces:

- **LSP** to editors (Neovim in PoC; others later), over JSON-RPC 2.0.
- **MCP** to LLM clients (Claude Code in PoC), over the Model Context
  Protocol stdio transport.

Both surfaces share:
- the session pool,
- stable sentence IDs for all addressing,
- a typed error taxonomy,
- a correlation-ID scheme that threads client request IDs through the
  daemon and session-backend layers,
- a CAS-token scheme for optimistic concurrency on state-mutating
  operations,
- a single internal publish point for state-change notifications,
- a structured transcript format.

## 2. Framing

### 2.1 `ec llm` → daemon (session backend)

The daemon speaks to each `ec llm` subprocess over stdin/stdout in the
line-based protocol defined by `src/ec.ml:407-867`, with additions
(4), (5), (6) from `UPSTREAM.md`:

- Replies end with the literal line `<END>`.
- `OK [uuid:N][ <event-tags>]` and `ERROR [uuid:N][ <event-tags>]` are
  reply headers.
- `<event-tags>` are zero or more space-separated bracketed tags
  (addition 4). Currently emitted: `[restarted]` on every reply whose
  processing caused EC to restart (covers both explicit `pragma
  restart.` and the implicit restart at the start of every `LOAD`); and
  `[loaded:<file>:<line>]` on successful `LOAD` replies.
- `NOTICE: <line>` frames stream out-of-band over stdout (addition 4),
  one per line of the source notification. They can appear anywhere in
  the stream — typically before the enclosing `OK`/`ERROR` header,
  since the notifier flushes during command processing — and are
  identifiable purely by the `NOTICE: ` prefix. Clients treat NOTICE
  lines as events, not reply body.
- Two sentence-parse meta-commands (addition 1) run EC's real parser
  over a document and return one JSON record per top-level form:
  `PARSE-JSON "<file>"` parses the named file, and the
  `<PARSE-BEGIN>` / `<PARSE-DONE>` multi-line frame parses the
  delimited body as EC source (symmetric with `<BEGIN>`/`<DONE>`).
  Payload shape:
  `{ "sentences": [
       { "class": "executable|doc_comment|directive|meta",
         "kind": <global_action-ctor | "DocComment" | "Undo" | "Exit">,
         "start_line": N, "start_col": N,
         "end_line":   N, "end_col":   N,
         "start_offset": N, "end_offset": N,
         "src": <verbatim substring> } ],
     "parse_error": { start_line, start_col, …, detail } | null }`.
  `meta` covers `P_Undo`/`P_Exit` — daemons synthesise these
  themselves and should filter them out. Unknown `global_action`
  constructors default to `executable` per § 15.3. Known quirk:
  EC's lexer reports the DOCCOMMENT token location as the closing
  `*)`, not the full comment span — the `src`/offsets on
  `doc_comment` sentences are correspondingly narrow. Fixing that
  is an EC-lexer change out of scope for addition 1.
- The `GOALS-JSON` meta-command returns a single-line JSON body
  (addition 3, v0). Payload shape:
  `{ "active": bool,
     "subgoal_count": N,
     "current_index": 0,
     "subgoals": [
       { "index": i,
         "hypotheses": [
           { "name": <id>, "kind":
             "var|mem|modty|hyp|abs_st",
             "pp": <type-or-formula text> } ],
         "conclusion_pp": <text> } ] }`. Hypothesis names and kinds
  are structured; types and conclusions are still pretty-printed
  text for v0 — enough for the daemon's outline/UI wiring and for
  LLM context, with the typed-AST lift deferred. `active: false`
  when no proof is open or when the active proof uses `PSNoCheck`.
- Every `ERROR` reply carries an `ERROR-JSON: <json>` line immediately
  after the header (addition 8).
- Every `OK` reply carries an `OK-JSON: <json>` line immediately after
  the header (addition 15), symmetric with ERROR-JSON. v0 payload is
  `{}`; EXEC-JSON replies (addition 13) carry
  `{kind, command_kind, command_name}` and addition 9 populates
  `print`/`locate`/`search` results here. Clients must strip this
  line from the reply body when decoding.
- Two ANALYZE-JSON entry points (addition 14, v0): `ANALYZE-JSON
  "<file>"` for files and `<ANALYZE-BEGIN>` / `<ANALYZE-DONE>` for
  inline buffers (symmetric with PARSE-JSON's framing). Stateless on
  the EC side — runs against a fresh scope, so the live primary's
  state is untouched. Payload shape:
  `{ "sentences": [ <PARSE-JSON sentence shape> ... ],
     "diagnostics": [
       { "sentence_index": N | null,
         "enclosing_scope":
           { "kind": "proof|theory|section",
             "opener_sentence_index": N } | null,
         "code": "ParseError|TypeError|TacticFailure|Internal",
         "phase": "parse|typecheck|tactic|protocol|unknown",
         "location": { "file":..., "start_line":..., ... } | null,
         "detail": "<pretty-printed error text>" } ] }`. Diagnostics
  are anchored by the 0-based [sentence_index] into [sentences[]];
  daemon resolves to its own [sentence_id] via the matching `src`
  field. v0 stops on the first parse error (parse-recovery + cascade
  tagging deferred to v1; see `UPSTREAM.md` § 14).
  `enclosing_scope` (addition 14, scope-tagging extension): textual
  scope a diagnostic sits in, computed by an opener/closer stack
  walked alongside the dry-run pass. Openers: `Gaxiom { PLemma None }`
  / `Grealize { pr_proof = None }` (proof), `GthOpen` (theory),
  `GsctOpen` (section). Closers: `Gsave _` (proof, any of `qed.`/
  `save.`/`abort.`/`admit.`), `GthClose`, `GsctClose`. Stack updates
  are textual — push/pop happen regardless of whether EC accepted
  the sentence — so a failing `qed.` still ends the textual proof
  for diagnostic-attribution purposes. `null` at the top level. v0
  scope-tagging only; cascade tagging across scopes (downstream
  errors that reference a failed-scope's introduced names) remains
  deferred to addition 14 v1.
  **Synthetic-abort recovery (addition 14, Tier-2 wrapper)**: when
  a proof closer (`Gsave _` — `qed.`/`save.`/`abort.`/`admit.`)
  raises during the dry run, EC's scope still considers the proof
  open and every subsequent top-level sentence errors with "cannot
  process [...] inside a proof script" — drowning real diagnostics.
  `analyze_to_json` injects a synthetic `Gsave \`Abort` at the
  closer's location to force-discard the broken proof state, so
  post-`qed.` sentences process at the outer scope and produce
  their real diagnostics. Replaceable by a typed
  `EcScope.recover_to_outer_scope` API when the EcEnv/EcSection
  redesign lands; wire shape unaffected by the swap. See UPSTREAM.md
  § 14 for the Tier-2 marker.
- The `EXEC-JSON <json>` meta-command (addition 13) accepts a
  single-line JSON payload:
  `{ "kind":"tactic"|"directive", "name":<string>, "args":[Arg,...] }`
  where each `Arg` is one of:
  `{"kind":"qname","value":<string>}`, `{"kind":"int","value":<int>}`,
  `{"kind":"flag","value":<string>}`, `{"kind":"text","value":<string>}`.
  Response uses the normal `OK`/`ERROR` + OK-JSON/ERROR-JSON envelope.
  Unsupported command names or arg shapes return `ERROR-JSON.code =
  "UnsupportedExecJson"`; malformed JSON returns `MalformedExecJson`.
  v0 covers tactics `apply`, `exact`, `elim`, `case`, `rewrite`,
  `move`, `generalize`, `clear`, `reflexivity`, `trivial`,
  `assumption`, `congr`; directives `print`, `locate`, `search`,
  `pragma`. Payload shape:
  `{ "code": "<ParseError|TypeError|TacticFailure|Internal>",
     "phase": "<parse|typecheck|tactic|protocol|unknown>",
     "location": { "file": <string|null>, "start_line": N,
       "start_col": N, "end_line": N, "end_col": N } | null,
     "detail": "<pretty-printed error text>" }`. The PoC classifier is
  intentionally shallow: EC's typing / parse / lex / `HiScopeError` /
  `TcError` exceptions map to their obvious codes; everything else —
  including LOAD-level protocol errors with no originating exception —
  falls through to `Internal`. Daemon-owned codes from § 6
  (`StaleCas`, `PoolExhausted`, `BudgetExceeded`, …) are synthesized
  daemon-side, not emitted by `ec llm`.
- Multi-line input is framed with `<BEGIN>` / `<DONE>` (or
  `<PARSE-BEGIN>` / `<PARSE-DONE>`) and preserves the **raw**
  content of each line — no leading/trailing whitespace trimming
  (addition 5, refined). Byte offsets reported back by
  PARSE-JSON (§ 15 / addition 1) therefore match the caller's
  original source buffer one-for-one, so client-side splicing
  (edit, insert, delete) can use the reported offsets directly.
- The `READY` handshake carries a `[proto:N]` tag advertising the LLM
  REPL protocol version (addition 6). Concretely: `READY [uuid:0]
  [proto:1]`. The daemon fails the handshake with `ProtocolMismatch`
  (§ 6) if `N < minEcLlmVersion` (§ 11). `N` bumps in lock-step with any
  wire-visible protocol change.

### 2.2 LSP surface

JSON-RPC 2.0 with LSP's `Content-Length` framing, stdio or socket
transport. Transport is abstract (PoC stdio only); the wire format is
unchanged across transports.

### 2.3 MCP surface

MCP stdio transport, JSON-RPC message shape per the MCP specification.
Tool invocations are modeled as `tools/call` requests; server-initiated
state-change events as `notifications/*`.

### 2.4 Structure coverage — pp-text inventory

Authoritative list of leaf fields in `ec llm`'s structured JSON that
are pretty-printed strings instead of typed AST. Full-AST serialisation
is deferred post-PoC (see PoC-era commitments below); the wire pivot
is additive — add `"ast"` alongside `"pp"` and bump `[proto:N]` — so
schema design, not compatibility, is the real cost. **Rule: every new
EC→JSON endpoint updates this table in the same PR.**

| Endpoint (addition) | Field | Current form | Pivot note |
|---|---|---|---|
| `GOALS-JSON` (3) | `subgoals[].hypotheses[].pp` for `kind=var` | `EcPrinting.pp_type` output | Typed `EcAst.ty` serializer. |
| `GOALS-JSON` (3) | `subgoals[].hypotheses[].pp` for `kind=hyp` | `EcPrinting.pp_form` output | Typed `EcAst.form` serializer — largest schema. |
| `GOALS-JSON` (3) | `subgoals[].hypotheses[].pp` for `kind=mem` | `EcPrinting.pp_memtype` output | `EcMemory.memtype` serializer. |
| `GOALS-JSON` (3) | `subgoals[].hypotheses[].pp` for `kind=modty` | stub `"<module type>"` | Needs `pp_mty_mr` + publisher-or-struct; currently opaque. |
| `GOALS-JSON` (3) | `subgoals[].hypotheses[].pp` for `kind=abs_st` | stub `"<abstract statement>"` | Needs `EcModules.abs_uses` serializer. |
| `GOALS-JSON` (3) | `subgoals[].conclusion_pp` | `pp_form` output | Same serializer as hypothesis-hyp. |
| `ERROR-JSON` (8) | `detail` | pretty-printed exn text | Arguably stays pp: already typed by `code`/`phase`; `detail` is the human story. Optional: add structured `payload` per code (e.g., `TypeError` could carry expected/actual types). |
| `PARSE-JSON` (1) | `sentences[].src` | verbatim substring | Not pp-text; daemon uses for hashing. No pivot planned. |

Other additions that will add pp-text fields when they land (track
here at landing time):

- **Addition 9** (structured `print`/`locate`/`search`): each result
  will have a `kind`-tagged envelope; the rendered signature / body
  is expected to start as pp-text.
- **Addition 10** (hover / type-at-point): the resolved identifier's
  `type` field is a candidate to start as pp-text.
- **Addition 11** (SMT counter-example): `model` values are the prime
  candidate — Why3 already returns structured terms, so this one may
  land typed from day one.
- **Addition 2** (declaration dump): each entry's signature/body
  starts as pp-text.

## 3. Addressing — stable sentence IDs

Every reference to a position in a document uses a **stable sentence
ID**, not a line/column range. Sentence IDs are:

- Computed daemon-side from `(content-hash, structural-path)` of the
  parsed sentence. Structural path is the chain of containing
  `theory`/`section` blocks plus the zero-based ordinal within its
  parent.
- Stable under whitespace-only edits.
- Invalidated on `Restart`.
- Opaque to clients; comparison is equality only.

Line/column positions appear at two transport edges:
- LSP `textDocument/*` requests carry them because LSP is
  position-based; the daemon resolves them to sentence IDs on entry.
- `ec llm` source feeds are line-delimited because the REPL is
  line-based; the daemon generates the feed from `(document +
  overlays)`.

Inside the daemon, and in every persisted artifact (transcripts,
checkpoints, LLM-held state), only sentence IDs appear.

## 4. Correlation IDs

Every inbound request (LSP request, LSP notification with side effects,
MCP tool call) carries a client-assigned ID. The daemon:

- Threads the ID through all internal work on behalf of the request
  (pool acquisition, session exec, cancellation).
- Echoes it back on responses and on any asynchronous error or progress
  notification related to that request.
- Records the ID on every transcript event produced during the work.

The session backend drives each `ec llm` subprocess strictly half-duplex
per session: at most one outstanding `exec` per session at a time. A
cancel cannot race with an exec; cancellation is implemented as
SIGKILL + `Cancel.cancel` on the session switch (see plan §
"Correlation, cancellation, CAS").

## 5. CAS tokens

### 5.1 Shape

A CAS token is a 16-byte hex string (32 chars): the BLAKE2b-128 hash of
the ordered sequence of committed sentence IDs on the primary session
since the last `Restart`.

### 5.2 Usage

- Every state-mutating LSP/MCP request (`proof/execToPoint`,
  `proof/revertToPoint`, `proof/overlay/{set,clear}`, `exec_region`,
  `set_overlay`, `clear_overlay`) carries an optional
  `expectedCas` field.
- If present and mismatching the server-current CAS, the request fails
  fast with a `StaleCas` typed error (§ 6) containing the server-current
  CAS in the payload.
- Probes (`try_tactic`) and pure queries (`get_goals`, `search_lemma`,
  `get_document_symbol`) do *not* take a CAS; they operate on the
  current state as observed.

### 5.3 Client refresh contract

On receipt of `proof/stateChanged`, clients refresh their cached CAS
from the notification payload (§ 9.1). A client that never refreshes
will receive `StaleCas` on its next mutation and can recover by
re-issuing with the current CAS from the error payload.

Clients must not synthesize their own CAS tokens — only the daemon does.

## 6. Error taxonomy

Every error reply (LSP and MCP) carries a typed `code` plus a
human-readable `message`, plus an optional structured `data` payload.

| code | `data` fields | when |
|---|---|---|
| `ParseError` | `{ sentence_id?, location, detail }` | input rejected by EC parser |
| `TypeError` | `{ sentence_id, location, detail }` | EC type-checker rejects |
| `TacticFailure` | `{ sentence_id, goal, detail }` | tactic did not close / made no progress |
| `SmtTimeout` | `{ sentence_id, provers_tried, budget }` | SMT budget exhausted before close |
| `SmtCounterExample` | `{ sentence_id, model }` | SMT returned a model (non-closure) |
| `BudgetExceeded` | `{ kind: deadline\|tokens, spent, limit }` | per-request budget exhausted |
| `Cancelled` | `{ reason }` | explicit client cancel or supervisor cancel |
| `StaleCas` | `{ server_cas }` | CAS mismatch on state-mutating op |
| `UnknownSentenceId` | `{ sentence_id }` | request references a sentence the daemon doesn't know |
| `OverlayConflict` | `{ overlay_names: [string] }` | two overlays cannot compose |
| `SessionRestarted` | `{ cas, reason }` | session restarted mid-op; client must resync |
| `PoolExhausted` | `{ kind: lsp\|mcp\|spec }` | fairness quota saturated |
| `ProtocolMismatch` | `{ client_ver, server_ver, min_required }` | incompatible handshake |
| `Internal` | `{ detail }` | bug; always paired with a transcript event |
| `UnsupportedExecJson` | `{ detail }` | EXEC-JSON command name or arg shape not covered by the server's v0 schema |
| `MalformedExecJson` | `{ detail }` | EXEC-JSON payload failed JSON parse or missing required fields |

LSP maps `code` to JSON-RPC error `code` integers (see § 7); MCP carries
the typed code as a tool-result field because MCP tool errors are not
JSON-RPC errors.

## 7. LSP methods

TODO: per-method JSON-RPC examples. Inventory (standard / custom):

**Standard subset (PoC):**
- `initialize`, `initialized`, `shutdown`, `exit`
- `textDocument/didOpen`, `didChange`, `didClose`
- `textDocument/publishDiagnostics` (server notification)
- `textDocument/hover`
- `textDocument/documentSymbol` (file-local in PoC; workspace-wide
  in v1)
- `textDocument/definition` (single-file in PoC)
- `$/cancelRequest`, `$/progress`

**Custom (registered via `LSP_FEATURE`):**
- `proof/execToPoint` — request; mutating; takes `expectedCas`.
- `proof/revertToPoint` — request; mutating; takes `expectedCas`.
- `proof/goals` — request; read-only.
- `proof/overlay/set`, `proof/overlay/clear` — requests; mutating;
  take `expectedCas`.
- `proof/checkpoint`, `proof/revertCheckpoint` — requests; sugar over
  sentence IDs; mutating.
- `proof/stateChanged` — server notification; § 9.
- `server/restarted` — server notification; § 9.

Cut for PoC, planned for v1+: `workspace/symbol`, `textDocument/rename`,
`textDocument/typeDefinition`, `textDocument/references`,
`textDocument/semanticTokens`.

JSON-RPC error code mapping: reuse LSP reserved range where semantics
match (`-32601` method not found, `-32602` invalid params, etc.) and
allocate `-32001…` custom codes for the typed errors in § 6 (mapping
table TBD).

## 8. MCP tools

TODO: per-tool JSON schema for inputs and outputs.

Tool inventory:

- `get_goals` — returns structured goals at a sentence ID.
- `exec_region` — mutating; advances primary through a sentence-ID
  range; takes `expectedCas`.
- `try_tactic` — probe on scratch; returns resulting goals or error;
  never touches primary.
- `search_lemma` — workspace index query; may return empty if
  declaration dump hasn't populated.
- `get_document_symbol` — file-local outline.
- `set_overlay`, `clear_overlay` — mutating; sentence-ID-addressed;
  take `expectedCas`.
- `cancel` — cancels an in-flight correlation ID.

Every tool carries the typed error taxonomy (§ 6) on failure in the
tool-result payload.

## 9. Notifications

### 9.1 `proof/stateChanged`

Emitted on every primary-session state advance or revert. Payload:

```json
{
  "documentUri": "file:///path/to/file.ec",
  "cas": "<current CAS hex>",
  "currentSentenceId": "<opaque>",
  "seq": 42,
  "origin": { "kind": "lsp|mcp|daemon", "correlationId": "<string>" }
}
```

- `seq` is monotonic per document.
- `origin` identifies who caused the change; a client that originated
  the change still receives the notification (no client-side filtering
  in PoC).

### 9.2 `server/restarted`

Emitted when a session restarts (tagged event frame from
addition 4). Payload:

```json
{
  "documentUri": "file:///...",
  "reason": "user-requested|invariant-violation|session-crash",
  "newCas": "<fresh CAS>",
  "seq": 43,
  "clientMustReplay": true
}
```

Clients **must** honor `clientMustReplay` by replaying `didOpen` + last
known cursor before issuing further requests (§ 10).

## 10. Reconnect contract

### 10.1 What survives a client disconnect

- **Scratch sessions and overlays**: survive. A reconnecting client that
  previously created overlays receives an overlay survival list on
  reconnect (§ 11 capability handshake reply).
- **Primary session state**: survives.
- **MCP in-flight tool calls**: do *not* survive. They are cancelled on
  disconnect and not resumed. A client that wants
  resume-after-disconnect must drive re-submission itself.

### 10.2 What a client does on reconnect

1. Send `initialize` (§ 11). Handshake reply includes the current CAS,
   current sentence ID, and overlay survival list.
2. Replay `didOpen` for each document the client owns, at the document
   version the server currently reports.
3. Cache the CAS; begin normal operation.

### 10.3 What survives a session restart

- Sentence→uuid map: invalidated.
- Scratch sessions + overlays: dropped.
- Primary session: replaced (fresh).

Clients observe this via `server/restarted` (§ 9.2) and re-replay per
10.2.

## 11. Capability handshake

LSP `initialize` request additionally carries:

- `clientVersion`: client's daemon-protocol version.
- `clientCapabilities.proof`: `{ supportsOverlay, supportsProbe, … }`.

Server reply carries:

- `serverVersion`: daemon version.
- `minClientVersion`: minimum client version the server accepts.
- `minEcLlmVersion`: minimum `ec llm` protocol version this daemon
  requires; if the active session reports lower, daemon fails the
  handshake with `ProtocolMismatch`.
- `authField`: reserved, always `null` in PoC. Future TCP/WASM
  transports populate with auth context.
- `currentCas`, `currentSentenceId`, `survivedOverlays`: for
  reconnect.

MCP equivalent uses the MCP `initialize` request/response with the same
semantic fields in custom extension metadata.

## 12. Pub/sub fan-out — single-client per surface (PoC)

In PoC, every state-change event (§ 9) is published to the single
LSP connection and the single MCP connection. Concretely:

- The daemon has one internal publish point. No handler writes events
  to surfaces directly.
- Each connection has a bounded event queue (default 256 entries).
  Overflow disconnects the client with `PoolExhausted`-like shutdown
  (concrete code TBD).
- Events carry monotonic per-document `seq` and an `origin` record.
- The publish point also exposes `snapshot()` returning
  `{cas, goals, diagnostics, overlayStack}` at the primary's current
  sentence. Required for v1 late-join (snapshot + event tail), not
  used by PoC clients.

Multi-client semantics — per-client filtering, late-join replay,
coalescing, per-topic subscription — are deferred to v1. The publish
point is the v1 extension seam.

## 13. Artifact cache key

Forward-compatible stub; no-op in PoC (§ plan Phase 4).

Cache key tuple:
```
(statement_hash, env_hash)
```

where:

- `statement_hash` = BLAKE2b-128 of the canonical form of the lemma
  statement (deterministically printed sequence of declarations the
  statement depends on). Concrete canonicalization is a 0b TODO.
- `env_hash` = BLAKE2b-128 of the sequence of
  `(sentence_id, sentence_kind, effective_pragma_stack)` on the primary
  session up to the lemma's defining position.

Value shape:
```
{
  proved: bool,
  provers_used: [string],
  timing_ms: int,
  artifact_path: string | null
}
```

Store is content-addressable on the key tuple. Future distributed
cache shares the same key shape.

## 14. Transcript event taxonomy

Structured JSON-per-line. Every line:
```json
{ "t": <monotonic micros since daemon start>,
  "cid": "<correlation id or null>",
  "kind": "<event kind>",
  "payload": { ... } }
```

Event kinds:
- `request.in` — inbound LSP/MCP request; payload is the full request.
- `request.out` — outbound reply; payload is the reply.
- `notification.out` — server-initiated notification.
- `session.spawn`, `session.exec`, `session.reply`, `session.kill`,
  `session.restart` — subprocess-level events; payload includes
  session label and raw bytes reference.
- `session.crashed` — subprocess exited unexpectedly (not via
  daemon-initiated `close`/`cancel`). Payload:
  `{label, exit_kind: "exit:N" | "signal:N"}` where `N` in
  `signal:N` is the POSIX signal number. Emitted by the per-session
  supervisor fiber forked at session start; the daemon translates
  this into a `Session_crashed` publish event so surfaces and the
  pool can react without waiting for the next caller's `exec` to
  discover the dead pipe.
- `pool.acquire`, `pool.release`, `pool.evict` — pool lifecycle.
- `overlay.set`, `overlay.clear`, `overlay.apply`.
- `cas.issue`, `cas.stale_reject`.
- `invariant.uuid_mismatch` — uuid-invariant tripped; always paired
  with a following `session.restart`.
- `log.info`, `log.warn`, `log.error` — structured log entries.

Transcripts replay offline via the Phase 9 replay driver: the driver
reads the JSON stream and drives a fresh backend instance with the
recorded session.spawn/exec/reply sequence, asserting that daemon
outputs match.

## 15. REPL directive enumeration

### 15.1 Top-level REPL forms (consumed by the splitter)

Per the current EC grammar, the top-level forms the REPL accepts are
four (see `src/ecParser.mly:3967-3990`):

| Form | Classification | uuid effect |
|---|---|---|
| `P_Prog` wrapping `global_action` | depends on inner (see 15.2) | depends |
| `P_Undo N` | *meta* — not fed to `ec llm` by the daemon | none |
| `P_Exit` | *meta* — not fed to `ec llm` by the daemon | none |
| `P_DocComment` | `doc_comment` | advances uuid |

The daemon synthesizes `P_Undo`/`P_Exit` from its own intent (revert,
shutdown) rather than forwarding them from client input, so they don't
appear as sentence classes.

### 15.2 `global_action` classification

Classification reflects the state **after EC addition 7** (read-only
queries no longer advance uuid). For pre-addition behavior, see § 15.4.

**`executable` (uuid-advancing):**

- Theory-level: `GthOpen`, `GthClose`, `GthRequire`, `GthImport`,
  `GthExport`, `GthClone`, `GthClear`, `GthAlias`.
- Module/section: `GModImport`, `GsctOpen`, `GsctClose`, `Gmodule`,
  `Ginterface`.
- Declarations: `Gtype`, `Gsubtype`, `Gtycinstance`, `Goperator`,
  `Gexception`, `Gprocop`, `Gpredicate`, `Gnotation`, `Gabbrev`,
  `Greduction`, `Gaxiom`.
- Proofs: `Gtactics`, `Gsave` (qed/abort), `Grealize`.
- Hints / rewrite DB: `Gaddrw`, `Ghint`.
- Config that changes future behavior: `Gprover_info`, `Goption` (the
  `pragma +x` / `pragma -x` / `pragma x = N` grammar forms).

**`directive` (non-uuid-advancing — both pragmas and read-only queries):**

- Pragmas: `Gpragma` (the plain `pragma <name>` form only).
- Queries (post-addition 7): `Gprint`, `Gsearch`, `Glocate`, `GdumpWhy3`.

Note: `Gtcdump` looks like a query but actually processes tactics
(`EcScope.Tactics.process` at `ecCommands.ml:708-710`), so it stays
in `executable`.

### 15.4 Compatibility note (pre-addition-7 behavior)

Before EC addition 7 lands, query forms (`Gprint`, `Gsearch`, `Glocate`,
`Gtcdump`, `GdumpWhy3`) advance uuid via `` `Fct `` in
`src/ecCommands.ml:784-788`. The daemon's uuid-invariant must tolerate
both states during the transition: log but do not abort if a directive-
classed sentence advances uuid by 1 (pre-addition EC). Once addition 7
is merged and the tooling minimum `ec llm` version bumps past it
(addition 6), the invariant tightens to the post-addition form.

### 15.3 Notes for the splitter / addition (1)

- Classification is by the parsed `global_action` variant returned by
  `EcIo.xparse`; not by the input token stream. The splitter cannot
  distinguish `pragma foo` (directive) from `pragma +foo` (executable)
  without full parse.
- If EC later grows new `global_action` forms, addition (1)'s JSON
  output names the constructor so the daemon can adopt new classes
  without a new EC release. Unknown constructors default to
  `executable` (conservative: expect uuid advance).

## 16. uuid invariant (precise statement)

After every daemon-issued `exec` of a parsed sentence *s*:

- If `class(s) ∈ { executable, doc_comment }`: `replied_uuid == last_uuid + 1`.
- If `class(s) == directive`: `replied_uuid == last_uuid`.
- If EC replies with `RESTARTED` tag (addition 4): the invariant is
  suspended for this reply; the daemon invalidates state per § 10.3.
- Any other case is an invariant violation: daemon aborts the session,
  emits `server/restarted` with `reason: "invariant-violation"`.

Clients do not see the invariant directly; they see its enforcement as
`server/restarted` when it fires.
