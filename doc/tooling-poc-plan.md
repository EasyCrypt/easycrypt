# EasyCrypt Tooling — PoC Implementation Plan (v6)

Companion to `doc/tooling-roadmap.md`. Phase sequencing for the PoC.
Time estimates omitted. Commitments and invariants live here; concrete
formats and signatures live in the Phase 0b protocol doc.

> **Status:** project is in **beta-prep mode** as of 2026-04-28.
> The PoC phase sequencing below covers the ground that's been
> covered. The 14-point beta-prep priority list — what closes the
> initial-beta-1 deliverable + what iterates immediately after —
> is pinned in `STATUS.md § Workflow status` and detailed in
> `HANDOFF-VSCODE-FIRST.md`. Cross-cutting design docs:
> - `doc/cancellation.md` — `proof/cancel` v1 + future fiber rework
> - `doc/session-model.md` — per-project sessions, multi-session axis

## Scope

One modular OCaml daemon exposing LSP (to editors) and MCP (to LLM
clients) surfaces over a shared subprocess session pool wrapping
`ec llm`. Neovim 3-pane plugin + Claude Code in terminal split as
primary clients; TUI as additive side-product. Monorepo under
`tooling/` during PoC; split and upstream EC additions after.

---

## EC-side additions (tracked in `UPSTREAM.md`)

1. **Sentence-granular parse endpoint** — JSON boundaries + ranges via
   `EcIo.xparse`; sentences classified as `executable`, `doc_comment`,
   `directive`.
2. **Declaration dump** — lemmas / operators / modules / types;
   schema covers functors, abstract theories, clones.
3. **Structured goals** — JSON form alongside pretty-printed.
4. **Tagged event frames** — `NOTICE`, `RESTARTED`, future events;
   covers explicit `Restart` and `LOAD` implicit restart; notices
   emitted in real time.
5. **`<BEGIN>`/`<DONE>` newline preservation** (`src/ec.ml:762-764`).
6. **Minimum protocol version** advertised by `ec llm` at handshake.
7. **Read-only queries don't advance uuid** — `Gprint`, `Gsearch`,
   `Glocate`, `GdumpWhy3` switch to `` `State ``; query forms join
   the `directive` class. `Gtcdump` is excluded — it runs tactics
   despite the name and does mutate state.
8. **Structured error output** — JSON event frame next to the pretty-
   printed `ERROR` line; feeds typed-error taxonomy directly.
9. **Structured `print` / `locate` / `search`** — JSON list results
   alongside pretty-printed text; backs LSP hover/definition/symbol.
10. **Hover / type-at-point endpoint** — given
    `(sentence_id, cursor_offset)`, return kind + name + type +
    defining location as JSON.
11. **Structured SMT counter-examples** — Why3 model exposed as a
    `{ var: value }` structure when SMT returns a model.
12. **Drop dead `break` parameter on `EcCommands.process`** — trivial
    cleanup.
13. **Structured execution (`EXEC-JSON`)** — accept a JSON-encoded
    EC command (tactic, directive) and dispatch it (v0: render-and-
    parse through the text path; v1+: direct AST dispatch per tactic).
    Substrate for semantic edit mode and structured proof-tree
    transcripts. **Landed (v0).**
14. **Batch diagnostics with parse recovery (`ANALYZE-JSON`)** —
    stateless meta-command that reports every parse/type/tactic error
    in a document with cascade tagging; precondition for real LSP
    diagnostics. **Landed v0 + scope-tagging extension + Tier-2
    synthetic-abort recovery** (failing proof closer triggers a
    synthetic `Gsave \`Abort` so subsequent sentences process at the
    outer scope). Cascade tagging across scopes still deferred to v1.
15. **Structured success output (`OK-JSON`)** — symmetric envelope for
    addition 8; carries a post-exec typed payload slot. **Landed.**
16. **`PARSE-JSON` `start_offset` at first token** — move
    `start_offset` past leading separator whitespace so every
    byte-level splicer can stop reimplementing the scan. **Landed.**

Phase 0b lands (1), (3), (4), (5), (6), (7), (8), (12), (15).
(13) and (16) bundle with Phase 3; (9) rides addition 13's schema
envelope work. (2), (9), (10) land with Phase 4. (14) is a Phase 5
precondition. (11) lands later (Phase 5/6 window).
See `UPSTREAM.md` for authoritative status.

---

## Extension points — two registries, two abstraction-only kinds

Proof-semantic and surface extensions have different lifetimes and
state coupling; they register separately. Concrete signatures are a 0b
deliverable (see below).

- **Surface plugins** (stateless dispatch): `LSP_FEATURE`, `MCP_TOOL`.
  Handlers receive a `Surface_ctx` (correlation ID, cancel token,
  read-only document snapshot at a sentence ID, budgets).
- **Proof-semantic plugins** (stateful, session-adjacent):
  `OVERLAY_KIND`. Future slots: `CACHE_FEEDER`, `ANALYSIS_PLUGIN`.
- **Abstraction-only** (module-type abstracted; one impl in PoC; future
  impls drop in without registry changes): `TRANSPORT` (stdio in PoC),
  `SESSION_BACKEND` (`ec llm` subprocess in PoC).

**Session interface** (narrow, unchanged): `exec`, `revert_to(state_id)`,
`goals`, `cancel`, lifecycle. No `checkpoint` (sugar over `revert_to`);
no `-nosmt` (pragma injection if needed).

---

## Cross-cutting commitments

### Addressing

Every position reference — protocol, overlays, transcripts, checkpoints,
reconnect replay, LLM-held state — uses **stable sentence IDs**.
Line/col appears only at transport edges. IDs = content hash +
structural path; survive whitespace edits; invalidated on `Restart`.

### Speculative state — two shapes, one pool

- **Overlay**: transformed-source compilation on a scratch session;
  forks its own sentence→uuid map; primary untouched.
- **Probe**: ephemeral `exec` on a scratch at primary's current uuid;
  no source rewriting. `try_tactic` is a probe.

Both consume the scratch pool. **Fairness**: per-kind static
reservation (`K_lsp`, `K_mcp`, `K_spec = 0` reserved for roadmap-v1
speculative background compilation) with `K_lsp + K_mcp + K_spec ≤
pool_size` and `remainder = pool_size − sum(K_*)` shared. Concrete
property tested: queued LSP `didChange` starts within ≤ 2 probe
completions given `K_lsp ≥ 1`, with 10 probes in flight.
Starvation-freedom: under steady MCP load, LSP `didChange` p99 latency
below a threshold chosen from the 0a spike.

### Scratch lifecycle

Scratch sessions are daemon-owned and survive client disconnect.
Overlays survive client disconnect; MCP in-flight calls are cancelled
on disconnect and not resumed. On `Restart`, all scratch sessions are
torn down and their forked maps dropped.

### Correlation, cancellation, CAS — concrete mechanisms

- Client request IDs thread end-to-end; each session is driven
  half-duplex by its owning fiber.
- **Cancel = SIGKILL + `Cancel.cancel` on the session switch.**
  The session fiber owns its fd exclusively for its lifetime; pool-
  replace allocates a fresh fiber + fd, never hands an existing fiber
  a replaced fd (rules out the fiber-between-reads race). Cancellation
  reaches the fiber either as an EOF from its pending `Eio.Flow.read`
  or as a switch-cancel; either path yields `Error Session_restarted`
  and releases the pool slot.
- **uuid-invariant**: for sentences of class `executable` or
  `doc_comment`, EC's replied uuid == (last-tracked uuid + 1) after the
  exec; for sentences of class `directive` (the `Gpragma` form; see 0b
  directive enumeration), uuid is unchanged. A `RESTARTED` event frame
  takes precedence over the invariant (expected path). Unexplained
  mismatch → abort session + emit `server/restarted`.
- **CAS token** = hash of the ordered sequence of committed sentence
  IDs on the primary since last `Restart`. Clients refresh on
  `proof/stateChanged`; stale-CAS is a typed error.

### Restart and reconnect

Detected via the tagged event frame (addition 4), never output-string
matching. Daemon invalidates sentence→uuid map and all scratch state;
emits `server/restarted`; clients replay `didOpen` + cursor per the 0b
contract.

### Event fan-out — simple now, forward-compatible

PoC implements a **single-client-per-surface** event model:
- Single internal publish point for all state-change events (no
  scattered writes); per-connection bounded queue; overflow disconnects
  the client.
- The publish point also exposes a `snapshot()` accessor returning
  current state (goals + diagnostics + overlay stack at the primary's
  current sentence ID). Required for v1 late-join semantics
  (snapshot + event tail), not just event replay; one-line contract
  now prevents retrofit.
- Events carry monotonic sequence number + origin; consumed in
  submission order.
- Multi-client semantics (filtering, late-join = snapshot + tail,
  coalescing, per-topic subscription) deferred to v1. The single
  publish point is
  the extension seam; v1 work adds filtering/replay there without
  touching emitters.

### Error taxonomy, transcripts, observability

Typed error enum (codes + payloads) is a 0b deliverable. Transcripts
are JSON-per-line with correlation IDs; event taxonomy in 0b. Logs are
structured and correlation-ID-keyed. Counters: cancellation, pool
eviction, SMT-kill, budget breach, uuid-invariant mismatch, fairness
preemption.

### Workspace ownership

The workspace is the sole authority on load path. Minimal workspace
(doc set + load path) ships in Phase 2; full promotion (cache,
symbols, discovery) in Phase 4. No `addidir` accumulation across
document lifecycle.

### Concurrency — Eio, cancellation proven in 0a

Constructs in use: `Switch`, `Cancel`, `Fiber.fork_daemon`,
`Eio.Flow`. The 0a spike exercises three SMT scenarios end-to-end:
success, cancel-mid-solve, two concurrent — adapter correctness under
cancellation, not merely "path presence."

### Demo CLI as living harness

Introduced in Phase 1; grows each phase. Every phase's acceptance
includes a CLI-driven path. CLI exercises the session API ahead of
LSP/MCP.

---

## Test strategy (classes stated once)

- **Unit** — splitter, pool, cancellation, transport framing.
- **Property** — diff laws; overlay stack algebra; CAS staleness
  rejection + refresh recovery.
- **Differential oracle** — per corpus file, compare structured goals
  at every sentence ID between cold full-load and edit-then-re-feed.
- **Stress** — cancellation mid parse/elaborate/SMT; fairness as
  specified above.
- **Conformance** — scripted LSP client; MCP tool goldens; tagged-
  event-frame suite (NOTICE during long exec arrives before OK;
  RESTARTED inside error path; framing survives embedded `<END>`).
- **Integration** — end-to-end via transcripts; reconnect convergence;
  overlay+Restart interaction; stale-pid recovery after daemon kill.
- **Fuzz** — REPL framing edges (bare CR, UTF-8 boundaries).
- **Boundary lint** — daemon imports restricted by allowlist; CI
  enforced.

---

## Sequencing

**Updated 2026-04-26 — VSCode-first ordering** (see STATUS.md for the
detailed staged plan that backs this).

```
0a (rolled into 1) → 0b → 1 → 2 → 2.5 → { 3-substrate ∥ 4 ∥ 4.5 }
                                       → 5-core (LSP server + min methods)
                                       → 5.0 (cache + replay-to-sid + Cas)
                                       → VSCode demo (Milestone 2)
                                       → 5.5 (speculative compilation)
                                       → 5-full (hover/def, gated on 4)
                                       → 6-core / 6-full
                                       → 7 (Neovim, after 5-full + 6-full)
                                       → 9 (polish + docs)
                                       → 10 (merge polish, see below)
```

The OVERLAY_KIND substrate that was originally Phase 3's deliverable is
**deferred to v1+**. Lax-as-overlay subsumed by cache-policy lax (see
STATUS.md "Reframed: lax mode"); other overlays (Time_budget,
Disable_smt, Admit_subtree) deferred or reframed as daemon settings.

Parallelism is partial. Load-bearing caveats:

- **EC-core parser serialization.** Additions 13 (Phase 3) and 14
  (Phase 5-core) both live in `src/ecIo.ml`/`src/ec.ml` and serialize
  at the `ec-core:` commit boundary even when daemon work parallels.
  Both already landed (v0).
- **Phase 5 is staged.** Phase 5-core (LSP lifecycle + diagnostics via
  addition 14 + custom proof methods over sentence-IDs) unblocks after
  Phase 2.5. Phase 5-full (`hover`, `documentSymbol`, `definition`)
  additionally requires additions 2/9/10 from Phase 4. Phase 5
  acceptance has two gates, not one.
- **Phase 6 is staged the same way.** 6-core (`try_tactic`,
  `get_goals`, `exec_region`, `cancel`) runs on the Phase 1 session
  API alone. `search_lemma` stubs until Phase 4 (addition 2) lands;
  that's 6-full. Note: `set_overlay`/`clear_overlay` MCP tools dropped
  from PoC scope (overlays deferred).
- **Critical path is Phase 7-ward.** The shipped PoC (Neovim plugin)
  threads through 5-full + 6-full. Phases 3 and 4 enrich features
  independently.

Other notes:

- Phase 1 includes the replay driver (pulled from Phase 9).
- Phase 2 absorbed daemon discovery library and session supervisor
  fiber; Phase 2.5 (new) wires the discovery into a long-running
  `ecd daemon` subcommand.
- Phase 3 substrate (EXEC-JSON v0 + addition 16) landed. Overlay
  primitive deferred to v1+ (lax-as-overlay subsumed by cache policy).
- Phase 4 (former Phase 4b): symbol sources from additions 2/9/10 and
  the workspace-index layer above them.
- Phase 4.5: cross-file invalidation. Gated on addition 2.
- Phase 5.0 (new): cache + replay-to-sid + Cas — substrate for
  fast iteration. Originally framed as v1 optimization; **elevated
  to PoC foundation** because cache-policy lax replaces overlay-based
  failure handling.
- Phase 5.5 (new): speculative background compilation. Sits on top of
  Phase 5.0 cache substrate.
- Phase 8 (TUI client) was additive/droppable; already de-facto
  shipped (`ecd tui` over `Repl_core`).
- **Phase 10 reframed under merged-binary.** Original "tooling repo
  split + upstream PR set" no longer applies — daemon merging into EC
  is the long-term direction. Phase 10 collapses to: TCB lint, `ec daemon`
  subcommand promotion, capability-negotiation removed as redundant
  (closed-loop), single-binary install docs. See "Merged-binary
  architecture (working notes)" below.

---

## Phases

### Phase 0a — Scaffolding

`tooling/` subdir, dune, Nix flake extension, Eio pinned (OCaml 5.x).
`UPSTREAM.md` seeded; commit-prefix convention; boundary-lint allowlist
file + CI. Tree-sitter pinned-CI lands with the grammar workstream,
not here.

The concurrency-correctness spike and the pool-sizing measurements
originally scoped here roll into Phase 1 acceptance — running them
against the real session backend is the same test with higher
fidelity than a throwaway harness, and Phase 1 has to ship them as
acceptance criteria anyway.

**Acceptance**: scaffolding in place; boundary lint passing.

### Phase 0b — Protocol design + EC additions (1, 3, 4, 5, 6, 7, 8, 12)

Protocol doc is a checklist deliverable, not prose:

- JSON-RPC examples for every LSP method (standard + custom).
- MCP tool schemas.
- **Compilable `.mli` stubs + no-op impls** for `Session`, `Surface_ctx`,
  `LSP_FEATURE`, `MCP_TOOL`, `OVERLAY_KIND`, plus the publish-point
  (`publish` + `snapshot`) — compiled against a stub session.
- **Composition smoke tests**: a trivial echo `MCP_TOOL` and a trivial
  admit-first-sentence `OVERLAY_KIND`, each exercising scratch-pool
  acquisition + cancel propagation + publish-point emission in one
  round-trip. This is the gate from "types named" to "contracts
  grounded" — type-check alone is theater.
- Typed error enum + payload shapes.
- Correlation-ID and CAS rules; client refresh contract; stale-CAS
  error code.
- `proof/stateChanged`, `server/restarted` shapes.
- Reconnect contract: what survives disconnect (overlays) vs doesn't
  (MCP in-flight); client replay steps.
- Capability handshake + minimum `ec llm` version + auth field reserved
  for future TCP.
- **Capability-negotiation schema (design now, implement at Phase 10).**
  Wire format for `[caps:...]` on `READY`; daemon-side `has_cap`
  predicate; feature-gate sites enumerated (today: `goals-json` on the
  `GOALS` fallback; post-Phase-3: `exec-json`; post-Phase-4:
  `decl-dump`, `print-json`, `hover-at-point`); handshake-failure
  message shape (`CapabilityMissing` from § 6). Implementation is
  deferred to Phase 10 per the closed-loop monorepo decision, but the
  schema is pinned here so Phase 10 doesn't redesign under time
  pressure.
- Artifact cache key tuple (`statement hash + env hash`).
- Transcript event taxonomy.
- Full enumeration of REPL directive tokens.
- Event fan-out contract: single-client-per-surface in PoC; extension
  seam documented for future multi-client.

EC additions (1), (3), (4), (5), (6), (7), (8), (12) land.

**Acceptance**: checklist complete; `.mli` stubs compile; eight EC
additions merged (1, 3, 4, 5, 6, 7, 8, 12); UPSTREAM.md updated.

### Phase 1 — Session core, registries, demo CLI

Both registries defined (core dispatches through them only). Subprocess
`SESSION_BACKEND` using addition (3) for structured goals; if (3)
deferred, `goals` returns pretty-printed text and structured consumers
stub. Session pool: 1 primary per doc + K scratch, bounded + LRU,
per-kind fairness reservation, explicit `didClose` eviction. Eio
cancellation via `Switch`/`Cancel`/`Fiber.fork_daemon`; budgets are
deadlines. Restart via tagged frame; map + scratch invalidation; surface
notifications. Single internal publish point wired. Structured transcript
writer + **replay driver** (consumes the transcript JSON stream,
re-drives a fresh backend against recorded `session.spawn/exec/reply`,
asserts outputs match — pulled here from Phase 9 to serve as the
test substrate every subsequent phase uses for deterministic
conformance and regression goldens). Post-exec uuid-invariant check.
Observability from first code.

Tests: unit; cancellation stress; transcript goldens (rekeyed to
sentence IDs in Phase 2).

**Demo CLI**: opens file, steps, reverts, prints goals, cancels in
flight, handles Restart cleanly.

**End-of-phase measurements** (rolled in from Phase 0a): against real
`.ec` files from `theories/` / `examples/`, record cold-start
(± `.eco`), per-session RSS after full load, SIGKILL + pool-replace
cost, and three SMT scenarios through the actual session backend:
success, cancel-mid-solve, two concurrent. These settle
`K_lsp`/`K_mcp`/`pool_size` defaults.

**Acceptance**: demo CLI exercises the full session API; every entry
point lands through a registry; three SMT scenarios green against
the real backend; pool-sizing defaults documented (re-tuned in
Phase 1.5); replay driver reproduces a recorded transcript bit-for-bit
against a fresh backend.

**Current status (Phase 1 core landed).** Subprocess `Ec_llm_session`
implements `Session.BACKEND`; demo CLI at `ecd drive <file>` exercises
parse + exec + goals + revert; structured JSON transcript from
`Transcript` covers spawn/exec/reply/restart/kill plus
invariant.uuid_mismatch. Three SMT scenarios (`success`, `cancel-
mid-solve`, `two-concurrent`) + a `startup-cost` probe in
`tooling/smoke/run_smt_scenarios.ml`; all green against the real
`ec llm`. Registry dispatch (`LSP_FEATURE` / `MCP_TOOL`) and pool
fairness land with Phase 5/6 when the surfaces come online.

**Measurements (nix `withDevTools` shell; alt-ergo/z3/cvc5 wired via
`~/.config/easycrypt/why3.conf`; figures from a single pass of
`tooling/smoke/run_smt_scenarios.ml`).**

| Scenario | Duration |
|---|---|
| cold start (spawn + READY + handshake) | ~140 ms |
| lemma + `smt()` + qed on a nonlinear goal | ~140 ms |
| two concurrent lemma+smt execs (parallel sessions) | ~200 ms |
| cancel fiber fires 50 ms into `smt()`, sibling exec unblocks via promise + SIGKILL | ~50 ms → `Session_restarted` |

A 20-second hard deadline on the cancel scenario guards against
future regressions: if the exec fiber ever fails to unblock within
that window it's a fail, not a hang.

**Pool-sizing defaults (provisional).** Pending real prover
measurements, `Pool.Make` is configured in the composition smoke
with `pool_size=4`, `k_lsp=1`, `k_mcp=1`, `k_spec=0`. These are
placeholders; Phase 2's calibration sub-step replaces them with real
numbers.

### Phase 2 — Document + sentence model + minimal workspace + daemon discovery + prover calibration

Splitter from addition (1); stable sentence IDs. Sentence→uuid map
per session; invalidated on Restart. Diff-on-`didChange`. Minimal
workspace: document set + authoritative load path. Multi-document
support. Demo CLI gains edit-diff + re-feed.

**Daemon discovery (pulled from former Phase 4):** binary-path config;
pid/socket file on startup; stale-pid cleanup tested with `kill -9` +
client-ignores-stale. Makes the daemon persistent across client
disconnects from here on, so TUI/REPL/LSP/MCP can attach to a shared
long-running instance rather than spawn their own. Testing the
`survives-client-disconnect` contract (Cross-cutting commitments —
Scratch lifecycle) lands here rather than being crammed into Phase 5.

**Session supervisor fiber (correctness for the persistence contract
above):** each session gets a `Fiber.fork_daemon` watching
`Eio.Process.await`; on non-zero exit or signal it publishes
`session.crashed` through the central publish point, so the pool +
all surfaces see a consistent restart/respawn picture. Without this,
persistent-daemon correctness is "callers notice when exec returns
`Session_restarted` and respawn," which works for the current
single-surface REPL/TUI but fails as soon as Phase 5/6 fan out to
multiple surfaces sharing a session. Moved forward from Deferrals —
the persistence contract that discovery establishes here is what
makes supervision load-bearing, not polish.

**Prover-pool calibration (sub-step, formerly Phase 1.5).** Dedicated
measurement pass to replace Phase 1's placeholder pool sizes with real
numbers before any LSP/MCP surface makes fairness load-bearing:
- **Corpus**: ~10 files from `theories/` covering typical workloads
  (nonlinear arithmetic lemma, crypto game hop, abstract-theory
  instantiation, plus filler). Pinned under `tooling/smoke/` so
  numbers stay comparable across runs.
- **Workload for fairness**: 10-minute run with 5 concurrent LSP-like
  didChange cycles (parse + diagnostics + goals-json) interleaved
  with 3 concurrent MCP-like `try_tactic` probes; measure LSP p50/p99
  latency under steady MCP load.
- **Measurements**: per-session RSS after full load; per-scenario
  wall time; scratch-pool contention at varying `pool_size`;
  `EcPrinting.pp_form` wall-clock on the goals-json hot path (piggy-
  back data point for the deferred EC-printing perf question — no
  architectural commitment, just numbers).
- **Output**: updated `Pool.Make` defaults + `K_lsp`/`K_mcp`/`k_spec`
  in the composition smoke; a brief calibration note in
  `tooling/docs/` recording the environment the numbers came from.

Tests: unit (grammar corpus: nested proof/qed, `abort`, sections,
abstract theory, clone with, inline modules, `by` one-liners, doc
comments); property (diff laws); differential oracle; framing fuzz;
discovery integration (kill daemon mid-session, client reconnects
to the fresh instance without spawning a duplicate); **supervisor
smoke** (send `SIGKILL` to an `ec llm` child, assert the supervisor
publishes `session.crashed` within a deadline and the pool replaces
the slot without caller intervention). Rekey Phase 1 goldens.

**Acceptance**: differential oracle green on corpus; grammar corpus
passes; property tests pass; discovery + stale-pid cleanup green;
supervisor smoke green; pool-sizing defaults updated from measured
numbers; starvation-freedom property test (LSP `didChange` p99 under
the fairness workload) passes with the new defaults.

**Current status (Phase 2 core landed).** Content-addressed
`Sentence_id.of_source` (MD5 for v0); Ec_llm_session maintains a
per-session `sentence_id → uuid` map, cleared on `[restarted]`
replies per protocol § 10.3. `Document.t` wraps a parse with
`{id; parsed}` records; `Document.diff` returns a common-prefix
split. `Workspace` is the doc registry + load-path holder. A
differential oracle smoke (`run_diff_oracle`) runs a small
corpus cold, reverts to the first sid, re-feeds the remainder,
and asserts every (sid, GOALS-JSON) pair is byte-identical.
Remaining for full Phase 2 scope: larger corpus with property
tests; grammar corpus; LCS diff for suffix-salvage on mid-
document edits. Daemon discovery library landed 2026-04-25
(supervisor fiber + `Daemon_discovery` library smokes 5/5 + 13/13);
long-running `ecd daemon` subcommand pulled forward as Phase 2.5.

### Phase 2.5 — `ecd daemon` long-running subcommand

Wires the `Daemon_discovery` library (landed Phase 2) into a real
persistent process. Prerequisite for Phase 5-core LSP server work:
without `ecd daemon`, there's nothing for VSCode/MCP clients to
connect to.

Deliverables:
- `ecd daemon [--label NAME] [--socket PATH]` subcommand.
- Takes the `Daemon_discovery` lock at startup; releases on exit
  (atexit + signal-handler).
- Listens on a Unix socket (default path computed from runtime dir +
  label).
- Signal-handler graceful shutdown (SIGTERM / SIGINT): drain
  in-flight requests, kill scratch sessions, release pool, release
  discovery lock, exit 0.
- Stale-pid cleanup on startup (already handled by `Daemon_discovery`).
- Crash log on signal-handler crash (separate work item under
  Stage 2 of the VSCode-first plan).

Acceptance: smoke that starts `ecd daemon` as subprocess, verifies
pid file written, sends SIGTERM, verifies pid file cleaned up; second
smoke verifies SIGKILL leaves stale file recoverable by next
`Daemon_discovery.acquire`.

### Phase 3 — Structured execution (overlay primitive deferred to v1+)

**Note (2026-04-26):** the OVERLAY_KIND substrate originally part of
this phase is **deferred to v1+**. PoC ships the EXEC-JSON +
PARSE-JSON ergonomics work (additions 13 v0, 16 — both landed); the
overlay registry, composition algebra, and OVERLAY_KIND
implementations (mask-with-admit, lax, etc.) wait for v1+ feature
pressure. Lax-as-overlay subsumed by cache-policy lax (Phase 5.0);
other overlays (Time_budget reframed as daemon setting; Disable_smt
dropped; Admit_subtree subsumed by smart caching). See STATUS.md
"Reframed: lax mode" and "Overlay system (NEW: deferred from PoC)".

Ships two EC-core additions plus daemon-side consolidation. The
previous framing of Phase 3 as "document edits pushed into EC-core"
was wrong — byte-level splicing is a client concern and stays there.
What EC-core gets is the structured-execution substrate (addition 13,
reclaiming its natural name) and one PARSE-JSON ergonomics fix
(addition 16) that removes the need for every client to reimplement
the same leading-whitespace scan.

**Addition 13 (EXEC-JSON, EC-core).** Structured execution — accept a
JSON-encoded EC command (tactic invocation, directive) and dispatch
it directly into the execution entry points, bypassing the text
parser for cases the schema covers. v0 scope: tactic invocations
with name-arg tactics, directive forms (`print`/`search`/`locate`/
`pragma`). Declarations and term-arg tactics fall back to text via
the daemon until addition 17's typed formula serializer lands. See
UPSTREAM.md for schema scope notes and the "not for document
editing" boundary.

**Addition 16 (PARSE-JSON first-token offset, EC-core).** Cheap
cleanup — move `sentences[].start_offset` forward past leading
separator whitespace. Removes the `actual_sentence_start` scan from
every byte-level splicer. Logical fix; independently shippable.

**Daemon-side splice consolidation (no new EC-core).**
- `Edit_ops` daemon module consolidates the three splice sites
  (`cmd_insert` / `cmd_edit` / `cmd_delete` in
  [`repl_core.ml`](tooling/lib/repl_core.ml)) into one helper.
  Post-addition-16, the `actual_sentence_start` scan in that helper
  goes away. Post-reparse truncation guard stays as belt-and-
  suspenders.

**(Deferred to v1+):** `OVERLAY_KIND` registry + composition algebra
+ mask-with-admit + overlay+Restart integration + demo CLI overlay
set/clear. The overlay infrastructure waits for v1+ when forcing
functions appear (semantic-mode S2/S3, collaborative editing,
teaching mode). Lax-equivalent UX shipped via cache-policy lax
(Phase 5.0); time bounding via daemon-level setting; Disable_smt
dropped.

Tests: existing EXEC-JSON round-trip goldens (12/14 v0 commands at
34/34 checks). Overlay-related tests deferred with the substrate.

**Acceptance:** addition 13 EC-core landed with v0 schema (✓);
addition 16 EC-core landed (✓); EXEC-JSON goldens match their
text-path counterparts byte-for-byte (✓); `Edit_ops` consolidated
(✓). Original overlay-related acceptance items moved to v1+ scope.

**Current status (substrate landed; overlay scope deferred).**
Addition 16 landed (`ae58c706d`); addition 13 landed v0
render-and-parse for 10 tactics + 4 directives (`f4692ad23`);
`Edit_ops` consolidated (`5124ed246`); `:exec-json` REPL command,
`Ec_llm_session.exec_json`, and the replay-driver exec_json dispatch
path all wired (`b4183ec1d`, `f9f8366da`). Round-trip equivalence
smoke covers 12 of the 14 v0 commands at 34/34 checks (`f248677e4`).
Remaining v1+ work: `OVERLAY_KIND` substrate (when needed); EXEC-JSON
v0.1 (compound tactics with nested args — enables `RecoveryStrategy`
catalog in `proof/execToPoint`); EXEC-JSON v1 (direct-AST dispatch
+ subgoal-addressing — enables sub-sentence Tier 3 chain
decomposition).

### Phase 4 — Symbol sources + workspace index

(Former Phase 4b. Former Phase 4a — workspace promotion + daemon
discovery — is absorbed by Phase 2.)

Ships EC additions 2 (declaration dump), 9 (structured
`print`/`locate`/`search` — schema already drafted in Phase 3 alongside
EXEC-JSON), and 10 (hover / type-at-point). Note: addition 9 and 10
share a JSON envelope but are architecturally independent — 9 is
query-driven (user names a symbol), 10 is cursor-driven (daemon must
resolve position → identifier via `EcEnv`/`EcScope`). The
position-resolver is addition 10's real work; addition 9 does not
shrink it, only shares its serialization. Daemon-side symbol sources
built on top:

- File-local outline from addition 1 (`documentSymbol`, PoC scope).
- Workspace-wide symbol index from addition 2; empty if addition 2
  slips, degrades gracefully.
- Position-based lookups from addition 9 (`print` / `locate` /
  `search` by qualified name) and addition 10 (hover by
  `(sentence_id, cursor_offset)`).
- Cache interface (no-op impl in PoC; key tuple per 0b's artifact
  cache stub). Real population comes post-PoC.

Crash/reconnect contract tested against 0b. (Daemon discovery itself
lives in Phase 2; the reconnect-after-restart flow is exercised here.)

Tests: addition 9/10 JSON goldens; workspace symbol lookup against
a `theories/` slice; `documentSymbol` against grammar corpus;
crash/reconnect + stale-pid recovery (builds on Phase 2's discovery).

**Acceptance**: file-local `documentSymbol` returns real outlines;
addition-9 structured results parse and round-trip; hover returns
sensible payloads on an identifier-dense corpus; reconnect tests
green. Runs parallel with Phases 3/5/6.

### Phase 4.5 — Cross-file invalidation

Multi-document support in Phase 2 gives each file its own primary
session; nothing today propagates state when a file's dependency on
disk changes. `A.ec` that `require import`s `B` holds B's compiled
declarations inside A's session; editing B leaves A stale until a
manual `:reload`. For an editor to feel live, the daemon needs to
notice and handle this. Gated on addition 2 (declaration dump) so the
import graph can be derived from typed data, not pretty-printed
output.

Deliverables:

- **File-dependency graph** built from addition 2's output. Each
  loaded document contributes its `require`/`require import` /
  `clone` references; the graph is `document → set of documents it
  requires (directly and transitively)`. Maintained as workspace
  state; rebuilt incrementally on `didOpen` / `didChange`.
- **On-save invalidation**. When `B.ec` reaches `didSave` (or the
  filesystem watcher sees an external change), every open document A
  whose transitive requires contain B is marked `stale`. Sessions
  for stale documents are torn down (`pragma restart.`) and the
  sentence-ID map dropped; the new session picks up B's fresh `.eco`
  on next `require`. Emits `server/restarted` with
  `reason: "dependency-invalidation"` + new payload field
  `triggered_by: [B_uri, ...]` so clients can distinguish cascade
  restarts from user-requested ones.
- **Policy: auto vs. prompt.** PoC default is auto-restart for stale
  documents. A workspace-config flag
  (`proof.autoReloadDependents: true|false`) lets power users
  require manual confirmation — same mechanism as
  `speculativeCompilation` toggle (see roadmap). Rationale: for
  typical edit-save-check loops auto is right; for "I know what I'm
  doing, don't touch my running proof" cases the user wants control.
- **Detection caveat.** EC's `clone` with substitution, abstract-
  theory-with-type-aliases, and `require`-under-section produce
  dependency edges that addition 2's schema must capture; if it
  doesn't, graph is best-effort and the fallback is "stale unless
  proven fresh" (over-invalidate conservatively). PoC can ship
  over-invalidating and tighten once addition 2 is proven out.

Tests: unit (graph construction on a two-file corpus with explicit
imports, on a three-file transitive-dependency corpus, on a cloned-
theory corpus); integration (edit B, verify A's session restarts
and goals at A's cursor match a cold reload); policy smoke (flag
off → no auto-restart, banner emitted, `:step` triggers the restart
and reports cascade reason); regression (edit B's body without
changing its signature — A still restarts, confirmed to be the
right conservative call for PoC).

**Acceptance**: two-file + three-file transitive corpora pass; auto-
restart policy green against the differential oracle (stale
reconcile == cold-load result); `server/restarted` with
`triggered_by` payload reaches both LSP and MCP surfaces once
Phases 5 and 6 land; policy flag honored. May parallel Phases 5/6.

### Phase 5 — LSP (base + proof methods + single-file nav)

(Former Phases 5a + 5b collapsed. The split was artificial: "LSP
infrastructure" alone produces nothing testable — real conformance
requires at least one method end-to-end. In practice these ship
interleaved.)

**Method namespace:** `easycrypt/proof/*` (per 2026-04-26 decision —
matches upstream's `vscode` branch so their extension drops in
cheaply). Implemented via single `proof_ns` constant in
`lsp_methods.ml`.

**Precondition: EC addition 14 (`ANALYZE-JSON`)** — landed v0
2026-04-25.

**Base surface:** JSON-RPC framing on Eio transport (`lsp_io.ml`);
`initialize` / `shutdown` / `exit`; **capability handshake daemon ↔
client** (per 2026-04-26 reframe — capability negotiation is
client-direction, not EC-direction). `didOpen` / `didChange` /
`didClose`; `publishDiagnostics` driven by addition 14. Sentence-id
based events. Cancellation via `$/cancelRequest` + Eio.

**Custom methods (via `LSP_FEATURE` registry):**
`easycrypt/proof/execToPoint`, `easycrypt/proof/revertToPoint`,
`easycrypt/proof/goals`, `easycrypt/proof/checkpoint`,
`easycrypt/proof/revertCheckpoint` (sugar over sentence IDs).

`execToPoint` carries `RecoveryStrategy: halt | best_effort_admit`
parameter (post-iteration decision; replaces overlay-based lax).
Default `halt` for safety; clients (VSCode) opt into
`best_effort_admit` for interactive flows.

**Note: `proof/overlay/{set,clear}` methods dropped from PoC scope**
— overlay infrastructure deferred to v1+; lax-equivalent UX
provided by cache-policy lax (Phase 5.0).

**Standard methods (PoC scope):** `hover`, `documentSymbol`
(file-local), `definition` (single-file). These depend on Phase 4's
additions 2/9/10 and land in the 5-full gate below. Cut for PoC:
`workspace/symbol`, `rename`, `typeDefinition`, `references`,
`semanticTokens`.

**Acceptance — staged:**

- **5-core**: scripted-client conformance suite green for the
  session-level surface — `initialize` handshake, `didChange` →
  diagnostics round-trip (via addition 14), `easycrypt/proof/execToPoint`
  + `easycrypt/proof/revertToPoint`, `easycrypt/proof/stateChanged`,
  `easycrypt/server/restarted`. **VSCode extension demo end-to-end**
  is the user-visible acceptance gate (Milestone 2 in STATUS.md).
- **5-full**: standard LSP methods land — `hover`, `documentSymbol`,
  `definition` on an identifier-dense corpus. Gated on Phase 4
  shipping additions 2/9/10.

**Status (post-Slice-D):** 5-core acceptance criteria are met.
Conformance smoke 16/16 (socket); stdio smoke 10/10; proof-flow
smoke 20/20 covers the PG-style step/back/restart/exec-to-cursor +
auto-reconcile flow end-to-end. Slices A-D added the convenience
methods (`step`/`back`/`restart`) + `currentEndPosition` on
stateChanged + `didChange`-driven reconcile. VSCode extension MVP
ships locked-region tinting (Slice B), goal-pane WebviewPanel
(Slice C), auto-reconcile rendering (Slice D). 5-full still gated
on Phase 4. Next deliverable is the Proof_speculation lift /
parity plan (see Phase 5-parity below).

### Phase 5-parity — daemon-as-foundation pivot + VSCode/TUI parity

(Added post-Slice-D.) Pivot the architecture so daemon-side core
modules are the foundation; REPL/TUI/VSCode become equal consumers.
Today `Semantic_tui` owns speculation logic, and `Repl_core` is the
de-facto base layer that TUI sits on. Pivot folds speculation into
a new `Proof_speculation` shared module so all surfaces share one
truth; `Repl_core` becomes a sibling consumer (kept because
scripted REPL tests are the cheapest end-to-end check).

Phases (sketch — full plan in [HANDOFF-VSCODE-FIRST.md](../HANDOFF-VSCODE-FIRST.md)):

- **Phase 0** — the lift. Pure refactor, ~300-500 LoC. New
  `Proof_speculation` module exposing `begin_session / try / commit
  / discard` + `preview_lemma` + `suggest_closers` (with
  `on_progress` callback). Lifts logic from `Semantic_tui`. Three
  design decisions baked in: (1) `on_progress` invoked per candidate
  AFTER rollback; (2) rollback errors flow up as `Result`; (3)
  cumulative-handle session API as the only model — LSP one-shots
  become sugar.
- **Phase 1** — navigation completeness. `step { count? }`,
  `back { count? }`, `execAll { uri }`, `cycleSubgoal { direction }`.
  Step-to-cursor already shipped in Slice A.
- **Phase 2** — one-goal-at-a-time goal view (UI only). VSCode
  webview shows `subgoals[current_index]` with cycle ± keybinds.
- **Phase 3** — `tryTactic` + `suggestClosers` LSP methods over
  Proof_speculation. VSCode adds Tactic Preview pane + Suggest
  Closer QuickPick. Hard per-candidate timeout until `proof/cancel`.
- **Phase 4** — lemma fuzzy search picker. `searchLemmas` +
  `previewApply`. Async via `$/progress`. Resource cleanup needs
  `proof/cancel` (open architectural point #3).

### Phase 5.0 — Cache substrate (lands after Phase 5-core demo)

(New phase per 2026-04-26 ordering decision. Originally framed as
v1 performance optimization; **elevated to PoC foundation** because
cache-policy lax replaces the overlay-based failure handling we
deferred from Phase 3.)

Deliverables:

- **`Cas` module** (`tooling/lib/cas.{ml,mli}`) — BLAKE2b-128
  fingerprint per document via `digestif`. Cache key splits into
  `(statement_hash, proof_hash)`; downstream entries depend only
  on `statement_hash`. ~110 LoC + smoke. Add `digestif` to
  boundary-allowlist.
- **`Goals_cache`** (`tooling/lib/goals_cache.{ml,mli}`) — LRU
  cache keyed by `(doc_uri, sid)` → goals JSON. Default budget
  64MB/workspace, configurable (`proof.goalsCacheBudgetMB`).
  Provenance tags `normal | lax_admitted | lax_clean` so policy
  filters work. Drop on Restart; suffix-drop on revert. ~280 LoC.
- **Replay-to-sid primitive** (`tooling/lib/replay.ml` extension)
  — on cache miss, acquire scratch from pool, replay non-lax
  context up to target sid, capture goals, populate cache. ~150 LoC.
- **Cache-policy lax** — workspace setting `proof.cachePolicy: "lax"
  | "strict"`. Lax: `proof_hash` mismatch (currently-failing proof)
  invalidates only the entry, not downstream entries depending on
  `statement_hash`. Strict: any failure cascades. Default: lax for
  interactive sessions; strict for CI launches.
- **Wire cache into** `easycrypt/proof/goals`,
  `easycrypt/proof/execToPoint`, `publishDiagnostics` paths.
- **Wire cache into `Repl_core`** for REPL/TUI speedup (~50 LoC).

Acceptance: cache-hit rate on diff-oracle corpus > 90% on
no-edit re-execution; lax mode preserves downstream cache when a
mid-document proof body fails; strict mode invalidates as expected;
mode-switch lax → strict revalidates correctly.

**Net user-visible effect:** existing flows feel fast. VSCode demo
from Phase 5-core gains "second run is instant" property. REPL/TUI
benefit too.

**Quick tip motion** (parity-plan UX target). Goals_cache also
unlocks "scrub forward to sid N, see goals instantly while EC catches
up in the background." Cheap to wire (~50 LoC daemon-side) once Phase
5.0 lands:

- LSP `easycrypt/proof/execToPoint { target }` returns the cached
  goals at `target` immediately + `currentEndPosition: target` in the
  `stateChanged` notification, so the client renders the locked
  region forward instantly.
- Background fiber re-execs sentences `current → target` in EC.
- Tactic submissions (`tryTactic`, `step`, etc.) queue with
  `$/progress` until catch-up completes; reads (goal pane refresh,
  hover) keep working.
- If the client jumps elsewhere mid-catch-up, abort the in-flight
  replay and start over.

Backward motion is already fast (REVERT pops EC's undo stack). The
asymmetry is structural to EC. *Executable* instant forward motion
(move *and* be ready to act on a previously-uncached tip) is not
free; see the Post-PoC cache layering below.

### Beyond Phase 5.0 — cache layering (post-PoC)

Goals_cache is the in-memory L1. Three further layers compose linearly
without protocol changes — all keyed off `(statement_hash, env_hash)`
(protocol § 13's pinned tuple):

- **"Phase X" — per-proof checkpoint cache.** Disk-persistent
  verified-flag at `(statement_hash, proof_hash, env_hash)`. EC's
  `Gsave` checks the cache; on hit, skips the proof body and just
  emits the axiom. Survives daemon restart. Requires the
  canonicalization TODO (protocol § 13) to land first. EC-side
  scope: localized to `Gsave` + a hash-aware skip in scope
  processing.
- **"SMT memoization" — Why3 call cache.** Hash the SMT-LIB query +
  prover config; cache `unsat` results. Three modes (strict /
  middle / weak) over the same daemon setting axis as cache-policy
  lax. Composes with the ecSMT redesign — the rewrite gives natural
  cache hooks at the call site. Optional unsat-core capture gives
  precise lemma-dependency invalidation (only invalidate cache
  entries whose unsat-core depends on a changed lemma).
- **"Phase Y" — fork-safe workers.** Orthogonal to caching, not a
  cache per se. Each forked child is an implicit process-state
  snapshot via copy-on-write. Daemon adopts/discards forks for fast
  speculative execution, parallel tries (LLM "close subgoal with
  budget"), instant tip restore at common parked positions.
  Requires EC fork-safety (open architectural point #2). Hundreds-
  to-low-thousands LoC ec-core, contained scope (subprocess
  handles, fds, Random state, buffered I/O).

These layer rather than replace each other — X handles "skip closed
proofs," SMT memo handles "skip prover calls," Y handles "fast
process-state restore." Combined, they capture ~80-90% of the UX wins
of a hypothetical full-state cache (see "Phase Z" below) without
touching the kernel data model.

Decision rationale: this bundle is the linear post-PoC progression.
Each layer ships independently and delivers user-visible wins; later
layers compose without protocol changes. None gates the PoC; the
cache key tuple was deliberately reserved wide enough in protocol §
13 to admit the whole sequence.

### "Phase Z" — full serializable proof state (blue sky)

Recorded for completeness; do not block PoC decisions on this.

`(doc_uri, sid) → serialized EcEnv + scope stack + proof tree`.
Conditional on:

- EcEnv/EcScope rework removing physical-equality and mutable-ref
  obstacles to serialization (already confirmed direction; scope
  unknown).
- A new ec-core "proof-checkpoint serializer" addition beyond the
  rework — substantial, probably comparable to the `.eco` design
  effort.
- Re-verification on load is non-negotiable for soundness; can be
  backgrounded for interactive UX (trusting cached state during the
  wait), strict-mode disabled for CI.
- Recompute-on-upgrade rather than migrate-on-upgrade — cache key
  includes EC version, upgrade = total miss.

Z's *unique* value over X+SMT+Y is "instant any-tip restore at sids
no fork or speculation has reached." Y already covers the common
parked-position restore via warm forks. Skipping Z entirely in favor
of X+SMT+Y is defensible and may end up the right call.

Architecturally the cache key tuple admits Z without redesign;
provenance flag extends with `cached_state` if Z ever lands.

### Phase 5.5 — Speculative background compilation

(New phase per 2026-04-26 ordering decision. Sits on top of Phase
5.0 cache substrate.)

Daemon pre-executes sentences ahead of cursor in a background scratch
session. When user advances to that position, goals + diagnostics
are already in the cache; UI renders instantly.

Deliverables:
- **Speculation scheduler fiber** — watches user cursor (LSP request
  events); picks `K_spec` scratch slots from the pool; pre-execs
  ahead of cursor.
- **Cache integration** — speculation populates Goals_cache; on
  cursor advance, cache hits.
- **Invalidation hooks** — edit behind speculation point → discard
  speculative state, re-schedule.
- **Budget enforcement** — speculation yields to user-driven exec;
  `proof.speculationBudgetMs` workspace setting.
- **Toggleable** — `proof.speculation: true | false` (default true
  on desktop; users can disable for low-power machines).

~150 LoC on top of Phase 5.0 substrate. Composes naturally with the
existing Goals_cache structure.

Acceptance: with speculation on, cursor-advance latency on a
500-sentence document drops below 100ms (vs ~500ms without); user-
driven exec is never blocked by speculation work; speculation
correctly invalidates on edit.

### Phase 6 — MCP surface

Runs parallel with Phases 3, 4, 5 — `try_tactic`/`get_goals`/
`exec_region`/`set_overlay`/`clear_overlay`/`cancel` need only the
session API (Phase 1) + sentence addressing (Phase 2); `search_lemma`
stubs until addition 2 lands in Phase 4. Pulling MCP into the parallel
block opens an early Claude Code consumer path before LSP is ready,
and dogfoods the daemon against a real LLM client from Phase 3 onward.

Tools via `MCP_TOOL`: `get_goals`, `exec_region`, `try_tactic` (probe
on scratch), `search_lemma` (workspace index; possibly empty),
`get_document_symbol`, `cancel`. Shared pool with LSP; fairness
enforced. Tool goldens + integration alongside LSP scripted drivers.

Note (2026-04-26): `set_overlay` / `clear_overlay` MCP tools dropped
from PoC scope (overlay infrastructure deferred to v1+ along with
LSP-side `proof/overlay/*`).

### Phase 7 — Neovim plugin + discovery wiring

Depends on Phases 5 and 6. Lua plugin, `filetype=easycrypt`, `vim.lsp`
client, binary-path config. 3-pane layout. Keybinds: exec/revert-
to-cursor, step ±, checkpoint, revert, toggle mask overlay on visual
selection. Terminal split launching Claude Code via pid/socket.

Tree-sitter grammar is a separate workstream; `semanticTokens` is a
future daemon-authoritative fallback (both cut from PoC). Plugin
ships with plain syntax and upgrades when tree-sitter lands.

**Acceptance** requires one of: addition 2 landed (so `search_lemma`
works), or a demo script that avoids cross-file search and exercises
goto-def + hover + exec-to-point on a single file.

### Phase 8 — TUI client (de-facto shipped)

The TUI was originally scoped as an additive, droppable side-product.
In practice `ecd tui` (notty + notty_unix) ships over the shared
`Repl_core` command layer alongside `ecd repl`, and has been the
demo driver throughout Phases 1 and 2. Remaining delta versus a
"full" TUI — attach to a standalone daemon over LSP/MCP rather than
spawning its own `ec llm` subprocess — folds naturally into Phase 7's
discovery wiring and is not scheduled as a standalone phase.

### Phase 9 — Polish, install docs

Polish pass; install docs; keybinds reference; demo walkthrough.

Reframed 2026-04-26: split-prep removed under merged-binary
direction (see Phase 10 below + Merged-binary architecture section).

(The replay driver is no longer in this phase — pulled into Phase 1
as a test substrate.)

### Phase 10 — Merge polish (reframed under merged-binary architecture)

**Reframed 2026-04-26.** Original Phase 10 was "extract `tooling/`
into its own repo + open upstream PR set." That direction is no
longer current — daemon merging into EC is the long-term
architecture (see "Merged-binary architecture (working notes)"
below). Phase 10 collapses to merge polish:

- TCB lint enforcement (`ec-core ↔ UPSTREAM.md` automated check;
  `tooling/**` cannot import EC-internal modules outside the public
  addition surface — see `doc/tcb-discipline.md`).
- `ec daemon` subcommand promotion (rename `ecd daemon` → `ec daemon`
  if/when daemon merges into ec binary; backward-compat shim for
  `ecd`).
- Capability negotiation **does not land** — closed-loop merged-binary
  world makes it irrelevant. The schema is pinned in
  `doc/lsp-schema.md` § Capability handshake for the daemon ↔ client
  axis (per 2026-04-26 reframe), but daemon ↔ EC negotiation is
  vestigial and never implemented.
- Single-binary install docs.
- Migration note in README covering the minimum EC SHA at merge time.

**Acceptance**: TCB lint passes; merged-binary builds and the full
smoke + conformance suites pass against the merged binary; install
landed to date (plus 13/14/15 if they've landed by split time);
daemon started against a pre-cap `ec` fails handshake with a
legible error message naming the missing cap.

---

## Shipping against upstream redesigns (EcEnv / EcSection / ecSMT)

Two EC-core redesigns are confirmed but their scope and landing
windows are unknown: the `EcEnv` / `EcSection` global-state cleanup
and the `ecSMT` direct-SMT-LIB rewrite (dropping Why3 as
middleman). This section tells the story of what we ship against
current EC vs. what waits — using a four-tier discipline so we
don't block on upstream's timeline, and so any code built against
current EC internals has a known demolition date.

**Core discipline:** every daemon↔EC JSON schema is stable and
designed against consumer needs, not EC's current internal shape.
EC-side gatherers can be rewritten post-redesign without touching
the schema or the daemon-side consumers.

### Tier 1 — ship now, no wrapper

Features that compose over landed additions (1/3/4/5/6/7/8/12/13/15/16)
and independent surfaces (`EcIo`, transcripts, dispatch loops). Not
exposed to the redesigns.

| feature | basis |
|---|---|
| batch diagnostics with parse recovery | `EcIo` parse recovery + dispatch loop |
| LSP core surface (lifecycle, proof methods, publishDiagnostics) | landed additions |
| MCP core tools (`try_tactic`, `exec_region`, `get_goals`, overlays, `cancel`) | session API + landed additions |
| cross-file dependency graph + on-save invalidation | PARSE-JSON `require` edges |
| VSCode extension (ported + retargeted from upstream's `vscode` branch) | client-side TypeScript |
| LSP `textDocument/definition` (single-file) | PARSE-JSON sentence ranges |
| LSP `textDocument/documentSymbol` (file-local outline) | PARSE-JSON kinds + ranges |
| import-graph viz | PARSE-JSON `require` edges across workspace |
| annotated proof-tree viz (daemon-side inference from tactic traces) | transcripts + GOALS-JSON deltas |
| Eio-native LSP framing (`lsp_io`) | independent (Option 2 per earlier discussion) |
| jump-to-sentence, tactic-sequence builder, file picker, async cancellable TUI pickers (daemon side) | existing session + speculation primitives |

### Tier 2 — ship now with a thin wrapper that dies post-redesign

Daemon↔EC JSON schema is designed clean; EC-side gatherer walks
today's (ugly) internals, produces schema-conformant output, and
is flagged for replacement when the redesign lands. Wrapper cost
noted per entry; schema survives the swap.

| feature | wrapper (crude EC-side gatherer) | cost | dies when |
|---|---|---|---|
| declaration dump | walk current `EcEnv` by theory, emit typed entries against our schema | ~250-400 LoC | EcEnv redesign |
| workspace symbol index | daemon-side aggregation consuming declaration dump | — | automatic |
| MCP `search_lemma` | fuzzy match over index | — | automatic |
| LSP `workspace/symbol` | LSP handler over index | — | automatic |
| admitted-lemma tracker | filter index by status | — | automatic |
| structured `print` / `locate` / `search` results | parse today's pp-text output into our schema | ~100-200 LoC per form | addition 9 lands; parser swap |
| SMT counter-example surfacing | regex-parse Why3's pretty-printed model | ~100-150 LoC, format-fragile | ecSMT lands; direct model access |

**Wrapper cost-benefit calls:**

- **Declaration-dump wrapper is the highest-value single piece.**
  Its ~300 LoC unlocks the entire symbol-index dependency chain
  (index, `search_lemma`, `workspace/symbol`, admitted-lemma
  tracker). Worth doing ahead of the EcEnv redesign.
- **Print/locate/search parser wrapper is moderate-value, low-stakes.**
  Ship it only if a specific demo / user benefits in the near term.
- **SMT counter-example parser wrapper is low-value, high-risk.**
  Why3's model pretty-print varies across provers and versions;
  parser maintenance is ongoing. Prefer to defer.

**Wrapper discipline:**

1. Every wrapper lives in a single module with a clean `.mli`.
2. Each `.mli` carries a header comment: "This module is a wrapper
   dying post-<redesign-name> — replaced by clean EC-side
   gatherer when that lands."
3. Every schema has a golden-round-trip test (wrapper output parses
   back to the same typed record; post-refactor output must match).
4. Commit messages that touch a wrapper module reference this
   section so removal tracking is obvious at git-log time.

### Tier 3 — post-EcEnv / EcSection redesign

Features where the wrapper path would cost more than the real
thing, or where the post-redesign API makes the feature
qualitatively different.

| feature | why wrapper doesn't pay |
|---|---|
| LSP `hover` / type-at-point | position→identifier resolution walks EcEnv with context; wrapping ≈ reimplementing the env traversal |
| blast-radius | reverse-ref extraction from today's env is too intertwined with elaboration internals |
| proof-dep graph (lemma → lemma) | same |
| type-signature search (Hoogle-style) | needs structural type data; pp-text match is low-signal |

### Tier 4 — post-ecSMT redesign

| feature | why wrapper doesn't pay |
|---|---|
| snapshot-before-SMT UX | needs actual snapshot/restore semantics; no cheap wrapper |
| clean SMT cancellation at EC layer | Why3 process-kill (our current approximation) stays as-is until rewrite |
| Eio-fiber async for TUI pickers — *correctness-mode* | partial async works today; proper cancellation waits for ecSMT (`smt()` / `/#` hang triggers) |

### Tier 5 — needs both redesigns or a concrete consumer

| feature | trigger |
|---|---|
| typed formula / type serializer | post-EcEnv + concrete consumer (semantic-mode S3) |
| semantic-mode S3 (term builder with holes) | post typed-serializer |
| dead-hypothesis detection | post-EcEnv + new addition for post-tactic env inspection |
| session-as-library primitive + fork-worker | most cleanup is inside the two redesigns |

### Strategic implications

1. **Higher headroom than the previous "blocked on upstream" framing
   suggested.** With wrappers, we can ship roughly 90% of the
   Phase 5 + Phase 6 feature surface + half of the v1 exploration
   bundle (admitted-lemma tracker, import-graph, proof-tree viz)
   before either redesign lands. The genuinely-blocked items
   reduce to hover, blast-radius / dep-graph viz, Hoogle search,
   and the SMT-UX features (snapshot + EC-layer cancellation).

2. **Phase 4 (symbol sources) scope clarifies.** Split into Phase
   4-wrap (Tier 2 features with the wrapper) and Phase 4-clean
   (replace the wrapper with the post-EcEnv gatherer). Phase
   4-wrap ships during the current PoC window; Phase 4-clean
   ships alongside the EcEnv redesign whenever that happens.

3. **Some previously-deferred items reclassify as "ship now."**
   LSP definition (single-file), LSP documentSymbol (file-local),
   import-graph viz, annotated proof-tree viz (daemon-side), all
   thought to be redesign-blocked but actually depend only on
   PARSE-JSON + transcripts. These move up.

4. **Addition 11 (SMT counter-examples) should be held.** The
   wrapper is low-value / high-risk; wait for ecSMT.

5. **Schema design is the near-term critical work.** Every Tier 2
   feature's daemon↔EC contract needs to be pinned down before
   its wrapper is worth writing. Two schemas particularly worth
   nailing:
   - **Declaration-dump entry schema** (addition 2's eventual
     output, the wrapper's target format).
   - **SMT counter-example schema** (addition 11's eventual
     payload; designed now so we know what ecSMT redesign needs
     to emit when it lands).

### Update to the EC-side additions list

This section refines the shipping strategy for several entries in
the additions list at the top of this plan without changing their
numbering:

- **Addition 2** (declaration dump): wrapper-first implementation
  under this strategy. Schema pinned in Phase 4-wrap; wrapper
  gatherer ships in Phase 4-wrap; clean gatherer swaps in
  post-EcEnv.
- **Addition 9** (structured `print`/`locate`/`search`): defer
  unless a concrete demo needs it. Parser-wrapper available as
  a cheap interim if the demand appears.
- **Addition 10** (hover): Tier 3 — waits for EcEnv.
- **Addition 11** (SMT counter-examples): Tier 4 — waits for
  ecSMT.
- **Addition 17** (typed formula serializer): Tier 5 — waits
  for both and a concrete consumer.

---

## Deferrals

Items discussed during planning that are intentionally not scheduled
in the PoC. Included here so future sessions don't re-litigate them.

- **Capability negotiation** (`[caps:...]` on READY, `has_cap` gates
  at daemon feature sites). Solves version skew between independently
  released binaries. In the closed-loop monorepo it solves a problem
  that doesn't exist. Lands with Phase 10.
- **`min_proto` / `[proto:N]` cleanup.** The one consumer
  (`t.proto >= 1` in `Ec_llm_session.goals`) can't reach its else
  branch because handshake already enforces `proto >= 1`. Dead but
  harmless; leave until the Phase 10 handshake rework replaces it.
- **Eio-native `ec-core` I/O.** Would let the daemon's promise-based
  cancel path (`read_line_cancellable` in `ec_llm_session.ml`) go
  away. Saves ~15 lines; requires threading Eio through EC's REPL
  loop or a SIGUSR1 scheme. Value does not justify the EC-side
  surgery; SMT cancel still needs SIGKILL because Why3 provers are
  subprocesses, so the win is partial.
- **WAL / per-document session journal.** The Phase-1 replay driver +
  transcript event stream already cover 80% of the value (reproduce a
  session deterministically). A `--resume-from <transcript>` flag on
  `ecd` would close the rest with no new data format. Wait for a
  concrete workflow that needs it.
- **Content-addressable artifact cache.** Protocol § 13 defines the
  key tuple; PoC implementation is a no-op stub. Cross-session sharing
  isn't a PoC scenario and the daemon's `revert_to` + re-feed handles
  warm-start within a session. Build when CI or multi-user sharing
  demands it.
- **Sub-library boundary lint inside `tooling/lib/`.** The
  tooling↔EC boundary is enforced by `scripts/boundary-lint.sh`
  today. Sub-library boundaries (`lsp` ↛ `mcp`, etc.) only become
  load-bearing once Phase 5 and Phase 6 produce distinct handler
  modules. Add an allowlist there at phase boundary, not earlier.
- **EC-printing performance work** (lazy pp at the protocol boundary,
  session-level memo on `(form_hash, env_hash)`, full-AST bypass).
  Deferred pending a measurement pass. `EcPrinting.pp_form` is on the
  hot path for goals-json today and will be for hover once addition
  10 lands; a `--bench` smoke against `theories/` would tell us
  whether memo or laziness is the better first move. No architectural
  commitment until numbers exist.
- (The session supervisor fiber previously lived here. Moved into
  Phase 2 as correctness for the persistent-daemon contract that
  Phase 2's discovery work introduces — see Phase 2.)

---

## Open architectural points (for later discussion)

Items raised during the PoC work whose resolution we've explicitly
paused on. The user will re-raise; listed here so the next session
has the context.

- **EC-merge (§ "daemon + workers inside `ec`"): codebase separation
  within a single binary.** If we go ahead with merging the daemon
  into EC as a subcommand (`ec daemon` / `ec worker` same binary,
  fork-based workers for cheap scratch-spawn), we still want the
  daemon codebase kept somewhat separate from the proof-engine
  codebase — clear module boundaries, clear dune-library separation
  inside `src/`, clear import rules. Open: what those boundaries
  look like concretely, how they map onto EC's current
  `include_subdirs unqualified` layout, whether `tooling/` becomes
  an in-tree library with a boundary-lint allowlist similar to the
  current one.

- **EC-merge: refactor scope for fork-safe workers.** The big
  performance win (pre-warmed master + fork on scratch-spawn)
  requires EC's initialization / scope / prover-connection code to
  survive `fork()` cleanly. EC today isn't designed for that. Open:
  actual scope of the refactor, what breaks under fork (prover
  subprocesses, Random state, buffered I/O, Why3 session), whether
  a narrower fork-worker addition (keep daemon external, EC just
  gets a `--fork-parent` / `--fork-child` mode) captures enough of
  the win to defer the full refactor.

- **Non-blocking / cancellable TUI picker operations.** The
  semantic-TUI closer-suggester runs its speculation sweep
  synchronously inside the notty event-handler and blocks input
  until the sweep completes (progressive rendering lands frames
  mid-sweep but the main loop still can't read keys during it).
  Same pattern will bite any future picker feature that wants
  "run N speculative probes in parallel" — tactic suggester
  extensions, lemma-search-by-unification, tactic-sequence dry-
  runs, etc. Real fix: run the sweep in an Eio fiber, multiplex
  terminal input against fiber-progress events via
  [Eio.Condition] / [Eio.Stream], let Esc cancel the in-flight
  fiber, let the user drive other picker actions during a sweep.
  Scope: ~1 day of event-loop restructuring. Defer until either
  a specific picker sweep grows long enough to be annoying
  routinely, or the Neovim plugin (Phase 7) makes the
  synchronous-blocking UX undemoable. Same plumbing naturally
  serves Phase 6 MCP's `try_tactic` cancellation and any future
  LSP long-running-operation surface.

  **Known in-demo triggers**: (1) the `smt()` candidate at the
  tail of the closer-sweep can be multi-second on hard goals;
  (2) the rewrite-builder hangs when a token resolves into a
  path that invokes SMT (e.g. `rewrite /#` expands to an
  inlined-and-simplified form EC runs the prover over). Both
  surface as "TUI frozen for 5–30s, no way to abort" today.
  Neither is a bug in the picker — both are blocked-event-loop
  symptoms that the cancellable-fiber rework cleans up.

---

## Performance budgets (UX targets)

Pinned 2026-04-26 as targets, not enforced gates. Provide forcing
functions for every implementation decision. Updated when the
benchmark suite (Stage 6+ deliverable) produces real measurements.

| Operation | Target | Notes |
|---|---|---|
| `didChange` → `publishDiagnostics` (small file, ≤100 sentences) | < 500ms | After debouncing (default 200ms); ANALYZE-JSON dispatch + diagnostic push |
| `didChange` → `publishDiagnostics` (medium file, 100-500 sentences) | < 2s | Same path; degrades gracefully |
| `easycrypt/proof/goals { sid }` cache hit | < 50ms | Goals_cache lookup + JSON encode |
| `easycrypt/proof/goals { sid }` cache miss | < 1s (small file), < 5s (medium) | Replay-to-sid + capture |
| `easycrypt/proof/execToPoint { sid }` (single sentence advance) | < 200ms | Excluding SMT/long-proof sentences |
| Cold daemon start + `initialize` reply | < 500ms | Daemon spawn + handshake |
| Semantic-mode click-to-response (already in roadmap) | 50-100ms | For S1 palette interactions |

Failure to hit a budget is a regression to investigate, not a build
break. CI tracks via the benchmark suite.

## Merged-binary architecture (working notes)

**Direction confirmed 2026-04-26.** Daemon merges into `ec` binary
as a subcommand (`ec daemon` / future). Closed-loop world becomes
the steady state. Several plan-document items reframe under this
direction.

**What's confirmed:**
- Tooling code stays under `tooling/` as an in-tree library; daemon
  becomes a subcommand of `ec` (or both `ecd` and `ec daemon` for
  back-compat).
- `UPSTREAM.md` purpose shifts: tracks "EC kernel additions under
  TCB-discipline review" rather than "PR set destined for upstream
  EC."
- TCB discipline maintained via overapproximation heuristic (see
  `doc/tcb-discipline.md`): `ec-core:` prefix gates differential
  oracle + replay corpus + grammar corpus tests; `daemon:` /
  `tui:` / etc. prefixes ride lighter test bars.
- Boundary lint extends post-merge: `tooling/**` cannot import
  EC-internal modules outside the public addition surface tracked
  in `UPSTREAM.md`. Today the lint checks dune library deps; the
  module-import lint is a future addition.

**Open architectural points** (still to resolve):
- Codebase separation inside the merged `ec` binary — what do the
  in-tree boundaries look like, how do they map onto EC's
  `include_subdirs unqualified` layout?
- Refactor scope for fork-safe workers — EC initialization isn't
  designed for `fork()` (prover subprocesses, Random state, buffered
  I/O, Why3 session). Open: actual scope; whether a narrower
  `--fork-parent` / `--fork-child` mode captures enough of the win.

**What this changes in earlier-phase planning:**
- Phase 10 reframed (see Phase 10 above).
- Capability negotiation deferred indefinitely (closed-loop has no
  daemon ↔ EC version skew; daemon ↔ client capabilities still
  pinned in `doc/lsp-schema.md`).
- VSCode extension still ships as a separate repo / package
  (TypeScript client of the daemon's LSP); only the daemon merges.

## Post-PoC anchors — don't lock us out

Major feature arcs the PoC doesn't ship but must remain *reachable*.
Listed here so PoC-phase design decisions don't inadvertently block
them. Detailed feature scoping lives in `doc/tooling-roadmap.md`;
this section is the load-bearing-invariants view.

### Arcs anchored here

1. **v1 exploration / info-gathering bundle.** Dashboards and
   analyses that compose over Phase 4's addition 2 + the workspace
   index + sentence-IDs + transcripts: admitted-lemma tracker,
   workspace proof-status dashboard, blast-radius, proof dependency
   graph visualization, import graph view, tactic timing / hotspot
   heatmap, goal-state timeline scrubbing, annotated proof tree
   visualization, semantic proof diff. Most require no new EC-core
   work beyond addition 2 and existing primitives; a handful
   (dead-hypothesis detection, authoritative proof-term export for
   the proof tree) need new additions which can land incrementally.
   Ships as a wave of `LSP_FEATURE` / `MCP_TOOL` plugins over the
   Phase 5/6 surfaces.

2. **Semantic edit mode (S1 → S3).** User never touches text
   directly — click hypotheses, pick tactics from a filtered palette,
   build terms via AST holes. Three-stage rollout, each shippable
   independently. Uses UPSTREAM addition 13 (EXEC-JSON, structured
   execution) as its submit path; additional future EC-core work
   named but not numbered in `tooling-roadmap.md` covers tactic
   catalog, typed formula serializer, tactic applicability dry-run,
   holey-term typecheck.

3. **Formatter / linter bundle.** Plugins on a round-trippable CST.
   Requires an EC parser refactor (roadmap "Future work" — currently
   no UPSTREAM number; will get one when scoped). Bullet-emission
   formatter (see anchor 7) is a useful early formatter target.

4. **Annotated proof tree visualization** (subcomponent of arc 1 but
   worth naming — it's the headline proof-exploration feature). Two
   data paths: daemon-side inference from tactic-trace deltas (cheap,
   live view, imperfect for structured tactics), and EC-side proof-
   term export (authoritative post-qed only, new addition). Probably
   ship inference first.

5. **REPL/TUI eventual LSP-consumption** (added 2026-04-26). Today
   `ecd repl`, `ecd tui` use `Repl_core` directly over raw sessions;
   plugins (VSCode/Neovim) use LSP. End-state: all surfaces drive
   from the same LSP wire, just rendering differently. Without an
   explicit commitment, the architectures fork — TUI grows features
   that don't map cleanly to LSP, then a future "unify" effort costs
   2-3× what it would today. Bounds present design choices: every
   TUI capability today must be expressible as LSP method calls
   eventually. Retarget after Phase 7 ships.

6. **External file watcher** (added 2026-04-26). PoC ships hybrid
   in-memory dependency table + lazy poll on every primary exec;
   real fsnotify/inotify/FSEvents watcher deferred to v1+. Watcher
   feeds the same invalidation pipeline; pivot is purely additive
   (~150 LoC + opam dep + platform abstraction).

7. **EC-core bullets-with-semantics** (added 2026-04-26). Independent
   EC addition: make `-`/`+`/`*` proof bullets structural — bullets
   open subgoal-focus scopes, bullet-close requires scoped subgoals
   discharged, failure to discharge = error at bullet close.
   Benefits: manual proof writers get clear structure; daemon
   tooling gets explicit subtree boundaries (subtree admission,
   recovery, navigation). Compat modes (`strict | lenient | off`)
   for legacy proofs. Formatter (anchor 3) auto-inserts bullets
   from observed proof tree. Simplifies a lot of post-PoC tooling
   features (subtree admit, blast radius scope, etc.).

8. **Sub-sentence Tier 3 chain decomposition** (added 2026-04-26).
   Daemon-side tactic-chain interpreter mimicking EC's combinator
   semantics (`;`, `first`, named subgoal indices, `||`, `do`,
   `try`, `repeat`). Depends on EXEC-JSON v1 (direct-AST dispatch +
   subgoal-addressing) co-developed with EC. Enables fine-grained
   recovery for chained tactics like `intro x; rewrite H; auto.`
   without losing the `intro x` effect on rewrite failure. Tier 1
   (sentence-level) is the PoC commitment; Tier 2 explicitly
   skipped because Tier 3 is the natural end-state with EC
   co-development.

9. **Cache-policy lax** (formalized 2026-04-26). The previously-
   designed lax-as-overlay collapses to a cache-invalidation policy
   bit. Cache key splits into `(statement_hash, proof_hash)`;
   downstream entries depend only on `statement_hash`; lax mode
   tolerates `proof_hash` mismatch (currently-failing proof) without
   cascading to invalidate downstream. PoC ships this in Phase 5.0.

### Invariants the PoC must preserve

Load-bearing decisions already made whose reversal would block one or
more arcs above. Surfaced so future PoC-phase work doesn't
inadvertently undo them:

1. **Sentence IDs stay the wire vocabulary** for all edit ops,
   overlays, goals, transcripts, checkpoints. Every arc above uses
   sentence_id as the anchor. Any retreat to line:col breaks all of
   them. (Already committed in Cross-cutting commitments → Addressing;
   reaffirmed here.)

2. **Transcript event-schema stability.** Tactic timing / hotspot,
   annotated proof tree, replay-based regression goldens, and the
   v1 dashboards all query the transcript stream. The taxonomy in
   protocol § 14 is a promise, not an implementation detail. Adding
   new kinds is non-breaking; renaming or repurposing existing kinds
   requires the same care as a wire-protocol bump.

3. **Addition 2's schema admits reverse lookups + type-pattern
   unification.** Blast-radius, proof-dep graph, import-graph need
   "who uses X"; type-signature search (roadmap [later]) needs
   structured type data to unify against. Phase 4's addition-2 schema
   review must test both query shapes against a realistic corpus
   before committing — otherwise the v1 exploration bundle lands
   with a schema it has to re-negotiate, and semantic mode S2's
   lemma-by-type search is dead on arrival.

4. **Goal-state retention per sentence_id.** Goal-state timeline
   scrubbing and annotated proof tree both want goals-at-any-sid.
   The daemon already computes them at exec time. The session layer
   must commit to one of two strategies (decide in Phase 5 or
   earliest Phase 6, don't leave for v1):
   - **Keep in-memory per sid** — RSS cost grows linearly with
     document length.
   - **Reconstruct on demand via scratch-session replay-to-sid** —
     latency cost per query, pool contention under busy workspaces.
   Either is fine; drifting without a call means v1 papers over the
   choice and the first real user hits whichever worst case lands.

5. **Idiomatic render-back from every structured edit path.**
   EXEC-JSON today, semantic-mode tactic application later, future
   refactors — all must produce EC source a human would accept in
   review. Diff-review, git blame, and the mixed-mode (text ↔
   semantic) contract depend on this. Pretty-printer work that
   happens anywhere structured ops land holds this bar as a
   correctness requirement, not a polish item.

6. **Full-AST JSON path stays optionality-preserved.**
   `feedback_defer_full_ast` + protocol § 2.4 pp-text inventory:
   every new EC→JSON endpoint records its pp-text fields in the
   inventory table. Each entry is a place the typed-AST extension
   plugs in later without breaking wire compatibility. Phase 4's
   addition 9 adds to this inventory; semantic mode S3 un-defers by
   filling it. The rule "every new pp-text field gets an inventory
   row in the same PR" is the load-bearing discipline.

7. **Structured extension seams over registries.** `LSP_FEATURE`,
   `MCP_TOOL`, `OVERLAY_KIND` registries (0b contracts) mean the v1
   exploration features, the semantic-mode services, and any
   formatter/linter plugins all land as plugin registrations, not
   patches to the core. Keeping the registries narrow and complete
   is a PoC concern even when we're not shipping plugins beyond the
   PoC set.

---

## Security

PoC is stdio, local-only, no auth. 0b wire doc reserves a handshake
auth field for future TCP / WASM.

## Risk register

1. **Declaration dump (addition 2) schema complexity** → `search_lemma`
   and `workspace/symbol` degrade gracefully (empty index).
2. **Splitter vs EC grammar** → property + differential oracle +
   grammar corpus (Phase 2).
3. **SMT-budget enforcement is subprocess-kill** → Phase 1 measures
   cost against the real backend; pool-replace is the only path.
4. **Eio↔Lwt adapter correctness under cancellation** (Why3 in
   transition) → de-risked in Phase 1 via the three SMT scenarios
   (success / cancel-mid-solve / two-concurrent).
5. **Pool memory** higher than spike suggests → hard cap + LRU +
   aggressive scratch eviction. Real numbers land in Phase 2's
   calibration sub-step.
6. **Monorepo boundary drift** → UPSTREAM.md + prefixes + lint +
   split dry-runs from Phase 9 onward.
7. **Registry churn post-0b** → `.mli` stubs in 0b ground the
   contracts; any post-0b change requires updating stubs + re-running
   the composition smoke.
8. **EXEC-JSON scope creep toward document editing** (addition 13)
   → the plan was briefly framed around EXEC-JSON as a server-side
   document-edit primitive; that was wrong (splice logic relocates
   to EC without solving anything). Current scope is structured
   *execution* only. If a future phase wants structured edits, they
   belong on the daemon or editor side — the rule holds even if
   that phase has momentum to push into EC-core.
9. **ANALYZE-JSON parser recovery regressions** (addition 14) →
   parse-recovery points are isolated to `EcIo.xparse`; existing
   interactive parse paths unchanged. Differential-oracle corpus
   (Phase 2) re-run as smoke against the recovery-enabled parser
   catches any behavioral drift before Phase 5 consumes the output.
