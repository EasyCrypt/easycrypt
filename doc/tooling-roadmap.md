# EasyCrypt Tooling — Feature Roadmap

Scope notes. Not the PoC plan; a reference for what the PoC architecture
must remain compatible with.

Legend: [PoC] shipping in first PoC · [v1] soon after · [later] post-PoC ·
[defer] acknowledged, not actively planned · [?] speculative / revisit

## Project layout & tech stack

- **Monorepo during PoC development**, split afterwards. Everything
  tooling-related lives under a dedicated subdirectory (`tooling/` TBD)
  of the EasyCrypt tree; EC-side additions go in their normal places
  in EC source.
- **Split plan post-PoC**: tooling becomes its own repo; EC-side
  additions are PR'd upstream as one coherent set.
- **Boundary discipline while colocated**:
  - Keep `UPSTREAM.md` as the authoritative inventory of EC-side
    changes destined for upstream. Every EC-core change either appears
    there or has a tagged justification.
  - Split-aware commit prefixes (`ec-core:` vs `daemon:` vs `nvim:`
    etc.) so `git filter-repo` / cherry-pick at split time is mechanical.
  - Daemon does not import EC internals outside the upstream-additions
    list. Treat that list as a public API surface today.
- **Daemon language**: OCaml (allows future kernel-fork backend, shared
  types with EC, ecosystem fit).
- **Concurrency**: **Eio** (structured concurrency, first-class
  cancellation). Required by our cancellation-heavy design (per-request
  cancel, pool eviction, budget enforcement). Why3 dep is being phased
  out upstream; Lwt↔Eio adapter in the interim where needed.
- **Build**: dune + Nix flake (extend the existing EC flake initially).

## Core architecture (PoC)

- Single daemon, editor- and LLM-agnostic; LSP + MCP surfaces over a shared
  session pool and document state.
- Daemon architecture is modular: features (formatter, linter, analyzers,
  future capabilities) ship as plugins against stable internal interfaces,
  not patches to the core.
- Session backend behind an interface; subprocess pool is one impl.
- LSP feature registry; MCP tools defined against the same session interface.
- Document overlays as a first-class primitive (mask/admit exposed in PoC;
  try-edit, speculative replace, A/B later).
- Workspace model from day one (single-file index in PoC, cross-file later).
- Structured goals (JSON alongside pretty-printed).
- Transport abstraction (stdio PoC; TCP/socket/WASM free).
- Pub/sub state events for client coherence.
- Protocol versioning + capability handshake.
- Structured cancellation + progress notifications.
- Request correlation IDs end-to-end.
- Optimistic concurrency tokens on mutating ops.
- Stable sentence IDs (not line:col) in protocol.
- Typed error taxonomy.
- Per-request timeouts and budgets.
- Record / replay of daemon transcripts.
- Lifecycle discipline (drain, cancel-all, reap).

## Proof authoring

- [PoC] Overlay system as primitive — mask-with-admit exposed first.
- [PoC, additive] TUI client talking to daemon over LSP/MCP — cheap
  second client that validates editor-agnosticism and lets people try
  the tool without a Neovim setup.
- [v1] Outline view (defs/lemmas with proved/admitted/broken/unchecked status
  and jump).
- [later] Extract-selection-into-lemma refactor, with LLM-suggested statement.
- [later] Structured editing — evaluate per-feature; individual items
  (drag-reorder, click-to-inspect, collapse sub-proofs) have different costs;
  decide item-by-item.
- [later] Snippets / templates — needs dedicated design discussion.

## Semantic edit mode

User never touches text directly: click hypotheses, pick tactics from a
filtered palette, build terms via AST holes. The file on disk stays
idiomatic EC source — semantic mode is a surface, not a file format.
Text users and semantic users interleave on the same file.

Staged rollout, each stage independently shippable:

- **[v1, S1] Thin — hypothesis-click + tactic picker.** Click a
  hypothesis → structured `{tactic:"apply", args:[{kind:"name",
  value:"H"}]}` submitted via EXEC-JSON (UPSTREAM addition 13,
  Phase 3). Tactic palette is a hand-curated top-N list with argument
  slots the user types. Plus the tactic-catalog addition below, to
  populate the palette from EC rather than by hand.
- **[v1/later, S2] Medium — applicability-filtered palette +
  lemma-by-type search.** Palette filters by what actually applies to
  the current goal (tactic-applicability addition below);
  lemma-by-type search (Hoogle-style over addition 2). User still
  types terms but gets autocomplete + relevant-lemma suggestions.
  Covers ~70% of everyday proving without free-form typing.
- **[later, S3] Full — term builder.** Iterative AST construction
  with holes; EC typechecks at every step (holey-term-typecheck
  addition below). The real post-PoC product; warrants its own
  sub-project.

Dependent future EC-core additions (numbers assigned in UPSTREAM.md
when each becomes concretely planned — don't commit to specific
numbers here, they'd shift as intervening additions land):

- **Tactic catalog** — enumerate EC's tactic grammar (name +
  argument shape + short description per tactic) so the palette
  doesn't need to be hand-curated. Required for S1 / S2.
- **Typed formula/type serializer** — un-defers
  `feedback_defer_full_ast`, scoped to first-order forms + basic
  types first; modules / memtypes / abstract-statements remain
  pp-text until their click-UX becomes real. Required for S3, and
  for the typed "term" argument shape inside EXEC-JSON tactics.
- **Tactic applicability / dry-run** — given a structured
  `TacticInvocation` + current goal, return `{applicable,
  new_subgoals, warnings}`. Drives palette filtering. Required
  for S2.
- **Holey-term typecheck** — submit a partial typed term with
  holes, get back `{well_formed, holes, type_errors}`. Required
  for S3 iterative term construction.

Structured tactic submission — the "click hypothesis → run apply H"
wire path — is **addition 13 itself** (EXEC-JSON), not a separate
addition. No EXEC-JSON "extension" is needed: S1 uses its name-arg
tactic schema directly; S2 adds applicability filtering on top of
the same submit path; S3 fills in `term` arguments once the typed
formula serializer lands.

Daemon-side services on top of the additions:

- Palette service (`proof/palette`).
- Term-builder session (`term/build/{start,fill,search,commit,abort}`).
- Lemma search-by-type (Hoogle-over-addition-2).
- Render-and-persist: every committed semantic op renders through EC's
  pretty-printer and lands as an EXEC-JSON edit. Idiomatic text is a
  correctness requirement, not a nice-to-have.

Hard constraints:

1. **Round-trip with text mode.** Semantic edits must produce idiomatic
   EC source. Ugly-but-correct output is a failure — diff-review, git
   blame, and mixed-mode teams require it. Formatter work (CST + trivia
   preservation, under Future work / parser refactor below) becomes a
   hard prerequisite for S3.
2. **Escape-to-text always available.** Every semantic op has an
   inspectable, editable text equivalent. Users hit an edge case the
   palette doesn't cover, drop to text, fix, return. No lock-in.
3. **Full-AST schema is a sustained workstream** (S3). `EcAst.form` has
   ~20 constructors; `EcAst.ty` ~10; patterns, memtypes, modules each
   add their own tree. Round-trip tests per constructor are mandatory;
   don't ship partial schemas that silently drop structure.
4. **Performance budget: ~50–100ms click-to-response.** Mandates lazy
   subtree loading, memoized pretty-print, and `EcPrinting.pp_form`
   caching (currently listed in PoC Deferrals — semantic mode is the
   forcing function that un-defers it).
5. **Applicability is heuristic.** Addition 18's fast path (shape-based
   match) drives the palette; slow path (scratch-session dry-run) is
   only for hover-preview. Wrong 5% of the time is fine; slow is not.

PoC commitments that this mode leans on without requiring new work:
sentence IDs as wire vocabulary, EXEC-JSON, the publish-point seam,
artifact cache interface, transport abstraction, structured goals
(addition 3). Nothing in the PoC plan blocks semantic mode later —
what it requires additionally is captured in the EC-core additions
above plus the CST/formatter workstream.

## LLM-assisted proving

- [v1] "Close this subgoal" with budget; parallel scratch-session attempts;
  returns a diff.
- [v1] "Explain this goal / why did this fail" — LLM consumes goal, error,
  counter-example, nearby lemmas.
- [v1] Inline next-tactic suggestion — must be context-aware (goal state +
  hypotheses + nearby lemmas), not generic completion.
- [v1] Proof shrinker / generalizer.
- [v1] Spec-first: prose → lemma statement → prove.
- [defer, last] Multi-agent race + critic — sugar; build after singletons work.
- [defer] Cross-system port (Coq/Lean → EC) — scope unclear, not priority.

## Analysis & understanding

All in scope post-PoC:
- [v1] Goal-state timeline scrubbing. Depends on per-sentence goal
  retention in the session layer (see PoC plan's "Post-PoC anchors").
- [v1] Counter-example surfacing from Why3 (UPSTREAM addition 11).
- [v1] Dead-hypothesis detection. Requires post-tactic-application
  environment inspection that isn't currently exposed — likely needs
  its own EC-core addition (new, unnumbered).
- [later] Blast-radius ("what breaks if I change this lemma").
  Reverse lookup over UPSTREAM addition 2's declaration dump.
- [later] Proof dependency graph visualization. Same data source as
  blast-radius; editor-side rendering.
- [later] Semantic proof diff. Sentence-ID-anchored; compose over the
  workspace index.
- [later] Tactic timing / hotspot heatmap. Pure post-processing on
  the daemon transcript (timing already recorded per `session.exec`).
- [later] Annotated proof tree visualization. Render the proof's
  branching structure — tactic → subgoals → tactics → subgoals —
  with each node annotated with tactic name, goal-before / goal-
  after, wall-clock timing, proved / admitted / broken status.
  Depends on per-sentence goal retention (above) plus a tree-shape
  inference layer. Two options, evaluable per feature:
  - **Daemon-side inference from tactic traces**: watch
    goals-before → goals-after deltas per `Gtactics` exec; increasing
    subgoal count = branch, decreasing = close. Cheap, works for the
    common case; breaks on structured tactics whose visual tree
    differs from the linear trace (e.g. `by`, deeply nested
    `rewrite`).
  - **EC-side proof-term export**: a new addition that dumps the
    proof's term structure after `qed.` — authoritative but only
    useful once the proof closes; no intermediate view.
  - Probably ship inference first (live view), add proof-term export
    later for authoritative post-qed views.

## Workspace / project

All in scope. Workspace index is load-bearing for LLM and refactoring
features; design must admit it from PoC even if populated with one file.
- [v1] Workspace lemma index: fuzzy + by-type search.
- [later] **Type-signature search with wildcards** — Hoogle-style
  queries over operators and lemmas (e.g. `int -> _ -> bool`,
  `_ %/ _ = _`) with holes unified against the workspace index.
  Depends on the declaration dump (UPSTREAM addition 2) landing
  with enough type structure to unify against, and on a pattern
  parser + unifier in the daemon. No action this phase.
- [v1] Standard LSP navigation, insofar as applicable to EasyCrypt:
  - `textDocument/definition` — goto-definition (op, lemma, module, type).
  - `textDocument/typeDefinition` — goto-type-definition.
  - `textDocument/hover` — show definition / signature / docstring.
  - `textDocument/references` — find-all-uses.
  - `textDocument/documentSymbol` — outline of current file.
  - `workspace/symbol` — workspace-wide symbol search.
  - `textDocument/signatureHelp` — argument hints for applied operators.
  - Editor "peek" variants use the same endpoints; UX lives in the plugin.
- [v1] Rename across workspace (`textDocument/rename`).
- [v1] Admitted-lemma tracker with staleness detection.
- [later] Import graph view.
- [later] Workspace proof-status dashboard.

## Performance / caching

Layered caching plan, all keyed off the same content-addressed
`(statement_hash, env_hash)` tuple (protocol § 13 reservation). Each
layer ships independently and delivers user-visible wins; later layers
compose without protocol changes.

- [PoC, Phase 5.0] **Goals_cache** — in-memory LRU keyed by
  `(doc_uri, sid) → goals JSON`. Drives steady-state UX: instant
  goal-pane refreshes, post-rollback restore, lax-mode downstream
  display. Provenance flag (`fresh | cached | lax_admitted`) lets
  clients render the distinction; without the visual cue, lax-mode
  silently lies to the user.
- [PoC, Phase 5.5] **Speculative background compilation** — pre-execs
  ahead of cursor into the Goals_cache. See § below.
- [v1, "Phase X"] **Per-proof checkpoint cache** — at `qed.`, EC
  records a verified-flag at `(statement_hash, proof_hash, env_hash)`.
  On re-run with matching hashes (e.g. user re-opens the file, no
  edits to upstream), EC skips the proof body and just emits the
  axiom. Disk-persistent; survives daemon restart. Schema uses the
  protocol § 13 key tuple unchanged. Requires the canonicalization
  TODO (§ 13) to land first.
- [v1, "SMT memoization"] **Why3 call cache** —
  `(smt_query_hash, prover_config_hash) → unsat | unknown`. Cache
  `unsat` results (re-verifying determinism is what's skipped); never
  cache `unknown` (we want to retry). Optional unsat-core capture
  gives precise lemma-dependency invalidation — only invalidate when
  a core lemma changes. Three modes:
  - strict: re-run always (CI / release)
  - middle: trust cache iff goal + lemma-set hash matches (default
    interactive)
  - weak: trust cache verbatim
  Lives well in EC's prover bridge or as daemon-side Why3 RPC
  interception. Composes with the ecSMT redesign — the rewrite gives
  natural cache hooks at the call site.
- [later, "Phase Y"] **Fork-safe workers** — orthogonal mechanism,
  not a cache per se. Each forked child is an implicit process-state
  snapshot via copy-on-write; daemon adopts/discards forks for fast
  speculative execution, parallel tries (LLM "close subgoal with
  budget"), instant tip restore. Requires EC fork-safety (open
  architectural point #2). Composes with the cache layers — forks are
  the in-memory tier; checkpoint cache is the disk tier.
- [later] Selective expensive-tactic memoization — pure-function
  tactics (`auto`, `simplify`, `field`, deep unification) wrapped at
  per-tactic granularity. ~50-100 LoC per tactic, value-judged
  against measured benefit. Not a blanket policy.
- [later] Distributed SMT cache across team — same content-addressed
  key tuple flips into a shared store (CI farm, team shared cache).
- [blue sky, "Phase Z"] **Full serializable proof state at any
  sid** — `(doc_uri, sid) → serialized EcEnv + scope + proof tree`.
  Conditional on EcEnv/EcScope rework removing physical-equality and
  mutable-ref obstacles, plus a new ec-core "proof-checkpoint
  serializer" addition. Years out, possibly never if the X+SMT+Y
  bundle covers the practical wins. Architecture admits it without
  redesign because the cache key tuple is wide enough; provenance
  flag would extend with `cached_state`. Listed for completeness; do
  not block PoC decisions on it.

**UX-bearing implication of the cache plan.** Quick proof-tip motion
("scrub forward to sid 80, see goals instantly") splits into:

- *Visual* instant tip motion: cheap, ~50 LoC daemon once Phase 5.0
  lands. Goals_cache serves the post-tip goal immediately while EC
  catches up in the background; tactic submissions queue with a
  progress indicator until catch-up finishes. Backward motion is
  already fast (REVERT pops EC's undo stack).
- *Executable* instant tip motion (move *and* be ready to act): not
  free. Forward motion through previously-execed sentences requires
  EC to actually rebuild env state — same replay cost as fresh
  execution. Three options to dodge the cost: Phase 5.5 speculation
  (pre-runs ahead), Phase Y fork (warm-spare process at the tip),
  or Phase Z (deserialize state — blue sky). The cache alone does
  not provide this.

The "client must show locked-region tint distinct from cursor" UX
contract (already shipped in Slice B) is what makes this honest:
users see at a glance where EC is parked vs what they're viewing.

### Speculative background compilation

Ahead of the cursor, the daemon pre-executes sentences in a background
scratch session. When the user advances to that position, goals and
diagnostics are already computed, so the UI renders instantly instead of
waiting for exec-to-point. Requirements:

- Fully transparent: no user command, no visible state change beyond
  speed-of-response.
- Resource-limited: capped CPU, memory, and SMT budget; yields to
  user-initiated work.
- Toggleable: on/off via workspace config (off on low-power machines,
  during SMT-heavy debugging, etc.).
- Invalidation-cheap: if the user edits behind the speculation point, the
  speculative session is either rewound or discarded and restarted.
- Isolated: speculation failures must not affect primary session state.

## Collaboration

- [later] Pair proving (shared remote daemon, multiple humans on one session).
- [later] Git integration: tactic-granularity blame; "who last touched
  this proof."
- [later] Review mode: PR-style review with comments anchored to sentence
  IDs, goal states rendered alongside the diff.
- [defer] Federated proof search — too speculative.

## Teaching

- [later] Small tutorial for the tooling itself (not EC tutorials; those
  live in a separate project).
- [later] Literate proving (interleaved prose + proof), preferably with a
  clean extraction mechanism. Overlaps with notebook mode.
- [defer] Tutorial mode for EC itself — out of scope, separate project.
- [defer] Replay-my-session — current framing unclear; revisit if concrete
  use case emerges (distinct from internal record/replay for debugging).
- [defer] "Explain this codebase's conventions" — just chat, no special
  tooling needed.

## Ecosystem / integration

- [later] Semantic proof diff for existing CI (EC already has CI).
- [later] Export to LaTeX / HTML with interleaved goal states.
- [later] Notebook mode (= literate proving surface).
- [later] VSCode plugin (after Neovim PoC stabilizes).
- [later] Web version: daemon + EC compiled to WASM + in-browser editor.
- [skip] Emacs / Zed plugins — not prioritized.
- [PoC reuse] GitHub Action — consider if existing CI doesn't cover diff
  reporting.

## Syntax highlighting

Layered strategy:

- **Tree-sitter grammar** for lexical/syntactic highlighting. Separate
  workstream / repo; hand-written (auto-generation from Menhir is not
  worth the complexity). Fast, incremental, error-tolerant, daemon-free.
- **LSP semantic tokens** for meaning-level classification (identifier →
  lemma / operator / module / local-var / type / etc.). Served by the
  daemon on top of the workspace index; editor blends over tree-sitter.

### Drift control

- **Version-pin** the tree-sitter grammar to specific content hashes (or
  git SHAs) of `src/ecParser.mly` and `src/ecLexer.mll` it was built
  against.
- CI job diffs upstream EC parser/lexer against the pinned versions; on
  mismatch, fails with a pointer to the upstream diff. Human reviews and
  updates grammar + bumps pin.
- Corpus-based CI check: parse a corpus of `.ec` files with the
  tree-sitter grammar; assert no `ERROR` nodes (and optionally diff
  highlight classifications against a golden file). Catches cases where
  the pinned diff looks trivial but the grammar consequence isn't.
- **Escape hatch**: if tree-sitter maintenance ever becomes a burden,
  fall back to daemon-authoritative tokens via `semanticTokens`. Trades
  "highlighting without daemon running" for "parser is the single source
  of truth."

## Future work — parser / formatter / linter bundle

Deferred; designed as daemon plugins, not built into core.

- [later] Parser refactor for better errors and round-trippable CST
  (preserves comments, trivia, user grouping). Prerequisite for a serious
  formatter and for richer linter rules.
- [later] Formatter — LSP `textDocument/formatting` + `rangeFormatting`;
  plugin, shipped independently. Depends on CST work.
- [later] Linter — extensible rule registry producing diagnostics and
  code-action fixes; syntactic rules on CST, semantic rules on session
  state. Plugin.

## Wild / research

All deferred. TODO: schedule a dedicated speculation pass later to expand
and evaluate these once the PoC is real:

- Informal-prose → formal-lemma translation.
- Proof-by-induction skeleton synthesis from goal shape.
- Benchmark harness for LLM-agent performance regressions.
- Others — explicitly revisit this section post-PoC.

## Design commitments the feature list reinforces

1. **Workspace index is first-class** — lemma search, rename,
   blast-radius, spec-first LLM flows, admitted-lemma tracking, and the
   standard LSP navigation endpoints (definition, typeDefinition, hover,
   references, documentSymbol, workspace/symbol, signatureHelp) all depend
   on it. Must exist (even single-file) in PoC scaffolding; per-file
   symbol extraction should be wired up in the PoC even if cross-file
   resolution lands in v1.
2. **Overlays are first-class** — mask/admit in PoC, but try-edit,
   speculative replace, A/B, LLM subgoal attempts all stack on the same
   primitive. Worth the abstraction now.
3. **Stable sentence IDs** — review mode, git blame, pair proving, LLM
   references, persisted checkpoints all need anchors that survive edits.
4. **Structured goals** — LaTeX/HTML export, notebook mode, literate
   proving, UI rendering, LLM reasoning all benefit. Design goals as data,
   render to text as one consumer.
5. **Artifact cache interface** — empty in PoC is fine; later features
   (speculative compilation, cross-session cache, distributed cache, CI
   diff) all plug into the same shape.
6. **Transport abstraction** — stdio now; web/WASM, pair proving, remote
   daemon all need it free.
7. **Idiomatic render-back** — any structured edit path (EXEC-JSON,
   semantic mode S1/S2/S3, future formatter) must produce EC source a
   human would accept in review. Diff-review, git blame, mixed-mode
   teams, and the interleave-text-and-semantic-edits contract all
   depend on this. Formatter work (CST + trivia preservation) is the
   eventual forcing function.
