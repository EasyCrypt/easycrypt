# UPSTREAM.md — EC-core additions for the tooling project

Authoritative inventory of changes to EasyCrypt core (`src/`, `theories/`,
`etc/`, `3rdparty/`, root `dune`/`dune-project`, root `flake.nix` for EC
concerns) made in service of the tooling project and destined for the
upstream EC repository at split time.

**Discipline.** Every commit that touches EC core either:
1. appears as an entry below with a phase owner and status, or
2. has a tagged justification in the "Exceptions" section.

No exceptions are silent. The boundary lint (point 4 of Phase 0a) enforces
the separation programmatically; this document is the human record and the
PR set for split.

**Statuses.** `planned` → `drafted` → `in-progress` → `landed` (in
monorepo) → `upstreamed` (merged in EC upstream). "Landed" means merged
into this branch; "upstreamed" means merged into EC's main.

**Split plan.** At PoC split, each `landed`/`upstreamed` entry becomes one
upstream PR (or a bundled PR where logically grouped). The `tooling/`
subdirectory is extracted to its own repo and pins EC at the commit where
the full set is upstreamed.

---

## Additions

### 0. Multi-package `dune-project` preparation

- **Status**: landed (not committed yet).
- **Phase**: 0a.
- **Files**: `dune-project`, `dune`, `src/dune`, `etc/dune`,
  `theories/dune`, `3rdparty/inifiles-1.2/dune`, `flake.nix`.
- **Summary**: Declare a second `(package tooling)` alongside `easycrypt`
  in the root `dune-project`; add explicit `(package easycrypt)`
  attribution to existing install stanzas so dune can disambiguate; extend
  the Nix flake to build the tooling package and include its deps in the
  dev shell.
- **Rationale**: mandatory plumbing for tooling to coexist with EC in the
  monorepo. Trivial upstream change; unlocks everything else.

### 1. Sentence-granular parse endpoint

- **Status**: landed (v0 scope).
- **Phase**: 0b.
- **Files**: `src/ec.ml` (`classify_global`, `parse_to_json`,
  `PARSE-JSON` + `<PARSE-BEGIN>`/`<PARSE-DONE>` meta-commands),
  `doc/llm/CLAUDE.md`, `doc/tooling-protocol.md` § 2.1.
- **Summary**: Two entry points to EC's real parser: `PARSE-JSON
  "file"` for files and `<PARSE-BEGIN>…<PARSE-DONE>` for inline
  buffers, each returning a JSON list of sentences with class
  (`executable`/`doc_comment`/`directive`/`meta`), constructor-
  derived `kind`, line+col range, byte offsets, and verbatim
  source substring. Classification follows protocol § 15.2 post-
  addition-7 semantics — queries + plain `pragma` are
  `directive`, `Gtcdump` stays `executable`, everything else is
  `executable`. Driven off the existing `EcIo.xparse` loop,
  terminating on `locterm=true` (the parser's EOF/stop path) or
  `P_Exit`; parse errors are captured non-fatally into the
  `parse_error` field. Known lexer quirk: `doc_comment`
  sentences' location spans only the closing `*)`, not the full
  comment — out of scope to fix in addition 1.
- **Rationale**: the daemon's sentence splitter (Phase 2) must reuse EC's
  real parser rather than reimplement it. Also feeds the file-local
  outline for `documentSymbol` (Phase 4).

### 2. Declaration dump

- **Status**: planned.
- **Phase**: 4 (draft reviewed in 0b).
- **Files (expected)**: new module adjacent to `src/ecEnv.ml` /
  `src/ecPrinting.ml`; REPL command in `src/ec.ml`.
- **Summary**: Enumerate declarations visible in the current environment
  (lemmas, operators, modules, types, theories) as structured data.
  Schema explicitly covers functors, abstract theories, and cloned
  theories with substitution.
- **Rationale**: feeds the workspace-wide lemma index for `search_lemma`,
  `workspace/symbol`, blast-radius analysis, and LLM lemma suggestion.
  Biggest of the six; scoped to degrade gracefully (empty index) if it
  slips.

### 3. Structured JSON goals

- **Status**: landed (v0 scope; types remain pretty-printed text;
  pp-failure hardening landed).
- **Phase**: 0b.
- **Files**: `src/ec.ml` (`goals_to_json`, `GOALS-JSON` meta-command),
  `doc/llm/CLAUDE.md`, `doc/tooling-protocol.md` § 2.1.
- **Summary**: New `GOALS-JSON` meta-command returns a single-line
  JSON payload exposing the subgoal list, hypothesis bindings (with
  structured `name` and `local_kind` tag: `var`/`mem`/`modty`/`hyp`/
  `abs_st`), and the conclusion. Hypothesis types and conclusion
  formulas are pretty-printed strings for v0; typed-AST structure
  for types/formulas is deferred — sufficient for daemon outline,
  LLM context, and UI rendering without parsing the full pretty
  printer output. `modty` and `abs_st` payloads stub out their `pp`
  until EC exposes a public renderer for them.
- **Pp-failure hardening (landed)**: each `pp_type` / `pp_memtype` /
  `pp_form` call inside `goals_to_json` is wrapped in a try/with
  guard. After a daemon-driven `REVERT` past a `proc`/`axiom`/`op`
  introduction, formula and memenv references in the surviving goal
  state can dangle and `EcPrinting` raises `EcEnv.LookupFailure`
  while chasing them. Without the guard the exception escapes to
  top-level and KILLS the `ec llm` subprocess (`Fatal error`),
  losing all proof state. The guard substitutes a placeholder
  (`<hyp: stale env lookup>`, etc.) and the session keeps running —
  user sees a stale-state marker on the affected hypothesis or
  conclusion, can step / back to a coherent state, and continues.
  This is a Tier-2 fix relative to the EcEnv/EcSection redesign;
  the architecturally clean version is "REVERT also rolls forward
  any env references in the surviving goal" — not feasible until
  the redesign lands.
- **Rationale**: required by LLM reasoning, UI rendering (clickable
  hypotheses, collapsible panels), LaTeX/HTML export, notebook mode,
  literate proving. Phase 1 has a pretty-printed fallback if this slips.

### 4. Tagged event frames

- **Status**: landed.
- **Phase**: 0b.
- **Files**: `src/ec.ml` (REPL reply formatting), `doc/llm/CLAUDE.md`,
  `doc/tooling-protocol.md` § 2.1.
- **Summary**: `[restarted]` bracketed event tag on `OK`/`ERROR` reply
  headers after any restart (explicit `pragma restart.` and the
  implicit restart at the start of every `LOAD`, on both success and
  error paths). `NOTICE: <text>` lines stream out-of-band over stdout
  in real time as the notifier fires during command processing, rather
  than being batched into the reply body — daemon sees progress during
  long operations. `reply_error` gained an optional `?tag` parameter
  for symmetry with `reply_ok`.
- **Rationale**: daemon's `server/restarted` contract and correctness of
  the uuid-invariant check require a reliable restart signal. Also
  cleanly separates diagnostics from bodies for `publishDiagnostics`.

### 5. `<BEGIN>`/`<DONE>` newline preservation

- **Status**: landed (commit `37061f9c5`).
- **Phase**: 0b.
- **Files**: `src/ec.ml:762-764`.
- **Summary**: Stop collapsing multi-line input to spaces; preserve
  newlines.
- **Rationale**: position-sensitive input (line-accurate errors,
  comments, docstrings) breaks under the current behavior. Two-line fix.

### 6. Minimum protocol version

- **Status**: landed.
- **Phase**: 0b.
- **Files**: `src/ec.ml` (handshake emission + `llm_protocol_version`
  constant), `doc/llm/CLAUDE.md`, `doc/tooling-protocol.md` § 2.1.
- **Summary**: `ec llm` advertises its LLM REPL protocol version as a
  `[proto:N]` bracketed tag on the `READY` line (current value: `1`).
  The daemon compares against its `minEcLlmVersion` and fails the
  handshake with `ProtocolMismatch` on a lower report.
- **Rationale**: version-skew guardrail so protocol changes don't silently
  corrupt daemon behavior when built against an older EC. `N` bumps in
  lock-step with any wire-visible protocol change.

### 7. Read-only queries do not advance uuid

- **Status**: landed (commit `2ac65146a`).
- **Phase**: 0b.
- **Files**: `src/ecCommands.ml` (switch relevant constructors from
  `` `Fct `` to `` `State ``).
- **Summary**: `Gprint`, `Gsearch`, `Glocate`, `GdumpWhy3` no longer
  push a context on success; the scope is genuinely unchanged so uuid
  stays put. `Gtcdump` is not included — despite the name, it runs
  tactics (`EcScope.Tactics.process` in `process_dump`) and does
  mutate state.
- **Rationale**: queries are semantically read-only. Today each push
  clones the scope into the undo stack (waste) and forces the daemon /
  users to compensate with extra undos. Also simplifies the protocol-
  level classification: post-addition, `executable`/`doc_comment`
  advance uuid; `directive` (pragmas) and query forms do not.

### 8. Structured error output

- **Status**: landed.
- **Phase**: 0b.
- **Files**: `src/ec.ml` (classifier + JSON writer + `reply_error`
  wiring), `doc/llm/CLAUDE.md`, `doc/tooling-protocol.md` § 2.1.
- **Summary**: Every `ERROR` reply now carries an `ERROR-JSON:
  {code, phase, location, detail}` frame immediately after the
  header. PoC classifier: `TyError`/`TymodCnvFailure`/
  `RestrictionError` → `TypeError`; `EcParser.Error`/
  `EcLexer.LexicalError`/`EcParsetree.ParseError` → `ParseError`;
  `HiScopeError`/`EcCoreGoal.TcError` → `TacticFailure`; everything
  else → `Internal`. Location is extracted from the outer
  `TopError` wrapper when present, otherwise from the inner
  exception for the types that carry one. Protocol-level errors
  raised without an originating exception (e.g. REVERT range checks)
  fall through to `{code: Internal, phase: protocol, location: null}`.
- **Rationale**: the daemon's typed error taxonomy (protocol doc § 6)
  currently has to reverse-engineer EC's error strings to classify.
  Structured errors close that gap and stabilize the LSP
  `publishDiagnostics` payload.

### 9. Structured output for `print` / `locate` / `search`

- **Status**: planned.
- **Phase**: 0b draft, 4 landing.
- **Files (expected)**: `src/ecCommands.ml` (process_print,
  process_locate, process_search), adjacent JSON serializer near
  `EcPrinting`.
- **Summary**: JSON result alongside pretty-printed text for each of
  `print`, `locate`, `search`. Result shape is kind-tagged (operator,
  lemma, module, type, ...) with defining location, type, and
  containing theory.
- **Rationale**: required by LSP `hover` / `definition` / workspace
  symbol search, and by MCP `search_lemma`. Parsing the pretty-printed
  column output would lock the daemon to a specific EC build.
  (Partially overlaps addition 2's workspace index, but these are
  position / query-driven and needed even when the index is empty.)

### 10. Hover / type-at-point endpoint

- **Status**: planned.
- **Phase**: 0b draft, later landing (tentatively 4).
- **Files (expected)**: new module wiring a position-based lookup
  through `EcEnv` / `EcScope`; REPL command to invoke it.
- **Summary**: Given `(sentence_id, cursor_offset_in_source)`, return
  the resolved identifier's kind, fully-qualified name, type, and
  defining location as JSON. Null when the cursor is not on an
  identifier.
- **Rationale**: backs LSP `textDocument/hover` and single-file
  `definition` with data EC already has internally.

### 11. Structured SMT counter-examples

- **Status**: planned.
- **Phase**: later (Phase 5/6 range).
- **Files (expected)**: adjacent to where EC consumes Why3's result
  (`src/ecScope.ml` / prover glue), plus reply formatting in
  `src/ec.ml`.
- **Summary**: When SMT fails with a model rather than timeout, emit
  the Why3 model as a `{ var: value }` JSON structure alongside the
  pretty-printed diagnostic.
- **Rationale**: roadmap's "counter-example surfacing" feature; MCP
  `try_tactic` error payload can carry the model for LLM debugging.

### 12. Drop dead `break` parameter on `EcCommands.process`

- **Status**: landed (commit `5438314d6`).
- **Phase**: 0b (trivial cleanup).
- **Files**: `src/ecCommands.ml:958-961`.
- **Summary**: The `?break` argument is accepted and immediately
  `ignore`d. Remove it and all call sites.
- **Rationale**: dead code; small but in the same area we're already
  touching.

### 13. Structured execution (`EXEC-JSON`)

- **Status**: landed (v0 render-and-parse; direct-AST dispatch migration is
  an incremental v1 follow-up that does not change the wire).
- **Phase**: 3 (structured-execution substrate).
- **Files (expected)**: new meta-command in `src/ec.ml` dispatching
  directly into EC's execution entry points
  (`EcScope.Tactics.process`, `process_operator`, `process_print`,
  `process_pragma`, etc.) without round-tripping through the text
  parser; shared JSON envelope with addition 9.
- **Summary**: Accept a JSON-encoded EC command (tactic invocation,
  directive, declaration) and execute it directly. Bypasses
  `EcIo.xparse` for cases the schema covers; falls through to the
  text path for unsupported constructs. Response uses the normal
  `OK`/`ERROR` + `OK-JSON`/`ERROR-JSON` framing, with the OK-JSON
  envelope populated with structured post-exec metadata (the
  dispatched command's kind, any structured result payload, uuid).
- **v0 scope (Phase 3):**
  - **Tactic invocation**: `{kind:"tactic", name:"<tactic-name>",
    args:[{kind:"name"|"text"|...}]}`. `"name"` args (e.g. `apply H`,
    `rewrite -> L`) dispatch structurally. `"text"` is the escape
    hatch for any argument shape the schema doesn't yet cover —
    daemon passes the EC source fragment through.
  - **Directive execution**: `{kind:"directive",
    name:"print"|"search"|"locate"|"pragma", args:[...]}` with the
    same args envelope.
- **Deferred to v1 / semantic edit mode**:
  - Operator / type / lemma declarations (need addition 17's typed
    formula serializer to be worth it — text path is fine until
    then).
  - Tactics that take term arguments beyond names (same dep; accept
    `"text"` fallback in v0).
- **Rationale**: substrate for semantic edit mode (click a
  hypothesis → structurally invoke `apply H`), structured transcript
  of what was executed (proof-tree viz consumes this directly
  instead of inferring from text deltas), LLM tooling submitting
  tactics without the text round-trip and its parse-error risk, and
  tactic-catalog execution. The execution endpoints that the
  text-path parser feeds into already exist inside EC; this is the
  stable JSON entry to them.
- **Not for document editing.** The splicing of source buffers
  stays daemon-side (today's `repl_core.ml` plus the consolidation
  in Phase 3). Pushing document editing into EC would relocate
  complexity rather than solve it. See addition 16 below for the
  one PARSE-JSON ergonomics fix that *does* belong in EC.

### 14. Batch diagnostics with parse recovery (`ANALYZE-JSON`)

- **Status**: landed (v0 + scope-tagging extension; parse-recovery +
  cascade tagging still deferred to v1).
- **Phase**: 5 (LSP precondition).
- **Files (expected)**: `src/ecIo.ml` (parse-recovery points);
  `src/ec.ml` (new meta-command operating on a fresh scratch scope).
- **Summary**: Stateless meta-command taking a document body and
  returning `{ sentences: [...], diagnostics: [...] }` where each
  diagnostic carries `{sentence_id, code, phase, location, detail,
  cascade_of?}` and each sentence records the binders it introduces.
  Implementation: fresh scope; sentence-by-sentence; on parse error,
  skip to next top-level delimiter (`. `, `qed.`/`save.`/`admit.`) via
  parser recovery point and continue; on type/tactic error, EC's
  per-sentence atomicity already leaves scope intact, so continue;
  record names the failing sentence would have introduced (from partial
  parse or the unchecked AST) and tag downstream errors referencing
  them with `cascade_of: <parent_sid>`.
- **Rationale**: LSP `publishDiagnostics` wants every error in the
  document at once; interactive `<BEGIN>/<DONE>` can't accommodate that
  without polluting its semantics. Separate analysis pathway leaves
  the interactive flow untouched. Cascade policy (hide, group,
  downgrade) stays client-side — EC only tags.
- **v0 implementation (landed)**: `analyze_to_json` in `src/ec.ml`
  reuses PARSE-JSON's parse loop, builds a fresh scope via
  `EcCommands.initial ~boot:false ~checkproof:true`, and dry-runs
  every parsed `executable`/`doc_comment` action through
  `EcCommands.process_internal EcCommands.loader`. On exception, the
  scope is unchanged (assumption (a) holds — `process_internal` raises
  with the input scope intact) and the diagnostic is captured via
  the same `error_json_line` classifier (addition 8) with a
  `sentence_index` field added. Wire frames: `<ANALYZE-BEGIN>` /
  `<ANALYZE-DONE>` (inline) and `ANALYZE-JSON "<file>"` (file).
- **Scope-tagging extension (landed)**: each emitted diagnostic
  carries `enclosing_scope: { kind: "proof"|"theory"|"section",
  opener_sentence_index: N } | null`. Tracked by an opener/closer
  stack walked alongside the dry-run pass. Openers: `Gaxiom { PLemma
  None }` / `Grealize { pr_proof = None }` (proof), `GthOpen`
  (theory), `GsctOpen` (section). Closers: `Gsave _`, `GthClose`,
  `GsctClose`. Stack is updated textually — push/pop happen
  regardless of whether EC accepted the sentence — so a failing
  `qed.` still ends the textual proof for diagnostic-attribution
  purposes (matches the user's source-structural mental model).
  Cascade tagging across scopes (downstream errors that reference
  broken-scope names) remains deferred — see v1 deferrals below.
- **Synthetic-abort recovery (landed; Tier-2 wrapper)**: when a
  proof closer (`Gsave _`) raises, `analyze_to_json` feeds a
  synthetic `Gsave \`Abort` at the closer's location into
  `EcCommands.process_internal` to force-discard the broken proof
  state. Without this, EC's dry-run still considers the proof open
  and every subsequent top-level sentence errors with "cannot
  process [...] inside a proof script" — bogus errors that drown
  the real ones. With abort recovery, post-`qed.` sentences
  process at the outer scope and produce their real diagnostics.
  **Tier-2 per `doc/tooling-poc-plan.md` § "Shipping against
  upstream redesigns".** The architecturally clean version is a
  typed recovery API in `EcScope`/`EcCommands`
  (e.g. `recover_to_outer_scope : scope -> scope`) that
  `analyze_to_json` calls instead of synthesizing AST nodes;
  swap in when the EcEnv/EcSection redesign lands. Wire shape
  unaffected.
- **Deferred to v1**:
  - Parse-recovery past top-level delimiters (`.`, `qed.`/`save.`/`admit.`)
    with additional recovery points inside `abstract theory` /
    `section` / nested proof blocks.
  - Cascade tagging — record names a failing sentence would have
    introduced (token-level binder extractor for parse-failed
    sentences; AST inspection for type-rejected sentences) and
    annotate downstream errors with `cascade_of: <parent_index>`.
  - Pragma isolation — `Goption`/`Gpragma` inside the analyzed
    document still mutate global EC state. Push/pop a pragma stack
    around the call.
  - Notifier capture — currently emits `NOTICE:` lines on stdout
    during the dry run; daemon strips them, but a per-call
    capture-only notifier would tidy the wire.

### 15. Structured success output (`OK-JSON`)

- **Status**: landed (ec-core side; daemon-side consumer in same wave).
- **Phase**: 0b-tail (independent; ship anytime).
- **Files (expected)**: `src/ec.ml` (`reply_ok` emission path).
- **Summary**: Symmetric with addition 8's `ERROR-JSON`. Optional
  `OK-JSON: <json>` line after the `OK` header, carrying structured
  success metadata — reply kind, post-exec uuid, and a directive-
  specific payload slot that addition 9 will populate for
  `print`/`locate`/`search`. Most replies emit `OK-JSON: {}`.
- **Rationale**: eliminates client-side sniffing between free-form
  reply bodies and JSON lines, gives the wire a cleaner
  success/failure symmetry, and reserves an envelope for addition 9
  before that schema lands. Trivial EC change — cheap enough to land
  as a next-up commit rather than wait on a consumer.

### 16. `PARSE-JSON`: `start_offset` at first token

- **Status**: landed (ec-core side; daemon cleanup in same wave).
- **Phase**: 3 (cheap cleanup; landed independently ahead of addition 13).
- **Files (expected)**: `src/ec.ml` (`parse_to_json` offset
  calculation where sentence records are built).
- **Summary**: `PARSE-JSON`'s `sentences[].start_offset` currently
  includes any leading separator whitespace (blank lines,
  indentation) between the previous sentence's terminator and the
  current sentence's first token — separator bytes get attributed to
  the current sentence's range. Move `start_offset` forward to the
  first non-whitespace byte. Separator whitespace then cleanly
  belongs to neither sentence and lives in the gap between
  `previous.end_offset` and `this.start_offset`.
- **Client impact**: removes the `actual_sentence_start` scan every
  byte-level splicer is doing today (see [`repl_core.ml`]
  [repl-core]). Post-fix, `start_offset` is already what the client
  wants — insert / edit / delete byte ranges come straight off
  PARSE-JSON without a forward-scan.
- **Rationale**: one-line logical fix, eliminates a recurring
  client-side workaround, makes offset semantics intuitive
  (`[start_offset, end_offset)` == "the sentence's bytes").

[repl-core]: tooling/lib/repl_core.ml

### 17. EXEC-JSON v0.1 — compound tactics with nested args

- **Status**: planned (Phase 5/6 useful prerequisite; not blocking).
- **Phase**: post-Phase-5-core (Stage 5 / cache substrate window or
  later).
- **Files (expected)**: `src/ec.ml` (`EcExecJson` schema extension),
  `src/ecExecJson.ml`.
- **Summary**: Extend EXEC-JSON v0 to cover compound tactics that
  take nested tactic args. v0.1 scope:
  - Tactics: `have NAME : STMT [by TAC].`, `cut STMT.`,
    `pose NAME := EXPR.`, `wlog STMT.`, `gen NAME.`.
  - New arg kind `tactic` — recursive tactic invocation as nested
    JSON. Enables `by TAC` arg in `have`/`cut`/etc. Nesting depth
    bounded only by EC's grammar limits.
  - `text` still covers term/STMT args (typed formula serializer is
    addition 17 v2 / addition 20).
- **Rationale**: enables AST-level structural recovery in
  `RecoveryStrategy: best_effort_admit` on `proof/execToPoint`
  (rewrite `have h : Foo by smt` → `have h : Foo by admit` as a
  structural-AST transformation, no text rewriting). Catalog of
  recovery patterns is mirrored in `doc/lax-recovery-catalog.md`
  (or equivalent under cache-policy lax framing).
- **Expected scope**: ~150 LoC ec-core. Round-trip equivalence
  smoke must extend to cover the new compound shapes.

### 18. EXEC-JSON v1 — direct-AST dispatch + subgoal-addressing

- **Status**: planned (Tier 3 enabler, post-PoC).
- **Phase**: post-Phase-5/6.
- **Files (expected)**: `src/ec.ml`, `src/ecExecJson.ml`,
  `src/ecCommands.ml`, possibly `src/ecCoreGoal.ml` for
  subgoal-addressing API.
- **Summary**:
  - Direct-AST dispatch — bypass text path entirely; EXEC-JSON
    payload dispatches to `EcScope.Tactics.process` directly via
    structurally-typed actions.
  - Subgoal-addressing API — `{kind:"focus_subgoal", target:"first"
    | "last" | {index:N}}` as a structural arg. Tactics like
    `1: tac` become structural.
  - Tactic-chain combinators — `{kind:"chain", op:";", children:
    [...]}` for `;`-style sequencing; also `first`, `last`, `||`,
    `do n`, `try`, `repeat` as structural.
  - Tactic-applicability dry-run — `{kind:"check_applicability",
    ...}` returns `{applicable, would_introduce_subgoals,
    would_close}` without committing.
- **Rationale**: enables sub-sentence Tier 3 chain decomposition in
  `proof/execToPoint`'s `RecoveryStrategy` (preserves intermediate
  subgoal state across chained-tactic failures). Also enabler for
  semantic-mode S2 (applicability-filtered palette); benefits
  annotated proof-tree visualization, refactoring tools.
- **Expected scope**: ~200-300 LoC ec-core.

### 19. EC-core bullets-with-semantics

- **Status**: planned (independent EC addition; benefits manual proof
  writers + tooling).
- **Phase**: post-Phase-5; useful at v1.
- **Files (expected)**: `src/ecParser.mly`, `src/ecLexer.mll`,
  `src/ecScope.ml`, `src/ecCoreGoal.ml`.
- **Summary**: Make proof bullets (`-`, `+`, `*`) structural rather
  than cosmetic.
  - Bullets at increasing depth open subgoal-focus scopes.
  - Closing a bullet requires its scoped subgoals to be discharged.
  - Failure to discharge → error at bullet close (not at proof end).
  - `admit.` as a bullet body discharges its subgoal explicitly.
  - **Compat modes** for legacy proofs (workspace setting `proof.
    bulletSemantics: "strict" | "lenient" | "off"`):
    - `strict` — bullets enforced; mismatch is error.
    - `lenient` — bullets are hints; daemon honors when they match,
      falls back when they don't. Default for migration.
    - `off` — bullets purely cosmetic, no daemon use. Backward-compat
      for legacy.
- **Rationale**: makes proof-tree structure syntactically explicit.
  Benefits manual proof writing (clearer structure, errors caught at
  bullet-close not qed-time). Benefits tooling: subtree boundaries
  become syntactic; subtree admission, navigation, blast-radius
  scoping all simplify dramatically. Companion: bullet-emission
  formatter (auto-insert bullets from observed proof tree, helps
  legacy migration).
- **Expected scope**: ~150-300 LoC ec-core. Independent of tooling
  work; benefits both worlds.

### 20. Coherent REVERT + pp_form vs env state

- **Status**: forward-path root cause fixed (goals_to_json env
  selection, ~10 LoC ec-core). Tier-2 Fpr-branch pp fallback in
  EcPrinting still in place as defensive guard for the separate
  post-revert dangling-xpath case (now redundant for the
  forward-path case but kept). Revert-path itself + non-Fpr-form
  xpath paths still deferred to the EcEnv redesign.
- **Phase**: post-PoC.
- **Files**: `src/ec.ml` (LANDED — per-pregoal render env in
  `goals_to_json`). `src/ecPrinting.ml` (LANDED 362678ac7 —
  Tier-2 Fpr fallback; now redundant for forward-path but
  retained). Future work: `src/ecEnv.ml` (lookup-fallback paths
  or xpath-resolution rework), `src/ecCommands.ml` (REVERT
  abort-on-dangling).
- **Summary**: `EcPrinting.pp_form_core_r` raises
  `EcEnv.LookupFailure` while pretty-printing goals whose
  hypotheses or conclusions reference xpaths the current env
  doesn't index. Surfaces in two scenarios:
  - **Post-revert across a `proc`/`module`/`axiom` declaration**:
    surviving proof state holds memenv references (`mem &m`,
    `var x : A.guess`, etc.) into the now-rolled-back env. EC's
    REVERT restores the proof state from the undo stack but does
    NOT invalidate / rewrite xpath references inside it. PP
    chases → fails.
  - **First-time forward execution** of crypto game-style files
    using abstract theory instantiations, clone-with substitutions,
    section-bound declarations, or module-type vs concrete-module
    xpath patterns. Same pp lookup path; same failure. Less of a
    "REVERT bug" and more "pp's xpath chasing isn't robust to
    EcEnv's actual indexing semantics."
  - Affects both VSCode-via-daemon and emacs-PG (same EC core).
    PG users see a Fatal-error process crash; daemon users see
    the placeholder text we substitute (Tier-2 hardening on
    addition 3) as `<conclusion: stale env lookup>`. Daemon
    behavior is non-destructive but still bad UX.
- **Patch ladder** (cheapest first; tooling-side mitigations
  exist independently):
  1. **Daemon auto-restart on placeholder** (~30 LoC daemon, no
     EC change): detect placeholder string in goals JSON, issue
     restart + replay-to-cursor automatically. Slow (~1-3s per
     occurrence) but invisible to user beyond a brief
     "restoring…" notification. Masks the bug; doesn't fix it.
     Not implemented; obsoleted for the forward-path case by
     option 1.5 below.
  1.5. **EC: pp_form Fpr fallback (LANDED 362678ac7,
     redundant after 1.6 for forward-path)**. ~25 LoC in
     `EcPrinting.pp_form_core_r`'s Fpr branch: catch
     `EcEnv.LookupFailure` from `prF_memenv`, synthesize a
     minimal memenv (memory + `res : unit`) so the rest of the
     formula renders. Pp-only fallback. Originally landed as
     the forward-path mitigation under the (incorrect) hypothesis
     that the bug was `prF_memenv` lookup failing for abstract-
     bound xpaths. Per 1.6 below, the actual root cause was the
     daemon-side render env, not the lookup; with 1.6 in place
     `prF_memenv` doesn't raise for the in-proof abstract-module
     case and this fallback never fires for it. Retained as a
     defensive guard for the post-revert dangling-xpath case
     (item 2 below) and as belt-and-suspenders behind 1.6 (e.g.,
     a future caller that builds `ppe` incorrectly still survives
     with a `<conclusion: stale env lookup>` placeholder rather
     than a crash). Worth retiring on its own follow-up commit
     once 1.6 has soaked.
  1.6. **Daemon: per-pregoal render env in goals_to_json
     (LANDED, this commit)**. ~10 LoC in `src/ec.ml`. Root cause:
     `goals_to_json` built the render `PPEnv` from
     `EcScope.env scope` (lexical/top-level env) rather than
     `EcEnv.LDecl.toenv pregoal.g_hyps` (per-pregoal enriched env
     with the proof's hypothesis bindings: lemma module
     parameters like `(A <: D)`, memory tags `&m`, etc.). Using
     the scope env caused `pp_form` to fail resolving proof-bound
     xpaths like `A./f`, which `safe_pp` surfaced as the
     `<conclusion: stale env lookup>` placeholder. Note: other
     display sites in `src/ecCommands.ml` build the ppe from
     scope env too but feed it to `pp_goal` / `pp_goal1`, which
     internally enriches the ppe via `pre_pp_hyp` → `PPEnv.add_mods`
     before rendering the conclusion. `goals_to_json` was the
     unique site that bypassed `pp_goal` and called `pp_form`
     directly with the scope ppe. Fix uses a `ref` updated
     per-pregoal at the top of `subgoal_json`. Display-only,
     standard `ec-core:` workflow. Smoke regression in
     `run_lsp_speculation_smoke`'s abstract-theory case (already
     present from 1.5) now passes naturally without 1.5's
     fallback firing.
  2. **EC: detect dangling on REVERT, auto-abort proof** (~50 LoC
     ec-core, ~1 day). When REVERT crosses a sentence introducing
     names still referenced by surviving proof state, abort the
     proof with an explicit "proof aborted: revert past
     declaration X" message instead of leaving it dangling.
     Honest about the limitation; fixes the revert path. Still
     deferred; forward-path now covered by 1.5.
  3. **EC: pp_form fallback through undo stack** (~60-80 LoC
     ec-core, ~2 days). `EcEnv.Fun.by_xpath` (and similar) tries
     the most recent undo snapshot containing the xpath when the
     current env doesn't have it; uses it for printing only.
     Soundness defensible (display-only stale read); covers
     non-Fpr forms (hover types, hypothesis pp) the 1.5 fallback
     doesn't. Bigger TCB-adjacent footprint.
  4. **Real fix**: EcEnv/EcSection redesign restores xpath
     resolution invariant across REVERT and across cloned /
     sectioned declarations. Tier-3+ kernel work; date unknown.
- **Rationale**: bad UX to ship "stale env lookup" placeholders
  to users in routine flows. Patch 2 is the right "patch-ish" fix
  if/when prioritized; patch 1 is the daemon-side stopgap if real
  EC work isn't in the budget.
- **Tracker for current state**: addition 3 carries the daemon-
  side `safe_pp` hardening that catches any residual
  `LookupFailure` and surfaces a placeholder. With 1.6 landed,
  the forward-path in-proof abstract-module case no longer hits
  `LookupFailure` at all — `safe_pp` only fires for the
  genuinely-stale post-revert dangling-xpath case. This entry
  continues to track the broader EcEnv redesign work for that
  remaining path.

### 21. Directive replies omit goals body

- **Status**: landed. ~10 LoC in `src/ec.ml`.
- **Phase**: PoC.
- **Files**: `src/ec.ml` (inside `run_llm_repl.process_ec_input`).
- **Summary**: `process_ec_input` used to call `reply_ok_goals ()`
  unconditionally after every `P_Prog`, including programs that
  contain only directives (`Gprint`, `Gsearch`, `Glocate`,
  `Gpragma`, `GdumpWhy3`). That writes the current goal as the
  reply body. Directives don't mutate proof state, so the goal
  "after" is identical to the goal "before" — emitting it is
  redundant. More importantly, the directive's actual output
  streams via the notifier as `NOTICE:` lines (a separate channel
  from the body), so daemon callers that consume the reply body —
  like the `easycrypt/proof/print` LSP method — would see the
  current goal interleaved with what the user asked for.
  Fix uses `classify_global` (already shared with `analyze_to_json`)
  to detect directive-only programs and reply with empty body via
  `reply_ok ""` instead of `reply_ok_goals ()`. Mixed programs
  (executable + directive) and empty programs keep the legacy
  behavior.
- **Scope**: `ec llm` mode only. The `compile`, `-emacs` (PG),
  batch, and Tty REPL paths all use `EcTerminal` + `EcCommands.process`
  directly without LLM-protocol framing — they're untouched.
- **TCB**: `src/ec.ml` is the LLM entry point. Change is reply
  formatting, not soundness. Standard `ec-core:` workflow.
- **Tests** (in `run_lsp_speculation_smoke`):
  - `print true: error is null`
  - `print true: output non-empty`
  - `print on bogus qname: surfaces an informative message`
  - `print in-proof: output non-empty`
  - `print in-proof: output does NOT contain goal marker "Type variables"`
  - `print in-proof: output does NOT contain memory marker "&hr"`

### 24. STMT-JSON — structured per-instruction statement nodes

- **Status**: landed (commit `dcfa1f9db`). ~580 LoC across EC,
  daemon, vscode.
- **Phase**: PoC.
- **Files**:
  - `src/ec.ml` — `stmt_node_to_json` + `stmt_list_to_json` walkers
    over `EcAst.instr`. Block constructs (Sif / Swhile / Smatch)
    recurse into nested stmts; leaves (Sasgn / Srnd / Scall /
    Sraise / Sabstract) emit pp_instr text. `stmt_struct_node`
    wrapper produces the `{kind:"stmt", body:[...]}` envelope.
    `conclusion_to_json`'s S-variant judgments use
    `stmt_struct_node` for stmt_* positions; F-variants keep
    `pp_xpath_node` for now (xpath references; body not available
    without env lookup, deferred).
  - `tooling/lib/goal_view.{ml,mli}` — new `Cn_stmt` variant on
    `conclusion_node`; typed `stmt_node` variant covering all 8 EC
    instr kinds + match branches + optional `stmt_loc`.
    `decode_stmt_node` defensive on unknown kinds (degrades to
    `Sn_abstract` placeholder). `to_pp_text` extended via
    `stmt_node_to_pp_text` helper (best-effort flatten).
  - `vscode/src/extension.ts` — `ConclusionNode` + `StmtNode` TS
    interfaces mirror OCaml shape. `stmtTreeToRows` walker emits
    `ProgRow` entries with hierarchical position labels (parent.idx
    prefix). Block constructs emit a "header" row at their position
    + nested body rows; branch separators (`} else {`,
    `| pattern =>`, `}`, `end`) as label-only rows with no number,
    indented per depth. `renderRowsLeftNumbered` for hoare/phoare/
    ehoare; `renderRowsMiddleNumbered` for equiv/eager (with
    setting-driven aligned vs independent numbering).
- **Schema** (clean prefix of v_full):
  ```
  type ConclusionNode =
    | { kind: "pp", text }
    | { kind: "judgment", judgment_kind, ...labeled fields }
    | { kind: "stmt", body: StmtNode[] }   // NEW

  type StmtNode =
    | { kind: "asgn"|"rnd"|"call"|"raise"|"abstract", pp, loc }
    | { kind: "if",    cond_pp, then_body, else_body, loc }
    | { kind: "while", cond_pp, body, loc }
    | { kind: "match", target_pp, branches: {pattern_pp, body}[], loc }

  type StmtLoc = { start_line, start_col, end_line, end_col } | null
  ```
  `loc` always null in v0 — EC's IR drops parsetree positions during
  typecheck; threading them through is a follow-up amendment.
  Schema-stable (clients null-check).
- **Settings**:
  - `easycrypt-tooling.display.equivAlignment` (`"aligned"` default
    or `"independent"`) — controls equiv side-by-side numbering.
- **TCB**: `src/ec.ml` is the LLM REPL entry point (TCB-adjacent).
  Read-only printer extension, no soundness surface. Standard
  `ec-core:` workflow.
- **Known gaps (follow-up amendments, schema-stable)**:
  1. `loc` always null — populating requires EC IR parsetree
     position threading. Click-to-jump per instruction blocked.
  2. F-variant judgments (HoareF / equivF / eagerF) keep xpath
     references as Cn_pp leaves — needs env lookup to expand the
     referenced procedure body.
  3. Smatch pattern_pp shows just bound var names, no constructor
     name (PPEnv internals not exposed for the lookup).
  4. Print panel response shape doesn't yet carry stmt_node — print
     keeps text-only TM-tokenizer rendering. Display logic at the
     renderer level is unified (programWithLeftNumbers /
     programsWithMiddleNumbers handle both Cn_stmt and Cn_pp inputs)
     so once print response carries StmtNode[], it routes through the
     same renderer with no additional render code.
- **Bonus reuse** (unlocked by this addition):
  - Click-to-jump per instruction (once `loc` populated)
  - Sub-sentence stepping (Tier 3 from the original tooling roadmap)
  - Refactoring transforms (extract loop body, inline assignment)
  - Current-pc highlighting in equiv proofs (which left/right
    instruction is `proc.` currently positioned at)
  - "What does this instruction modify" hovers

---

### 23. GOALS-JSON conclusion tree (program-printing v0)

- **Status**: landed. ~150 LoC EC + ~280 LoC daemon + ~400 LoC vscode
  (incl. tokenizer module + structured renderers + style classes +
  TM bridge via vscode-textmate / vscode-oniguruma).
- **Phase**: PoC.
- **Files**:
  - `src/ec.ml` — `goals_to_json`: replaces flat `conclusion_pp:
    string` with structured `conclusion: ConclusionNode` recursive
    tree. Outermost form classified via `f.f_node` match; per-judgment
    extractors (`FhoareF/S`, `FbdHoareF/S`, `FeHoareF/S`, `FequivF/S`,
    `FeagerF`) emit labeled per-kind fields (pre / stmt / post +
    bound/cmp for phoare + stmt_left/right for equiv + transferred
    for eager).
  - `tooling/lib/goal_view.{ml,mli}` — adds `conclusion_node` typed
    variant + per-judgment `judgment_node` discriminator. `to_pp_text`
    helper for consumers that want flat text. `decode_conclusion`
    exposed for raw-JSON consumers.
  - `tooling/daemon/semantic_tui.ml` — replaces `sg.conclusion_pp`
    accesses with `Goal_view.to_pp_text sg.conclusion`.
  - `tooling/lib/repl_core.ml` — same migration for the REPL goal
    view.
  - `tooling/smoke/run_semantic_lib_smoke.ml` — fixture + assertions
    updated to new shape; exercise both `Cn_pp` leaf and the round-
    trip via `to_pp_text`.
  - `vscode/src/extension.ts` — Subgoal interface uses
    `conclusion: ConclusionNode`; `renderConclusion` walks the tree
    and dispatches per-judgment-kind layouts (stacked
    hoare/phoare/ehoare; side-by-side equiv with horizontal scroll on
    narrow widths; eager + transferred-stmt blocks). Prettification
    transform applies forall/exists/<=/>= → ∀/∃/≤/≥ etc.
  - `vscode/src/tokenizer.ts` — new module bridging vscode-textmate +
    vscode-oniguruma. Loads existing `easycrypt.tmLanguage.json` at
    activation; `tokenize(source) → TokenLine[]` then
    `tokensToHtml(...)` emits classified `<span class="ts-...">` HTML.
    Scope→class mapping table; webview style block defines
    `.ts-*` classes against VSCode token-color CSS variables.
  - `vscode/package.json` — new deps `vscode-textmate ^9.0.0` +
    `vscode-oniguruma ^2.0.1`; new setting
    `easycrypt-tooling.display.prettify` (default true).
- **Schema** (v0 — strict subset of v_full):
  ```
  type ConclusionNode =
    | { kind: "pp"; text: string }
    | { kind: "judgment"; judgment_kind: JudgmentKind; ...labeled... }
  type JudgmentKind = "hoare" | "phoare" | "ehoare" | "equiv" | "eager"
  ```
  Per-kind labeled fields (each is a `ConclusionNode`):
  - `hoare`: pre, stmt, post
  - `phoare`: pre, stmt, post, bound, cmp ("<="|"="|">=")
  - `ehoare`: pre, stmt, post
  - `equiv`: pre, stmt_left, stmt_right, post
  - `eager`: pre, stmt_left, stmt_right, transferred_left,
    transferred_right, post
  v0 emits only `pp` and `judgment` node kinds; sub-children inside
  judgments are always `pp` leaves. v1+ extends with propositional
  connectives (`implies`, `forall`, `and`, `or`, ...) so chain goals
  decompose; v_full adds structured terms inside leaf positions.
- **Architecture for tokenizer extensibility**: `tokenize(source)
  → TokenLine[]` interface lives in `vscode/src/tokenizer.ts`. v0
  backend is vscode-textmate via existing TM grammar. Future swap
  to Treesitter (web-tree-sitter + EC grammar) or LSP semantic
  tokens (textDocument/semanticTokens/full from daemon) is one
  module-internal change behind the same interface — no caller
  refactors.
- **TCB**: `src/ec.ml`'s `goals_to_json` is in the LLM REPL entry
  point (TCB-adjacent). Change is read-only formatting (no soundness
  surface). Standard `ec-core:` workflow.
- **No backcompat**: `conclusion_pp` field removed entirely (replaced
  by `conclusion`). All in-tree consumers migrated.
- **Tests**:
  - `run_semantic_lib_smoke`: fixture `{kind:"pp", text:"1 = 1"}`;
    assertions on `Cn_pp` leaf shape + `to_pp_text` round-trip.
  - All existing smokes pass against the new shape (no other smoke
    asserted on `conclusion_pp` content beyond presence).

---

### 22. `searchall` directive (overload-tolerant search)

- **Status**: landed. ~120 LoC across `src/{ecLexer.mll, ecParser.mly,
  ecParsetree.ml, ecCommands.ml, ecScope.ml, ecScope.mli, ec.ml}`
  + daemon-side wiring in VSCode picker (no `lsp_methods.ml` change
  needed — client constructs `searchall ...` source directly).
- **Phase**: PoC.
- **Files**:
  - `src/ecLexer.mll` — new `SEARCHALL` keyword
  - `src/ecParser.mly` — `SEARCHALL` token + `Gsearchall` production
  - `src/ecParsetree.ml` — `Gsearchall of pformula list` variant
  - `src/ecCommands.ml` — `process_searchall` dispatch
  - `src/ecScope.ml` — `Search.searchall` implementation
  - `src/ecScope.mli` — exported signature
  - `src/ec.ml` — `classify_global` returns `("Gsearchall", "directive")`
    (inherits UPSTREAM #21's "no goals body" semantics)
  - `vscode/src/extension.ts` — picker default verb is `searchall`,
    Stage 2 toggle button switches to `search` for strict mode
- **Summary**: EC's `search (...)` typechecks the pattern up-front
  via `EcTyping.trans_pattern`, which fails on operator-overload
  ambiguity (`_ <= _` errs because EC can't pick between `Int.(<=)`,
  `Real.(<=)`, etc.). `searchall` is a parallel directive that:
  1. First tries `trans_pattern` (clean queries cost nothing extra —
     same speed as strict `search`).
  2. On any typing failure, walks the parsetree pattern to collect
     every operator name referenced via `PFident`, enumerates ALL
     overloads of each via `EcEnv.Op.all`, builds a `ByOr` of
     `ByPath` clauses pointing at every overload's path. Loses the
     structural-shape filter but returns lemmas mentioning ANY of
     the candidate paths — ambiguity-recovery semantics.
- **Scope**: standalone `ec llm` REPL, daemon `easycrypt/proof/searchLemmas`
  via the source string. Independent of compile / `-emacs` PG / batch
  paths — pure new directive.
- **TCB**: read-only directive. Builds entirely on existing primitives
  (`EcEnv.Op.all`, `EcSearch.search`, `EcUnify`). No new soundness
  surface. Standard `ec-core:` workflow (NOT `ec-core-critical:`).
- **Default in VSCode**: `searchall` is the default mode; user can
  toggle to strict `search` per-search via the Stage 2 title-bar
  button. Workspace setting for default mode pinned for later.
- **Future reuse**: the parsetree-walk + per-overload union pattern
  is the building block for: hover (UPSTREAM #10) showing which
  overload an operator resolves to, completion suggesting all
  overloads, and a future "search across all kinds" feature
  (lemmas + ops + preds + types) that walks `EcEnv.{Op, Ax, Ty, Mod}.all`
  uniformly. Honest reuse: ~30-50 LoC of EcEnv table-walking
  patterns are shared; per-feature surfaces (resolution context for
  hover, prefix ranking for completion, multi-kind for global search)
  are independent work.
- **Tests** (in `run_lsp_speculation_smoke`):
  - `search (strict) on ambiguous \`_ <= _\` errs OR returns no hits`
  - `searchall on ambiguous \`_ <= _\` does NOT err`
  - `searchall on ambiguous \`_ <= _\` returns hits across overloads`
- **Known coverage gaps (follow-up amendments)**:
  1. **Multi-level abbreviation chains** — `unfold_overload` only
     unfolds one level. `abbrev a = b. abbrev b = le.` would add `b`
     to paths, but lemmas using `le` would be missed. Fix:
     recursive unfold with `Sp.t` cycle-detection set, ~20 LoC.
  2. **Parameterized abbrev bodies** — when the body is
     `f_lambda xs (Fapp(Fop p, args))`, peel the one application layer
     to also add `p` as a candidate path (in addition to the
     ByPattern lambda). Catches abbrev-of-application cases like
     `abbrev (<=) (x y : real) = real_le x y`. ~30-50 LoC.
- **Test invariant for the corpus** (introduce as gap fixes land):
  for any pattern `P` where strict `search P.` succeeds with `N`
  hits, `searchall P.` must return `>= N` hits — containment, not
  strict superset (typed pattern P is one disambiguation; `searchall`
  unions all of them). Smoke regression: differential check against
  a small library of patterns (`_ <= _`, `_ + _`, `_ = _`, etc.).
  Test corpus grows as edge cases are encountered.
- **Combined gap-fix cost**: ~80-100 LoC + ~70 LoC tests, ~1 day.
  Pin as #22-amendment for next "EC library polish" pass; not
  blocking for v0.

---

### 25. `proof/cancel` — `EcCancel` module + Cancel.check instrumentation

- **Status**: C1 + C2 + C3 + C4 landed — beta-1 gate point 1
  closed end-to-end. (ec-core module +
  FApi/find_rewrite_patterns instrumentation + LLM REPL signal-
  handler install + per-command flag clear + `EcCancel.Abort` →
  "canceled" reply; Why3 prover-bridge SIGTERM-on-cancel via
  `EcCancel.register_on_cancel` callback hook + lazy respawn on
  next call; daemon `easycrypt/proof/cancel` LSP method +
  `Proof_state.cancel_in_flight` + `Ec_llm_session.send_sigint`
  + analyze-session shutdown fix; vscode `easycrypt.proof.cancel`
  command + keybind (Cmd/Ctrl+Alt+.) + `preview.timeoutMs` setting
  + cancellable closer-sweep notification + reusable
  `withPreviewTimeout` helper for further preview paths.)
- **Phase**: pre-beta. Standard `ec-core:` workflow.
- **Files**:
  - `src/ecCancel.ml{,i}` (C1 + C2) — flag, `Abort` exn, `check`,
    `install_signal_handler` (idempotent), `clear`,
    `register_on_cancel` (callback registry — handler runs all
    registered callbacks after setting the flag, so signal-driven
    interrupters like Why3-kill plug in cleanly).
  - `src/ecCoreGoal.ml` (C1) — `Cancel.check ()` calls in `FApi.t_seq`,
    `t_seqs`, `t_or`, `t_do_r` (covers `t_do` + `t_repeat`),
    `t_ors_pmap` (covers `t_ors` + `t_ors_map` + `t_or_map`).
  - `src/ecHiGoal.ml` (C1) — `Cancel.check ()` at top of
    `LowRewrite.find_rewrite_patterns ~inpred` recursion.
  - `src/ec.ml` (C1 + C2) — install signal handler in
    `run_llm_repl` only (NOT batch mode); `EcCancel.clear ()` at
    the head of `process_ec_input` and `handle_load`; explicit
    `EcCancel.Abort` arm + a `_ when !cancel_requested` arm in
    both `with` clauses re-attribute cancel-induced exceptions
    (e.g. Why3 connection-lost from C2's SIGTERM) as a clean
    "canceled" reply and reset the flag.
  - `src/ecProvers.ml` (C2) — `why3_pid` ref captures the
    why3server child pid at fork time; `kill_why3 ()` (registered
    once with `EcCancel.register_on_cancel` on first successful
    spawn) sends only `SIGTERM` from the signal-handler context
    (Prove_client.disconnect cannot run safely there — closing
    the socket fd while a `Unix.read` is in flight on the same
    thread races and hangs). The peer-side close from why3's exit
    wakes the in-flight read; `EcCancel.check ()` inside
    `execute_task`'s blocking-loop body and at function entry
    turns the wakeup into a clean `Abort` and bails out of
    `EcSmt.select`'s iterate-with-more-lemmas retry. The
    `try_finally` cleanup branches on the cancel flag: on the
    cancel path, just `Prove_client.disconnect ()` (skipping
    `interrupt_call` / `wait_on_call` entirely — Why3's
    `send_interrupt` auto-`connect_internal`s when the socket is
    None, which would spawn a new why3server and spinloop on a
    stale id). Lazy respawn on next call (existing
    `is_connected ()` check at the head of
    `maybe_start_why3_server_` re-spawns transparently). The
    "background respawn fiber" optimization in
    `doc/cancellation.md` is deferred — lazy respawn meets the
    < 500ms SMT-bound abort budget without adding threading.
  - `tooling/smoke/run_ec_cancel_smoke.ml` (C2) — OCaml-level
    smoke driving `ec llm` directly: SIGINT mid-SMT (unsolvable
    Lagrange-style goal so the call doesn't close before the
    cancel window) returns "canceled" within
    `cancel_response_budget_s = 2.0s`; abort + trivial SMT
    afterward confirms session liveness + Why3 respawn; idle
    SIGINT is absorbed cleanly. Added to `tooling/smoke/dune` as
    its own test stanza.
  - `tooling/lib/ec_llm_session.ml` (C3) — `send_sigint t`
    delivers SIGINT to the EC subprocess without marking the
    session terminated (unlike `cancel`, which SIGKILLs).
  - `tooling/lib/proof_state.{ml,mli}` (C3) —
    `cancel_in_flight t` calls `Ec_llm_session.send_sigint`
    WITHOUT taking the proof-state mutex (the in-flight request
    holds the mutex; interrupting it is the whole point).
  - `tooling/lib/lsp_methods.ml` (C3) — registers
    `easycrypt/proof/cancel { uri }` returning
    `{ canceled: true }`. Per-request `seq` correlation deferred
    (current scope: cancel ALL in-flight work on the connection's
    primary session).
  - `tooling/daemon/main.ml` (C3) — explicitly
    `Ec_llm_session.close analyze_session` after `Lsp_server.run`
    exits in `serve_lsp_connection`. Without this, an in-flight
    debouncer fiber processing a long-running document can stall
    the conn-switch close by tens of seconds (the analyze
    session's ec subprocess keeps running until conn-switch
    cleanup forces SIGKILL).
  - `tooling/smoke/run_lsp_cancel_smoke.ml` (C3) — LSP-level
    smoke: didOpen with an unsolvable smt() doc, send
    `execToPoint` then `cancel`, assert cancel returns
    `{ canceled: true }` immediately, execToPoint surfaces a
    `canceled` diagnostic within budget, follow-up
    revertToPoint + goals succeed, daemon shuts down cleanly.
  - `vscode/package.json` (C4) —
    `easycrypt.proof.cancel` command (`EasyCrypt: Cancel
    In-Flight Tactic / SMT Call`); keybind Cmd/Ctrl+Alt+.;
    `easycrypt-tooling.preview.timeoutMs` setting (default 3000,
    minimum 100).
  - `vscode/src/extension.ts` (C4) — `sendCancel(uri)` helper
    sending `easycrypt/proof/cancel`; `handleCancel` command
    handler; `previewTimeoutMs` reader; `withPreviewTimeout`
    racing wrapper that fires `proof/cancel` on expiry;
    `handleSuggestClosers` rewired with `cancellable: true`
    progress notification + token-cancel-to-cancel wiring +
    timeout race. Goal-pane "Cancel" inline button deferred —
    the keybind + notification's Cancel button + command palette
    cover the user-facing affordance.
- **Summary**: introduce a single `EcCancel` module owning a
  cancellation flag, `SIGINT` handler installation, `Cancel.check ()`
  function (raises `Abort` if flag set), and `Abort` exception type.
  Instrument shared infrastructure to call `Cancel.check ()` at
  strategic points: FApi tactic combinators (`t_seq`, `t_seqs`,
  `t_or`, `t_ors_pmap`), iteration helpers (`t_do_r` covers both
  `t_do` and `t_repeat`), and pattern walks
  (`find_rewrite_patterns`). Individual tactics inherit cancellation
  through the combinators — no per-tactic instrumentation. Why3 /
  SMT subprocesses get SIGTERM'd on cancel via the prover bridge
  (C2); background respawn fiber so the cancel response returns
  immediately.
- **Latency targets**: 90th percentile abort < 100ms for typical
  tactics; < 500ms for SMT-bound aborts (one Why3 re-spawn).
- **Rollback**: commit-based — each layer (EcCancel module +
  instrumentation, prover-bridge kill, daemon LSP method, vscode
  dispatch) lives in its own commit. Reverting any one removes
  that layer cleanly. No runtime feature flag; reverting commits
  IS the rollback path.
- **Future supersession**: full cancellable-fiber rework — a
  proper fiber-based execution model with explicit yield points
  (similar to async/await) — replaces the v1 polling-flag
  approach. Future ec-core-critical territory; will need EC-dev
  discussion + design. Pinned in
  `doc/tooling-poc-plan.md` Open Architectural Points + tracked
  in `doc/cancellation.md` rollback-and-rearchitect checklist.
- **Tests**: cancel mid-tactic returns within budget; subsequent
  tryTactic against the same session succeeds; Why3 background-
  respawn doesn't block other operations; SIGINT during a
  pure-OCaml computation is delivered at the next combinator
  boundary.
- **Post-beta investigation — incremental Why3 reuse**. Today
  every iteration of `EcSmt.select` calls `execute_task`, which
  spins up a fresh `Call_provers.prover_call` (and re-sends the
  task to the prover subprocess). Folded into the planned
  EcSmt rewrite, the lifetime of the per-prover handle would
  extend across iterations, with new lemmas pushed via the
  underlying solver's incremental protocol (`(push 1) (assert
  ...) (check-sat)`). Cuts the per-iteration cost from
  re-elaborate + re-send to "send a few new asserts." Soundness
  review needed (we'd be trusting the solver's incremental
  engine). Pinned for after the beta-1 ship.
- **Post-beta investigation — SMT result memoization**. Cache
  `(canonical_task_hash, prover_binary_hash, timeout)` →
  prover answer. Prover-binary-hash (sha256 of the prover
  executable) is more robust than name+version (handles
  unversioned builds, in-tree forks). Timeout-asymmetric
  invalidation: a higher new call timeout doesn't invalidate
  a cached *definite* answer (Valid / Invalid stand for any
  budget); for a cached *Unknown / Timeout*, a higher new
  timeout triggers a retry (we may now succeed). Definite
  answers cached across EC restarts (with TCB story), Unknowns
  in-memory only. Independent of the goals_cache at Phase 5.0.

---

### 14′. Per-project sessions — `Session_manager` + URI routing

- **Status**: initial-beta core landed. Per-project session
  isolation working end-to-end (cross-project smoke green) +
  per-project EC spawn CWD wired (`Ec_llm_session.start_in_dir`,
  Session_manager passes `~cwd:project_root`) so EC's
  `easycrypt.project` upward walk picks up the right .project
  file. LRU eviction, idle timeout, and master `disableEviction`
  toggle all deferred to post-beta.
- **Phase**: pre-beta. Standard daemon-class change (no
  `ec-core:` prefix required); the only `ec-core:` touch was
  exposing `EcOptions.find_project_file`.
- **Files**:
  - `src/ecOptions.{ml,mli}` — lifted `find_project_file` from
    a local `let` inside `Ec.main` to a top-level export so
    callers (now: only `Ec.main` itself) share one definition.
  - `tooling/lib/session_manager.{ml,mli}` (new) — owns
    `(project_root → entry)` map, where `entry` carries the
    project's primary `Proof_state.t` + analyze
    `Ec_llm_session.t`. Resolves URI → project_root via a
    24-line walk (DUPLICATED from `EcOptions.find_project_file`
    because the daemon's boundary-allowlist forbids linking
    `ecLib`; pinned TODO under "Pending follow-ups"). Synthetic
    project_root = file's containing directory for files
    without an `easycrypt.project` up-tree.
  - `tooling/lib/lsp_methods.{ml,mli}` — `register_all` /
    `register_text_document` / `register_proof_methods`
    rewired to take `~manager` instead of `~proof_state` /
    `~analyze_session`. Each handler resolves its per-URI
    `proof_state` via `Session_manager.proof_state_for`.
    `easycrypt/proof/cancel` routes through
    `Session_manager.cancel_in_flight` so SIGINT only hits the
    URI's project session.
  - `tooling/daemon/main.ml` — `serve_lsp_connection` allocates
    a `Session_manager` instead of single `proof_state` +
    `analyze_session`. The debouncer's `process` callback
    resolves the analyze session per-URI through the manager.
    Connection-close calls `Session_manager.close` (closes
    proof + analyze for every project).
  - `tooling/smoke/run_lsp_proof_flow_smoke.ml` — three
    cross-project isolation checks (id 100-104): open a doc
    under `/tmp/sm-smoke-projA/`, step it 2 sentences, open a
    second doc under `/tmp/sm-smoke-projB/`, verify A's session
    stays active while B is independent. 36 checks total
    (was 33; +3 for session_manager).
  - `vscode/src/extension.ts` — `easycrypt.project`
    `FileSystemWatcher`. On change: prompt user with
    Reload / Keep choices. Reload sends
    `easycrypt/proof/restart` against an open `.ec` URI under
    the project's directory; the daemon respawns that project's
    EC subprocess (which picks up the new load paths). Keep
    adds the file to a session-local ignore set so the prompt
    doesn't fire again until manual reload via
    `EasyCrypt: Restart Language Server`.
- **Pending follow-ups (post-beta)**:
  - **`Session_manager.find_project_file` duplication**.
    Mirrors `EcOptions.find_project_file` byte-for-byte (24
    LoC). Daemon's boundary-allowlist forbids linking ecLib
    (load-bearing for the EC-merge plan). Resolve at EC-merge
    time via a small shared module that both can link.
  - **Multiple `easycrypt.project` files up the tree**. EC's
    current behavior: closest-only. User's earlier intuition
    was layered (deeper overrides shallower); confirmed today's
    behavior diverges. Pinned for a future EC discussion.
  - **LRU + idle-timeout + master `disableEviction` toggle**.
    Sessions accumulate forever in v0; relies on window
    restart to clear. Settings declared but unused.
- **Tests**: cross-project isolation smoke checks A's state
  survives B's mutation; daemon shutdown closes all sessions.
  No CWD-isolation smoke yet (would need real-filesystem
  fixtures with distinct `easycrypt.project` files; defer with
  the CWD threading work).

---

### 26. Proc rewrite — full applicable `rwarg1` subset

- **Status**: planned (beta-1 gate, point 2 of beta-prep list).
- **Phase**: pre-beta. Standard `ec-core:` workflow.
- **Files**: `src/ecParser.mly` (PROC REWRITE production change),
  `src/ecParsetree.ml` (`prrewrite` shape), `src/phl/ecPhlRewrite.ml`
  (`process_rewrite_rw` rework + dispatch on rwarg1 variant).
- **Summary**: extend `proc rewrite` from accepting a bare
  `pterm` to accepting a full `rwarg1` (matching the regular
  `rewrite` parser shape). Runtime reject for inapplicable
  variants with friendly error message
  `"the <variant> modifier is not applicable to proc rewrite"`.
- **Applicable**: rwside, rwrepeat, rwocc, rwmatch (incl. `[x in p]`
  context-binder form added in origin/main), rwpterms (single +
  multi), RWDelta (`/op` unfold of an op definition at the
  targeted instruction's expression).
- **Dropped (no residual to close — proc rewrite's discharge
  auto-closes via t_reflex)**: RWPr (no Pr at expression level —
  Pr is a formula construct), RWSmt (no residual to close),
  RWDone* (`//`, `//=`, `/=`, `//~=`, `/~=`, `//#`, `/#` — no
  residual), RWTactic (`#ring`, `#field` — closers; nothing to
  close).
- **Implementation notes**:
  - Thread `rwside` through `find_rewrite_patterns` + `t_rewrite`
    (currently both hard-coded `LtoR`).
  - Wrap discharge with `FApi.t_do` for `rwrepeat` (don't iterate
    `t_change` itself — work on the discharge equality, not the
    program).
  - Thread `rwocc` to the rewrite call's `(direction, occurrence)`
    arg.
  - Thread `rwmatch` to `find_rewrite_patterns`'s in-pattern
    bracket.
  - Iterate `t_change` per pterm in multi-pterm form.
  - Dispatch RWDelta to expression-level delta-unfold.
- **Future**: a "ring-as-simplifier" mode (non-closing variant of
  ring/field that simplifies expressions in-place) would unblock
  RWTactic for proc rewrite. Separate small EC addition; not in
  scope here. Pinned as a follow-up to address if user demand.
- **Tests**: round-trip each modifier (forward / reverse / repeat /
  occ / match / `[x in p]` / multi-pterm / RWDelta) through the
  proc-rewrite picker via `tryTactic`; assert outcome `'ok'` or
  `'err'` BUT NOT a parse error. Reject test for each dropped
  variant — assert the friendly message surfaces.

---

### 27. (Optional, deferred) Absolute-index focus tactic

- **Status**: deferred — `Pfocus` name already taken in EC for a
  different tactic combinator (`<focus> : <tactic>` runs `<tactic>`
  scoped to `<focus>`). Cycle-relative approach (point 4 of beta-
  prep, no EC change) chosen instead.
- **Future addition** (if user demand surfaces): add `goto N.` or
  `select N.` as the absolute-index focus primitive. Daemon's
  "focus current goal" command emits the absolute form rather
  than `cycle <delta>.`. Self-documenting in the resulting proof
  script.
- **Files (if pursued)**: `src/ecParser.mly` (new keyword + production),
  `src/ecParsetree.ml` (new tactic variant), `src/ecHiTacticals.ml`
  + `src/ecCoreGoal.ml` (process + tactical implementation).
- **Tests**: smoke that emits the new tactic + EC's parser accepts +
  EC's typechecker focuses correctly + replaying the script
  reproduces the same goal traversal.

### 28. Runtime SMT-invocation telemetry

- **Status**: landed (2026-08, "runtime SMT-invocation telemetry"
  commit; field report B14 / round 12').
- **Phase**: MCP v1.5.
- **Files**:
  - `src/ecGState.ml` / `.mli` — monotone `gs_smt_calls` counter on
    the gstate (create 0; copy preserves) + `smt_calls` /
    `bump_smt_calls` accessors
  - `src/ecSmt.ml` — one bump at the head of `EcSmt.check`, the
    single choke point every SMT discharge funnels through
  - `src/ecCommands.ml` / `.mli` — `smt_calls ()` accessor over the
    current scope's gstate
  - `src/ecLlm.ml` — per-phrase delta measured around each P_Prog
    action and spliced into the OK-JSON reply as `{"smt_calls":N}`
- **Summary**: solver invocations are counted at RUNTIME, so
  `by smt(...)` closers, the `/#` view, tacticals and any future
  surface syntax count by construction — a lexical scan was tried
  twice and was brittle twice. Telemetry only: no checking-behavior
  change; monotone-plus-deltas is immune to undo and scope sharing.
- **Tests**: MCP smoke pins `/#` = 1 invocation with zero `smt`
  tokens in the source (prof.ec fixture, total_smt = 4).

### 29. LOAD stop report + per-sentence LOAD ledger (`LEDGER-JSON`)

- **Status**: landed (2026-08, "LOAD stop report + per-sentence
  ledger" commit; field reports B15/B18).
- **Phase**: MCP v1.5.
- **Files**:
  - `src/ecLlm.ml` — Load loop counts COMPLETE top-level parse
    units, rolls a half-executed multi-command unit back to its
    boundary (`EcCommands.undo` to the unit-start uuid), records a
    per-sentence `(end_line, uuid_after)` ledger, and serves it via
    the new machine command `LEDGER-JSON`; the LOAD failure reply
    carries a structured stop report
  - `src/ecLlmJson.ml` / `.mli` — `load_error_json` (generic
    per-exception ERROR-JSON + guaranteed location + a `"load"`
    object with loaded sentences / last loaded line), built on the
    extracted `loc_json_field`
- **Summary**: a failed LOAD tells the client everything the loader
  knew — failing position (authoritative top-file parser loc even
  when the exception's own loc is missing or points into a
  require'd file) and how much of the file REMAINS LOADED; the
  session state IS that prefix, so clients keep it (MCP partial
  opens). The ledger gives clients a document-position -> uuid map:
  EC's undo keeps every uuid, so backwards repositioning becomes
  REVERT + short replay instead of a prefix re-run.
- **Tests**: MCP smoke pins the partial open (position, live goals,
  fix-in-place, repaired resync) and the exact-boundary rewind
  (`rewind:true`, zero re-execution).

---

### 30. `Log:debug` / `Log:info` loglevel pragmas

- **Status**: landed (2026-08, "Log:debug/Log:info pragmas" commit;
  ready-now queue item from the circuit-debug investigation).
- **Phase**: MCP v1.5.
- **Files**:
  - `src/ecCommands.ml` — `Pragmas.Log.{debug,info}` +
    `process_pragma` arms calling `EcGState.set_loglevel` on the
    current scope's gstate.
- **What**: the gstate loglevel (`Debug < Info < Warning <
  Critical`) had NO surface access: the default `Info` threshold
  drops every `Debug` notification (e.g. the circuit tactic's
  `EcEnv.notify env `Debug` traces in `ecCircuits.ml`), and
  nothing could raise it. `pragma Log:debug.` routes them through
  to the front-ends' notifiers (REPL NOTICE lines / MCP notices);
  `pragma Log:info.` restores the default. Mutates the live
  gstate like the boolean gstate flags: not undoable.
- **Tests**: `run_mcp_smoke` "pragma Log:debug / Log:info
  accepted" (an unknown `Log:*` name still warns
  `unknown pragma`).

## ANALYZE-JSON v1 deferrals (under addition 14)

For reference — these are deferred-from-v0 items tracked under
addition 14, not separate UPSTREAM entries:

- **Pragma isolation** — wrap `analyze_to_json` in global-pragma
  stack save/restore so `Goption`/`Gpragma` inside analyzed docs
  don't leak into live state. ~30 LoC ec-core. Same primitive
  serves the future `Inject_pragma` overlay (whenever that lands).
- **Parse-recovery past top-level delimiters** — recovery at `.`,
  `qed.`/`save.`/`admit.`, plus inside `abstract theory` / `section`
  / nested proof blocks.
- **Cascade tagging** — record names a failing sentence would have
  introduced (token-level binder extractor for parse-failed
  sentences; AST inspection for type-rejected sentences); annotate
  downstream errors with `cascade_of: <parent_index>`.
- **Notifier capture** — per-call capture-only notifier so `NOTICE:`
  lines don't stream to stdout during the dry run (currently noisy
  but daemon strips them).

---

## Exceptions (changes to EC core not destined for upstream)

None at this time.

Any change to EC core that is **not** upstreamable (workaround, local
hack, build-system peculiarity we can't fix in EC) must be listed here
with:
- files touched,
- rationale,
- revert / refactor plan at split time.
