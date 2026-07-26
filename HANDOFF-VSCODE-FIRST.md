# HANDOFF — beta-prep

Cross-session bootstrap for resuming work on the path to **initial
beta-1 ship**. Read alongside [ONBOARDING.md](ONBOARDING.md) and
[STATUS.md](STATUS.md); this doc focuses on **where we are heading
into beta** and **the 14 pinned points to close**.

## TL;DR (2026-04-29)

**Beta-1 gates: 6 of 14 closed this session, 1 in progress, 1
remaining, 6 deferred per discussion.** See full table in
[STATUS.md § Beta-prep priority list](STATUS.md).

- ✅ **Closed gates**: 1 (proof/cancel C1+C2+C3+C4), 3
  (rewrite-builder UX), 4 (execAll + focusCurrentGoal), 7-partial
  (keybind metadata + PG preset), 10-slim (.vsix packaging,
  slim variant), 13 (WIP commit hygiene), 14 (per-project
  sessions + Session_manager + CWD).
- 🛠 **In progress**: 10-bundled (release-merge with Circuits;
  `~/Repos/ec-tooling-release` worktree mid-build). Resumes in
  the next chat — see "Release-bundle status" section in
  [STATUS.md](STATUS.md).
- ⏳ **Remaining**: 12 (BETA.md + Report-a-bug command).
- ⏸ **Deferred per discussion**: 2 (proc rewrite full rwarg1),
  5, 6, 7-modal, 8, 9, 11. Post-beta-1.

- Initial beta-1 = self-contained `.vsix` distribution (slim +
  bundled-with-Circuits variants) for non-developer EC users;
  rolling-iteration on direct OOB feedback after.
- 14-point design discussion concluded 2026-04-28.
- Phase 5-parity end-to-end-shipped: Phases 0/2/3/4 + Phase 5
  (mouse line selection for proc rewrite/change at `a1b8b580f`).
- `main` is fully merged into `llm-interactive` — `git rebase
  main` is a no-op. Branch is **211 commits** ahead of
  `origin/llm-interactive`.
- `git rerere` enabled globally (autoupdate too) for the
  release-merge pipeline.
- Parity Phase 4 — lemma fuzzy search picker + token builders:
  ✅ shipped with two known UX bugs (commits `c181788dc daemon` +
  `53dd954c8 vscode`). New LSP method `easycrypt/proof/searchLemmas`
  dispatches EC's `search` directive and returns parsed
  Search_result.hit records. Three new commands:
  - `Cmd/Ctrl+Alt+M` — Move builder (incremental `move => t1 t2 ...`)
  - `Cmd/Ctrl+Alt+W` — Rewrite builder (incremental `rewrite t1 t2 ...`)
  - `Cmd/Ctrl+Alt+L` — Apply lemma picker (two-stage:
    pattern InputBox → fuzzy QuickPick of hits)
  Both builders use the existing tryTactic for cumulative speculation
  (no daemon-side session-handle wire needed). Lemma picker stage 2
  fires debounced previewApply on selection-change. Goal-pane
  preview-override infrastructure (`goalsPreview` Map) lets builders
  push speculative state into the pane with a "🔍 builder/lemma
  preview" badge.
  **Known bugs from initial Phase 4 ship — both RESOLVED later
  iterations:**
  1. ✅ Goal-pane preview not visible — root cause was that the
     `Goal_view.to_json` payload returned by the daemon's `tryTactic`
     was missing the `provenance` / `cas` envelope fields that
     `proof/goals` carries, which made the client-side
     `escapeHtml(g.provenance)` throw on `undefined` and silently
     abort the preview render. Fixed daemon-side: `tryTactic`'s
     `goalsAfter` is now wrapped with `provenance="speculation"` +
     `cas=zero_cas`. Client also now auto-opens the goal pane on
     builder/picker entry so the preview always has somewhere to
     render. Smoke regression in `run_lsp_speculation_smoke`.
  2. ✅ "Pick lemma" button rendering on rewrite builder — sidestepped
     by adding a `?` sentinel (typing `?` then Enter in the rewrite
     builder opens the lemma picker, regardless of whether the
     title-bar button renders). Title-bar button kept as visual cue;
     sentinel is the bulletproof path. Same sentinel pattern then
     extended to apply builder + apply phase-3.

## Closed since this doc was last refreshed

**This refresh — beta-prep snapshot** (commits `b4d908bef`,
`dfded581e`, `a1b8b580f`):

- **`merge: origin/main`** (`b4d908bef`) — 10 upstream commits
  pulled in + manual conflict resolution on `theories/algebra/Perms.ec`
  (took origin/main's `[smt_opaque]` form; HEAD's axiom form
  collided with existing `lemma allperms_r0`/`allperms_rS`
  proofs), `src/ecOptions.{ml,mli}` (union `llm_option` record:
  `llmo_input` + `llmo_provers` + `llmo_help` + `llmo_lastgoals`
  + `llmo_upto`; `llmo_input = ""` sentinel for REPL mode pending
  the LLM/MCP refactor), `doc/llm/CLAUDE.md` (concatenated both
  sides with separator block; full rewrite slated for post-MCP).
  Auto-merge fallout in `src/ec.ml`: `cm_quorum` field threaded
  to daemon-side checkmode init, `Gexpect` added to
  `classify_global` as directive, two `| `Llm llmopts ->` arms
  unified (input="" → REPL, else → batch).
- **`vscode: codepos module`** (`dfded581e`) — pure-helper TS
  module `vscode/src/codepos.ts` (~300 LoC) carrying tactic-
  source synthesizers for proc rewrite / proc change + 5-slot
  rewrite-builder helpers. Self-contained Node-runnable test file
  with 71 unit-test cases.
- **`vscode+daemon: mouse line selection (proc rewrite/change) +
  5-slot rewrite builder + MatchByPos`** (`a1b8b580f`) — ~1900
  LoC vscode + ~150 LoC OCaml smoke. Right-click on goal-pane
  program rows → context menu with "Rewrite at line N" / "Change
  range N..M". 5-slot rewrite builder (Cmd/Ctrl+Alt+W AND via
  line selection) — independently-editable side / repeat /
  occurrence / match / lemma slots with title-bar buttons + `?` /
  `[` / `@` sentinels + `✓ commit` button. Sentinels typed alone
  don't trigger preview parse-errors. Lemma picker integration
  via `singleDirection: true` (returns bare qname; rewrite
  builder owns direction independently). MatchByPos walker —
  emits `match-by-pos: { idx: 1-based }` for descendants of match
  arms (closes UPSTREAM #24's pattern_pp ctor-name gap).
  Speculation smoke 36 → 48 (12 new proc rewrite/change tactic-
  string round-trip cases).
- **14-point design discussion concluded** (this session) — beta-
  prep priorities pinned. See "What's in flight right now" below.

Major items shipped across subsequent iterations (this section grows
between full doc refreshes; treat as a roll-up of "things you
shouldn't re-investigate").

**Latest handoff snapshot — UPSTREAM #21 / #22 / #23 + supporting
work** (commits `dc0855aa1` … `3359b05be` on `llm-interactive`):

- **`daemon: Resolve cursor in inter-sentence whitespace to preceding
  sentence`** (`dc0855aa1`) — position-resolver fix per PG semantics +
  `proof_state.mli` contract.
- **`ec-core: searchall directive (UPSTREAM #22)`** (`7b0160887`) —
  including amendments (recursive abbreviation unfold + parameterized
  abbrev body head-extraction). VSCode picker default mode is
  `searchall`; toggle via 🎯 button.
- **`ec-core: Directive replies omit goals body + GOALS-JSON
  conclusion tree (UPSTREAM #21 + #23)`** (`dba1d5670`) — both touch
  `src/ec.ml`. Directives no longer leak goal text into reply body
  (fixes goal-bleed-into-print bug); structured `conclusion: ConclusionNode`
  tree replaces flat `conclusion_pp`.
- **`daemon: easycrypt/proof/print + tryTactic envelope shape`**
  (`badb56277`) — new LSP method for read-only directives; tryTactic's
  `goalsAfter` now carries `provenance="speculation" + cas` envelope
  (fixes silent preview-render abort).
- **`daemon: Goal_view structured conclusion (UPSTREAM #23 mirror)`**
  (`8b71276f7`) — typed `conclusion_node` variant + `to_pp_text` +
  `decode_conclusion`; consumers (REPL, semantic_tui, smokes) all
  migrated.
- **`tooling: Smoke regressions for UPSTREAM #21 / #22 / print
  method`** (`a831f6d71`) — +13 net assertions across speculation
  smoke (envelope, in-proof print no-leak, searchall, containment
  invariant).
- **`vscode: Bug fixes + print/search + apply phase-3 + comparison
  view + UPSTREAM #23 client + TM tokenizer + prettify`**
  (`3359b05be`) — bulk vscode commit (extension.ts has many shared
  change sites; splits would require patch-level git operations).
  Major items: print panel, print/search-symbols commands, apply
  comparison view (success/closed/error/needs-args boxes + cycle
  controls + auto-wildcard fallback + Shift+Enter → phase-3 handoff),
  ephemeral term editor popup, TacticSchema refactor, tactic
  launcher, tryTactic refactor (launcher + free-text + per-schema
  preview), auto-open goal pane on nav, file-switch refresh, many
  bug fixes (trailing-dot, intentionallyHiding flag, single-result
  preview, Esc rollback hierarchy, cycle keybinds context-gated),
  UPSTREAM #23 client side (renderConclusion walks tree, per-kind
  layouts: stacked hoare/phoare/ehoare with left line numbers,
  side-by-side equiv/eager with middle line numbers + horizontal
  scroll on narrow widths, sleek kind-tag, phoare bound with colored
  cmp pill, single outer scroll on .subgoal), TM tokenizer module
  (vscode-textmate + vscode-oniguruma in extension; theme-aware
  color palettes per body.vscode-{light,dark,high-contrast};
  multi-token sequence merger for split operators), prettify
  (built-ins + user-config replacements + toggle command + wrap
  toggle).

**UPSTREAM § 20 forward-path resolved** (commits `e1b0e4fc9`,
`89d95ead7`):

- **`ec-core: per-pregoal render env in goals_to_json`**
  (`e1b0e4fc9`) — root-cause fix for the `<conclusion: stale env
  lookup>` placeholder inside abstract-theory proofs. Previous
  diagnosis (Tier-2 wrapper at `362678ac7`) was wrong: tracing
  showed `prF_memenv` succeeds for abstract-bound xpaths against
  the correct env. The bug was the daemon-side `goals_to_json`
  building `PPEnv` from `EcScope.env scope` (lexical/top-level
  env) rather than `LDecl.toenv pregoal.g_hyps` (per-pregoal env
  enriched with the proof's hypothesis bindings: `(A <: D)`,
  `&m`, etc.). Fix: `ppe` is a `ref`, set per-pregoal at the top
  of `subgoal_json`. ~10 LoC. Display-only / standard `ec-core:`
  workflow (NOT `ec-core-critical:` despite the original framing
  — turned out to be a daemon-side serializer bug, not a
  soundness-touching kernel issue).
- **`ec-core: Retire Tier-2 Fpr-branch pp_form fallback`**
  (`89d95ead7`) — wrapper at `362678ac7` is now redundant for
  the in-proof case. Removed. `safe_pp` in `goals_to_json` still
  catches genuinely-stale post-revert dangling-xpath
  `LookupFailure`s (UPSTREAM § 20 v1 territory), surfacing the
  placeholder rather than crashing — so the wrapper retirement
  doesn't regress the deferred path.
- See project memory `project_ec_hyps_vs_scope_env.md` for the
  hyps-env-vs-scope-env diagnostic guidance (load-bearing for
  any future pp-related debugging in EC).

**Pre-existing landings** (commits `dc9be0e60`, `dcfa1f9db`):

- **VSCode prettify formula fix** (`dc9be0e60`) — formula leaves
  (`escapeOrPrettify`) now route through TM tokenizer. `Pr`, `<$`,
  and other table entries fire correctly inside formula bodies
  like `Pr[A.guess(x) @ &m : ...]`. Bonus: formulas get TM syntax
  highlighting too (forall/exists/fun keywords colored in pre/post).
- **UPSTREAM #24 (STMT-JSON)** (`dcfa1f9db`) — per-instruction
  structured statement nodes landed end-to-end.
  - EC: `stmt_node_to_json` walker over `EcAst.instr` covering all
    8 variants (Sasgn / Srnd / Scall / Sraise / Sabstract / Sif /
    Swhile / Smatch). S-variant judgments emit `Cn_stmt` for stmt
    fields.
  - Daemon: `stmt_node` typed variant + `Cn_stmt` on
    `conclusion_node`. Defensive decode + `to_pp_text` flatten.
  - VSCode: `stmtTreeToRows` walks the tree producing
    hierarchical-position rows (1, 2, 2.1, 2.2, 3 sub-numbering
    inside nested blocks). Block constructs render headers + body
    rows + branch separators; depth-based indentation. Equiv
    side-by-side: aligned-by-row (default) or per-side independent
    via `easycrypt-tooling.display.equivAlignment` setting.
  - Known gaps documented as follow-up amendments (UPSTREAM #24):
    `loc` always null (no EC IR positions yet), F-variant
    judgments keep xpath as Cn_pp, Smatch pattern_pp lacks
    constructor name, print panel response not yet stmt-structured
    (display logic unified at renderer; print can switch later
    without render rewrite).

Roll-up of pre-snapshot work (still relevant — kept from prior
refreshes):

- **UPSTREAM #21** — directive replies omit goals body. EC's
  `process_ec_input` no longer emits `reply_ok_goals ()` after
  directive-only programs; goal text no longer leaks into the daemon's
  `easycrypt/proof/print` output when the user prints mid-proof.
  ~10 LoC `ec-core:` change in `src/ec.ml`. Smoke regression in
  `run_lsp_speculation_smoke` ("print in-proof: output does NOT
  contain goal marker").
- **Daemon: `easycrypt/proof/print` LSP method** — wraps EC's `print`
  directive (any read-only directive, actually); returns
  `{output, error}`. Used by VSCode print panel + search-symbols
  preview.
- **Daemon: position resolver fix** — cursor in inter-sentence
  whitespace resolves to PRECEDING sentence (matches PG / matches
  the `proof_state.mli` contract), not the next one. Smoke
  regression.
- **VSCode print panel** — webview with `enableFindWidget: true`,
  `📋 Open in editor` button posts content to a scratch `.ec` doc
  for users who want native editor controls.
- **VSCode print/search commands** — `Cmd/Ctrl+Alt+;` (print qname),
  `Cmd/Ctrl+Alt+Shift+;` + right-click context menu (print symbol
  under cursor), `Cmd/Ctrl+Alt+/` (search-symbols browse mode).
- **VSCode comparison view for apply lemma picker** — top: current
  goal (unchanged); bottom: green box (success + cycle controls) /
  gold box (closes focused goal) / red box (does not apply +
  err message). Cycle controls work via context-gated keybinds
  (`Cmd/Ctrl+Alt+]/[`) so they don't dismiss the picker.
- **VSCode auto-open goal pane on navigation** + file-switch refresh.
- **VSCode auto-wildcard fallback on apply picker** — parallel
  probes with N=0..5 wildcards; smallest-N-that-works wins;
  badge shows `+N wildcards`; insert path uses the resolved source.
- **VSCode TacticSchema refactor** — schema-driven builders. Tactics
  declared as data: id, label, hint, cumulative, sentinels,
  wildcardProbe. Single `runBuilder` consumes the schema. New
  schemas (have, case, elim, exact, apply) plug in cheaply.
  Tactic launcher (`Cmd/Ctrl+Alt+B`) lists all schemas via fuzzy
  pick. `?` sentinel = lemma picker for rewrite/apply.
- **VSCode ephemeral term editor popup** (`editTermInPopup`) — small
  webview with multi-line `<textarea>`, Cmd+Enter commit / Esc
  cancel, dispose-on-finish. Reusable primitive — used by `??`
  sentinel in apply phase-3, planned for hover-to-edit, future
  local-edit-mode arc, program-printing v1 inline editor.
- **VSCode apply phase-3 arg builder** — Shift+Enter (or 🔧 button)
  in apply lemma picker hands off to a single-level addressable
  arg builder. Pre-populated from auto-wildcard probe so user
  starts at `apply qname _ _ ...` matching their preview.
  Position-aware editing: arrows ◀ ▶ navigate without deleting;
  Enter at non-end position replaces; Enter on empty mid-list
  deletes. Sentinels `?` (lemma picker), `??` (popup), `<<` / `>>`
  (move position), `_` (literal wildcard token).
- **VSCode tryTactic refactor** — `Cmd/Ctrl+Alt+T` opens a fuzzy
  launcher with `free text` (legacy one-shot) + every tactic
  schema. Free-text fallback preserves the prior behavior.
- **VSCode goal pane gets `enableScripts: true`** for cycle
  postMessage handler (also serves any future webview-button needs).
- **Disposal-on-hide bug class fixed** — `intentionallyHiding` flag
  in both `runBuilder` and `runApplyPhase3` prevents `onDidHide`
  from disposing the InputBox when it's hiding to launch a sub-
  picker / popup. Without this, the popup webview taking focus
  would dispose the parent input mid-flow and break `input.show()`
  on return.

Doc refreshes happen on natural seams (between major phases).
Until then, this list is the canonical roll-up.

## What's in flight right now (2026-04-29)

**Release-bundle merge.** All beta-1 gates closed except 12
(BETA.md). Currently iterating on the
`release/beta-1-circuits` build (worktree at
`~/Repos/ec-tooling-release`) — combines `llm-interactive` +
Circuits' EC-core changes (`bdep_ecCircuitsRefactor` minus its
inherited `origin/vscode` content) for the bundled `.vsix`.

See [STATUS.md § Release-bundle status](STATUS.md) for the full
detail of resolutions applied so far.

**14-point beta-prep priority list — phasing (legacy ordering):**

- **Initial-beta gates (close before beta-1 ships)**: 1, 2, 3, 4,
  7-partial, 10, 12, 13, 14.
- **Immediately post beta-1 ship**: 6, 7-modal, 9, 11.
- **Post-beta later**: 5, 8 + (b)/(c) follow-ups in
  [doc/session-model.md](doc/session-model.md).

Full pinning detail in [STATUS.md § Workflow status](STATUS.md);
design docs:
- [doc/cancellation.md](doc/cancellation.md) — `proof/cancel` v1
  scope, instrumentation points, rollback boundary, future-fiber-
  rework checklist.
- [doc/session-model.md](doc/session-model.md) — per-project
  sessions; multi-session axis (per-connection × per-project,
  shared-via-`attachTo` label); lifecycle.
- [BETA.md](BETA.md) — install + first-proof + report-bug + known
  limits, the user-facing entry point.

## Branch state

- Worktree: `/Users/gdel/Repos/easycrypt-tooling`.
- Branch: `llm-interactive`, ~197 commits ahead of `origin`.
- Smokes: full suite green (`dune build @runtest` exit 0). 19
  test stanzas + 1 diagnostic. Speculation smoke 48 cases
  (proc rewrite/change tactic-string round-trip).
- VSCode TS unit tests: 71 cases on the `codepos` module via
  `node out/codepos.test.js` after `npm run compile`.
- Untracked at repo root: `SDist_repro.ec` (16-line minimal
  UPSTREAM § 20 repro file, kept as reference; gitignored).

For the full session log: `git log --oneline llm-interactive
^b8cf78b04` (b8cf78b04 = "docs: Add HANDOFF-VSCODE-FIRST.md for
next-session bootstrap" — the doc's first commit).

## What's working end-to-end now

`ecd daemon --stdio` (or `ecd daemon` for socket mode) serves a full
LSP surface with the daemon-side machinery for PG-style proof
authoring:

1. **Lifecycle**: initialize / initialized / shutdown / exit.
2. **textDocument**: didOpen / didChange / didClose. didChange
   triggers debounced `ANALYZE-JSON` → `publishDiagnostics` AND
   `Proof_state.reconcile` (Slice D) — if the new source diverges
   inside the locked region, the primary session reverts to the
   last common-prefix sentence and emits `stateChanged`.
3. **Real proof methods** (Slice A) — all back a per-connection
   `Proof_state` that owns one primary `Ec_llm_session`:
   - `easycrypt/proof/step { count? }` — advance one (or N)
     sentences, skipping Meta. Returns `advancedTo` sid +
     `atEndOfDocument` flag.
   - `easycrypt/proof/back { count? }` — symmetric.
   - `easycrypt/proof/execToPoint { target: sid|position }` —
     advance / replay to the named sentence. Position-based target
     resolves to the immediately-preceding sentence if the cursor
     falls in inter-sentence whitespace.
   - `easycrypt/proof/revertToPoint { target: sid|position }` —
     symmetric.
   - `easycrypt/proof/goals { uri }` — returns the GOALS-JSON
     envelope at the current state. Degrades to inactive stub
     when no document bound. provenance/CAS still stub until
     Phase 5.0.
   - `easycrypt/proof/restart { uri }` — tear down + respawn
     primary subprocess.
4. **`stateChanged` notifications** carry `currentSentenceId`,
   `currentEndPosition` (LSP 0-based), monotonic `seq`. Emitted
   on every state-mutating call.
5. **publishDiagnostics** with scope-tagging + synthetic-abort
   recovery (UPSTREAM addition 14 extensions). `data.scope` lets
   clients collapse diagnostics by enclosing scope; failed
   proof closers no longer cascade into "cannot process inside
   proof script" noise.

VSCode extension consumes all of the above:

- Spawns `ecd daemon --stdio` via `vscode-languageclient`.
- Locked-region tint span `(0,0)` → `currentEndPosition`.
- Goal pane (Slice C) — side-by-side WebviewPanel rendering
  GOALS-JSON envelope; auto-refreshes on stateChanged.
- Commands + keybindings for step / back / exec-to-cursor /
  revert-to-cursor / goals / restart.
- In-flight guard on step/back so OS keyboard-repeat doesn't
  flood the daemon.

## Known issues — RESOLVED in this session

- Shutdown response race in `lsp_server.run` (incorrect inline
  `request_shutdown` from the shutdown handler). Fixed in
  `cfb1da0ed`.
- `tooling/lib/dune` listed unused `lsp` opam dep. Dropped in
  `dc8bd7319`.
- Debouncer fired overlapping `process` calls (race on session
  Buf_read). Serialized via Eio.Mutex in `7a6318d03`. Two new
  regression tests in `run_substrate_smoke`.
- `lsp_server.write_mutex` was stdlib `Mutex.t` (deadlock-detects
  in Eio's single-thread fiber world). Switched to `Eio.Mutex` in
  `e474a41ad`. Two regression tests added (`run_lsp_io_smoke`
  case 7 + `run_lsp_proof_flow_smoke` pipelining).
- Sentence_id duplicate-source collision broke step past
  `sp 1 1.`-style repeated lines. Track `current_index`
  directly in `Proof_state` (`c5974205a`).

## Known follow-ups (open)

- **`proof/cancel`** — pinned in `doc/lsp-schema.md` for the
  cancellable-fiber rework (open architectural point #3). Slice 4
  of the parity plan (lemma picker preview) waits on it.
- **Auto-restart of analyze session on death** — currently a
  failed analyze leaves the connection in a degraded state until
  the user reloads the window. Restart-in-place would be smoother.
- **Cascade tagging** in ANALYZE-JSON v1 (UPSTREAM addition 14
  deferral). Scope tagging shipped (this session); cascade
  tagging would let clients suppress downstream errors that
  reference broken-scope names.

## Recommended next session — beta-prep series

The 14 pinned points are sequenced into three phases. The
**initial-beta gates** are 8 items; closing all of them produces
the beta-1 deliverable. Recommended order for the beta-1 series:

### Beta-1 series (sequential, each builds on prior)

#### A. `proof/cancel` (point 1)

Hang recovery — gating beta because looping rewrites + slow SMT
calls lock the editor with no escape today. See
[doc/cancellation.md](doc/cancellation.md) for full design.

Land as four commits:
- **C1 (ec-core)**: new `EcCancel` module — cancel-flag,
  signal handler installation, `Cancel.check ()` function,
  `Abort` exception. Instrument shared infrastructure: FApi
  combinators (`t_seq`, `t_first`, `t_or`, `t_seqs`),
  `t_repeat` / `t_do` helpers, `find_rewrite_patterns` walks.
  ~60 LoC total.
- **C2 (ec-core)**: prover-bridge subprocess kill — SIGTERM
  Why3 child on cancel; background-respawn fiber so cancel
  response returns immediately and next SMT call awaits the
  spawn. ~40 LoC.
- **C3 (daemon)**: `easycrypt/proof/cancel { uri, seq? }` LSP
  method. Per-request `seq` ID; convenience wrappers for
  "cancel all" / "cancel current". Resolves URI → project
  session (per [doc/session-model.md](doc/session-model.md)) →
  SIGINT to that session's EC subprocess. ~30 LoC.
- **C4 (vscode)**: preview-cancel dispatch + timeout
  (3000ms default, `easycrypt-tooling.preview.timeoutMs`
  setting) + Cancel button in the goal-pane title. On supersede
  or timeout, send `proof/cancel` and clear preview. ~50 LoC.

Smokes: cancel mid-tactic returns within budget; subsequent
tryTactic succeeds; Why3 background-respawn doesn't block other
operations.

#### B. EC parity for proc rewrite (point 2)

Match the regular `rewrite` parser: `PROC REWRITE side? pos
r=rwarg1` (full rwarg1, runtime reject for inapplicable variants
with friendly error). Applicable: rwside, rwrepeat, rwocc,
rwmatch (incl. `[x in p]`), rwpterms (single + multi), RWDelta.
Dropped (no residual to close): RWPr, RWSmt, RWDone*, RWTactic.

Update `process_rewrite_rw` in
[src/phl/ecPhlRewrite.ml](src/phl/ecPhlRewrite.ml):
- thread `rwside` through `find_rewrite_patterns` + `t_rewrite`
  (currently hard-coded `LtoR`).
- wrap discharge with `FApi.t_do` for `rwrepeat`.
- thread `rwocc` to the rewrite call's `(direction, occurrence)`
  arg.
- thread `rwmatch` to `find_rewrite_patterns`'s in-pattern bracket.
- iterate `t_change` per pterm in multi-pterm form.
- dispatch RWDelta to expression-level delta-unfold.
- runtime reject the dropped variants with
  `"the <variant> modifier is not applicable to proc rewrite"`.

~80-120 LoC ec-core. Smokes: round-trip each modifier through
the proc rewrite picker via `tryTactic`.

#### C. Rewrite-builder UX fix (point 3)

Move accumulated-term summary into `input.title` (two-line, never
pushed by `validationMessage`):
- Line 1: `EasyCrypt: rewrite — committed: <args>` (or `proc
  rewrite{side} at <cp> — committed: <args>` for proc rewrite).
- Line 2: `in-flight: <slots-summary>` — `(empty)` placeholder
  always.

Overflow handling on long committed lists: truncate `…+M more`
with click-to-expand reveal + wrap. Errors truncated to first
line + ~120 chars in `validationMessage`; full error to a
dedicated Output channel "EasyCrypt: tactic preview" via a
`(detail)` button. Severity Error for tactic failures, Info for
sentinel hints.

~80 LoC vscode/src/extension.ts.

#### D. Parity Phase 1 finish (point 4)

- `easycrypt/proof/execAll { uri }` LSP method — daemon-side
  iterator over `Proof_state` advancing all remaining non-Meta
  sentences. Stops on first non-Meta error (matches PG's "process
  to end" UX). Inherits cancellation from point A — `proof/cancel`
  rolls back to last-executed sentence. Emits `stateChanged` per
  sentence.
- "Focus current goal" command (UI-only Cmd/Ctrl+Alt+]/[ stay as
  display-only; new command emits stock-EC tactic for offline
  re-checkability): computes
  `delta = displayed_index - current_index` and inserts
  `cycle <delta>.` at cursor. ~30 LoC vscode + smoke.

~50 LoC daemon + ~50 LoC vscode + smoke.

#### E. Keybind metadata audit + PG preset (point 7-partial)

`vscode/package.json` audit: every command has
`category: "EasyCrypt"` + clear `title`. PG preset: parallel
keybind entries gated on `easycrypt-tooling.keybindings.preset`
context. Modal mode deferred to immediately-post-beta-1.

~40 LoC `package.json` + ~10 LoC extension.ts (preset toggle
command + context setting).

#### F. `.vsix` packaging (point 10)

- `vsce package` → produces slim `.vsix` (no bundled binaries).
- Bundle variant: pre-built `ec.native` + `ecd` for darwin-arm64,
  darwin-x64, linux-x64. Use `vsce package` with platform-
  specific entries.
- Binary discovery chain: `EC_BIN` / `ECD_BIN` env vars →
  workspace setting (absolute path or PATH-searched name) →
  `which ec` / `which ecd` → bundled fallback if shipped.
- Preserve nix devshell.

~1 day total: build script for the bundled-binary entries +
discovery wiring in `extension.ts`.

#### G. `BETA.md` (point 12)

Single getting-started doc at repo root. Sections:
- Install (slim vs bundled `.vsix`).
- First proof walkthrough.
- Keybind cheat sheet (default + PG preset).
- Settings reference.
- Known limitations (rolling beta).
- Reporting bugs (OOB direct message + the `Report a bug`
  command).

`Report a bug` command (~30 LoC vscode): bundles daemon log +
extension state into a tarball; opens it in editor for the user
to copy-attach.

#### H. WIP commit hygiene (point 13) — done at `dfded581e` + `a1b8b580f`.

### Post beta-1 ship (immediately)

Items 6 (code consolidation pass + state-machine refactor),
7-modal (modal mode design + impl), 9 (LLM/MCP refactor), 11 (UX
benchmark suite). These iterate on user feedback from rolling
beta.

### Post-beta later

Items 5 (two-point chaser; surfaces only if a specific bug forces
it), 8 (cache substrate; arch needs more design), session-model
(b)/(c) follow-ups (reconnect-survival, cross-connection
sharing).

## How to verify everything still works

```bash
dune build                  # clean
dune build @runtest         # all 19 (test) stanzas green; 48 cases in speculation smoke
scripts/boundary-lint.sh    # clean
cd vscode && npm run compile && node out/codepos.test.js  # 71 TS unit cases ALL PASS
```

Manual VSCode demo (in nix devshell with node available):

```bash
cd vscode && npm install && npm run compile
# Then F5 from the repo root in VSCode (uses .vscode/launch.json).
# Set easycrypt-tooling.ec.path if your EC binary isn't named
# 'easycrypt' (e.g. 'ec.native').
```

Open a `.ec` file in the Extension Host; step with Cmd/Ctrl+Alt+N;
Cmd/Ctrl+Alt+G to open the goal pane. Cmd/Ctrl+Alt+W for the
5-slot rewrite builder. Right-click on a program row in the goal
pane (when in a hoare/equiv goal) for proc rewrite / proc change.

## Open architectural points (still parked)

User will re-raise post-beta:

1. EC-merge codebase separation inside merged `ec` binary.
2. EC-merge fork-safe workers refactor scope.
3. Full cancellable-fiber rework superseding `EcCancel` v1
   (post-beta re-architecture; rollback via reverting the cancel-
   v1 commits).
4. Two-point chaser daemon architecture pivot — defer unless
   a specific bug / feature / UX issue forces it earlier.
5. Phase 5.0 cache substrate.
6. Reconnect-survival + cross-connection session sharing
   ([doc/session-model.md](doc/session-model.md) (b)/(c)).
7. Daemon ↔ ec binary merge — collapses ec/ecd distinction post-
   beta.

## Stack workflow (2026-04-29)

**Next concrete deliverable**: finish the release-bundle build
loop in `~/Repos/ec-tooling-release`. We are mid-iteration on the
release-merge of Circuits onto `llm-interactive`. Most of
the merge is resolved; remaining work is reactive — the user
runs `make`, pastes errors, I patch.

**After the release builds**: run smokes against the merged
tree. If they pass, package the bundled `.vsix` via `vsce
package --target darwin-arm64`. linux-x64 build is a follow-up
(user has a build machine).

**Then**: gate 12 (`BETA.md` + Report-a-bug command) is the last
beta-1 item. After that, **initial-beta-1 ships**.

**Files for the next session** (read in this order):
1. [STATUS.md § Release-bundle status](STATUS.md) — full state
   of the release-merge pipeline.
2. The build-loop log from where the user left off — they'll
   paste the next `make` failure.
3. [STATUS.md § Beta-prep priority list](STATUS.md) — closed/
   in-progress/remaining table.

The release-merge state is preserved across sessions:
- `~/Repos/ec-tooling-release` worktree on
  `release/beta-1-circuits` branch.
- `/tmp/ec-circuits-clean` worktree (Circuits with vscode
  reverts).
- `/tmp/circuits-clean.patch` (the canonical patch).
