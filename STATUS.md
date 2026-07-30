# STATUS — tooling worktree

> **2026-07-26 — this branch is `llm-interactive-next`**: Pierre-Yves' EcLlm
> base rebased onto current `main`, plus the transplanted daemon /
> vscode stack, the machine-profile port (`src/ecLlmJson.ml` +
> additive `ecLlm.ml` wiring, proto 3), and **MCP v1.5** (`ecd mcp`,
> 24 tools over named parallel sessions with edit-mode locks, the
> refactoring loop (check_script / resync_file / replace_proof +
> stale + timings), the strategy layer (proof_outline /
> proof_profile / check_skeleton / extract_lemma), semantic
> per-subgoal claims (claim_subgoal / exec_in), admit visibility
> (admitted arrays + admitted_goals), and — round 4, 2026-07-27 —
> comment-blind diff identity, the proof-body-only
> environment-equivalence certificate with tail skip,
> position-preserving formatting-only resyncs, the widened
> fast-forward gate, src previews, auto-tree on goal growth,
> `smt_timeout`, and session-lexical `define` bindings; round 5
> (B6): the single `exec_keyword` tokenizer — bullet/comment-blind
> keyword matching everywhere (bulleted admits are debt; smt(args)
> flagged; first_token deleted); round 6 (B7/B8/B9): authored vs
> DOCUMENT text — `<DOC-BEGIN>` wire blocks check file text under
> the file's own rules (strict_bullets enforced on resync tails,
> verification, and check_script/check_skeleton candidates; the
> REPL bullet exemption is per-phrase-scoped, the global pragma is
> document truth), per-proof authoring transcript (typed bullets
> stripped — COMMIT owns presentation; empty transcript explains
> itself and refuses to land), define expansion is code-only;
> round 7 (B10): COMMIT emits bullets only at REAL branch points
> (linear have-chains commit flat, nested splits unchanged);
> round 8 (B11): the COMMIT emitter is a snapshot-driven FRAME
> simulation (ecBullets' own model — the proof-DAG walk is gone):
> sibling frames from >=2-new-goal phrases, continuations never
> shift level, verified on the real 57-sentence bw3_real_eager
> (emitted body passes check_script under strict_bullets);
> round 9 (F6/F7): `goal_scope: focused` on the six goal-bearing
> tools (one goal instead of 80 kB on call-dispatch states,
> subgoal_count stays truthful), claim-conflict errors carry the
> close_session remedy, list_sessions rows carry `alive` and an
> empty listing explains per-process lock scope;
> `run_mcp_smoke` 159/159).
> `searchall` (#22) and EXEC-JSON v0 (#13) re-landed 2026-07-26;
> still deferred: EcCancel, bullets scoping — see
> [doc/ecllm-compat.md](doc/ecllm-compat.md), which is
> the governing plan. The sections BELOW are the imported daemon-v1
> snapshot (2026-04-29) and are stale wherever they touch `src/`
> facts; a full refresh is pending.

Volatile snapshot of where the project is right now. Onboarding
procedure lives in [ONBOARDING.md](ONBOARDING.md).

**Last updated:** 2026-04-29 (beta-prep nearly complete — 13
commits in this session closed beta-1 gates 1, 3, 4, 7-partial,
10-slim, 14 + a proc-rewrite emission bug fix + two doc pins.
Branch `llm-interactive` now 211 commits ahead of
`origin/llm-interactive` and is 100% on top of current `main`
(no rebase needed). **Open**: gate 12 (BETA.md) + the
release-bundle pipeline (`release/beta-1-circuits` worktree at
`~/Repos/ec-tooling-release`, mid-build-iteration). Earlier this
session: 14-point design pinning + mouse line selection for
proc rewrite/change + 5-slot rewrite builder + MatchByPos walker
[`dfded581e` / `a1b8b580f`]. Roll-up of pre-snapshot work in
[HANDOFF-VSCODE-FIRST.md](HANDOFF-VSCODE-FIRST.md).

## Branch state

- **Worktree:** `/Users/gdel/Repos/easycrypt-tooling`.
- **Branch:** `llm-interactive`, **211 commits** ahead of
  `origin/llm-interactive`. Clean tree (modulo user's in-flight
  `theories/distributions/SDist.ec` + `theories/crypto/TweakableHashFunctions.eca`
  edits — left untouched). Untracked `SDist_repro.ec` at repo
  root (16-line minimal § 20 repro file, kept as reference;
  gitignored).
- **`main` is fully merged** (via `b4d908bef`); rebase = no-op.
- **Release-bundle worktree**: `~/Repos/ec-tooling-release` on
  branch `release/beta-1-circuits`. Carries
  `llm-interactive` + a transplant of Circuits' EC-core changes
  (vscode/ stripped). Mid-build-iteration; see "Release-bundle
  status" section below.
- **`git rerere` enabled globally** this session (autoupdate too) —
  per-cycle release-merges replay prior conflict resolutions.
- **Smokes (llm-interactive)**: full suite green under
  `dune build @runtest`. 21 `(test)` stanzas + 1 diagnostic
  `(executable)`. proof-flow smoke now 36 checks (was 30; +3
  execAll, +3 cross-project session_manager).
- **Smokes (older counts kept for reference)**: speculation smoke
  is 48 cases (proc-rewrite/change tactic-string
  round-trip via tryTactic). VSCode-side: 71 unit-test cases on the
  pure helpers in `vscode/src/codepos.ts` via
  `node out/codepos.test.js`.

## Release-bundle status (2026-04-29 — IN PROGRESS)

A **release-merge pipeline** that combines `llm-interactive` +
Circuits (`bdep_ecCircuitsRefactor` minus its inherited
`origin/vscode` content) into a buildable tree, for producing
the bundled `.vsix` users have asked for.

**Worktree**: `~/Repos/ec-tooling-release` on
`release/beta-1-circuits`. Worktree-only branch; never pushed
(the user keeps a local copy of `bdep_ecCircuitsRefactor` and
edits it freely; per-release-merge it's re-merged via this
pipeline).

**What's in place:**

- **Setup** (one-time): `git config --global rerere.enabled true`
  + `rerere.autoUpdate true`. Subsequent release-merges replay
  recorded resolutions.
- **Local copy of Circuits**: `/tmp/ec-circuits-clean` worktree.
  Three vscode-merge commits reverted (`19c88a048`, `aad4d5006`)
  to strip the inherited `origin/vscode` content + the `lwt`
  opam dep. Pure-EC-core delta only.
- **Patch**: `/tmp/circuits-clean.patch` — 17,656 lines, the
  Circuits delta from merge-base to (Circuits-cleaned) tip. No
  vscode/, no lwt.
- **Apply state**: 26 rejects originally; resolved as follows
  (see `~/Repos/ec-tooling-release/`):
  - **15 spurious afbb8b766-derived rejects** dropped — the
    "forward-ecall" PR (Circuits' `b6c6e268a` ≡ main's
    `afbb8b766`) is already in main, so Circuits' delta on those
    files re-applies a refactor llm-interactive already has.
    Files: `src/ecAst.mli`, `src/ecEnv.mli`, `src/ecHiTacticals.ml`,
    `src/ecMatching.{ml,mli}`, `src/ecPV.{ml,mli}`,
    `src/ecParsetree.ml`, `src/ecProofTerm.{ml,mli}`,
    `src/phl/ecPhlCall.{ml,mli}`, `src/phl/ecPhlEager.ml`,
    `src/phl/ecPhlExists.{ml,mli}`.
  - **`src/ecEnv.ml`**: took Circuits' wholesale (carries
    crbindings + the `module Theory` relocation + the
    afbb8b766 LDecl `push_active_all` change; llm-interactive
    doesn't touch ecEnv.ml so no loss).
  - **Wholesale-take-Circuits**: `src/phl/ecPhlCodeTx.ml`,
    `ecPhlRewrite.{ml,mli}`, `tests/procchange.ec` (llm-interactive
    doesn't touch them).
  - **Surgical**: `src/ecCommands.ml` (one-line `Gcrbinding`
    dispatch entry), `dune` (added `libs` to dirs + `(env ...)`
    block to relax warnings 9/23/27/32/58/67/69 for
    libs/lospecs).
  - **Duplicate-symbol cleanup** during build:
    - `src/ecParser.mly` — duplicate `direction:` rule (one
      copy deleted).
    - `src/ecParsetree.ml` — duplicate `pecall` + `pdirection`
      types + duplicate `Prwprgm` constructor (deletions).
    - `src/ecParsetree.ml` — `sim_info` → `psim_info`
      rename to match main.
  - **Adapted-to-current-shape**: `src/ecParser.mly`'s
    `RWDelta` production now emits `(false, rwopt, fp)` to
    match the new parsetree shape (rigid flag in main but
    Circuits' parser side wasn't ported); `src/ecHiGoal.ml`'s
    `RWDelta (rwopt, p)` pattern now `RWDelta (_rigid, rwopt, p)`.
  - **`src/phl/ecPhlCodeTx.ml`** — Circuits' wholesale used
    `~bdhoare:true` arg that main's `t_code_transform` doesn't
    accept; stripped at all 5 call sites.
  - **`src/ecHiTacticals.ml`** — added the missing `Pcircuit`
    case (`Solve`/`Simplify` → `EcPhlBDep.t_bdep_solve`/
    `t_bdep_simplify`) ported from Circuits' dispatch.
  - **flake.nix / flake.lock**: kept llm-interactive's flake
    wholesale (has nodejs + tooling deps). User reconciled
    Circuits' flake-nix delta manually after I produced a
    zdiff3 marker file at `flake.nix.merge`. flake currently
    builds; opam scope resolves bitwuzla-cxx +
    ppx_deriving_yojson.
  - **Skipped Circuits-only feature**: rewrite-rule `rigid`
    flag (`/~`). Circuits-only addition; required record-shape
    update in `prrewrite_arg` we declined to apply for v1.
    Documented as a follow-up.
- **Build status**: ITERATING. After fixing
  parser+ecHiGoal+ecPhlCodeTx+ecHiTacticals, expecting more
  errors. Each iteration the user runs `make`, pastes errors;
  I patch.
- **Once green**: produce the bundled `.vsix` (`vsce package
  --target darwin-arm64`).

**Release flow as a script** (for next cycle): see
[doc/release-flow.md](doc/release-flow.md) (TBD; pin in this
session if time permits).

**`bdep_ecCircuitsRefactor` itself stays untouched** at the
upstream tip; the local `/tmp/ec-circuits-clean` worktree carries
the reverts. Per-cycle re-create or push-forward.

## Known bugs / deferred investigations

- **`(*&` and `(*^` lexer behavior reported as confusing.** EC's
  lexer ([src/ecLexer.mll:389-393](src/ecLexer.mll#L389-L393)) reserves
  `(*&` and `(*^` for **doc comments** (item-level / global-level
  respectively). Inside doc-comment mode, EC expects a structured
  closing form `&*)` / `^*)` and structured content. Users writing
  `(*&` thinking it's a generic comment hit parse errors. Not a bug
  per se, but the UX is non-obvious — the lexer eats `(*&` silently,
  parsing diverges, error message doesn't tell user "you opened a doc
  comment". Pinned for repro + better diagnostic (or doc-comment
  syntax change). Workaround: insert space (`(* &`) for plain comments.
- **STMT-JSON known coverage gaps** (UPSTREAM #24 follow-up
  amendments, schema-stable):
  - `loc` field always null until EC IR carries parsetree positions
    through typecheck. Click-to-jump per instruction blocked on this.
  - F-variant judgments (HoareF / equivF / eagerF) keep xpath
    references as Cn_pp leaves — needs env lookup to expand the
    referenced procedure body. Deferred as a separate amendment.
  - Smatch pattern_pp shows just bound var names, no constructor name
    (PPEnv internals not exposed for the lookup).
  - Print panel response shape doesn't yet carry stmt_node — print
    keeps text-only TM-tokenizer rendering. Display logic at the
    renderer level is unified (programWithLeftNumbers /
    programsWithMiddleNumbers handle both Cn_stmt and Cn_pp inputs)
    so once print response carries StmtNode[], it routes through the
    same renderer with no additional render code.

## Known UX bugs (reported, not yet investigated)

**Tactic-preview log + (detail) button — partial regression on the
beta-1 point-3 ship** (commit `8ee4bd0ba`). Manual testing surfaced
three issues to revisit alongside the broader UX-flow state-machine
refactor (open arch point #8). Functional path (cancel + closer-
sweep channel + severity colors) confirmed working; the UX
affordances below are deferred:

1. **(detail) button not appearing on the InputBox when an error is
   in flight.** Click target was supposed to open the per-builder
   Output channel; user reports the button does not surface.
   Likely culprits: button-array rebuild on validationMessage
   transitions; ThemeIcon(`output`) icon name might be wrong; or
   `input.buttons = [...]` reassignment timing vs. the
   debounce-driven `setShortValidation` callback. Workaround: the
   `easycrypt.proof.previewLog.show` command (Cmd-Shift-P) lets the
   user open any channel directly.
2. **`easycrypt.proof.previewLog.show` QuickPick — incomplete UX.**
   Lists open channels + `(all)`, but reportedly not all expected
   entries surface. Investigate alongside (1).
3. **Esc on the apply-phase-3 args refine flow closes the parent
   picker rather than rolling back to it.** Symptom of the closure
   + boolean-flag glue called out in open arch point #8 (sub-task
   "UX flow state-machine architecture"). Need explicit transition
   table per state: `commit | rollback | escape | sub-invoke | sub-
   return`. Pinned for the post-beta consolidation pass.

The broader push: build the **UX benchmark suite** (point 11 of the
beta-prep list / open arch point #7) so flows like the above get
explicit checklists and don't regress silently between iterations.

Historical / superseded section — Phase 4 UX bugs from earlier in
the session ALL resolved (see HANDOFF-VSCODE-FIRST.md "Closed since
this doc was last refreshed" for the rollup):

1. **Goal-pane preview override not visible during builders / lemma
   picker.** `setGoalsPreview(uri, goalsAfter, '🔍 builder preview')`
   is wired to push speculative post-tactic state into the goal pane,
   but the user reports nothing appears. Likely cause:
   `setGoalsPreview` only re-renders if `goalsPanel` is currently
   open; if the user invokes the builder without having opened the
   goal pane (Cmd/Ctrl+Alt+G), there's no panel to push to.
   Hypothesis: builders/picker should `ensureGoalsPanel()` at start
   so the preview always has somewhere to render. Worth verifying
   the badge actually appears when the panel IS open before assuming
   that's the only fix.

2. **"Pick lemma (with direction)" button not visible on Rewrite
   builder.** Code attaches the button via `input.buttons = [...]`
   in `refreshUI()` for `kind === 'rewrite'`. Possible causes:
   button rendering quirk in VSCodium, button order issue,
   `vscode.ThemeIcon('search')` not resolving, or `refreshUI()`
   timing before/after `input.show()` matters in some VSCode
   versions. Worth opening the Extension Host's Developer Tools
   console to check for any errors when the rewrite builder
   opens.

## Phase status

Plan reference: `doc/tooling-poc-plan.md`.

| Phase | State | Notes |
|---|---|---|
| 0a — scaffolding, boundary lint | landed | folded into Phase 1 acceptance |
| 0b — protocol design, EC additions 1/3/4/5/6/7/8/12 | landed | composition smoke green; protocol doc still has open `TODO:`s in §§ 7, 8, 13 |
| 1 — session core, registries, demo CLI, replay | landed | three SMT scenarios green; pool defaults provisional |
| 2 — document + sentence model + workspace | core landed; supervisor + discovery library landed; `ecd daemon` subcommand pulled forward as Phase 2.5 | supervisor fiber + `Daemon_discovery` library shipped 2026-04-25 with smokes (5/5 + 13/13). Remaining: grammar corpus, LCS suffix-salvage |
| 2.5 — `ecd daemon` long-running subcommand | landed | socket-mode + stdio-mode (Stage 4 add) both shipped; smokes 10/10 + 10/10 |
| 3 — structured execution + overlay primitive | substrate landed; **overlay primitive deferred to v1+** | additions 13 v0 + 16 + Edit_ops + EXEC-JSON round-trip. Lax-as-overlay subsumed by cache-policy reframe; overlays not needed for PoC |
| 4 — symbol sources + workspace index | not started | gates v1 features; declaration-dump wrapper is the highest-value single piece |
| 4.5 — cross-file invalidation | not started | gated on addition 2 |
| 5.0 — substrate (cache + replay-to-sid + Cas + debouncer) | not started; lands after Phase 5-core demo per VSCode-first plan | cache becomes PoC foundation, not v1 optimization |
| 5-core — LSP server impl + minimum methods | landed | conformance smoke 16/16 (socket); stdio smoke 10/10; proof-flow smoke 27/27 with PG-style step/back/restart/exec-to-cursor + auto-reconcile + locked-region tinting + goal-pane webview in VSCode |
| 5-parity Phase 0 — Proof_speculation lift | landed (1b350dbbc) | Cumulative-handle session API, `try_tactic` sugar, `query`, `preview_lemma`, `suggest_closers` with `before_candidate` + `on_progress` hooks. Closer-detection fixed for multi-subgoal goals (476c0b6a1). Smoke 45/45 |
| 5-parity Phase 1 — navigation completeness | partial | step/back `count` param landed; bidirectional execToCursor, queued amber tint, step/back coalescing, per-step stateChanged. **Beta gate**: `execAll` LSP method + "focus current goal" command (emits `cycle <delta>.`) — see beta-prep point 4 |
| 5-parity Phase 5 — proc rewrite / proc change mouse line selection | shipped (`a1b8b580f`) | Right-click on goal-pane program rows → context menu → Rewrite-at-line / Change-range. 5-slot rewrite builder (side / repeat / occurrence / match / lemma) with title-bar buttons + sentinels. MatchByPos walker closes UPSTREAM #24 match-arm gap. **Beta gate**: EC parity for proc rewrite (full applicable rwarg1) — see beta-prep point 2 |
| 5-parity Phase 2 — one-goal-at-a-time view | landed | Single-subgoal goal-pane render with cycle ± keybinds (e1aa83921). Default index follows EC's `current_index`; user pin via Cmd/Ctrl+Alt+]/[ wraps boundaries; `📌 pinned (EC focus: subgoal N)` badge shows divergence; pin clears on every stateChanged. Pure UI feature, no daemon work |
| 5-parity Phase 3 — tryTactic + suggestClosers LSP | landed | daemon (62341872f) + vscode (e864baaa0); goalsAfter via Goal_view.to_json (7f8539a30), formatTryTacticOk uses closedFocused (a67ffd4bd). Phase 3 smoke 20/20. Outstanding: per-candidate timeout gates on `proof/cancel` rework |
| 5-parity Phase 4 — lemma fuzzy search picker + token builders | shipped (with two known UX bugs) | searchLemmas LSP method (c181788dc) → Search_result.hit list. VSCode move/rewrite token builders + apply-lemma two-stage picker (53dd954c8). Three commands: Cmd/Ctrl+Alt+M (move), W (rewrite), L (apply lemma). Goal-pane preview override infrastructure for builder/picker visualization. **Known bugs**: see "Known UX bugs" section above. Daemon-side two-point chaser architecture pivot still pinned for the daemon-driven version of this; current implementation is client-side coalescing through tryTactic |
| 5.5 — speculative background compilation | not started | depends on cache substrate |
| 6 — MCP surface | not started | runs parallel to 5 once substrate exists |
| 7 — Neovim plugin + discovery wiring | not started | depends on 5-full + 6-full |
| 8 — TUI client | de-facto shipped | `ecd tui` over `Repl_core`; Semantic TUI extensions ongoing |
| 9 — polish, install docs, split-prep | not started | includes end-of-PoC code refactor pass (see Pinned open architectural points) |
| 10 — execute the split + capability negotiation | reframed under merged-binary architecture | capability negotiation deferred indefinitely (closed-loop); Phase 10 collapses |

## EC-core additions (verify against `UPSTREAM.md`)

- **Landed (18):** 0, 1, 3 (+ pp-failure hardening, addition 3 v1),
  4, 5, 6, 7, 8, 12, 13 (v0), 14 (v0 + scope-tagging + Tier-2
  synthetic-abort recovery; parse-recovery + cascade tagging still
  deferred to v1), 15, 16, 20 (forward-path: per-pregoal render env
  in `goals_to_json` — `e1b0e4fc9`; Tier-2 Fpr wrapper retired
  `89d95ead7`. Post-revert dangling-xpath case still deferred to
  redesign), 21 (directive replies omit goals body — fixes goal-
  text leak into `easycrypt/proof/print` body for in-proof print
  invocations), 22 (`searchall` directive — overload-tolerant
  search for ambiguous operator patterns), 23 (GOALS-JSON
  conclusion tree — structured PHL judgment rendering; program-
  printing v0 with TM-driven syntax highlighting + prettification
  toggle), 24 (STMT-JSON — per-instruction structured statement
  nodes for deep code positions; if/while/match block constructs
  render with hierarchical sub-numbering; equiv side-by-side with
  shared-row aligned numbering or per-side independent numbering
  via `easycrypt-tooling.display.equivAlignment`).
- **Planned (4):** 2 (decl dump — wrapper-first highest value), 9
  (struct print/locate/search), 10 (hover — Tier 3, post-EcEnv), 11
  (SMT counter-examples — Tier 4, post-ecSMT).
- **Schema-pinned, scheduled with EC co-development:**
  - **EXEC-JSON v0.1** — compound tactics (`have`, `cut`, `pose`, `wlog`, `gen`)
    with nested tactic args. Enables structural recovery catalog (folded
    into `proof/execToPoint`'s `RecoveryStrategy`).
  - **EXEC-JSON v1** — direct-AST dispatch + subgoal-addressing API.
    Enables sub-sentence Tier 3 chain decomposition.
  - **EC-core bullets-with-semantics** — make `-`/`+`/`*` proof bullets
    structural (define subgoal-focus scopes; bullet-close requires scoped
    subgoals discharged). Independent EC addition; benefits manual proof
    writers + simplifies tooling subtree-admission dramatically.

## Locked-in decisions (post-iteration)

### Architecture

- **LSP framing — Option 2.** Eio-native; daemon library uses
  `jsonrpc` for `Jsonrpc.Packet` / `Request` / `Notification` /
  `Response.Error.*` and hand-encodes LSP method payloads
  (Diagnostic, Position, Range) as Yojson. Module signatures pinned
  (`lsp_io.mli` / `lsp_server.mli` / `lsp_methods.mli`); impl landed
  Stage 3. The `lsp` opam package is **not** consumed by the daemon
  library (verified 2026-04-26); it is reserved for conformance
  smokes that want typed `Lsp.Types.*` constructors. Decision:
  hand-encoding stays for now — refactor to typed `Lsp.Types.*` is
  optional polish, deferred until a forcing function (e.g., a wire
  shape we get wrong by hand).
- **Daemon merging into EC** confirmed direction. Phase 10 (split)
  reframed. UPSTREAM.md becomes "EC kernel additions tracked under
  TCB-discipline review" rather than "PR set destined for upstream EC."
- **TCB discipline (overapproximation)**: walk dep graph from kernel
  modules outward; tag any module within N hops as TCB. False positives
  acceptable; false negatives not. `ec-core:` prefix gates TCB-strict
  commits (differential oracle + replay corpus + grammar corpus required);
  non-TCB `src/` changes ride daemon-class testing. See
  `doc/tcb-discipline.md`.
- **Capability negotiation**: between daemon ↔ LSP/MCP client, **not**
  daemon ↔ EC (irrelevant under merged-binary). Schema pinned; impl
  ships when needed.

### Cache + invalidation (NEW: elevated to foundation)

- **Goals_cache becomes PoC foundation** (was v1 optimization).
  Two-tier: in-memory LRU + replay-to-sid fallback on miss. Disk
  overflow via artifact cache (post-PoC).
- **Cache key splits `(statement_hash, proof_hash)`.** Downstream
  entries depend only on `statement_hash`; lax/strict policy controls
  whether `proof_hash` mismatch (currently-failing proof) cascades to
  invalidate downstream.
- **`proof.cachePolicy: "lax" | "strict"`** workspace setting:
  - `strict` — failing proof invalidates downstream; honest about
    current incompleteness.
  - `lax` — failing proof invalidates only itself; downstream stays
    valid (treats prior verification as sufficient). **Default for
    interactive sessions.** Replaces lax-as-overlay entirely.

### Overlay system (NEW: deferred from PoC)

- **OVERLAY_KIND substrate (registry, composition algebra, drift-awareness)
  deferred to v1+.** No overlay needed for PoC; cache + ANALYZE-JSON +
  cache-policy lax cover the use cases.
- **Lax overlay, Admit_subtree, Disable_smt, Time_budget overlays — all
  dropped from PoC.** Time_budget becomes a daemon-level setting
  (`proof.maxExecMsPerSentence`) rather than a range-scoped overlay.
- **Failure-recovery during proof execution** becomes a daemon-internal
  `RecoveryStrategy` parameter on `proof/execToPoint` (`halt | best_effort_admit`).
  The structural-recovery catalog (inline-atomic patterns like
  `have h : Foo by tac` → `... by admit`) is implementation detail behind
  this parameter, not an overlay primitive.

### Wire / methods

- **LSP method namespace: `easycrypt/proof/*`** — matches upstream's
  `vscode` branch so their extension can drop in. Implemented via single
  `proof_ns` constant in `lsp_methods.ml` for cheap future flipping.
- **MCP tool naming: noun-phrase** — matches protocol § 8 (`exec_region`
  not `exec`). Documented in `doc/mcp-schema.md`.
- **File modes**: real-time (default) + preservation. Preservation merge
  UX deferred to v1+.
- **Multi-instance per surface**: each connection spawns a per-connection
  instance. Unified-session axis (LSP+MCP attached to same session) and
  parallel-sessions axis both supported. Session linkage via
  `attachTo: <session_label>` parameter.
- **`proof/execToPoint` carries `RecoveryStrategy`** — `halt` (default,
  CI/strict) or `best_effort_admit` (interactive, focused-admit fallback +
  inline-atomic catalog when EXEC-JSON v0.1 lands).
- **Sentence-id + line:col both accepted** for range/position parameters
  in proof methods; daemon resolves position to nearest enclosing sentence.

### Other policy

- **Sentence IDs are the wire vocabulary** for all edit ops, goals,
  transcripts, checkpoints. Line/col only at LSP / REPL transport edges.
- **EXEC-JSON is execution only**, never document editing.
- **Atomic release flips** (server + client): we control both sides; can
  flip method names / wire shapes without external coordination cost.

## Pinned open architectural points (user re-raises)

1. **EC-merge — codebase separation inside a merged `ec` binary.**
   Boundary-lint extension to forbid direct EC-internal imports from
   `tooling/**`. Map onto `include_subdirs unqualified` layout.
2. **EC-merge — refactor scope for fork-safe workers.** EC's
   initialization isn't fork-safe (prover subprocesses, Random state,
   buffered I/O, Why3 session). Open: actual scope.
3. **Non-blocking / cancellable TUI picker operations.** Cancellable-fiber
   rework. Same plumbing serves Phase 6 MCP `try_tactic` cancellation
   AND parity Phase 3's `suggestClosers` per-candidate timeout.
4. **Two-point chaser for navigation (parity Phase 4 architecture
   pivot).** Daemon owns BOTH the user-target point and the EC
   actual-state point; chaser fiber executes/reverts to close the
   gap; client subscribes to `targetChanged` + `stateChanged`
   notifications and renders amber from notifications. Replaces
   today's client-side `pendingGoto + pendingStepDelta` driver
   (commits 6b95f2f03, d58156f12). Trade: ~150 LoC daemon refactor;
   wins multi-client consistency, cleaner cancellation when
   `proof/cancel` lands. Lands with Phase 4 lemma fuzzy picker.
5. **Modal proof-tree mode + refactoring transforms (post-Phase-4 arc).**
   Builds on subgoal-id + diff envelope (UPSTREAM § "Schema-pin
   candidates discussed but not yet on UPSTREAM.md" — to be added).
   Daemon owns proof_tree.t; surfaces (mouse/menu + keyboard modal)
   render the same primitive operations. Refactoring transforms
   (factor-merge equal subproofs, hoist common prefix, eliminate
   dead admit, normalize tactic style, auto-bullet-insert) ride
   the tree representation. Captured in conversation; not yet
   pinned in roadmap doc.
6. **`ec-core-critical:` workflow established.** Soundness-touching
   root-cause fixes to EC kernel surface (EcEnv, EcTyping,
   EcCoreGoal, EcLowGoal, prover bridge, kernel tactics) require
   explicit pre+post approval, root-cause focus, detailed inline
   docs, TCB-strict tests (diff oracle + replay + grammar), and
   no autonomous execution even in auto mode. See
   `doc/commit-conventions.md` § rule 7 + `doc/tcb-discipline.md`.
   No instance landed yet under this workflow. The first candidate
   (UPSTREAM § 20 root cause) turned out NOT to need it: tracing
   showed `prF_memenv` succeeds for abstract-bound xpaths against
   the correct env; the bug was the daemon-side `goals_to_json`
   building the render env from `EcScope.env scope` rather than
   `LDecl.toenv pregoal.g_hyps`. Proper fix landed as a display-
   only `ec-core:` change (`e1b0e4fc9`) — see project memory
   `project_ec_hyps_vs_scope_env.md`. Workflow remains established
   for genuine kernel-soundness root causes when they arrive.
7. **Tactic builder UX next pass** (designed in detail, partial impl
   landed). Recursive sub-arg builder with sentinel grammar (`(`, `)`,
   `<<`, `>>`) for nested applications; folded strip rendering with
   ~40-char threshold; full TacticSchema → shapes/slots refactor
   (each tactic = list of shapes with typed slots: text/qname/term/
   formula/tactic/hyp/intro_pat/rewrite_arg); schema enrichment
   (have shapes, rewrite directional sentinels, case/elim hyp pickers);
   whitespace-in-token sniffer (info hint). The ephemeral term editor
   popup primitive (`editTermInPopup`) and apply phase-3 single-level
   builder shipped in the prior pass; this work extends them. Pinned
   for next iteration.
8. **End-of-PoC code consolidation pass.** Iterative building over
   many sessions has accumulated waste: duplicated patterns (each
   builder reimplemented preview / validate / sentinel handling
   before the schema refactor extracted them; some still duplicate
   debounce / probe / commit logic), now-unused branches kept for
   defensive reasons that are no longer relevant, comment-rot
   (post-refactor comments referencing old shapes), inconsistent
   naming (`compareCycle*` vs `cycleSubgoal*`, `setGoalsPreview`
   vs `setGoalsComparisonPreview`), and split files that should
   probably consolidate (`vscode/src/extension.ts` is ~3000 LoC and
   should split into `goals/` `print/` `picker/` `builder/` modules
   before going to v1). Pre-Phase-9 sweep: walk the diff since the
   last clean refactor (~50 commits worth), look for: dead code,
   over-defensive branches, premature abstractions that didn't pay
   off, primitives that should be merged, duplicate string-templates
   in the JSON wire that could be schema'd, etc. Goal: ship the v0
   cut with a code base smaller than what we have now, before
   committing to v1 architecture decisions on top of it. Estimated
   ~1-2 days of focused refactoring with no behavior change.

   **Sub-task: UX flow state-machine architecture.** Picker / builder
   /  phase-3 / sub-flows (lemma picker `?` subcommand, popup `??`
   subcommand, Esc rollback to specific previous stage) are glued
   together with closures, boolean flags (`skipToStage2`,
   `intentionallyHiding`, `refineArgsRequested`), and per-flow
   callback chains. Adding a new flow requires plumbing yet another
   flag through several layers. Smell signs already visible:
   `runLemmaPicker` carries 5+ pieces of state across a `while
   (true)` loop; `runApplyPhase3` carries another 5; sub-flows
   manipulate parent state via captured closure variables. Replace
   with an explicit state machine: enumerate states (e.g.,
   `SEARCH_PATTERN`, `BROWSE_HITS`, `REFINE_ARGS`,
   `EDIT_TERM_POPUP`, `LEMMA_PICKER_SUB`), transitions
   (`commit | rollback | escape | sub-invoke | sub-return`), and
   handlers per state. Benefits: Esc semantics become a single
   transition table per state (no per-callsite ad-hoc code); new
   flows declare states + edges; modal mode rides on top naturally;
   testing is easier (drive the machine with sequences of
   transitions). Pin alongside the broader consolidation — likely
   the most architecturally-impactful piece of the cleanup.
8. **UX benchmark suite** (TODO, not started). Build a curated set
   of `.ec` files + a written test plan that exercises every UX
   flow end-to-end: step / back / exec-to-cursor (incl. inter-
   sentence whitespace), goal pane (single + comparison view + cycle
   controls), apply-lemma picker (success / err / closes / multi-
   subgoal), search-symbols, print + print-under-cursor, move /
   rewrite builders, locked-region tinting, file switching, restart,
   PHL-goal program rendering (once shipped). Each flow has an
   expected outcome and a screenshot/recording reference. Lets us
   regression-test UX changes manually in 10-15 minutes instead of
   discovering bugs ad-hoc, and gives the program-printing work a
   measurable wire-size + render-cost benchmark. Should also be
   the basis for any future automated VSCode-extension tests.

## Known hang triggers (Deferrals)

- Closer-sweep `smt()` candidate at sweep tail.
- Rewrite-builder `/#` SMT expansion.

Both blocked-event-loop symptoms; cancellable-fiber rework cleans them up.

## Implementation plan — VSCode-first ordering

User-visible milestones:

- **Milestone 1** (deferred from original ordering): cache-driven
  REPL/TUI speedup — folded into Stage 5 below; arrives with VSCode
  speedup.
- **Milestone 2** (~18-27 commits): **VSCode demo** — open EC file,
  real-time diagnostics, step through proofs with keybinds, side panel
  shows goals. First time daemon's value is concrete to non-developer.
- **Milestone 3**: Phase 5-full + Phase 6 MCP + cross-file invalidation +
  Claude Code integration.

### Stage 1 — Documentation (this stage in progress)

Pin schemas before implementation so wire stays stable across cache
addition later. Components:

1. `STATUS.md` — this file (in progress).
2. `doc/lsp-schema.md` — MVP version with cache-aware fields pinned upfront.
3. `doc/tooling-poc-plan.md` — drop overlay substrate; add Phase 2.5/5.0/5.5;
   performance budgets section; post-PoC anchors (REPL/TUI eventual LSP,
   external file watcher, sub-sentence Tier 3, EC-core bullets,
   cache-policy lax); merged-binary architecture working notes;
   capability-negotiation reframe.
4. `doc/tcb-discipline.md` — TCB overapproximation, file-map, test gates.
5. `doc/golden-policy.md` — structural goldens default + verbatim
   wire-shape rules + regenerate-on-mismatch dev flow.
6. `commit-conventions.md` — doc-discipline line.
7. `UPSTREAM.md` — addition 14 v1 deferrals, EXEC-JSON v0.1/v1 schema
   pins, EC-core bullets-with-semantics slot.

### Stage 2 — Minimum substrate for LSP

1. `Log` module (~50 LoC) — wraps `Logs` opam, structured JSONL output,
   configurable destination.
2. Signal-handler crash log (~50 LoC) — SIGSEGV/SIGABRT/SIGFPE/SIGBUS
   handlers writing crash log.
3. `Request_registry` (~50 LoC) — generic correlation_id → switch
   tracking, surface-agnostic, reused for LSP and MCP.
4. `Debouncer` (~40 LoC) — per-document debouncing for didChange-driven
   work.
5. `Configuration` skeleton (~50 LoC) — typed accessors over LSP
   `workspace/configuration` + local config.
6. `ecd daemon` long-running subcommand (~200 LoC) — takes
   `Daemon_discovery` lock, listens on Unix socket, signal-handler
   graceful shutdown.

### Stage 3 — LSP framing + minimum methods

1. Fill `lsp_io.ml` — `Jsonrpc.Packet` codec on Eio flows with LSP
   `Content-Length:` framing.
2. Fill `lsp_server.ml` — inbound loop, dispatch via Request_registry,
   per-request fibers under switch.
3. Fill `lsp_methods.ml`:
   - lifecycle: initialize / initialized / shutdown / exit (~50 LoC).
   - text document: didOpen / didChange / didClose (~80 LoC).
   - publishDiagnostics: hook didChange → ANALYZE-JSON → diagnostics
     (~60 LoC).
   - proof methods: `easycrypt/proof/{execToPoint,revertToPoint,goals}`
     (~120 LoC).
4. Conformance smoke (scripted LSP client) (~150 LoC).

### Stage 4 — VSCode extension

1. Port from `origin/vscode`, retarget to our daemon's method names.
2. TextMate grammar from upstream (~100 lines).
3. Minimum keybinds: step forward / step back / goto cursor / show goals.
4. Connect to `ecd daemon` via stdio or Unix socket.

**→ Milestone 2 lands here.**

### Stage 5 — Cache substrate

1. `Cas` module with `(statement_hash, proof_hash)` split + `digestif`
   dep (~110 LoC).
2. `Goals_cache` — LRU + provenance + lax/strict policy (~280 LoC).
3. Replay-to-sid primitive (~150 LoC).
4. Wire cache into `proof/goals`, `proof/execToPoint`,
   `publishDiagnostics` paths.
5. Wire cache into `Repl_core` for REPL/TUI speedup (~50 LoC).

**→ Milestone 1 (speedup visible) folds in here.**

### Stage 6+ — Continue substrate + Phase 5-full + Phase 6

- Workspace pure-value + side-table separation (~60 LoC restructure).
- Workspace `Hashtbl folder_uri → Workspace.t` indirection (~30 LoC).
- Hover / definition / documentSymbol (Phase 4-dependent).
- MCP server + tools.
- Speculation (Phase 5.5).
- `Telemetry` seam (~30 LoC).
- Per-feature benchmark suite scaffold (~400 LoC).
- Diff oracle expansion to ANALYZE-JSON (~40 LoC).
- Boundary-lint enhancement: ec-core ↔ UPSTREAM.md verification (~30 LoC).

## Test coverage (current)

Run via `dune test`. 19 `(test)` stanzas + 1 diagnostic
`(executable)`. Two new since last STATUS update:
`run_proof_speculation_smoke` (Phase 0 lift smoke) and
`run_lsp_speculation_smoke` (Phase 3 LSP speculative methods +
abstract-theory pp regression).

| Test | Lines | What it covers |
|---|---|---|
| `run_smoke` | 80 | composition gate — echo MCP_TOOL + admit-first OVERLAY_KIND apply-shape on stub session + pool acquisition + publish emission |
| `run_ec_llm_smoke` | 213 | session: spawn / exec / parse-error / restart-via-pragma / restart-tag bubble-up / addition-16 first-token offset / transcript event kinds |
| `run_smt_scenarios` | ~220 | startup cost + lemma+smt+qed + cancel-mid-solve (20s hard deadline) + two-concurrent |
| `run_document_smoke` | 137 | Sentence_id + Document.diff common-prefix + Workspace open/update/close |
| `run_repl_core_tests` | 658 | 68 cases: insert/delete/edit/diff/save/jump/cycle/byte-integrity, truncation guard, blank-line preservation |
| `run_diff_oracle` | 201 | (sid, goals) parity: cold full-load vs revert-then-re-feed at every sentence |
| `run_replay_smoke` | 185 | record clean transcript → replay (assert no mismatches) → perturb session.reply uuid → assert mismatch detected |
| `run_exec_json_smoke` | 337 | EXEC-JSON v0 round-trip equivalence (text path vs structured) — 42 checks |
| `run_semantic_lib_smoke` | 213 | Goal_view + Fuzzy_filter + Search_result decoders; Speculation capture/rollback/commit |
| `run_supervisor_smoke` | ~95 | per-session supervisor fiber (5 checks) |
| `run_discovery_smoke` | ~115 | `Daemon_discovery` lock states (13 checks) |
| `run_analyze_smoke` | ~250 | ANALYZE-JSON v0 + scope-tagging + synthetic-abort recovery (15 checks) |
| `run_substrate_smoke` | ~250 | Log + Configuration + Request_registry + Debouncer (40 checks; +2 debouncer concurrency regression) |
| `run_daemon_subcommand_smoke` | ~200 | `ecd daemon` lifecycle, pid/socket files, stale recovery (10 checks) |
| `run_lsp_io_smoke` | ~230 | Content-Length framing roundtrip + concurrent-writer Eio.Mutex regression (17 checks) |
| `run_lsp_conformance_smoke` | ~290 | Stage 3 socket-mode end-to-end via Unix socket (16 checks; shutdown race fix landed) |
| `run_lsp_stdio_smoke` | ~230 | Stage 4 stdio-mode end-to-end via subprocess stdio (10 checks) |
| `run_lsp_proof_flow_smoke` | ~340 | Slice A-D PG-style flow: step / back / goals / restart / didChange-reconcile + pipelined-goals write_mutex regression (20 checks) |

Diagnostic only: `run_search_debug` — invoke via `dune exec`; not in
`dune test`.

### Known coverage gaps

1. **Pool fairness / starvation-freedom.** Plan Phase 2 acceptance names
   a measurement; not implemented.
2. **Publish-point bounded queue + overflow + snapshot.** Smoke asserts
   emit count only.
3. **uuid-invariant mismatch path.** Transcript schema admits the kind;
   no test triggers it.
4. **Correlation-ID echo.** IDs threaded; no assertion that a given
   correlation surfaces on the matching reply.
5. **Daemon-side typed errors.** No construction or round-trip tests.
6. **ANALYZE-JSON v1 follow-ups.** Parse-recovery, cascade tagging,
   pragma isolation, notifier capture. See UPSTREAM.md § 14.
7. **proof/cancel.** Pinned in `doc/lsp-schema.md` for the
   cancellable-fiber rework (open architectural point #3); not
   wired. Slice 4 of the parity plan (lemma picker preview) waits
   on this.

## Schema-pin candidates discussed but not yet on UPSTREAM.md

- **STMT-JSON** — structured `EcModules.stmt` / `instr` serialization.
  Tier 1, AST-stable. Forcing function: program-edit arc, two-sided
  rendering of equiv goals.
- **GOALS-JSON program-state extension** (UPSTREAM #22, planned) —
  populate `goal_kind` + structured `program` block for PHL judgments.
  - **v0 (this is the next slice)**: outer-judgment-only. When the
    conclusion's outermost connective IS a PHL judgment (hoare /
    phoare / ehoare / equiv / eager), emit a structured `program`
    field; else `program = null` and clients render `conclusion_pp`
    as today. No byte-span anchors, no embedded judgments — chain
    goals like `prop => equiv => phoare` fall back to plain pp text
    (manual escape: `intros` to peel the prop layers).
  - **v1 (post-PoC, replaces v0 schema-wise)**: skip byte-span
    stopgap — go directly to full hash-consed structured-tree JSON
    for the entire goal (`EcFol.form` serialization, hash-consed
    + lazy-expanded sub-terms). EC's internal representation already
    hash-conses, so wiring is mostly serialization plumbing rather
    than a new data model. Benchmark wire-size + render cost at that
    point and optimize as needed (CBOR/MessagePack, lazy fetch,
    etc.). Reference UX-benchmark suite drives the perf budget.
  - **Extensibility**: `judgment.kind` open-ended; new program logics
    (probabilistic relational, cost logic, future) add their own
    kind + `extras` map. Clients pattern-match; unknown kinds
    fallback to a generic structured render.
- **Holey-stmt typecheck** — `proc change` term builder enabler.
- **MODULE-JSON** — module structure. Tier 3 (post-EcEnv).
- **SMT unsat-core schema** — schema design Tier 1; emission Tier 4.
  Daemon analysis layer (core minimization, shrink-hints, aggregation,
  what-if probes) Tier 1 once data lands.

## Live gaps in the protocol doc

Phase 0b deliverables that still carry `TODO:`:

- § 7 — per-method JSON-RPC examples (folded into `doc/lsp-schema.md`
  as part of Stage 1).
- § 8 — per-tool MCP schemas (folded into `doc/mcp-schema.md` later).
- § 13 — `statement_hash` canonicalization for the artifact-cache key
  tuple.
- § 11 — reconnect survival-list shape on `initialize` reply.

## Goal-state retention strategy (resolved this iteration)

**Decision: hybrid LRU cache + replay-to-sid fallback.**
- L1: in-memory LRU keyed by `(doc_uri, sid)`, default 64MB/workspace,
  configurable (`proof.goalsCacheBudgetMB`).
- L2: replay fallback on cache miss via scratch session (uses recovery
  scratch as warm prefix).
- L3 (post-PoC): disk overflow via artifact cache.

Eager population on every successful primary exec. Drops on Restart;
suffix-drop on revert-to-uuid. Provenance tagged
(`normal | lax_admitted | lax_clean`) so lax/strict policy can filter.

## Reframed: lax mode

Lax-as-overlay is dropped. Lax becomes a cache-invalidation policy
(`proof.cachePolicy`). One bit of policy; two consistent consequences:

1. *Cache view*: downstream lemmas display as fine via cache hits even
   if a midstream proof currently fails.
2. *Execution view*: if user advances primary past the broken proof,
   daemon treats it as admitted (cache says it WAS valid). Primary
   advances; downstream executes against admit-tainted state.

Mode-switch asymmetry: lax → strict revalidates everything (expensive);
strict → lax cheap. Default lax for interactive; strict for CI/release.

This entirely subsumes the prior lax-as-overlay design with simpler
semantics.

## Workflow status

Project is heading into **beta-prep mode**. Initial-beta cut targets a
self-contained `.vsix` distribution to non-developer EC users, with
rolling-iteration on direct OOB feedback. 14-point design-pinning
discussion concluded 2026-04-28; see HANDOFF-VSCODE-FIRST.md for the
full handoff doc.

### Beta-prep priority list (14 points) — STATUS 2026-04-29

| # | Gate | Status | Commit(s) |
|---|---|---|---|
| 1 | proof/cancel via SIGINT (C1+C2+C3+C4) | ✅ closed | `06f9f2268`, `9c6a8346e`, `546471a8f`, `aa7bc876f` |
| 2 | proc rewrite full applicable rwarg1 | ⏸ deferred post-beta | per discussion |
| 3 | Rewrite-builder UX (per-builder log channels) | ✅ closed | `8ee4bd0ba` (+ UX bugs pinned in `acc91b44a`) |
| 4 | Parity Phase 1 finish (`execAll` + cycle-subgoal) | ✅ closed | `4dd2dda51` |
| 5 | Daemon-side two-point chaser | ⏸ post-beta | (no work this cycle) |
| 6 | Code consolidation pass + state-machine refactor | ⏸ post-beta-1 | (no work this cycle) |
| 7 | Keybind metadata + PG preset (partial only) | ✅ closed | `009dbde76` |
| 8 | Phase 5.0 cache substrate | ⏸ post-beta | (no work this cycle) |
| 9 | LLM/MCP refactor | ⏸ post-beta-1 | (no work this cycle) |
| 10 | `.vsix` packaging — slim | ✅ closed | `32284cc84` |
| 10 | `.vsix` packaging — bundled (with Circuits) | 🛠 in progress | release/beta-1-circuits worktree |
| 11 | UX benchmark suite | ⏸ post-beta-1 | (no work this cycle) |
| 12 | `BETA.md` getting-started doc | ⏳ remaining | next session |
| 13 | WIP commit hygiene | ✅ closed | `dfded581e`, `a1b8b580f` |
| 14 | Per-project sessions + Session_manager + CWD | ✅ closed | `a7c566ce6`, `8268700ec` |

**Plus** (this session): `629f18607` — proc-rewrite emission bug fix; `414c75d65` — pinned post-beta investigations (incremental Why3, SMT memo cache).

Phasing (legacy):
- **Initial-beta scope**: 1, 2, 3, 4, 7-partial (keybind metadata
  + PG preset only), 10, 12, 13.
- **Immediately post beta-1 ship**: 6, 7-modal, 9 (LLM/MCP), 11
  (UX benchmark suite).
- **Post-beta later**: 5 (two-point chaser), 8 (cache substrate),
  + the (b)/(c) follow-ups under the session-model design doc.

#### Beta gates (must land before initial-beta)

1. **Hang recovery — `proof/cancel` via SIGINT**. New `EcCancel`
   module (~50 LoC ec-core) + `Cancel.check ()` instrumentation at
   ~5-10 strategic points in shared infrastructure (FApi
   combinators `t_seq`/`t_first`/`t_or`, `t_repeat`/`t_do`, prover
   bridge). Why3 subprocess kill on cancel + background re-spawn
   so the cancel-response returns immediately and the next SMT
   call awaits the spawn. Per-request `seq` ID; convenience wrappers
   for "cancel all" / "cancel current". Rollback by reverting the
   four staged commits (no runtime feature flag). Future: full
   cancellable-fiber rework — pinned post-beta as a re-architecture
   that supersedes this v1 (see [doc/cancellation.md](doc/cancellation.md)).
2. **EC parity for proc rewrite — full applicable rwarg1**. Parser
   shape: `PROC REWRITE side? pos r=rwarg1` (full rwarg1, runtime
   reject for inapplicable variants with friendly error message).
   Applicable: rwside, rwrepeat, rwocc, rwmatch (incl. `[x in p]`),
   rwpterms (single + multi), RWDelta. Dropped (no residual to
   close): RWPr, RWSmt, RWDone*, RWTactic. ~80-120 LoC ec-core.
3. **Rewrite-builder UX fix**. Two-line `input.title` (`label /
   committed: ...` + `in-flight: <slots-summary>`) — always
   visible, doesn't get pushed by validationMessage. `(empty)`
   placeholder always for in-flight. Overflow truncates `…+M more`
   with click-to-expand reveal that wraps. Errors truncated to
   first line + ~120 chars in `validationMessage`; full error to
   Output channel via `(detail)` button. Severity Error for tactic
   failures, Info for sentinel hints.
4. **Parity Phase 1 — `execAll` + cycle-subgoal command**.
   `easycrypt/proof/execAll { uri }` advances until end-of-doc OR
   first non-Meta error; rollback to last-executed sentence on
   `proof/cancel`. UI-only `Cmd/Ctrl+Alt+]/[` cycle stays as today
   (display only). New "focus current goal" command computes
   `displayed - current_index` delta and emits `cycle <delta>.`
   into the document at the cursor — preserves stock-EC checkability
   of the resulting script. (No new EC tactic; absolute-index
   primitive deferred — `Pfocus` name is taken by an existing
   tactic-combinator with different semantics.) Future: semantically-
   named subgoals (provenance-based) so `focus <name>` becomes
   robust to subgoal-index churn.
7. **Configurable keybindings + PG preset (partial)**. Metadata
   audit on `package.json` so every command has clear `category` +
   `title` and is remappable via VSCode's `keybindings.json`.
   Add `easycrypt-tooling.keybindings.preset: 'default' | 'pg'`
   setting + parallel keybind entries gated on a `when` context.
   Modal mode deferred to immediately-post-beta-1.
10. **Packaging — `.vsix` slim + bundled**. Two distribution
    artifacts: slim (no EC binaries) and bundled (ec + ecd
    pre-built for macOS arm64/x64 + Linux x64). Binary discovery
    chain: `EC_BIN` / `ECD_BIN` env vars → workspace setting
    `easycrypt-tooling.ec.path` / `daemon.path` (absolute path or
    PATH-searched executable name) → `which ec`/`which ecd` →
    bundled fallback if shipped. Out-of-marketplace; manual `.vsix`
    distribution. Daemon-merge collapses ec/ecd distinction
    post-beta.
12. **`BETA.md`** — single getting-started doc at repo root
    covering install + first-proof + keybind cheat sheet +
    settings reference + known-limitations + report-a-bug. OOB
    issue tracking (direct message). "Report a bug" command +
    button bundles daemon log + extension state for triage. Manual
    update push.
13. **WIP commit hygiene** ✅ — staged WIP feature into checkpoint
    commits (`dfded581e` + `a1b8b580f`).

#### Immediately post beta-1 ship

6. **Code consolidation pass + UX flow state-machine refactor**
   (open arch point #8). Pre-PoC sweep: extract duplicated
   patterns, drop now-unused defensive branches, split
   `vscode/src/extension.ts` (~5000 LoC) into `goals/` `print/`
   `picker/` `builder/` modules. Sub-task: replace closure +
   boolean-flag glue (`skipToStage2`, `intentionallyHiding`,
   `refineArgsRequested`) with explicit state-machine transitions.
   Cleaner foundation for the rolling-iteration phase.
7. **Modal mode** (vim-style command groups). Half-day for design;
   ships behind a setting toggle.
9. **LLM-mode → MCP refactor**. Extract `ec llm` core logic into a
   shared layer; MCP server first-class consumer; REPL fallback
   retained as test aid. Sentinel `llmo_input = ""` collapse +
   `doc/llm/CLAUDE.md` rewrite happens here. Beta-2 with LLM
   integration starts after this lands.
11. **UX benchmark suite** (open arch point #7). Curated `.ec`
    files + written checklist. Anchors regression discipline for
    rolling-iteration; seeds future automated VSCode-extension
    tests via `@vscode/test-electron`.

#### Post-beta later

5. **Parity Phase 4 — daemon-side two-point chaser** (open arch
   point #4). Daemon owns BOTH user-target and EC-current points;
   chaser fiber executes/reverts to close the gap; client renders
   amber from `targetChanged` + `stateChanged` notifications.
   Replaces client-side `pendingGoto + pendingStepDelta` driver.
   Deferred unless a specific bug / feature / UX issue surfaces it
   earlier.
8. **Phase 5.0 cache substrate**. Goals_cache + replay-to-sid +
   Cas; lax/strict policy. Architecture needs more design before
   committing — full deferral.

#### New design points pinned during this discussion

14. **EC import-path management — per-project sessions**.
    Session-keying becomes a sub-axis under per-connection (LSP /
    MCP). Each connection owns a `(project_root → proof_session)`
    map; project_root discovered via EC's existing `easycrypt.project`
    walk + `Unix.realpath` canonicalization. Soft-cap of 4 active
    sessions per connection (LRU evict on overflow); 2-min idle
    eviction; configurable via `easycrypt-tooling.session.{maxActive,
    idleTimeoutMs}` + master toggle. Hot-reload on `easycrypt.project`
    change via file-watcher. Full design in
    [doc/session-model.md](doc/session-model.md). Reconnect-survival
    + cross-connection sharing pinned post-beta.

Plan + handoff details: see HANDOFF-VSCODE-FIRST.md.
