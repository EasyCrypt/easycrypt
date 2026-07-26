# TCB Discipline

**Trusted Computing Base** = the set of code whose correctness
implications are *soundness* (proofs being accepted that shouldn't
be) rather than *UX* (slow, crashed, wrong diagnostic, dropped
notification). TCB bugs corrupt the system's truth-telling; non-TCB
bugs degrade the system's helpfulness.

This document codifies how we distinguish the two and what
disciplines apply to each.

## Heuristic: overapproximate

True TCB membership is hard to determine analytically. We
overapproximate: walk the dependency graph from kernel modules
outward; any module within N hops of a TCB seed is tagged TCB. False
positives (non-TCB files flagged TCB) acceptable; false negatives
(TCB files missed) are not.

### Seed list

These modules are TCB by definition:

- `src/ecCoreFol.ml` — proof-term and formula representation.
- `src/ecAst.ml` — AST core.
- `src/ecTyping.ml` — type-checker.
- `src/ecCoreGoal.ml` — proof-state kernel.
- `src/ecLowGoal.ml` — kernel-level tactics that produce raw proof
  terms.
- `src/ecReduction.ml` — definitional equality.
- `src/ecMatching.ml` — pattern matching at the kernel level.
- `src/ecCoreLib.ml` — core library theorems.
- Why3 bridge / SMT prover glue (accepts external prover decisions;
  must be sound about which solver outputs to trust).
- `src/ecParser.mly`, `src/ecLexer.mll` — parser/lexer (debatable;
  structural parsing isn't soundness per se, but bad parses can
  mislead the user about what got accepted; conservative inclusion).

### Sweep

Any module that opens / depends on a seeded module within one or
two hops is also tagged TCB. Iteratively. The result is an
**overapproximated TCB list** maintained in this doc.

### Initial TCB list (DRAFT — needs maintainer confirmation)

This is a first-pass overapproximation; the EC maintainer should
review and prune obvious non-TCB members. False positives are
acceptable.

**Definitely TCB (seeds + immediate kernel):**
- `src/ecAst.ml`, `src/ecCoreFol.ml`, `src/ecCoreGoal.ml`,
  `src/ecLowGoal.ml`, `src/ecCoreLib.ml`.
- `src/ecTyping.ml`, `src/ecReduction.ml`, `src/ecMatching.ml`.
- `src/ecUnify.ml` (kernel-level unification, if present).
- Why3 bridge files (TBD enumeration based on actual file names).
- `src/ecParser.mly`, `src/ecLexer.mll`.

**Likely TCB (one hop out, conservative):**
- `src/ecScope.ml` — scope management; touches every kernel
  operation. Conservative: TCB.
- `src/ecCommands.ml` — command dispatcher; routes to kernel
  operations. Conservative: TCB.
- `src/ecIo.ml` — feeds parser; conservative: TCB.

**Likely non-TCB (despite being in `src/`):**
- `src/ecHiGoal.ml` — high-level tactics that compose kernel
  primitives. Outputs are kernel-rechecked, so bugs here don't
  produce unsound proofs.
- `src/ecPrinting.ml` — pretty-printer. Bugs → wrong displayed
  text, never wrong proof.
- `src/ec.ml` — REPL driver, JSON serialization, additions (1, 3,
  4, 5, 6, 7, 8, 13, 14, 15, 16). UI / wire layer; non-TCB.
- `src/ecExecJson.ml` — addition 13 dispatch logic; non-TCB
  (routes to kernel, doesn't itself check).
- `src/ecSearchTab.ml` — search; non-TCB.
- `src/ecLocation.ml` — source-location tracking; non-TCB.

**Maintainer review needed.** This list is a starting point; an
EC kernel maintainer should walk the actual dependency graph and
finalize. The `daemon:` vs `ec-core:` discipline depends on
having this map correct.

### Tooling-side (`tooling/**`)

By construction, **non-TCB**. The daemon doesn't make proof-checker
decisions; it routes them. Bugs are UX-grade (wrong diagnostic,
slow exec, dropped event), never soundness-grade.

The boundary lint enforces this: `tooling/**` cannot import
EC-internal modules outside the public addition surface tracked in
`UPSTREAM.md`. (Lint enforcement extends post-merge — see
`doc/tooling-poc-plan.md` § Merged-binary architecture.)

## Discipline by category

### TCB code — soundness-touching root-cause fixes (`ec-core-critical:` prefix)

This is the strictest category. Use when touching TCB files (per
the list above) AND the change addresses a soundness mechanism
(typechecking, function/symbol resolution, kernel reduction,
proof-state manipulation, prover bridge, kernel tactics that
produce raw proof terms).

**Tests required:**
- Differential oracle (current `run_diff_oracle`, expanded for
  ANALYZE-JSON; future expansions as new EC↔JSON endpoints land).
- Replay corpus (`run_replay_smoke` plus future replay-corpus
  expansion).
- Grammar corpus (`run_repl_core_tests` covers some; full grammar
  corpus is a Phase 2 acceptance gate, not yet implemented).
- Existing TCB-relevant smokes (`run_ec_llm_smoke`, etc.).
- All three must be re-run and reported in the commit message;
  green state is a precondition for post-approval.

**Workflow** (per `doc/commit-conventions.md` rule 7):
- **Pre-approval**: written proposal — code path, semantic shift,
  soundness argument, files, expected LoC, test plan. Maintainer's
  explicit "go" required before any code is written.
- **Post-approval**: maintainer reviews diff + tests + soundness
  argument + concrete bug-fix repro before commit. Maintainer's
  explicit "commit" required.
- **No autonomous execution**, even in auto mode.
- **No scope creep**: scope locked at pre-approval; no "while
  I'm here" cleanups, refactors, renames, or adjacent fixes.
- **Detailed inline documentation** at the change site explaining
  the mechanism being repaired and the fix's correctness.

**Review depth:**
- EC kernel-team review (maintainer-driven).
- Reviewer responsibilities: verify the change preserves kernel
  invariants; check that the differential oracle stays green;
  watch for subtle proof-term equality changes; verify the
  soundness argument matches the code as written.

**Refactor velocity:**
- Conservative. Small, well-tested, narrowly scoped commits.
- No "experimental cleanup" PRs in TCB. Cleanups only if approved
  in their own pre-review.

### TCB code — non-soundness-touching (`ec-core:` prefix in TCB files)

For TCB files where the change is mechanically clean and doesn't
modify the soundness invariant — e.g., adding a structured-output
JSON serializer alongside an existing pretty-printer (addition 3),
adding a meta-command that dispatches into existing kernel paths
(addition 13), tagging events on REPL replies (addition 4).

**Tests required:**
- Same TCB-strict gate as above (diff oracle + replay + grammar +
  smokes); the file IS in the TCB list, so the testing bar
  matches.

**Workflow:**
- Standard `ec-core:` workflow. UPSTREAM.md entry required;
  matched in same commit.
- Manual review by EC kernel-team for any TCB file touch, but
  without the formal pre/post approval cycle of the critical
  category.

**Refactor velocity:**
- Conservative within TCB files; same testing bar as critical.

When in doubt between `ec-core:` and `ec-core-critical:`: ask
the maintainer. The line is "does this change a soundness
mechanism, even subtly?" If the change could cause the kernel
to accept a previously-rejected proof or reject a previously-
accepted one — even in obscure edge cases — it's `ec-core-critical:`.

### Non-TCB code in `src/` (still `ec-core:` prefix)

**Tests required:**
- Smoke + conformance tests (whatever is appropriate for the
  feature — same bar as `daemon:` work).
- Differential oracle / replay corpus optional (not load-bearing
  for these changes).

**Review depth:**
- Standard review.
- Reviewer responsibilities: spec-compliance, UX correctness,
  test coverage.

**Refactor velocity:**
- Looser; comparable to daemon work.
- Experiments OK with smoke coverage.

### Tooling code (`daemon:` / `tui:` / `nvim:` / etc. prefixes)

**Tests required:**
- Smoke tests for new behavior.
- Round-trip / conformance for wire-affecting changes.
- Unit tests where appropriate.

**Review depth:**
- Standard review.

**Refactor velocity:**
- Aggressive OK; non-TCB layer.
- Experimentation encouraged within the boundary.

## How to evaluate a new file

When a new `src/**` file is added:

1. List its direct dependencies (`open` / module references).
2. If any dependency is in the TCB list → new file is also TCB.
3. If unclear, default to TCB (overapproximation). Reviewer can
   demote later with confidence.

When a new `tooling/**` file is added: non-TCB by construction.

## Periodic re-sweep

The TCB list ages. Once per release cycle, an EC kernel maintainer
re-walks the dependency graph and updates the list. Typical churn:
new modules added, old modules split / merged, refactors changing
import structure. Re-sweep catches drift.

## Why this discipline

EC's value is *correctness of accepted proofs*. Anything in the
soundness path needs the most rigorous tests we can muster (oracle,
replay, grammar corpus). Non-TCB code can move faster because its
worst case is "annoying," not "wrong proofs accepted."

Without this distinction:
- TCB changes ride daemon-class testing → soundness regressions
  slip through.
- Non-TCB changes ride TCB-class testing → glacial development pace
  for UX work.

The distinction lets us be appropriately rigorous about kernel work
without strangling the iteration speed of UI/UX/LSP/MCP work.
