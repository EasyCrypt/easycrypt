# EcLlm × tooling daemon — convergence brief

Meeting doc, 2026-07-26. Detailed evidence in the appendices.

**Context.** Two descendants of the original `llm-interactive` REPL
now exist. PYS force-pushed `origin/llm-interactive` @ `fd5e04a0e`:
the REPL rewritten into `src/ecLlm.ml` (15 commits over Jul-15
main). Gustavo's local branch @ `8268700ec` (204 commits over Apr-29
main): the daemon/LSP/VSCode stack, whose EC side is the *old* REPL
plus a machine-facing protocol surface. Zero shared patches. Both
speak the same protocol family (`READY/OK/ERROR [uuid:N]`, `<END>`,
`<BEGIN>/<DONE>`, LOAD/UNDO/REVERT/CHECKPOINT/GOALS/SEARCH/QUIET).

## Where we each are

- **EcLlm** (PYS): clean Parse/Dispatch REPL; TREE / FOCUS / NEXT
  over a real proof DAG (`pr_parent` in `EcCoreGoal.proofenv`),
  COMMIT (bullet-structured proof emission), `LOAD -trace|-nosmt` +
  per-LOAD `easycrypt.project` overlay, `-eval` scripted mode,
  `-stdlib DIR`. Agent-facing, single session, pp-text output.
- **Daemon stack** (Gustavo): `ecd` (OCaml/Eio) orchestrating `ec
  llm` subprocesses — per-project sessions, document model +
  reconcile, PG-style navigation, speculation (tryTactic / preview /
  closer sweep), LSP → VSCode extension (goal pane, builders,
  pickers), MCP planned. Needs from EC: JSON frames (GOALS-JSON,
  PARSE, ANALYZE, EXEC-JSON), typed errors, `[proto:]`/`[restarted]`
  tags, `NOTICE:` framing, SIGINT cancel (`EcCancel`) — all present
  in the old REPL, absent from EcLlm (see Appendix A).

## Proposal

**EcLlm becomes the single session core; one wire protocol with two
profiles; the daemon consumes only that protocol.**

```
L0  engine additions: pr_parent DAG, focus, bullets, EcCancel
L1  EcLlm: uuid/undo, checkpoints, transcript+COMMIT, LOAD, tree
      · ergonomic profile (pp goals, TREE, HELP)  ← agents direct
      · machine profile (JSON frames, tags)       ← daemon
L2  daemon: sessions, documents, speculation — MCP (first target) + LSP
L3  agents via MCP · VSCode/TUI · raw agents via `ec llm`
```

Key invariant kept: the *document* stays the single source of truth
(stock-`easycrypt`-checkable); COMMIT becomes the sanctioned bridge
from session-first authoring back into text.

**Construction rule (proposed): split by layer, not by branch.**

- **Kernel / TCB / proof checker — PY's, verbatim.** His
  `pr_parent` DAG, `rotate_focus`, DAG accessors, `focus_goal`,
  `pp_tree`, bullets machinery, `set_xgoal` are maintainer-
  validated and land as-is. Future kernel-adjacent work routes
  through him — including our `EcCancel` (it instruments FApi
  combinators + the prover bridge), submitted for his review under
  exactly this rule.
- **Communication layer — ours, evolving JSON-first.** Our
  envelope/serialization surface is the base, and it migrates to a
  uniform JSON wire (v2, behind a proto bump): every reply, notice,
  error, and goal structured end-to-end — the substrate a proper
  MCP needs. EXEC-JSON generalizes from side-command to *the*
  command channel. PY's ergonomic line REPL (pp-text, TREE,
  `-eval`) is untouched as the human/direct-agent mode; both modes
  share the session core in `ecLlm.ml`.
- **Tooling on top — ours, reordered: MCP is the first target**
  (semantic proof mode for agents), the VSCode experience second,
  both over the same daemon primitives.

His REPL features are kept and re-served structurally: TREE/FOCUS/
COMMIT logic feeds JSON equivalents (subgoal DAG with stable paths,
structured proof fragments); LOAD `-nosmt`/`-trace`/projini,
`-eval`, `-stdlib` adopted as-is.

## Agenda — decisions wanted

1. **Ownership split — the main point.** Kernel/TCB additions are
   yours: we take them verbatim and route future kernel-adjacent
   work through you (our EcCancel included). The communication
   layer and the tooling above it are ours, moving to a JSON-first
   wire whose first consumer is a proper MCP server. Ask: both
   modes (your ergonomic REPL, our machine wire) share the session
   core in-tree, so neither side re-ports the other.
2. **Three one-line protocol fixes** worth taking regardless:
   `[proto:N]` on READY; `[restarted]` tag on restart-class replies;
   `NOTICE: ` prefix framing (streamed, not buffered).
3. **`<BEGIN>/<DONE>` line handling**: keep raw lines + newlines
   (current EcLlm strips + space-joins → offsets/literals drift).
4. **`strict_bullets` relaxation scope**: REPL-typed phrases only.
   Blanket relax makes daemon-fed documents check differently than
   batch — breaks re-checkability.
5. **uuid contract, written down**: +1 executable, FOCUS +1
   (undoable — good); directive behavior to verify empirically. The
   daemon adopts whatever EcLlm does — it just needs the contract
   stable and documented.
6. **Directive replies** — resolved daemon-side: we adopt a
   `QUIET ON` + explicit-`GOALS-JSON` convention, so no change to
   his reply behavior is needed (FYI; the `NOTICE:` prefix from (2)
   still helps separate payload from warnings).
7. **EcCancel — deferred from pass 1** to keep the ec-core delta
   minimal. Submitted for your review later (EcLlm would gain safe
   Ctrl-C); until then daemon cancel degrades to subprocess kill +
   respawn.
8. **Branch homes**: `llm-interactive` = EcLlm track? Where the
   daemon stack lives; push policy for the converged tree.
9. **Forward-looking — parallel proof workers**: N sessions each
   `LOAD file LINE -nosmt` → `FOCUS` → try → `COMMIT`; coordinator
   splices fragments, primary re-checks. EcLlm's primitives are
   exactly the worker verbs; later fork-safe workers give O(1)
   clones. Strengthens (1). Also: `-stdlib` is a direct win for the
   bundled `.vsix`; LOAD-projini vs per-project subprocesses worth a
   shared design note.
10. **Forward-looking — inspecting long LLM-generated proofs.**
    Agent-written proofs run hundreds of lines; reviewing them needs
    more than linear reading. The converged pieces map directly:
    frame tree → proof outline + editor folding; uuid↔sentence map
    (+ goals cache) → click-any-line state inspection; `LOAD -trace`
    / structured goal diffs → per-step "what changed" review;
    speculation + parallel workers → automated audit passes
    (dead-step elimination, `admit`/`smt` census, per-step timing,
    proof minimization); COMMIT → normalize flat agent output into
    bullet-structured scripts. Mostly daemon/editor-side work, but
    it leans on engine data (DAG, structured goals, trace) — more
    weight behind (1).

## What the daemon side adopts from EcLlm

TREE/FOCUS/NEXT as the subgoal-addressing substrate (GOALS-JSON to
carry dotted paths); COMMIT + document splice; `-eval` for scripted
smokes; `-stdlib` for bundling; Parse/Dispatch as the host structure
for the ported surface.

## Proposed sequence (post-meeting)

1. Rebase model, no merge commits: the new branch starts at
   `origin/llm-interactive` (already linear on main's history); our
   content lands as a fresh linear series on top — tooling /
   vscode / doc transplant first, then the machine-layer port (his
   REPL skeleton, our wire inside; batch `llm` mode retired). The
   old line is preserved at `archive/llm-interactive-20260726`.
   Catch-up to the `main` tip happens by rebase, ideally riding
   PY's own next rebase. Smoke suite green gates each step.
2. Wire v2: pin the JSON envelope schema (NDJSON replies/events,
   typed errors, structured goals native; commands via generalized
   EXEC-JSON), implement behind a proto bump; daemon flips in
   lockstep (we control both ends).
3. **MCP v1 — the first target**: semantic tool set (structured
   goals / tree / focus / exec / speculate / search /
   commit-fragment / document splice) + worker sessions with
   per-lemma region leases for parallel agents on one file.
4. QoL substrate: statement-hash cache + `-nosmt` prefix loading =
   skip untouched proofs; incremental re-check. Serves MCP and
   VSCode alike.
5. VSCode experience rides the same primitives (the existing LSP
   stays working via capability gating); beta re-cut after.

---

## Appendix A — gap matrix (daemon vs EcLlm today)

Fatal: no `[proto:]` on READY (handshake rejects at spawn); no
GOALS-JSON / `<PARSE-…>` / `<ANALYZE-…>` / EXEC-JSON (goal pane,
sentence splitting, diagnostics, structured exec all fail); no
`[restarted]` tag (uuid-invariant check declares session dead on any
restart); no EcCancel (SIGINT kills the process — cancel becomes
destructive).

Degraded: no `ERROR-JSON` (typed errors collapse to `Internal`);
notices buffered + unprefixed in bodies (print/search output mixed
with goals; no streamed progress for speculation hooks); error
replies append goals to the message; `<BEGIN>/<DONE>` space-join
(in-sentence error locations, multi-line literals, first-token
offsets).

Semantics to pin: blanket `disable_repl_bullets`; whether directives
bump uuid; COMMIT transcript records directives (noise).

## Appendix B — take/keep inventory (by layer)

**From PY, verbatim (kernel/TCB)**: `pr_parent` DAG +
`rotate_focus` + parent/children accessors (`EcCoreGoal`);
`focus_goal`, `open_handles`, `pp_tree`, `in_proof`,
`disable_repl_bullets` (`EcCommands`); `EcScope.set_xgoal`.
Non-kernel but adopted as-is: LOAD `-nosmt`/`-trace`/projini
overlay, `-eval` + exit codes, `-help`, `-stdlib`, `llm_option`
cleanup (batch mode retired), Parse/Dispatch module shape, and the
FrameTree + COMMIT feature logic (re-served through JSON).

**Ours (communication layer)**: session/uuid envelope discipline,
proto versioning, restart signaling, notice/error semantics —
recast as typed JSON events in wire v2 — plus the structured
surface: GOALS-JSON stack (conclusion tree, STMT-JSON, per-pregoal
PPEnv), PARSE/ANALYZE frames (first-token offsets, scope-tagging,
synthetic-abort), `searchall`, newline-preserving multi-line.
EXEC-JSON returns as the v2 command channel.

**Ours (tooling)**: daemon (sessions, documents, reconcile,
speculation), MCP server (new — first target), LSP + VSCode
extension, TUI, smoke/replay/diff-oracle substrate.

**Routed through PY (TCB rule) — both deferred from pass 1** to
keep the ec-core delta minimal: EcCancel + combinator
instrumentation + prover-bridge kill/respawn (until then, daemon
cancel degrades to kill + respawn of the EC subprocess);
bullets-relaxation scoping (short-term we accept EcLlm's blanket
relax — `+strict_bullets` files are rare — daemon-strict flag comes
with the ask later).

**Aims → mechanisms**: semantic proof mode = MCP tools over
structured goals + speculation + tree/focus; faster iteration =
statement-hash cache (skip untouched proofs) + `-nosmt` prefix +
incremental re-check; parallel agents = worker sessions + per-lemma
region leases + COMMIT/splice merge + primary re-check.

## Appendix C — merge conflict surface

Both touch: `src/ec.ml` (ours +1568: old REPL + JSON emission; his:
`` `Llm`` arm → `EcLlm.run`, projini, `-stdlib`),
`ecCommands.{ml,mli}`, `ecCoreGoal.ml(+mli)`, `ecOptions.{ml,mli}`,
`ecScope.{ml,mli}`. Ours-only: `ecCancel.*`, `ecExecJson.ml`,
`ecHiGoal.ml`, `ecLexer.mll`, `ecParser.mly`, `ecParsetree.ml`,
`ecProvers.ml`, `phl/ecPhlLoopTx.ml`, `dune`; all of `tooling/`,
`vscode/`, `doc/`. Main-drift (64 commits) is a separate mechanical
axis. Estimate: one merge session + 1–2 port sessions.
