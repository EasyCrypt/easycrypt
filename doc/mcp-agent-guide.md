# EasyCrypt MCP — agent guide

Operating manual for LLM agents driving EasyCrypt proof sessions
through the `ecd mcp` server (23 tools). Written for the agent;
the [Setup](#setup-human-operator) section is for the human
operator. Server internals: `tooling/lib/mcp_server.ml`; design:
[doc/ecllm-compat.md](ecllm-compat.md).

## Mental model (read this first)

1. **A session is a live EasyCrypt subprocess** holding one proof
   state, identified by a label you choose (`{"session": "w1"}`;
   default `"main"`). Sessions share nothing at runtime; parallel
   sessions cannot corrupt each other.
2. **The document is the only truth.** Nothing you do in a session
   is real until it lands in the `.ec` file and re-checks. Your
   session work is exploration; `commit_proof` / `replace_proof`
   are the bridges back to text.
3. **`uuid` is the undo-stack position.** Every reply reports it.
   `revert {uuid}` goes back; you can never go forward again —
   treat uuids you might return to as checkpoints and prefer the
   state-restoring tools (`try_tactic`, `check_script`,
   `check_skeleton`) over manual revert bookkeeping.
4. **`stale: true` on a reply means the file changed on disk after
   your session last loaded/synced it.** Everything you compute
   while stale is against old text. Run `resync_file` before
   trusting or writing anything.
5. **Edit modes are locks.** `mode=statement` (default) may change
   declarations and holds the file exclusively. `mode=proof` +
   `lemmas=[...]` claims specific lemmas and parallelizes; you may
   only touch the proof bodies of your claims. Conflicts are
   refused with the holder named — that is coordination working,
   not an error to work around.
6. **Sentences end with `.`** — every `text`/`script`/`tactic`
   argument is EasyCrypt concrete syntax, `.`-terminated,
   newline-separated for multi-sentence input.
7. **No cancellation yet.** A slow `smt()` blocks the session until
   it finishes. Keep iteration cheap: `nosmt` prefixes, small
   candidate scripts, and consider `pragma silent` prover-timeout
   discipline in exploration.

## Tools by workflow

### Opening and navigating

- `open_file {path, mode?, lemmas?, upto_line?, nosmt?, session?}`
  — spawn a session and LOAD the file. `upto_line` stops after the
  sentence ending on that line; `nosmt: true` weak-checks the
  prefix (fast; safe when the prefix is already verified — the
  standard way to position at a lemma). Proof mode requires
  `lemmas`; the reply's `claims` carry each lemma's document
  region (`start_line` / `decl_end_line` / `end_line`) — use them
  for `upto_line` targeting and splicing. Leading banner comments
  attach to the declaration: `start_line` may point at the banner
  (the region moves as one block), while `decl_end_line` is always
  the declaration's own last line — target that for positioning.
  Re-opening a label replaces that session and releases its locks.
- `goals {session?}` — structured proof state (GOALS-JSON):
  subgoal count, hypotheses (name/kind/pp), conclusion tree (PHL
  judgments carry structured program statements). Parse it; never
  scrape pp text when a structured field exists.
- `tree` / `focus {path|"next"}` — the open-subgoal tree with
  dotted paths, and focus rotation (undoable: advances uuid).
- `exec {text}` — execute and advance, ONE SENTENCE AT A TIME: the
  input is split by the real parser; successes COMMIT, the first
  failure stops the sequence, and the reply reports every sentence
  (per-sentence uuid + time_ms, `goals_at_failure` on error —
  earlier sentences REMAIN EXECUTED; revert or resync to unwind).
  Input with a parse error anywhere is refused ATOMICALLY. The
  wire itself rejects multi-phrase blocks, so nothing can be
  silently dropped at any layer.
- `revert {uuid}` — go back to an earlier uuid.
- `list_sessions` / `close_session {session}` — inventory (with
  modes + claims) and teardown. Close sessions you are done with:
  each one is an OS process, and your locks release with it.

### Reading and searching

- `search {pattern, strict?, limit?}` — structured lemma/operator
  hits. Default mode is overload-tolerant (`searchall`): untyped
  patterns like `(_ <= _)` or `(_ %/ _)` just work. Use it before
  inventing a lemma name; `total_hits`/`truncated` tell you when
  to narrow.
- `query {text}` — any read-only directive (`print Foo.`,
  `locate f.`). Output arrives as text; state does not move.
- `analyze_file {path}` — whole-file diagnostics (positions,
  classes, enclosing scopes) without touching session state. Use
  after batch edits to find breakage cheaply. Session-free: if the
  label has no session (e.g. `open_file` itself just failed), it
  runs in an ephemeral one — always available as a diagnostic.

### The exploration loop (state-neutral)

- `try_tactic {tactic}` — run one tactic, capture resulting goals,
  auto-revert. Your cheapest probe.
- `check_script {script}` — run a multi-sentence candidate (a
  whole proof body) from the current state: per-sentence verdicts
  + `time_ms`, a `closes` verdict, then full state restore. The
  refactoring inner loop: iterate candidates here; only write when
  one passes. On failure, `goals_at_failure` is the state entering
  the failed sentence — no blind re-runs to see the residual goal.

### Writing back (the only file-writing path)

- `commit_proof {session, lemma?, write?}` — emit your session's
  successful phrases as a bullet-structured proof body. With
  `write: true` and a claimed `lemma` it LANDS the proof
  directly: wraps the transcript in `proof.`/`qed.`, splices,
  resync-verifies, restores on failure. Requires the proof to
  be closed — the zero-seam ending after stepping with `exec`.
- `replace_proof {lemma, script, nosmt?}` — verified in-place body
  replacement: splices over the claimed lemma's body lines,
  re-syncs (weak prefix + fully-checked tail), and RESTORES the
  original file automatically if verification fails. Stale-gated
  and claim-gated. `ok: false` with `file_restored: true` means
  "candidate rejected, nothing changed on disk".
- `resync_file {nosmt?, upto_line?}` — after ANY on-disk edit
  (yours via editor tools, or another agent's): diffs against the
  loaded snapshot, weak-checks the unchanged prefix, fully checks
  the changed tail. The `classification` field tells you the blast
  radius: `proof-body-only` provably cannot affect other lemmas;
  `additive` = pure appends; `statement-changing` invalidates
  downstream (and warns in proof mode — that edit belonged in a
  statement session). Note: session state becomes exactly the
  file's state; un-committed interactive work is dropped.
  `upto_sentence: N` executes exactly the first N sentences —
  positioning at ANY sentence boundary, including mid packed line.
  `at_lemma: "<name>"` positions just inside that lemma's proof —
  sentence-granular, so it works on packed `proof. tac. qed.`
  lines where `upto_line` cannot; prefer it over manual line math.
  When the file is unchanged and the target is ahead, the reply
  carries `fast_forward: true` and nothing reloads — forward hops
  are near-free.

### Strategy layer (refactoring at proof-structure level)

- `proof_profile {lemma}` — per-branch hotspot ranking: time, smt
  and admit counts, fragility markers (`progress`, `!`-rewrites).
  Decide WHAT to restructure here.
- `proof_outline {lemma}` — the proof's shape: every sentence
  attributed to a branch path, split points, and the OBLIGATION
  SET (per-split goal hashes + one-liners). Two built-in recipes,
  no extra tool needed: (a) *similarity* — compare branches'
  `src` sequences and entry goals yourself to spot factoring
  candidates; (b) *obligation diff* — run outline before and
  after a restructure and compare the hash sets: same hashes =
  same proof debt reorganized; new/missing hashes = you changed
  what is owed. Both outline and profile REPOSITION the session
  to the lemma's end.
- `check_skeleton {script}` — verify a restructured skeleton at
  admit-speed: `admit.` sentences are holes; the reply lists each
  hole's branch path + goal + hash; state restored. Iterate
  structure first, pay for leaves later.
- `admitted_goals {lemma?}` — the goals your admits close: audits
  every admit-bearing declaration (or one lemma) by replay,
  returning goal + hash per admit. Every executing tool also
  reports a live `admitted` array — swept-under-the-rug debt is
  always visible. Repositions the session.
- `extract_lemma {name?}` — candidate standalone lemma from the
  focused goal (vars → binders, hyps → premises). UNVERIFIED and
  prop-conclusions-only: refine it, `check_script` it, then place
  it via a statement-mode edit.

### Semantic per-subgoal claims ("semantic bullets")

For working one subtree at a time with enforced containment —
including filling `check_skeleton` holes:

- `claim_subgoal {path, force?}` — claim one open subtree by its
  `tree` path. Focus moves there; the reply carries the entry
  goal + hash (verify it matches the hole/goal you intended) and
  `remaining_in_subtree`. One open claim per session — for
  parallel subgoals, use one session per subgoal.
- `exec_in {text}` — run tactics INSIDE the claim,
  transactionally: `qed`/`save` and `cycle` are refused (closers
  belong to the skeleton owner; cycle escapes the claim),
  containment is checked after every sentence, and any failure or
  violation reverts the whole sequence. `subtree_closed: true`
  returns your accumulated transcript — hand it to the
  coordinator for assembly. Bullets are re-generated by
  `commit_proof` at text time; you never type them.

## Standard workflows

**Prove one lemma — two loops, both landing themselves.**

*Compose loop* (default for routine proofs — one round trip per
candidate, and the passing candidate lands itself):
```
open_file {path, mode:"proof", lemmas:["foo"], nosmt:true}
resync_file {at_lemma:"foo"}
check_script {script:<whole body>, on_close:"commit", lemma:"foo"}
   # fails -> goals_at_failure, state restored; iterate
   # closes -> written + verified, SAME call. Done.
```

*Step loop* (switch when candidates keep dying — per-step goal
feedback beats blind recomposition, and failed smt() is the cost
model):
```
resync_file {at_lemma:"foo"}
goals / try_tactic (probe) → exec (commit the winning step) → ...
   # exec replies carry proof_complete:true when the goals close
commit_proof {lemma:"foo", write:true}     # transcript lands, verified
```
No manual splicing in either loop; `replace_proof` remains for
landing text composed elsewhere.

**Parallel lemmas (orchestrator + workers).** Orchestrator picks
disjoint lemmas; each worker opens `{session: "w<i>", mode:
"proof", lemmas: ["lem_i"], nosmt: true}` — the locks make
interference impossible. Workers iterate `check_script` →
`replace_proof`. A worker refused for `stale` just runs
`resync_file` (absorbing siblings' writes) and retries. Statement
edits: close workers → one statement session → edit → re-dispatch.

**Refactor a big file for speed/size.**
```
proof_profile {lemma}         → pick the expensive branch
proof_outline {lemma}         → read the strategy; note obligation hashes
resync_file {at_lemma: "<lemma>"}
check_skeleton {new skeleton with admit. holes}
  → for each hole: claim_subgoal {path} → exec_in until closed
  → assemble: skeleton with holes replaced by transcripts
check_script {assembled body} → closes: true?
replace_proof {lemma, script: assembled}
proof_outline again           → hash-diff obligations vs before
```

**Recover from anything confusing.** `resync_file` makes the
session ≡ file. If the session itself is wedged (rare), re-run
`open_file` with the same label.

## Discipline

- After every reply, glance at `stale` and `uuid`. Stale → resync
  before you trust or write.
- Never edit the file regions of lemmas you have not claimed; the
  server refuses what it can see, but out-of-band editor writes
  are on you until the final re-check catches them.
- Prefer state-neutral probes (`try_tactic`, `check_script`,
  `check_skeleton`) over exec-then-revert.
- When a goal embeds a whole `main`, reach for `tree` (one line
  per goal) or `goal_detail: "shape" | "counts"` — loop tools
  default to `shape` (program bodies elided to instruction
  counts); full dumps are what `goals {goal_detail: "full"}` is
  for. Every reply carries exactly ONE terminal-state field
  (`goals`/`goals_at_end` on success, `goals_at_failure` on
  failure).
- `admit` is allowed and visible (profile counts it; skeleton
  treats it as a hole). Never leave one in text you hand back
  without saying so.
- Long `smt()` calls block the session (no cancel yet). In
  exploration, keep candidates small; rely on `nosmt` prefixes;
  full-strength checking happens at replace/resync tail time and
  in the final batch check.
- Tool errors (`isError`) are protocol/coordination refusals —
  read the message; it names the conflicting session or the
  missing step. EasyCrypt-level failures inside otherwise-OK
  replies (`ok: false`, per-sentence `error`) are proof feedback.

## Setup (human operator)

Build in the `ec-llm-next` worktree with the dev shell — a FULL
`dune build` (the root `ecd.native` promote rule does not fire on
incremental `dune build tooling/...` invocations, which leaves a
stale root binary):

```bash
dune build                       # refreshes root ecd.native (promote)
rm -f ec.native && cp _build/default/src/ec.exe ec.native && chmod +w ec.native
```

Register **from the project directory the agent session works in**
(local scope is per-project; registering from the tooling repo
hides the server from real sessions), or add `--scope user` for
all projects:

```bash
claude mcp add easycrypt \
  --env EC_LLM_BIN=/Users/gdel/Repos/ec-llm-next/ec.native \
  -- /Users/gdel/Repos/ec-llm-next/ecd.native mcp
```

The server speaks MCP over stdio; sessions spawn `ec llm`
subprocesses with the target file's directory as CWD (so
`easycrypt.project` is honored). `EC_LLM_BIN` pins the EC binary;
without it, discovery falls back to the in-tree `_build` binary
and then `easycrypt` on PATH. Smoke: `EC_LLM_BIN=$PWD/ec.native
dune exec tooling/smoke/run_mcp_smoke.exe` (expects 58/58).

## Known limits (v1, honest)

- No cancellation (EcCancel deferred): a hung candidate costs its
  SMT timeout; a killed session costs a reload.
- Containment in `exec_in` is goal-count accounting plus a lexical
  gate on `cycle` — handle-level verification is pinned (needs a
  TREE-JSON machine command).
- `proof_outline` attribution assumes standard focused-goal
  sentences; exotic multi-goal tacticals may mis-attribute.
- `extract_lemma` output is a candidate, not a theorem.
- Cross-file `require` dependencies are not lock-modeled: editing
  a required library invalidates dependents silently until their
  resync/re-check.
- `replace_subproof` / `merge_subproofs` (per-subgoal writes) are
  not yet implemented — assemble subtree transcripts into a body
  and use `replace_proof` at lemma granularity.
