# Program-logic (`src/phl`) refactoring — plan & rationale

This is the design document for the long-running reorganization of EasyCrypt's
program logic. The companion [README.md](README.md) is the short, stable
"how a migrated tactic is structured" reference; this file records the *why*,
the full plan, and the per-tactic migration recipe. Work proceeds **one tactic
at a time**.

---

## 1. Motivation — what was wrong

The original `src/phl` is ~75 files, one `.ml`/`.mli` pair per *tactic*
(`ecPhlSeq`, `ecPhlWhile`, …), each holding **every logic** for that tactic.
Concretely:

1. **Typing entangled with dispatch.** `process_<tactic>` interleaves
   "which logic is this goal?" (`is_hoareS`, `match concl.f_node`) with
   "type this formula in that logic's memory". You cannot read one logic's rule
   without reading all the others' arms.
2. **Inconsistent dispatch.** Some tactics match `concl.f_node`, some use `is_*`
   predicates, some add an extra `ecPhlHi<Tactic>` file — no principled layer.
3. **Proof-nodes are not recheckable.** Low-level (TCB) tactics close goals with
   `FApi.xmutate1 tc \`Tag [subgoals]`. The tag (`` `HlApp ``, `` `While ``, …)
   carries **no parameters** and is **never destructed anywhere in the tree**.
   The data justifying the step (split position, intermediate assertion,
   bijection, invariant) is discarded, so a node cannot be re-validated.
   `FApi.close` trusts every tactic unconditionally; there is no checker kernel.
4. **TCB vs derived is implicit** — only discoverable by grepping for `xmutate`
   (30 of 37 `.ml` files are TCB; 7 are pure orchestration).
5. **A logic is scattered** — auditing "everything in the equiv logic" means
   opening ~30 files.

## 2. Findings about the current engine (so the plan is grounded)

- **TCB boundary** is `FApi.xmutate / close` ([ecCoreGoal.ml](../ecCoreGoal.ml)).
  A node is `VExtern : 'a * handle list` — a GADT existential, so a generic
  traversal cannot even inspect the tag.
- **Dispatch wiring**: `process1_phl` in [ecHiTacticals.ml](../ecHiTacticals.ml)
  maps each `EcParsetree` tactic constructor (`Pseq`, `Pwhile`, …) to a
  `process_*` function.
- **Goal classification** lives in `ecCoreFol` (`is_hoareS`/`destr_hoareS`/…) and
  `ecLowPhlGoal` (`tc1_as_hoareS`/`pf_as_hoareS`/…).
- **Three tactic families** (this drives the directory layout, §5):
  - *logic rules* — genuinely different subgoals per logic: seq, while, call,
    cond, rnd, conseq, fun, exists.
  - *code transforms* — transform the program statement and re-wrap in the
    **same** judgement; logic enters only as "grab the stmt+memory", so the core
    is shared across logics: wp, sp, inline, swap, rcond, fission/fusion/unroll/
    splitwhile, kill/alias/cfold, outline, rwequiv.
  - *bridges / multi-logic* — deno, pr, byequiv, fel, upto, eager; and the
    special multi-logic tactics conseq/trans/sym that operate across judgements.

## 3. Target architecture — the four-layer spine

Every tactic is decomposed into the same four layers:

```
DISPATCH      process_<tactic>        logic-agnostic. Inspect goal kind, route.
   │                                  Only place is_hoareS / f_node lives. No typing.
   ▼
ELABORATION   process_<logic>_<tac>   goal kind known; type parse-tree args in that
   │                                  logic's memory, build typed params, call rule.
   ▼
RULE (TCB)    t_<logic>_<tac>         compute subgoals from typed params via a PURE
   │                                  shared builder, emit a recheckable node that
   │                                  records those params.
   ▼
CHECKER       check_<logic>_<tac>     read params from the node, rerun the SAME pure
                                      builder, is_conv-compare to the stored subgoals.
```

The rule and its checker **share one pure subgoal-builder**
`<logic>_<tac>_subgoals : LDecl.hyps -> <judgement> -> params -> form list`. The
checker is then just "rerun the builder and compare", so recording the params in
the node is the entire cost of recheckability. The builder takes the goal's
`hyps` (the authoritative context — `env` is just `LDecl.toenv` of it, and the
conversion check needs `hyps` anyway), so the rule and checker share one context.
Derived (orchestration-only) tactics emit **no** node and need **no** checker —
rechecking recurses into the rules they expand to.

The destruct/rebuild/compare boilerplate common to every checker is factored into
its own module, [`ecPhlRecheck.ml`](ecPhlRecheck.ml): `recheck_forms` (arity +
per-subgoal `is_conv` under each subgoal's hyps) and `checker_of name destr
build` (assemble a `rule_checker` from a `pf_as_*` reader and a builder, wrapping
any rebuild exception into a `RecheckFailure`). A per-rule checker is then only
its registration. A hyps-changing rule (one emitted via `xrule*_hyps`, e.g.
`while`) will need a hyps-aware variant that also validates the recorded
hypotheses — to be added when the first such rule is migrated.

## 4. Recheckable proof-nodes (kernel)

Implemented in [ecCoreGoal.mli](../ecCoreGoal.mli) / `.ml`:

- `type rule = ..` — an **open** (extensible) variant. Each migrated tactic adds
  one constructor carrying its params, e.g.
  `type EcCoreGoal.rule += RHoareSeq of codegap1 * ss_inv`.
- `VRule of rule * handle list` — a new `validation` node, the recheckable
  sibling of `VExtern`.
- `FApi.xrule1 tc r subgoals` — like `xmutate1` but emits `VRule (r, _)`.
  (`xrule`, `xrule_hyps`, `xrule1_hyps` for the other arities.)
- `register_rule_checker : (rule -> rule_checker option) -> unit` — a registry of
  partial handlers over the open type. Each tactic registers a handler that
  matches its constructor (capturing the params) and returns `None` otherwise.
  This is what lets the kernel dispatch to a phl-layer checker without knowing
  the constructor — no GADT-opacity, no upward type dependency.
- `recheck_proofenv : proofenv -> unit` — the **driver**: iterates the flat goal
  map `pr_goals`; for each `VRule (r, hds)` it finds the checker, resolves the
  subgoal handles to their pregoals, and runs the checker. Non-`VRule`
  validations are trusted; `VRule` nodes with no registered checker (unmigrated)
  are skipped — this is what makes migration incremental.
- `exception RecheckFailure of string`.

The driver runs at `qed` in [ecScope.save_r](../ecScope.ml), gated by the
**`EC_RECHECK`** environment variable, so normal runs pay nothing and
`EC_RECHECK=1` re-validates every migrated node of every proof.

### Known limitation (current state)

The driver re-validates each node *locally* (the recorded subgoals are the ones
the builder yields for that goal). It does **not** yet check graph connectivity
(that a node's subgoal handles are the goals other nodes discharge) nor re-run
the trusted non-`VRule` kernel rules. It is a per-node soundness net for TCB
tactics, not yet a standalone independent proof-checker — that comes once enough
rules carry their params.

## 5. Directory layout — by family, then logic

`(include_subdirs unqualified)` in [src/dune](../dune) slurps everything under
`src/` into one flat-namespace library, so subdirectories are **purely
organizational** — module names must stay globally unique (keep the
`Ec<Logic><Tactic>` prefix; directories are for humans, no dune changes needed).

```
src/phl/
  rules/        genuine logic rules (different subgoals per logic)
    hoare/  ehoare/  bdhoare/  equiv/  eager/
  codetx/       logic-uniform program transforms (wp, sp, inline, swap, rcond, …)
  bridge/       probabilistic / cross-logic bridges (deno, pr, byequiv, fel, upto)
  multi/        multi-logic tactics with shared machinery (conseq, trans, sym)
  ecPhl<Tactic>.ml   legacy, thin dispatchers, not-yet-migrated tactics
```

Rationale: dir-per-logic is right for *logic rules* but would **scatter** the
logic-uniform code transforms and has no home for the multi-logic tactics —
hence the family split first. Within `rules/`, file-per-(logic,tactic) because
that is the unit that pairs 1:1 with a proof-node kind + checker, and
one-file-per-logic would yield 2–3k-line modules.

## 6. Special / multi-logic tactics

`conseq` is the hard case: `t_conseq` matches goal-form × invariant-token
(`Inv_ss`/`Inv_ts`) and routes to 11 variants; `process_conseq` is ~2.5k lines.
These (and `trans`, `sym`, the deno/pr bridges) get their own `multi/` area: keep
the dispatcher generic, but still split each *logic's* rule into its own
builder+checker so the node model stays uniform. Do not force them into
`rules/<logic>/`. Migrate them **last**, once the pattern is proven on the
regular rules.

## 7. Phased plan

- **Phase 0 — scaffolding** (DONE): kernel `rule`/`VRule`/`xrule`, checker
  registry, `recheck_proofenv`, `EC_RECHECK` hook, layout dirs, this doc + README.
- **Phase 1 — pilot on `seq`** (hoare arm DONE): proves the whole spine
  end-to-end with a real rule + checker.
- **Phase 2…N — one tactic per PR**, roughly increasing difficulty:
  finish seq (ehoare / bdhoare / equiv / onesided) → skip → wp/sp (codetx pilot)
  → cond → rnd → while → call → fun → exists → … → conseq / trans / sym last.

Each PR: move the file into the new layout, split the four layers, record params
in the node + add the checker, register it. **Proofs must not change.**

### Invariants for every phase

- No proof-script changes anywhere in `theories/` or `tests/`.
- `dune build` clean; test suite green; always run `ec.exe` with `-no-eco`.
- A full `EC_RECHECK=1` pass over the stdlib raises **zero** `RecheckFailure`.

## 8. Per-tactic migration recipe

1. Create `src/phl/<family>/<logic>/ecPhl…` (or `Ec<Logic><Tactic>`) keeping a
   globally-unique module name.
2. Extract the pure core `<logic>_<tac>_subgoals : LDecl.hyps -> … -> form list`
   from the existing `t_*_r` (everything up to the `xmutate1` call, returning the
   `form list`; take `hyps` and derive `env = LDecl.toenv hyps` inside).
3. Add `type EcCoreGoal.rule += R<Logic><Tac> of <params>`.
4. Rewrite the rule to
   `FApi.xrule1 tc (R… params) (… _subgoals (FApi.tc1_hyps tc) …)`.
5. Register the checker with `EcPhlRecheck.checker_of "<logic>-<tac>" pf_as_<logic>
   (fun hyps j -> <logic>_<tac>_subgoals hyps j params)` — no per-rule comparison
   code.
6. Write/move `process_<logic>_<tac>` (the typing), and have the tactic's
   `process_<tactic>` dispatcher route the relevant logic arm to it.
7. Re-export the moved `t_*`/`process_*` from the old module if its `.mli` or
   external callers still reference them (avoids touching unrelated files).
8. Build; run the tactic's tests with `EC_RECHECK=1`; add a negative test once
   (temporarily break the checker) to confirm it actually fires.

## 9. Status

Landed (this branch): Phase 0 + hoare-`seq`. Reference module:
[rules/hoare/ecHoareSeq.ml](rules/hoare/ecHoareSeq.ml). Validated: 91 stdlib
theories + 23 seq-using test files compile under `EC_RECHECK=1` with zero
`RecheckFailure`; negative test confirmed the checker fires only under
`EC_RECHECK`, at `qed`.
