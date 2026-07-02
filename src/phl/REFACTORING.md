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

## 7b. Parameters travel as records, not tuples

Two records make each tactic self-documenting (fields show up in the `.mli`):

- **Parse input** — *lives in the parsetree*, not in `src/phl`. The tactic's
  `EcParsetree` info type is a record with named, prefixed fields (e.g.
  `seq_info = { seqi_side; seqi_at; seqi_mid; seqi_bd }`), built in the grammar.
  We do **not** mirror it with a phl-side copy — the parse info *is* the
  parsetree node. The dispatcher `process_<tactic>` routes purely on the goal
  kind and forwards the **whole record** to the per-logic
  `process_<logic>_<tac>`, which takes that same record and owns its
  surface-syntax validation (single vs double, side allowed, bound allowed, …).
  So `process_*` are never positional.
- **Rule arguments** — a record defined in the migrated `rules/*` module (e.g.
  `hoare_seq_rule = { hsr_at; hsr_mid }`, high level: the position is still a
  symbolic `codegap1`). The **canonical rule in `rules/*` takes this record**
  (`EcHoareSeq.t_hoare_seq : hoare_seq_rule -> backward`). The **legacy positional
  entry in `phl/*` keeps its `.mli` unchanged** and is a thin adapter onto it
  (`let t_hoare_seq i phi = EcHoareSeq.(t_hoare_seq { hsr_at = i; hsr_mid = phi })`),
  so not-yet-migrated callers are untouched.
- **Node payload** — a *separate* record (e.g. `hoare_seq_node = { hsn_at; hsn_mid }`)
  carried by the proof-node constructor (`RHoareSeq of hoare_seq_node`) and
  consumed by the shared subgoal-builder. It holds the **resolved, low-level**
  parameters (see §7c): `hsn_at` is the normalized integer split index, not the
  symbolic gap.

Field names use a short per-record **prefix** (`seqi_`, `hsr_`, `hsn_`), matching
the existing EC record style (`hs_m`, `es_pr`, `bhs_bd`) and avoiding label
clashes within a module.

## 7c. The checker is post-resolution; the node records resolved data

A checker is *trusted* re-validation, so its TCB must be minimal. It must **not**
redo elaboration/resolution work the rule already did — code-position
resolution, name lookup, unification, etc. Concretely, the rule splits at a
symbolic `codegap1`, which `normalize_cgap1 env` resolves to an integer index
(`nm_codegap1`). If the node stored the `codegap1` and the checker re-resolved
it, all of code-position normalization would sit inside the checker's TCB.

Instead: the rule does the env-dependent resolution **once**
(`EcLowPhlGoal.s_split_index`), records the **resolved** value in the node, and
both the rule and the checker build subgoals through the same pure low-level
core (`hoare_seq_subgoals : sHoareS -> hoare_seq_node -> form list`), which splits
at the integer with `split_at_nmcgap1` (no env). The rule builds its subgoals via
that core too, so faithfulness is by construction: the checker reruns the exact
same function on the exact same recorded data.

Rule of thumb when migrating: **record the lowest-level value that still
determines the subgoals** (a resolved index, a typed formula, an instantiated
witness) — never the surface syntax that produced it. The high-level
`*_rule` record is the rule's *input*; the `*_node` record is what survives into
the proof and the checker.

## 8. Per-tactic migration recipe

1. Create `src/phl/<family>/<logic>/ecPhl…` (or `Ec<Logic><Tactic>`) keeping a
   globally-unique module name.
2. Define two records (prefixed fields, §7b/§7c): the high-level **rule
   arguments** `<logic>_<tac>_rule` (symbolic positions, untyped-derived data as
   supplied by callers) and the low-level **node payload** `<logic>_<tac>_node`
   (resolved indices, typed data). Extract the pure low-level core
   `<logic>_<tac>_subgoals : <judgement> -> <logic>_<tac>_node -> form list` from
   the existing `t_*_r` — everything from *after* resolution up to the `xmutate1`
   call. It should need no env (resolution already happened); if it genuinely
   needs more, pass it explicitly.
3. Add `type EcCoreGoal.rule += R<Logic><Tac> of <logic>_<tac>_node`.
4. Write the canonical rule in `rules/*` taking the rule-arguments record:
   `t_<logic>_<tac> : <logic>_<tac>_rule -> backward`. Body: do the env-dependent
   resolution (e.g. `EcLowPhlGoal.s_split_index`), build the `<…>_node`, then
   `FApi.xrule1 tc (R… n) (<…>_subgoals j n)`. Turn the legacy `phl/*` `t_*`
   (positional `.mli` unchanged) into a thin adapter that builds the rule record
   and calls it. If the tactic's `EcParsetree` info is still a tuple, convert it
   to a record (§7b) at the same time.
5. Register the checker with `EcPhlRecheck.checker_of "<logic>-<tac>" pf_as_<logic>
   (fun _hyps j -> <logic>_<tac>_subgoals j n)` — runs only the post-resolution
   core, no comparison code.
6. Write `process_<logic>_<tac> : <tactic>_info -> backward` (taking the parsetree
   record): validate the surface syntax for that logic, type the arguments, build
   the rule record and call `t_<logic>_<tac>`. In the `phl/*` dispatcher
   `process_<tactic>`, route by **pattern-matching the goal's `f_node`** —
   `| F<logic>S _ -> EcPhl…process_<logic>_<tac> info tc` — and drop the
   corresponding legacy arm. Do not use `is_*` predicates for dispatch.
7. Keep the legacy `phl/*` `t_*` (positional adapter) so external callers and the
   module's `.mli` are untouched.
8. Build; run the tactic's tests with `EC_RECHECK=1`; add a negative test once
   (temporarily break the checker) to confirm it actually fires.

## 9. Status

Landed (this branch): Phase 0 + hoare-`seq`. Reference module:
[rules/hoare/ecHoareSeq.ml](rules/hoare/ecHoareSeq.ml). Validated: 91 stdlib
theories + 23 seq-using test files compile under `EC_RECHECK=1` with zero
`RecheckFailure`; negative test confirmed the checker fires only under
`EC_RECHECK`, at `qed`.
