# Program-logic tactics (`src/phl`)

This directory is being reorganized around a uniform, recheckable structure.
This note records the target layout and the per-tactic spine. It is being
applied **one tactic at a time**; until a tactic is migrated it keeps its old
shape (one `ecPhl<Tactic>.ml` holding every logic).

## The four-layer spine

Every tactic is decomposed into the same layers, so that typing, dispatch and
the trusted core are separated and each TCB step is re-checkable:

```
DISPATCH      process_<tactic>        logic-agnostic. Inspects the goal kind and
   │                                  routes. The ONLY place is_hoareS / f_node
   │                                  matching belongs. No typing here.
   ▼
ELABORATION   process_<logic>_<tac>   the goal kind is known. Type the parse-tree
   │                                  arguments in that logic's memory and build
   │                                  the typed rule parameters, then call the rule.
   ▼
RULE (TCB)    t_<logic>_<tac>         compute the subgoals from the typed params
   │                                  and emit a recheckable node carrying THOSE
   │                                  params: FApi.xrule1 tc (R... params) subgoals.
   ▼
CHECKER       check_<logic>_<tac>     read the params back from the node, recompute
                                      the subgoals via the SAME pure core, and
                                      confirm they match (is_conv) what was stored.
```

Key rule: the rule and its checker share one **pure subgoal-builder**
(`<logic>_<tac>_subgoals : LDecl.hyps -> <judgement> -> params -> form list`).
The checker is then "rerun the builder and compare", which is why recording the
params in the node is all that recheckability costs. The builder is handed the
goal's `hyps` (the authoritative context; its environment is `LDecl.toenv` of
them), so the rule and checker reason in exactly the same context.

The comparison boilerplate is shared in [`ecPhlRecheck.ml`](ecPhlRecheck.ml):
`EcPhlRecheck.checker_of name destr build` turns a judgement reader (`pf_as_*`)
and a builder into a `rule_checker`, and wraps any exception raised while
rebuilding into a `RecheckFailure`. A checker is then just its registration:

```ocaml
let () = register_rule_checker (function
  | R<Logic><Tac> params ->
      Some (EcPhlRecheck.checker_of "<logic>-<tac>" pf_as_<logic>
              (fun hyps j -> <logic>_<tac>_subgoals hyps j params))
  | _ -> None)
```

Derived (non-TCB) tactics that only orchestrate other tactics emit **no** node
and need **no** checker — rechecking recurses into the rules they expand to.

## Recheckable proof-nodes

The kernel ([`ecCoreGoal`](../ecCoreGoal.mli)) provides:

- `type rule = ..` — an open type. Each migrated tactic adds one constructor,
  e.g. `type EcCoreGoal.rule += RHoareSeq of codegap1 * ss_inv`.
- `FApi.xrule1 tc r subgoals` — like `xmutate1` but emits a recheckable
  `VRule (r, _)` node instead of an opaque `VExtern`.
- `register_rule_checker : (rule -> rule_checker option) -> unit` — register a
  partial handler that, for your constructor, returns its checker.
- `recheck_proofenv` — walks a finished proof and runs every registered checker.
  It is invoked at `qed` time when the `EC_RECHECK` environment variable is set
  (see `ecScope.save_r`); unmigrated `VExtern` nodes are skipped.

Run the test suite with `EC_RECHECK=1` to exercise every migrated checker.

## Directory layout

`(include_subdirs unqualified)` in `src/dune` slurps everything under `src/`
into one flat-namespace library, so subdirectories are purely organizational —
**module names must stay globally unique** (keep the `Ec<Logic><Tactic>` prefix;
directories are for humans).

```
src/phl/
  rules/        genuine logic rules (different subgoals per logic)
    hoare/  ehoare/  bdhoare/  equiv/  eager/
  codetx/       logic-uniform program transforms (wp, sp, inline, swap, rcond, …)
  bridge/       probabilistic / cross-logic bridges (deno, pr, byequiv, fel, upto)
  multi/        multi-logic tactics with shared machinery (conseq, trans, sym)
  ecPhl<Tactic>.ml   legacy, thin dispatchers, not-yet-migrated tactics
```

## Migrated so far

- **hoare `seq`** — [`rules/hoare/ecHoareSeq.ml`](rules/hoare/ecHoareSeq.ml).
  The reference example of the full spine + checker. `EcPhlSeq.process_seq`
  dispatches its `hoareS` arm here. The canonical rule `EcHoareSeq.t_hoare_seq`
  takes a `hoare_seq_rule` record; the legacy `EcPhlSeq.t_hoare_seq` keeps its
  positional `.mli` and adapts onto it, so existing callers are unchanged.
