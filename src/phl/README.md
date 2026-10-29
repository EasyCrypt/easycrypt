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

Key rule: the rule and its checker share one **pure low-level subgoal-builder**
(`<logic>_<tac>_subgoals : <judgement> -> <node> -> form list`), operating on the
node's *resolved* parameters (e.g. an integer split index, not a symbolic code
gap). The checker is then "rerun the builder and compare", which is why recording
the resolved params in the node is all that recheckability costs. Resolution
(code positions, typing, …) happens once in the rule, **before** the core, so it
stays out of the checker's trust boundary — see REFACTORING §7c.

The comparison boilerplate is shared in [`ecPlRecheck.ml`](ecPlRecheck.ml):
`EcPlRecheck.checker_of name destr build` turns a judgement reader (`pf_as_*`)
and a builder into a `rule_checker`, and wraps any exception raised while
rebuilding into a `RecheckFailure`. A checker is then just its registration:

```ocaml
let () = register_rule_checker (function
  | R<Logic><Tac> node ->
      Some (EcPlRecheck.checker_of "<logic>-<tac>" pf_as_<logic>
              (fun _hyps j -> <logic>_<tac>_subgoals j node))
  | _ -> None)
```

Derived (non-TCB) tactics that only orchestrate other tactics emit **no** node
and need **no** checker — rechecking recurses into the rules they expand to.

## Trusted rules

- A TCB rule is stated on exactly the statement it governs: **no implicit
  seq-ing** (splitting is the `seq` rule's job) and **no implicit framing**
  (generalizing over modified variables is the frame rule's job). Surface
  tactics acting on a larger program are derived compositions of these.
- Each rule module's `.mli` documents its TCB rules as inference rules (with
  their node and checker), then its derived tactics (with what they expand to),
  then its elaboration entry points.

See `REFACTORING.md` §7d–§7e.

## Recheckable proof-nodes

The kernel ([`ecCoreGoal`](../ecCoreGoal.mli)) provides:

- `type rule = ..` — an open type. Each migrated tactic adds one constructor,
  e.g. `type EcCoreGoal.rule += RHoareSeq of hoare_seq_node`.
- `FApi.xrule1 tc r subgoals` — like `xmutate1` but emits a recheckable
  `VRule (r, _)` node instead of an opaque `VExtern`.
- `register_rule_checker : (rule -> rule_checker option) -> unit` — register a
  partial handler that, for your constructor, returns its checker.
- `recheck_proofenv` — walks a finished proof and runs every registered checker.
  It is invoked at `qed` time when the `EC_RECHECK` environment variable is set
  (see `ecScope.save_r`); unmigrated `VExtern` nodes are skipped.

Run the test suite with `EC_RECHECK=1` to exercise every migrated checker.

## Program transformations

Tactics that replace the program by an equivalent one and keep the judgement
(rndsem, rcond, swap, inline, proc rewrite / change, …) go through **one** trusted
transformation rule per logic, `t_<logic>_transform` (`Ec<Logic>Transform`;
equiv: one side at a time), parameterized by an entry of a catalogue:

```
   J [c' : P ==> Q]        O_1 … O_n      (c', [O_1 … O_n]) = t(c)
 ------------------------------------------------------------------
                          J [c : P ==> Q]
```

- The catalogue ([`EcPlTransform`](rules/ecPlTransform.mli)) is an open type
  `transform` plus a registry; each entry (`rules/transforms/EcTr<Name>`)
  carries resolved parameters and is a pure, deterministic, statement-level
  function, which may extend the memory with fresh program variables.
- The obligations are abstract (a small closed set: so far, "every
  terminating run of the prefix `hd` from the precondition satisfies
  `cond`", "the statement `ks` is lossless", "the expressions `e` and
  `e'` are equal in every memory" and "the fragments `s` and `s'` are
  locally equivalent", the latter's frame being computed by each rule
  from its own precondition); each logic's rule states them as its own
  premises (see its `.mli`).
- The node records the transformation and its parameters; the checker
  ("<logic>-transform") re-runs it on the goal's program and compares the
  subgoals up to conversion (programs up to alpha-equivalence).

Current catalogue: `rndsem` (`EcTrRndSem`), `rcond` (`EcTrRCond`),
`rmatch` (`EcTrRMatch`), `if-push` (`EcTrIfPush`), `match-push`
(`EcTrMatchPush`), `swap` (`EcTrSwap`), `inline` (`EcTrInline`), `kill`
(`EcTrKill`), `alias` (`EcTrAlias`), `set` (`EcTrSet`), `set-match`
(`EcTrSetMatch`), `cfold` (`EcTrCFold`), `asgn-case` (`EcTrAsgnCase`),
`simplify-if` (`EcTrSimplifyIf`), and the loop transformations `fission`
(`EcTrFission`), `fusion` (`EcTrFusion`), `unroll` (`EcTrUnroll`) and
`splitwhile` (`EcTrSplitWhile`), and the program rewritings
`expr-change` (`EcTrExprChange`, `proc rewrite`), `stmt-change`
(`EcTrStmtChange`, `proc change`), `circuit-change`
(`EcTrCircuitChange`, `proc change circuit`) and `idassign`
(`EcTrIdAssign`). `if-push` / `match-push` push
the continuation of a leading conditional / `match` into its branches: the
`if` and `match` tactics are push + rule on the conditional alone
(`Ec<Logic>If`, `Ec<Logic>Match`).
Further entries come with the tactics that use them. The framed form of
`match C k` changes the precondition: it stays a separate trusted rule of
each logic, `t_<logic>_rmatch_framed` (`Ec<Logic>RMatch`). See
`REFACTORING.md` §7f.

## Directory layout

`(include_subdirs unqualified)` in `src/dune` slurps everything under `src/`
into one flat-namespace library, so subdirectories are purely organizational —
**module names must stay globally unique** (keep the `Ec<Logic><Rule>` prefix;
directories are for humans).

```
src/phl/
  rules/
    hoare/  ehoare/  bdhoare/  equiv/  eager/
                Ec<Logic><Rule>: one module per (logic, rule)
    transforms/ EcTr<Name>: catalogue entries of the program transformations
    ecPl*.ml    computations shared by the rules of every logic: EcPlFrame,
                EcPlSp, EcPlWp, EcPlRndSem, EcPlRCond, EcPlTransform,
                EcPlMatch, EcPlFun, EcPlCall
  ecPlRecheck.ml     checker scaffolding
  ecPhl<Tactic>.ml   legacy: thin dispatchers and adapters, not-yet-migrated
                     tactics
```

- `wp` and `sp` are logic rules on an explicit suffix / prefix, in
  `rules/<logic>/` (the shared computation in `EcPlWp` / `EcPlSp`).
- `sym` and `trans` are equiv-only rules, in `rules/equiv/`.
- The `proc` rules (`Ec<Logic>FunDef`, `Ec<Logic>FunAbs`,
  `EcEquivFunAbsUpto`, `Ec<Logic>FunToCode`, `EcEagerFunToCode`) are
  logic rules in `rules/<logic>/`; `proc I` is derived (consequence + rule).
- The `call` rules (`Ec<Logic>Call`) are logic rules on the call alone;
  `call` is derived (`seq` + rule), except in bdhoare, whose rule keeps its
  composite statement on `c; x <@ f(a)`.
- A rule relating two logics (e.g. the `pr` bridges) lives with the logic of
  its conclusion.
- A rule concluding a probability statement from a judgement (`byphoare`,
  `byehoare`, `byequiv`: `Ec<Logic>Deno`) lives with the logic of that
  judgement.
- The failure-event lemma (`fel`, `EcBdHoareFel`) concludes a probability
  bound from phoare premises; it lives in `rules/bdhoare/`.
- The upto rule of `byupto` (`EcEquivUpto`, a premise-free rule concluding
  `Pr[f1 : E /\ !bad] = Pr[f2 : E /\ !bad]` for procedures equal up to
  `bad`) is relational: it lives in `rules/equiv/`.
- The facts on probabilities of `rewrite Pr` (`EcBdHoarePrFact`, a
  premise-free axiom schema on the probabilities of one procedure) live
  in `rules/bdhoare/`; `rewrite Pr` itself is derived.
- Program transformations use the transformation rule of each logic; only
  their catalogue entries live in `rules/transforms/`.
