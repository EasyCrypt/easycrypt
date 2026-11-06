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
6. **Rules do implicit seq-ing and framing.** Many TCB rules act on a larger
   program than the statement they are about: `rnd` and `call` take
   `c; i` and keep the prefix `c` (an implicit `seq`), and `call`, `while`,
   `rcond`, … generalize their conditions over the modified variables (an
   implicit frame, `generalize_mod`). Each rule thus re-implements, slightly
   differently, the side conditions of `seq` and of the frame rule; this has
   been a recurring source of soundness bugs.

## 2. Findings about the current engine (so the plan is grounded)

- **TCB boundary** is `FApi.xmutate / close` ([ecCoreGoal.ml](../ecCoreGoal.ml)).
  A node is `VExtern : 'a * handle list` — a GADT existential, so a generic
  traversal cannot even inspect the tag.
- **Dispatch wiring**: `process1_phl` in [ecHiTacticals.ml](../ecHiTacticals.ml)
  maps each `EcParsetree` tactic constructor (`Pseq`, `Pwhile`, …) to a
  `process_*` function.
- **Goal classification** lives in `ecCoreFol` (`is_hoareS`/`destr_hoareS`/…) and
  `ecLowPhlGoal` (`tc1_as_hoareS`/`pf_as_hoareS`/…).
- **Three tactic families**:
  - *logic rules* — genuinely different subgoals per logic: seq, while, call,
    cond, rnd, wp, sp, conseq, fun, exists.
  - *program transformations* — replace the program by an equivalent one and
    keep the **same** judgement; logic enters only as "grab the stmt+memory",
    so the core is shared across logics: rndsem, inline, swap, rcond,
    fission/fusion/unroll/splitwhile, kill/alias/cfold, outline, rwequiv.
    They are expressed as one transformation rule per logic plus a catalogue
    of transformations (§7f).
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
its own module, [`ecPlRecheck.ml`](ecPlRecheck.ml): `recheck_forms` (arity +
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
  `type EcCoreGoal.rule += RHoareSeq of hoare_seq_node`.
- `VRule of rule * handle list` — a new `validation` node, the recheckable
  sibling of `VExtern`.
- `FApi.xrule1 tc r subgoals` — like `xmutate1` but emits `VRule (r, _)`.
  (`xrule`, `xrule_hyps`, `xrule1_hyps` for the other arities.)
- `register_rule_checker : (rule -> rule_checker option) -> unit` — a registry of
  partial handlers over the open type. Each tactic registers a handler that
  matches its constructor (capturing the params) and returns `None` otherwise.
  This is what lets the kernel dispatch to a program-logic checker without knowing
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

## 5. Directory layout — by logic, plus the shared computations

`(include_subdirs unqualified)` in [src/dune](../dune) slurps everything under
`src/` into one flat-namespace library, so subdirectories are **purely
organizational** — module names must stay globally unique (keep the
`Ec<Logic><Rule>` prefix; directories are for humans, no dune changes needed).

```
src/phl/
  rules/
    hoare/  ehoare/  bdhoare/  equiv/  eager/
                Ec<Logic><Rule>: one module per (logic, rule) — its records,
                node, pure builder, checker, derived forms, elaboration
    transforms/ EcTr<Name>: the catalogue entries of the program
                transformations (§7f)
    ecPl*.ml    logic-agnostic computations shared by the rules of every
                logic: EcPlFrame (framing conditions), EcPlSp (strongest
                postcondition), EcPlWp (weakest precondition), EcPlRndSem
                (semantic sampling), EcPlRCond (deciding a conditional or
                a match), EcPlTransform (the transformation catalogue and
                its obligations), EcPlMatch (branches of a `match` on
                fresh program variables), EcPlFun (unfolding a procedure,
                the oracle conditions of the abstract-procedure rules,
                the single-call statement of `proc*`), EcPlCall (the
                result assignment and argument substitution of a call),
                EcPlWeakMem (restricting a memory weakened by fresh local
                variables)
  ecPlRecheck.ml     checker scaffolding
  ecPhl<Tactic>.ml   legacy: thin dispatchers and adapters, not-yet-migrated
                     tactics
```

Every rule lives in the directory of its logic, including the ones that are
uniform across logics or relate several judgements:

- `wp` and `sp` are logic rules on an explicit suffix / prefix
  (`EcHoareWp`, `EcEquivSp`, …), the shared computation being in
  `EcPlWp` / `EcPlSp`;
- `sym` and `trans` are equiv-only rules, in `rules/equiv/`;
- the `proc` rules are logic rules in `rules/<logic>/`: `Ec<Logic>FunDef`
  (a concrete procedure, by its body), `Ec<Logic>FunAbs` (an abstract
  procedure with an invariant, stated on `[f : I ==> I]`, `proc I` being
  the consequence rule then the rule), `EcEquivFunAbsUpto` (the abstract
  upto rule) and `Ec<Logic>FunToCode` (`proc*`, also `EcEagerFunToCode`
  in `rules/eager/`);
- the `call` rules are logic rules in `rules/<logic>/` (`Ec<Logic>Call`),
  stated on the call alone (`lv <@ f(a)`; `lv <@ f(a) ~ skip` for the
  one-sided equiv rule), with the specification of the procedure as
  premise and the weakest precondition of the call as precondition;
  `call` is derived (`seq`, then the rule); the bdhoare rule keeps its
  statement on `c; lv <@ f(a)` (implicit seq and framing: the bdhoare
  `seq` rule has extra premises);
- the `weakmem` rules (`Ec<Logic>WeakMem`; equiv: one side at a time)
  weaken the memory of a judgement on a statement by fresh local
  variables it does not mention (the shared computation in
  `EcPlWeakMem`); the `weakmem` tactic is derived: a cut of the weakened
  hypothesis, closed by the rule and the hypothesis;
- a rule relating judgements of two logics (the `pr` bridges, `hoare` from
  `phoare`, …) lives with the logic of its conclusion;
- a rule concluding a statement on probabilities from a judgement
  (`byphoare`, `byehoare`, `byequiv`) lives with the logic of that
  judgement (`EcBdHoareDeno`, `EcEHoareDeno`, `EcEquivDeno`);
- the failure-event lemma (`fel`, `EcBdHoareFel`), whose conclusion is a
  probability bound and whose oracle premises are phoare bounds, lives in
  `rules/bdhoare/`; it is stated on the whole procedure body (an implicit
  seq at the end of the initialization, there being no seq rule on
  probabilities);
- the upto rule (`EcEquivUpto`, `byupto`), whose conclusion is an
  equality of probabilities of two procedures, is relational and lives in
  `rules/equiv/`; the forms of `byupto` other than `Pr[_] = Pr[_]` are
  derived (a lemma of the real theory, the rule and `rewrite Pr`);
- the facts on probabilities of `rewrite Pr` (`EcBdHoarePrFact`, an
  axiom schema without premise: `mu_eq`, `mu_sub`, `mu_split`, `muE`,
  …; the node records the schema and its resolved parameters, binders
  included, and the checker regenerates the fact and compares it with
  the goal) are statements on the probability of an event of one
  procedure, the object of the phoare logic: they live in
  `rules/bdhoare/`; `rewrite Pr` is derived (a rewriting with the cut
  fact, closed by the rule), and `byupto` / `byequiv` use it;
- program transformations go through the transformation rule of each logic
  (`Ec<Logic>Transform`); only their catalogue entries live in
  `rules/transforms/`.

Within `rules/`, file-per-(logic,rule) because that is the unit that pairs 1:1
with a proof-node kind + checker, and one-file-per-logic would yield 2–3k-line
modules.

## 6. Special / multi-logic tactics

`conseq` is the hard case: `t_conseq` matches goal-form × invariant-token
(`Inv_ss`/`Inv_ts`) and routes to 11 variants; `process_conseq` is ~2.5k lines.
Keep its dispatcher generic, but still split each *logic's* rule into its own
builder+checker (in `rules/<logic>/`) so the node model stays uniform. Migrate
it **last**, once the pattern is proven on the regular rules.

## 7. Phased plan

- **Basis** — kernel `rule`/`VRule`/`xrule`, checker registry,
  `recheck_proofenv`, `EC_RECHECK` hook, `EcPlRecheck`, layout, this doc +
  README. No rule uses it yet.
- **Then one PR per tactic class**, all of its logics at once, roughly by
  increasing difficulty: seq (the reference, proving the whole spine
  end-to-end with real rules + checkers) → frame (the frame rule of §7d,
  which every other rule relies on) → skip → wp/sp → cond
  → rnd → while → call → fun → exists → … → the rest of conseq / trans / sym
  last.

Each PR: move the code into the new layout, split the four layers, record params
in the node + add the checker, register it. **Proofs must not change.**

### Invariants for every phase

- No change to any existing proof script in `theories/`, `tests/` or
  `examples/` (new tests exercising a migrated rule are welcome).
- `dune build` clean; test suite green; always run `ec.exe` with `-no-eco`.
- A full `EC_RECHECK=1` pass over the stdlib raises **zero** `RecheckFailure`.

## 7b. Parameters travel as records, not tuples

Two records make each tactic self-documenting (fields show up in the `.mli`):

- **Parse input** — *lives in the parsetree*, not in `src/phl`. The tactic's
  `EcParsetree` info type is a record with named, prefixed fields (e.g.
  `seq_info = { seqi_side; seqi_at; seqi_mid; seqi_bd }`), built in the grammar.
  We do **not** mirror it with a copy on the program-logic side — the parse info *is* the
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

## 7d. No implicit seq-ing, no implicit framing

A TCB rule is stated on **exactly the statement it governs**:

- **No implicit seq-ing.** The `rnd` rule is about `x <$ d`, the `call` rule
  about `x <- f(a)`, the `if` rule about `if b then c1 else c2` — never about
  `c; x <$ d`. Splitting a program is done by the `seq` rule, and only by it.
- **No implicit framing.** A rule does not generalize its conditions over the
  variables written by the program. Framing is done by a single *frame* rule
  per logic — a framed weakening of the postcondition — and only by it:

  ```
       forall &m, P => forall (mod c), Q' => Q      hoare [c : P ==> Q']
      -------------------------------------------------------------------
                            hoare [c : P ==> Q]
  ```

  The framed consequence (also strengthening the precondition) is derived:
  the frame rule followed by the consequence rule.

Surface tactics that act on a larger program (`rnd` on the last instruction,
`call`, `while`, …) are **derived**: they compose `seq` (at the position they
act on, with the intermediate assertion they compute today), the frame rule (or
the framed consequence), and the single-statement rule, and close the premises
they always closed. The user-visible subgoals are therefore unchanged, while
the TCB shrinks to small single-statement rules plus `seq` and the frame rules,
each with its own checker.

## 7e. Each rule is documented, in the `.mli`, as an inference rule

The `.mli` of a rule module has three sections, in this order:

- **Rules (trusted).** Each TCB rule as an inference rule — premises above the
  line, conclusion below, side conditions next to it — followed by the node it
  records and the name of its checker. For instance:

  ```
  (* [t_hoare_seq { hsr_at = k; hsr_mid = R }]

         hoare [c1 : P ==> R]      hoare [c2 : R ==> Q]
       ------------------------------------------------  c = c1; c2
                    hoare [c : P ==> Q]                   (c1 = c[0..k))

     Node: RHoareSeq { hsn_at = k (resolved); hsn_mid = R }.
     Checker: "hoare-seq". *)
  ```

- **Derived tactics.** Each derived tactic, with the rules it expands to and
  the premises it closes itself.
- **Elaboration.** The `process_*` entry points, described as surface syntax.

So what is trusted, which rule is applied, and what is derived is readable
from the interface alone.

## 7f. Program transformations: one rule per logic, a catalogue of transformations

A program transformation replaces the program of a judgement by an equivalent
one and keeps the judgement. Instead of one trusted rule per (logic,
transformation), each logic has **one** trusted transformation rule,
parameterized by an entry of a **catalogue** of transformations:

```
   J [c' : P ==> Q]        O_1 … O_n      (c', [O_1 … O_n]) = t(c)
 ------------------------------------------------------------------
                          J [c : P ==> Q]
```

- **The catalogue** ([`rules/ecPlTransform.ml`](rules/ecPlTransform.mli)): an
  open type `transform`, each entry adding a constructor that carries its
  **resolved** parameters (§7c) and registering the function computing it
  (`EcPlTransform.register`, a registry of partial handlers like the rule
  checkers). An entry is a pure, deterministic function of a context and of
  the statement `c`; it acts at the statement level only and may extend the
  memory with fresh program variables. Its context holds the hypotheses and
  environment of the goal, the memory of `c` and what it needs from the
  judgement — so far the program variables read by the postcondition —
  computed by each logic's rule from its own judgement, so that the checker
  recomputes it from the goal (a recorded set is never trusted). `EcPlTransform.apply` runs an entry, raising
  `InvalidTransform` with a user-facing message when it does not apply.
  Entries live in `rules/transforms/`, one module `EcTr<Name>` each.
- **The obligations** are **abstract** and form a small closed set; each
  logic's rule states them as premises of its own (first, in order, then the
  transformed judgement — same pre/post, possibly extended memory). The
  kinds so far:
  - `OPrefixPost (hd, cond)`: every terminating run of the prefix `hd` from
    the precondition ends in a state satisfying `cond`. Per logic:
    - hoare: `hoare [hd : P ==> cond | E]` (the goal's exceptional
      postconditions kept);
    - ehoare: `hoare [hd : P_bool ==> cond]`, the precondition having the
      form ``P_bool `|` f``;
    - bdhoare: `hoare [hd : P ==> cond]`;
    - equiv (transformation of side `i`): `forall &j, hoare [hd : P ==>
      cond]`, the relation read on side `i` with the other memory
      quantified.

    These are the premises `rcondt` / `rcondf` have always stated.
  - `OLossless ks`: the statement `ks` terminates with probability 1 from
    every state; in every logic `phoare [ks : true ==> true] = 1`, in the
    memory of the transformed program (the premise `kill` has always
    stated).
  - `OExprEq (xs, e, e')`: in every memory of the transformed program's
    type and for every value of the local identifiers `xs`, `e` and `e'`
    evaluate to the same value; in every logic `forall &m, forall xs, e =
    e'`, `&m` named after the program's memory (the premises `proc
    rewrite` has always stated, one per rewritten expression).
  - `OLocalEquiv (xs, s, s', R, W, M)`: for every value of the match-arm
    locals `xs` in scope, from states agreeing on `R` (and satisfying, on
    the side of `s`, the frame), the fragment `s` of the program and the
    new fragment `s'` end in states agreeing on `W`; in every logic
    `forall xs, equiv [s ~ s' : ={R} /\ F{1} ==> ={W}]`, left memory
    type that of the program, right that of the transformed program (the
    premise `proc change` has always stated). The frame `F` is the
    obligation depending on the precondition: it is computed by each
    rule from its own precondition (`EcPlTransform.frame`), as the
    top-level conjuncts of the boolean precondition that only mention the
    memory of the program and are independent from `M` (what may be
    written before `s` runs):
    - hoare, bdhoare: the precondition;
    - ehoare: the boolean part `P` of a precondition ``P `|` f``, no frame
      otherwise;
    - equiv (transformation of side `i`): the relational precondition,
      the conjuncts mentioning only the memory of side `i`.
- **The rules** `t_<logic>_transform` (`rules/<logic>/Ec<Logic>Transform`;
  equiv: one side at a time, the other program and memory unchanged) record
  `(transformation, resolved parameters)` (and the side) in their node. The
  checker ("<logic>-transform") re-runs the transformation on the goal's own
  program and compares the rebuilt subgoals with the recorded ones through
  `EcPlRecheck.checker_of`: programs are thus compared up to alpha-equivalence
  (the fresh binders an entry introduces may differ from run to run).
- **The tactics** using a transformation are derived: they resolve their
  arguments, check what they always checked (to keep their error messages),
  and apply the transformation rule.

Current catalogue:
- `rndsem` (`EcTrRndSem`, semantic sampling of a straight-line suffix,
  computed by `EcPlRndSem`; no obligation), used by the `rndsem` tactic in
  hoare, bdhoare and equiv;
- `rcond` (`EcTrRCond`, deciding the `if` / `while` at a position; obligation
  `OPrefixPost (hd, b)` or `OPrefixPost (hd, !b)`), used by `rcondt` /
  `rcondf` in every logic;
- `rmatch` (`EcTrRMatch`, deciding the `match` at a position, the arguments
  of the constructor being assigned to fresh program variables; obligation
  `OPrefixPost (hd, exists xs, e = C xs)`), used by `match C k` in every
  logic (its unframed form, see below);
- `if-push` (`EcTrIfPush`): `if b then c1 else c2; c` becomes the single
  instruction `if b then { c1; c } else { c2; c }`; no obligation;
- `match-push` (`EcTrMatchPush`): `match e with C xs => b ...; c` becomes
  the single instruction `match e with C xs => { b; c } ...`; no
  obligation. The pattern variables are local identifiers bound in the
  branch only: the binders of a branch are renamed apart when they occur
  free in `c`, so that `c` is not captured;
- `swap` (`EcTrSwap`, moving the block `[s..f)` of the possibly nested block
  at a resolved path to a gap `t` outside it; the independence of the
  exchanged statements and the absence of `raise` are checked by the entry;
  no obligation, same memory), used by `swap` (and `interleave`, a sequence
  of swaps) in every logic;
- `inline` (`EcTrInline`, inlining the calls selected by a resolved pattern
  of integer offsets, possibly nested in the branches of an `if`, `while` or
  `match`: arguments assigned to fresh copies of the parameters, body with
  parameters and locals renamed to fresh program variables added to the
  memory, result assigned (component-wise through fresh variables for a
  tuple pattern without `tuple`); no obligation), used by `inline` in every
  logic;
- `kill` (`EcTrKill`): removes the `n` instructions `ks` at a (possibly
  nested) position, provided that what they write is read neither by the
  code that may run after them (in their block and the enclosing ones, and
  the guard and whole body of each enclosing loop) nor by the postcondition
  (for hoare, including the exceptional ones); obligation `OLossless ks`;
- `alias` (`EcTrAlias`): `lv <- e` / `lv <$ d` / `lv <@ f(a)` becomes
  `x' <- e; lv <- x'` (resp. `<$`, `<@`), `x'` a fresh program variable;
  no obligation;
- `set` (`EcTrSet`): inserts `x' <- e` at a position, `x'` fresh; no
  obligation;
- `set-match` (`EcTrSetMatch`): names the subterm `t` matched in the
  expression of an instruction, `x' <- t; i(e[occ := x'])`, the selected
  occurrences being alpha-equivalent to `t`; no obligation;
- `cfold` (`EcTrCFold`): propagates an assignment to local variables into
  the following instructions as long as valid (eager or not), and
  materializes it afterwards; no obligation;
- `asgn-case` (`EcTrAsgnCase`): splits a tuple assignment into one
  assignment per variable (`case <-`); no obligation;
- `simplify-if` (`EcTrSimplifyIf`): turns a conditional whose branches are
  assignments into a single assignment (`simplify if`); no obligation;
- `fission` (`EcTrFission`, splitting the loop at a — possibly nested —
  position in two loops at two offsets of its body, its prelude of `n`
  instructions duplicated; read / write independence, determinism and
  `raise`-freedom side conditions; no obligation), used by `fission` in
  every logic;
- `fusion` (`EcTrFusion`, the inverse: merging two consecutive loops with
  equal preludes, conditions and epilogs, under the side conditions of
  `fission`; no obligation), used by `fusion` in every logic;
- `unroll` (`EcTrUnroll`): `while e do c` becomes
  `if e then c; while e do c`; no obligation; used by `unroll` (`unroll
  for` stays derived: rcond, wp, seq, conseq, cfold);
- `splitwhile` (`EcTrSplitWhile`): `while e do c` becomes
  `while (e /\ b) do c; while e do c`; no obligation; used by
  `splitwhile`;
- `expr-change` (`EcTrExprChange`): replaces expressions of a — possibly
  nested — range (or of the whole statement), enumerated in program
  order, each replacement being stated over identifiers recorded for the
  match-arm locals in scope (renamed back in the program, with
  type and capture side conditions); obligation `OExprEq` per replaced
  expression; used by `proc rewrite` and `proc rewrite /=` in every
  logic, which discharge the obligations on the spot;
- `stmt-change` (`EcTrStmtChange`): replaces a — possibly nested — range
  by a statement over the memory extended with fresh locals (bound by the
  entry with `EcMemory.bindall_fresh`, deterministically); obligation
  `OLocalEquiv` between the two fragments, on the variables read by both
  and the written variables observable afterwards (by the code that may
  run after the range, the postcondition, and, in a loop, the fragments
  themselves); used by `proc change` in every logic;
- `circuit-change` (`EcTrCircuitChange`): replaces the `n` instructions
  at a — possibly nested — position by a statement over fresh locals,
  provided that they are circuit-equivalent (`EcCircuits.instrs_equiv`,
  run by the entry, under the context's hypotheses) on the variables
  observable afterwards; assignments to local variables only, hence no
  `raise` (the entry is sound with exceptional postconditions, whose
  variables are observable); no obligation; used by `proc change
  circuit` (hoare only);
- `idassign` (`EcTrIdAssign`): inserts `x <- x` at a — possibly nested —
  position; no obligation; used by `idassign` (hoare only).

The decisions of a conditional or a match are computed by `EcPlRCond`.
The `if` and `match` tactics are push + rule on the conditional alone: they
push the continuation into the branches (when there is one) through the
transformation rule (on each side, for the two-sided equiv forms), then
apply the `if` / `match` rule of their logic (`Ec<Logic>If`,
`Ec<Logic>Match`), stated on the conditional alone. Further entries come
with the tactics that use them.

Exception: the framed form of `match C k` (used when the variables of the
discriminant `e` are neither read nor written by the prefix, and the
judgement ignores the initial memories in which the prefix does not
terminate: hoare, ehoare, phoare `<=`, or an empty prefix) adds `e = C ys`
to the precondition instead of assigning `ys` in the program. It changes
the precondition, so it is not a program transformation in this sense and
stays a separate trusted rule of each logic, `t_<logic>_rmatch_framed`
(`Ec<Logic>RMatch`, checker "<logic>-rmatch-framed"), stated on the whole
statement (to be rediscussed). The `match C k` tactic of each logic is
derived: it applies that rule when the framing condition holds, the
`rmatch` transformation otherwise.

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
   to a record (§7b) at the same time. Do not wrap the rule in
   `FApi.t_low0..4`: they ignore their name argument and are the identity, so
   drop them from each tactic as it is ported.
5. Register the checker with `EcPlRecheck.checker_of "<logic>-<tac>" pf_as_<logic>
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
8. Remove implicit seq-ing and framing (§7d): restate the rule on the single
   statement it governs, and make the surface tactic a derived composition of
   `seq`, the frame rule (or the framed consequence) and that rule, producing
   the same subgoals as before.
9. Document the module's `.mli` as in §7e.
10. Build; run the tactic's tests with `EC_RECHECK=1`; add a negative test once
    (temporarily break the checker) to confirm it actually fires.
