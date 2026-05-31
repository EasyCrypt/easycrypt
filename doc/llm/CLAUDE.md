# EasyCrypt — LLM Agent Guide

EasyCrypt is a proof assistant for reasoning about the security of
cryptographic constructions. It provides support for probabilistic
computations, program logics (Hoare logic, probabilistic Hoare logic,
probabilistic relational Hoare logic), and ambient mathematical
reasoning.

## Using the `llm` interactive mode

The `llm` subcommand provides an interactive REPL with a
machine-friendly protocol designed for LLM agents. The LLM sends
commands over stdin and receives structured responses on stdout.

```
easycrypt llm [OPTIONS]
```

Standard loader and prover options (`-I`, `-timeout`, `-p`, etc.) are
available. Use `-help` to print this guide and exit:

```
easycrypt llm -help
```

### Protocol

**Startup.** EasyCrypt prints a `READY` message and waits for input:

```
READY [uuid:0]
<END>
```

**Responses.** Every response has a typed envelope and an `<END>`
sentinel:

```
OK [uuid:N]
<body>
<END>
```

```
ERROR [uuid:N]
<error message>
<END>
```

The `uuid` is a monotonically increasing integer identifying the proof
engine state. It increments with each successful command.

### Meta-commands

These are protocol-level commands, not EasyCrypt syntax:

| Command | Description |
|---------|-------------|
| `LOAD "file.ec" [LINE[:COL]] [-nosmt] [-trace]` | Reset state, compile file (optionally skip SMT or trace last sentence) |
| `UNDO` | Undo the last proof step |
| `REVERT <uuid-or-name>` | Revert to a specific state (by uuid or checkpoint name) |
| `GOALS` | Print the current goal (first subgoal only, with remaining count) |
| `GOALS ALL` | Print all subgoals |
| `TREE` | List open subgoals with dotted-path labels showing nesting, marking the focused one |
| `TREE ALL` | Same as `TREE`, but with full goal bodies |
| `FOCUS P` | Rotate focus to the leaf addressed by path `P` (`N` or `N1.N2.N3...`) |
| `NEXT` | Rotate focus to the next subgoal (equivalent to `FOCUS 2`) |
| `COMMIT` | Emit recorded REPL phrases as a bulleted proof body (works under `+strict_bullets`) |
| `CHECKPOINT <name>` | Save current uuid under a name for later `REVERT` |
| `SEARCH <pattern>` | Search for lemmas matching a pattern |
| `QUIET ON` / `QUIET OFF` | Suppress/enable automatic goal display after tactics |
| `<BEGIN>` / `<DONE>` | Delimit multi-line EasyCrypt input |
| `HELP` | Print this guide |
| `QUIT` | Exit |

### EasyCrypt commands

Any line that is not a meta-command is parsed as EasyCrypt input.
This covers tactics, declarations, `search`, `print`, `require`,
etc. The line must be a complete EasyCrypt statement ending with `.`

```
smt().
rewrite H1 H2.
search (%/).
print mulzK.
```

For multi-line statements, wrap with `<BEGIN>` and `<DONE>`:

```
<BEGIN>
lemma test :
  0 <= n =>
  0 < n + 1.
<DONE>
```

### Workflow

**1. Load a file up to the proof point:**

```
LOAD "myfile.ec" 42
```

This compiles the file through line 42 (processing any command whose
end is on or before that line). The response includes where it
stopped:

```
OK [uuid:15] [loaded:myfile.ec:42]
Current goal
...
<END>
```

For large files, use `-nosmt` to skip SMT calls during prefix
compilation (safe when the prefix was already verified):

```
LOAD "myfile.ec" 436 -nosmt
```

Add `-trace` to a LOAD to inspect the proof state around the last
loaded sentence. The reply body contains four delimited blocks:

```
LOAD "myfile.ec" 42 -trace

=== BEFORE: line 42 (col 0) ===
<focused goal before the sentence>
=== TACTIC (lines 42:0 - 42:10) ===
<exact source text of the sentence>
=== AFTER: line 42 (col 0) ===
<new focused goal, plus any new sibling goals>
=== SUMMARY ===
open goals: N1 -> N2
```

The position comes from the existing `LINE[:COL]` argument; omit it to
trace the file's last sentence. On tactic failure the reply uses the
`ERROR` envelope and still includes the BEFORE/TACTIC blocks plus an
`<sentence failed>` marker in the AFTER block.

**2. Try tactics, using REVERT to restart:**

The uuid returned by LOAD is a revertible state. Use `REVERT` to
return to it after failed experiments — this is instant, unlike
re-doing LOAD which recompiles the prefix.

```
LOAD "myfile.ec" 42
→ OK [uuid:15] [loaded:myfile.ec:42]

smt().                  ← fails, state unchanged
rewrite H1. smt().      ← succeeds (uuid:17)
rewrite H2.             ← wrong direction
REVERT 17               ← back to after the successful smt()
```

To restart the proof from scratch, revert to the LOAD uuid:

```
REVERT 15               ← back to the state right after LOAD
```

Always note the LOAD uuid so you can return to it.

**3. Use checkpoints for branching exploration:**

```
CHECKPOINT before_split
split.
smt().          ← fails
REVERT before_split
apply H.        ← try a different approach
```

**4. Inspect and navigate nested subgoals with `TREE` and `FOCUS`:**

When a tactic opens multiple subgoals, the engine focuses the first
one. By default subsequent tactics act on it; siblings wait their
turn. Use `TREE` to see the structure, including nested splits:

```
TREE
→ OK [uuid:N]
    [1.1.1] x = 0 <- focused
    [1.1.2] y = 1
  [1.2] z = 2
[2] w = 3
<END>
```

The labels are dotted paths. `FOCUS P` rotates focus to the leaf at
path `P`:

```
FOCUS 1.2        ← work on `z = 2`
FOCUS 2          ← work on `w = 3`
FOCUS 1.1.1      ← back to `x = 0`
```

`FOCUS k` (a single integer) targets the k-th open goal in the flat
listing. `NEXT` is shorthand for `FOCUS 2`. Selecting an internal
frame errors (`FOCUS: path must select a leaf goal, not a frame`).

Replies carry a `[focus: k/N]` tag when more than one goal is open
(e.g. `OK [uuid:42] [focus: 1/3]`) so you always know which goal the
next tactic will hit. **TREE labels are not stable across focus
changes** — `FOCUS 1.2` from one state may name a different goal in
another, because the tree always shows the focused goal first.

**5. Build a `+strict_bullets`-friendly proof with `COMMIT`:**

The REPL records every successful interactive phrase. `COMMIT` walks
the proof DAG and emits the recorded tactics with bullets inserted
at every multi-child split. The output is a proof body that compiles
under `pragma +strict_bullets`:

```
LOAD "myfile.ec" 42
split.
- rewrite H. trivial.    ← REPL accepts the unbulleted form
- exact hq.
COMMIT
→ OK [uuid:N]
split.
- rewrite H. trivial.
- exact hq.
<END>
```

Bullet characters cycle through `-`, `+`, `*`, `--`, `++`, `**`, ...
and are chosen to avoid colliding with any frames the LOAD prefix
already opened. Use `COMMIT` once the proof is complete (or at any
checkpoint) and paste the result back into the source file.

`UNDO` / `REVERT` trim the COMMIT transcript automatically.

**6. Use QUIET mode to save tokens during bulk tactic application:**

```
QUIET ON
rewrite H1.
rewrite H2.
rewrite H3.
QUIET OFF
GOALS
```

**7. Search for lemmas using patterns:**

EasyCrypt `search` uses pattern syntax, not keywords. Use `_` as
wildcard:

```
search (fdom _).                ← lemmas involving fdom
search (_ %/ _).                ← integer division lemmas
search (card (_ `|` _)).        ← card of union
search (mu _ _) (_ <= _).       ← mu lemmas with inequalities
```

The SEARCH meta-command is a shorthand that adds `search`/`.`:

```
SEARCH (fdom _)
SEARCH (_ %/ _)
```

## EasyCrypt proof strategy

### General approach

- Start with a pen-and-paper proof plan before writing tactics.
- Use `smt()` aggressively. Try it first — if it fails, add hints:
  `smt(lemma1 lemma2)`.
- Build proofs with `have` assertions. Establish intermediate facts
  as named hypotheses, then combine with `smt()`. Avoid long rewrite
  chains.
- Case split early: `case (n = 0) => [->|hn0].` Base cases often
  close by computation.
- Provide specific instances of lemmas to smt:
  `have h := lemma arg1 arg2.` SMT works much better with ground
  instances than with universally quantified axioms.

### Integer division (`%/`)

- `divzK`: `d %| m => m %/ d * d = m` — recovering from exact
  division
- `mulzK`: `d <> 0 => m * d %/ d = m` — canceling a known factor
- `divzMpl`: `0 < p => p * m %/ (p * d) = m %/ d` — simplifying
  common factors
- To prove `a %/ d = x`, establish `a = x * d` (with `d %| a`),
  then use `mulzK`.
- Don't try to rewrite inside `%/` expressions directly. Instead,
  prove the equality as a `have` and use it.

### What works, what doesn't

- `ring` solves polynomial equalities over integers but treats
  abstract ops (like `fact`) as opaque. It **cannot** simplify
  `fact(n-1+1)` to `fact(n)`.
- `smt()` can do linear arithmetic and combine hypotheses, but
  struggles with nonlinear integer division. Pre-compute key facts
  with `have` and `divzK`/`mulzK`, then let smt combine them.
- `rewrite {k}h` rewrites the k-th occurrence only. Essential when a
  term appears on both sides of an equation.
- For induction on naturals: `elim/natind: n` gives base (`n ≤ 0`)
  and step (`0 ≤ n → P n → P (n+1)`).

### SMT usage

`smt()` and `/#` are equivalent — both call external SMT solvers.

- Use `smt()` **only** on goals that are pure arithmetic or pure
  propositional logic. If the goal contains abstract operators,
  FMap terms, or `if-then-else`, reduce it first with `rewrite`,
  `case`, or `have` before calling `smt()`.
- If `smt()` takes more than 1 second, the goal is too complex.
  Simplify with interactive tactics instead of increasing the
  timeout.

### Common pitfalls

- `rewrite (factS n) //` generates a side goal `0 <= n`. Use
  `first smt()` or provide the precondition explicitly.
- `by` closes **all** remaining subgoals. If it fails, the error
  refers to the first unclosed goal, which may not be the intended
  one.
- When a tactic generates multiple subgoals, the engine focuses the
  first one. Address them in any order via `FOCUS path`, or in the
  default order by closing each in turn. Use `TREE` or `GOALS ALL`
  to see what's open.
- When more than one subgoal is open, replies carry a
  `[focus: k/N]` tag (e.g. `OK [uuid:42] [focus: 1/3]`) so you know
  which one the next tactic will hit.
- `pragma +strict_bullets` does **not** apply to REPL input. Files
  loaded via `LOAD` still respect their own pragmas, but tactics typed
  at the REPL prompt are never rejected for missing bullets — the
  REPL is the focus mechanism.
- `rewrite lemma in H` modifies hypothesis `H` in place (it does
  not consume it). If you need to preserve the original, copy it
  first: `have H' := H; rewrite lemma in H'`.

## EasyCrypt language overview

### File structure

An EasyCrypt file typically begins with `require` and `import`
statements, followed by type, operator, and module declarations, and
then lemma statements with their proofs.

```
require import AllCore List.

type key.
op n : int.
axiom gt0_n : 0 < n.

lemma foo : 0 < n + 1.
proof. smt(gt0_n). qed.
```

### Proofs

A proof is delimited by `proof.` and `qed.`. Inside, tactics are
applied sequentially to transform the goal until it is discharged.

```
lemma bar (x : int) : x + 0 = x.
proof. by ring. qed.
```

### Common tactics

- `trivial` — solve trivial goals
- `smt` / `smt(lemmas...)` — call SMT solvers, optionally with hints
- `auto` — automatic reasoning
- `split` — split conjunctions
- `left` / `right` — choose a disjunct
- `assumption` — close goal from a hypothesis
- `apply H` — apply a hypothesis or lemma
- `rewrite H` — rewrite using an equality
- `have : P` — introduce an intermediate goal
- `elim` — elimination / induction
- `case` — case analysis
- `congr` — congruence
- `ring` / `field` — algebraic reasoning
- `proc` — unfold a procedure (program logics)
- `inline` — inline a procedure call
- `sp` / `wp` — symbolic execution (forward / backward)
- `if` — handle conditionals in programs
- `while I` — handle while loops with invariant `I`
- `rnd` — handle random sampling
- `seq N : P` — split a program at statement `N` with mid-condition `P`
- `conseq` — weaken/strengthen pre/postconditions
- `byequiv` / `byphoare` — switch between program logics
- `skip` — skip trivial program steps
- `sim` — similarity (automatic relational reasoning)
- `ecall` — external call

### Tactic combinators

- `by tac.` — apply `tac` and require all goals to be closed
- `tac1; tac2` — sequence
- `try tac` — try, ignore failure
- `do tac` / `do N tac` — repeat
- `[tac1 | tac2 | ...]` — apply different tactics to each subgoal
- `tac => //.` — apply `tac`, then try `trivial` on generated subgoals
- `move=> H` / `move=> /H` — introduction and views

### Key libraries

- `AllCore` — re-exports the core libraries (logic, integers, reals,
  lists, etc.)
- `Distr` — probability distributions
- `DBool`, `DInterval`, `DList` — specific distributions
- `FSet`, `FMap` — finite sets and maps
- `SmtMap` — maps with SMT support
- `PROM` — programmable/lazy random oracles

### Guidelines

* Use SMT solver only in direct mode (smt() or /#) on simple goals
  (arithmetic goals, pure logical goals).

* Refrain from unfolding operator definitions unless necessary.
  If you need more properties on an operator, state this property
  in a dedicated lemma, but avoid unfolding definitions in higher
  level proofs.
