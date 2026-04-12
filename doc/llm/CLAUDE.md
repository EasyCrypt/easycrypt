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
available.

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
| `LOAD "file.ec" [LINE[:COL]]` | Reset state, compile file up to the given line |
| `UNDO` | Undo the last proof step |
| `REVERT <uuid-or-name>` | Revert to a specific state (by uuid or checkpoint name) |
| `GOALS` | Print the current goal (first subgoal only, with remaining count) |
| `GOALS ALL` | Print all subgoals |
| `CHECKPOINT <name>` | Save current uuid under a name for later `REVERT` |
| `SEARCH <pattern>` | Search for lemmas matching a pattern |
| `QUIET ON` / `QUIET OFF` | Suppress/enable automatic goal display after tactics |
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

**2. Try tactics interactively:**

```
smt().
```

If it fails, the state is unchanged — try another tactic immediately:

```
rewrite H1.
smt(lemma1 lemma2).
```

**3. Use checkpoints for branching exploration:**

```
CHECKPOINT before_split
split.
smt().          ← fails
REVERT before_split
apply H.        ← try a different approach
```

**4. Use QUIET mode to save tokens during bulk tactic application:**

```
QUIET ON
rewrite H1.
rewrite H2.
rewrite H3.
QUIET OFF
GOALS
```

**5. Search for lemmas:**

```
SEARCH mulzK
SEARCH dvdz
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

### Common pitfalls

- `rewrite (factS n) //` generates a side goal `0 <= n`. Use
  `first smt()` or provide the precondition explicitly.
- `by` closes **all** remaining subgoals. If it fails, the error
  refers to the first unclosed goal, which may not be the intended
  one.
- When a tactic generates multiple subgoals, each subgoal must be
  closed in order. Use `GOALS ALL` to see them all.

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
