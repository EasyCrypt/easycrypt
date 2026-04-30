# EasyCrypt — LLM Agent Guide

EasyCrypt is a proof assistant for reasoning about the security of
cryptographic constructions. It provides support for probabilistic
computations, program logics (Hoare logic, probabilistic Hoare logic,
probabilistic relational Hoare logic), and ambient mathematical
reasoning.

## Using the `llm` command

The `llm` subcommand is designed for non-interactive, LLM-friendly
batch compilation. It produces no progress bar and no `.eco` cache
files.

```
easycrypt llm [OPTIONS] FILE.ec
```

### Options

- `-upto LINE` or `-upto LINE:COL` — Compile up to (but not
  including) the given location, then print the current goal state to
  stdout and exit with code 0. Use this to inspect the proof state at
  a specific point in a file.

- `-lastgoals` — On failure, print the goal state (as it was just
  before the failing command) to stdout, then print the error to
  stderr, and exit with code 1. Use this to understand what the
  failing tactic was supposed to prove.

Standard loader and prover options (`-I`, `-timeout`, `-p`, etc.) are
also available.

### Output conventions

- **Goals** are printed to **stdout**.
- **Errors** are printed to **stderr**.
- **Exit code 0** means success (or `-upto` reached its target).
- **Exit code 1** means a command failed.
- If there is no active proof at the point where goals are requested,
  stdout will contain: `No active proof.`

### Workflow for writing and debugging proofs

1. Try to write a pen-and-paper proof first.

2. Write the `.ec` file with your proof attempt. For a large proof,
   write down skeleton and `admit` subgoals first, and then detail
   the proof.

3. Run `easycrypt llm -lastgoals FILE.ec` to check the full file.
   - If it succeeds (exit 0), you are done.
   - If it fails (exit 1), read the error from stderr and the goal
     state from stdout to understand what went wrong.

4. Use `-upto LINE` to inspect the proof state at a specific point
   without running the rest of the file. This is useful for
   incremental proof development.

5. Fix the proof and repeat from step 2. The ultimate proof should
   not contain `admit` or `admitted`.

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

<!-- TODO: expand this section with descriptions and examples -->

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

* Use SMT solver only in direct mode (smt() or /#) on simple goals (arithmetic goals, pure logical goals).

* Refrain from unfolding operator definitions unless necessary.
  If you need more properties on an operator, state this property in a dedicated lemma,
  but avoid unfolding definitions in higher level proofs.

