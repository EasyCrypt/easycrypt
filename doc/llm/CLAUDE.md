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
| `LOAD "file.ec" [LINE[:COL]] [-nosmt]` | Reset state, compile file (optionally skip SMT) |
| `UNDO` | Undo the last proof step |
| `REVERT <uuid-or-name>` | Revert to a specific state (by uuid or checkpoint name) |
| `GOALS` | Print the current goal (first subgoal only, with remaining count) |
| `GOALS ALL` | Print all subgoals |
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

**4. Use QUIET mode to save tokens during bulk tactic application:**

```
QUIET ON
rewrite H1.
rewrite H2.
rewrite H3.
QUIET OFF
GOALS
```

**5. Search for lemmas using patterns:**

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

### When the agent can't hold a persistent pipe

Some LLM front-ends (Claude Code, Codex CLI, etc.) expose the shell as
one-shot command execution — the agent *cannot* keep stdin/stdout open
to `easycrypt llm` across turns. Naively, every tactic would then
require re-`LOAD`-ing the file prefix.

The `scripts/llm/` directory contains a reference fifo-backed daemon
that lets many short-lived shell invocations drive one persistent EC
REPL. Start it once at the beginning of a session, then issue each
tactic as a separate `ec_send.sh` call. See `scripts/llm/README.md` for
the full pattern.

### Iterate interactively, then codify

For long proofs — especially program-logic bodies with 5+ chained
`ecall`s, or big algebraic derivations — write tactics one at a time
in the REPL, inspecting `GOALS` after each, and only commit the final
sequence back to the file once it works. Two reasons:

- **SMT budget.** Committing a long batch and issuing one LOAD
  compounds SMT cost across every intermediate side-condition at once.
  The same tactics often pass individually with a shorter per-call
  timeout.
- **Cheap backtracking.** Use `CHECKPOINT` at every branching point
  and `REVERT` liberally — it's O(1), whereas re-LOAD re-compiles the
  whole prefix.

Pattern:

```
LOAD "file.ec" 100          ← note uuid:N
CHECKPOINT before_body
<try tactic>
GOALS                       ← inspect
<try tactic>
REVERT before_body          ← if the branch fails
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
- When a tactic generates multiple subgoals, each subgoal must be
  closed in order. Use `GOALS ALL` to see them all.
- `rewrite lemma in H` modifies hypothesis `H` in place (it does
  not consume it). If you need to preserve the original, copy it
  first: `have H' := H; rewrite lemma in H'`.
- **`have H := lemma args` may leave unevaluated lambdas.** Lemma
  applications that produce `init`/`map`/`filter` terms often carry
  β-redexes into the introduced hypothesis. Later `rewrite H` can then
  hang indefinitely while the kernel tries to unify. Force
  normalization at introduction with `have /= H := lemma args`.
- **Tactic-repetition (`!tac`) over-applies on nested structures.**
  `!mapiE`, `!initiE`, `!allP` descend into inner layers at different
  array sizes, generate side-conditions that can't be closed by `/#`,
  and either leave stale goals or hang. Use the exact count needed
  (usually 1 or 2 for an equality: `rewrite mapiE 1:/# /= mapiE 1:/#`).
- **`1:/#` vs `1:smt(hints)` in rewrite chains.** Inside a
  `rewrite lemma 1:...` position only `/#` parses; `1:smt(hints)` is
  a parse error. Break the chain:
  `rewrite lemma 1:/#; first smt(hints). rewrite next_lemma.`
- **`suff` not `suffices`.** The surface syntax uses `suff H : P.`;
  `suffices` triggers a parse error.
- **`rewrite allP` only touches the first `all`.** When unfolding
  range predicates on both sides of an implication
  (`all P x => all Q x`), use `!allP` — otherwise the subsequent
  `=> H j Hj` fails with "nothing to introduce" because the conclusion
  is still wrapped in `all`.
- **`congr` vs `congr 1`.** `congr` walks down an array equality all
  the way to list/element equality; `congr 1` takes one structural
  step. Reach for `congr 1` when `congr` descends too far and exposes
  stale `init`/`mkseq` structure.

### Reconciling syntactically distinct constants

When a word-type modulus (`W13.modulus`, `W8.modulus`, …) appears on
one side of a goal and its numeric literal (`8192`, `256`, …) on the
other — for instance after one subterm was lowered through a circuit
lemma while the other came from the spec — `smt()` treats them as
distinct atoms and won't bridge. Normalize explicitly:

```easycrypt
have W13_eq : W13.modulus = 8192 by smt(W13.ge2_modulus).
rewrite W13_eq.
```

Same pattern for `modulus_W`, cardinalities of finite types, and other
constants that have both a symbolic and a numeric form.

### Ring/field commutativity: use the fully-qualified path

Bare `mulrC`/`addrC` may not resolve against a concrete ring clone's
theory. When working in a cloned ring (`Zq`, `Fq`, polynomial rings
over Zq, …), the fully-qualified name of the `ComRing`/`ZModule` lemma
usually succeeds where the short form fails:

```easycrypt
by rewrite Zq.ComRing.mulrC.
```

Use `SEARCH` to find the right path:

```
SEARCH (_ * _) (commutative _)
```

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
