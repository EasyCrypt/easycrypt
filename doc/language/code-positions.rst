:orphan:

.. remove the :orphan: marker above once this page is referenced from a
   language-reference toctree.

========================================================================
Code positions
========================================================================

A *code position* designates an instruction (or a gap between
instructions) inside a procedure body.  One common language of code
positions is shared by the program tactics that take a position
argument — `swap`, `wp`, `sp`, `alias`, `kill`, `outline`,
`proc change`, ... — and by fine-grained module definitions
(:doc:`module-update`).

------------------------------------------------------------------------
Base positions
------------------------------------------------------------------------

- a plain integer `n` — the `n`-th instruction of the block (1-based);
- an anchor `^if`, `^while`, `^match`, `^x<-` (assignment to `x`),
  `^x<$` (sampling into `x`), `^x<@` (call assigned to `x`), or the
  left-value-less forms `^<-`, `^<$`, `^<@` — the first matching
  instruction; a specific occurrence is selected with `{n}`, e.g.
  `^<@{2}` for the second call;
- an offset `{anchor} &+ n` / `{anchor} &- n` relative to an anchor.

------------------------------------------------------------------------
Nested positions
------------------------------------------------------------------------

A position may descend into the branches of structured instructions,
written as a path of positions and *branch selectors*: after a
position, `.` enters the body of a `while` or the true branch of an
`if`, `?` enters the false branch of an `if`, and `#C.` enters the
branch of a `match` for constructor `C`.

- `^while.2` is the second instruction of the loop body;
- `^if?1` is the first instruction of the else branch;
- `^match#Some.^if.1` is the first instruction of the true branch of
  the `if` inside the `Some` branch of the `match`.

.. warning::

  A `.` followed by whitespace ends the sentence.  Nested positions and
  match-branch selectors must therefore be written **without spaces**
  around the dot: `^while.^s<-`, `#Some.]` (with the closing bracket
  abutting the selector), never `^while. ^s<-`.

------------------------------------------------------------------------
Ranges
------------------------------------------------------------------------

Contexts that operate on a block of instructions accept ranges of
positions: `[{codepos} .. {codepos}]` selects an inclusive span, and
`[{codepos} +> n]` selects the instruction at `{codepos}` and the `n`
following ones.
