========================================================================
Tactic: `swap`
========================================================================

The `swap` tactic applies to program-logic goals by rewriting the program
into a semantically equivalent form where two consecutive, independent
program fragments are exchanged.

In a nutshell, `swap` permutes commands when doing so does not change the
program’s behavior (typically because the swapped fragments do not
interfere, e.g., they write to disjoint variables and neither reads what the
other writes).

Applying `swap` replaces the current goal by the same goal, but with the
selected commands swapped in the program. This is useful to expose a more
convenient program structure, for example to align programs in relational
proofs or to bring related statements closer together.

.. contents::
   :local:

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

The `swap` tactic comes in several forms:

.. admonition:: Syntax

  - `swap {side}? {codepos1}`
  - `swap {side}? {codepos1} {codeoffset1}`
  - `swap {side}? [{codepos1}..{codepos1}] {codeoffset1}``

Here:

- `{side}` is optional and is either `1` or `2`. It selects the left or
  right program in relational goals. If omitted, the tactic applies to the
  single program under consideration.

- `{codepos1}` denotes a code position in the program.

- Any `{codepos1}` or block `[{codepos1}..{codepos1}]` may be prefixed with a
  *code path*, selecting a nested block in which the swap takes place. Each
  step of the path is a code position followed by a branch selector: `.`
  for the then-branch of a conditional or the body of a loop, `?` for the
  else-branch of a conditional, and `#C.` for the arm of a `match` labelled
  by the constructor `C`. A single position directly follows the path,
  while a block is separated from it by `:`. For instance, `2#Some.1`
  designates the first command of the `Some` arm of the `match` at position
  `2`, and `1.:[1..2]` the block formed by the first two commands of the
  then-branch (or loop body) of the command at position `1`.

- A `{codeoffset1}` is either:

  - a signed integer (`n` or `-n`), denoting a relative position, or
  - an absolute code position written `@ {codepos1}`.

The meaning of these forms is as follows:

- `swap {side}? {codepos1}`

  swaps the two adjacent commands starting at the top-level position
  `{codepos1}`.

- `swap {side}? {codepos1} {codeoffset1}`

  swaps the command at top-level position `{codepos1}` with the command
  at the position designated by `{codeoffset1}`.

- `swap {side}? [{codepos1}..{codepos1}] {codeoffset1}`

  swaps a whole sequence of commands delimited by `[{codepos1}..{codepos1}]`
  with the commands starting at the position designated by `{codeoffset1}`.

In all cases, the swap is only valid when the exchanged fragments are
independent, so that the transformation preserves the program semantics.

When a code path is given, positions and offsets are interpreted relative
to the selected block, the destination must lie inside that block, and the
enclosing command (conditional, loop or `match`) and its other branches are
left unchanged.

------------------------------------------------------------------------
Example (single statement)
------------------------------------------------------------------------

The following example swaps two adjacent assignments that do not interfere.
The returned result is unchanged, but the rewritten program may be more
convenient for subsequent proof steps.

.. ecproof::

  require import AllCore.

  module M = {
    proc reorder(x : int) : int = {
      var a, b : int;
      a <- x + 1;
      b <- x + 2;
      return a + b;
    }
  }.

  lemma reorder_correct (n : int) :
    hoare [ M.reorder : x = n ==> res = (n + 1) + (n + 2) ].
  proof.
    proc.

    (*$*) (* Swap the command at position 1 with the next command (offset +1). *)
    swap 1 1.

    (* The goal is the same, but with the program rewritten. *)
    admit.
  qed.

------------------------------------------------------------------------
Example (swapping a block)
------------------------------------------------------------------------

The following example illustrates the block form
`swap [{codepos1}..{codepos1}] {codeoffset1}`.  We swap a block of two
commands with a later, independent command.

.. ecproof::

  require import AllCore.

  module M = {
    proc swap_block(x : int) : int = {
      var a, b, c : int;

      a <- x + 1;      (* 1 *)
      b <- x + 2;      (* 2 *)
      c <- x + 3;      (* 3 *)
      a <- a + 10;     (* 4 *)

      return a + b + c;
    }
  }.

  lemma swap_block_correct (n : int) :
    hoare [ M.swap_block : x = n ==> res = (n + 1 + 10) + (n + 2) + (n + 3) ].
  proof.
    proc.
    (*$*)
    (* Swap the block [2..3] (b <- x+2; c <- x+3) with the following command
       a <- a + 10. These fragments are independent since:
       - the block assigns b and c, and
       - the command updates a using only a. *)
    swap [2..3] 1.

    (* The goal is the same, but with the program rewritten. *)
    admit.
  qed.

------------------------------------------------------------------------
Example (swapping inside a branch)
------------------------------------------------------------------------

The following example uses a code path to swap two commands located in the
then-branch of a conditional. The conditional itself and its else-branch are
preserved.

.. ecproof::

  require import AllCore.

  module M = {
    var x : bool
    var y : int

    proc branch(b : bool) : unit = {
      if (b) { x <- true; y <- 2; } else { x <- false; y <- 6; }
    }
  }.

  lemma branch_correct : hoare [ M.branch : !b ==> !M.x ].
  proof.
    proc.

    (*$*)
    (* Swap the first command of the then-branch of command 1 with the
       following command of that branch. The program becomes
       `if (b) { y <- 2; x <- true; } else { x <- false; y <- 6; }`. *)
    swap 1.:[1..1] 1.

    (* The conditional is still there. *)
    admit.
  qed.

------------------------------------------------------------------------
Example (invalid swap)
------------------------------------------------------------------------

The following example shows a swap attempt that fails because the two
commands are not independent: the second command reads the value written by
the first one.

.. ecproof::

  require import AllCore.

  module M = {
    proc bad_swap(x : int) : int = {
      var a, b : int;
      a <- x + 1;   (* 1 *)
      b <- a + 2;   (* 2 *)
      return b;
    }
  }.

  lemma bad_swap_demo (n : int) :
    hoare [ M.bad_swap : x = n ==> res = n + 3 ].
  proof.
    proc.

    (*$*)(* This swap is invalid: b depends on a. *)
    fail swap 1 1.

    admit.
  qed.
