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

- `{codepos1}` denotes a *top-level code position*.

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
