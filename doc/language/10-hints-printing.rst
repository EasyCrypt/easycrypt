.. _language-hints:

========================================================================
Hints, printing, and configuration
========================================================================

Beyond definitions and proofs, EasyCrypt provides commands for
configuring automated reasoning, inspecting the environment, and
controlling the prover.

.. contents::
   :local:

------------------------------------------------------------------------
Hint databases
------------------------------------------------------------------------

EasyCrypt maintains several databases of lemmas that automated tactics
can draw from.  The ``hint`` command registers lemmas in these
databases.

Simplification hints
~~~~~~~~~~~~~~~~~~~~

The ``simplify`` tactic uses a database of rewrite rules to
normalize terms.  You add rules with:

.. code-block:: easycrypt

   hint simplify lemma1, lemma2.

This registers ``lemma1`` and ``lemma2`` as simplification rules:
whenever ``simplify`` runs, it tries to apply these lemmas as
left-to-right rewrites.

The standard library uses this extensively:

.. code-block:: easycrypt

   hint simplify oget_some, oget_none.

Rewriting hints
~~~~~~~~~~~~~~~

The rewriting database is used by tactics that search for applicable
rewrite lemmas:

.. code-block:: easycrypt

   hint rewrite mydb : lemma1 lemma2 lemma3.

This creates (or extends) a named rewrite database ``mydb`` with the
given lemmas.  You can then use it:

.. code-block:: easycrypt

   rewrite mydb.     (* applies any lemma from mydb that matches *)

Solve hints
~~~~~~~~~~~

The ``solve`` hint database is used by the ``solve`` tactic to
discharge goals automatically:

.. code-block:: easycrypt

   hint solve 0 : lemma1 lemma2.

The number (here ``0``) is a priority. Priority ``0`` means the
lemma must match exactly (no unification); higher priorities allow
more flexibility.

------------------------------------------------------------------------
Print, search, and locate
------------------------------------------------------------------------

These commands help you explore what is available in the current
environment.

``print``
~~~~~~~~~

Displays the definition and type of an item:

.. code-block:: easycrypt

   print op double.         (* shows the definition of double    *)
   print type color.        (* shows the definition of color     *)
   print axiom mulA.        (* shows the statement of mulA       *)
   print module type Adv.   (* shows the Adv interface           *)
   print module M.          (* shows the structure of module M   *)
   print theory Ring.       (* shows the contents of theory Ring *)

``search``
~~~~~~~~~~

Searches for lemmas whose statement matches a pattern:

.. code-block:: easycrypt

   search ( + ).            (* lemmas mentioning addition     *)
   search (_ + _ = _ + _).  (* lemmas with a specific shape   *)
   search [-some_tag].      (* excluding tagged lemmas        *)

``search`` is invaluable for discovering relevant lemmas in the
standard library.

``locate``
~~~~~~~~~~

Finds the fully qualified name of an identifier:

.. code-block:: easycrypt

   locate size.             (* finds e.g. List.size, FSet.card *)

------------------------------------------------------------------------
Prover configuration
------------------------------------------------------------------------

EasyCrypt relies on external SMT solvers (such as Z3, CVC4, Alt-Ergo)
to discharge proof obligations. The ``smt`` tactic sends the current
goal to these solvers.

Configuring provers
~~~~~~~~~~~~~~~~~~~

The ``prover`` command controls which solvers are available and how
they are invoked:

.. code-block:: easycrypt

   prover timeout=5.         (* set timeout to 5 seconds *)
   prover maxprovers=4.      (* use up to 4 solvers in parallel *)
   prover [z3 cvc4].         (* use only z3 and cvc4 *)

Solver hints
~~~~~~~~~~~~

You can guide ``smt`` by providing lemmas as hints:

.. code-block:: easycrypt

   smt(lemma1 lemma2).       (* provide these lemmas to the solver *)

This is often necessary for non-trivial goals: the solver may not
find the right lemmas on its own, but succeeds when given a hint.

------------------------------------------------------------------------
Pragmas
------------------------------------------------------------------------

Pragmas control various aspects of EasyCrypt's behavior.  They are
set with the ``pragma`` command:

.. code-block:: easycrypt

   pragma Proofs:weak.       (* accept unfinished proofs *)
   pragma Proofs:check.      (* require all proofs (default) *)

Common pragmas:

``Proofs:weak``
  Allows ``admit`` and ``admitted`` without warning. Useful during
  proof development.

``Proofs:check``
  The default mode: all proofs must be completed.

``noia``
  Disables automatic iota-reduction.

------------------------------------------------------------------------
Timeout and resource control
------------------------------------------------------------------------

You can wrap commands in a ``timeout`` block to limit execution time:

.. code-block:: easycrypt

   timeout 10 smt.           (* give smt 10 seconds *)

------------------------------------------------------------------------
Dump and debug
------------------------------------------------------------------------

For debugging, EasyCrypt provides:

.. code-block:: easycrypt

   print.                    (* print current goal      *)
   debug.                    (* enter debug mode        *)

The ``dump`` command can output intermediate proof state for
inspection.
