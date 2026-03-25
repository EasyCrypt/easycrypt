========================================================================
Hints: `hint simplify`
========================================================================

The `hint simplify` commands manage user reduction rules used by
`simplify`, `cbv`, and tactics that rely on the same simplification
machinery.

Hints can be declared globally in a theory, selected through named
databases, and adjusted locally inside a proof.

.. contents::
   :local:

------------------------------------------------------------------------
Global declarations
------------------------------------------------------------------------

Global declarations add lemmas to a simplification database.

.. admonition:: Syntax

   `hint simplify {lemma}+ .`

Add the listed lemmas to the default simplification database.

.. admonition:: Syntax

   `hint simplify in {db} : {lemma}+ .`

Add the listed lemmas to the named database `{db}`.

These commands are theory-level declarations: once imported, the
corresponding rules are available to simplification.

------------------------------------------------------------------------
The `hint` clause
------------------------------------------------------------------------

`simplify` and `cbv` accept a single `hint` clause that controls which
user-reduction rules are used. The clause is introduced by the `hint`
keyword and is built from an unsigned base database selection followed by
any number of signed items:

.. admonition:: Syntax

   `simplify hint {db}* {item}*`

where each `{item}` is one of:

- `+ {db}` / `- {db}` — activate / deactivate a database;
- `+[ {op}+ ]` / `-[ {op}+ ]` — head filter: keep only / drop rules headed
  by the listed operators (at most one filter per clause);
- `{ {lemma}+ }` — add lemmas to the default database for this call.

The delimiter disambiguates an item: a bare name is a database, `[…]`
holds operators, `{…}` holds lemmas. Lemma sets are add-only -- a clause
never removes lemmas from a database; use the head filter to restrict
which rules apply. The same clause is accepted by `cbv`.

The database part of a clause is *either* an unsigned selection *or*
signed deltas, never both (mixing them is redundant and rejected). An
unsigned list `hint d1 d2` **replaces** the consulted databases with
exactly `{d1, d2}`. Signed `+ {db}` / `- {db}` instead modify the current
set (the proof-local default, else the active set): `simplify hint +d2`
adds `d2` to it, `simplify hint -d3` removes `d3`.

A head filter performs full simplification (like a bare `simplify`) with
user reduction restricted to the selected operators.

The `hint` clause is independent of the reduction arguments that
`simplify` and `cbv` already accept: a bare `simplify` performs full
simplification, `simplify delta` additionally unfolds all definitions,
`simplify f g` unfolds the operators `f` and `g`, and a keyword-less list
such as `beta zeta` performs only the named reductions. A `hint` clause
may follow any of these (for example `simplify delta hint +[f]`).

------------------------------------------------------------------------
Proof-local commands
------------------------------------------------------------------------

Inside a proof, the simplify configuration can be changed without
modifying the theory-level declarations. The `hint` command takes the
same clause as the `simplify`/`cbv` tactics, and each kind of item has a
persistent effect on the proof state:

.. admonition:: Syntax

   `hint {db}* {item}* .`

- `+ {db}` / `- {db}` — activate / deactivate a database (for later bare
  `simplify`/`cbv`);
- `{ {lemma}+ }` — add lemmas to the default database;
- an unsigned database list `{db}+` — set the proof-local default
  databases used by later `simplify`/`cbv` calls;
- `+[ {op}+ ]` / `-[ {op}+ ]` — set the proof-local default head filter.

As in the tactic clause, the database part is *either* an unsigned
selection *or* signed `+`/`-` deltas, never both.

.. admonition:: Syntax

   `hint clear {db}? .`

Clear the local lemma additions: for the default database when `{db}` is
omitted, or for the named database `{db}`. Note that `hint clear default`
is reserved for the form below, so a database named `default` cannot be
cleared this way.

.. admonition:: Syntax

   `hint clear default .`

Clear the proof-local default database and head filter.

These proof-local changes are part of the proof state and therefore
follow the usual subgoal branching behavior. Explicit arguments on
`simplify`/`cbv` take precedence over the proof-local defaults.

------------------------------------------------------------------------
Scoped application
------------------------------------------------------------------------

A `hint` command can be used as a scoped wrapper around a tactic, with the
same clause syntax.

.. admonition:: Syntax

   `with hint {clause} ( {tactic} )`

For example:

.. code-block:: easycrypt

   with hint +ring (simplify).
   with hint {fooE} (rewrite foo /=).
   with hint ring (cbv).

The wrapped tactic runs with the modified hint configuration, but the
subgoals produced afterwards are restored to the original configuration.

------------------------------------------------------------------------
Example
------------------------------------------------------------------------

.. ecproof::
   :title: Simplify hint databases

   require import AllCore Int.

   op wrap1 (x : int) = x + 1.
   op wrap2 (x : int) = x + 2.
   op box   (x : int) = x.

   lemma wrap1E x : box (wrap1 x) = box (x + 1).
   proof. smt(). qed.

   lemma wrap2E x : box (wrap2 x) = box (x + 2).
   proof. smt(). qed.

   hint simplify wrap1E.
   hint simplify in named : wrap2E.

   lemma demo_default (x : int) :
     box (wrap1 x) = box (x + 1).
   proof.
     simplify.
     trivial.
   qed.

   lemma demo_named (x : int) :
     box (wrap2 x) = box (x + 2).
   proof.
     simplify hint named.
     trivial.
   qed.

   lemma demo_local_default (x : int) :
     box (wrap2 x) = box (x + 2).
   proof.
     with hint named (simplify).
     trivial.
   qed.

   lemma demo_head_filter (x : int) :
     box (wrap1 x) = box (x + 1).
   proof.
     simplify hint +[wrap1].
     trivial.
   qed.
