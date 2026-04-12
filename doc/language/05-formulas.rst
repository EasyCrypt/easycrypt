.. _language-formulas:

========================================================================
Formulas
========================================================================

Formulas are the language of propositions in EasyCrypt. A formula is
an expression of type ``bool`` -- there is no separate sort for
propositions. This means that all the expression syntax from
:ref:`language-expressions` is available inside formulas: arithmetic,
function application, pattern matching, etc.

What distinguishes formulas from plain expressions is a set of
additional constructs for referring to program state (memories,
program variables, probabilities) and for expressing judgments in
the program logics.

.. contents::
   :local:

------------------------------------------------------------------------
Logical connectives
------------------------------------------------------------------------

The logical connectives were listed in
:ref:`language-expressions` under boolean operators, but they bear
repeating here since they are the backbone of formulas:

.. code-block:: easycrypt

   P /\ Q          (* conjunction *)
   P \/ Q          (* disjunction *)
   P => Q          (* implication *)
   P <=> Q         (* equivalence *)
   ! P             (* negation    *)

   true             (* tautology   *)
   false            (* absurdity   *)

These are regular boolean operators. Implication ``=>`` associates
to the right: ``P => Q => R`` means ``P => (Q => R)``.

Quantifiers
~~~~~~~~~~~

.. code-block:: easycrypt

   forall (x : t), P x         (* universal *)
   exists (x : t), P x         (* existential *)

Multiple binders:

.. code-block:: easycrypt

   forall (x y : int) (b : bool), ...

------------------------------------------------------------------------
Equality
------------------------------------------------------------------------

Equality is polymorphic and decidable for every type:

.. code-block:: easycrypt

   x = y            (* equality    *)
   x <> y           (* disequality, abbreviation for !(x = y) *)

------------------------------------------------------------------------
Program variable references
------------------------------------------------------------------------

Inside formulas, you can refer to the values of program variables
at specific *memories* (snapshots of program state). This is
essential for stating pre- and post-conditions.

In a **Hoare** judgment, the memory is implicit:

- Program variables in the precondition refer to the initial state.
- Program variables in the postcondition refer to the final state.
- The special identifier ``res`` refers to the return value in
  postconditions.

In a **relational** judgment (``equiv`` / ``pRHL``), there are two
memories -- the *left* memory and the *right* memory -- distinguished
by tags:

.. code-block:: easycrypt

   x{1}       (* variable x in the left memory  *)
   x{2}       (* variable x in the right memory  *)

   glob M{1}  (* global state of module M, left side  *)
   glob M{2}  (* global state of module M, right side *)

   res{1}     (* return value of the left procedure  *)
   res{2}     (* return value of the right procedure *)

In non-relational contexts (Hoare logic), program variables carry
no tag:

.. code-block:: easycrypt

   x          (* in hoare pre/postconditions *)

------------------------------------------------------------------------
Module state in formulas
------------------------------------------------------------------------

The expression ``glob M`` denotes the tuple of all global variables
of module ``M`` (and its sub-modules). It is a first-class value
that can be compared, stored, and quantified over:

.. code-block:: easycrypt

   glob M{1} = glob M{2}       (* the two sides have the same state *)

The type of ``glob M`` depends on the variables declared in ``M``.

------------------------------------------------------------------------
Probability expressions
------------------------------------------------------------------------

EasyCrypt can express the probability of an event after running a
procedure. The general syntax is:

.. code-block:: easycrypt

   Pr[M.f(args) @ &m : event]

where:

- ``M.f(args)`` is a procedure call with concrete arguments.
- ``&m`` is a *memory identifier*, representing the initial state.
- ``event`` is a boolean formula over program variables, representing
  the event whose probability is being measured.

Examples:

.. code-block:: easycrypt

   Pr[Game.main() @ &m : res]
   Pr[Game.main() @ &m : res /\ Game.x = 0]

The result is a ``real`` value between 0 and 1.

To use probability expressions in lemma statements, you typically
quantify over the initial memory:

.. code-block:: easycrypt

   lemma example &m : Pr[Game.main() @ &m : res] = 1%r / 2%r.

------------------------------------------------------------------------
Hoare judgments
------------------------------------------------------------------------

EasyCrypt supports several program logics, each with its own judgment
form. These can appear as top-level lemma statements or as
sub-formulas.

Hoare logic (HL)
~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   hoare[M.f : pre ==> post]

States that if the precondition ``pre`` holds before calling ``M.f``,
then the postcondition ``post`` holds after ``M.f`` terminates. In
``post``, the identifier ``res`` refers to the return value.

Probabilistic Hoare logic (pHL)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   phoare[M.f : pre ==> post] >= p
   phoare[M.f : pre ==> post] <= p
   phoare[M.f : pre ==> post] = p

Like Hoare logic, but the postcondition is satisfied with a given
probability bound ``p``.

A special case is losslessness (the procedure terminates with
probability 1):

.. code-block:: easycrypt

   islossless M.f

This is equivalent to ``phoare[M.f : true ==> true] = 1%r``.

Probabilistic relational Hoare logic (pRHL)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   equiv[M.f ~ N.g : pre ==> post]

States that for any initial states satisfying ``pre``, the final
states of ``M.f`` and ``N.g`` satisfy ``post`` with equal
probability. The precondition and postcondition can refer to
variables on both sides using the ``{1}`` and ``{2}`` tags.

Eager Hoare logic (eHL)
~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   ehoare[M.f : pre ==> post]

Used for reasoning about expected values and costs. The postcondition
is an *extended real* expression (possibly involving ``+oo``), and
the judgment bounds the expected value of the postcondition.

------------------------------------------------------------------------
Putting it together
------------------------------------------------------------------------

Here is an example of a complete lemma statement involving a
relational judgment:

.. code-block:: easycrypt

   lemma example :
     equiv[Game0.main ~ Game1.main :
       ={glob Game0, glob Game1} ==>
       ={res}].

This states that ``Game0.main`` and ``Game1.main`` produce the same
return value (``={res}`` is syntactic sugar for ``res{1} = res{2}``)
whenever they start from the same global state.

The ``={}`` notation is a convenient shorthand for pointwise equality:

.. code-block:: easycrypt

   ={x, y}          (* x{1} = x{2} /\ y{1} = y{2} *)
   ={glob M}        (* glob M{1} = glob M{2}       *)
