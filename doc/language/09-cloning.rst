.. _language-cloning:

========================================================================
Cloning
========================================================================

*Cloning* is the mechanism for instantiating abstract theories with
concrete definitions.  It creates a copy of a theory in which
abstract types, operators, predicates, and axioms are replaced by
concrete ones.  Lemmas proved in the original theory carry over to
the clone, provided the axioms they depend on are discharged.

Cloning is one of the most powerful features of EasyCrypt and is used
extensively in the standard library and in real-world proofs.

.. contents::
   :local:

------------------------------------------------------------------------
Basic cloning
------------------------------------------------------------------------

The simplest form of cloning copies a theory under a new name:

.. code-block:: easycrypt

   clone Foo as Bar.

This creates a copy of theory ``Foo`` named ``Bar``.  Everything in
``Bar`` is identical to ``Foo`` -- the names are just prefixed
differently.

More commonly, you clone a theory while providing concrete
definitions for its abstract components. Consider an abstract theory:

.. code-block:: easycrypt

   abstract theory Monoid.
     type t.
     op e : t.
     op (+) : t -> t -> t.

     axiom addA (x y z : t) : x + (y + z) = (x + y) + z.
     axiom add0 (x : t) : e + x = x.
   end Monoid.

You clone it by specifying the type and operations:

.. code-block:: easycrypt

   clone Monoid as IntAdd with
     type t    = int,
     op   e    = 0,
     op   (+)  = Int.(+)
   proof.
     realize addA. by smt(). qed.
     realize add0. by smt(). qed.
   qed.

The ``with`` clause provides concrete replacements for abstract
items.  The ``proof`` block discharges the axioms of the original
theory by proving they hold for the concrete definitions.

------------------------------------------------------------------------
Overriding types, operators, and predicates
------------------------------------------------------------------------

The ``with`` clause supports several forms of override.

Type overrides
~~~~~~~~~~~~~~

.. code-block:: easycrypt

   clone T as T' with
     type key = int,
     type 'a container = 'a list.

Operator overrides
~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   clone T as T' with
     op f = fun (x : int) => x + 1,
     op g (x : int) = x * 2.

Predicate overrides
~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   clone T as T' with
     pred P (x : int) = 0 < x.

Override modes
~~~~~~~~~~~~~~

There are several override operators:

- ``=`` -- defines the abstract item as an alias for the given
  expression. The original name becomes transparent.

- ``<-`` -- defines the item *inline* and removes the original
  abstract name.

- ``<=`` -- defines the item inline but keeps the original name.

In most cases, ``=`` is what you want.

------------------------------------------------------------------------
Renaming and removing
------------------------------------------------------------------------

Renaming
~~~~~~~~

The ``rename`` clause renames items in the clone:

.. code-block:: easycrypt

   clone T as T' with ...
   rename op "old_name" as "new_name".

You can rename types, operators, predicates, lemmas, exceptions,
modules, module types, and theories.  The string arguments are
matched as regular expressions, which allows bulk renaming:

.. code-block:: easycrypt

   rename lemma "foo_" as "bar_".   (* renames foo_X to bar_X *)

Removing
~~~~~~~~

The ``remove`` clause removes abbreviations from the clone:

.. code-block:: easycrypt

   clone T as T' with ...
   remove abbrev ( * ).

This is useful when the clone provides its own notation and the
original abbreviations would cause conflicts.

------------------------------------------------------------------------
Proof obligations
------------------------------------------------------------------------

When an abstract theory has axioms, cloning it generates *proof
obligations* -- you must prove that the axioms hold for your concrete
definitions.

The proof block after a ``clone`` uses ``realize`` to discharge each
axiom:

.. code-block:: easycrypt

   clone Monoid as IntMul with
     type t   = int,
     op   e   = 1,
     op   (+) = Int.( * )
   proof.
     realize addA. by smt(). qed.
     realize add0. by smt(). qed.
   qed.

If you want to leave some axioms unproven (keeping them as axioms in
the clone), you can omit their ``realize`` or use ``admit``:

.. code-block:: easycrypt

   proof. realize addA. by smt(). qed. qed.
   (* add0 is not realized, so it remains an axiom in the clone *)

Proof tags
~~~~~~~~~~

You can selectively include or exclude axioms from the proof
obligation using tags.  Axioms can be tagged in the original theory:

.. code-block:: easycrypt

   axiom [mytag] foo : ...

And the clone can filter by tag:

.. code-block:: easycrypt

   clone T as T' with ... proof *.   (* prove all *)
   clone T as T' with ... proof -.   (* prove none *)

------------------------------------------------------------------------
Common cloning patterns
------------------------------------------------------------------------

Instantiating algebraic structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The standard library defines abstract theories for rings, fields,
ordered types, etc.  These are instantiated by cloning:

.. code-block:: easycrypt

   require import Ring.

   clone ComRing as IntRing with
     type t     = int,
     op   zeror = 0,
     op   oner  = 1,
     op   (+)   = Int.(+),
     op   ( * ) = Int.( * ),
     op   [-]   = Int.([-])
   proof. (* ... *) qed.

Instantiating finite types
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``FinType`` theory defines the notion of a finite type with
enumeration. To declare that your type is finite:

.. code-block:: easycrypt

   require import FinType.

   clone FinType as BoolFin with
     type t      = bool,
     op   enum   = [true; false]
   proof. (* ... *) qed.

Instantiating cryptographic primitives
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``PROM`` theory provides a programmable random oracle model.
Cloning it sets up the oracle for your specific key/hash types:

.. code-block:: easycrypt

   require import PROM.

   clone FullRO as RO with
     type in_t    = msg,
     type out_t   = hash,
     op   dout  _ = dhash
   proof. (* ... *) qed.

------------------------------------------------------------------------
Clone without ``as``
------------------------------------------------------------------------

If you omit the ``as`` clause, the contents of the clone are
imported directly into the current scope (like an anonymous clone):

.. code-block:: easycrypt

   clone Monoid with
     type t   = int,
     op   e   = 0,
     op   (+) = Int.(+)
   proof. (* ... *) qed.

This is convenient but can cause name clashes. Using ``as`` to give
the clone an explicit name is generally safer.

------------------------------------------------------------------------
Local clones
------------------------------------------------------------------------

A clone can be declared ``local``, making it visible only within the
enclosing theory:

.. code-block:: easycrypt

   local clone Monoid as M with ... proof. ... qed.
