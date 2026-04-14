.. _language-overview:

========================================================================
Overview
========================================================================

EasyCrypt is an interactive proof assistant designed for reasoning about
the security of cryptographic constructions. It provides:

- A **typed functional language** for writing mathematical definitions:
  types, operators, predicates, lemmas, and proofs.

- An **imperative programming language** for describing the behavior
  of cryptographic algorithms and adversaries as probabilistic programs.

- A collection of **program logics** -- Hoare logic, probabilistic
  Hoare logic, probabilistic relational Hoare logic, and others -- for
  reasoning about the behavior of those programs.

This chapter introduces the general structure of EasyCrypt files and
how the various pieces fit together.

.. contents::
   :local:

------------------------------------------------------------------------
File structure
------------------------------------------------------------------------

An EasyCrypt source file has the extension ``.ec``. A file consists of
a sequence of top-level declarations and definitions. The main kinds
of top-level items are:

- **Type declarations**: introduce new types (abstract, aliases,
  records, algebraic datatypes).

- **Operator and predicate declarations**: introduce new functions and
  predicates, either abstract or with a concrete definition.

- **Axioms and lemmas**: state properties (axioms are assumed, lemmas
  must be proved).

- **Module type declarations**: describe the interface of a module
  (a collection of mutable state and procedures).

- **Module declarations**: define modules that implement a module type.

- **Theories**: group related declarations together under a name.

- **Sections**: provide a scoping mechanism for local assumptions.

- **Clone directives**: instantiate abstract theories with concrete
  definitions.

Items are terminated by a period (``.``).

Here is a minimal EasyCrypt file that declares a type, defines an
operator, and states a lemma:

.. code-block:: easycrypt

   require import AllCore.

   type color = [Red | Green | Blue].

   op is_primary (c : color) : bool =
     with c = Red   => true
     with c = Green => false
     with c = Blue  => true.

   lemma red_is_primary : is_primary Red.
   proof. by []. qed.

------------------------------------------------------------------------
Loading theories
------------------------------------------------------------------------

EasyCrypt files can load other files (called *theories*) using the
``require`` command:

.. code-block:: easycrypt

   require AllCore.

This makes the contents of ``AllCore`` available under a qualified
name (e.g. ``AllCore.List.size``). To bring the names into scope
without qualification, add ``import``:

.. code-block:: easycrypt

   require import AllCore.

There is also ``export``, which re-exports the imported names so that
any file that later imports the current file also sees them:

.. code-block:: easycrypt

   require export AllCore.

You can require several theories at once:

.. code-block:: easycrypt

   require import AllCore List FSet.

The ``import`` and ``export`` keywords can also be used standalone to
import or export a theory that has already been required:

.. code-block:: easycrypt

   require AllCore.
   import AllCore.

------------------------------------------------------------------------
Comments
------------------------------------------------------------------------

Comments in EasyCrypt are delimited by ``(*`` and ``*)`` and can be
nested:

.. code-block:: easycrypt

   (* This is a comment *)

   (* Comments (* can be *) nested *)

------------------------------------------------------------------------
A first example
------------------------------------------------------------------------

To give a flavor of how the language pieces fit together, here is a
small but complete example. It defines an abstract type, an operator
over that type, and proves a simple property.

.. code-block:: easycrypt

   require import AllCore.

   (* An abstract type with decidable equality *)
   type key.

   (* A simple operator *)
   op xor (x y : key) : key.

   (* We assume xor is involutive *)
   axiom xorK (x y : key) : xor (xor x y) y = x.

   (* A consequence: xor is a left-inverse of itself *)
   lemma xor_cancel (x y : key) : xor (xor x y) y = x.
   proof. by apply xorK. qed.

The following chapters describe each part of the language in detail.
:ref:`Types <language-types>` covers the type system.
:ref:`Operators and predicates <language-operators>` explains how to
define functions and predicates. :ref:`Expressions <language-expressions>`
and :ref:`Formulas <language-formulas>` describe the term language.
:ref:`Programs <language-programs>` introduces the imperative fragment.
:ref:`Modules <language-modules>` covers the module system.
:ref:`Theories and sections <language-theories>` and
:ref:`Cloning <language-cloning>` explain theory management.
