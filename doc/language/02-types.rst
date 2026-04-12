.. _language-types:

========================================================================
Types
========================================================================

Every expression in EasyCrypt has a type. Types classify values:
integers, booleans, lists, functions, distributions, and so on. This
chapter describes the type system, starting with the built-in types
and working up to user-defined types.

.. contents::
   :local:

------------------------------------------------------------------------
Built-in types
------------------------------------------------------------------------

EasyCrypt provides the following primitive types. They are always in
scope (defined in the ``Pervasive`` prelude).

``unit``
  The unit type. It has a single value, written ``tt``. It is used
  when no meaningful value needs to be returned.

``bool``
  The type of booleans, with values ``true`` and ``false``.

``int``
  The type of (unbounded) integers.  Integer literals are written as
  usual: ``0``, ``42``, ``-3``.  Hexadecimal literals are also
  supported: ``0x1A2B``.

``real``
  The type of real numbers.  Real literals are written with a decimal
  point or as a ratio: ``0.5``, ``3.14``, ``1%r`` (the integer 1
  coerced to a real).

``'a distr``
  The type of (sub-)distributions over a type ``'a``.  A value of
  type ``'a distr`` assigns a probability (a non-negative real) to
  each value of type ``'a``, with the total probability at most 1.

``'a option``
  The option type, with constructors ``None`` and ``Some``.  It is
  defined in the ``Logic`` prelude as an algebraic datatype.

``exn``
  The type of exceptions.  New exception constructors are introduced
  by ``exception`` declarations (see :ref:`language-programs`).

All types in EasyCrypt are *inhabited*: there is a polymorphic
constant ``witness : 'a`` that provides a default value for any type.
This means there is no empty type.

------------------------------------------------------------------------
Type variables and polymorphism
------------------------------------------------------------------------

Types can be parameterized by *type variables*, which are written with
a leading tick: ``'a``, ``'b``, ``'key``, etc.  Polymorphic
definitions work for any choice of type arguments.

For example, the identity function is polymorphic in its argument type:

.. code-block:: easycrypt

   op id (x : 'a) : 'a = x.

When using a polymorphic operator, EasyCrypt infers the type arguments
automatically in most cases.  When it cannot, you can supply them
explicitly using angle-bracket syntax:

.. code-block:: easycrypt

   op id<:int> 42.

------------------------------------------------------------------------
Tuples
------------------------------------------------------------------------

Given types ``t1``, ``t2``, ..., ``tn``, the product type
``t1 * t2 * ... * tn`` is the type of tuples of those types.  Tuple
values are written with parentheses and commas:

.. code-block:: easycrypt

   (1, true)             (* : int * bool      *)
   (1, true, 42)         (* : int * bool * int *)

Tuple components are accessed by *projection*, written with a
backtick and a 1-based index:

.. code-block:: easycrypt

   op fst_example : int = (1, true).`1.     (* = 1    *)
   op snd_example : bool = (1, true).`2.    (* = true *)

The standard library also provides ``fst`` and ``snd`` abbreviations
for pairs.

Pattern matching on tuples is supported in ``let`` bindings and in
operator definitions:

.. code-block:: easycrypt

   op swap (p : 'a * 'b) : 'b * 'a =
     let (x, y) = p in (y, x).

------------------------------------------------------------------------
Function types
------------------------------------------------------------------------

The type ``t1 -> t2`` is the type of functions from ``t1`` to ``t2``.
Function types associate to the right:

.. code-block:: easycrypt

   (* These are the same type: *)
   (* int -> int -> bool       *)
   (* int -> (int -> bool)     *)

Functions are first-class values.  You can pass them as arguments,
return them from operators, and store them in data structures.

.. code-block:: easycrypt

   op apply (f : 'a -> 'b) (x : 'a) : 'b = f x.

   op compose (g : 'b -> 'c) (f : 'a -> 'b) : 'a -> 'c =
     fun x => g (f x).

------------------------------------------------------------------------
Type declarations
------------------------------------------------------------------------

New types are introduced with the ``type`` keyword.  There are several
forms.

Abstract types
~~~~~~~~~~~~~~

An abstract type declaration introduces a type name with no definition.
Nothing is known about the type except that it is inhabited (it has a
``witness``).

.. code-block:: easycrypt

   type key.
   type 'a container.

Abstract types are useful for specifying interfaces: you work with
the type name without committing to a representation.

Type aliases
~~~~~~~~~~~~

A type alias gives a new name to an existing type expression:

.. code-block:: easycrypt

   type point = int * int.
   type 'a predicate = 'a -> bool.

Aliases are transparent: ``point`` and ``int * int`` are
interchangeable everywhere.

------------------------------------------------------------------------
Record types
------------------------------------------------------------------------

A record type groups named fields together:

.. code-block:: easycrypt

   type person = {
     name : string;
     age  : int;
   }.

Record values are constructed with braces:

.. code-block:: easycrypt

   op alice : person = {| name = "Alice"; age = 30; |}.

Fields are accessed with dot notation:

.. code-block:: easycrypt

   op alice_age : int = alice.`age.

Records can also be updated functionally:

.. code-block:: easycrypt

   op older_alice : person = {| alice with age = 31; |}.

------------------------------------------------------------------------
Algebraic datatypes
------------------------------------------------------------------------

An algebraic datatype (also called a *variant* or *sum type*) defines
a type by listing its constructors.  Each constructor can carry zero
or more arguments.

.. code-block:: easycrypt

   type color = [Red | Green | Blue].

   type 'a tree = [
     | Leaf
     | Node of 'a & 'a tree & 'a tree
   ].

Constructors are introduced inside square brackets, separated by
``|``.  Arguments of a constructor are separated by ``&`` (not ``*``,
which would denote a single tuple argument).

Values of an algebraic datatype are built by applying a constructor:

.. code-block:: easycrypt

   op example_tree : int tree =
     Node 1 (Node 2 Leaf Leaf) Leaf.

Pattern matching is the primary way to inspect algebraic datatypes.
See :ref:`language-expressions` for the ``match`` expression and
pattern-matching operator definitions.

The ``option`` type is a standard algebraic datatype:

.. code-block:: easycrypt

   type 'a option = [None | Some of 'a].

------------------------------------------------------------------------
Subtypes
------------------------------------------------------------------------

A *subtype* carves out a subset of an existing type that satisfies
a predicate.  The syntax is:

.. code-block:: easycrypt

   subtype name = { x : carrier | predicate }.

For example, to define a type of natural numbers as non-negative
integers:

.. code-block:: easycrypt

   subtype nat = { x : int | 0 <= x }.

A subtype declaration generates:

- An injection from the subtype into the carrier type.
- A partial projection from the carrier type to the subtype (which
  requires the predicate to hold).
- An axiom stating that the injection is indeed injective.
- An axiom stating that the projection is a left-inverse of the
  injection on values satisfying the predicate.

You can optionally provide a constructor name with ``as``:

.. code-block:: easycrypt

   subtype nat AS Nat = { x : int | 0 <= x }.

------------------------------------------------------------------------
Type classes and instances
------------------------------------------------------------------------

EasyCrypt has a lightweight type-class mechanism, mainly used for
algebraic structures.  The standard library defines type classes such
as ``ring`` and ``field``, along with associated operators and axioms.

To declare that a type is an instance of a type class, use the
``instance`` keyword.  For example, declaring that ``int`` is a
commutative ring:

.. code-block:: easycrypt

   instance ring with int
     op rzero = 0
     op rone  = 1
     op radd  = Int.(+)
     op rmul  = Int.( * )
     op ropp  = Int.([-])
     proof. (* ... prove the ring axioms ... *) qed.

Once an instance is registered, the ``ring`` and ``field`` proof
tactics can automatically solve equations over that type.

Type classes are not something most users need to define; the standard
library provides the main ones.  Understanding how to declare
*instances* is the important part.
