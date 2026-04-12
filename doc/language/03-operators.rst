.. _language-operators:

========================================================================
Operators and predicates
========================================================================

Operators and predicates are the building blocks of definitions in
EasyCrypt. An *operator* is a function that returns a value; a
*predicate* is a function that returns a boolean (a proposition).
This chapter explains how to declare and define them.

.. contents::
   :local:

------------------------------------------------------------------------
Operator declarations
------------------------------------------------------------------------

Operators are introduced with the ``op`` keyword.

Abstract operators
~~~~~~~~~~~~~~~~~~

An abstract operator has a name and a type but no definition:

.. code-block:: easycrypt

   op f : int -> int.
   op g : int -> int -> bool.
   op h ['a] : 'a -> 'a -> bool.

Nothing is known about an abstract operator except its type. Abstract
operators are useful inside abstract theories and sections, where
properties are stated as axioms and later instantiated.

Concrete operators
~~~~~~~~~~~~~~~~~~

A concrete operator has a body. The simplest form takes arguments and
returns an expression:

.. code-block:: easycrypt

   op double (x : int) : int = x + x.
   op max (x y : int) : int = if x < y then y else x.

The return type can often be inferred:

.. code-block:: easycrypt

   op double (x : int) = x + x.

Multiple arguments of the same type can share a type annotation:

.. code-block:: easycrypt

   op add3 (x y z : int) = x + y + z.

Pattern-matching definitions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Operators over algebraic datatypes can be defined by pattern matching
using ``with`` clauses:

.. code-block:: easycrypt

   type 'a option = [None | Some of 'a].

   op odflt (d : 'a) (ox : 'a option) : 'a =
     with ox = None   => d
     with ox = Some x => x.

   op omap (f : 'a -> 'b) (ox : 'a option) : 'b option =
     with ox = None   => None
     with ox = Some x => Some (f x).

The ``with`` clauses must be exhaustive: every constructor of the
datatype must appear. Nested patterns are supported.

Operator aliases
~~~~~~~~~~~~~~~~

You can declare multiple names for the same operator in one declaration:

.. code-block:: easycrypt

   op add, plus (x y : int) = x + y.

Here both ``add`` and ``plus`` refer to the same operator.

Polymorphic operators
~~~~~~~~~~~~~~~~~~~~~

Operators can be polymorphic. Type variables appearing in the arguments
or return type are universally quantified:

.. code-block:: easycrypt

   op id (x : 'a) : 'a = x.
   op const (x : 'a) (y : 'b) : 'a = x.

You can also declare type variables explicitly using brackets:

.. code-block:: easycrypt

   op id ['a] (x : 'a) : 'a = x.

This is useful when a type variable appears only in the return type,
not in any argument.

Operator symbols and infix notation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Operators can be given symbolic names for use in infix, prefix, or
mixfix position. Symbolic operator names are enclosed in parentheses
in their declaration:

.. code-block:: easycrypt

   op (+) (x y : int) : int.          (* infix  *)
   op ([-]) (x : int) : int.          (* prefix *)

In expressions, these are used in their natural position:

.. code-block:: easycrypt

   op example : int = 3 + 4.
   op negation : int = -5.

------------------------------------------------------------------------
Predicate declarations
------------------------------------------------------------------------

A predicate is like an operator that returns ``bool``.  The ``pred``
keyword is a convenience for declaring such operators.

Abstract predicates
~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   pred P : int.                 (* P : int -> bool *)
   pred R : int & int.           (* R : int -> int -> bool *)

Note: for predicates, multi-argument types are separated by ``&``,
not ``*`` or ``->``.

Concrete predicates
~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   pred is_positive (x : int) = 0 < x.
   pred in_range (lo hi x : int) = lo <= x /\ x < hi.

A ``pred`` definition is equivalent to an ``op`` definition with
return type ``bool``:

.. code-block:: easycrypt

   (* These two are equivalent: *)
   pred is_even (x : int) = x %% 2 = 0.
   op   is_even (x : int) : bool = x %% 2 = 0.

------------------------------------------------------------------------
Inductive predicates
------------------------------------------------------------------------

An *inductive predicate* defines a predicate as the smallest relation
closed under a set of rules. The syntax uses the ``inductive`` keyword:

.. code-block:: easycrypt

   inductive is_even : int -> bool =
     | Even0 : is_even 0
     | EvenSS (n : int) of is_even n : is_even (n + 2).

Each constructor corresponds to an introduction rule. The declaration
generates:

- The predicate itself.
- A constructor for each rule.
- An induction principle (elimination lemma).

Inductive predicates are especially useful for defining reachability
relations, well-formedness conditions, and similar recursive
properties.

------------------------------------------------------------------------
Abbreviations
------------------------------------------------------------------------

An *abbreviation* (``abbrev``) defines an operator that is
automatically unfolded during type-checking and proof search. It is
essentially a macro:

.. code-block:: easycrypt

   abbrev (<>) (x y : 'a) = !(x = y).

Abbreviations are transparent -- they are expanded wherever they
appear. They can be useful for notational convenience.

The ``[-printing]`` option prevents an abbreviation from being used
when EasyCrypt displays terms (so the expanded form is shown instead):

.. code-block:: easycrypt

   abbrev [-printing] fst (p : 'a * 'b) : 'a = p.`1.

With this option, EasyCrypt will display ``p.`1`` rather than
``fst p`` in goal output.

------------------------------------------------------------------------
Notations
------------------------------------------------------------------------

The ``notation`` command introduces syntactic sugar that is desugared
during parsing. Unlike abbreviations, notations can define arbitrary
mixfix syntax.

.. code-block:: easycrypt

   notation myif <- <-b, 'a-> b x y : 'a = if b then x else y.

Notations are an advanced feature primarily used in the standard
library. Most users do not need to define new notations.

------------------------------------------------------------------------
Locality
------------------------------------------------------------------------

Declarations can be prefixed with a *locality* modifier that controls
their visibility:

``local``
  The declaration is visible only within the current theory. It is
  not exported when the theory is required by another file.

  .. code-block:: easycrypt

     local op helper (x : int) = x + 1.

``declare``
  The declaration is *abstract within a section* and is automatically
  generalized when the section is closed. See
  :ref:`language-theories` for details on sections.

  .. code-block:: easycrypt

     declare op f : int -> int.

If no modifier is given, the declaration is *global*: it is visible
everywhere.
