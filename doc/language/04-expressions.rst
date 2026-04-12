.. _language-expressions:

========================================================================
Expressions
========================================================================

Expressions are the terms of the EasyCrypt logic. They denote values:
integers, booleans, functions, tuples, and so on. Expressions appear
in operator definitions, lemma statements, proof goals, and (in a
restricted form) inside programs.

This chapter covers the syntax and meaning of expressions. The
distinction between expressions and *formulas* (which add logical
connectives and quantifiers) is discussed in :ref:`language-formulas`.

.. contents::
   :local:

------------------------------------------------------------------------
Literals
------------------------------------------------------------------------

Integer literals
~~~~~~~~~~~~~~~~

Integer literals are written in decimal or hexadecimal:

.. code-block:: easycrypt

   42
   -3
   0
   0x1A2B

Real literals
~~~~~~~~~~~~~

Real literals use a decimal point or the ``%r`` suffix to coerce an
integer to a real:

.. code-block:: easycrypt

   3.14
   0.5
   1%r         (* the integer 1, coerced to real *)

Boolean literals
~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   true
   false

The unit value
~~~~~~~~~~~~~~

The sole value of type ``unit`` is:

.. code-block:: easycrypt

   tt

------------------------------------------------------------------------
Variables
------------------------------------------------------------------------

There are two kinds of variables in EasyCrypt.

**Logical variables** appear in operator definitions, lemma statements,
and quantifiers. They are immutable and range over all values of their
type. Logical variables are simply written by name:

.. code-block:: easycrypt

   x    y    key    msg

**Program variables** appear inside module procedures and in formulas
that refer to program state. They are discussed in
:ref:`language-programs` and :ref:`language-formulas`.

------------------------------------------------------------------------
Arithmetic and comparison operators
------------------------------------------------------------------------

The standard arithmetic operators are defined in the core libraries.
After ``require import AllCore``:

.. list-table::
   :header-rows: 1
   :widths: 15 30 30

   * - Operator
     - Type
     - Description
   * - ``+``
     - ``int -> int -> int``
     - Addition
   * - ``-``
     - ``int -> int -> int``
     - Subtraction
   * - ``*``
     - ``int -> int -> int``
     - Multiplication
   * - ``%%``
     - ``int -> int -> int``
     - Euclidean modulo (from ``IntDiv``)
   * - ``%/``
     - ``int -> int -> int``
     - Euclidean division (from ``IntDiv``)
   * - ``-`` (prefix)
     - ``int -> int``
     - Negation
   * - ``=``
     - ``'a -> 'a -> bool``
     - Equality (polymorphic)
   * - ``<>``
     - ``'a -> 'a -> bool``
     - Disequality
   * - ``<``
     - ``int -> int -> bool``
     - Strict less-than
   * - ``<=``
     - ``int -> int -> bool``
     - Less-or-equal
   * - ``>``
     - ``int -> int -> bool``
     - Strict greater-than
   * - ``>=``
     - ``int -> int -> bool``
     - Greater-or-equal

The same arithmetic operators are also available for ``real`` (after
importing the appropriate libraries).

------------------------------------------------------------------------
Boolean operators
------------------------------------------------------------------------

.. list-table::
   :header-rows: 1
   :widths: 15 30 30

   * - Operator
     - Type
     - Description
   * - ``!``
     - ``bool -> bool``
     - Negation (not)
   * - ``/\``
     - ``bool -> bool -> bool``
     - Conjunction (and)
   * - ``\/``
     - ``bool -> bool -> bool``
     - Disjunction (or)
   * - ``=>``
     - ``bool -> bool -> bool``
     - Implication
   * - ``<=>``
     - ``bool -> bool -> bool``
     - Equivalence (if and only if)
   * - ``&&``
     - ``bool -> bool -> bool``
     - Short-circuit and
   * - ``||``
     - ``bool -> bool -> bool``
     - Short-circuit or

The operators ``/\`` and ``&&`` both denote conjunction, and ``\/``
and ``||`` both denote disjunction. The difference is that ``&&`` and
``||`` are *short-circuit* (the second argument is not evaluated if
the first determines the result), while ``/\`` and ``\/`` are
symmetric. In practice, ``/\`` and ``\/`` are used in logical
formulas, while ``&&`` and ``||`` appear in programs.

------------------------------------------------------------------------
Tuples and projections
------------------------------------------------------------------------

Tuple expressions are written with parentheses and commas:

.. code-block:: easycrypt

   (1, true)               (* int * bool      *)
   (1, 2, 3)               (* int * int * int *)

Components are accessed by projection, written with a backtick and a
1-based index:

.. code-block:: easycrypt

   (1, true).`1            (* = 1    *)
   (1, true).`2            (* = true *)

For pairs, the standard library provides ``fst`` and ``snd``.

------------------------------------------------------------------------
Records
------------------------------------------------------------------------

Record values are constructed with ``{|`` and ``|}`` delimiters,
listing field assignments:

.. code-block:: easycrypt

   type point = { x : int; y : int; }.

   op origin : point = {| x = 0; y = 0; |}.

Fields are accessed with backtick-field syntax:

.. code-block:: easycrypt

   op get_x (p : point) : int = p.`x.

A record can be updated functionally using ``with``:

.. code-block:: easycrypt

   op move_right (p : point) : point = {| p with x = p.`x + 1; |}.

------------------------------------------------------------------------
Constructors and pattern matching
------------------------------------------------------------------------

Values of algebraic datatypes are built by applying constructors:

.. code-block:: easycrypt

   Some 42        (* : int option  *)
   None           (* : 'a option   *)
   Red            (* : color        *)

The ``match`` expression inspects a value of an algebraic datatype
and branches based on its constructor:

.. code-block:: easycrypt

   match ox with
   | None   => 0
   | Some x => x + 1
   end.

Patterns can be nested and can bind variables:

.. code-block:: easycrypt

   match ot with
   | Leaf           => 0
   | Node x Leaf _  => x
   | Node x _    _  => x + 1
   end.

The ``match`` must be exhaustive: every constructor must be covered.

------------------------------------------------------------------------
List syntax
------------------------------------------------------------------------

Lists have special syntactic support.  The empty list is ``[]`` and
the cons operator is ``::``:

.. code-block:: easycrypt

   []                       (* empty list      *)
   1 :: 2 :: 3 :: []        (* [1; 2; 3]       *)
   [1; 2; 3]                (* same as above    *)

List operations are provided by the ``List`` theory (see
:ref:`language-stdlib`).

------------------------------------------------------------------------
Let bindings
------------------------------------------------------------------------

A ``let`` expression introduces a local definition:

.. code-block:: easycrypt

   let x = 2 + 3 in x * x.        (* = 25 *)

Patterns are supported on the left-hand side:

.. code-block:: easycrypt

   let (x, y) = (1, 2) in x + y.  (* = 3 *)

------------------------------------------------------------------------
Conditionals
------------------------------------------------------------------------

The ``if-then-else`` expression selects between two branches based on
a boolean condition:

.. code-block:: easycrypt

   if 0 < x then x else -x.

The ``else`` branch is mandatory. Both branches must have the same
type.

------------------------------------------------------------------------
Lambda abstractions
------------------------------------------------------------------------

Anonymous functions are written with the ``fun`` keyword:

.. code-block:: easycrypt

   fun x => x + 1                     (* int -> int      *)
   fun (x : int) => x + 1             (* with annotation  *)
   fun x y => x + y                   (* int -> int -> int *)
   fun (x y : int) => x + y           (* with annotation   *)

Lambdas are first-class: they can be passed to operators, stored in
data structures, and returned from other operators.

.. code-block:: easycrypt

   op succ : int -> int = fun x => x + 1.

------------------------------------------------------------------------
Quantifiers
------------------------------------------------------------------------

Universal and existential quantifiers bind variables and range over
all values of their type:

.. code-block:: easycrypt

   forall (x : int), 0 <= x * x.
   exists (y : int), y * y = 4.

The parenthesized type annotation is optional when the type can be
inferred:

.. code-block:: easycrypt

   forall x, x = x.

Multiple variables can be bound at once:

.. code-block:: easycrypt

   forall (x y : int), x + y = y + x.

Quantifiers associate to the right and extend as far as possible:

.. code-block:: easycrypt

   forall x, forall y, x + y = y + x.
   (* is the same as *)
   forall (x y : int), x + y = y + x.

------------------------------------------------------------------------
Type annotations
------------------------------------------------------------------------

Any expression can be annotated with a type using a colon:

.. code-block:: easycrypt

   (42 : int)
   (fun x => x : int -> int)

Type annotations are useful for resolving ambiguities when EasyCrypt's
type inference cannot determine the type on its own, for instance with
polymorphic operators.

------------------------------------------------------------------------
Map operations
------------------------------------------------------------------------

EasyCrypt provides special syntax for functional map (association)
operations. Given a function ``f : 'a -> 'b``:

.. code-block:: easycrypt

   f.[x]            (* lookup: f x                        *)
   f.[x <- v]       (* update: fun y => if y = x then v else f y *)

These are defined in the ``Logic`` prelude and work on any function
type. The ``SmtMap`` and ``FMap`` theories provide more structured
map types with their own operations.
