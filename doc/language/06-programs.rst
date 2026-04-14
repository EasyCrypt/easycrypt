.. _language-programs:

========================================================================
Programs
========================================================================

EasyCrypt has an imperative programming language for describing
algorithms. Programs live inside *modules* (see
:ref:`language-modules`): a module declares mutable global variables
and *procedures* that operate on them.

This chapter describes the statement language used inside procedures.
The focus is on the syntax of individual statements; modules
themselves are covered in the next chapter.

.. contents::
   :local:

------------------------------------------------------------------------
Procedures
------------------------------------------------------------------------

A procedure is declared inside a module with the ``proc`` keyword.
It has a name, parameters, a return type, and a body:

.. code-block:: easycrypt

   module M = {
     proc add (x y : int) : int = {
       var r : int;
       r <- x + y;
       return r;
     }
   }.

The body is a block of statements enclosed in braces.

The return type can be ``unit`` for procedures that do not return a
meaningful value.  In that case, the ``return`` statement can be
omitted.

------------------------------------------------------------------------
Variable declarations
------------------------------------------------------------------------

Local variables are declared at the beginning of a procedure body
with the ``var`` keyword:

.. code-block:: easycrypt

   var x : int;
   var y, z : bool;
   var r : int <- 0;     (* with initializer *)

Multiple variables of the same type can be declared together.
Variables can optionally be given an initial value with ``<-``.
Uninitialized variables start with an arbitrary value of their type.

Global (module-level) variables are declared inside a module but
outside any procedure:

.. code-block:: easycrypt

   module M = {
     var count : int          (* global variable *)

     proc incr () : unit = {
       count <- count + 1;
     }
   }.

Global variables persist across procedure calls and are part of the
module's state.

------------------------------------------------------------------------
Assignments
------------------------------------------------------------------------

A deterministic assignment stores a value in a variable:

.. code-block:: easycrypt

   x <- 42;
   x <- x + 1;
   (a, b) <- (b, a);     (* tuple assignment / swap *)

The left-hand side is a variable name (or a tuple of variable names
for simultaneous assignment).

------------------------------------------------------------------------
Random sampling
------------------------------------------------------------------------

The sampling statement draws a value from a distribution and stores
it in a variable:

.. code-block:: easycrypt

   x <$ d;

Here ``d`` is an expression of type ``'a distr``.  After the
statement, ``x`` holds a random value drawn according to ``d``.

Common distributions (from the standard library):

.. code-block:: easycrypt

   x <$ duniform l;        (* uniform over list l        *)
   b <$ dbool;             (* fair coin flip             *)
   n <$ [0..k-1];          (* uniform integer in range   *)

The ``<$`` operator is what makes EasyCrypt programs *probabilistic*.
All randomness must be introduced through sampling.

------------------------------------------------------------------------
Procedure calls
------------------------------------------------------------------------

A procedure call invokes a procedure and (optionally) stores the
result:

.. code-block:: easycrypt

   r <@ M.f(x, y);         (* call M.f, store result in r *)
   M.g();                   (* call M.g, discard result    *)

The ``<@`` operator indicates a procedure call (as opposed to ``<-``
for deterministic assignment or ``<$`` for sampling).

Tuple unpacking works on the left-hand side:

.. code-block:: easycrypt

   (a, b) <@ M.pair_proc(x);

------------------------------------------------------------------------
Conditionals
------------------------------------------------------------------------

.. code-block:: easycrypt

   if (condition) {
     (* then-branch statements *)
   } else {
     (* else-branch statements *)
   }

The ``else`` branch is optional.  Braces are mandatory even for
single-statement branches.

There is also an ``elif`` form:

.. code-block:: easycrypt

   if (x < 0) {
     r <- -1;
   } elif (x = 0) {
     r <- 0;
   } else {
     r <- 1;
   }

------------------------------------------------------------------------
While loops
------------------------------------------------------------------------

.. code-block:: easycrypt

   while (condition) {
     (* loop body *)
   }

The loop executes the body repeatedly as long as the condition holds.

.. note::

   EasyCrypt does not have a ``for`` loop construct.  Bounded
   iteration is typically done with a ``while`` loop and a counter,
   or at the logical level using recursion on lists or ranges.

------------------------------------------------------------------------
Pattern matching
------------------------------------------------------------------------

A ``match`` statement branches on the constructor of an algebraic
datatype:

.. code-block:: easycrypt

   match ox with
   | None => {
       r <- 0;
     }
   | Some x => {
       r <- x;
     }
   end;

Each branch is a block of statements.

------------------------------------------------------------------------
Exceptions
------------------------------------------------------------------------

EasyCrypt supports exceptions in the imperative fragment.

Declaring exceptions
~~~~~~~~~~~~~~~~~~~~

New exception constructors are declared at the top level:

.. code-block:: easycrypt

   exception Error.
   exception Timeout of int.

Exception constructors are values of type ``exn`` and can carry
arguments (like datatype constructors).

Raising exceptions
~~~~~~~~~~~~~~~~~~

The ``raise`` statement aborts the current procedure with an
exception:

.. code-block:: easycrypt

   raise Error;
   raise (Timeout 42);

Note: exception handling (``try``/``catch``) is limited in EasyCrypt.
Exceptions are mainly used as a modeling tool for certain
code-transformation arguments in proofs.

------------------------------------------------------------------------
Program variables vs. logical variables
------------------------------------------------------------------------

It is important to distinguish the two kinds of variables in
EasyCrypt:

**Program variables** are mutable.  They exist inside module
procedures and change as the program executes.  In formulas, they
refer to the value at a specific point in execution (initial state,
final state, left/right memory).

**Logical variables** are immutable.  They are bound by quantifiers
(``forall``, ``exists``), ``let`` expressions, or as parameters of
operators and lemmas.  They do not change.

In formulas, program variables can be tagged with a memory
(``x{1}``, ``x{2}``) to specify which execution point they refer to.
Logical variables never carry memory tags.

Inside a procedure body, all variables are program variables. In a
lemma statement or operator definition, all variables are logical.
The two worlds meet in pre- and postconditions of Hoare judgments,
where program variables refer to concrete execution state and logical
variables act as parameters or ghost state.

------------------------------------------------------------------------
Return values
------------------------------------------------------------------------

A procedure returns a value using the ``return`` statement:

.. code-block:: easycrypt

   proc f (x : int) : int = {
     return x + 1;
   }

In postconditions, the keyword ``res`` refers to the return value:

.. code-block:: easycrypt

   hoare[M.f : x = 5 ==> res = 6]

If a procedure does not have an explicit ``return``, the return value
is the last assigned value of the ``res`` local variable (implicitly
declared), or ``witness`` if nothing was assigned.
