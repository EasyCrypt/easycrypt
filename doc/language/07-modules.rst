.. _language-modules:

========================================================================
Modules
========================================================================

Modules are the mechanism for packaging mutable state and procedures
together. They play a central role in EasyCrypt: cryptographic
schemes, adversaries, oracles, and security games are all modeled as
modules.

.. contents::
   :local:

------------------------------------------------------------------------
Module types
------------------------------------------------------------------------

A *module type* (also called a *signature* or *interface*) declares
the procedures a module must provide, without specifying their
implementation:

.. code-block:: easycrypt

   module type Adv = {
     proc guess(c : cipher) : key
   }.

This declares an interface ``Adv`` with a single procedure ``guess``
that takes a ``cipher`` and returns a ``key``.

Module types can declare several procedures:

.. code-block:: easycrypt

   module type Oracle = {
     proc init() : unit
     proc query(x : int) : int
   }.

Procedure declarations in a module type do not have bodies -- only
names, parameters, and return types.

Including other module types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A module type can include another module type to inherit its
procedure declarations:

.. code-block:: easycrypt

   module type ExtOracle = {
     include Oracle
     proc reset() : unit
   }.

This gives ``ExtOracle`` all the procedures of ``Oracle`` plus an
additional ``reset`` procedure.

A restriction clause can limit which procedures are included:

.. code-block:: easycrypt

   module type Limited = {
     include Oracle [query]    (* only include query, not init *)
   }.

------------------------------------------------------------------------
Concrete modules
------------------------------------------------------------------------

A concrete module implements a module type by providing variable
declarations and procedure bodies:

.. code-block:: easycrypt

   module M : Oracle = {
     var table : (int, int) fmap

     proc init() : unit = {
       table <- empty;
     }

     proc query(x : int) : int = {
       var r : int;
       r <$ [0..100];
       if (x \notin table) {
         table.[x] <- r;
       }
       return oget table.[x];
     }
   }.

The ``: Oracle`` annotation is optional. If present, EasyCrypt checks
that the module provides all procedures required by the module type.

Global variables (``var``) are part of the module's state. They
persist across procedure calls and can be read or written by any
procedure in the module.

------------------------------------------------------------------------
Functors
------------------------------------------------------------------------

A *functor* is a module that is parameterized by other modules.  This
is the standard way to model algorithms that interact with an
adversary or oracle.

.. code-block:: easycrypt

   module Game (A : Adv) (O : Oracle) = {
     proc main() : bool = {
       var k, k' : key;
       var c : cipher;

       O.init();
       k <$ dkey;
       c <- encrypt k m;
       k' <@ A.guess(c);
       return (k = k');
     }
   }.

Here ``Game`` is parameterized by an adversary ``A`` of type ``Adv``
and an oracle ``O`` of type ``Oracle``.  The procedures of ``A`` and
``O`` can be called inside the body of ``Game``.

Functors are *applied* (instantiated) by supplying concrete modules:

.. code-block:: easycrypt

   module ConcreteGame = Game(ConcreteAdv, ConcreteOracle).

The result ``ConcreteGame`` is a concrete module with no remaining
parameters.

------------------------------------------------------------------------
Module restrictions
------------------------------------------------------------------------

When a module type is used as a functor parameter, you often want to
restrict which other modules the parameter can access.  This prevents
an adversary from, say, calling an oracle it should not have access to.

Restrictions are specified with a set annotation on the module type:

.. code-block:: easycrypt

   module type Adv = {
     proc guess(c : cipher) : key
   }.

   module Game (A : Adv {-Game}) = { ... }.

The ``{-Game}`` restriction says that ``A`` must not access the
global state of ``Game``. The syntax ``{+M}`` means "may access M",
and ``{-M}`` means "must not access M".

More complex restrictions are possible:

.. code-block:: easycrypt

   module Game (A : Adv {-Game, +O}) (O : Oracle {-A}) = { ... }.

Here ``A`` may access ``O`` but not ``Game``, and ``O`` may not
access ``A``.

Restrictions are critical for the soundness of game-based proofs:
they ensure that adversaries interact only through the intended
interfaces.

------------------------------------------------------------------------
Abstract modules
------------------------------------------------------------------------

Inside a *section*, you can declare an abstract module -- a module
whose implementation is unknown but whose type is given:

.. code-block:: easycrypt

   section.
     declare module A <: Adv.
     (* ... lemmas about A ... *)
   end section.

The ``declare module`` statement introduces ``A`` as a module of type
``Adv`` without fixing its implementation.  This is analogous to an
abstract type: you can use ``A`` in procedure calls and formulas, but
you know nothing about it beyond what the module type guarantees.

When the section is closed, all lemmas that use ``A`` are
automatically universally quantified over all modules of type ``Adv``.

Abstract modules can also carry restrictions:

.. code-block:: easycrypt

   declare module A <: Adv {-Game, -O}.

------------------------------------------------------------------------
Module state
------------------------------------------------------------------------

The state of a module is the collection of its global variables. In
formulas, the expression ``glob M`` refers to the current value of
all global variables of module ``M`` (packaged as a tuple).

.. code-block:: easycrypt

   glob Game          (* the state of module Game *)
   glob A             (* the state of abstract module A *)

This is useful for writing pre- and postconditions:

.. code-block:: easycrypt

   equiv[Game(A).main ~ Game(A).main :
     ={glob A, glob Game} ==> ={res}].

The type of ``glob M`` depends on the variables declared in ``M``.
For abstract modules, the type is also abstract.

------------------------------------------------------------------------
Module expressions
------------------------------------------------------------------------

Beyond simple module names, EasyCrypt supports several forms of
module expressions:

Functor application
~~~~~~~~~~~~~~~~~~~

.. code-block:: easycrypt

   Game(A, O)

Applies a functor to its arguments.

Module restriction
~~~~~~~~~~~~~~~~~~

You can restrict a module in expressions to hide some of its
procedures:

.. code-block:: easycrypt

   module M' = M [query].

This creates a module that only exposes the ``query`` procedure of
``M``.
