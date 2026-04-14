.. _language-stdlib:

========================================================================
Standard library tour
========================================================================

EasyCrypt comes with a substantial standard library covering
mathematics, data structures, probability, algebra, and cryptographic
definitions. This chapter gives a guided tour of the most commonly
used theories.

Most EasyCrypt files start with:

.. code-block:: easycrypt

   require import AllCore.

which brings the core theories into scope. For specific needs, you
require additional theories.

.. contents::
   :local:

------------------------------------------------------------------------
AllCore
------------------------------------------------------------------------

``AllCore`` is the standard entry point. It re-exports:

- ``Core`` -- basic operations on pairs, options, functions.
- ``Int`` -- integer arithmetic (from ``CoreInt`` and others).
- ``Real`` -- real number arithmetic (from ``CoreReal`` and others).
- ``Xint`` -- extended integers (integers plus infinity).
- ``Ring.IntID`` -- the integer ring instance.

After ``require import AllCore``, you have access to:

- Pair operations: ``fst``, ``snd``.
- Option operations: ``oget``, ``omap``, ``obind``, ``odflt``,
  ``is_none``, ``is_some``.
- Function operations: ``idfun`` (identity), ``\o`` (composition),
  ``(==)`` (extensional equality).
- Map update syntax: ``f.[x <- v]``.
- Integer arithmetic: ``+``, ``-``, ``*``, comparisons.
- Real arithmetic: ``+``, ``-``, ``*``, ``/``, ``inv``.
- Extended integers: ``N`` (finite), ``+oo`` (infinity), operations.
- The ``witness`` constant (default value for any type).

------------------------------------------------------------------------
Lists
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import List.

The ``List`` theory provides the type ``'a list`` with:

Construction and destruction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``[]`` -- the empty list.
- ``::`` -- cons: ``x :: xs``.
- ``[x1; x2; ...]`` -- list literal syntax.
- ``head`` -- first element (with a default).
- ``behead`` -- tail of the list.

Measurement
~~~~~~~~~~~

- ``size xs`` -- length of a list.

Concatenation
~~~~~~~~~~~~~

- ``++`` -- append: ``xs ++ ys``.
- ``flatten`` -- concatenate a list of lists.

Access
~~~~~~

- ``nth d xs i`` -- element at index ``i``, default ``d``.
- ``last d xs`` -- last element.

Transformation
~~~~~~~~~~~~~~

- ``map f xs`` -- apply ``f`` to each element.
- ``filter p xs`` -- keep elements satisfying ``p``.
- ``zip xs ys`` -- pair up elements.
- ``unzip xs`` -- split a list of pairs.
- ``rev xs`` -- reverse.

Searching
~~~~~~~~~

- ``mem xs x`` (also ``x \in xs``) -- membership.
- ``has p xs`` -- does any element satisfy ``p``?
- ``all p xs`` -- do all elements satisfy ``p``?
- ``find p xs`` -- first element satisfying ``p``.
- ``count p xs`` -- number of elements satisfying ``p``.
- ``index x xs`` -- index of first occurrence.

Other
~~~~~

- ``undup xs`` -- remove duplicates.
- ``perm_eq xs ys`` -- ``xs`` and ``ys`` are permutations.
- ``iota_ i n`` -- the list ``[i; i+1; ...; i+n-1]``.
- ``range i j`` -- shorthand for ``iota_ i (j - i)``.
- ``nseq n x`` -- list of ``n`` copies of ``x``.
- ``mkseq f n`` -- ``[f 0; f 1; ...; f (n-1)]``.

------------------------------------------------------------------------
Finite sets and maps
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import FSet.
   require import FMap.
   require import SmtMap.

``FSet`` -- finite sets
~~~~~~~~~~~~~~~~~~~~~~~

The type ``'a fset`` represents a finite set. Key operations:

- ``fset0`` -- empty set.
- ``fset1 x`` -- singleton.
- ``x \in s`` -- membership.
- ``s1 `|` s2`` -- union.
- ``s1 `&` s2`` -- intersection.
- ``s1 `\` s2`` -- difference.
- ``card s`` -- cardinality.
- ``oflist xs`` -- set from a list.
- ``elems s`` -- list of elements.

``FMap`` -- finite maps
~~~~~~~~~~~~~~~~~~~~~~~

The type ``('a, 'b) fmap`` represents a finite map. Key operations:

- ``empty`` -- empty map.
- ``m.[x]`` -- lookup (returns ``'b option``).
- ``m.[x <- v]`` -- update.
- ``rem m x`` -- remove a key.
- ``dom m`` -- domain (as a finite set).
- ``rng m`` -- range (as a finite set).

``SmtMap`` -- SMT-friendly maps
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``SmtMap`` provides a simpler map type that works well with SMT
solvers. It is often preferred over ``FMap`` for straightforward
map reasoning because SMT can handle it more easily.

------------------------------------------------------------------------
Distributions
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import Distr.
   require import DBool.
   require import DInterval.

``Distr`` -- core distribution theory
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The type ``'a distr`` is built in. The ``Distr`` theory provides:

- ``mu d E`` -- probability of event ``E`` under distribution ``d``.
- ``mu1 d x`` -- probability of value ``x`` (point mass).
- ``support d x`` -- whether ``x`` has positive probability.
- ``is_lossless d`` -- total probability is exactly 1.
- ``is_full d`` -- every value has positive probability.
- ``is_uniform d`` -- all values in the support have equal
  probability.
- ``dmap d f`` -- push-forward: apply ``f`` to samples from ``d``.
- ``dlet d f`` -- monadic bind: sample from ``d``, then from
  ``f`` applied to the result.

``DBool`` -- boolean distributions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``dbool`` -- fair coin flip (uniform over ``{true, false}``).

``DInterval`` -- integer distributions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``[a..b]`` -- uniform distribution over integers from ``a`` to
  ``b`` (inclusive).

``DList`` -- distributions over lists
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``dlist d n`` -- sample ``n`` independent values from ``d``.

``DProd`` -- product distributions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``d1 `*` d2`` -- independent product of two distributions.

``DMap`` -- distribution mapping
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``dmap d f`` (also available in ``Distr``).

------------------------------------------------------------------------
Algebra
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import Ring.
   require import IntDiv.
   require import StdOrder.
   require import StdBigop.

``Ring`` -- abstract algebra
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defines abstract theories for:

- ``ZModule`` -- additive groups (with ``+``, ``-``, ``0``).
- ``ComRing`` -- commutative rings (adds ``*``, ``1``).
- ``IDomain`` -- integral domains.
- ``Field`` -- fields (adds division).

These are instantiated by cloning for concrete types like ``int`` and
``real``. The ``ring`` and ``field`` tactics use these instances.

``IntDiv`` -- integer division
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``(%/)`` -- Euclidean division.
- ``(%%)`` -- Euclidean modulo.
- ``(%|)`` -- divisibility predicate.
- ``gcd``, ``lcm`` -- greatest common divisor, least common multiple.

``StdOrder`` -- orderings
~~~~~~~~~~~~~~~~~~~~~~~~~

Provides abstract ordered types and clones for ``int`` and ``real``:

- ``IntOrder`` -- ordering lemmas for integers.
- ``RealOrder`` -- ordering lemmas for reals.

These bring ``<``, ``<=``, ``>``, ``>=`` along with a rich collection
of lemmas (monotonicity, transitivity, etc.).

``StdBigop`` -- big operators
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defines summation and products over lists and ranges:

- ``BIA.bigi`` -- big sum of integers: ``bigi predT f 0 n``
  computes ``f 0 + f 1 + ... + f (n-1)``.
- ``BRA.big`` -- big sum of reals.
- ``BIM.big`` -- big product.

------------------------------------------------------------------------
Finite types
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import FinType.
   require import Finite.
   require import Discrete.

``FinType`` -- enumerable finite types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The abstract theory ``FinType`` describes types with a finite number
of values.  You clone it providing:

- ``type t`` -- the type.
- ``op enum : t list`` -- a list of all values.

This gives you the cardinality (``card``) and uniform distribution
over the type (``dunifin``).

``Finite`` -- general finiteness
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

More general finiteness properties not requiring explicit enumeration.

``Discrete`` -- discrete types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Types with a ``witness`` and decidable equality.

------------------------------------------------------------------------
Cryptographic theories
------------------------------------------------------------------------

.. code-block:: easycrypt

   require import PROM.
   require import PKE.
   require import Hybrid.

The standard library includes theories defining standard
cryptographic concepts:

``PROM`` -- programmable random oracle model
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Provides abstract theories for random oracles that can be cloned
with your specific input/output types.

``PKE`` -- public-key encryption
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defines IND-CPA security games for public-key encryption schemes.

``PKS`` -- public-key signatures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defines EUF-CMA security games for signature schemes.

``Hybrid`` -- hybrid argument
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Provides a generic hybrid argument framework for reducing an
``n``-step distinguishing advantage to a single-step one.

``Commitment`` -- commitment schemes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Defines binding and hiding properties for commitment schemes.

------------------------------------------------------------------------
Discovering what is available
------------------------------------------------------------------------

To find lemmas and definitions in the standard library:

1. Use ``search`` with a pattern:

   .. code-block:: easycrypt

      search (size (_ ++ _)).

2. Use ``print`` to inspect a theory:

   .. code-block:: easycrypt

      print theory List.

3. Use ``locate`` to find where a name is defined:

   .. code-block:: easycrypt

      locate mem.

4. Read the source files in the ``theories/`` directory of the
   EasyCrypt installation. They are well-commented and serve as
   the definitive reference.
