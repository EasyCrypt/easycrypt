========================================================================
Command: `bind`
========================================================================

The ``bind`` family of commands declares a correspondence between
EasyCrypt objects and their counterparts in the boolean-circuit world
used by the `circuit` family of tactics.

Four variants are available:

- ``bind bitstring`` — declares that a type is a fixed-size bitstring,
  by giving an isomorphism with ``bool list`` together with conversions
  from/to (signed and unsigned) integers.

- ``bind array`` — declares that a polymorphic type constructor is a
  fixed-size array, by giving access/update operators plus an
  isomorphism with ``list``. The element type need not be a bitstring
  at the time of binding, but it must become one whenever the array
  type is used at a circuit-translated site.

- ``bind op`` — declares that a user-defined operator implements one
  of a fixed catalog of bitvector/array primitives (corresponding to
  the operators of the QFABV theory of SMT-LIB). A monomorphic and a
  multi-type form are available.

- ``bind circuit`` — asserts that a user-defined operator is
  semantically equivalent to a circuit definition given in the
  low-level specification (``.spec``) language. **These bindings are
  trusted and become part of the TCB** (see the warning below).

Each variant may be prefixed with the locality modifier ``local`` or
``global``, with the usual section-locality semantics. The default,
inside a section, is to be exported; outside a section the modifier is
ignored.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: ``bind bitstring``
------------------------------------------------------------------------

.. admonition:: Syntax

  ``bind bitstring`` *to_bits* *from_bits* *to_uint* *to_sint* *of_int* *type* *size* ``.``

The seven arguments are: the two halves of the ``type ↔ bool list``
isomorphism (``to_bits``, ``from_bits``), the two integer projections
(``to_uint`` for the unsigned reading and ``to_sint`` for the
two's-complement signed reading), the integer injection
(``of_int``), the type being bound, and its size in bits (an integer
formula).

.. ecproof::
   :title: Bitstring Binding Example

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   (*$*) bind bitstring
     to_bits
     from_bits
     to_uint
     to_sint
     of_int
     W8
     8.

   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

The command leaves seven side conditions to be discharged via
``realize`` (in this example with ``admit``; in practice they should
be proved from the type's defining equations). The axioms are those of
the abstract ``BV`` theory in ``theories/datatypes/QFABV.ec``:

.. list-table::
   :header-rows: 1
   :widths: 18 82

   * - Axiom
     - Statement
   * - ``gt0_size``
     - ``0 < size``
   * - ``size_tolist``
     - ``size (tolist bv) = size`` (the list image has the expected length)
   * - ``tolistP``
     - ``oflist (tolist bv) = bv`` (round-trip via the list isomorphism)
   * - ``oflistP``
     - ``size xs = size => tolist (oflist xs) = xs`` (other direction, on lists of the right length)
   * - ``touintP``
     - ``touint bv = bs2int (tolist bv)`` (unsigned reading)
   * - ``tosintP``
     - two's-complement reading: ``tosint bv = touint bv`` when the MSB is 0, and ``touint bv - 2^size`` otherwise (with ``size = 1`` as a degenerate case)
   * - ``ofintP``
     - ``ofint i = oflist (int2bs size i)`` (integer injection is the inverse of ``bs2int`` on size-many bits)

------------------------------------------------------------------------
Variant: ``bind array``
------------------------------------------------------------------------

.. admonition:: Syntax

  ``bind array`` *get* *set* *tolist* *oflist* *type* *size* ``.``

The six arguments are: read/write operators (``get`` of type
``'a t -> int -> 'a`` and ``set`` of type ``'a t -> int -> 'a -> 'a
t``), the two halves of the ``type ↔ list`` isomorphism (``tolist``,
``oflist``), the (polymorphic) type constructor being bound, and the
array length.

.. ecproof::
   :title: Array Binding Example

   require import AllCore List QFABV.

   theory Array8.
   type 'a t.

   op tolist : 'a t -> 'a list.
   op oflist : 'a -> 'a list -> 'a t.
   op "_.[_]" : 'a t -> int -> 'a.
   op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.

   end Array8.

   (*$*) bind array Array8."_.[_]" Array8."_.[_<-_]" Array8.tolist Array8.oflist Array8.t 8.
   realize gt0_size by auto.
   realize tolistP by admit.
   realize oflistP by admit.
   realize eqP by admit.
   realize get_setP by admit.
   realize get_out by admit.

The command leaves six side conditions to be discharged. The axioms
are those of the abstract ``A`` theory in
``theories/datatypes/QFABV.ec``:

.. list-table::
   :header-rows: 1
   :widths: 18 82

   * - Axiom
     - Statement
   * - ``gt0_size``
     - ``0 < size``
   * - ``tolistP``
     - ``to_list a = mkseq (fun i => get a i) size`` (the list view is the canonical enumeration)
   * - ``oflistP``
     - for indices ``0 <= i < size``, ``nth dfl xs i = get (of_list dfl xs) i`` (the list-to-array constructor preserves indexing in range)
   * - ``eqP``
     - extensional equality: two arrays are equal iff they agree at every in-range index
   * - ``get_setP``
     - ``get (set a j v) i`` is ``v`` if ``i = j``, else ``get a i`` (in-range)
   * - ``get_out``
     - out-of-range reads agree across all arrays (i.e. the value at an out-of-range index is unspecified-but-uniform)

------------------------------------------------------------------------
Variant: ``bind op``
------------------------------------------------------------------------

.. admonition:: Syntax

  | ``bind op`` *type* *operator* ``"`` *name* ``" .``
  | ``bind op [`` *type₁* ``&`` *type₂* ``&`` … ``]`` *operator* ``"`` *name* ``" .``

The first (monomorphic) form is for operators whose signature mentions
a single bound type. The second (multi-type) form takes a
``&``-separated list of types inside brackets and is needed for
operators whose signature mixes types — for instance ``get`` (a
bitstring and a single-bit bitstring) or ``ainit`` (a bitstring index
type and an array element type).

The ``name`` string must be one of the operator catalog below.

.. ecproof::
   :title: Operator Binding Example (monomorphic)

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring
     to_bits
     from_bits
     to_uint
     to_sint
     of_int
     W8
     8.

   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op (+^) : W8 -> W8 -> W8.

   (*$*) bind op W8 (+^) "xor".
   realize bvxorP by admit.

.. ecproof::
   :title: Operator Binding Example (multi-type)

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring
     to_bits
     from_bits
     to_uint
     to_sint
     of_int
     W8
     8.

   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op bool2bits (b : bool) : bool list = [b].
   op bits2bool (b : bool list) : bool = List.nth false b 0.
   op i2b : int -> bool.
   op b2si (b : bool) = 0.

   bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
   realize gt0_size by done.
   realize size_tolist by auto.
   realize tolistP by auto.
   realize oflistP by rewrite /bool2bits /bits2bool; smt(size_eq1).
   realize touintP by admit.
   realize tosintP by done.
   realize ofintP by admit.

   op "_.[_]" : W8 -> int -> bool.

   (*$*) bind op [W8 & bool] "_.[_]" "get".
   realize le_size by auto.
   realize eq1_size by auto.
   realize bvgetP by admit.

The ``[W8 & bool]`` syntax names the two bitstring types involved in
``get``'s signature: the bitvector being indexed, and the single-bit
bitvector holding the extracted bit. Since ``bool`` is a primitive
type, it must itself be ``bind bitstring``-bound (to size 1) before
it can appear in a multi-type ``bind op``.

Each ``bind op`` leaves a single side condition of the form
``bv<name>P``, stating the semantics of the operator (e.g. ``bvxorP``
for ``xor``, ``bvgetP`` for ``get``). Multi-type bindings may also
leave size-relation side conditions, e.g. ``le_size`` (one bitstring
size bounds another), ``eq1_size`` (a bitstring has size one). These
all come from the corresponding sub-theories of ``BVOperators`` in
``theories/datatypes/QFABV.ec``.

Only this base catalog of operators needs an explicit binding.
Operators built on top of them are translated into circuits by
recursive descent through their definitions, applying the bindings at
the leaves and composing the resulting sub-circuits.

Operator catalog
~~~~~~~~~~~~~~~~

The ``name`` argument to ``bind op`` must be one of the following.
The "Types" column shows the shape of the bracketed type list expected
by the multi-type form (``BV`` = a bitstring type, ``BV[1]`` = a
bitstring type of size 1, ``A`` = an array type); single-``BV``
operators may also be given to the monomorphic form.

Arithmetic (one ``BV`` argument):

``add``, ``sub``, ``mul``, ``opp``
  signed-wrap arithmetic on bitvectors of size ``n``.
``udiv``, ``urem``, ``sdiv``, ``srem``
  unsigned and signed division and remainder.

Bitwise (one ``BV`` argument):

``and``, ``or``, ``xor``, ``not``
  pointwise boolean operations.

Constant shifts (one ``BV`` argument):

``shl``, ``shr``, ``ashr``
  shift left, logical shift right, arithmetic (sign-extending) shift right.
``rol``, ``ror``
  rotate left, rotate right.

Variable shifts (``BV & BV`` — value, amount):

``shls``, ``shrs``, ``ashrs``
  shift left / logical shift right / arithmetic shift right where the
  shift amount is itself a bitvector.

Comparisons (``BV[1] & BV`` — result and operand):

``ult``, ``ule``, ``slt``, ``sle``
  unsigned and signed strict and non-strict ordering, returning a
  one-bit bitvector.

Size manipulation (``BV & BV`` — source and target sizes):

``zextend``, ``sextend``
  zero- and sign-extension to a wider bitvector.
``truncate``
  truncation to a narrower bitvector.
``insert``, ``extract``, ``aextract``
  insert/extract a sub-bitvector; ``aextract`` is the
  arithmetic-extracting variant.
``concat`` (``BV & BV & BV``)
  concatenation of two bitvectors.

Bit-level indexing:

``init`` (``BV[1] & BV``)
  build a bitvector from a function ``int -> bit``.
``get`` (``BV & BV[1]``)
  extract a single bit at a given index.

Array primitives:

``ainit`` (``BV & A``)
  build an array of bitvectors from a function ``int -> BV``.
``asliceget`` (``BV & BV & A``), ``asliceset`` (``BV & BV & A``)
  read/write a sub-bitvector slice spanning array cells.
``a2b`` (``BV & BV & A``), ``b2a`` (``BV & BV & A``)
  reshape between a single wide bitvector and an array of bitvectors
  whose concatenation has the same width.
``map`` (``BV & BV & A``)
  pointwise map of a bitvector function over an array of bitvectors.

------------------------------------------------------------------------
Variant: ``bind circuit``
------------------------------------------------------------------------

.. admonition:: Syntax

  ``bind circuit`` *op₁* ``<- "`` *name₁* ``" ,`` … ``,`` *opₖ* ``<- "`` *nameₖ* ``" from "`` *file* ``" .``

A non-empty comma-separated list of ``op <- "name"`` associations is
followed by a mandatory ``from "<file>"`` clause naming the
``.spec`` file from which the named circuit definitions are loaded.

.. warning::

  The equivalences declared by ``bind circuit`` are **trusted**: no
  proof obligation is generated, and so an incorrect binding silently
  becomes part of the trusted computing base of every proof that
  uses it. Use ``bind op`` whenever possible. The recommended use of
  ``bind circuit`` is to attach circuit semantics to operators that
  are otherwise abstract, treating the binding as an axiomatisation
  rather than as a definition — proofs about the operator are then
  discharged via the ``circuit`` tactic, which makes use of these
  semantics.

A typical use looks like the following (this example is shown as
plain text rather than as a checked proof because it depends on a
spec file outside the example's working directory)::

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring
     to_bits from_bits to_uint to_sint of_int W8 8.
   (* ... realize side conditions ... *)

   op (+^) : W8 -> W8 -> W8.

   bind circuit
     (+^) <- "BVXOR_8" from "specs.spec".

The definition of the ``BVXOR_8`` circuit, in the
companion ``specs.spec`` file, is::

  BVXOR_8(w1@8, w2@8) -> @8 =
    xor<8>(w1, w2)

Each ``op`` named in the binding list must already be declared, its
arity must match the corresponding spec definition, and every argument
and the return type must be ``bind bitstring``-bound to a bitstring of
the size declared in the spec.
