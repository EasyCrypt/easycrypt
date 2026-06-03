========================================================================
Command: `bind`
========================================================================

The ``bind`` family of commands is used to allow translation of EasyCrypt
objects into boolean circuits for use in the `circuit` family of tactics.

We have the following possibilities for these commands:

- `bind bitstring`, which establishes a bijection between the given type
  and a type of fixed size bitstrings through given isomorphisms with lists
  of booleans (plus necessary side conditions)

- `bind array`, which establishes the bijection between the given type constructor
  (which must be polymorphic over a given type which must be bound to a 
  bitstring type in instantiations) and the type of arrays of a given fixed size.

- `bind op`, which establishes the semantic equivalence of the given operator to 
  a specified operator from a fixed list (detailed below), which roughly corresponds
  to the operators supported by the QFABV theory of SMTLib.

- `bind circuit`, which asserts the semantic equivalence of the given operator to 
  the one given by a definition in the low level specification (spec) language. 
  All equivalences establishes through this particular mean are trusted (rather than
  verified) and so become part of the TCB for the given proof.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: ``bind bitstring``
------------------------------------------------------------------------

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


Here we have an example of defining a type and establishing 
its equivalence with the type of bitstring of size 8, along 
with the side conditions needed to verify that equivalence.
Since we only give an abstract type, these side conditions 
are admitted, but in a real example they would need to be 
proven using the semantics of whatever type we were using.

------------------------------------------------------------------------
Variant: ``bind array`` 
------------------------------------------------------------------------

.. ecproof::
   :title: Array Binding Example

   require import AllCore List QFABV.

   theory Array8.
   type 'a t.

   op tolist : 'a t -> 'a list.
   op oflist : 'a list -> 'a t.
   op "_.[_]" : 'a t -> int -> 'a.
   op "_.[_<-_]" : 'a t -> int -> 'a -> 'a t.

   end Array8.

   (*$*) bind array Array8."_.[_]" Array8."_.[_<-_]" Array8.tolist Array8.oflist Array8.t 8.
   realize gt0_size by auto.
   realize tolistP by admit.
   realize eqP by admit.
   realize get_setP by admit.
   realize get_out by admit.


In this example, we can see how the correspondence is established
for a given polymorphic array type. As in the example above, we 
use an abstract type and admit the side conditions for simplicity
of presentation, but in a real case we would have to use the 
semantics of our array type in order to discharge these conditions.


------------------------------------------------------------------------
Variant: ``bind op`` 
------------------------------------------------------------------------

.. ecproof::
   :title: Operator Binding Example

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


Here we give an example of giving the semantic equivalence for 
an operator. We again instantiate this abstractly and admit the
side conditions for ease of exposition, assuming that in a real 
case the semantics of the operator itself would be used in order
to show that the conditions hold.

Of note that these bindings are only necessary for a base subset 
of operators, and further operators defined in terms of these basic
ones are translated through recursive descent through their definition,
usage of these base cases and a notion of composition for boolean circuits.


------------------------------------------------------------------------
Variant: ``bind circuit`` 
------------------------------------------------------------------------
.. ecproof::
   :title: Spec Binding Example

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

   (*$*) bind circuit 
      (+^) <- "BVXOR_8".

Here we have an example of attributing semantics coming from a 
low level specification language (spec) file to an operator.
We remark again that these equivalences are trusted and so a 
potential source of error and unsoundness. This will be subject
to change in the future, but until then the recommended way 
to use them is to be very careful or otherwise just bind 
operators which are abstract and use these bindings as an 
axiomatization (proving lemmas about these through the use 
of the circuit family of tactics which is able to make use
of these semantics).

The definition of the ``BVXOR_8`` operator in the spec language
is as follows::

  BVXOR_8(w1@8, w2@8) -> @8 =
    xor<8>(w1, w2)


..
  This is similar to what is done to establish a correspondence
  between the basic types and their counterparts in the SMTs.
