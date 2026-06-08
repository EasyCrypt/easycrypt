========================================================================
Tactical: `extens`
========================================================================

``extens`` is a tactical that performs an extensionality-style
case-split: it enumerates the concrete values of a finite quantity,
generates one subgoal per case, and runs a user-supplied tactic on
each generated subgoal. The original goal closes only when every
subgoal closes.

Two goal shapes are recognised, distinguished by the presence or
absence of the bracketed binder:

- A first-order proposition of the form ``all P (iota_ start len)``
  (over ``int``) — no binder. The split produces one subgoal ``P i``
  per integer ``i`` in the range ``[start, start+len)``.

- A Hoare triple ``hoare[M.f : pre ==> post]`` together with a binder
  ``[v]`` naming a program variable. The variable's type must be
  ``bind bitstring``-bound (see :doc:`bindings`). The split produces
  ``2^n`` Hoare triples (with ``n`` the bound bitstring size), in
  each of which the program variable ``v`` has been substituted by
  the corresponding ``of_int i`` everywhere — in the program, in the
  precondition, and in the postcondition.

In both cases the inner tactic is then run on each generated subgoal.
If a subgoal fails to close, the residual goal is reported as an
error.

.. admonition:: Syntax

  ``extens`` *[v]*? ``:`` *tactic*

The bracketed binder ``[v]`` is required for the Hoare-triple variant
(it picks the program variable to enumerate) and forbidden for the
``iota_`` variant.

The most common use is ``extens [v] : circuit`` (or, with
simplification first, ``extens [v] : (circuit simplify; ...)``).
The benefit over a bare ``circuit`` is that the per-case translation
sees a program in which one input has been replaced by a concrete
constant, which lets circuit translation succeed on programs whose
whole-input translation would fail or blow up.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: List enumeration over ``iota_``
------------------------------------------------------------------------

.. ecproof::
   :title: List-all enumeration example

   require import AllCore List QFABV IntDiv.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
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
   bind op [W8 & bool] "_.[_]" "get".
   realize le_size by auto.
   realize eq1_size by auto.
   realize bvgetP by admit.

   lemma W8_ext (a : W8) : all (fun i => a.[i] = a.[i]) (iota_ 0 8).
   proof.
     (*$*) extens : circuit.
   qed.

The goal ``all (fun i => a.[i] = a.[i]) (iota_ 0 8)`` is split into
eight independent subgoals (one per ``i`` in ``[0, 8)``), each of
which is then discharged by ``circuit``.

Both the ``start`` and ``len`` arguments of ``iota_`` must be ground
integer literals; ``extens`` rejects a non-constant range with
``Iota start should be constant`` or ``Iota length should be
constant``.

------------------------------------------------------------------------
Variant: Hoare-triple enumeration over a bitstring variable
------------------------------------------------------------------------

.. ecproof::
   :title: Hoare triple bitstring enumeration

   require import AllCore List QFABV IntDiv.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op (+^) : W8 -> W8 -> W8.
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc test (a : W8, b : W8) = {
       var c : W8;
       c <- a +^ b;
       return c;
     }
   }.

   lemma L (a_ b_ : W8) :
     hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
   proof.
     proc.
     (*$*) extens [a] : (wp; skip; smt()).
   qed.

The binder ``[a]`` picks the program variable to enumerate. Since
``a : W8`` is bound to an eight-bit bitstring, the tactic produces
``2^8 = 256`` Hoare triples in which ``a`` has been replaced by each
concrete value ``of_int i``; the supplied tactic
``wp; skip; smt()`` then closes each.

This pattern is most useful when the inner tactic is ``circuit``
itself: replacing one program input by a concrete constant often lets
the per-case circuit translation succeed even when the
whole-program circuit translation would not. The same example with
``circuit`` as the inner tactic:

.. ecproof::
   :title: Bitstring enumeration paired with ``circuit``

   require import AllCore List QFABV IntDiv.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.

   bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op (+^) : W8 -> W8 -> W8.
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc test (a : W8, b : W8) = {
       var c : W8;
       c <- a +^ b;
       return c;
     }
   }.

   lemma L (a_ b_ : W8) :
     hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
   proof.
     (*$*) by proc; extens [a] : circuit.
   qed.

The ``2^n`` blow-up makes this variant practical only for small bit
widths: ``n = 8`` already produces 256 subgoals, and the cost grows
exponentially.

------------------------------------------------------------------------
Failure modes
------------------------------------------------------------------------

``Wrong goal shape``
  The goal is neither ``all _ (iota_ _ _)`` nor a Hoare triple, or
  the binder presence does not match the goal shape (binder given on
  an ``iota_`` goal, or omitted on a Hoare triple).

``Failed to find var <name> in memory <m>``
  The bracketed binder names a variable that does not exist in the
  Hoare triple's memory.

``Failed to get size for type <τ>``
  The bracketed binder names a variable whose type is not
  ``bind bitstring``-bound (or is bound only abstractly, without a
  concrete size). Arrays are not currently supported for the binder.

``Iota start should be constant`` / ``Iota length should be constant``
  The ``iota_`` arguments are not ground integer literals.

``Unsupported List pattern``
  The list inside ``all`` is not of the form ``iota_ start len``.

``Failed to close goal: <residual>``
  The inner tactic ran on every subgoal but left at least one
  unclosed. The residual goal is reported as part of the error.
