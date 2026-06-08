========================================================================
Tactic: `circuit`
========================================================================

The ``circuit`` tactic discharges or simplifies goals over finite
types by translating them into boolean circuits and reasoning about
the resulting bit-level representation. It applies to three goal
shapes — first-order propositions, Hoare triples, and program
equivalences — and has two modes, ``circuit`` and ``circuit
simplify``.

``circuit`` attempts to close the current goal by translating it into
a boolean circuit and checking that the circuit is identically true.

``circuit simplify`` performs the same translation but does not close
the goal: instead, it rewrites the postcondition using bit-level
equalities derived from the circuit, leaving a simpler residual goal
to be discharged by other tactics.

The translation uses the type and operator bindings declared by the
``bind`` family of commands (see :doc:`bindings`). Every type
appearing in the goal must be ``bind bitstring`` or ``bind array``;
every operator must be ``bind op`` or ``bind circuit``, or definable
in terms of bound operators; and every program statement must be an
assignment whose right-hand side translates to a circuit.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: ``circuit`` (FOL)
------------------------------------------------------------------------

When the goal is a first-order proposition (i.e., not a Hoare or
equivalence judgement), ``circuit`` translates the formula directly
into a boolean circuit and checks that it is a tautology.

.. ecproof::
   :title: First-order example

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
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   lemma L (w1 w2 : W8) : w1 +^ w2 = w2 +^ w1.
   proof.
     (*$*) circuit.
   qed.

The equality ``w1 +^ w2 = w2 +^ w1`` is translated into a boolean
circuit parameterised by the bits of ``w1`` and ``w2`` and equal to
``true`` exactly when the two sides agree. The tactic closes the goal
by checking that this circuit is identically true — in effect, a
case-analysis over all assignments of the input bits, but performed
symbolically on the circuit structure.

The goal must contain no free type variables (the FOL case requires a
ground context).

------------------------------------------------------------------------
Variant: ``circuit`` (HL)
------------------------------------------------------------------------

When the goal is a Hoare triple, ``circuit`` translates the
precondition, the program, and the postcondition into circuits and
checks that the postcondition circuit is implied by the precondition
on every initial state.

.. ecproof::
   :title: Hoare logic example

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
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc f(w : W8) = {
       return w +^ w;
     }
   }.

   lemma L (w_ : W8) : hoare[M.f : w_ = w ==> res = of_int 0].
   proof.
     proc. (*$*) circuit.
   abort.

The execution proceeds in three phases:

1. **Precondition processing.** The precondition is split along its
   top-level conjunctions. Each equation of the form ``prog_var =
   expr`` (in either direction) is treated as a definition: it is
   added to the symbolic state and used to specialise the
   construction of all later circuits. Each remaining clause that
   translates to a boolean circuit is recorded as an antecedent;
   clauses that do not translate are silently dropped.

2. **Program translation.** The body is processed instruction by
   instruction, maintaining a mapping from each program variable to
   the circuit that computes its current value from the program's
   inputs. The inputs are the program variables (treated as
   universally quantified bit-vectors) together with any logical
   variables constrained by the precondition.

3. **Postcondition discharge.** The postcondition is split along its
   conjuncts; each conjunct is translated into a boolean circuit
   using the input-to-output map computed in phase 2. The tactic then
   checks that, on every input satisfying the precondition
   antecedents, every postcondition circuit is true.

When the goal is an equality, the postcondition is decomposed
bit-by-bit and the tactic looks for structurally identical
sub-conditions across the bits, sharing them so that each input bit
is examined only once.

------------------------------------------------------------------------
Variant: ``circuit`` (rHL)
------------------------------------------------------------------------

When the goal is a program equivalence (``equiv[M.f1 ~ M.f2 : pre
==> post]``), the tactic produces a separate input-to-output map for
each program, then checks that the postcondition relating the two
sides holds on every joint initial state satisfying the precondition.

.. ecproof::
   :title: Program equivalence example

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
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc f1(w1 w2 : W8) = {
       var a : W8;
       a <- w1 +^ w2;
       return a;
     }

     proc f2(w1 w2 : W8) = {
       var a : W8;
       a <- w2 +^ w1;
       return a;
     }
   }.

   lemma L : equiv[M.f1 ~ M.f2 : ={arg} ==> ={res}].
   proof.
     proc. (*$*) circuit.
   abort.

------------------------------------------------------------------------
Variant: ``circuit simplify``
------------------------------------------------------------------------

``circuit simplify`` runs the same translation as ``circuit`` (HL) but
does not attempt to close the goal. Instead, it rewrites the
postcondition using the bit-level equalities derived from the circuit
translation of the program, then normalises by callbyvalue reduction.
The result is a new Hoare triple with the same precondition and
program but a simplified postcondition, which can then be discharged
by ordinary tactics.

.. ecproof::
   :title: Simplification mode

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
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc test (a : W8, b : W8) = {
       var c : W8;
       c <- a +^ b;
       return c;
     }
   }.

   lemma L (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
   proof.
     proc. (*$*) circuit simplify. trivial.
   qed.

Here the original postcondition ``res = a_ +^ b_`` becomes ``true``
after the circuit-level simplification, which ``trivial`` then closes.
More generally, ``circuit simplify`` is useful as a preprocessing step
when the full ``circuit`` translation would succeed only on part of
the postcondition and other reasoning is needed for the rest.

``circuit simplify`` only applies to Hoare triples.

------------------------------------------------------------------------
Failure modes
------------------------------------------------------------------------

Both ``circuit`` and ``circuit simplify`` may fail in the following
ways:

``failed to verify postcondition``
  The translation succeeded but the resulting circuit is not a
  tautology — i.e., the postcondition is genuinely false on some
  input satisfying the precondition, or its translation was too weak
  to capture the property.

``exception(s) not supported``
  The Hoare triple's postcondition includes an
  exception-monad invariant component; the circuit translation
  handles only the pure (``inv``-empty) part of the goal.

``circuit solve failed with error: …`` (or ``Circuit simplify failed with error: …``)
  A ``CircError`` was raised during translation. The most common
  causes are: an operator with no ``bind op`` or ``bind circuit``
  binding; a type with no ``bind bitstring`` or ``bind array``
  binding; a program statement that is not a translatable
  assignment.

``Wrong goal shape``
  ``circuit simplify`` was invoked on a goal that is not a Hoare
  triple.

------------------------------------------------------------------------
Limitations
------------------------------------------------------------------------

- Program statements must be assignments whose right-hand sides
  translate into circuits. Control flow (``if``, ``while``, ``match``)
  and module/procedure calls are not handled — they must be
  eliminated (e.g. via unrolling or inlining) before ``circuit`` is
  invoked.
- Sampling statements (``<$``) and exception-raising statements are
  not supported.
- Every type appearing in the goal must be either ``bind
  bitstring``-bound to a concrete (non-abstract) size, or ``bind
  array``-bound with a bound element type.
- The FOL variant additionally requires that the goal has no free
  type variables.
- The cost of the equivalence check grows with the bit-width of the
  variables and the depth of the resulting circuit; goals over
  large bitstrings or with many independent inputs may be infeasible
  to check directly. ``circuit simplify`` and the ``extens`` tactical
  (see :doc:`extens`) are the usual escape hatches.

========================================================================
Tactic: ``proc change circuit``
========================================================================

``proc change circuit`` rewrites a contiguous run of program
statements into an alternative block, using circuit equivalence as the
soundness check. Unlike the regular ``proc change`` — which generates
a separate proof obligation for the equivalence of the two fragments
— ``proc change circuit`` discharges that obligation automatically
through the same machinery as the ``circuit`` tactic.

.. admonition:: Syntax

  ``proc change circuit`` *[bindings]*? *cpos* ``+`` *N* ``{`` *stmt* ``} .``

- *cpos* is the code position at which to begin rewriting.
- *N* is the number of source instructions to replace, starting at
  *cpos*.
- *stmt* is the replacement block, enclosed in braces.
- *[bindings]* (optional) introduces fresh local variables visible
  only inside the replacement block, using the standard
  ``[x : ty, …]`` syntax. This lets the new code use intermediate
  names that did not exist in the original procedure.

The equivalence check considers only those variables that are
**live** at the end of the rewritten region — i.e., read by the rest
of the procedure body or by the postcondition. Variables written by
the replacement block but never read again may freely differ.

.. ecproof::
   :title: Replacing a fragment with an equivalent one

   require import AllCore List QFABV.

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
     proc f (a : W8, b : W8) = {
       var c : W8;
       c <- a +^ b;
       return c;
     }
   }.

   lemma swap_xor_args (a_ b_ : W8) :
     hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
   proof.
     proc.
     (*$*) proc change circuit 1 + 1 { c <- b +^ a; }.
     circuit.
   qed.

The single instruction at code position ``1`` is replaced by
``c <- b +^ a``; the circuit-equivalence checker establishes that the
two fragments agree on the value of ``c``, which is the only variable
read downstream.

.. ecproof::
   :title: Introducing a fresh local

   require import AllCore List QFABV.

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
     proc f (a : W8, b : W8) = {
       var c : W8;
       c <- a +^ b;
       return c;
     }
   }.

   lemma with_fresh_local (a_ b_ : W8) :
     hoare[M.f : a_ = a /\ b_ = b ==> res = a_ +^ b_].
   proof.
     proc.
     (*$*) proc change circuit [d : W8] 1 + 1 { d <- a; c <- d +^ b; }.
     circuit.
   qed.

The ``[d : W8]`` binding introduces a fresh local that exists only
inside the replacement block; the original procedure body has no such
variable.

------------------------------------------------------------------------
Failure modes (``proc change circuit``)
------------------------------------------------------------------------

``statements are not circuit-equivalent``
  Both fragments translated into circuits, but the equivalence check
  failed. This means the rewrite is genuinely unsound on at least one
  live output. (Use ``fail proc change circuit …`` to assert that a
  rewrite is rejected — see ``tests/proc-change-circuit.ec`` for an
  example.)

``circuit-equivalence checker error: …``
  Translation of one of the fragments raised an exception. The
  typical cause is the same as for ``circuit``: an unbound operator,
  an unbound type, or a non-assignment instruction inside the
  region being replaced.

``exceptions not supported``
  The postcondition's exception-monad invariant is non-empty.
