require import Int.
require import Real.
require import Distr. (* We use core knowledge on probabilities *)

(* To apply the lemmas, you will need to rewrite
   your oracle to increment Count.c when called.
   This is a very simple transformation.
   However, note that each oracle needs to be treated
   separately by:
     1) refactoring to use Count,
     2) applying the relevant transform,
     3) refactoring to remove the use of Count.
   This is independent of any counting done inside the oracles. *)
module Count = {
  var c:int

  fun init(): unit = { c = 0; }
  fun incr(): unit = { c = c + 1; }
}.

type from.
type to.

(* An abstract oracle if a function f from from to to. *)
module type Oracle = {
  fun f(x:from): to
}.

(* The adversary tries to distinguish between two implementations of f *)
module type Adv(O:Oracle) = {
  fun distinguish(): bool
}.

module IND (O:Oracle, A:Adv) = {
  module A = A(O)

  fun main(): bool = {
    var b:bool;

    Count.init();
    b = A.distinguish();
    return b;
  }
}.

(** This theory allows transitions between enforcement-style
    and penalty-style bounds on the number of oracle queries *)
theory Event.
  const bound:int.
  axiom leq0_bound: 0 <= bound.

  const default:to.

  module Wrap(O:Oracle) = {
    fun f(x:from): to = {
      var r:to = default;

      if (Count.c < bound)
        r = O.f(x);
      return r;
    }
  }.

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.
    axiom O_fC ci: bd_hoare[O.f: Count.c = ci ==> Count.c = ci + 1] = 1%r.
    (* We really want to be able to prove this from the previous axiom and the basic equiv knowledge on O.f *)
    axiom O_fC_E ci: equiv[O.f ~ O.f: ={Count.c, x, glob O} /\ Count.c{1} = ci ==>
                                      ={Count.c, res, glob O} /\ Count.c{1} = ci + 1].

    declare module A:Adv {O, Count}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.

    lemma event_wrap &m:
      Pr[IND(O,A).main() @ &m: res /\ Count.c <= bound] = Pr[IND(Wrap(O),A).main() @ &m: res].
    proof strict.
    equiv_deno (_: ={glob A, glob O} ==> Count.c{1} <= bound /\ (Count.c{1} <= bound => ={res}))=> //; last smt.
    symmetry; fun.
    call (_: bound < Count.c, ={Count.c, glob O, glob Count}, Count.c{1} <= bound).
      (* A lossless *)
      by apply A_distinguishL.
      (* O.f ~ Wrap(O).f *)
      fun*; inline Wrap(O).f; case (Count.c{2} = bound).
        rcondf{1} 3; first by progress; wp; skip; smt.
        exists* Count.c{2}; elim* => c; call{2} (O_fC c).
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Count.c{2}; elim* => c; call (O_fC_E c).
        by wp; skip; smt.
      (* Wrap(O).f lossless *)
      by intros=> _ _; fun; sp; if; first call O_fL.
      (* O.f preserves bad *)
      intros=> &m1 //=; bypr; intros=> &m0 bad.
        cut: 1%r <= Pr[O.f(x{m0}) @ &m0: bound < Count.c]; last smt.
        cut lbnd: bd_hoare[O.f: Count.c = Count.c{m0} ==> Count.c = Count.c{m0} + 1] >= 1%r;
          first conseq (O_fC Count.c{m0}).
        by bdhoare_deno lbnd=> //; smt.
    call (_: true ==> ={glob Count} /\ Count.c{1} <= bound); first by fun; wp; skip; smt.
    by skip; smt.
    qed.
  end section.
end Event.

theory Static.
  section.
    (* declare const bound:int. *)
    const bound:int.
    axiom leq0_bound: 0 <= bound.

    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.
    axiom O_fC ci: bd_hoare[O.f: Count.c = ci ==> Count.c = ci + 1] = 1%r.
    (* We really want to be able to prove this from the previous axiom and the basic equiv knowledge on O.f *)
    axiom O_fC_E ci: equiv[O.f ~ O.f: ={Count.c, x, glob O} /\ Count.c{1} = ci ==>
                                      ={Count.c, res, glob O} /\ Count.c{1} = ci + 1].

    declare module A:Adv {O, Count}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.
    axiom AO_distinguishC:
      bd_hoare[A(O).distinguish: Count.c = 0 ==> Count.c <= bound] = 1%r.
    axiom AO_distinguishC_E:
      equiv[A(O).distinguish ~ A(O).distinguish:
        ={Count.c, glob O, glob A} /\ Count.c{1} = 0 ==>
        ={Count.c, glob O, glob A, res} /\ Count.c{1} <= bound].

    lemma bndAdv_event &m:
      Pr[IND(O,A).main() @ &m: res] = Pr[IND(O,A).main() @ &m: res /\ Count.c <= bound].
    proof strict.
    equiv_deno (_: ={glob A, glob O} ==> ={Count.c, res} /\ Count.c{1} <= bound)=> //; fun.
    call AO_distinguishC_E.
    by call (_: true ==> ={Count.c} /\ Count.c{1} = 0); first by fun; wp.
    qed.
  end section.
end Static.

(** Ideally, this theory would allow transitions between penalty-style
    bounds on the number of oracle queries and cryptographer-friendly
    static restrictions on the adversary. These obviously need to be
    checked when instantiating lemmas and should make for smooth-looking
    lemmas if we can get things to line up properly. *)
theory StaticWrap.
  const bound:int.
  axiom leq0_bound: 0 <= bound.

  const default:to.

  module Wrap(O:Oracle) = {
    fun f(x:from): to = {
      var r:to = default;

      if (Count.c < bound)
        r = O.f(x);
      return r;
    }
  }.

  module WrapAdv (A:Adv, O:Oracle) = A(Wrap(O)). 

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.
    axiom O_fC ci: bd_hoare[O.f: Count.c = ci ==> Count.c = ci + 1] = 1%r.
    (* We really want to be able to prove this from the previous axiom and the basic equiv knowledge on O.f *)
    axiom O_fC_E ci: equiv[O.f ~ O.f: ={Count.c, x, glob O} /\ Count.c{1} = ci ==>
                                      ={Count.c, res, glob O} /\ Count.c{1} = ci + 1].

    declare module A:Adv {O, Count}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.

    lemma wrapAdv_bnd:
      bd_hoare[WrapAdv(A,O).distinguish: Count.c = 0 ==> Count.c <= bound] = 1%r.
    proof strict.
      fun (Count.c <= bound)=> //; first by smt.
        by apply A_distinguishL.
      by fun; sp; if; [exists* Count.c; elim* => c; call (O_fC c) |].
    qed.

    lemma event_bndAdv &m:
      Pr[IND(O,A).main() @ &m: res /\ Count.c <= bound] = Pr[IND(O,WrapAdv(A)).main() @ &m: res].
    proof strict.
    equiv_deno (_: ={glob A, glob O} ==> ={res, glob Count} /\ Count.c{1} <= bound)=> //.
    symmetry; fun.
    call (_: bound < Count.c, ={glob Count, glob Wrap, glob O}).
      (* A lossless *)
      by apply A_distinguishL.
      (* Wrap(O).f ~ O.f *)
      fun*; inline Wrap(O).f; case (Count.c{1} = bound).
        rcondf{1} 3; first by progress; wp.
        exists* Count.c{2}; elim* => c; call{2} (O_fC c).
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Count.c{2}; elim* => c; call (O_fC_E c).
        by wp.
      (* Wrap(O).f lossless *)
      by progress; fun; sp; if; [call (O_fL) |].
      (* O.f preserves bad *)
      progress; bypr; intros=> &m0 bad.
      cut: 1%r <= Pr[O.f(x{m0}) @ &m0: bound < Count.c]; last smt.
      cut lbnd: bd_hoare[O.f: Count.c = Count.c{m0} ==> Count.c = Count.c{m0} + 1] >= 1%r;
        first by conseq (O_fC Count.c{m0}).
      by bdhoare_deno lbnd; last smt.
    call (_: true ==> ={glob Count} /\ Count.c{1} = 0);
      first by fun; wp.
    by skip; smt.
    qed.
  end section.
end StaticWrap.
