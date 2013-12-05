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
module type Counter = {
  fun init(): unit {*}
  fun incr(): unit
}.

module Counter = {
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

(* A generic transform to turn any oracle into a counting oracle *)
module Count (O:Oracle) = {
  fun f(x:from): to = {
    var r:to;

    Counter.incr();
    r = O.f(x);
    return r;
  }
}.

section.
  declare module O:Oracle {Count}.

  lemma CountO_fL: islossless O.f => islossless Count(O).f.
  proof strict.
  by intros=> O_fL; fun;
     call O_fL;
     inline Counter.incr; wp.
  qed.

  lemma CountO_fC ci:
    islossless O.f =>
    bd_hoare[Count(O).f: Counter.c = ci ==> Counter.c = ci + 1] = 1%r.
  proof strict.
  by intros=> O_fL; fun;
     call O_fL;
     inline Counter.incr; wp.
  qed.

  equiv CountO_fC_E ci:
    Count(O).f ~ Count(O).f:
      ={Counter.c, x, glob O} /\ Counter.c{1} = ci ==>
      ={Counter.c, res, glob O} /\ Counter.c{1} = ci + 1.
  proof strict.
  by fun; inline Counter.incr;
     call (_: true); wp.
  qed.

  equiv CountO_O: Count(O).f ~ O.f: ={glob O, x} ==> ={glob O, res}.
  proof strict.
  by fun*; inline Count(O).f Counter.incr; wp;
     call (_: true); wp.
  qed.
end section.

(* The adversary tries to distinguish between two implementations of f *)
module type Adv(O:Oracle) = {
  fun distinguish(): bool
}.

module IND (O:Oracle, A:Adv) = {
  module A = A(O)

  fun main(): bool = {
    var b:bool;

    Counter.init();
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

  module Enforce(O:Oracle) = {
    fun f(x:from): to = {
      var r:to = default;

      if (Counter.c < bound)
        r = O.f(x);
      return r;
    }
  }.

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.

    declare module A:Adv {Count(O)}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.

    lemma event_wrap &m:
      Pr[IND(Count(O),A).main() @ &m: res /\ Counter.c <= bound] <= Pr[IND(Enforce(Count(O)),A).main() @ &m: res].
    proof strict.
    equiv_deno (_: ={glob A, glob O} ==> Counter.c{1} <= bound => res{1} = res{2})=> //; last smt.
    symmetry; fun.
    call (_: !Counter.c <= bound, ={glob Counter, glob O}, Counter.c{1} <= bound).
      (* A lossless *)
      by apply A_distinguishL.
      (* Enforce(Count(O)).f ~ Count(O) *)
      fun*; inline Enforce(Count(O)).f; case (Counter.c{2} = bound).
        rcondf{1} 3; first by progress; wp; skip; smt.
        exists* Counter.c{1}; elim* => c; call{2} (CountO_fC O c _); first by apply O_fL.
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Counter.c{2}; elim* => c; call (CountO_fC_E O c).
        by wp; skip; smt.
      (* Enforce(Count(O)).f lossless *)
      by progress; fun; sp; if=> //;
         inline Count(O).f Counter.incr; wp; call O_fL; wp; skip; smt.
      (* Count(O).f preserves bad *)
      intros=> &m1 //=; bypr; intros=> &m0 bad.
        cut: 1%r <= Pr[Count(O).f(x{m0}) @ &m0: bound < Counter.c]; last smt.
        cut lbnd: bd_hoare[Count(O).f: Counter.c = Counter.c{m0} ==> Counter.c = Counter.c{m0} + 1] >= 1%r;
          first by conseq (CountO_fC O Counter.c{m0} _); apply O_fL.
        by bdhoare_deno lbnd=> //; smt.
    by inline Counter.init; wp; skip; smt.
    qed.
  end section.
end Event.

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

      if (Counter.c < bound)
        r = O.f(x);
      return r;
    }
  }.

  module WrapAdv (A:Adv, O:Oracle) = A(Wrap(O)). 

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.

    declare module A:Adv {Count(O)}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.

    lemma wrapAdv_bnd:
      bd_hoare[WrapAdv(A,Count(O)).distinguish: Counter.c = 0 ==> Counter.c <= bound] = 1%r.
    proof strict.
      fun (Counter.c <= bound)=> //; first by smt.
        by apply A_distinguishL.
      by fun; sp; if;
           [exists* Counter.c; elim* => c; call (CountO_fC O c _); first apply O_fL |];
         skip; smt.
    qed.

    lemma event_bndAdv &m:
      Pr[IND(Count(O),A).main() @ &m: res /\ Counter.c <= bound] <= Pr[IND(Count(O),WrapAdv(A)).main() @ &m: res].
    proof strict.
    equiv_deno (_: ={glob A, glob O} ==> Counter.c{1} <= bound => ={res, glob Count})=> //; last smt.
    symmetry; fun.
    call (_: bound < Counter.c, ={glob Counter, glob Wrap, glob O}).
      (* A lossless *)
      by apply A_distinguishL.
      (* Wrap(O).f ~ O.f *)
      fun*; inline Wrap(Count(O)).f; case (Counter.c{1} = bound).
        rcondf{1} 3; first by progress; wp.
        exists* Counter.c{2}; elim* => c; call{2} (CountO_fC O c _);
          first apply O_fL.
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Counter.c{2}; elim* => c; call (CountO_fC_E O c).
        by wp.
      (* Wrap(O).f lossless *)
      by progress; fun; sp; if; [call (CountO_fL O _); first apply O_fL |].
      (* O.f preserves bad *)
      progress; bypr; intros=> &m0 bad.
      cut: 1%r <= Pr[Count(O).f(x{m0}) @ &m0: bound < Counter.c]; last smt.
      cut lbnd: bd_hoare[Count(O).f: Counter.c = Counter.c{m0} ==> Counter.c = Counter.c{m0} + 1] >= 1%r;
        first by conseq (CountO_fC O Counter.c{m0} _); first apply O_fL.
      by bdhoare_deno lbnd; last smt.
    inline Counter.init; wp.
    by skip; smt.
    qed.
  end section.
end StaticWrap.
