(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int Real Distr StdOrder.
(*---*) import RealOrder.

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
  proc * init(): unit {}
  proc incr(): unit
}.

module Counter = {
  var c:int

  proc init(): unit = { c <- 0; }
  proc incr(): unit = { c <- c + 1; }
}.

type from.
type to.

(* An abstract oracle if a function f from from to to. *)
module type Oracle = {
  proc f(x:from): to
}.

(* A generic transform to turn any oracle into a counting oracle *)
module Count (O:Oracle) = {
  proc f(x:from): to = {
    var r:to;

    Counter.incr();
    r <@ O.f(x);
    return r;
  }
}.

section.
  declare module O:Oracle {Count}.

  lemma CountO_fL: islossless O.f => islossless Count(O).f.
  proof strict.
  by move=> O_fL; proc;
     call O_fL;
     inline Counter.incr; wp.
  qed.

  lemma CountO_fC ci:
    islossless O.f =>
    phoare[Count(O).f: Counter.c = ci ==> Counter.c = ci + 1] = 1%r.
  proof strict.
  by move=> O_fL; proc;
     call O_fL;
     inline Counter.incr; wp.
  qed.

  equiv CountO_fC_E ci:
    Count(O).f ~ Count(O).f:
      ={Counter.c, x, glob O} /\ Counter.c{1} = ci ==>
      ={Counter.c, res, glob O} /\ Counter.c{1} = ci + 1.
  proof strict.
  by proc; inline Counter.incr;
     call (_: true); wp.
  qed.

  equiv CountO_O: Count(O).f ~ O.f: ={glob O, x} ==> ={glob O, res}.
  proof strict.
  by proc*; inline Count(O).f Counter.incr; wp;
     call (_: true); wp.
  qed.
end section.

(* The adversary tries to distinguish between two implementations of f *)
module type Adv(O:Oracle) = {
  proc distinguish(): bool
}.

module IND (O:Oracle, A:Adv) = {
  module A = A(O)

  proc main(): bool = {
    var b:bool;

    Counter.init();
    b <@ A.distinguish();
    return b;
  }
}.

section.
  declare module O:Oracle {Count}.
  axiom O_fL: islossless O.f.

  declare module A:Adv {Count(O)}.
  axiom A_distinguishL (O <: Oracle {A}):
    islossless O.f =>
    islossless A(O).distinguish.

  lemma IND_CountO_O &m (P: glob O -> glob A -> bool):
    Pr[IND(Count(O),A).main() @ &m: res /\ P (glob O) (glob A)] =
      Pr[IND(O,A).main() @ &m: res /\ P (glob O) (glob A)].
  proof strict.
  byequiv (_: ={glob A, glob O} ==> ={glob O, glob A, res})=> //; proc.
  call (_: ={glob O});
    first by proc*; inline Count(O).f Counter.incr; wp;
             call (_: true); wp.
  by inline Counter.init; wp.
  qed.
end section.

theory EnfPen.
  const bound:int.
  axiom leq0_bound: 0 <= bound.

  const default:to.

  module Enforce(O:Oracle) = {
    proc f(x:from): to = {
      var r:to <- default;

      if (Counter.c < bound)
        r <@ O.f(x);
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

    lemma enf_implies_pen &m:
      Pr[IND(Count(O),A).main() @ &m: res /\ Counter.c <= bound] <= Pr[IND(Enforce(Count(O)),A).main() @ &m: res].
    proof strict.
    byequiv (_: ={glob A, glob O} ==> Counter.c{1} <= bound => res{1} = res{2})=> //; last smt.
    symmetry; proc.
    call (_: !Counter.c <= bound, ={glob Counter, glob O}, Counter.c{1} <= bound).
      (* A lossless *)
      by apply A_distinguishL.
      (* Enforce(Count(O)).f ~ Count(O) *)
      proc*; inline Enforce(Count(O)).f; case (Counter.c{2} = bound).
        rcondf{1} 3; first by progress; wp; skip; smt.
        exists* Counter.c{1}; elim* => c; call{2} (CountO_fC O c _); first by apply O_fL.
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Counter.c{2}; elim* => c; call (CountO_fC_E O c).
        by wp; skip; smt.
      (* Enforce(Count(O)).f lossless *)
      by progress; proc; sp; if=> //;
         inline Count(O).f Counter.incr; wp; call O_fL; wp; skip; smt.
      (* Count(O).f preserves bad *)
      move=> &m1 //=; bypr; move=> &m0 bad.
        apply/ler_anti; rewrite andaE; split; first by smt w=mu_bounded.
        cut lbnd: phoare[Count(O).f: Counter.c = Counter.c{m0} ==> Counter.c = Counter.c{m0} + 1] >= 1%r;
          first by conseq [-frame] (CountO_fC O Counter.c{m0} _); apply O_fL.
        by byphoare lbnd=> //; smt.
    by inline Counter.init; wp; skip; smt.
    qed.
  end section.
end EnfPen.

theory PenBnd.
  const bound:int.
  axiom leq0_bound: 0 <= bound.

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.

    declare module A:Adv {Count(O)}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.
    axiom A_distinguishC:
      phoare[A(Count(O)).distinguish: Counter.c = 0 ==> Counter.c <= bound] = 1%r.
    axiom A_distinguishC_E:
      equiv[A(Count(O)).distinguish ~ A(Count(O)).distinguish:
              ={glob A, glob O, Counter.c} /\ Counter.c{1} = 0 ==>
              ={glob A, glob O, res, Counter.c} /\ Counter.c{1} <= bound].

    lemma pen_implies_bnd &m:
      Pr[IND(Count(O),A).main() @ &m: res] =
        Pr[IND(Count(O),A).main() @ &m: res /\ Counter.c <= bound].
    proof strict.
    by byequiv (_: ={glob O, glob A} ==> ={Counter.c, res} /\ Counter.c{1} <= bound)=> //;
       proc; call A_distinguishC_E;
       inline Counter.init; wp.
    qed.
  end section.
end PenBnd.

theory BndPen.
  const bound:int.
  axiom leq0_bound: 0 <= bound.

  const default:to.

  module Enforce(O:Oracle) = {
    proc f(x:from): to = {
      var r:to <- default;

      if (Counter.c < bound)
        r <@ O.f(x);
      return r;
    }
  }.

  module EnforcedAdv (A:Adv, O:Oracle) = A(Enforce(O)).

  section.
    declare module O:Oracle {Count}.
    axiom O_fL: islossless O.f.

    declare module A:Adv {Count(O)}.
    axiom A_distinguishL (O <: Oracle {A}):
      islossless O.f =>
      islossless A(O).distinguish.

    (* The adversary we build is bounded in both senses used above (for sanity) *)
    lemma enforcedAdv_bounded:
      phoare[EnforcedAdv(A,Count(O)).distinguish: Counter.c = 0 ==> Counter.c <= bound] = 1%r.
    proof strict.
      proc (Counter.c <= bound)=> //; first by smt.
        by apply A_distinguishL.
      by proc; sp; if;
           [exists* Counter.c; elim* => c; call (CountO_fC O c _); first apply O_fL |];
         skip; smt.
    qed.

    equiv enforcedAdv_bounded_E:
      EnforcedAdv(A,Count(O)).distinguish ~ EnforcedAdv(A,Count(O)).distinguish:
        ={glob A, glob O, Counter.c} /\ Counter.c{1} = 0 ==>
        ={glob A, glob O, res, Counter.c} /\ Counter.c{1} <= bound.
    proof strict.
    proc (={glob O, Counter.c} /\ Counter.c{1} <= bound)=> //; first smt.
    proc; sp; if=> //; inline Count(O).f Counter.incr; wp; call (_: true); wp; skip; smt.
    qed.

    (* Security against the bounded adversary implies penalty-style security  *)
    lemma bnd_implied_pen &m:
      Pr[IND(Count(O),A).main() @ &m: res /\ Counter.c <= bound] <=
       Pr[IND(Count(O),EnforcedAdv(A)).main() @ &m: res].
    proof strict.
    byequiv (_: ={glob A, glob O} ==> Counter.c{1} <= bound => ={res, glob Count})=> //; last smt.
    symmetry; proc.
    call (_: bound < Counter.c, ={glob Counter, glob Enforce, glob O}).
      (* A lossless *)
      by apply A_distinguishL.
      (* Wrap(O).f ~ O.f *)
      proc*; inline Enforce(Count(O)).f; case (Counter.c{1} = bound).
        rcondf{1} 3; first by progress; wp.
        exists* Counter.c{2}; elim* => c; call{2} (CountO_fC O c _);
          first apply O_fL.
        by wp; skip; smt.
        rcondt{1} 3; first by progress; wp; skip; smt.
        wp; exists* Counter.c{2}; elim* => c; call (CountO_fC_E O c).
        by wp.
      (* Wrap(O).f lossless *)
      by progress; proc; sp; if; [call (CountO_fL O _); first apply O_fL |].
      (* O.f preserves bad *)
      progress; bypr; move=> &m0 bad.
      cut: 1%r <= Pr[Count(O).f(x{m0}) @ &m0: bound < Counter.c]; last smt.
      cut lbnd: phoare[Count(O).f: Counter.c = Counter.c{m0} ==> Counter.c = Counter.c{m0} + 1] >= 1%r;
        first by conseq [-frame] (CountO_fC O Counter.c{m0} _); first apply O_fL.
      by byphoare lbnd; last smt.
    inline Counter.init; wp.
    by skip; smt.
    qed.
  end section.
end BndPen.
