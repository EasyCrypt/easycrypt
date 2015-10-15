(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Option.
require import Int.
require import Real.
require import Distr.
require import List.
require (*--*) Sum.
(*---*) import Monoid.

(** A non-negative integer q **)
op q:int.
axiom lt0q: 0 < q.

(** A type T equipped with its full uniform distribution **)
type T.

op uT: T distr.
axiom uT_ufT: is_uniform_over uT predT.

(** A module that samples in uT on queries to s **)
module Sample = {
  var l:T list

  proc init(): unit = {
    l = [];
  }

  proc s(): T = {
    var r;

    r = $uT;
    l = r::l;
    return r;
  }
}.

module type Sampler = {
  proc init(): unit
  proc s(): T
}.

(** Adversaries that may query an s oracle **)
module type ASampler = {
  proc s(): T
}.

module type Adv(S:ASampler) = {
  proc a(): unit
}.

(** And an experiment that initializes the sampler and runs the adversary **)
module Exp(S:Sampler,A:Adv) = {
  module A = A(S)

  proc main(): unit = {
    S.init();
    A.a();
  }
}.

(** Forall adversary A that makes at most q queries to its s oracle,
    the probability that the same output is sampled twice is bounded
    by q^2/|T|                                                        **)
section.
  declare module A:Adv {Sample}.
  axiom A_ll (S <: ASampler {A}): islossless S.s => islossless A(S).a.
  axiom A_bounded &m: size Sample.l{m} = 0 => Pr[A(Sample).a() @ &m: size Sample.l <= q] = 1%r.

  local hoare hl_A_bounded: A(Sample).a: size Sample.l = 0 ==> size Sample.l <= q.
  proof.
    hoare.
    phoare split ! 1%r 1%r=> //=.
      conseq (A_ll Sample _).
        by proc; auto=> //=; rewrite -/predT; smt. (* FIXME: -delta *)
    by bypr=> &m l_empty; rewrite (A_bounded &m l_empty).
  qed.

  local module BSample = {
    proc init = Sample.init

    proc s(): T = {
      var r = witness;

      if (size Sample.l < q) {
        r = $uT;
        Sample.l = r::Sample.l;
      }
      return r;
    }
  }.

  local equiv eq_Sample_BSample: Exp(Sample,A).main ~ Exp(BSample,A).main: ={glob A} ==> ={Sample.l}.
  proof.
    symmetry.
    proc.
    conseq (_: ={glob A} ==> size Sample.l{2} <= q => ={Sample.l}) _ (_: true ==> size Sample.l <= q); first 2 smt.
      call hl_A_bounded.
      by inline*; auto; smt.
    call (_: !size Sample.l <= q, ={Sample.l})=> //=.
      exact A_ll.
      by proc; sp; if{1}=> //=; auto; smt.
      by move=> &2 bad; proc; sp; if=> //=; auto; rewrite -/predT; smt. (* FIXME: -delta *)
      by proc; auto; rewrite -/predT; smt. (* FIXME: -delta *)
    by inline *; auto; smt.
  qed.

  local lemma pr_BSample &m:
    Pr[Exp(BSample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l]
    <= (q^2)%r * mu uT ((=) witness).
  proof.
    fel 1 (size Sample.l) (fun x, q%r * mu uT ((=) witness)) q (!uniq Sample.l) [BSample.s: (size Sample.l < q)]=> //.
      (* We love real arithmetic... NOT *)
      rewrite Sum.int_sum_const //= /Sum.intval FSet.Interval.card_interval_max.
      cut ->: max (q - 1 - 0 + 1) 0 = q by smt.
      cut ->: q^2 = q * q; last by smt.
      rewrite (_: 2 = 1 + 1) // -Int.pow_add //.
      by rewrite (_: q^1 = q) // (_: 1 = 0 + 1) 1:// powS // pow0.
      by inline*; auto; smt.
      proc; sp; if=> //; last by (hoare; auto; smt).
      wp; rnd (mem Sample.l); skip=> //=.
      progress.
        cut:= FSet.mu_Lmem_le_length (Sample.l{hr}) uT (mu uT (pred1 witness)) _.
        move=> x _; rewrite /mu_x; cut: mu uT (pred1 x) = mu uT (pred1 witness); last smt.
        have [uT_fu [_ uT_suf]]:= uT_ufT.
        by apply uT_suf; apply uT_fu.
        by smt.
        by move: H4; rewrite H0.
      by progress; proc; rcondt 2; auto; smt.
      by progress; proc; rcondf 2; auto.
  qed.

  lemma pr_collision &m:
    Pr[Exp(Sample,A).main() @ &m: !uniq Sample.l]
    <= (q^2)%r * mu uT ((=) witness).
  proof.
    cut ->: Pr[Exp(Sample,A).main() @ &m: !uniq Sample.l]
            = Pr[Exp(BSample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l].
      byequiv (_: ={glob A} ==> ={Sample.l} /\ size Sample.l{2} <= q)=> //=.
      conseq eq_Sample_BSample _ (_: _ ==> size Sample.l <= q)=> //=.
        proc.
        call (_: size Sample.l <= q).
          by proc; sp; if=> //=; auto; smt.
        by inline *; auto; smt.
    by apply (pr_BSample &m).
  qed.
end section.

(*** The same result using a bounding module ***)
(** TODO: factor out the second step of the proof (pr_BSample)
    and exercise some modularity **)
module Bounder(S:Sampler) = {
  var c:int

  proc init(): unit = {
    S.init();
    c = 0;
  }

  proc s(): T = {
    var r = witness;

    if (c < q) {
      r = S.s();
      c = c + 1;
    }
    return r;
  }
}.

module ABounder(S:ASampler) = {
  proc s(): T = {
    var r = witness;

    if (Bounder.c < q) {
      r = S.s();
      Bounder.c = Bounder.c + 1;
    }
    return r;
  }
}.

module Bounded(A:Adv,S:ASampler) = {
  proc a(): unit = {
    Bounder.c = 0;
    A(ABounder(S)).a();
  }
}.

equiv PushBound (S <: Sampler {Bounder}) (A <: Adv {S,Bounder}):
  Exp(Bounder(S),A).main ~ Exp(S,Bounded(A)).main:
    ={glob A,glob S} ==>
    ={glob A,glob S}.
proof. by proc; inline*; sim. qed.

(** Forall adversary A with access to the bounded s oracle, the
    probability that the same output is sampled twice is bounded by
    q^2/|T|                                                         **)
section.
  declare module A:Adv {Sample,Bounder}.

  axiom A_ll (S <: ASampler {A}): islossless S.s => islossless A(S).a.

  local module BSample = {
    proc init = Sample.init

    proc s(): T = {
      var r = witness;

      if (size Sample.l < q) {
        r = $uT;
        Sample.l = r::Sample.l;
      }
      return r;
    }
  }.

  local equiv eq_Sample_BSample: Exp(Bounder(Sample),A).main ~ Exp(BSample,A).main: ={glob A} ==> ={Sample.l}.
  proof.
    transitivity  Exp(Sample,Bounded(A)).main 
                  (={glob A,glob Sample} ==> ={glob A,glob Sample})
                  (={glob A} ==> ={Sample.l})=> //.
    + by progress; exists (glob A){2}, Sample.l{1}.
    + exact (PushBound Sample A).
    proc; inline*.
    call (_: ={glob Sample} /\ Bounder.c{1} = size Sample.l{1}).
      by proc; sp; if=> //; inline Sample.s; auto; smt.
    by auto.
  qed.

  local lemma pr_BSample &m:
    Pr[Exp(BSample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l]
    <= (q^2)%r * mu uT ((=) witness).
  proof.
    fel 1 (size Sample.l) (fun x, q%r * mu uT ((=) witness)) q (!uniq Sample.l) [BSample.s: (size Sample.l < q)]=> //.
      (* We love real arithmetic... NOT *)
      rewrite Sum.int_sum_const //= /Sum.intval FSet.Interval.card_interval_max.
      cut ->: max (q - 1 - 0 + 1) 0 = q by smt.
      cut ->: q^2 = q * q; last by smt.
      rewrite (_: 2 = 1 + 1) // -Int.pow_add //.
      by rewrite (_: q^1 = q) // (_: 1 = 0 + 1) 1:// powS // pow0.
      by inline*; auto; smt.
      proc; sp; if=> //; last by (hoare; auto; smt).
      wp; rnd (mem Sample.l); skip=> //=.
      progress.
        cut:= FSet.mu_Lmem_le_length (Sample.l{hr}) uT (mu uT (pred1 witness)) _.
        move=> x _; rewrite /mu_x; cut: mu uT (pred1 x) = mu uT (pred1 witness); last smt.
        have [uT_fu [_ uT_suf]]:= uT_ufT.
        by apply uT_suf; apply uT_fu.
        by smt.
        by move: H4; rewrite H0.
      by progress; proc; rcondt 2; auto; smt.
      by progress; proc; rcondf 2; auto.
  qed.

  lemma pr_collision_bounded_oracles &m:
    Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq Sample.l]
    <= (q^2)%r * mu uT ((=) witness).
  proof.
    cut ->: Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq Sample.l]
            = Pr[Exp(BSample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l].
      byequiv (_: ={glob A} ==> ={Sample.l} /\ size Sample.l{2} <= q)=> //=.
      conseq eq_Sample_BSample _ (_: _ ==> size Sample.l <= q)=> //=.
        proc.
        call (_: size Sample.l <= q).
          by proc; sp; if=> //=; auto; smt.
        by inline *; auto; smt.
    by apply (pr_BSample &m).
  qed.
end section.
