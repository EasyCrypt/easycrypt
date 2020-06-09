(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring.
require import StdRing StdOrder StdBigop FelTactic.
require (*--*) Mu_mem.
(*---*) import RField IntOrder RealOrder.

(** A non-negative integer q **)
op q : { int | 0 <= q } as ge0_q.

(** A type T equipped with its full uniform distribution **)
type T.

op uT: T distr.
op maxu : T.
axiom maxuP x: mu1 uT x <= mu1 uT maxu.

(** A module that samples in uT on queries to s **)
module Sample = {
  var l:T list

  proc init(): unit = {
    l <- [];
  }

  proc s(): T = {
    var r;

    r <$ uT;
    l <- r::l;
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

  lemma pr_Sample_le &m:
    Pr[Exp(Sample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l]
    <= (q^2)%r * mu1 uT maxu.
  proof.
    fel 1 (size Sample.l) (fun x, q%r * mu1 uT maxu) q (!uniq Sample.l) []=> //.
    + rewrite Bigreal.sumr_const count_predT size_range /=.
      rewrite ler_maxr 1:smt mulrA ler_wpmul2r 1:smt //.
      have ->: q^2 = q * q by rewrite (_:2 = 1 + 1) // exprS // expr1.
      by rewrite -fromintM le_fromint ler_wpmul2r 1:ge0_q /#.
    + by inline*; auto.
    + proc;wp; rnd (mem Sample.l); skip=> // /> &hr ???.
      have:= Mu_mem.mu_mem_le_size (Sample.l{hr}) uT (mu1 uT maxu) _.
      + by move=> x _;rewrite maxuP.
      move=> /ler_trans Hle;apply/Hle/ler_wpmul2r;smt (mu_bounded).
    by move=> c; proc; auto=> /#.
  qed.

  axiom A_bounded: hoare [A(Sample).a : size Sample.l = 0 ==> size Sample.l <= q].

  lemma pr_collision &m:
    Pr[Exp(Sample,A).main() @ &m: !uniq Sample.l]
    <= (q^2)%r * mu1 uT maxu.
  proof.
    cut ->: Pr[Exp(Sample,A).main() @ &m: !uniq Sample.l] =
            Pr[Exp(Sample,A).main() @ &m: size Sample.l <= q /\ !uniq Sample.l].
    + byequiv (_: ={glob A} ==> ={Sample.l} /\ size Sample.l{2} <= q)=> //=.
      conseq (_: _ ==> ={Sample.l}) _ (_: _ ==> size Sample.l <= q)=> //=;2:by sim.
      by proc;call A_bounded;inline *;auto.
    by apply (pr_Sample_le &m).
  qed.

end section.

(*** The same result using a bounding module ***)
module Bounder(S:Sampler) = {
  var c:int

  proc init(): unit = {
    S.init();
    c <- 0;
  }

  proc s(): T = {
    var r <- witness;

    if (c < q) {
      r <@ S.s();
      c <- c + 1;
    }
    return r;
  }
}.

module ABounder(S:ASampler) = {
  proc s(): T = {
    var r <- witness;

    if (Bounder.c < q) {
      r         <@ S.s();
      Bounder.c <- Bounder.c + 1;
    }
    return r;
  }
}.

module Bounded(A:Adv,S:ASampler) = {
  proc a(): unit = {
    Bounder.c <- 0;
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

  lemma pr_collision_bounded_oracles &m:
    Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq Sample.l]
    <= (q^2)%r * mu1 uT maxu.
  proof.
    cut ->: Pr[Exp(Bounder(Sample),A).main() @ &m: !uniq Sample.l] =
            Pr[Exp(Sample,Bounded(A)).main() @ &m: !uniq Sample.l].
    + byequiv (PushBound Sample A) => //.
    apply (pr_collision (Bounded(A)) _ _ &m).
    + move=> S HS;proc;call (A_ll (ABounder(S)) _);2:by auto.
      by proc;sp;if;auto;call HS.     
    proc; call (_: size Sample.l <= Bounder.c <= q).
    + proc;sp;if=>//;inline *;auto=> /#.
    auto;smt w=ge0_q.
  qed.

end section.
