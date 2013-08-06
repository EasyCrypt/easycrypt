require import Map.
require import Distr.

type from.
type to.

op dsample : to distr. (* Distribution to use on the target type *)

(* A signature for random oracles from "from" to "to". *)
module type Oracle =
{
  fun init():unit {*}
  fun o(x:from):to
}.

module type ARO = { fun o(x:from):to }.

module Correct(O:Oracle) = {
  fun call2(x:from): to * to = {
    var g, g':to;
    g = O.o(x);
    g' = O.o(x);
    return (g,g');
  }

  fun call1(x:from): to = {
    var g:to;
    g = O.o(x);
    return g;
  }
}.

theory ROM.
  require import FSet.
    import ISet.Finite.

  module RO:Oracle = {
    var m:(from, to) map
    var qs:from set

    fun init() : unit = {
      m = Map.empty;
      qs = FSet.empty;
    }
  
    fun o(x:from) : to = {
      var y : to;
      qs = add x qs;
      y = $dsample;
      if (!in_dom x m) m.[x] = y;
      return proj (m.[x]);
    }
  }.

  lemma lossless_init: islossless RO.init.
  proof strict.
  by fun; wp; skip.
  qed.

  lemma termination_o r:
    mu dsample cpTrue = r =>
    bd_hoare [RO.o: true ==> true] = r.
  proof.
  by intros=> r_def; fun; wp; rnd (cpTrue); wp.
  qed.

  (** There is currently no way of using termination_o to prove lossless_o *)
  lemma lossless_o:
    mu dsample cpTrue = 1%r => islossless RO.o.
  proof strict.
  by intros=> Hd; apply (termination_o 1%r).
  qed.

  lemma init_m_qs:
    bd_hoare [RO.init: true ==> dom RO.m == RO.qs] = 1%r.
  proof.
  by fun; wp; skip; progress; smt.
  qed.

  lemma o_m_qs r:
    mu dsample cpTrue = r =>
    bd_hoare [RO.o: dom RO.m == RO.qs ==>
                    dom RO.m == RO.qs] = r.
  proof.
  intros=> r_def; fun; wp; rnd (cpTrue); wp; skip; progress.
    by rewrite dom_set; smt.
    by smt.
  qed.

  lemma correct_RO: mu dsample cpTrue = 1%r =>
    equiv [Correct(RO).call2 ~ Correct(RO).call1: ={glob RO, x} ==> ={glob RO} /\ res{1} = (res,res){2}].
  proof.
  intros=> lossless; fun; inline RO.o;
  wp; rnd{1}; wp; rnd; wp; skip; smt.
  qed.
(* A more elegant, but more verbose, proof:
 (*fun; seq 1 1: (={glob RO, g, x} /\ (mem x RO.qs){1} /\ RO.m.[x]{1} = Some g{2}).
    exists* x{2}; elim* => x';
    call (_: ={glob RO, x} /\ x' = x{2} ==>
             ={glob RO, res} /\ (mem x' RO.qs){1} /\ RO.m.[x']{1} = Some res{2})=> //;fun;
    wp; rnd; wp; skip.
      by progress=> //; smt.
    exists* x{1}; elim* => x';
    exists* RO.qs{1}; elim* => qs;
    exists* RO.m{1}; elim* => m;
    call{1} (_: RO.m = m /\ RO.qs = qs /\ x = x' /\ in_dom x RO.m /\ mem x RO.qs ==>
                RO.m = m /\ RO.qs = qs /\ res = proj (RO.m.[x'])).
      fun; rcondf 3.
        by rnd; wp=> //.
        by rnd=> //; wp; skip; progress=> //; smt.
      by skip; progress=> //; [rewrite /in_dom  | ]; smt.
    qed.*)
*)
end ROM.
