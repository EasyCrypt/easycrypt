require import Map.
require import Distr.

type from.
type to.

op dsample : to distr. (* Distribution to use on the target type *)

(* A signature for random oracles from "from" to "to". *)
module type Oracle =
{
  fun init():unit
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

  module RO:Oracle = {
    var m:(from, to) map

    fun init():unit = {
      m = Map.empty;
    }
  
    fun o(x:from):to = {
      var y : to;
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

  lemma lossless_o:
    mu dsample cpTrue = 1%r => islossless RO.o.
  proof strict.
  by intros=> Hd; apply (termination_o 1%r).
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


(** Budget-tracking wrapper *)
require import FSet.
module Count(H:Oracle) = {
  var qs:from set

  fun init(): unit = {
    H.init();
    qs = FSet.empty;
  }

  fun o(x:from): to = {
    var r:to;
    qs = add x qs;
    r = H.o(x);
    return r;
  }

  fun queries(): int = {
    return card qs;
  }
}.

(** Query-tracking wrapper *)
require import Int.
module Index(H:Oracle) = {
  var qs:(int,from) map
  var qc:int

  fun init(): unit = {
    H.init();
    qs = Map.empty;
    qc = 0;
  }

  fun o(x:from): to = {
    var r:to;
    if (!in_rng x qs)
    {
      qs.[qc] = x;
      qc = qc + 1;
    }
    r = H.o(x);
    return r;
  }
}.

(** Query-numbering wrapper *)
module Number(H:Oracle) = {
  var qs:(from,int) map
  var qc:int

  fun init(): unit = {
    H.init();
    qs = Map.empty;
    qc = 0;
  }

  fun o(x:from): to = {
    var r:to;
    if (!in_dom x qs)
    {
      qs.[x] = qc;
      qc = qc + 1;
    }
    r = H.o(x);
    return r;
  }
}.