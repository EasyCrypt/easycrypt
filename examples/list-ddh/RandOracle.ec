require import Map.
require import FSet.
require import Real.
require import Distr.

theory RandOracle.

  (* finite type of oracle inputs *)
  type from.
  const univ_from : from set.
  axiom univ_from_all_mem : forall (x : from), mem x univ_from.

  type to.

  op dsample : to distr.

  module type RO = {
    fun init() : unit
    fun query(x : from) : to
  }.

  (* Lazy random oracle: Values are sampled on demand. *)
  module LRO : RO = {
    var m : (from, to) map
    fun init() : unit = {
      m = Map.empty;
    }
    fun query(x : from) : to = {
      var y : to;
      if (! in_dom x  m) {
        y = $dsample;
        m = m.[x <- y];
      }
      return proj m.[x];
    }
  }.

  (* Fixed random oracle: All values are sampled in advance. *)
  module FRO : RO = {
    var m : (from, to) map
    fun init() : unit = {
      var x : from;
      var xs : from set;
      var y : to;
      m = Map.empty;
      xs = univ_from;
      while (xs <> FSet.empty) {
        x  = pick xs;
        xs = rm x xs;
        y  = $dsample;
        m = m.[ x <- y ];
      }
    }
    fun query(x : from) : to = {
      return proj m.[x];
    }
  }.

  type ro_user_from.
  type ro_user_to.

  module type RO_USER(RO : RO) = {
    fun f(x : ro_user_from) : ro_user_to
  }.

  module G(RO : RO, UF : RO_USER) = {
    module U = UF(RO)

    fun main(x : ro_user_from) : ro_user_to = {
      var r : ro_user_to;
      RO.init();
      r = U.f(x);
      return r;
    }
  }.

  lemma LRO_lossless_query:
    mu dsample cpTrue = 1%r => islossless LRO.query.
  proof strict.
  intros=> samp.
  fun.
    if.
      wp; rnd. smt.
    skip; smt.
    skip. smt.
  qed.

  lemma LRO_lossless_init:
    islossless LRO.init.
  proof strict.
  fun. wp; skip; smt.
  save.
  
  lemma FRO_lossless_query:
    islossless FRO.query.
  proof strict.
  fun. skip; smt.
  save.

  lemma FRO_lossless_init:
    mu dsample cpTrue = 1%r => islossless FRO.init.
  proof strict.
  intros=> dsamp.
  fun.
  while true (card xs).
  intros=> z.
  wp. rnd. smt.
  wp. skip.
  intros=> &hr H.
  elim H => noEmpty card. smt.
  wp. skip. progress. smt.
  save.

  (* We could prove this using the old 'eager' tactic *)
  axiom Lazy_Fixed_dh_equiv:
    forall (UF <: RO_USER),
      equiv [ G(LRO,UF).main ~ G(FRO,UF).main : true ==> ={glob UF} ].
(*  proof.
    intros UF.
    fun.
    inline LRO.init FRO.init.
    admit.
  save.*)

end RandOracle.
