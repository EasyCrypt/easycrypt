(* This module deals with random oracles.
   Note that we ignore the adversary wrapper for the random
   oracle that logs the queries and limits the number of queries
   since it is not required in our example.
*)
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
  qed.
  
  lemma FRO_lossless_query:
    islossless FRO.query.
  proof strict.
  fun. skip; smt.
  qed.

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
  qed.

  (** Switching between lazy and fixed random oracle *)

  type ro_user_from.
  type ro_user_to.


  (* A random oracle user *)
  module type RO_USER(RO : RO) = {
    fun init() : unit {}
    fun f(x : ro_user_from) : ro_user_to {RO.query}
  }.

  (* A module that initializes a random oracles and "runs" the random
     oracle user *)
  module G(RO : RO, UF : RO_USER) = {
    module U = UF(RO)

    fun main(x : ro_user_from) : ro_user_to = {
      var r : ro_user_to;
      U.init();
      RO.init();
      r = U.f(x);
      return r;
    }
  }.

  (* We could prove this using the old 'eager' tactic *)
  axiom Lazy_Fixed_dh_equiv(UF <: RO_USER{FRO,LRO}):
    equiv [ G(LRO,UF).U.init ~ G(FRO,UF).U.init : true ==> ={glob UF} ] =>
    equiv [ G(LRO,UF).main ~ G(FRO,UF).main : true ==> ={res, glob UF} ].

  (* If we could quantify over relations, then we could state the
     the following version which would directly work with modules UF
     that use adversaries because we could could instantiate
     rel with ={Glob A}.
  axiom Lazy_Fixed_dh_equiv(UF <: RO_USER{FRO,LRO}) rel:
    equiv [ G(LRO,UF).U.init ~ G(FRO,UF).U.init : rel ==> ={glob UF} ] =>
    equiv [ G(LRO,UF).main ~ G(FRO,UF).main : rel ==> ={res, glob UF} ].
  *)

  (* This is just a proof sketch of the axiom above *)
  lemma Lazy_Fixed_dh_equiv_proof_sketch(UF <: RO_USER{FRO,LRO}):
    equiv [ G(LRO,UF).U.init ~ G(FRO,UF).U.init : true ==> ={glob UF} ] =>
    equiv [ G(LRO,UF).main ~ G(FRO,UF).main : true ==> ={res, glob UF} ].
  proof strict.
    intros=> H.
    fun.
    seq 1 1: (={glob UF}).
    admit. (* apply H. (* why doesn't this work? *) *)
    inline LRO.init FRO.init.
    admit. (* This should be provable using eager if we add the same while loop
              to the end of the left game.
              Note that U.f is abstract and only allowed to perform oracle queries.
           *)
  qed.
end RandOracle.