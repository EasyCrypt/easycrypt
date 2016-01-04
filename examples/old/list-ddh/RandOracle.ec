(* This module deals with random oracles.
   Note that we ignore the adversary wrapper for the random
   oracle that logs the queries and limits the number of queries
   since it is not required in our example.
*)

require import List.
require import Map.
require import FSet.
require import ISet.
  import ISet.Finite.
require import Real.
require import Int.
require import Distr.

theory RandOracle.

  (* finite type of oracle inputs *)
  type from.

  axiom from_univ_finite : finite univ<:from>.

  op univ_from = toFSet (univ<:from>).

  type to.

  op dsample : to distr.

  module type RO = {
    fun init() : unit {*}
    fun query(x : from) : to
  }.

  (* Lazy random oracle: Values are sampled on demand. *)
  module LRO : RO = {
    var m : (from, to) map
    fun resample () : unit = {
      var x : from;
      var xs : from list;
      var y : to;
      xs = FSet.elems univ_from;
      while (xs <> []) {
        x  = List.hd xs;
        xs = List.tl xs;
        y  = $dsample;
        if (!in_dom x m) m = m.[ x <- y ];
      }
    }
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

    fun resample () : unit = {
      var x : from;
      var xs : from list;
      var y,y0 : to; (* y0 is used for the proof *)
      xs = FSet.elems univ_from;
      while (xs <> []) {
        x  = List.hd xs;
        xs = List.tl xs;
        y  = $dsample;
        if (!in_dom x m) m = m.[ x <- y ];
      }
    }
    fun init() : unit = {
      m = Map.empty;
      resample();
    }
    fun query(x : from) : to = {
      return proj m.[x];
    }
  }.

  lemma LRO_lossless_query:
    mu dsample cpTrue = 1%r => islossless LRO.query.
  proof strict.
  move=> samp.
  fun.
    if.
      wp; rnd; skip; smt.
    skip; smt.
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
    mu dsample Fun.cpTrue = 1%r => islossless FRO.init.
  proof strict.
    move=> H; fun.
    inline FRO.resample.
    while true (length xs).
     by move=> z; wp; rnd; wp; skip; smt.
     wp; skip; smt.
  qed.

  (** Switching between lazy and fixed random oracle *)

  type ro_user_from.
  type ro_user_to.

  (* A random oracle user *)
  module type RO_USER(RO : RO) = {
    fun main(x : ro_user_from) : ro_user_to {*RO.query}
  }.

  (* A module that initializes a random oracles and "runs" the random
     oracle user *)
  module G(RO : RO, UF : RO_USER) = {
    module U = UF(RO)

    fun main(x : ro_user_from) : ro_user_to = {
      var r : ro_user_to;
      RO.init();
      r = U.main(x);
      return r;
    }
  }.

  module GL(UF : RO_USER) = {
    module U = UF(LRO)

    fun main(x : ro_user_from) : ro_user_to = {
      var r : ro_user_to;
      LRO.init();
      r = U.main(x);
      LRO.resample();
      return r;
    }
  }.

  lemma Fixed_Lazy_query :
        mu dsample cpTrue = 1%r =>
        eager[ FRO.resample();, FRO.query ~ LRO.query, LRO.resample(); :
        ={x} /\ FRO.m{1} = LRO.m{2} ==> ={res} /\ FRO.m{1} = LRO.m{2}].
  proof.
   move=> Hsample; eager fun.
     inline FRO.resample LRO.resample.
     swap{2} 3 -2;seq 1 1 : (={x,xs} /\ FRO.m{1} = LRO.m{2} /\ (List.mem x xs){1}).
       wp;skip;progress;smt.
     if{2}.
      transitivity{1} {y0 = $dsample;
                       while (! xs = []) {
                         x0 = hd xs; xs = tl xs; y = $dsample;
                         if (! in_dom x0 FRO.m) FRO.m = FRO.m.[x0 <- if x = x0 then y0 else y];
                       }
                       result = proj FRO.m.[x]; }
                      (={x,xs,FRO.m} ==> ={result,FRO.m})
                      ((={x, xs} /\ FRO.m{1} = LRO.m{2} /\ mem x{1} xs{1}) /\ ! in_dom x{2} LRO.m{2} ==> ={result} /\ FRO.m{1} = LRO.m{2}) => //.
        move=> &m1 &m2 H;exists LRO.m{m2}, x{m2}, xs{m2}; move: H => //.
      transitivity{1} {
                       while (! xs = []) {
                         x0 = hd xs; xs = tl xs; y = $dsample;
                         if (! in_dom x0 FRO.m) FRO.m = FRO.m.[x0 <- y];
                       }
                       y0 = $dsample;
                       result = proj FRO.m.[x]; }
                      (={x,xs,FRO.m} ==> ={result,FRO.m})
                      (={x, xs,FRO.m} ==> ={result,FRO.m}) => //.
         move=> &m1 &m2 H;exists FRO.m{m2}, x{m2}, xs{m2}; move: H => //.
         eqobs_in;rnd{2};conseq [-frame] (_ : _ ==> ={x,FRO.m});[ progress;smt | eqobs_in].
         wp;symmetry.
         eager while (h1:y0 = $dsample; ~ y0 = $dsample; : true ==> ={y0}) => //; first eqobs_in.
         swap{2} 5 -4. swap 4 -2.
         case (x = hd xs){1}.
          wp;rnd{1};rnd;rnd{2};skip;progress;try smt.
          wp;do !rnd;skip;progress;smt.
       eqobs_in.
       wp.
       while (={x,xs} /\ y0{1} = y{2} /\
              (mem x xs || in_dom x FRO.m){1} /\
              (in_dom x LRO.m /\ LRO.m.[x] = Some y){2} /\
              if in_dom x{1} FRO.m{1} then FRO.m{1} = LRO.m{2} /\ (FRO.m.[x] = Some y0){1} else (FRO.m.[x <- y0]){1} = LRO.m{2}).
         wp;rnd;wp;skip;progress=> //;smt.
       wp;rnd;skip;progress;smt.
      wp;while ((={x,xs} /\ FRO.m{1} = LRO.m{2}) /\ in_dom x{2} LRO.m{2} /\
                 proj FRO.m{1}.[x{1}] = result{2}).
       wp;rnd;wp;skip;progress => //; smt.
    wp;skip;progress => //.
  qed.

  lemma Fixed_Lazy_dh_equiv_GL(UF <: RO_USER{FRO,LRO}):
    mu dsample cpTrue = 1%r =>
    equiv [ G(FRO,UF).main ~ GL(UF).main : ={x} ==> ={res, glob UF} ].
  proof.
    move=> Hsample;fun;inline LRO.init FRO.init.
    seq 1 1 : (FRO.m{1} = LRO.m{2} /\ ={x}); first eqobs_in.
    eager (h : FRO.resample(); ~ LRO.resample(); : FRO.m{1} = LRO.m{2} ==> FRO.m{1} = LRO.m{2}) :
       (FRO.m{1} = LRO.m{2}) => //.
     eqobs_in.
     eager fun h (FRO.m{1} = LRO.m{2}) => //.
     apply Fixed_Lazy_query => //.
     fun;eqobs_in.
  save.

  lemma Fixed_Lazy_dh_equiv(UF <: RO_USER{FRO,LRO}):
    mu dsample cpTrue = 1%r =>
    equiv [ G(FRO,UF).main ~ G(LRO,UF).main : ={x} ==> ={res} ].
  proof.
    move=> Hsample;transitivity GL(UF).main (={x} ==> ={res, glob UF}) (={x} ==> ={res}) => //.
      move=> &m1 &m2 H;exists x{m2} => //.
    apply (Fixed_Lazy_dh_equiv_GL UF _) => //.
    fun.
    seq 2 2 : (={r}); first eqobs_in.
    inline LRO.resample.
      while{1} true (length xs{1}).
      move=> &m z;wp;rnd;wp;skip;progress;smt.
    wp;skip;smt.
  save.

  lemma Lazy_Fixed_dh_equiv_proof_sketch(UF <: RO_USER{FRO,LRO}):
    mu dsample cpTrue = 1%r =>
    equiv [ G(LRO,UF).main ~ G(FRO,UF).main : ={x} ==> ={res} ].
  proof strict.
    move=> Hsample;symmetry. conseq [-frame] (_ : ={x} ==> ={res}) => //.
    apply (Fixed_Lazy_dh_equiv UF _) => //.
  qed.
end RandOracle.
