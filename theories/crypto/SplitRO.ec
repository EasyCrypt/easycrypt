require import AllCore PROM SmtMap Distr DProd.

abstract theory Split.

  type from, to, input, output.

  op sampleto : from -> to distr.

  clone import FullRO as IdealAll with 
    type in_t    <- from,
    type out_t   <- to,
    type d_in_t  <- input,
    type d_out_t <- output,
    op   dout    <- sampleto.

abstract theory SplitDom.

op test : from -> bool.

module RO_DOM (ROT : RO) (ROF: RO) : RO = {
  proc init () = { ROT.init(); ROF.init(); }
 
  proc get(x : from) = {
    var r;
    if (test x) r <@ ROT.get(x);
    else r <@ ROF.get(x);
    return r;
  }

  proc set(x : from, y : to) = {
    if (test x) ROT.set(x, y);
    else ROF.set(x, y);
  }

  proc rem(x : from) = {
    if (test x) ROT.rem(x);
    else ROF.rem(x);
  }

  proc sample(x : from) = {
    if (test x) ROT.sample(x);
    else ROF.sample(x);
  }
}.

clone MkRO as ROT.
clone MkRO as ROF.

section PROOFS.
  declare module D: RO_Distinguisher { RO, ROT.RO, ROF.RO }.

  equiv RO_split: 
    MainD(D,RO).distinguish ~ MainD(D,RO_DOM(ROT.RO,ROF.RO)).distinguish : 
      ={glob D, x} ==> ={res, glob D} /\ RO.m{1} = union_map ROT.RO.m{2} ROF.RO.m{2} /\
                     (forall x, x \in ROT.RO.m{2} => test x) /\
                     (forall x, x \in ROF.RO.m{2} => !test x).
  proof.
    proc. 
    call (_: RO.m{1} = union_map ROT.RO.m{2} ROF.RO.m{2} /\
             (forall x, x \in ROT.RO.m{2} => test x) /\
             (forall x, x \in ROF.RO.m{2} => !test x)).
    + by proc; inline *; auto=> /> &2 _ _ @/union_map; rewrite merge_empty //=; smt(mem_empty).
    + proc; inline *.
      by if {2}; auto=> />; smt(get_setE mem_union_map set_union_map_l set_union_map_r mem_set mergeE).
    + proc; inline *.
      by if {2}; auto=> />; smt(get_setE mem_union_map set_union_map_l set_union_map_r mem_set mergeE).
    + by proc; inline *; auto=> />; smt(rem_id mem_rem rem_merge).
    + proc; inline *.
      by if {2}; auto=> />; smt(get_setE mem_union_map set_union_map_l set_union_map_r mem_set mergeE).
    by inline *; auto; smt(merge_empty mem_empty).
  qed.

  (* Remark: this is not the most general result *)
  lemma pr_RO_split (p: glob D -> output -> bool) &m x0: 
    Pr[ MainD(D,RO).distinguish(x0) @ &m : p (glob D) res] =
    Pr[ MainD(D,RO_DOM(ROT.RO,ROF.RO)).distinguish(x0) @ &m : p (glob D) res].
  proof. by byequiv RO_split. qed.

end section PROOFS.

end SplitDom.

abstract theory SplitCodom.

type to1, to2.

op topair : to -> to1 * to2.
op ofpair : to1 * to2 -> to.

axiom topairK: cancel topair ofpair.
axiom ofpairK: cancel ofpair topair.

op sampleto1 : from -> to1 distr.
op sampleto2 : from -> to2 distr.

axiom sample_spec (f:from) : sampleto f = dmap (sampleto1 f `*` sampleto2 f) ofpair.

clone FullRO as I1 with
  type in_t    <- from,
  type out_t   <- to1,
  type d_in_t  <- input,
  type d_out_t <- output,
  op   dout    <- sampleto1.

clone FullRO as I2 with
  type in_t    <- from,
  type out_t   <- to2,
  type d_in_t  <- input,
  type d_out_t <- output,
  op   dout    <- sampleto2.

module RO_Pair (RO1 : I1.RO) (RO2 : I2.RO) : RO = {
  proc init () = { RO1.init(); RO2.init(); }
 
  proc get(x : from) = {
    var r1, r2;
    r1 <@ RO1.get(x);
    r2 <@ RO2.get(x);
    return ofpair(r1,r2);
  }

  proc set(x : from, y : to) = {
    RO1.set(x,(topair y).`1); RO2.set(x,(topair y).`2);
  }

  proc rem(x : from) = {
    RO1.rem(x); RO2.rem(x);
  }

  proc sample(x : from) = {
    RO1.sample(x); RO2.sample(x);
  }
}.

section PROOFS.

  declare module D : RO_Distinguisher { RO, I1.RO, I2.RO }.

  local clone import ProdSampling with
    type t1 <- to1,
    type t2 <- to2.

  equiv RO_get : RO.get ~ RO_Pair(I1.RO, I2.RO).get : 
     ={x} /\
      RO.m{1} = map (fun (_ : from) => ofpair) (pair_map I1.RO.m{2} I2.RO.m{2}) /\
      forall (x : from),  x \in RO.m{1} = x \in I1.RO.m{2} /\ x \in RO.m{1} = x \in I2.RO.m{2} 
     ==>
     ={res} /\
      RO.m{1} = map (fun (_ : from) => ofpair) (pair_map I1.RO.m{2} I2.RO.m{2}) /\
      forall (x : from), x \in RO.m{1} = x \in I1.RO.m{2} /\ x \in RO.m{1} = x \in I2.RO.m{2}.
  proof.
    proc; inline *.
    swap{2} 5 -3; swap{2} 6 -2; sp 0 2.
    seq 1 2 : (#pre /\ r{1} = ofpair (r{2}, r0{2})).
    + conseq />.
      transitivity*{2} { (r,r0) <@ S.sample2(sampleto1 x0, sampleto2 x1); } => //; 1: smt().
      + transitivity*{2} { (r,r0) <@ S.sample(sampleto1 x0, sampleto2 x1); } => //; 1: smt().
        + inline *; wp; rnd topair ofpair; auto => /> &2 ?; split.
          + by move=> ??; rewrite ofpairK. 
          move=> _; split.
          + move=> [t1 t2]?; rewrite sample_spec dmap1E; congr; apply fun_ext => p. 
            by rewrite /pred1 /(\o) (can_eq _ _ ofpairK).
          move=> _ t; rewrite sample_spec supp_dmap => -[[t1 t2] []] + ->>.
          by rewrite topairK ofpairK => ->.
        by call sample_sample2; auto.
      by inline *; auto => />.
    by auto; smt (get_setE map_set set_pair_map mem_map mem_pair_map mem_set mapE mergeE).
  qed.

  equiv RO_split: 
    MainD(D,RO).distinguish ~ MainD(D,RO_Pair(I1.RO,I2.RO)).distinguish : 
      ={glob D, x} ==> ={res, glob D} /\ RO.m{1} = map (fun _ => ofpair) (pair_map I1.RO.m{2} I2.RO.m{2}) /\
                       forall x, x \in RO.m{1} = x \in I1.RO.m{2} /\ x \in RO.m{1} = x \in I2.RO.m{2}.
  proof.
    proc.
    call (_: RO.m{1} = map (fun _ => ofpair) (pair_map I1.RO.m{2} I2.RO.m{2}) /\
             forall x, x \in RO.m{1} = x \in I1.RO.m{2} /\ x \in RO.m{1} = x \in I2.RO.m{2}).
    + proc; inline *;auto => /> &2 _. 
      have hn := o_pair_none <: from, to1, to2>.
      by rewrite /pair_map merge_empty // map_empty /= => ?; rewrite !mem_empty. 
    + by conseq RO_get.
    + by proc; inline *; auto => />;
       smt (get_setE map_set set_pair_map mem_map mem_pair_map mem_set mapE mergeE ofpairK topairK).
    + by proc; inline *; auto; smt (map_rem rem_merge mem_map mem_pair_map mem_rem).
    + proc *.
      alias{1} 1 y = witness <:to>; alias{2} 1 y = witness <:to>. 
      transitivity*{1} { y <@ RO.get(x); } => //;1: smt().
      + by inline *; sim.
      transitivity*{2} { y <@  RO_Pair(I1.RO, I2.RO).get(x); } => //; 1:smt().
      + by call RO_get.
      by inline *; sim.
    inline *; auto => />.
    have hn := o_pair_none <: from, to1, to2>. 
    by rewrite /pair_map merge_empty // map_empty /= => ?; rewrite !mem_empty.
  qed.

  lemma pr_RO_split (p: glob D -> output -> bool) &m x0: 
    Pr[ MainD(D,RO).distinguish(x0) @ &m : p (glob D) res] =
    Pr[ MainD(D,RO_Pair(I1.RO,I2.RO)).distinguish(x0) @ &m : p (glob D) res].
  proof. by byequiv RO_split. qed.

end section PROOFS.

end SplitCodom.

end Split.
