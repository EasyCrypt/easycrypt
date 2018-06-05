(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List SmtMap Distr.
require (*--*) IterProc.

pragma -oldip.
pragma +implicits.

(* -------------------------------------------------------------------- *)
type flag = [ Unknown | Known ].

lemma neqK_eqU f : f <> Known <=> f = Unknown.
proof. by case: f. qed.

(* -------------------------------------------------------------------- *)
(** Properties of flagged maps -- Generalize into a separate theory? **)
op in_dom_with (m : ('from, 'to * 'flag) fmap) (x:'from) (f:'flag) =
   x \in m /\ (oget (m.[x])).`2 = f.

op restr f (m : ('from, 'to * 'flag) fmap) =
  let m = filter (fun _ (p:'to*'flag) => p.`2=f) m in
  map (fun _ (p:'to*'flag) => p.`1) m.

lemma restrP (m : ('from, 'to * 'flag) fmap) f x:
  (restr f m).[x]
  = obind (fun (p:'to*'flag)=> if p.`2=f then Some p.`1 else None) m.[x].
proof.
rewrite /restr /= mapE filterE //=.
by case: (m.[x])=> //= y; case: (y.`2=f).
qed.

lemma dom_restr (m : ('from, 'to * 'flag) fmap) f x:
  x \in (restr f m) <=> in_dom_with m x f.
proof.
rewrite /in_dom_with !domE; case: (m.[x]) (restrP m f x)=>//= -[t f'] /=.
by rewrite oget_some /=; case (f' = f)=> [_ ->|].
qed.

lemma restr_set (m : ('from, 'to * 'flag) fmap) f1 f2 x y:
  restr f1 m.[x<-(y,f2)]
  = if f1 = f2 then (restr f1 m).[x<-y] else rem (restr f1 m) x.
proof.
apply/fmap_eqP; case: (f1 = f2)=> [->>|Hneq] x0; rewrite !(restrP, get_setE).
+ by case: (x0 = x).
case: (x0 = x)=> [->>|Hnx].
+ by rewrite (@eq_sym f2) Hneq remE.
by rewrite remE Hnx restrP.
qed.

lemma restr_set_eq (m : ('from, 'to * 'flag) fmap) f x y:
  restr f m.[x<-(y,f)] = (restr f m).[x<-y].
proof. by rewrite restr_set. qed.

lemma restr0 f: restr f empty<:'from, 'to * 'flag> = empty.
proof. by apply/fmap_eqP=>x; rewrite restrP !emptyE. qed.

lemma restr_set_neq f2 f1 (m : ('from, 'to * 'flag) fmap) x y:
  x \notin m =>
  f2 <> f1 => restr f1 m.[x<-(y,f2)] = restr f1 m.
proof.
move=> Hm Hneq.
rewrite restr_set (@eq_sym f1) Hneq /=; apply/fmap_eqP=> x'.
rewrite remE; case: (x' = x)=> [->>|//].
by move: Hm; rewrite domE /= restrP=> ->.
qed.

lemma restr_rem (m : ('from,'to*'flag) fmap) (x : 'from) f:
  restr f (rem m x)
  = if in_dom_with m x f then rem (restr f m) x else restr f m.
proof.
apply/fmap_eqP=> z; rewrite restrP.
by case: (in_dom_with m x f); rewrite !(restrP,remE) /in_dom_with domE /#.
qed.

(* -------------------------------------------------------------------- *)
abstract theory Ideal.
  type from, to.

  op sampleto : from -> to distr.

  module type RO = {
    proc init  ()                  : unit
    proc get   (x : from)          : to
    proc set   (x : from, y : to)  : unit
    proc rem   (x : from)          : unit
    proc sample(x : from)          : unit
  }.

  module type RO_Distinguisher(G : RO) = {
    proc distinguish(): bool 
  }.

  module type FRO = {
    proc init  ()                  : unit
    proc get   (x : from)          : to
    proc set   (x : from, y : to)  : unit
    proc rem   (x : from)          : unit 
    proc sample(x : from)          : unit
    proc in_dom(x : from,f : flag) : bool
    proc restrK()                  : (from, to) fmap
  }.

  module type FRO_Distinguisher(G : FRO) = {
    proc distinguish(): bool 
  }.

  module RO : RO = {
    var m : (from, to)fmap

    proc init () = { m <- empty; }

    proc get(x:from) = {
      var r;
      r <$ sampleto x;
      if (x \notin m) m.[x] <- r;
      return (oget m.[x]);
    }

    proc set (x:from, y:to) = {
      m.[x] <- y;
    }

    proc rem (x:from) = {
      m <- rem m x;
    }

    proc sample(x:from) = {
      get(x);
    }

    proc restrK() = {
      return m;
    }

  }.

  module FRO : FRO = {
    var m : (from, to * flag)fmap

    proc init () = { m <- empty; }

    proc get(x:from) = {
      var r;
      r <$ sampleto x;
      if (x \in m) r <- (oget m.[x]).`1;
      m.[x] <- (r,Known);
      return r;
    }

    proc set (x:from, y:to) = {
      m.[x] <- (y,Known);
    }

     proc rem (x:from) = {
      m <- rem m x;
    }

    proc sample(x:from) = {
      var c;
      c <$ sampleto x;
      if (x \notin m) m.[x] <- (c,Unknown);
    }

    proc in_dom(x:from, f:flag) = {
      return in_dom_with m x f;
    }

    proc restrK() = {
      return restr Known m;
    }
  }.

  (* ------------------------------------------------------------------ *)
  (* Equivalence between RO and trivial Flagged RO: oracles *)
  equiv RO_FRO_init :
    RO.init ~ FRO.init : true ==> RO.m{1} = map (fun _=> fst) FRO.m{2}.
  proof. by proc; auto=> />; apply/fmap_eqP=> x; rewrite mapE !emptyE. qed.

  equiv RO_FRO_get : RO.get ~ FRO.get :
         ={x} /\ RO.m{1} = map (fun _=> fst) FRO.m{2}
     ==> ={res} /\ RO.m{1} = map (fun _=> fst) FRO.m{2}.
  proof.
  proc; auto=> /> &2 r _; rewrite !domE !mapE !map_set !get_set_eqE //=.
  rewrite none_omap oget_some=> /= />.
  case: {-1}(FRO.m.[x]{2}) (eq_refl FRO.m.[x]{2})=> //= - [y f] /=.
  rewrite oget_some=> /= mx; apply/fmap_eqP=> x'; rewrite get_setE.
  by case: (x' = x{2})=> //= <<-; rewrite mapE mx.
  qed.

  equiv RO_FRO_set : RO.set ~ FRO.set :
         ={x,y} /\ RO.m{1} = map (fun _=> fst) FRO.m{2}
     ==> RO.m{1} = map (fun _=> fst) FRO.m{2}.
  proof. by proc; auto=> ? &ml [#] 3->; rewrite map_set. qed.

  equiv RO_FRO_rem : RO.rem ~ FRO.rem :
         ={x} /\ RO.m{1} = map (fun _=> fst) FRO.m{2}
     ==> RO.m{1} = map (fun _=> fst) FRO.m{2}.
  proof.
  proc; auto=> /> &2.
  by apply/fmap_eqP=> x'; rewrite !(remE, mapE); case: (x' = x{2}).
  qed.

  equiv RO_FRO_sample : RO.sample ~ FRO.sample :
         ={x} /\ RO.m{1} = map (fun _=> fst) FRO.m{2}
     ==> RO.m{1} = map (fun _=> fst) FRO.m{2}.
  proof.
  proc; inline *; auto=> /> &2 r _; rewrite !domE !map_set /= !mapE /=.
  by rewrite none_omap.
  qed.

  (* ------------------------------------------------------------------ *)
  (* Equivalence between RO and trivial Flagged RO: generic experiment  *)
  lemma RO_FRO_D (D<:RO_Distinguisher{RO,FRO}) : 
    equiv [D(RO).distinguish ~ D(FRO).distinguish : 
       ={glob D} /\ RO.m{1} = map (fun _=> fst) FRO.m{2} ==>
       ={res,glob D} /\ RO.m{1} = map (fun _=> fst) FRO.m{2} ].
  proof.
  proc (RO.m{1} = map (fun _=> fst) FRO.m{2})=>//.
  + by conseq RO_FRO_init.
  + by conseq RO_FRO_get.
  + by conseq RO_FRO_set. 
  + by conseq RO_FRO_rem.
  + by conseq RO_FRO_sample.
  qed.

  (* ------------------------------------------------------------------ *)
  (* Losslessness Lemmas on RO and FRO *)
  section LL. 
    lemma RO_init_ll : islossless RO.init.
    proof. by proc;auto. qed.

    lemma FRO_init_ll : islossless FRO.init.
    proof. by proc;auto. qed.

    lemma FRO_in_dom_ll : islossless FRO.in_dom.
    proof. by proc. qed.

    lemma FRO_restrK_ll : islossless FRO.restrK.
    proof. by proc. qed.

    lemma RO_set_ll : islossless RO.set.
    proof. by proc; auto. qed.

    lemma FRO_set_ll : islossless FRO.set.
    proof. by proc; auto. qed.

    section LL_conditional.
      axiom sampleto_ll x: is_lossless (sampleto x).

      lemma RO_get_ll : islossless RO.get.
      proof. by proc; auto; progress; apply/sampleto_ll. qed.

      lemma FRO_get_ll : islossless FRO.get.
      proof. by proc; auto; progress; apply/sampleto_ll. qed.

      lemma RO_sample_ll : islossless RO.sample.
      proof. by proc; call RO_get_ll. qed.

      lemma FRO_sample_ll : islossless FRO.sample.
      proof. by proc; auto; progress; apply/sampleto_ll. qed.
    end section LL_conditional.
  end section LL.
end Ideal.

(* -------------------------------------------------------------------------- *)
abstract theory GenEager.
  clone include Ideal.

  axiom sampleto_ll x: is_lossless (sampleto x).

  clone include IterProc with type t <- from.

  (** A RO that resamples public queries if the associated value is unknown *)
  module RRO : FRO = {
    proc init = FRO.init

    proc get(x:from) = {
      var r;
      r <$ sampleto x;
      if (x \notin FRO.m \/ (oget FRO.m.[x]).`2 = Unknown) {
        FRO.m.[x] <- (r,Known);
      }
      return (oget FRO.m.[x]).`1;
    }

    proc set = FRO.set 

    proc rem = FRO.rem

    proc sample = FRO.sample

    proc in_dom = FRO.in_dom

    proc restrK = FRO.restrK

    module I = {
      proc f (x:from) = {
        var c;
        c <$ sampleto x;
        FRO.m.[x] <- (c,Unknown);
      }
    }

    proc resample () = {
      Iter(I).iter (FSet.elems (fdom (restr Unknown FRO.m)));
    }
  }.

  (* A module which does not sample non-public queries *)
  module LRO : RO = {
    proc init = RO.init

    proc get = RO.get

    proc set = RO.set 

    proc rem = RO.rem

    proc sample(x:from) = {}
  }.

  (* ------------------------------------------------------------------------ *)
  (* Equivalence of RRO and LRO: oracles *)
  lemma RRO_resample_ll : islossless RRO.resample.
  proof. 
  proc; call (iter_ll RRO.I _)=> //.
  proc; auto=> /> ?; apply/sampleto_ll. 
  qed.

  lemma eager_init :
    eager [RRO.resample(); , FRO.init ~ RRO.init, RRO.resample(); :
           ={FRO.m} ==> ={FRO.m} ].
  proof.
  eager proc; inline{2} *; rcondf{2}3; auto=> />.
  + rewrite restr0 fdomE; apply/perm_eq_small=> //.
    apply/uniq_perm_eq=> //; 1:exact/FSet.uniq_elems.
    move=> x. rewrite -FSet.memE FSet.mem_oflist Finite.mem_to_seq 1:finite_dom.
    by rewrite domE emptyE.
  conseq (_:) (_: true==>true: =1%r) _=> //.
  by call RRO_resample_ll.
  qed.

  equiv iter_perm2 (i1 i2 : from):
    Iter(RRO.I).iter_12 ~ Iter(RRO.I).iter_21 :
      ={glob RRO.I, t1, t2} ==> ={glob RRO.I}.
  proof.
  proc; inline *; case: ((t1 = t2){1}); 1:by auto.
  swap{2}[4..5] -3. auto=> &ml &mr [#] 3-> neq /= ? -> ? -> /=.
  apply/fmap_eqP=> x; rewrite !get_setE.
  by case: (x = t2{mr}); case: (x = t1{mr})=> //= ->> ->> /#.
  qed.

  equiv I_f_neq x1 mx1: RRO.I.f ~ RRO.I.f :
      ={x,FRO.m} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = mx1
    ==> ={FRO.m} /\ FRO.m{1}.[x1] = mx1.
  proof.
  by proc; auto=> /> &2 Hneq ? _; rewrite get_setE Hneq.
  qed.

  equiv I_f_eqex x1 mx1 mx2: RRO.I.f ~ RRO.I.f :
         ={x}
      /\ x1 <> x{1}
      /\ eq_except (pred1 x1) FRO.m{1} FRO.m{2}
      /\ FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2
    ==>    eq_except (pred1 x1) FRO.m{1} FRO.m{2}
        /\ FRO.m{1}.[x1] = mx1
        /\ FRO.m{2}.[x1] = mx2.
  proof.
  proc; auto=> ? &mr [#] -> Hneq Heq /= Heq1 Heq2 ? -> /=.
  by rewrite !get_setE Hneq eq_except_set_eq.
  qed.

  equiv I_f_set x1 r1 : RRO.I.f ~ RRO.I.f : 
         ={x}
      /\ x1 <> x{1}
      /\ FRO.m{1}.[x1] = None
      /\ FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)]
    ==>    FRO.m{1}.[x1] = None
        /\ FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)].
  proof.
  proc; auto=> ? &mr [#] -> Hneq H1 -> /= ? ->.
  rewrite get_setE Hneq/= H1=> //=; apply/fmap_eqP=> y.
  by rewrite !get_setE; case: (y = x{mr}); case: (y = x1).
  qed.

  lemma eager_get :
    eager [RRO.resample(); , FRO.get ~ RRO.get, RRO.resample(); :
           ={x,FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc.
  wp; case: ((x \in FRO.m /\ (oget FRO.m.[x]).`2=Known){1}).
  + rnd{1};rcondf{2} 2;1:by auto=> /#.
    exists* x{1}, ((oget FRO.m.[x{2}]){1}); elim* => x1 mx.
    inline RRO.resample.
    call (iter_inv RRO.I (fun z=> x1 <> z) (relI (=) (fun o _ => o.[x1] = Some mx)) _).
    + by conseq (I_f_neq x1 (Some mx))=> @/relI /=.
    auto=> @/relI ? &mr [#] 4-> Hd Hget; rewrite sampleto_ll /= => ? _; split.
    + have:= Hd; have:= Hget; rewrite domE; case: (FRO.m{mr}.[x{mr}])=> //= -[t f].
      by rewrite oget_some=> /= ->> x'; rewrite -FSet.memE mem_fdom dom_restr /#.
    move=> @/relI [#] _ Heq ? mr [#] -> Heq' ? _.
    by rewrite domE Heq' oget_some /=; apply/fmap_eqP=> y; rewrite get_setE /#.
  case: ((x \in FRO.m){1}).
  + inline{1} RRO.resample=> /=; rnd{1}.
    transitivity{1} 
      { Iter(RRO.I).iter_1s(x, FSet.elems ( FSet.(`\`) (fdom (restr Unknown FRO.m)) (FSet.fset1 x))); }
      (={x,FRO.m} /\ x{1} \in FRO.m{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,FRO.m})
      (={x,FRO.m} /\ x{1} \in FRO.m{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown==>
       ={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
       FRO.m{1}.[x{2}] = Some (result{2},Unknown) /\
       FRO.m{2}.[x{2}] = Some (result{2},Known)).
    + by move=> ? &mr [#] -> -> ? ?; exists FRO.m{mr} x{mr}=> /#.
    + move=> ? &2 &m; rewrite domE=> [#] <*> [#] -> /eq_except_sym H Hxm Hx2.
      rewrite sampleto_ll=> r _; rewrite /= Hxm oget_some /=; apply /eq_sym.
      have /(congr1 oget):= Hx2 => <-; apply/fmap_eqP=> x'; rewrite !get_setE.
      case: (x' = x{m})=> [<<-| x_neq].
      + by case: (FRO.m{m}.[x']) Hx2.
      by move: H=> /eq_exceptP /(_ x' x_neq).
    + symmetry; call (iter1_perm RRO.I iter_perm2).
      skip=> &1 &2 [[->> ->>]] [Hdom Hm]; split=>//=.
      apply/uniq_perm_eq.
      + split.
        + by rewrite -FSet.memE FSet.setDE FSet.mem_oflist mem_filter /predC FSet.in_fset1.
        exact/FSet.uniq_elems.
      + exact/FSet.uniq_elems.
      move=> x'=> //=; case: (x' = x{1})=> [<<-|] /=.
      + by rewrite -FSet.memE mem_fdom dom_restr /#.
      by rewrite -!FSet.memE FSet.in_fsetD FSet.in_fset1.
    inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample.
    seq 5 3 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
               (l = FSet.elems (FSet.(`\`) (fdom (restr Unknown FRO.m)) (FSet.fset1 x))){1} /\
               FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
               FRO.m{2}.[x{2}] = Some (result{2}, Known)).
    + auto=> ? &mr [#] 2 -> /= ^Hdom -> ^Hget -> c -> /=.
      rewrite !get_setE /= oget_some !restr_set /=.
      have ->: pred1 x{mr} = predU pred0 (pred1 x{mr}) by done. (* Really? *)
      rewrite eq_except_set_neq //=.
      congr; apply/FSet.fsetP=> x'; rewrite !FSet.in_fsetD FSet.in_fset1 !mem_fdom.
      by rewrite mem_set; case: (x' = x{mr}).
    exists* x{1}, FRO.m{1}.[x{2}], FRO.m{2}.[x{2}]; elim*=>x1 mx1 mx2.
    call (iter_inv RRO.I
           (fun z=> x1 <> z)
           (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= mx1 /\ o2.[x1]=mx2)
           (I_f_eqex x1 mx1 mx2))=> /=.
    + auto=> /> &1 &2 eqe_x2_m1_m2 ^H1 -> ^H2 -> //=; split=> [|/>].
      split.
      + congr; apply/FSet.fsetP=> z; rewrite !FSet.inE !mem_fdom !dom_restr /in_dom_with.
        by have:= eqe_x2_m1_m2=> /eq_exceptP /(_ z) /#.
      by move=> x2; rewrite -FSet.memE !FSet.inE mem_fdom eq_sym.
  swap{1}-1; seq  1  1: (={r,x,FRO.m} /\ x{1} \notin FRO.m{1}); 1:by auto. 
  inline RRO.resample; exists* x{1}, r{1}; elim* => x1 r1.
  call (iter_inv RRO.I (fun z=> x1 <> z) 
           (fun o1 o2 => o1.[x1] = None /\ o2= o1.[x1<-(r1,Known)]) (I_f_set x1 r1)).
  auto=> ? &mr [#] 5 -> ^Hnin ^ + -> /=; rewrite domE=> /= -> /=.
  rewrite restr_set_neq //=; split.
  + by move=> z; rewrite -FSet.memE mem_fdom dom_restr /#. 
  by move=> _ ? mr [#] ^Hmem 2->; rewrite domE Hmem /= get_setE /= oget_some.
  qed.

  lemma eager_set :
    eager [RRO.resample(); , FRO.set ~ RRO.set, RRO.resample(); :
           ={x,y} /\ ={FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc. inline RRO.resample=> /=; wp.
  case ((x \in FRO.m /\ (oget FRO.m.[x]).`2 = Unknown){1}).
  + transitivity{1} { Iter(RRO.I).iter_1s(x,FSet.elems (FSet.(`\`) (fdom (restr Unknown FRO.m)) (FSet.fset1 x)));}
      (={x,y,FRO.m} /\ x{1} \in FRO.m{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,y,FRO.m})
      (={x,y,FRO.m} /\ x{1} \in FRO.m{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown==>
       ={x,y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
       FRO.m{2}.[x{2}] = Some (y{2},Known)).
    + by move=> ? &mr [#] 2-> ? ? ?; exists FRO.m{mr} x{mr} y{mr}=> /#.
    + move=> /> &m &mr [#] <*> [#] Hex Hm2.
      apply/fmap_eqP=> z; rewrite get_setE; case: (z = x{mr})=> //= [->>|].
      + by rewrite Hm2.
      by move: Hex=> /eq_exceptP + h=> /(_ z h).
    + symmetry; call (iter1_perm RRO.I iter_perm2); auto=> |> &1 Hdom Hm.
      apply/uniq_perm_eq=> //=.
      + split.
        + by rewrite -FSet.memE FSet.in_fsetD FSet.in_fset1.
        exact/FSet.uniq_elems.
      + exact/FSet.uniq_elems.
      by move=> z; rewrite -!FSet.memE FSet.in_fsetD FSet.in_fset1 !mem_fdom dom_restr /#.
    inline{1}Iter(RRO.I).iter_1s.
    seq 3 1: (={x,y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
              l{1} = (FSet.elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
              (FRO.m.[x]=Some(y, Known)){2}).
    + inline *; auto=> ? &mr [#] 3-> /= Hmem Hget; rewrite sampleto_ll=> ? _.
      have ->: pred1 x{mr} = predU pred0 (pred1 x{mr}) by done.
      rewrite (@eq_except_set_neq _ _ (_,Unknown) (_,Known) _ _) //=.
      split.
      + congr; rewrite FSet.fsetP=> z; rewrite !FSet.inE !mem_fdom !dom_restr /in_dom_with mem_set.
        case: (z = x{mr})=> [<<-|z_neq_x] //=.
        + by rewrite get_set_eqE.
        by rewrite get_setE z_neq_x.
      by rewrite get_set_sameE /= -FSet.memE !FSet.inE mem_fdom.
    exists* x{1},y{1},(FRO.m.[x]{1}); elim* => x1 y1 mx1; pose mx2:= Some(y1,Known).
    call (iter_inv RRO.I (fun z=> x1 <> z) 
           (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= mx1 /\ o2.[x1]=mx2) 
           (I_f_eqex x1 mx1 mx2))=>/=.
    by auto=> &1 &2 |> Hex Hx2 -> //= z /#.
  exists* x{1},y{1},(FRO.m.[x]{1}); elim* => x1 y1 mx1; pose mx2:= Some(y1,Known).
  call (iter_inv RRO.I (fun z=> x1 <> z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= mx1 /\ o2.[x1]=mx2) 
         (I_f_eqex x1 mx1 mx2))=> /=.
  auto=> ? &mr [#] -> <- 2-> ->> -> /= Hidm.
  rewrite restr_set get_set_sameE /mx2 /=; split=> [|_].
  + do !split.
    + by congr; apply/FSet.fsetP=> z; rewrite !mem_fdom mem_rem dom_restr /#.
    + by move=> z; rewrite -FSet.memE mem_fdom dom_restr /#.
    exact/eq_except_setr.
  move=> m1 m2 [#] /eq_exceptP Hex _ m2x; apply/fmap_eqP=> z; rewrite get_setE.
  by have:= Hex z=> @/pred1; rewrite eq_sym; case: (x{mr} = z)=> [<<-|] //=; rewrite m2x.
  qed.

  lemma eager_rem: 
    eager [RRO.resample(); , FRO.rem ~ RRO.rem, RRO.resample(); :
           ={x} /\ ={FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc;case ((in_dom_with FRO.m x Unknown){1}).
  + inline RRO.resample;wp.
    transitivity{1} 
      { Iter(RRO.I).iter_1s(x,FSet.elems (FSet.(`\`) (fdom (restr Unknown FRO.m)) (FSet.fset1 x))); }
      (={x,FRO.m}/\(in_dom_with FRO.m x Unknown){1}==> ={x,FRO.m}) 
      (={x,FRO.m}/\ (in_dom_with FRO.m x Unknown){1} ==> (rem FRO.m x){1} = FRO.m{2})=>//.
    + by move=> ? &mr [#] 2-> ?; exists FRO.m{mr} x{mr}.
    + symmetry; call (iter1_perm RRO.I iter_perm2); skip=> |> &1 x_in_m_with_U.
      apply/uniq_perm_eq=> /=.
      + split.
        + by rewrite -FSet.memE FSet.in_fsetD FSet.in_fset1.
        exact/FSet.uniq_elems.
      + exact/FSet.uniq_elems.
      move=> x'; rewrite -!FSet.memE FSet.in_fsetD FSet.in_fset1 mem_fdom dom_restr.
      by case: (x' = x{1})=> //=.
    inline{1}Iter(RRO.I).iter_1s.
    seq 3 1: (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
              l{1} = (FSet.elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
        (FRO.m.[x]=None){2}).
    + inline *; auto=> |> &2 x_in_m_with_U; rewrite sampleto_ll=> |> /= t _.
      do !split.
      + by apply/eq_exceptP=> x' @/pred1 /= neq_x; rewrite remE get_setE neq_x //.
      + congr; apply/FSet.fsetP=> x'; rewrite FSet.in_fsetD FSet.in_fset1 !mem_fdom !dom_restr.
        by rewrite /in_dom_with mem_rem remE; case: (x' = x{2}).
      + by rewrite -FSet.memE FSet.in_fsetD FSet.in_fset1.
      by rewrite remE.
    exists* x{1},(FRO.m.[x]{1}); elim* => x1 mx1.
    call (iter_inv RRO.I (fun z=> x1 <> z) 
           (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= mx1 /\ o2.[x1]=None) _).
    + by conseq (I_f_eqex x1 mx1 None).
    auto=> |> &1 &2 eqex _ x_notin_m; split=> [|_ mL mR].
    + by move=> x'; rewrite -FSet.memE mem_fdom dom_restr /in_dom_with domE /#.
    move=> eqex_x_mL_mR mL_x mR_x; apply/fmap_eqP=> x'.
    rewrite remE; case: (x' = x{2})=> //= [<<-|].
    + by rewrite mR_x.
    by move: eqex_x_mL_mR=> /eq_exceptP h /h.
  inline RRO.resample; wp.
  exists *x{1},(FRO.m.[x]{1}); elim* => x1 mx1.
  call (iter_inv RRO.I (fun z=> x1 <> z)
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= mx1 /\ o2.[x1]=None) _).
  + by conseq (I_f_eqex x1 mx1 None).
  auto=> ? &mr [#] 4-> Hin /=.
  rewrite restr_rem Hin /=; do !split=> [x'|||_ mL mR [#] /eq_exceptP @/pred1 eqe_x_mL_mR].
  + by rewrite -FSet.memE mem_fdom dom_restr; case: (x{mr} = x')=> [->>|].
  + by apply/eq_exceptP=> x' @/pred1; rewrite remE=> ->.
  + by rewrite remE.
  move=> mL_x mR_x; apply/fmap_eqP=> x'; rewrite remE.
  by move: (eqe_x_mL_mR x'); case: (x' = x{mr})=> //= ->>; rewrite mR_x.
  qed.

  lemma eager_in_dom:
    eager [RRO.resample(); , FRO.in_dom ~ RRO.in_dom, RRO.resample(); :
           ={x,f} /\ ={FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc; inline *; wp.
  while (={l,FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         in_dom_with FRO.m{1} x{1} f{1} = result{2}).
  + auto=> &m1 &m2 [#] 2-> Hz <- _ l_not_nil /= ? -> /=.
    split=> [z /mem_drop Hm|]; rewrite /in_dom_with domE get_setE.
    + smt().
    case: (x{m1} = head witness l{m2})=> //= ->; rewrite oget_some /=.
    have /Hz @/in_dom_with [] -> -> //: head witness l{m2} \in l{m2}.
    by move: l_not_nil; case: (l{m2}).    
  by auto=> ? &mr /= [#] 3-> /=; split=> // z; rewrite -FSet.memE mem_fdom dom_restr.
  qed.

  lemma eager_restrK:
    eager [RRO.resample(); , FRO.restrK ~ RRO.restrK, RRO.resample(); :
           ={FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc; inline *; wp.
  while (={l,FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         restr Known FRO.m{1} = result{2}).
  + auto=> ? &mr [#] 2-> Hz <- _ H /= ? -> /=.
    split=>[z /mem_drop Hm|];1:by rewrite /in_dom_with domE get_setE /#.
    rewrite restr_set /=; apply/fmap_eqP=> x'; rewrite remE; case: (x' = head witness l{mr})=> //=.
    move: H=> /(mem_head_behead witness) /(_ (head witness l{mr})) /= /Hz + h; rewrite -h.
    rewrite eq_sym -(negbK ((restr Known FRO.m{mr}).[x'] = None)) -domE dom_restr.
    by rewrite /in_dom_with=> [#] -> ->.
  by auto=> |> &2 z; rewrite -FSet.memE mem_fdom dom_restr.
  qed.

  lemma eager_sample:
    eager [RRO.resample(); , FRO.sample ~ RRO.sample, RRO.resample(); :
           ={x,FRO.m} ==> ={res,FRO.m} ].
  proof.
  eager proc.
  case: (x{2} \notin FRO.m{2}).
  + rcondt{2} 2; 1:by auto.
    transitivity{2} { c <$ sampleto x;
                      FRO.m.[x] <- (c, Unknown);
                      Iter(RRO.I).iter_1s(x,FSet.elems (FSet.(`\`) (fdom (restr Unknown FRO.m)) (FSet.fset1 x))); }
                    (={x,FRO.m} /\ x{2} \notin FRO.m{2} ==> ={x,FRO.m}) 
                    (={x,FRO.m} /\ x{2} \notin FRO.m{2} ==> ={x,FRO.m})=> //; last first.
    + inline{2} RRO.resample;call (iter1_perm RRO.I iter_perm2).
      auto=> ? &mr [#] 2-> Hmem /= ? -> /=.
      apply/uniq_perm_eq=> /=.
      + by rewrite -FSet.memE !FSet.inE /= FSet.uniq_elems.
      + exact/FSet.uniq_elems.
      move=> x'; rewrite -!FSet.memE !FSet.inE mem_fdom; case: (x' = x{mr})=> //= <<-.
      by rewrite dom_restr /in_dom_with mem_set get_setE.
    + by move=> ? &mr [#] 2-> ?; exists FRO.m{mr} x{mr}.
    inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample; wp; swap{1} -1.
    seq  1  7: (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
                l{2} = (FSet.elems (fdom (restr Unknown FRO.m))){1} /\
                (FRO.m.[x]){2} = Some(c{1},Unknown) /\ (FRO.m.[x]){1} = None).
    + wp; rnd; auto=> ? &mr [#] 2->; rewrite domE sampleto_ll /= => Heq ? _ ? ->; do !split=> //=.
      + have ->: pred1 x{mr} = predU (pred1 x{mr}) (pred1 x{mr}).
        + by apply/fun_ext=> z /#.
        exact/eq_exceptmS/eq_except_setr.
      + congr; apply/FSet.fsetP=> z; rewrite !FSet.inE !mem_fdom !dom_restr /in_dom_with.
        by rewrite mem_set get_setE; case: (z = x{mr})=> //= <<-; rewrite domE Heq.
      + by rewrite get_setE.
    exists* x{1},c{1}; elim* => x1 c1; pose mx2:= Some(c1,Unknown).
    call (iter_inv RRO.I (fun z=> x1 <> z) 
           (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= None /\ o2.[x1]=mx2) _).
    + by conseq (I_f_eqex x1 None mx2).
    auto=> &1 |> &2 eqe_m1_m2 m2_x m1_x; split=> [|_ mL mR /eq_exceptP eqe_x_mL_mR mL_x mR_x].
    + move=> x2; rewrite -FSet.memE mem_fdom dom_restr /in_dom_with domE; case: (x{2} = x2)=> //= <<-.
      by rewrite m1_x.
    rewrite domE mL_x /=; apply/fmap_eqP=> z; rewrite get_setE; case: (z = x{2})=> [<<-|/eqe_x_mL_mR] //.
    by rewrite mR_x m2_x.
  rcondf{2} 2; 1:by auto. 
  swap{1} 2 -1; inline*; auto.
  while (={l,FRO.m} /\ (x \in FRO.m){1}); auto.
  by move=> ? &mr [#] 2-> Hm Hl _ /= ? -> ;rewrite mem_set Hm.
  qed.

  (* ------------------------------------------------------------------------ *)
  (* Equivalence of FRO and RRO: general experiment *)
  section.
    declare module D:FRO_Distinguisher {FRO}.

    lemma eager_D : eager [RRO.resample(); , D(FRO).distinguish ~ 
                           D(RRO).distinguish, RRO.resample(); :
                             ={glob D,FRO.m} ==> ={FRO.m, glob D} /\ ={res} ].
    proof.
    eager proc (H_: RRO.resample(); ~ RRO.resample();: ={FRO.m} ==> ={FRO.m})
               (={FRO.m})=>//; try by sim.
    + by apply eager_init.
    + by apply eager_get.
    + by apply eager_set.
    + by apply eager_rem.
    + by apply eager_sample.
    + by apply eager_in_dom.
    + by apply eager_restrK.
    qed.

    module Eager (D:FRO_Distinguisher) = {
      proc main1() = {
        var b;
        FRO.init();
        b <@ D(FRO).distinguish();
        return b;
      }

      proc main2() = {
        var b;
        FRO.init();
        b <@ D(RRO).distinguish();
        RRO.resample();
        return b;
      }
    }.

    equiv Eager_1_2: Eager(D).main1 ~ Eager(D).main2 : 
      ={glob D} ==> ={res,glob FRO, glob D}.
    proof.
    proc. transitivity{1}
      { FRO.init(); RRO.resample(); b <@ D(FRO).distinguish(); }
      (={glob D} ==> ={b,FRO.m,glob D})
      (={glob D} ==> ={b,FRO.m,glob D})=> //.
    + by move=> ? &mr ->; exists (glob D){mr}.
    + inline *; rcondf{2} 3; 2:by sim.
      auto=> />. apply/perm_eq_small=> //=; apply/uniq_perm_eq=> //.
      + exact/FSet.uniq_elems.
      by move=> z; rewrite -FSet.memE mem_fdom dom_restr /in_dom_with mem_empty.
    seq  1  1: (={glob D, FRO.m}); 1:by inline *; auto.
    by eager call eager_D.
    qed.
  end section.

  equiv LRO_RRO_init :
    LRO.init ~ RRO.init :
      true ==> RO.m{1} = restr Known FRO.m{2}.
  proof. by proc; auto=> /=; rewrite restr0. qed.

  equiv LRO_RRO_get : LRO.get ~ RRO.get :
      ={x} /\ RO.m{1} = restr Known FRO.m{2}
    ==> ={res} /\ RO.m{1} = restr Known FRO.m{2}.
  proof. 
  proc;auto=> ? &ml [] -> -> /= ? -> /=.
  rewrite dom_restr /in_dom_with negb_and neqK_eqU.
  rewrite !restr_set /= !get_set_sameE oget_some=> />.
  by rewrite negb_or/= restrP domE /#.
  qed.

  equiv LRO_RRO_set : LRO.set ~ RRO.set :
    ={x,y} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
  proof. by proc; auto=> ? &ml [#] 3->; rewrite restr_set. qed.

  equiv LRO_RRO_rem : LRO.rem ~ RRO.rem :
    ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
  proof. 
  proc; inline *; auto=> ? &mr [#] -> ->; rewrite restr_rem.
  case (in_dom_with FRO.m{mr} x{mr} Known)=> // Hidw.
  apply/fmap_eqP=> x'; rewrite remE; case: (x' = x{mr})=> //= ->>.
  by move: Hidw; rewrite -dom_restr domE=> /= ->.
  qed.

  equiv LRO_RRO_sample : LRO.sample ~ RRO.sample:
    ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
  proof. 
  proc; auto=> ? &ml [] _ ->; rewrite sampleto_ll=> ? ?; rewrite restr_set /= =>Hnd.
  apply/fmap_eqP=> x'; rewrite remE; case: (x' = x{ml})=> //= ->>.
  by move: Hnd; rewrite restrP domE=> /= ->.
  qed.

  equiv LRO_RRO_D (D<:RO_Distinguisher{RO,FRO}) : 
    D(LRO).distinguish ~ D(RRO).distinguish : 
      ={glob D} /\ RO.m{1} = restr Known FRO.m{2} ==>
      ={res,glob D} /\ RO.m{1} = restr Known FRO.m{2}.
  proof.
  proc (RO.m{1} = restr Known FRO.m{2})=> //.
  + by conseq LRO_RRO_init.
  + by conseq LRO_RRO_get.
  + by conseq LRO_RRO_set.
  + by conseq LRO_RRO_rem.
  by conseq LRO_RRO_sample. 
  qed.

  section.
    declare module D : RO_Distinguisher{RO,FRO}.

    local module M = {
      proc main1() = {
        var b;
        RRO.resample();
        b <@ D(FRO).distinguish();
        return b;
      }

      proc main2() = {
        var b;
        b <@ D(RRO).distinguish();
        RRO.resample();
        return b;
      }
    }.

    lemma RO_LRO_D : 
      equiv [D(RO).distinguish ~ D(LRO).distinguish : 
        ={glob D,RO.m} ==> ={res,glob D}].
    proof.
    transitivity M.main1 
       (={glob D} /\ FRO.m{2} = map (fun _ c => (c,Known)) RO.m{1} ==>
          ={res,glob D})
       (={glob D} /\ FRO.m{1} = map (fun _ c => (c,Known)) RO.m{2} ==>
          ={res,glob D})=>//.
    + by move=> ? &mr [] 2->; exists (glob D){mr} (map(fun _ c =>(c,Known))RO.m{mr}).
    + proc*; inline M.main1; wp; call (RO_FRO_D D); inline *.
      rcondf{2} 2; auto.
      + move=> &mr [] _ ->; apply mem_eq0=> z.
        rewrite -FSet.memE mem_fdom dom_restr /in_dom_with mapE mem_map domE.
        by case: (RO.m{m}.[_]).
      move=> /> &mr; rewrite map_comp /fst /=.
      by apply/fmap_eqP=> z; rewrite mapE /=; case: (_.[z]).
    transitivity M.main2
       (={glob D, FRO.m} ==> ={res, glob D})
       (={glob D} /\ FRO.m{1} = map (fun _ c => (c,Known)) RO.m{2} ==>
          ={res,glob D})=>//.
    + by move=> ? &mr [] 2->; exists (glob D){mr} (map(fun _ c =>(c,Known))RO.m{mr}).
    + by proc; eager call (eager_D D); auto.
    proc*; inline M.main2; wp; call{1} RRO_resample_ll.
    symmetry; call (LRO_RRO_D D); auto=> &ml &mr [#] 2->; split=> //=.
    by apply/fmap_eqP=> x; rewrite restrP mapE; case: (RO.m{ml}.[x]).
    qed.
  end section.

end GenEager.
