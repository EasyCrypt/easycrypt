(* ==================== Programmable Random Oracle ==================== *)

require import Core List SmtMap FSet Distr.
require IterProc.

(* flag type for use with flagged maps of SmtMap: ('from, 'to * 'flag) fmap *)
type flag = [ Unknown | Known ].  (* map setting known by distinguisher? *)

lemma neqK_eqU f : f <> Known <=> f = Unknown.
proof. by case: f. qed.

(* -------------------------------------------------------------------- *)
(* Random Oracles and Flag Random Oracles                               *)

abstract theory Ideal.

type from, to, input, output.

op sampleto : from -> to distr.

module type RO = {
  proc init  ()                  : unit
  proc get   (x : from)          : to
  proc set   (x : from, y : to)  : unit
  proc rem   (x : from)          : unit
  proc sample(x : from)          : unit
}.

module type RO_Distinguisher(G : RO) = {
  proc distinguish(_:input): output 
}.

module type FRO = {
  proc init  ()                   : unit
  proc get   (x : from)           : to
  proc set   (x : from, y : to)   : unit
  proc rem   (x : from)           : unit 
  proc sample(x : from)           : unit
  (****)
  proc in_dom(x : from, f : flag) : bool
  proc restrK()                   : (from, to) fmap
}.

module type FRO_Distinguisher(G : FRO) = {
  proc distinguish(_ : input): output
}.

module RO : RO = {
  var m : (from, to) fmap

  proc init () = { m <- empty; }

  proc get(x : from) = {
    var r;
    r <$ sampleto x;
    if (! dom m x) m.[x] <- r;
    return (oget m.[x]);
  }

  proc set(x : from, y : to) = {
    m.[x] <- y;
  }

  proc rem(x : from) = {
    m <- rem m x;
  }

  proc sample(x : from) = {
    get(x);
  }

  proc restrK() = {
    return m;
  }
}.

module FRO : FRO = {
  var m : (from, to * flag) fmap

  proc init() = { m <- empty; }

  proc get(x : from) = {
    var r;
    r <$ sampleto x;
    if (dom m x) r <- (oget m.[x]).`1;
    m.[x] <- (r, Known);
    return r;
  }

  proc set(x : from, y : to) = {
    m.[x] <- (y, Known);
  }

   proc rem(x : from) = {
    m <- rem m x;
  }

  proc sample(x : from) = {
    var c;
    c <$ sampleto x;
    if (! dom m x) m.[x] <- (c, Unknown);
  }

  proc in_dom(x : from, f : flag) = {
    return in_dom_with m x f;
  }

  proc restrK() = {
    return restr Known m;
  }
}.

equiv RO_FRO_init : RO.init ~ FRO.init : true ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> /=; rewrite /noflags map_empty. qed.

equiv RO_FRO_get : RO.get ~ FRO.get :
   ={x} /\ RO.m{1} = noflags FRO.m{2} ==> ={res} /\ RO.m{1} = noflags FRO.m{2}.
proof.
  proc; auto=> &1 &2 [] 2!-> /= ? -> /=.
  rewrite mem_map /noflags !map_set /fst /= get_set_sameE => |>; progress.
  + by rewrite mapE oget_omap_some 1:-domE.
  + by rewrite eq_sym set_get_eq 1:mapE /= 1:get_some.
qed.

equiv RO_FRO_set : RO.set ~ FRO.set :
   ={x, y} /\ RO.m{1} = noflags FRO.m{2} ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> &1 &2 [#] 3->; rewrite /noflags map_set. qed.

equiv RO_FRO_rem : RO.rem ~ FRO.rem :
   ={x} /\ RO.m{1} = noflags FRO.m{2} ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> ? ?; rewrite /noflags map_rem. qed.

equiv RO_FRO_sample : RO.sample ~ FRO.sample :
   ={x} /\ RO.m{1} = noflags FRO.m{2} ==> RO.m{1} = noflags FRO.m{2}.
proof. 
  by proc; inline *; auto=> &1 &2 [] 2!-> /= ? ->; rewrite mem_map /noflags map_set.
qed.

lemma RO_FRO_D (D <: RO_Distinguisher{RO, FRO}) :
  equiv [D(RO).distinguish ~ D(FRO).distinguish : 
         ={arg, glob D} /\ RO.m{1} = noflags FRO.m{2} ==>
         ={res, glob D} /\ RO.m{1} = noflags FRO.m{2}].
proof.
  proc (RO.m{1} = noflags FRO.m{2})=> //.
  + by conseq RO_FRO_init.
  + by conseq RO_FRO_get.
  + by conseq RO_FRO_set. 
  + by conseq RO_FRO_rem.
  + by conseq RO_FRO_sample.
qed.

section LL. 

lemma RO_init_ll : islossless RO.init.
proof. by proc; auto. qed.

lemma FRO_init_ll : islossless FRO.init.
proof. by proc; auto. qed.

lemma FRO_in_dom_ll : islossless FRO.in_dom.
proof. by proc. qed.

lemma FRO_restrK_ll : islossless FRO.restrK.
proof. by proc. qed.

lemma RO_set_ll : islossless RO.set.
proof. by proc; auto. qed.

lemma FRO_set_ll : islossless FRO.set.
proof. by proc; auto. qed.

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

lemma RO_get_ll : islossless RO.get.
proof. by proc; auto; progress; apply sampleto_ll. qed.

lemma FRO_get_ll : islossless FRO.get.
proof. by proc; auto; progress; apply sampleto_ll. qed.

lemma RO_sample_ll : islossless RO.sample.
proof. by proc; call RO_get_ll. qed.

lemma FRO_sample_ll : islossless FRO.sample.
proof. by proc; auto; progress; apply sampleto_ll. qed.

end section LL.
 
end Ideal.

(* -------------------------------------------------------------------- *)
abstract theory GenEager.

clone include Ideal. 

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

clone include IterProc with type t <- from.

(* RRO is an FRO that resamples a query if the associated value is
 * unknown; it also has a resample procedure that resamples all
 * queries whose results are unknown.
 *
 * Uses the map of FRO
 *)

module RRO : FRO = {
  proc init = FRO.init

  proc get(x : from) = {
    var r;
    r <$ sampleto x;
    if (! dom FRO.m x || (oget FRO.m.[x]).`2 = Unknown) {
      FRO.m.[x] <- (r, Known);
    }
    return (oget FRO.m.[x]).`1;
  }

  proc set = FRO.set 

  proc rem = FRO.rem

  proc sample = FRO.sample

  proc in_dom = FRO.in_dom

  proc restrK = FRO.restrK

  module I = {
    proc f(x : from) = {
      var c;
      c <$ sampleto x;
      FRO.m.[x] <- (c, Unknown);
    }
  }

  proc resample () = {
    Iter(I).iter (elems (fdom (restr Unknown FRO.m)));
  }
}.

(* LRO is an RO whose sample procedure is lazy, i.e., does nothing.
 *
 * Uses the map of RO.
 *)

module LRO : RO = {
  proc init = RO.init

  proc get = RO.get

  proc set = RO.set 

  proc rem = RO.rem

  proc sample(x : from) = {}
}.

lemma RRO_resample_ll : islossless RRO.resample.
proof. 
  proc; call (iter_ll RRO.I _)=> //; proc; auto=> /= ?.
  by split; first apply sampleto_ll. 
qed.

(* now we use the eager tactics to show a series of lemmas
   of the form

    eager [RRO.resample();, FRO.<proc> ~ RRO.<proc>, RRO.resample(); :
           ={?<arg>, FRO.m} ==> ={?res, FRO.m}].

   where <proc> ranges over init, get, set, rem, sample, in_dom and
   restrK *)

lemma eager_init :
  eager [RRO.resample();, FRO.init ~ RRO.init, RRO.resample(); :
         ={FRO.m} ==> ={FRO.m}].
proof.
  eager proc. inline{2} *; rcondf{2} 3; auto=> /=.
  + by move=> ? _; rewrite restr0 fdom0 elems_fset0.
  + by conseq _ (_ : true ==> true: = 1%r) _ => //; call RRO_resample_ll.
qed.

lemma iter_perm2 (i1 i2 : from) :
  equiv [Iter(RRO.I).iter_12 ~ Iter(RRO.I).iter_21 :
         ={glob RRO.I, t1, t2} ==> ={glob RRO.I}].
proof.
  proc; inline *; case ((t1 = t2){1}); 1:by auto.
  * swap{2} [4..5] -3; auto=> &ml &mr [#] 3-> neq /= ? -> ? ->.
    by rewrite set_setE (eq_sym t2{mr}) neq.
qed.

equiv I_f_neq x1 mx1 : RRO.I.f ~ RRO.I.f :
    ={x, FRO.m} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = mx1 ==>
    ={FRO.m} /\ FRO.m{1}.[x1] = mx1.
proof.
  by proc; auto=> ? &mr [#] 2-> Hneq Heq /= ? ->; rewrite get_setE Hneq.
qed.

equiv I_f_eqex x1 mx1 mx2 : RRO.I.f ~ RRO.I.f :
    ={x} /\ x1 <> x{1} /\ eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\
    FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2 ==>
    eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\
    FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2.
proof.
  proc; auto=> ? &mr [#] -> Hneq Heq /= Heq1 Heq2 ? -> /=.
  by rewrite !get_setE Hneq eq_except_set_eq.
qed.

equiv I_f_set x1 r1 : RRO.I.f ~ RRO.I.f :
  ={x} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = None /\
  FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)] ==>
  FRO.m{1}.[x1] = None /\ FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)].
proof.
  proc; auto=> ? &mr [#] -> Hneq H1 -> /= ? ->.
  by rewrite get_setE Hneq/= set_setE (eq_sym _ x1) Hneq.
qed.

lemma eager_get :
  eager [RRO.resample();, FRO.get ~ RRO.get, RRO.resample(); :
         ={x, FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc.
  wp; case ((dom FRO.m x /\ (oget FRO.m.[x]).`2=Known){1}).
  + rnd{1}; rcondf{2} 2; 1:by auto=> /> _ _ ->.
    exists* x{1}, ((oget FRO.m.[x{2}]){1}); elim*=> x1 mx; inline RRO.resample.
    call (iter_inv RRO.I (fun z=> x1<>z)
                   (fun o1 o2 => o1 = o2 /\ o1.[x1]= Some mx) _)=> /=.
    + by conseq (I_f_neq x1 (Some mx))=> //.
    auto=> ? &mr [#] 4-> Hd Hget; split; first apply sampleto_ll.
    move=> /= _ ? _; split.
    + rewrite -some_oget // /= => z.
      rewrite -memE mem_fdom dom_restr /in_dom_with.
      by case (x{mr} = z)=> [<- | //]; rewrite Hget.
    move=> [#] _ Heq ? mr [#] -> Heq'.
    split=> [| _ r _]; first apply sampleto_ll.
    by rewrite domE Heq' /= set_get_eq 1:Heq' 1:{1}(pairS (oget FRO.m{mr}.[x{mr}])) 1:Hget.
  case ((dom FRO.m x){1}).
  + inline{1} RRO.resample=> /=; rnd{1}.
    transitivity{1} 
      { Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); }
      (={x, FRO.m} /\ dom FRO.m{1} x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x, FRO.m})
      (={x, FRO.m} /\ dom FRO.m{1} x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
       FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
       FRO.m{2}.[x{2}] = Some (result{2}, Known)).
    + move=> ? &mr [#] -> -> /negb_and [] // H1 H2; exists FRO.m{mr} x{mr};
      move=> />; by rewrite -neqK_eqU.
    + move=> ? ? ?; rewrite domE=> [#] <*> [#] -> /eq_except_sym H Hxm Hx2.
      split=> [| _ r _]; first apply sampleto_ll.
      rewrite /= Hxm /=; apply /eq_sym.
      have /(congr1 oget) /= <- := Hx2; apply eq_except_set_getlr=> //.
      by rewrite domE Hx2.
    + symmetry; call (iter1_perm RRO.I iter_perm2).
      skip=> &1 &2 [[->> ->>]] [Hdom Hm]; split=> //=.
      by apply /perm_eq_sym/perm_to_rem/mem_fdom/dom_restr;
        rewrite /in_dom_with Hdom Hm.      
    inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample.
    seq 5 3 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
               (l = elems(fdom (restr Unknown FRO.m) `\` fset1 x)){1} /\
               FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
               FRO.m{2}.[x{2}] = Some (result{2}, Known)).
    + auto=> ? &mr [#] 2-> /= ^Hdom -> ^Hget -> ? -> /=.
      by rewrite !get_setE /= !restr_set /= fdom_set eq_except_setlr //= fsetDK.
    exists* x{1}, FRO.m{1}.[x{2}], FRO.m{2}.[x{2}]; elim*=> x1 mx1 mx2.
    call (iter_inv RRO.I (fun z => x1 <> z) 
           (fun o1 o2 =>
              eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\ o2.[x1] = mx2) 
           (I_f_eqex x1 mx1 mx2)); auto=> /> &1 &2 eq_exc get1_x2 get2_x2.
      split. split=> [| x2].
      congr; rewrite fsetP=> y; rewrite in_fsetD1 2!mem_fdom.
      case (y = x{2})=> [->/= | ne_y_x2 /=].
      by rewrite dom_restr /in_dom_with get2_x2.
      rewrite 2!dom_restr /in_dom_with; rewrite eq_exceptP in eq_exc.
      have ^ get_y_eq -> := eq_exc y _. by rewrite /pred1.
      split=> />; by rewrite !domE get_y_eq.
      by rewrite -memE in_fsetD1 eq_sym.
      by rewrite get1_x2 get2_x2.
  swap{1} -1; seq 1 1 : (={r, x, FRO.m} /\ ! dom FRO.m{1} x{1}); 1:by auto. 
  inline RRO.resample; exists* x{1},r{1}; elim*=> x1 r1.
  call (iter_inv RRO.I (fun z=> x1<>z) 
           (fun o1 o2 => o1.[x1] = None /\ o2 = o1.[x1 <- (r1, Known)])
           (I_f_set x1 r1)); auto.
    move=> ? &mr [#] 5-> ^ Hnin ^ + -> /=; rewrite domE=> /= -> /=;
    rewrite get_setE /=; split=> [| _]. split=> [| y].
    congr; rewrite fsetP=> y;
      rewrite 2!mem_fdom 2!dom_restr /in_dom_with mem_set get_setE.
    case (y = x{mr})=> // ->;
      rewrite Hnin // -memE mem_fdom dom_restr /in_dom_with.
    rewrite -memE mem_fdom dom_restr /in_dom_with;
      case (x{mr} = y)=> [<- [#] // | //].
    move=> /> m_L; by rewrite domE.
qed.

lemma eager_set :
  eager [RRO.resample();, FRO.set ~ RRO.set, RRO.resample(); :
         ={x, y} /\ ={FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc.
  inline RRO.resample=> /=; wp.
  case ((dom FRO.m x /\ (oget FRO.m.[x]).`2 = Unknown){1}).
  + transitivity{1}
      { Iter(RRO.I).iter_1s(x, elems (fdom (restr Unknown FRO.m) `\` fset1 x)); }
      (={x, y, FRO.m} /\ dom FRO.m{1} x{1} /\
       (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x, y, FRO.m})
      (={x, y, FRO.m} /\ dom FRO.m{1} x{1} /\
       (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x, y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
       FRO.m{2}.[x{2}] = Some (y{2},Known)).
    + by move=> &ml &mr [#] 3-> x_in_m get_m_x_2_unk;
        exists FRO.m{mr} x{mr} y{mr}.
    + move=> ? &m &mr [#] <*> [#] 2-> Hex Hm2.
      by rewrite (eq_except_set_getlr FRO.m{mr} FRO.m{m} x{mr}) ?in_dom ?Hm2 //
         1:domE 1:Hm2 // eq_except_sym.
    + symmetry; call (iter1_perm RRO.I iter_perm2); auto=> ? &mr [#] 3 -> Hdom Hm;
      split=> //=.
      by apply /perm_eq_sym/perm_to_rem/mem_fdom/dom_restr; rewrite /in_dom_with Hdom.
    inline{1} Iter(RRO.I).iter_1s. 
    seq 3 1 :
      (={x, y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
       l{1} = (elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
       (FRO.m.[x] = Some (y, Known)){2}).
    + inline *; auto=> ? &mr [#] 3-> /= Hmem Hget.
      split=> [|_ c _]; first apply sampleto_ll.
      by rewrite (eq_except_setlr _ _ _ (c, Unknown)) //=
                 get_set_sameE restr_set /= fdom_rem /= -memE in_fsetD1.
    exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1;
      pose mx2 := Some (y1, Known).
    call (iter_inv RRO.I (fun z=> x1<>z) 
           (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                         o2.[x1] = mx2) 
           (I_f_eqex x1 mx1 mx2));
        auto=> &1 &2 /> eq_exc not_x2_in_unkn_m2 get_m2_x2_eq.
      split=> [x0 |].
      by rewrite -memE mem_fdom dom_restr /in_dom_with;
        case (x{2} = x0)=> // <-; rewrite get_m2_x2_eq.
      by rewrite get_m2_x2_eq.
  exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1;
    pose mx2 := Some (y1, Known).
  call (iter_inv RRO.I (fun z=> x1<>z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                       o2.[x1] = mx2) 
         (I_f_eqex x1 mx1 mx2))=> /=; auto=> &1 &2 /> /negb_and x2_disj.
    split=> [| _ _ _ m_L m_R eq_exc m_L_x2_eq m_R_x2_eq];1: split.
    + congr; rewrite fsetP=> z; rewrite 2!mem_fdom 2!dom_restr /in_dom_with mem_set.
      case (z = x{2})=> [-> /=| ne_z_x2 /=].
      + by rewrite get_set_sameE /= negb_and.
      by rewrite get_setE ne_z_x2.
    split=> [x0 |].
    + rewrite -memE mem_fdom dom_restr /in_dom_with.
      by case (x{2} = x0)=> [<- [#] | //]; by elim x2_disj.
      by rewrite get_set_sameE /mx2 /= eq_except_setr.
    rewrite get_set_sameE in m_R_x2_eq.
    rewrite -fmap_eqP=> z; rewrite get_setE; case (z = x{2})=> [-> |].
    + by rewrite -m_R_x2_eq.
    by move=> ne_z_x2; rewrite eq_exceptP in eq_exc; rewrite eq_exc /pred1.
qed.

lemma eager_rem :
  eager [RRO.resample();, FRO.rem ~ RRO.rem, RRO.resample(); :
         ={x} /\ ={FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc; case ((in_dom_with FRO.m x Unknown){1}).
  + inline RRO.resample; wp.
    transitivity{1} 
      { Iter(RRO.I).iter_1s(x, elems (fdom (restr Unknown FRO.m) `\` fset1 x)); }
      (={x, FRO.m} /\ (in_dom_with FRO.m x Unknown){1}==> ={x, FRO.m}) 
      (={x, FRO.m} /\ (in_dom_with FRO.m x Unknown){1} ==>
       (rem FRO.m x){1} = FRO.m{2})=> //.
    + by move=> ? &mr [#] 2-> ?; exists FRO.m{mr} x{mr}.   
    + symmetry; call (iter1_perm RRO.I iter_perm2);
        skip=> ? &mr [#] 2! -> ? /=; split=> //.
      by apply /perm_eq_sym /perm_to_rem /mem_fdom /dom_restr. 
    inline{1} Iter(RRO.I).iter_1s.
    seq 3 1: (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
              l{1} = (elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
              (FRO.m.[x] = None){2}).
    + inline *; auto=> &1 &2 [#] 2-> Hidm /=.
      split=> [| _ c _]; first apply sampleto_ll.
      rewrite (eq_except_remr (pred1 x{2}) _ FRO.m{2} x{2}) /pred1 //
              1:eq_except_setl /=.
      rewrite remE -memE in_fsetD1 negb_and /= restr_rem Hidm /=.
      congr; by rewrite fdom_rem.
    exists* x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1.
    call (iter_inv RRO.I (fun z=> x1<>z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                       o2.[x1] = None) _).
    + by conseq (I_f_eqex x1 mx1 None).
    auto=> &1 &2 [#] 3-> Hex -> Hx -> /=.
    split=> [ | _ mL mR [#] /eq_exceptP Hex' ? Heq].
    move=> /> z.
    rewrite -memE mem_fdom dom_restr /in_dom_with.
    rewrite -memE mem_fdom dom_restr /in_dom_with in Hx.
    case (x{2} = z) => [<- // | //].
    apply fmap_eqP=> z; rewrite remE; case (z = x{2})=> [-> /= | Hneq];
      [by rewrite Heq | by apply Hex'].
  inline RRO.resample; wp.
  exists *x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1.
  call (iter_inv RRO.I (fun z=> x1<>z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                       o2.[x1]=None) _).
  + by conseq (I_f_eqex x1 mx1 None).
  auto=> ? &mr [#] 4-> /= Hin; rewrite restr_rem Hin /= remE.
  split=> [| _ m_L m_R [#] Heqx m_L_x m_R_x]. split=> [z |].
  rewrite -memE mem_fdom dom_restr /in_dom_with.
  rewrite /in_dom_with in Hin.
  case (x{mr} = z) => [<- // | //].
  split=> //; rewrite eq_except_remr //.
  rewrite -fmap_eqP=> z; rewrite remE.
  case (z = x{mr})=> [-> | ne_z_xmr];
    [by rewrite m_R_x |
     by rewrite eq_exceptP in Heqx; rewrite Heqx /pred1].
qed.

lemma eager_sample :
  eager [RRO.resample();, FRO.sample ~ RRO.sample, RRO.resample(); :
         ={x, FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc.
  case (! dom (FRO.m{2}) x{2}).
  + rcondt{2} 2 ; 1:by auto.
    transitivity{2}
      { c <$ sampleto x; FRO.m.[x] <- (c, Unknown);
        Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); }
      (={x, FRO.m} /\ ! dom FRO.m{2} x{2} ==> ={x, FRO.m}) 
      (={x, FRO.m} /\ ! dom FRO.m{2} x{2} ==> ={x, FRO.m})=>//; last first.
    + inline{2} RRO.resample; call (iter1_perm RRO.I iter_perm2);
        auto=> ? &mr [#] 2-> Hmem /= ? -> /=.
      by apply /perm_eq_sym /perm_to_rem; rewrite restr_set /= mem_fdom mem_set.
    + by move=> ? &mr [#] 2-> ?; exists FRO.m{mr} x{mr}.
    inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample; wp; swap{1} -1.
    seq 1 7 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
               l{2} = (elems (fdom (restr Unknown FRO.m))){1} /\
               (FRO.m.[x]){2} = Some (c{1}, Unknown) /\ (FRO.m.[x]){1} = None).
    + wp; rnd; auto=> ? &mr [#] 2->; rewrite domE /=.
      move=> Heq; split; first apply sampleto_ll.
      move=> _ c _ cL ?; split=> // _.
      rewrite get_set_sameE restr_set /=.
      split; first rewrite set_set_sameE eq_except_setr.
      split=> //.
      congr; rewrite fsetP=> z;
        rewrite in_fsetD1 !mem_fdom  mem_set !dom_restr /in_dom_with.
      case (z = x{mr})=> [-> | //]; by rewrite domE Heq.
    exists* x{1}, c{1}; elim*=> x1 c1; pose mx2 := Some (c1, Unknown).
    call (iter_inv RRO.I (fun z=> x1<>z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= None /\
                       o2.[x1]=mx2) _).
    + by conseq (I_f_eqex x1 None mx2).
    auto=> ? &mr [#] 2<- -> Hex 2!-> ^ Hx1 -> /=.
    split. split.
    move=> z; rewrite -memE mem_fdom dom_restr /in_dom_with.
    case (x{mr} = z)=> [<- [#] | //]; by rewrite domE.
    split=> //.
    move=> _ m_L m_R [#] Hex' m_L_x m_R_x.
    case (x{mr} \in m_L)=> [x_in /= | x_not_in /=].
    rewrite -fmap_eqP=> z.
    case (z = x{mr})=> [| ne_z_xmr].
    by rewrite domE in x_in.
    rewrite eq_exceptP in Hex'; rewrite Hex'.
    by rewrite /pred1.
    by rewrite domE // in x_in.
    rewrite -fmap_eqP=> z.
    case (z = x{mr})=> [-> | ne_z_xmr].
    by rewrite get_set_sameE m_R_x /mx2.
    rewrite get_setE ne_z_xmr /=.
    rewrite eq_exceptP in Hex'.
    by rewrite Hex' /pred1.
  rcondf{2} 2; 1:by auto. 
  swap{1} 2 -1; inline*; auto.
  while (={l, FRO.m} /\ (dom FRO.m x){1}); auto.
  move=> ?&mr [#] 2-> Hm Hl _ /= ? ->; rewrite -mem_fdom fdom_set in_fsetU.
  left; by rewrite mem_fdom.
qed.

lemma eager_in_dom :
  eager [RRO.resample();, FRO.in_dom ~ RRO.in_dom, RRO.resample(); :
         ={x, f} /\ ={FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc; inline *; wp.
  while (={l, FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         in_dom_with FRO.m{1} x{1} f{1} = result{2}).
  + auto=> &1 &2 [#] 2-> Hz <- l2_nonemp _ /= ? -> /=. 
    split=>[z /mem_drop Hm |].
    rewrite /in_dom_with mem_set get_setE;
      case (z = head witness l{2})=> [-> //= | ne /=].
    by rewrite /in_dom_with in Hz; rewrite Hz.
    rewrite /in_dom_with mem_set get_setE.
    case (x{1} = head witness l{2})=> [-> /= | //].
    rewrite /in_dom_with in Hz.
    have [# -> -> //] :
      (head witness l{2} \in FRO.m{2}) /\
      (oget FRO.m{2}.[head witness l{2}]).`2 = Unknown
    by rewrite (Hz (head witness l{2}))
         -(mem_head_behead witness l{2} l2_nonemp (head witness l{2})); left.
  by auto=> ? &mr /= [#] 3-> /=; split=>// z; rewrite -memE mem_fdom dom_restr. 
qed.

lemma eager_restrK :
  eager [RRO.resample();, FRO.restrK ~ RRO.restrK, RRO.resample(); :
         ={FRO.m} ==> ={res, FRO.m}].
proof.
  eager proc; inline *; wp.
  while (={l, FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         restr Known FRO.m{1} = result{2}).
  + auto=> &1 &2 [#] 2-> Hz <- l2_nonemp _ /= ? -> /=.
    split=>[z /mem_drop Hm |];1:rewrite /in_dom_with mem_set get_setE.
    + by case (z = head witness l{2})=> [-> | ne] //=; apply/Hz/Hm.
    rewrite restr_set rem_id ?dom_restr //.
    by move: l2_nonemp=> /(mem_head_behead witness) /(_ (head witness l{2}))
                         /= /Hz @/in_dom_with />;
       rewrite neqK_eqU.
  by auto=> ? &mr /= -> /=; split=> // z; rewrite -memE mem_fdom dom_restr. 
qed.

section.

declare module D : FRO_Distinguisher {FRO}.

lemma eager_D :
  eager [RRO.resample();, D(FRO).distinguish ~ 
         D(RRO).distinguish, RRO.resample(); :
         ={glob D, FRO.m, arg} ==> ={FRO.m, glob D} /\ ={res}].
proof.
  eager proc (H_: RRO.resample(); ~ RRO.resample();: ={FRO.m} ==> ={FRO.m})
             (={FRO.m}) =>//; try by sim.
  + by apply eager_init. + by apply eager_get. + by apply eager_set. 
  + by apply eager_rem. + by apply eager_sample. 
  + by apply eager_in_dom. + by apply eager_restrK. 
qed.

module Eager (D : FRO_Distinguisher) = {
  proc main1(x:input) = {
    var b;
    FRO.init();
    b <@ D(FRO).distinguish(x);
    return b;
  }

  proc main2(x:input) = {
    var b;
    FRO.init();
    b <@ D(RRO).distinguish(x);
    RRO.resample();
    return b;
  }
}.

equiv Eager_1_2 : Eager(D).main1 ~ Eager(D).main2 :
  ={glob D, arg} ==> ={res, glob FRO, glob D}.
proof.
  proc.
  transitivity{1} 
    { FRO.init(); RRO.resample(); b <@ D(FRO).distinguish(x); }
    (={glob D, x} ==> ={b, FRO.m, glob D})
    (={glob D, x} ==> ={b, FRO.m, glob D})=> />. 
  + by move=> /> &mr; exists (glob D){mr} x{mr}.
  + inline *; rcondf{2} 3; 2:by sim.
    by auto=> ?; rewrite restr0 fdom0 elems_fset0.
  seq 1 1 : (={glob D, FRO.m, x}); 1:by inline *; auto.
  by eager call eager_D. 
qed.

end section.

(* now we show we can move from LRO to RRO as long as their maps agree
   on known (in RRO) settings *)

equiv LRO_RRO_init : LRO.init ~ RRO.init : true ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc; auto=> /=; rewrite restr0. qed.

equiv LRO_RRO_get : LRO.get ~ RRO.get :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==>
   ={res} /\ RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc; auto=> ? &ml [] -> -> /= ? -> /=.
  rewrite dom_restr orabP negb_and neqK_eqU.
  rewrite !restr_set /= !get_set_sameE ; progress.
  move: H; rewrite negb_or /= restrP domE.
  by move=> [/some_oget -> /=]; rewrite -neqK_eqU /= => ->.
qed.

equiv LRO_RRO_set : LRO.set ~ RRO.set :
   ={x, y} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc; auto=> ? &ml [#] 3->; rewrite restr_set. qed.

equiv LRO_RRO_rem : LRO.rem ~ RRO.rem :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc; inline *; auto=> ? &mr [#] -> ->. rewrite restr_rem.
  case (in_dom_with FRO.m{mr} x{mr} Known)=>// Hidw.
  by rewrite rem_id // dom_restr.
qed.

equiv LRO_RRO_sample : LRO.sample ~ RRO.sample :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc; auto=> ? &ml [] _ ->.
  split=> [| _ ? _]; first apply sampleto_ll.
  rewrite restr_set /==> Hnd. 
  by rewrite rem_id // dom_restr /in_dom_with Hnd.
qed.

lemma LRO_RRO_D (D <: RO_Distinguisher{RO, FRO}) :
  equiv [D(LRO).distinguish ~ D(RRO).distinguish : 
         ={glob D, arg} /\ RO.m{1} = restr Known FRO.m{2} ==>
         ={res, glob D} /\ RO.m{1} = restr Known FRO.m{2}].
proof.
  proc (RO.m{1} = restr Known FRO.m{2})=> //.
  + by conseq LRO_RRO_init. + by conseq LRO_RRO_get. + by conseq LRO_RRO_set.
  + by conseq LRO_RRO_rem. + by conseq LRO_RRO_sample. 
qed.

section.

declare module D : RO_Distinguisher{RO, FRO}.

local module M = {
  proc main1(x:input) = {
    var b;
    RRO.resample();
    b <@ D(FRO).distinguish(x);
    return b;
  }
  
  proc main2(x:input) = {
    var b;
    b <@ D(RRO).distinguish(x);
    RRO.resample();
    return b;
  }
}.

lemma RO_LRO_D :
  equiv [D(RO).distinguish ~ D(LRO).distinguish :
         ={glob D, RO.m, arg} ==> ={res, glob D}].
proof.
  transitivity M.main1 
     (={glob D, arg} /\ FRO.m{2} = map (fun _ c => (c, Known)) RO.m{1} ==>
        ={res, glob D})
     (={glob D, arg} /\ FRO.m{1} = map (fun _ c => (c, Known)) RO.m{2} ==>
        ={res, glob D})=> //.
  + by move=> /> &mr; exists (glob D){mr} (map (fun _ c =>(c, Known)) RO.m{mr}) arg{mr}.
  + proc*; inline M.main1; wp; call (RO_FRO_D D); inline *; rcondf{2} 3; auto.
    + move=> &mr [] _ ->; apply mem_eq0=> z;
        rewrite -memE mem_fdom dom_restr /in_dom_with mapE mem_map domE.
      by case (RO.m{m}.[_]).
  + by move=> /> &1; rewrite /noflags map_comp /fst /= map_id.
  transitivity M.main2
     (={glob D, FRO.m, arg} ==> ={res, glob D})
     (={glob D, arg} /\ FRO.m{1} = map (fun _ c => (c, Known)) RO.m{2} ==>
        ={res, glob D})=>//.
  + by move=> /> &mr; exists (glob D){mr} (map (fun _ c =>(c, Known)) RO.m{mr}) arg{mr}.
  + by proc; eager call (eager_D D); auto.
  proc*; inline M.main2; wp; call{1} RRO_resample_ll. 
  symmetry; call (LRO_RRO_D D); auto=> &ml &mr />.
  by rewrite -fmap_eqP=> x; rewrite restrP mapE; case (RO.m{ml}.[x]).
qed.

end section.

end GenEager.
