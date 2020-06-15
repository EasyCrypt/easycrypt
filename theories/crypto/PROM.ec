(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
require import AllCore SmtMap Distr.

(* -------------------------------------------------------------------- *)
type flag = [ Unknown | Known ].
abbrev (\is) (fv : ('a * flag) option) (f : flag) = (oget fv).`2 = f.

(* -------------------------------------------------------------------- *)
abstract theory FullRO.
type in_t, out_t.
op dout: in_t -> out_t distr.

type d_in_t, d_out_t.

(* -------------------------------------------------------------------- *)
module type RO = {
  proc init  ()                    : unit
  proc get   (x : in_t)            : out_t
  proc set   (x : in_t, y : out_t) : unit
  proc rem   (x : in_t)            : unit
  proc sample(x : in_t)            : unit
}.

module type RO_Distinguisher (G : RO) = {
  proc distinguish(_ : d_in_t): d_out_t
}.

(* -------------------------------------------------------------------- *)
module type FRO = {
  proc init    ()                    : unit
  proc get     (x : in_t)            : out_t
  proc set     (x : in_t, y : out_t) : unit
  proc rem     (x : in_t)            : unit 
  proc sample  (x : in_t)            : unit
  (****)
  proc queried (x : in_t, f : flag)  : bool
  proc allKnown()                    : (in_t, out_t) fmap
}.

module type FRO_Distinguisher (G : FRO) = {
  proc distinguish(_ : d_in_t): d_out_t
}.

(* -------------------------------------------------------------------- *)
module RO : RO = {
  var m : (in_t, out_t) fmap

  proc init () = {
    m <- empty;
  }

  proc get(x : in_t) = {
    var r;

    r <$ dout x;
    if (x \notin m) {
      m.[x] <- r;
    }
    return (oget m.[x]);
  }

  proc set(x : in_t, y : out_t) = {
    m.[x] <- y;
  }

  proc rem(x : in_t) = {
    m <- rem m x;
  }

  proc sample(x : in_t) = {
    get(x);
  }

  proc restrK() = {
    return m;
  }
}.

(* -------------------------------------------------------------------- *)
module FRO : FRO = {
  var m : (in_t, out_t * flag) fmap

  proc init() = {
    m <- empty;
  }

  proc get(x : in_t) = {
    var r;

    r <$ dout x;
    if (x \in m) {
      r <- (oget m.[x]).`1;
    }
    m.[x] <- (r, Known);
    return r;
  }

  proc set(x : in_t, y : out_t) = {
    m.[x] <- (y, Known);
  }

   proc rem(x : in_t) = {
    m <- rem m x;
  }

  proc sample(x : in_t) = {
    var c;

    c <$ dout x;
    if (x \notin m) {
      m.[x] <- (c, Unknown);
    }
  }

  proc queried(x : in_t, f : flag) = {
    return x \in m /\ m.[x] \is f;
  }

  proc allKnown() = {
    return restr Known m;
  }
}.

(* -------------------------------------------------------------------- *)
equiv RO_FRO_init : RO.init ~ FRO.init :
  true ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> /=; rewrite /noflags map_empty. qed.

equiv RO_FRO_get : RO.get ~ FRO.get :
  ={x} /\ RO.m{1} = noflags FRO.m{2}
  ==> ={res} /\ RO.m{1} = noflags FRO.m{2}.
proof.
proc; auto=> /> &2 r _.
rewrite !mem_map=> />; rewrite !domE get_set_sameE /noflags !map_set !mapE.
case: {-1}(FRO.m.[x]{2}) (eq_refl (FRO.m.[x]{2}))=> [|y m_x] />.
apply: fmap_eqP=> x'; rewrite mapE get_setE; case: (x' = x{2})=> [->>|].
+ by rewrite m_x.
by rewrite mapE.
qed.

equiv RO_FRO_set : RO.set ~ FRO.set :
  ={x, y} /\ RO.m{1} = noflags FRO.m{2}
  ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> &1 &2 [#] 3->; rewrite /noflags map_set. qed.

equiv RO_FRO_rem : RO.rem ~ FRO.rem :
  ={x} /\ RO.m{1} = noflags FRO.m{2}
  ==> RO.m{1} = noflags FRO.m{2}.
proof. by proc; auto=> /> &m'; rewrite /noflags map_rem. qed.

equiv RO_FRO_sample : RO.sample ~ FRO.sample :
  ={x} /\ RO.m{1} = noflags FRO.m{2}
  ==> RO.m{1} = noflags FRO.m{2}.
proof. 
by proc; inline *; auto=> /> &2 r _; rewrite mem_map /noflags map_set.
qed.

equiv RO_FRO_D (D <: RO_Distinguisher { RO, FRO }) :
  D(RO).distinguish ~ D(FRO).distinguish : 
    ={arg, glob D} /\ RO.m{1} = noflags FRO.m{2}
    ==> ={res, glob D} /\ RO.m{1} = noflags FRO.m{2}.
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

lemma FRO_in_dom_ll : islossless FRO.queried.
proof. by proc. qed.

lemma FRO_restrK_ll : islossless FRO.allKnown.
proof. by proc. qed.

lemma RO_set_ll : islossless RO.set.
proof. by proc; auto. qed.

lemma FRO_set_ll : islossless FRO.set.
proof. by proc; auto. qed.

section ConditionalLL.
axiom dout_ll x: is_lossless (dout x).

lemma RO_get_ll : islossless RO.get.
proof. by proc; auto=> />; rewrite dout_ll. qed.

lemma FRO_get_ll : islossless FRO.get.
proof. by proc; auto=> />; rewrite dout_ll. qed.

lemma RO_sample_ll : islossless RO.sample.
proof. by proc; call RO_get_ll. qed.

lemma FRO_sample_ll : islossless FRO.sample.
proof. by proc; auto=> />; rewrite dout_ll. qed.
end section ConditionalLL.
end section LL.

(* -------------------------------------------------------------------- *)
theory FullEager.
require import List FSet.
require (*--*) IterProc.

module LRO : RO = {
  proc init = RO.init

  proc get = RO.get

  proc set = RO.set 

  proc rem = RO.rem

  proc sample(x : in_t) = { }
}.

(* -------------------------------------------------------------------- *)
(** Hides internals in normal usage while allowing use where needed    **)
abstract theory EagerCore.
axiom dout_ll x: is_lossless (dout x).

clone include IterProc with
  type t <- in_t.

module RRO : FRO = {
  proc init = FRO.init

  proc get(x : in_t) = {
    var r;

    r <$ dout x;
    if (x \notin FRO.m \/ FRO.m.[x] \is Unknown) {
      FRO.m.[x] <- (r, Known);
    }
    return (oget FRO.m.[x]).`1;
  }

  proc set = FRO.set 

  proc rem = FRO.rem

  proc sample = FRO.sample

  proc queried = FRO.queried

  proc allKnown = FRO.allKnown

  module I = {
    proc f(x : in_t) = {
      var c;

      c <$ dout x;
      FRO.m.[x] <- (c, Unknown);
    }
  }

  proc resample () = {
    Iter(I).iter (elems (fdom (restr Unknown FRO.m)));
  }
}.

(* -------------------------------------------------------------------- *)
lemma RRO_resample_ll : islossless RRO.resample.
proof.
proc; call (iter_ll RRO.I _)=> //.
by proc; auto=> /> &m'; exact/dout_ll.
qed.

(* -------------------------------------------------------------------- *)
lemma eager_init :
  eager [RRO.resample();, FRO.init ~ RRO.init, RRO.resample(); :
         ={FRO.m} ==> ={FRO.m}].
proof.
eager proc.
inline{2} *; rcondf{2} 3; auto=> />.
+ by rewrite restr0 fdom0 elems_fset0.
by call{1} RRO_resample_ll.
qed.

equiv iter_perm2 : Iter(RRO.I).iter_12 ~ Iter(RRO.I).iter_21 :
    ={glob RRO.I, t1, t2} ==> ={glob RRO.I}.
proof.
proc; inline*; case: ((t1 = t2){1}); first by auto.
swap{2} [4..5] -3; auto=> /> &m' t1_neq_t2 c1 _ c2 _.
by rewrite set_setE (@eq_sym t2{m'}) t1_neq_t2.
qed.

equiv I_f_neq x1 mx1 : RRO.I.f ~ RRO.I.f :
  ={x, FRO.m} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = mx1
  ==> ={FRO.m} /\ FRO.m{1}.[x1] = mx1.
proof. by proc; auto=> /> &m' x1_neq_x c _; rewrite get_set_neqE. qed.

equiv I_f_eqex x1 mx1 mx2 : RRO.I.f ~ RRO.I.f :
    ={x} /\ x1 <> x{1} /\ eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\
    FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2
    ==> eq_except (pred1 x1) FRO.m{1} FRO.m{2} /\
        FRO.m{1}.[x1] = mx1 /\ FRO.m{2}.[x1] = mx2.
proof.
proc; auto=> /> &1 &2 x1_neq_x eqe c _.
by rewrite !get_setE x1_neq_x eq_except_set_eq.
qed.

equiv I_f_set x1 r1 : RRO.I.f ~ RRO.I.f :
  ={x} /\ x1 <> x{1} /\ FRO.m{1}.[x1] = None /\
  FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)]
  ==> FRO.m{1}.[x1] = None /\ FRO.m{2} = FRO.m{1}.[x1 <- (r1, Known)].
proof.
proc; auto=> /> &1 &2 x1_neq_x eqe c _.
by rewrite !get_setE x1_neq_x /= set_setE -(@eq_sym x1) x1_neq_x.
qed.

lemma eager_get :
  eager [RRO.resample();, FRO.get ~ RRO.get, RRO.resample(); :
         ={x, FRO.m} ==> ={res, FRO.m}].
proof.
eager proc.
wp; case ((x \in FRO.m /\ FRO.m.[x] \is Known){1}).
+ rnd{1}; rcondf{2} 2; first by auto=> /> &m' _ @/(\is) -> _ _ /#.
  exists* x{1}, ((oget FRO.m.[x{2}]){1}); elim * => x1 mx; inline RRO.resample.
  call (iter_inv RRO.I (fun z=> x1<>z)
                       (fun o1 o2 => o1 = o2 /\ o1.[x1]= Some mx) _)=> /=.
  + by conseq (I_f_neq x1 (Some mx))=> //.
  auto=> /> &m' x_in_m mx_Known; rewrite dout_ll //=.
  move=> r _; split=> /> => [|_ _ m mx' r' _].
  + split=> [x'|].
    + rewrite -memE mem_fdom dom_restr /in_dom_with; apply/contraLR=> /= ->>.
      by rewrite mx_Known.
    by rewrite get_some.
  rewrite domE mx' //=.
  move: mx'; rewrite -mx_Known; case: (oget FRO.m.[x]{m'})=> //= y1 y2.
  exact/get_set_id.
case ((x \in FRO.m){1}).
+ inline{1} RRO.resample=> /=; rnd{1}.
  transitivity{1} 
    { Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); }
    (={x, FRO.m} /\ x{1} \in FRO.m{1} /\ FRO.m{1}.[x{1}] \is Unknown ==>
     ={x, FRO.m})
    (={x, FRO.m} /\ x{1} \in FRO.m{1} /\ FRO.m{1}.[x{1}] \is Unknown ==>
     ={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
     FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
     FRO.m{2}.[x{2}] = Some (result{2}, Known)).
    + move=> /> &m' /negb_and [] // H1 H2; exists FRO.m{m'} x{m'}=> //=.
      by move: H1 H2; rewrite !domE=> />; case: ((oget FRO.m.[x]{m'}).`2).
    + move=> /> &m &m'; rewrite dout_ll /= !domE=> /eq_except_sym eqe mx m'x r _.
      rewrite mx /= eq_sym; have/(congr1 oget):= m'x=> /= <-.
      by apply/eq_except_set_getlr=> //; rewrite domE m'x.
    symmetry; call (iter1_perm RRO.I iter_perm2); auto=> |>.
    move=> &m'; rewrite !domE=> x_in_m mx_U.
    apply/uniq_perm_eq=> //=; 1,2:rewrite uniq_elems //=.
    + by rewrite -memE in_fsetD in_fset1.
    move=> x'; case: (x' = x{m'})=> [<<- //=|//=].
    + by rewrite -memE mem_fdom dom_restr /in_dom_with domE.
    by rewrite -!memE in_fsetD in_fset1 !mem_fdom.
  inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample.
  seq 5 3 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
             (l = elems (fdom (restr Unknown FRO.m) `\` fset1 x)){1} /\
             FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
             FRO.m{2}.[x{2}] = Some (result{2}, Known)).
  + auto=> /> &m' x_in_m mx_U c _.
    rewrite !get_setE /= eq_except_setlr //=.
    congr; congr; apply: fsetP=> x'; rewrite !mem_fdom restr_set /= mem_set.
    by rewrite dom_restr /in_dom_with; case: (x' = x{m'})=> />.
  exists* x{1}, FRO.m{1}.[x{2}], FRO.m{2}.[x{2}]; elim*=> x1 mx1 mx2.
  call (iter_inv RRO.I
         (fun z => x1 <> z)
         (fun o1 o2 =>
            eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\ o2.[x1] = mx2) 
         (I_f_eqex x1 mx1 mx2)); auto=> /> &1 &2 eq_exc get1_x2 get2_x2.
  + split. split=> [| x2].
    + congr; rewrite fsetP=> y; rewrite in_fsetD1 2!mem_fdom.
      case (y = x{2})=> [->/= | ne_y_x2 /=].
      by rewrite dom_restr /in_dom_with get2_x2.
    + rewrite !dom_restr /in_dom_with !domE.
      by move/eq_exceptP/(_ y ne_y_x2): eq_exc=> ->.
    + by rewrite -memE in_fsetD1 eq_sym.
    by rewrite get1_x2 get2_x2.
swap{1} -1; seq 1 1 : (={r, x, FRO.m} /\ ! dom FRO.m{1} x{1}); 1:by auto. 
inline RRO.resample; exists* x{1},r{1}; elim*=> x1 r1.
call (iter_inv RRO.I (fun z=> x1 <> z)
         (fun (o1 o2 : glob RRO.I) => o1.[x1] = None /\ o2 = o1.[x1 <- (r1, Known)])
         (I_f_set x1 r1)); auto.
move=> ? &mr [#] 5-> ^ Hnin ^ + -> /=; rewrite domE=> /= -> /=;
rewrite get_setE /=; split=> [| _]. split=> [| y].
+ congr; rewrite fsetP=> y.
  rewrite !mem_fdom restr_set /= mem_rem dom_restr /in_dom_with.
  by case: (y = x{mr})=> />; rewrite Hnin.
+ rewrite -memE mem_fdom dom_restr /in_dom_with.
  by case: (x{mr} = y)=> />; rewrite Hnin.
by move=> /> m_L; rewrite domE.
qed.

lemma eager_set :
  eager [RRO.resample();, FRO.set ~ RRO.set, RRO.resample(); :
         ={x, y} /\ ={FRO.m} ==> ={res, FRO.m}].
proof.
eager proc.
inline RRO.resample=> /=; wp.
case ((x \in FRO.m /\ FRO.m.[x] \is Unknown){1}).
+ transitivity{1}
    { Iter(RRO.I).iter_1s(x, elems (fdom (restr Unknown FRO.m) `\` fset1 x)); }
    (={x, y, FRO.m} /\ dom FRO.m{1} x{1} /\
     FRO.m{1}.[x{1}] \is Unknown ==>
     ={x, y, FRO.m})
    (={x, y, FRO.m} /\ dom FRO.m{1} x{1} /\
     FRO.m{1}.[x{1}] \is Unknown ==>
     ={x, y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
     FRO.m{2}.[x{2}] = Some (y{2}, Known)).
  + by move=> &ml &mr [#] 3-> x_in_m get_m_x_2_unk;
      exists FRO.m{mr} x{mr} y{mr}.
  + move=> ? &m &mr [#] <*> [#] 2-> Hex Hm2.
    by rewrite (@eq_except_set_getlr FRO.m{mr} FRO.m{m} x{mr}) ?in_dom ?Hm2 //
       1:domE 1:Hm2 // eq_except_sym.
  + symmetry; call (iter1_perm RRO.I iter_perm2); auto=> &mr ? [#] 3!-> Hdom Hm;
    split=> //=. apply/perm_eq_sym/perm_to_rem/mem_fdom.
    by rewrite dom_restr /in_dom_with.
  inline{1} Iter(RRO.I).iter_1s. 
  seq 3 1 :
    (={x, y} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
     l{1} = (elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
     (FRO.m.[x] = Some (y, Known)){2}).
  + inline *; auto=> ? &mr [#] 3-> /= Hmem Hget.
    rewrite dout_ll=> //= c _.
    rewrite (@eq_except_setlr _ _ _ (c, Unknown)) //=.
    rewrite get_set_sameE //= -memE in_fsetD1 //=.
    by congr; apply/fsetP=> y; rewrite in_fsetD1 !mem_fdom restr_set /= mem_rem.
  exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1.
  pose mx2 := Some (y1, Known).
  call (iter_inv RRO.I (fun z=> x1<>z) 
         (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                       o2.[x1] = mx2) 
         (I_f_eqex x1 mx1 mx2));
      auto=> &1 &2 /> eq_exc not_x2_in_unkn_m2 get_m2_x2_eq.
  split=> [x0 |].
  + rewrite -memE mem_fdom dom_restr /in_dom_with; apply/contraLR=> />.
    by rewrite get_m2_x2_eq.
  by rewrite get_m2_x2_eq.
exists* x{1}, y{1}, (FRO.m.[x]{1}); elim*=> x1 y1 mx1.
pose mx2 := Some (y1, Known).
call (iter_inv RRO.I (fun z=> x1<>z) 
       (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                     o2.[x1] = mx2) 
       (I_f_eqex x1 mx1 mx2))=> /=; auto=> &1 &2 /> /negb_and x2_disj.
  split=> [| _ _ _ m_L m_R eq_exc m_L_x2_eq m_R_x2_eq];1: split.
  + congr; rewrite fsetP=> z; rewrite !mem_fdom restr_set /= mem_rem dom_restr /in_dom_with.
    by case: (z = x{2})=> />; rewrite negb_and.
  split=> [x0 |].
  + rewrite -memE mem_fdom dom_restr /in_dom_with; apply/contraLR=> />.
    by rewrite negb_and.
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
eager proc; case ((x \in FRO.m /\ FRO.m.[x] \is Unknown){1}).
+ inline RRO.resample; wp.
  transitivity{1} 
    { Iter(RRO.I).iter_1s(x, elems (fdom (restr Unknown FRO.m) `\` fset1 x)); }
    (={x, FRO.m} /\ (x \in FRO.m /\ FRO.m.[x] \is Unknown){1} ==> ={x, FRO.m}) 
    (={x, FRO.m} /\ (x \in FRO.m /\ FRO.m.[x] \is Unknown){1} ==>
     (rem FRO.m x){1} = FRO.m{2})=> //.
  + by move=> /> &2 x_in_m x_is_U; exists FRO.m{2} x{2}.
  + symmetry; call (iter1_perm RRO.I iter_perm2); auto=> |> &1 x_in_m1 x_is_U1.
    apply/perm_eq_sym/perm_to_rem/mem_fdom/dom_restr.
    by rewrite /in_dom_with.
  inline{1} Iter(RRO.I).iter_1s.
  seq 3 1: (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
            l{1} = (elems (fdom (restr Unknown FRO.m))){2} /\ !mem l{1} x{1} /\
            (FRO.m.[x] = None){2}).
  + inline *; auto=> |> &2 x_in_m2 x_is_U2; rewrite dout_ll=> //= c _.
    rewrite (@eq_except_remr (pred1 x{2}) _ FRO.m{2} x{2}) /pred1 //=.
    + exact/eq_except_setl.
    rewrite remE -memE in_fsetD1 negb_and /=.
    rewrite -fdom_rem; congr; congr; apply/fmap_eqP=> z.
    by rewrite restr_rem /in_dom_with x_in_m2 x_is_U2.
  exists* x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1.
  call (iter_inv RRO.I (fun z=> x1<>z) 
       (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                     o2.[x1] = None) _).
  + by conseq (I_f_eqex x1 mx1 None).
  auto=> /> &1 &2 m1_eqe_m2 _ x_notin_m2; split=> [z|/> _ mL mR mL_eqe_mR mL_x mR_x].
  + rewrite -memE mem_fdom dom_restr /in_dom_with; apply/contraLR=> />.
    by rewrite domE x_notin_m2.
  apply/fmap_eqP=> z; rewrite remE. case: (z = x{2})=> /> => [|z_neq_x].
  + by rewrite mR_x.
  by move/eq_exceptP/(_ _ z_neq_x): mL_eqe_mR.
inline RRO.resample; wp.
exists *x{1}, (FRO.m.[x]{1}); elim*=> x1 mx1.
call (iter_inv RRO.I (fun z=> x1<>z) 
       (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1] = mx1 /\
                     o2.[x1]=None) _).
+ by conseq (I_f_eqex x1 mx1 None).
auto=> ? &mr [#] 4-> /= Hin.
rewrite (@eq_except_remr (pred1 x{mr}) _ FRO.m{mr} x{mr}) // remE /=.
split=> [|/> _ _ mL mR /eq_exceptP eqe mLx mRx]. split=> [|z].
+ congr; congr; apply/fmap_eqP=> z.
  rewrite !restrP remE; case: (z = x{mr})=> />.
  by move: Hin; rewrite domE; case: (FRO.m.[x]{mr})=> //= + ->.
+ by rewrite -memE mem_fdom dom_restr /in_dom_with; apply/contraLR.
apply/fmap_eqP=> z; rewrite remE; case: (z = x{mr})=> />.
+ by rewrite mRx.
by move=> /eqe.
qed.

lemma eager_sample :
  eager [RRO.resample();, FRO.sample ~ RRO.sample, RRO.resample(); :
         ={x, FRO.m} ==> ={res, FRO.m}].
proof.
eager proc.
case: ((x \notin FRO.m){2}).
+ rcondt{2} 2; first by auto.
  transitivity{2}
    { c <$ dout x; FRO.m.[x] <- (c, Unknown);
      Iter(RRO.I).iter_1s(x, elems ((fdom (restr Unknown FRO.m)) `\` fset1 x)); }
    (={x, FRO.m} /\ ! dom FRO.m{2} x{2} ==> ={x, FRO.m}) 
    (={x, FRO.m} /\ ! dom FRO.m{2} x{2} ==> ={x, FRO.m})=>//; last first.
  + inline{2} RRO.resample; call (iter1_perm RRO.I iter_perm2).
    auto=> |> &2 x_notin_m c _.
     by apply/perm_eq_sym/perm_to_rem; rewrite restr_set /= mem_fdom mem_set.
  + by move=> /> &2 x_notin_m; exists FRO.m{2} x{2}.
  inline Iter(RRO.I).iter_1s RRO.I.f RRO.resample; wp; swap{1} -1.
  seq 1 7 : (={x} /\ eq_except (pred1 x{1}) FRO.m{1} FRO.m{2} /\
             l{2} = (elems (fdom (restr Unknown FRO.m))){1} /\
             (FRO.m.[x]){2} = Some (c{1}, Unknown) /\ (FRO.m.[x]){1} = None).
  + wp; rnd; auto=> /> &2; rewrite domE dout_ll=> /= x_notin_m c _ cL _.
    rewrite get_set_sameE restr_set /=.
    have <-: (predU (pred1 x) (pred1 x)){2} = pred1 x{2}.
    + by apply/pred_ext=> z @/predU @/pred1; split=> [[|]|].
    rewrite eq_exceptmS 1:eq_except_setr //=.
    congr; apply/fsetP=> z; rewrite in_fsetD1 !mem_fdom mem_set.
    by case: (z = x{2})=> />; rewrite dom_restr /in_dom_with domE x_notin_m.
  exists* x{1}, c{1}; elim*=> x1 c1; pose mx2 := Some (c1, Unknown).
  call (iter_inv RRO.I (fun z=> x1<>z) 
       (fun o1 o2 => eq_except (pred1 x1) o1 o2 /\ o1.[x1]= None /\
                     o2.[x1]=mx2) _).
  + by conseq (I_f_eqex x1 None mx2).
  auto=> &1 &2 /> m1_eqe_m2 m2_x m1_x; split=> [z|_ mL mR /eq_exceptP mL_eqe_mR mL_x mR_x].
  + rewrite -memE mem_fdom dom_restr /in_dom_with domE; apply/contraLR=> />.
    by rewrite m1_x.
  rewrite domE mL_x /=; apply/fmap_eqP=> z; rewrite get_setE; case: (z = x{2})=> />.
  + by rewrite mR_x m2_x.
  by move=> /mL_eqe_mR.
rcondf{2} 2; first by auto. 
swap{1} 2 -1; inline *; auto.
while (={l, FRO.m} /\ (dom FRO.m x){1}); auto.
move=> /> &1 &2 x_in_m l_nil c _; rewrite -mem_fdom fdom_set in_fsetU.
by rewrite mem_fdom x_in_m.
qed.

lemma eager_queried :
  eager [RRO.resample();, FRO.queried ~ RRO.queried, RRO.resample(); :
         ={x, f} /\ ={FRO.m} ==> ={res, FRO.m}].
proof.
eager proc; inline *; wp.
while (   ={l, FRO.m}
       /\ (forall z, z \in l => in_dom_with FRO.m z Unknown){1}
       /\ in_dom_with FRO.m{1} x{1} f{1} = result{2}).
+ auto=> /> &1 &2 inv l2_neq_nil c _; split=> [z /mem_drop z_in_l|].
  + rewrite mem_set get_setE; case: (z = head witness l{2})=> //= _.
    by move: (inv _ z_in_l)=> @/in_dom_with.
  rewrite /in_dom_with mem_set get_setE; case: (x{1} = head witness l{2})=> />.
  move: (inv (head witness l{2}) _).
  + by apply/(@mem_head_behead witness _ l2_neq_nil).
  rewrite /in_dom_with=> />; rewrite domE.
  by case: (FRO.m.[head witness l]{2})=> /> [].
by auto=> /> &2 z; rewrite -memE mem_fdom dom_restr /in_dom_with.
qed.

lemma eager_allKnown :
  eager [RRO.resample();, FRO.allKnown ~ RRO.allKnown, RRO.resample(); :
         ={FRO.m} ==> ={res, FRO.m}].
proof.
eager proc; inline *; wp.
while (   ={l, FRO.m}
       /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1}
       /\ restr Known FRO.m{1} = result{2}).
+ auto=> /> &2 inv l2_neq_nil c _; split=>[z /mem_drop z_in_l|].
  + rewrite /in_dom_with mem_set get_setE; case: (z = head witness l{2})=> />.
    by move: (inv _ z_in_l)=> @/in_dom_with.
  rewrite restr_set rem_id ?dom_restr //.
  move: (inv (head witness l{2}) _).
  + by apply/(@mem_head_behead witness _ l2_neq_nil).
  by rewrite /in_dom_with=> />; rewrite domE=> _ ->.
by auto=> ? &mr /= -> /=; split=> // z; rewrite -memE mem_fdom dom_restr. 
qed.

(* -------------------------------------------------------------------- *)
section.
declare module D : FRO_Distinguisher {FRO}.

lemma eager_D :
  eager [RRO.resample();, D(FRO).distinguish ~ 
         D(RRO).distinguish, RRO.resample(); :
         ={glob D, FRO.m, arg} ==> ={FRO.m, glob D} /\ ={res}].
proof.
eager proc (H_: RRO.resample(); ~ RRO.resample();: ={FRO.m} ==> ={FRO.m})
           (={FRO.m}) =>//; try by sim.
+ by apply eager_init.
+ by apply eager_get.
+ by apply eager_set.
+ by apply eager_rem.
+ by apply eager_sample.
+ by apply eager_queried.
by apply eager_allKnown.
qed.
end section.

(* -------------------------------------------------------------------- *)
module Eager (D : FRO_Distinguisher) = {
  proc main1(x : d_in_t) = {
    var b;

    FRO.init();
    b <@ D(FRO).distinguish(x);
    return b;
  }

  proc main2(x : d_in_t) = {
    var b;

    FRO.init();
    b <@ D(RRO).distinguish(x);
    RRO.resample();
    return b;
  }
}.

(* -------------------------------------------------------------------- *)
section.
declare module D : FRO_Distinguisher {FRO}.

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
by eager call (eager_D D).
qed.
end section.

(* -------------------------------------------------------------------- *)
equiv LRO_RRO_init : LRO.init ~ RRO.init : true ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc; auto=> /=; rewrite restr0. qed.

equiv LRO_RRO_get : LRO.get ~ RRO.get :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==>
   ={res} /\ RO.m{1} = restr Known FRO.m{2}.
proof. 
proc; auto=> /> &2 r _.
rewrite dom_restr /in_dom_with negb_and !restr_set !restrP !get_set_sameE //= !domE.
by case: (FRO.m.[x]{2})=> /> [] /> r' [].
qed.

equiv LRO_RRO_set : LRO.set ~ RRO.set :
   ={x, y} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc; auto=> /> &2; rewrite restr_set. qed.

equiv LRO_RRO_rem : LRO.rem ~ RRO.rem :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof.
proc; inline *; auto=> /> &2; rewrite restr_rem.
case: ((in_dom_with FRO.m x Known){2})=>// Hidw.
by rewrite rem_id // dom_restr.
qed.

equiv LRO_RRO_sample : LRO.sample ~ RRO.sample :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof.
proc; auto=> /> &2; rewrite dout_ll=> //= c _.
rewrite restr_set=> //= Hnd. 
by rewrite rem_id // dom_restr /in_dom_with Hnd.
qed.

equiv LRO_RRO_D (D <: RO_Distinguisher{RO, FRO}) :
  D(LRO).distinguish ~ D(RRO).distinguish : 
    ={glob D, arg} /\ RO.m{1} = restr Known FRO.m{2}
    ==> ={res, glob D} /\ RO.m{1} = restr Known FRO.m{2}.
proof.
proc (RO.m{1} = restr Known FRO.m{2})=> //.
+ by conseq LRO_RRO_init.
+ by conseq LRO_RRO_get.
+ by conseq LRO_RRO_set.
+ by conseq LRO_RRO_rem.
by conseq LRO_RRO_sample. 
qed.
end EagerCore.

(* -------------------------------------------------------------------- *)
section.
declare module D : RO_Distinguisher { RO, FRO }.
axiom dout_ll x: is_lossless (dout x).

local clone import EagerCore as InnerProof
proof dout_ll by exact/dout_ll.

local module M = {
  proc main1(x : d_in_t) = {
    var b;

    RRO.resample();
    b <@ D(FRO).distinguish(x);
    return b;
  }

  proc main2(x : d_in_t) = {
    var b;

    b <@ D(RRO).distinguish(x);
    RRO.resample();
    return b;
  }
}.

equiv RO_LRO_D : D(RO).distinguish ~ D(LRO).distinguish :
  ={glob D, RO.m, arg} ==> ={res, glob D}.
proof.
transitivity M.main1 
   (={glob D, arg} /\ FRO.m{2} = map (fun _ c => (c, Known)) RO.m{1}
    ==> ={res, glob D})
   (={glob D, arg} /\ FRO.m{1} = map (fun _ c => (c, Known)) RO.m{2}
    ==> ={res, glob D})=> //.
+ move=> /> &2.
  by exists (glob D){2} (map (fun _ c => (c, Known)) RO.m{2}) arg{2}.
+ proc *; inline M.main1; wp; call (RO_FRO_D D); inline *.
  rcondf{2} 3.
  + auto=> />; apply/mem_eq0=> z; rewrite -memE mem_fdom dom_restr.
    by rewrite /in_dom_with domE mapE //=; case: (RO.m.[z]{m}).
+ by auto=> /> &1; rewrite /noflags map_comp /fst /= map_id.
transitivity M.main2
   (={glob D, FRO.m, arg} ==> ={res, glob D})
   (={glob D, arg} /\ FRO.m{1} = map (fun _ c => (c, Known)) RO.m{2} ==>
      ={res, glob D})=>//.
+ move=> /> &2.
  by exists (glob D){2} (map (fun _ c => (c, Known)) RO.m{2}) arg{2}.
+ by proc; eager call (eager_D D); auto.
proc*; inline M.main2; wp; call{1} RRO_resample_ll.
symmetry; call (LRO_RRO_D D); auto=> /> &1.
by apply/fmap_eqP=> x; rewrite restrP mapE; case: (RO.m.[x]{1}).
qed.

end section.
end FullEager.

end FullRO.
