(* NR-PRF *)
require import Int Real List SmtMap Distr DList FSet.
require (*--*) GroupAction PRF.

(* We need a regular, effective, abelian group action for this construction *) 
clone import GroupAction.ARegEGA as Ega.

(* Setup keyspace, domain, and range *)
type K = group * group.
type D = bool. (* Only one bit for the moment but will be an l-bit word *) 
type R = set.

(* This is the Naor-style PRF construction *)
op F (k : K) (m : D) =
    if   m
    then act (k.`1 * k.`2) x0
    else act k.`1 x0.

(* Setup the uniform distribution on our range *)
clone import MFinite as Uni_dR with
    type t <- R
rename
    "dunifin" as "dR".

(* Setting up the PRF *)
clone import PRF as PRF_t with
    type D <- D,
    type R <- R.

clone import RF as NS_RF with
    op dR _ <- dR
proof *.
realize dR_ll.
by move=> _; exact dR_ll.
qed.

clone import PseudoRF as NS_PRF with
    type K <- K,
    op dK <- sample `*` sample,
    op F <- F
proof *.
realize dK_ll.
apply dprod_ll.
split; exact DG.dunifin_ll.
qed.

(* ------------------------------------------------------ *)
(* Setup our bounding module *)

module type Bounded_PRF = {
    proc init(_ : int) : unit
    proc f(_ : D) : R
}.

module Bounded_PRF_IND (F : Bounded_PRF) (A : Distinguisher) = {
    proc main (Q : int) : bool = {
        var b : bool;
        F.init(Q);
        b <@ A(F).distinguish();
        return b;
    }
}.

module BoundPRF(O : PRF_t.PRF) : Bounded_PRF = {
    var c, q : int
    
    proc init(Q : int) : unit = {
        O.init();
        q <- Q;
        c <- 1;
    }

    proc f(x : D) : R = {
        var val : R;
        val <- witness;
        if (c <= q) {
            val <@ O.f(x);
            c <- c + 1;
        }
        return val;
    }
}.

op compute_action (gs : group list) (ss : bool list) (x : set) : set =
    with gs = "[]"     ,      ss = "[]" => x
    with gs = "[]"     , ss = (::) s ss => x
    with gs = (::) g gs,      ss = "[]" => x
    with gs = (::) g gs, ss = (::) s ss =>
      if s then compute_action gs ss (act g x)
           else compute_action gs ss x.

(* ------------------------------------------------------------ *)
(* Lemma 4.21 *)
(* Start by just considering the case when l = 1, here we will just have two games for an adversary to distinguish *)

module Hybrid_PRF_0 = {
    var g0, g1 : group

    proc init() = {
        g0 <$ sample;
        g1 <$ sample;
    }

    proc f(s) = {
        var val;
        val <- act g0 x0;
        if (s) {
            val <- act g1 val;
        }
        return val;
    }
}.

(* The lazy variant *)
module Hybrid_PRF_0' = {
    var m : (int, group) fmap
    var g1 : group

    proc init() = {
        g1 <$ sample;
        m <- empty;
    }

    proc get(i : int) : group = {
        var g;
        if (i \notin m) {
            g <$ sample;
            m.[i] <- g;    
        }
        return oget m.[i];
    }

    proc f(s) = {
        var val, g;
        g <@ get(0);
        val <- act g x0;
        if (s) {
            val <- act g1 val;
        }
        return val;
    }
}.

module Hybrid_PRF_L = {
    var m : (D, R) fmap

    proc init() = {
        m <- empty;
    }

    proc f(s) = {
        var gq;
        if (s \notin m) {
            gq <$ sample;
            m.[s] <- act gq x0;
        }
        return oget m.[s];
    }
}.

(* The eager variant *)
module Hybrid_PRF_L' = {
    var m : (D, R) fmap

    proc init() = {
        var g;
        g <$ sample;
        m.[true] <- act g x0;
        g <$ sample;
        m.[false] <- act g x0;
    }

    proc f(s) = {
        return oget m.[s];
    }
}.

equiv PRF_Eager_Lazy_eq:
  Hybrid_PRF_L.f ~ Hybrid_PRF_L'.f:
  Hybrid_PRF_L.m{1} = empty /\ true ==> ={res}.
proof.
admit.
qed.

(** |Pr[IND(PRF, D).main() @ &m: res] - Pr[IND(RF, D).main() @ &m: res]|
    <= Advantage of A(D) against something we think is hard **)

lemma sample_dR_iso g x: mu1 sample g = mu1 dR (act g x).
proof.
have /= <- := dmap1E_can dR (extract x) (fun g=> act g x) g _ _.
+ by rewrite /cancel=> g'; rewrite -extractUniq.
+ by move=> a _ /=; rewrite extractP.
congr; apply: eq_funi_ll.
+ exact: DG.dunifin_funi.
+ exact: DG.dunifin_ll.
+ apply/dmap_funi.
  + exists (fun g=> act g x); split.
    + by move=> a; exact: extractP.
    by move=> h; rewrite -extractUniq.
  exact: dR_funi.
exact/dmap_ll/Uni_dR.dR_ll.
qed.

equiv prf_bound_eq (D <: Distinguisher) (O <: PRF) :
  D(O).distinguish ~ D(BoundPRF(O)).distinguish:
      ={glob D, glob O} /\ BoundPRF.c{1} = 1 /\ BoundPRF.c{2} = 1
  ==> ={res}.
proof.
admit.
qed.

require (*--*) DProd.
clone DProd.ProdSampling with
  type t1 <- group,
  type t2 <- group.

lemma Hybrid_PRF_0_PRF_eq (D <: Distinguisher {Hybrid_PRF_0, BoundPRF, PRF}) (x : int) &m:
  Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(x) @ &m: res] = Pr[Bounded_PRF_IND(BoundPRF(Hybrid_PRF_0), D).main(x) @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
sp.
seq 1 2: (   ={glob D, Q, Q0}
          /\ NS_PRF.PRF.k{1} = (Hybrid_PRF_0.g0,Hybrid_PRF_0.g1){2}).
+ conseq />.
  transitivity {1} (** Which memory should the piece of code operate in? **)
               {PRF.k <@ ProdSampling.S.sample(sample, sample); } (** Which piece of code? **)
               (true ==> ={PRF.k}) (** Left-to-step similarity **)
               (true ==> PRF.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2}) (** Step-to-right similarity **)=> //.
  + by inline {2} 1; auto.
  transitivity {2}
               { (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1) <@ ProdSampling.S.sample2(sample, sample); }
               (true ==> PRF.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2})
               (true ==> ={Hybrid_PRF_0.g0, Hybrid_PRF_0.g1})=> //.
  + by call ProdSampling.sample_sample2; auto=> /> [].
  by inline {1} 1; auto.
wp.
sp.
call (:  PRF.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2}
      /\ ={BoundPRF.c, BoundPRF.q}).
+ proc; inline*; wp; skip=> />.
  move=> &2 _ _ @/F /=.
  rewrite comp.
  exact: actC.
skip=> />.
qed.

lemma Hybrid_PRF_L_RF_eq (D <: Distinguisher {Hybrid_PRF_L, RF, BoundPRF}) (a : int) &m:
    Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(a) @ &m: res] = Pr[Bounded_PRF_IND(BoundPRF(Hybrid_PRF_L), D).main(a) @ &m: res].
proof.
byequiv (_ : ={glob D, arg} ==> ={res})=> //.
proc.
inline *.
wp.
call (: ={m}(RF, Hybrid_PRF_L) /\ ={BoundPRF.c, BoundPRF.q}).
+ proc; inline*.
  sp.
  if; first by move=> />.
  + sp.
    if.
    + by move=> />.
    + wp.
      rnd (fun x => extract x0 x) (fun g => act g x0).
      skip=> &1 &2 /> _ _.
      split=> [g _ | _]; first exact extractUniq.
      split=> [g _ | _ r _]; first exact sample_dR_iso.
      by rewrite extractP.
    auto=> &1 &2 />.
  by auto.
by auto.
qed.

lemma PRF_Hybrid_PRF_Reduction (D <: Distinguisher {BoundPRF, Hybrid_PRF_0, Hybrid_PRF_L, PRF, RF}) (x : int) &m :
  `|Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(x) @ &m: res] - Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(x) @ &m: res]|
= `|Pr[Bounded_PRF_IND(BoundPRF(Hybrid_PRF_0), D).main(x) @ &m: res] - Pr[Bounded_PRF_IND(BoundPRF(Hybrid_PRF_L), D).main(x) @ &m: res]|.
by rewrite (Hybrid_PRF_0_PRF_eq D) (Hybrid_PRF_L_RF_eq D).
qed.

(* ----------------------------------------------- *)
(* Weak pseudorandomness assumption *)
module type WP = {
    proc init() : unit
    proc query() : R * R
}.

module type Bounded_WP = {
    proc init(_ : int) : unit
    proc query() : R * R
}.

module type WP_Oracles = {
    proc query() : R * R
}.

module type WP_Adv (F : WP_Oracles) = {
  proc distinguish () : bool
}.

module WP_IND (F : WP) (A : WP_Adv) = {
  proc main() : bool = {
    var b : bool;
    F.init();
    b <@ A(F).distinguish();
    return b;
  }
}.

module BoundWP(O : WP) : Bounded_WP = {
    var q, c : int
    proc init(Q : int) = {
        O.init();
        q <- Q;
        c <- 1;
    }

    proc query() = {
        var r : set * set;
        r <- witness;
        if (c <= q) {
            r <@ O.query();
        }
        return r;
    }
}.

module WP_Real = {
    var g : group
  
    proc init() = { g <$ sample; }

    proc query() = {
        var xq, yq : set;
        xq <$ dR;
        yq <- act g xq;
        return (xq, yq);
    }
}.

module WP_Ideal = {
    proc init() = { }

    proc query() = {
        var xq, yq : set;
        xq <$ dR;
        yq <$ dR;
        return (xq, yq);
    }
}.

module Hybrid_WP_Real = {
    var gt : group

    proc init() = { gt <$ sample; }

    proc query() = {
        var gq, xq, yq;
        gq <$ sample;
        xq <- act gq x0;
        yq <- act gt xq;
        return (xq, yq);
    }
}.

module Hybrid_WP_Ideal = {
    proc init() = { }

    proc query() = {
        var gq, hq, xq, yq;
        gq <$ sample;
        xq <- act gq x0;
        hq <$ sample;
        yq <- act hq xq;
        return (xq, yq);
    }
}.

lemma Hybrid_WP_WP_Real_eq (A <: WP_Adv{Hybrid_WP_Real, WP_Real}) &m:
   Pr[WP_IND(WP_Real, A).main() @ &m: res] = Pr[WP_IND(Hybrid_WP_Real, A).main() @ &m: res].
proof.
byequiv (: ={glob A, arg} ==> ={res})=> //.
proc; inline *.
call (: WP_Real.g{1} = Hybrid_WP_Real.gt{2}).
+ proc; wp.
  rnd (extract x0) (transpose act x0); auto=> /> &2.
  split=> [g _ | _]; first exact: extractUniq.
  split=> [g _ | _ xq _]; first exact: sample_dR_iso.
  by rewrite extractP.
by auto=> />.
qed.

lemma Hybrid_WP_WP_Ideal_eq (A <: WP_Adv{Hybrid_WP_Ideal, WP_Ideal}) &m:
   Pr[WP_IND(WP_Ideal, A).main() @ &m: res] = Pr[WP_IND(Hybrid_WP_Ideal, A).main() @ &m: res].
proof.
byequiv (: ={glob A, arg} ==> ={res})=> //.
proc.
inline *.
call (: true).
+ proc.
  seq 1 2 : (={xq}).
  + wp.
    rnd (fun x => extract x0 x) (fun g => act g x0).
    skip=> &1 &2 />.
    split=> [g _ | _]; first exact extractUniq.
    split=> [g _ | _ r _]; first exact sample_dR_iso.
    by rewrite extractP.
  wp.
  rnd (fun x => extract xq{1} x) (fun g => act g xq{2}).
  skip=> &1 &2 />.
  split=> [g _ | _]; first exact extractUniq.
  split=> [g _ | _ r _]; first exact sample_dR_iso.
  by rewrite extractP.
by auto=> />.
qed.

lemma Hybrid_WP_WP_Reduction (A <: WP_Adv{Hybrid_WP_Ideal, Hybrid_WP_Real, WP_Real, WP_Ideal}) &m :
`|Pr[WP_IND(Hybrid_WP_Real, A).main() @ &m: res] - Pr[WP_IND(Hybrid_WP_Ideal, A).main() @ &m: res] |
= `| Pr[WP_IND(WP_Real, A).main() @ &m: res] - Pr[WP_IND(WP_Ideal, A).main() @ &m: res] |.
by rewrite (Hybrid_WP_WP_Real_eq A) (Hybrid_WP_WP_Ideal_eq A).
qed.

(* Reduction the middle *)
module Hj (D : Distinguisher) = {
  var j   : int

  var g0  : group
  var gis : group

  var yqs : (bool list, set) fmap

  var c   : int
  var q   : int

  module O = {
    proc f(x) = {
      var xs <- [x];
      var  p <- take j xs;
      var  s <- drop j xs;
      var gq;
      var yq;
      var r <- witness;

      if (c <= q) {
        if (j = 0) {
          yq <- act g0 x0;
        } else {
          if (p \notin yqs) {
            gq <$ sample;
            yqs.[p] <- act gq x0;
          }
          yq <- oget (yqs.[p]);
        }
        c <- c + 1;
        r <- compute_action [gis] s yq;
      }
      return r;
    }
  }

  proc run(i : int, Q : int) : bool = {
    var b;

      j <- i;

      c <- 1;
      q <- Q;
     g0 <$ sample;
    gis <$ sample;
    yqs <- empty;

      b <@ D(O).distinguish();
    return b;
  }
}.

equiv PRF_Hybrid0 (D <: Distinguisher { BoundPRF, PRF, Hj }):
  Bounded_PRF_IND(BoundPRF(PRF), D).main ~ Hj(D).run:
    ={glob D, Q} /\ 0 <= Q{1} /\ i{2} = 0
    ==> ={res}.
proof.
proc=> /=.
call (:    Hj.j{2} = 0
        /\ ={q, c}(BoundPRF, Hj)
        /\ PRF.k{1} = (Hj.g0, Hj.gis){2}).
+ proc; sp; if; 1,3:auto.
  inline *; auto=> />.
  rcondt {2} 1; 1:by auto.
  by auto=> /> &2 _ @/F /=; rewrite actC comp.
inline *; sp; wp; conseq />.
transitivity {1} (** Which memory should the piece of code operate in? **)
              {PRF.k <@ ProdSampling.S.sample(sample, sample); } (** Which piece of code? **)
              (true ==> ={PRF.k}) (** Left-to-step similarity **)
              (true ==> PRF.k{1} = (Hj.g0, Hj.gis){2}) (** Step-to-right similarity **)=> //.
+ by inline {2} 1; auto.
transitivity {2}
              { (Hj.g0, Hj.gis) <@ ProdSampling.S.sample2(sample, sample); }
              (true ==> PRF.k{1} = (Hj.g0, Hj.gis){2})
              (true ==> ={Hj.g0, Hj.gis})=> //.
+ by call ProdSampling.sample_sample2; auto=> /> [].
by inline {1} 1; auto.
qed.

lemma PRF_Hybrid0_pr (D <: Distinguisher { BoundPRF, PRF, Hj }) q &m:
     0 <= q
  =>   Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(q) @ &m: res]
     = Pr[Hj(D).run(0, q) @ &m: res].
proof. by move=> ge0_q; byequiv (PRF_Hybrid0 D). qed.

equiv PRF_HybridL (D <: Distinguisher { BoundPRF, RF, Hj }):
  Bounded_PRF_IND(BoundPRF(RF), D).main ~ Hj(D).run:
    ={glob D, Q} /\ 0 <= Q{1} /\ i{2} = 1
    ==> ={res}.
proof.
proc=> /=; inline *.
call (:    Hj.j{2} = 1
        /\ ={q, c}(BoundPRF, Hj)
        /\ (forall (x : D), RF.m.[x]{1} = Hj.yqs.[[x]]{2})).
+ proc; sp; if; auto.
  rcondf {2} 1; 1:by auto.
  inline *.
  sp; if=> /=.
  + by rewrite !domE=> /> &1 &2 ->.
  + wp.
    rnd (fun x => extract x0 x) (fun g => act g x0).
    skip=> /> &1 &2 eqv _ nin.
    split=> [g _ | _]; first exact extractUniq.
    split=> [g _ | _ r _]; first exact sample_dR_iso.
    rewrite extractP !get_set_sameE /=.
    by move=> x'; rewrite !get_setE (eqv x').
  by auto=> &1 &2 /> eqv _ xin; rewrite eqv.
by auto=> /> &2 _ g _ gs _ x; rewrite !emptyE.
qed.

lemma PRF_HybridL_pr (D <: Distinguisher { BoundPRF, RF, Hj }) q &m:
     0 <= q
  =>   Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(q) @ &m: res]
     = Pr[Hj(D).run(1, q) @ &m: res].
proof. by move=> ge0_q; byequiv (PRF_HybridL D). qed.

module (B (D : Distinguisher) : WP_Adv) (F : WP_Oracles) = {
  var j   : int

  var gis : group

  var c   : int
  var q   : int

  var _qs : (bool list, set * set) fmap

  module O = {
    proc f(x) = {
      var xq, yq;
      var xs <- [x];
      var  p <- take j xs;
      var  b <- nth witness xs j;
      var  s <- drop (j + 1) xs;
      var  r <- witness;

      if (c <= q) {
        if (p \notin _qs) {
          (xq, yq) <@ F.query();
           _qs.[p] <- (xq, yq);
        }
        (xq, yq) <- oget _qs.[p];
               r <- compute_action [gis] s (if b then yq else xq);
               c <- c + 1;
      }
      return r;
    }
  }

  proc distinguish() = {
    var b;

      j <- 0;
      c <- 1;
    _qs <- empty;
    gis <$ sample;
      b <@ D(O).distinguish();
    return b;
  }
}.

equiv Toto (D <: Distinguisher { Hj, B, WP_Ideal }):
  Hj(D).run ~ B(D, WP_Ideal).distinguish:
    ={glob D} /\ i{1} = 1 /\ Q{1} = B.q{2} /\ 0 <= Q{1}
    ==> ={res}.
proof.
proc; sp=> //=.
call (:    B.j{2} = 0 /\ Hj.j{1} = 1
        /\ ={c, q, gis}(Hj, B)
        /\ (forall p, p \in Hj.yqs{1} => size p = Hj.j{1})
        /\ (forall p, p \in Hj.yqs{1} => take (size p - 1) p \in B._qs{2})
        /\ (forall p, p \in B._qs{1} => size p = B.j{1})
        /\ (forall p, p \in B._qs{2} => exists b, rcons p b \in Hj.yqs{1})
        /\ (forall p' b y',    Hj.yqs.[rcons p' b]{1} = Some y'
                           => exists x, B._qs.[p']{2} = Some (x, act B.gis{2} x)
                                     /\ y' = if b then act B.gis{2} x else x)
        /\ (forall p x y,    B._qs.[p]{2} = Some (x, y)
                          => forall b y', Hj.yqs.[rcons p b]{1} = Some y' => y' = if b then y else x)
        (** yqs[p' ++ [b]] = yq; _qs[p'] = (xq, gt * xq) **)).
+ proc; sp; if; 1,3:by auto.
  rcondf {1} 1; 1:by auto.
  inline WP_Ideal.query.
  if {1}.
  + if {2}.
    + wp=> />.
      conseq (: act gq{1} x0 = if x{2} then yq0{2} else xq0{2})=> //=.
      + move=> />. admit.
      case: (x{2}).
      + wp; rnd (fun g => act g x0) (fun x => extract x0 x); rnd {2}.
        admit.
      wp; rnd {2}; rnd (fun g=> act g x0) (fun x => extract x0 x).
      admit.
    admit.
  rcondf {2} 1.
  + by auto=> /> &0 _ /(_ [x{m}]).
  wp=> //=.
  auto=> /> &1 &2 domL_size domLR domR_size domRL valLR valRL c_le_q ^x_in_yqs; rewrite domE.
  case: {-1}(Hj.yqs{1}.[[x{2}]]) (eq_refl Hj.yqs{1}.[[x{2}]])=> //= y yqs_x.
  by move: (valLR [] x{2} y yqs_x)=> //= [] xq /> ->.
admit.
qed.  

module (C (D : Distinguisher) : WP_Adv) (F : WP_Oracles) = {
    module O = {
        var gs : (int, group) fmap
        var qs : (D list, R * R) fmap
        var j : int

        proc init() = {
            qs <- empty;
            j <- 0;

        (* More General
            i <- j + 2;
            gs <- empty;
            while (i <= 1) {
                g <$ sample;
                gs.[i] <- g;
                i <- i + 1;
            }
        *)
        }

        proc f(s) = {
            var x, y, val : R;
            var wrd, prefix, suffix : bool list;
            var switch : bool;
            wrd <- [s];
            prefix <- take j wrd;
            switch <- nth witness wrd j;
            suffix <- drop (j+1) wrd;

            (* Witness is replaced by the empty list in this case *)
            if (prefix \notin qs) {
                (x, y) <@ F.query();
                qs.[prefix] <- (x, y);
            } else {
                (x, y) <- oget qs.[prefix];
            }
            if (switch) {
                val <- y;
            } else {
                val <- x;
            }
            (* Handle the suffix stuff f~, j+2 onwards use compute_action gs suffix x0 *)
            return val;
        }
    }    

    proc distinguish() = {
        var b : bool;
        O.init();
        b <@ D(O).distinguish();
        return b;
    }
}.

lemma Hybrid_PRF_WP_Real_eq (D <: Distinguisher{Hybrid_PRF_0', Hybrid_WP_Real, C}) &m :
    Pr[IND(Hybrid_PRF_0', D).main() @ &m: res] = Pr[WP_IND(Hybrid_WP_Real, C(D)).main() @ &m: res].
proof.
admit.
(*
byequiv (: ={glob D, arg} ==> ={res})=> //.
proc.
inline *.
wp.
call (:   Hybrid_PRF_0'.g1{1} = Hybrid_WP_Real.gt{2}
  (* This will need generalised for i \in [0..j]*)
       /\ (0 \notin Hybrid_PRF_0'.m{1} <=> [] \notin C.O.qs{2})
       /\ (0 \in Hybrid_PRF_0'.m{1} => act (oget Hybrid_PRF_0'.m.[0]{1}) x0 = (oget C.O.qs.[[]]).`1{2})
       /\ (0 \in Hybrid_PRF_0'.m{1} => act Hybrid_PRF_0'.g1{1} (act (oget Hybrid_PRF_0'.m.[0]{1}) x0) = (oget C.O.qs.[[]]).`2{2})).
+ proc.
  inline *.
  sp.
  if=> //.
  + auto=> &1 &2 /> _ _ _ g h.
    rewrite !mem_set.
    auto=> _ />.
    by rewrite !get_set_sameE !Core.oget_some.
  auto=> &1 &2 /> _.
  move=> h1 h2 ?.
  split=> _.
  + exact h2.
  exact h1.
auto=> &1 &2 /> g _.
rewrite !emptyE !Core.oget_none.
do split; by apply contraLR; move=> _; rewrite mem_empty.
*)
qed.

lemma Hybrid_PRF_WP_Ideal_eq (D <: Distinguisher{Hybrid_PRF_L', Hybrid_WP_Ideal, C}) &m :
  Pr[IND(Hybrid_PRF_L', D).main() @ &m: res] = Pr[WP_IND(Hybrid_WP_Ideal, C(D)).main() @ &m: res].
proof.
byequiv (: ={glob D, arg} ==> ={res})=> //.
proc.
inline*.
wp.
call (:   ([] \in C.O.qs{2} => oget Hybrid_PRF_L'.m.[false]{1} = (oget C.O.qs.[[]]{2}).`1)
      /\  ([] \in C.O.qs{2} => oget Hybrid_PRF_L'.m.[true]{1} = (oget C.O.qs.[[]]{2}).`2)).
+ proc.
  inline *.
  sp.
  wp.
  if{2}.
  wp=> /=.
  + auto=> &1 &2 />.
    search dmap
    (* Need some magic, mainly g * h = j when all random*)
    admit.
  auto=> &1 &2 />.
  move=> h1 h2 ?.
  split=> _.
  + exact h2.
  exact h1.
auto=> &1 /> g1 _ g2 _.
split; by apply contraLR; move=> _; rewrite mem_empty.
qed.

lemma Security (D <: Distinguisher{PRF, RF, WP_Ideal, WP_Real, BoundPRF, Hybrid_PRF_0, Hybrid_PRF_0', Hybrid_PRF_L', C, Hybrid_PRF_L, Hybrid_WP_Ideal, Hybrid_WP_Real}) &m (x : int):
    `| Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(x) @ &m: res] - Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(x) @ &m: res] |
    <= `| Pr[WP_IND(WP_Real, C(D)).main() @ &m: res] - Pr[WP_IND(WP_Ideal, C(D)).main() @ &m: res] |.
proof.
rewrite (PRF_Hybrid_PRF_Reduction D).
rewrite -(Hybrid_WP_WP_Reduction (C(D))).
rewrite -(Hybrid_PRF_WP_Real_eq D).
rewrite -(Hybrid_PRF_WP_Ideal_eq D).
qed.
