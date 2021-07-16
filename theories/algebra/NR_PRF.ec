(* NR-PRF *)
require import Int Real List SmtMap Distr DList FSet PROM.
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

(* This function should compute the action of a list of group elements masked by an equal sized list of booleans *)
op compute_action (gs : group list) (ss : bool list) (x : set) : set =
    with gs = "[]"     ,      ss = "[]" => x
    with gs = "[]"     , ss = (::) s ss => x
    with gs = (::) g gs,      ss = "[]" => x
    with gs = (::) g gs, ss = (::) s ss =>
      if s then compute_action gs ss (act g x)
           else compute_action gs ss x.

(* A very useful lemma that shows that dR ~= sample *)
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


(* ---------------------------------------------------------------------------------------- *)

(* The hybrid used for the proof of Theorem 4.19 *)
(* This hybrid slowly replaces each action of a gi on x0 with the random sampling of a set element *)
(* The 0th hybrid should exactly represent a Pseudorandom function and the Lth hybrid a truly random function *)

module Hj (D : Distinguisher) = {

  (* Our hybrid parameter *)
  var j   : int

  var g0  : group (* This will only be used on the 0th hybrid *)
  var gis : group (* In the general case this will be a list of group elements of size l - j *)

  var yqs : (bool list, set) fmap (* Store any previous query's result *)

  (* Query bounding variables *)
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
        (* We have a special case for the 0th hybrid *)
        if (j = 0) {
          yq <- act g0 x0;
        } else {
          if (p \notin yqs) {
            gq <$ sample; (* FIXME: When the PRF theory is updated this line should be moved before the if *)
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

require (*--*) DProd.
clone DProd.ProdSampling with
  type t1 <- group,
  type t2 <- group.

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

(* Simple reduction statement for the case of l = 1 *)
lemma Hybrid_PRF_Reduction (D <: Distinguisher {BoundPRF, Hj, PRF, RF}) (q : int) &m :
    0 <= q
 =>  `|Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(q) @ &m: res] - Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(q) @ &m: res]|
   = `|Pr[Hj(D).run(0, q) @ &m: res] - Pr[Hj(D).run(1, q) @ &m: res]|.
by move=> z_le_q; rewrite (PRF_HybridL_pr D q &m z_le_q) (PRF_Hybrid0_pr D q &m z_le_q).
qed.

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

equiv prf_bound_eq (D <: Distinguisher) (O <: PRF) :
  D(O).distinguish ~ D(BoundPRF(O)).distinguish:
      ={glob D, glob O} /\ BoundPRF.c{1} = 1 /\ BoundPRF.c{2} = 1
  ==> ={res}.
proof.
admit.
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

(* -------------------------------------------------------- *)
(* Proving the hybrid reduction of lemma 4.21/ theorem 4.19 *)
clone import PROM.FullRO as YRO_t with
  type in_t    <- bool list,
  type out_t   <- R,
  type d_in_t  <- unit,
  type d_out_t <- bool,
    op dout _  <- dR. (* Might need to change this, who knows? *)

clone import PROM.FullRO as XRO_t with
  type in_t    <- bool list,
  type out_t   <- R,
  type d_in_t  <- unit,
  type d_out_t <- bool,
    op dout _  <- dR. (* Might need to change this, who knows? *)

module Y_RO (F : WP_Oracles)  : YRO_t.RO = {
  var yqs : (bool list, R) fmap

  proc init() = {
    yqs <- empty;
  }

  proc get(x) = {
    var xq, yq;
    if (x \notin yqs) {
      (xq, yq) <@ F.query();
      yqs.[x] <- yq;
    }
    return oget yqs.[x];
  }

  proc sample(x) = { get(x); }

  proc set(x : bool list, y : R) = {}
  proc rem(x : bool list) = {}
}.

module X_RO (F : WP_Oracles)  : XRO_t.RO = {
  var xqs : (bool list, R) fmap

  proc init() = {
    xqs <- empty;
  }

  proc get(x) = {
    var xq, yq;
    if (x \notin xqs) {
      (xq, yq) <@ F.query();
      xqs.[x] <- xq;
    }
    return oget xqs.[x];
  }

  proc sample(x) = { get(x); }

  proc set(x : bool list, y : R) = {}
  proc rem(x : bool list) = {}
}.

module B (D : Distinguisher) (Ys : YRO_t.RO) (Xs : XRO_t.RO) = {
  var j   : int

  var gis : group list

  var c   : int
  var q   : int

  module O = {
    proc f(x) = {
      var xs <- [x];
      var  p <- take j xs;
      var  b <- nth witness xs j;
      var  s <- drop (j + 1) xs;
      var  r <- witness;

      if (c <= q) {
        if (b) {
          r <@ Ys.get(p);
        } else {
          r <@ Xs.get(p);
        }
        r <- compute_action gis s r;
        c <- c + 1;
      }
      return r;
    }
  }

  proc distinguish() = {
    var b;
      Ys.init();
      Xs.init();
      j <- 0;
      c <- 1;
    gis <$ dlist sample 0; (* This should only sample for indices [j+2, l] *)
      b <@ D(O).distinguish();
    return b;
  }
}.

equiv Toto (D <: Distinguisher { Hj, B, Y_RO, X_RO, WP_Ideal }):
  Hj(D).run ~ B(D, Y_RO(WP_Ideal), X_RO(WP_Ideal)).distinguish:
    ={glob D} /\ i{1} = 1 /\ Q{1} = B.q{2} /\ 0 <= Q{1}
    ==> ={res}.
proof.
proc; sp=> //=.
call (:    B.j{2} = 0 /\ Hj.j{1} = 1
        /\ ={c, q}(Hj, B)
        /\ size B.gis{2} = 1 - B.j{2} - 1
        /\ (forall p, p \in Hj.yqs{1} => size p = Hj.j{1})
        /\ (forall p, p \in Y_RO.yqs{2} => size p = B.j{2})
        /\ (forall p, p \in X_RO.xqs{2} => size p = B.j{2})
        /\ (forall p, p \in Y_RO.yqs{2} => rcons p true \in Hj.yqs{1})
        /\ (forall p, p \in X_RO.xqs{2} => rcons p false \in Hj.yqs{1})
        /\ (forall p, Y_RO.yqs.[p]{2} = Hj.yqs.[rcons p true]{1})
        /\ (forall p, X_RO.xqs.[p]{2} = Hj.yqs.[rcons p false]{1})
        (** yqs[p' ++ [b]] = yq; _qs[p'] = (xq, gt * xq) **)).
+ proc; sp; if; 1,3:by auto.
  rcondf {1} 1; 1:by auto.
  inline *.
  if {1}.
  + if {2}; sp.
    + rcondt{2} 1=> //=.
      + auto=> /> &1 _ _ _ _ _ _ valLRy _ _ + x'.
        by rewrite x' !domE valLRy.
      wp=> />.
      symmetry.
      rnd (fun x => extract x0 x) (fun g => act g x0); rnd {1}.
      auto=> /> &1 &2 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q x_notin_yqs x'.
      move=> x xin.
      split=> [g _ | _]; first exact extractUniq.
      split=> [g _ | _ r _]; first exact sample_dR_iso.
      rewrite extractP /=.
      split.
      + rewrite !get_setE.
        by case (B.gis{1}).
      split.
      + by move=> p; rewrite mem_set=> - [] // /domR_size.
      split.
      + by move=> p; rewrite mem_set=> - [] // /domLy_size.
      split.
      + by move=> p; rewrite !mem_set=> - [] // /domLRy ->.
      split.
      + by move=> p; rewrite !mem_set=> /domLRx ->.
    by split; (case=> [ | b l]; rewrite !get_setE ?valLRy ?valLRx //=; case l).
    rcondt{2} 1=> //=.
      + auto=> /> &1 _ _ _ _ _ _ _ valLRx _ + x'.
        by rewrite x' !domE valLRx.
    wp=> />.
    symmetry.
    rnd {1}; rnd (fun x => extract x0 x) (fun g => act g x0).
    auto=> /> &1 &2 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q x_notin_yqs x'.
    split=> [g _ | _]; first exact extractUniq.
    split=> [g _ | _ r _]; first exact sample_dR_iso.
    rewrite extractP /=.
    move=> y yin.
    split.
    + rewrite !get_setE.
      by case (B.gis{1}).
    split.
    + by move=> p; rewrite mem_set=> - [] // /domR_size.
    split.
    + by move=> p; rewrite mem_set=> - [] // /domLx_size.
    split.
    + by move=> p; rewrite !mem_set=> /domLRy ->.
    split.
    + by move=> p; rewrite !mem_set=> - [] // /domLRx ->.
    by split; (case=> [ | b l]; rewrite !get_setE ?valLRy ?valLRx //=; case l).
  if {2}=> //=; sp.
  + rcondf{2} 1=> //=.
    + auto=> /> &1 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q + x'.
      by rewrite x' !domE valLRy.
    auto=> /> &1 &2 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q x_notin_yqs x'.
    move: size_gis.
    rewrite size_eq0=> -> /=; congr.
    by rewrite -(valLRy []).
  rcondf{2} 1=> //=.
  + auto=> /> &1 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q + x'.
    by rewrite x' !domE valLRx.
  auto=> /> &1 &2 size_gis domR_size domLy_size domLx_size domLRy domLRx valLRy valLRx c_le_q x_notin_yqs x'.
  move: size_gis.
  rewrite size_eq0=> -> /=; congr.
  by rewrite -(valLRx []).
inline *.
sp; wp.
rnd {2}.
auto=> /> &2 z_le_q g _ gi _ gis gis_in.
split.
+ exact (supp_dlist_size sample).
smt(mem_empty emptyE).
qed.

lemma Hybrid_PRF_WP_Real_eq (D <: Distinguisher{Hybrid_PRF_0', Hybrid_WP_Real, B}) &m :
    Pr[IND(Hybrid_PRF_0', D).main() @ &m: res] = Pr[WP_IND(Hybrid_WP_Real, B(D)).main() @ &m: res].
proof.
admitted.
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

lemma Security (D <: Distinguisher{PRF, RF, WP_Ideal, WP_Real, BoundPRF, Hybrid_PRF_0, Hybrid_PRF_0', Hybrid_PRF_L', B, Hybrid_PRF_L, Hybrid_WP_Ideal, Hybrid_WP_Real}) &m (x : int):
    `| Pr[Bounded_PRF_IND(BoundPRF(PRF), D).main(x) @ &m: res] - Pr[Bounded_PRF_IND(BoundPRF(RF), D).main(x) @ &m: res] |
    <= `| Pr[WP_IND(WP_Real, B(D)).main() @ &m: res] - Pr[WP_IND(WP_Ideal, B(D)).main() @ &m: res] |.
proof.
admitted.
