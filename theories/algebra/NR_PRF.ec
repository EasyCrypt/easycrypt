(* NR-PRF *)
require import Int Real List SmtMap Distr DList FSet.
require (*--*) GroupAction.

(* We need a regular, effective, abelian group action for this construction *) 
clone import GroupAction.ARegEGA as Ega.

(* Setup keyspace, domain, and range *)
type K = group * group.
type D = bool. (* Only one bit for the moment but will be an l-bit word *) 
type R = set.

(* This is the construction we wish to prove is a PRF *)
op F (k : K) (m : D) =
    if   m
    then act (k.`1 * k.`2) x0
    else act k.`1 x0.

(* Setup the uniform distribution on our range *)
clone import MFinite as DR with
    type t <- R.
op dR : D -> R distr = fun _ => DR.dunifin.
lemma dR_ll (x : D) : is_lossless (dR x).
proof.
exact DR.dunifin_ll.
qed. 

op dK : K distr = sample `*` sample.
lemma dK_ll : is_lossless dK.
proof.
apply dprod_ll.
split; exact DG.dunifin_ll.
qed.

(* ------------------------------------------------------ *)
(* Setup the bounded PRF games/oracles/adversaries *)

module type Bounded_PRF = {
    proc init(Q : int) : unit
    proc f(_ : D) : R
}.

module type PRF_Oracles = {
    proc f(_ : D) : R
}.

module type Distinguisher (F : PRF_Oracles) = {
    proc distinguish() : bool
}.

module Bounded_PRF_IND (F : Bounded_PRF) (D : Distinguisher) = {
    proc main(Q : int) : bool = {
        var b;
        F.init(Q);
        b <@ D(F).distinguish();
        return b;
    }
}.

module Bounded_PRF_Real = {
    var k : K
    var c, q : int
    
    proc init(Q : int) : unit = {
        k <$ dK;
        q <- Q;
        c <- 1;
    }

    proc f(x : D) : R = {
        var val : R;
        if (c <= q) {
            val <- F k x;
            c <- c + 1;
        } else {
            val <- witness;
        }        
        return val;
    }
}.

module Bounded_PRF_Ideal = {
    var c, q : int
    var m : (D, R) fmap

    proc init(Q : int): unit = {
        q <- Q;
        c <- 1;
        m <- empty;
    }

    proc f(x : D) : R = {
        var val : R;
        if (c <= q) {
            if (x \notin m) {
                val <$ dR x;
                m.[x] <- val;
            }
            val <- (oget m.[x]);
            c <- c + 1;
        } else {
            val <- witness;
        }
        return val;
    }
}.

(* ------------------------------------------------------------ *)
(* Lemma 4.21 *)
(* Start by just considering the case when l = 1, here we will just have two games for an adversary to distinguish *)

module type Hybrid_PRF = {
    proc init(_ : int) : unit
    proc doit(_ : D) : R
}.

module type WPR_Oracles = {
    proc doit(_ : D) : R
}.

module type Hybrid_PRF_Adv (O : WPR_Oracles) = {
    proc distinguish() : bool
}.

module Hybrid_PRF_IND (H : Hybrid_PRF) (A : Hybrid_PRF_Adv) = {
    proc main (Q : int) : bool = {
        var b : bool;
        H.init(Q);
        b <@ A(H).distinguish();
        return b;
    }
}.

module Hybrid_PRF_0 = {
    var g0, g1 : group
    var c, q : int

    proc init(Q : int) = {
        g0 <$ sample;
        g1 <$ sample;
        q <- Q;
        c <- 1;
    }

    proc doit(s) = {
        var val;

        (* Make sure we can't make more than Q, 'proper', queries *)
        if (c <= q) {
            val <- act g0 x0;
            if (s) {
                val <- act g1 val;
            }
            c <- c + 1;
        } else {
            val <- witness;
        }
        return val;
    }
}.

module Hybrid_PRF_L = {
    var m : (D, R) fmap
    var q, c : int
  
    proc init(Q : int) = {
        q <- Q;
        c <- 1;
        m <- empty;
    }

    proc doit(s) = {
        var gq, val;
        if (c <= q) {
            if (s \notin m) {
                gq <$ sample;
                val <- act gq x0;
                m.[s] <- val;
            } else {
                val <- oget m.[s];
            }
            c <- c + 1;
        } else {
            val <- witness;
        }
        return val;
    }
}.

(* Simply wrap around the distinguisher for a PRF *)
module (A (D : Distinguisher) : Hybrid_PRF_Adv) (F : WPR_Oracles) = {
    module O = {
        proc f = F.doit
    }

    proc distinguish() = {
        var b;

        b <@ D(O).distinguish();
        return b;
    }
}.

(** |Pr[IND(PRF, D).main() @ &m: res] - Pr[IND(RF, D).main() @ &m: res]|
    <= Advantage of A(D) against something we think is hard **)

require (*--*) DProd.
clone DProd.ProdSampling with
  type t1 <- group,
  type t2 <- group.

lemma Hybrid_PRF_0_PRF_Real_eq (D <: Distinguisher {Hybrid_PRF_0, Bounded_PRF_Real}) (x : int) &m:
  Pr[Bounded_PRF_IND(Bounded_PRF_Real, D).main(x) @ &m: res] = Pr[Hybrid_PRF_IND(Hybrid_PRF_0, A(D)).main(x) @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
sp.
seq  1  2: (={glob D}
            /\ Bounded_PRF_Real.k{1} = (Hybrid_PRF_0.g0,Hybrid_PRF_0.g1){2}
            /\ ={Q}
            /\ ={Q0}
            ).
+ conseq />.
  transitivity {1} (** Which memory should the piece of code operate in? **)
               { Bounded_PRF_Real.k <@ ProdSampling.S.sample(sample, sample); } (** Which piece of code? **)
               (true ==> ={Bounded_PRF_Real.k}) (** Left-to-step similarity **)
               (true ==> Bounded_PRF_Real.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2}) (** Step-to-right similarity **)=> //.
  + by inline {2} 1; auto.
  transitivity {2}
               { (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1) <@ ProdSampling.S.sample2(sample, sample); }
               ( true ==> Bounded_PRF_Real.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2})
               (true ==> ={Hybrid_PRF_0.g0, Hybrid_PRF_0.g1})=> //.
  + by call ProdSampling.sample_sample2; auto=> /> [].
  by inline {1} 1; auto.
wp.
sp.
call (: Bounded_PRF_Real.k{1} = (Hybrid_PRF_0.g0, Hybrid_PRF_0.g1){2}
      /\ Bounded_PRF_Real.c{1} = Hybrid_PRF_0.c{2}
      /\ Bounded_PRF_Real.q{1} = Hybrid_PRF_0.q{2}
      ).
+ proc; wp; skip=> />.
  move=> &2 _ _ @/F /=.  
  rewrite comp.
  exact: actC.
skip=> />.
qed.

lemma Hybrid_PRF_L_PRF_Real_eq (D <: Distinguisher {Hybrid_PRF_L, Bounded_PRF_Ideal}) (a : int) &m:
    Pr[Bounded_PRF_IND(Bounded_PRF_Ideal, D).main(a) @ &m: res] = Pr[Hybrid_PRF_IND(Hybrid_PRF_L, A(D)).main(a) @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
wp.
sp.
call (:  Bounded_PRF_Ideal.m{1} = Hybrid_PRF_L.m{2}
      /\ Bounded_PRF_Ideal.c{1} = Hybrid_PRF_L.c{2}
      /\ Bounded_PRF_Ideal.q{1} = Hybrid_PRF_L.q{2}
      ).
+ proc.
  if.
  + by move=> />.
  + if.
    + by move=> />.
    + seq 1 2 : (x{1} = s{2}
                /\ ={val}
                /\ Bounded_PRF_Ideal.m{1} = Hybrid_PRF_L.m{2}
                /\ Bounded_PRF_Ideal.c{1} = Hybrid_PRF_L.c{2}
                /\ Bounded_PRF_Ideal.q{1} = Hybrid_PRF_L.q{2}
                ).
      + wp.
        rnd (fun x => extract x0 x) (fun g => act g x0).
        skip=> &1 &2.
        do case => eq1 eq2 _ _ />.
        split.
        + move=> g _.
          exact extractUniq.
        move=> _.
        split.
        + move=> g _.
          have /= <- := dmap1E_can DR.dunifin (extract x0) (fun g=> act g x0) g _ _.
            + by rewrite /cancel=> g'; rewrite -extractUniq.
            + by move=> x _ /=; rewrite extractP.
          congr; apply: eq_funi_ll.
          + exact: DG.dunifin_funi.
          + exact: DG.dunifin_ll.
          + apply/dmap_funi.
            + exists (fun g=> act g x0); split.
              + by move=> x; exact: extractP.
              by move=> h; rewrite -extractUniq.
            exact: dunifin_funi.
          exact/dmap_ll/dunifin_ll.
        move=> _ r rin.
        by rewrite extractP.
      wp.
      skip.
      move=> &1 &2 />.
      rewrite get_set_sameE.
      trivial.
    wp.
    by skip.
  wp.
  by skip.
by skip.
qed.

(* ----------------------------------------------- *)
module type Hybrid_WPR = {
    proc init(_ : int) : unit
    proc vals() : R * R
}.

module type H_WPR_Oracles = {
    proc vals() : R * R
}.

module type Hybrid_WPR_Adv (F : H_WPR_Oracles) = {
    proc solve() : bool
}.

module Hybrid_WPR_IND (H : Hybrid_WPR) (A : Hybrid_WPR_Adv) = {
    proc main(Q : int) : bool = {
        var b : bool;
        H.init(Q);
        b <@ A(H).solve();
        return b;
    }
}.

module Hybrid_WPR_Ideal = {
    var q, c : int
    var gt : group
  
    proc init(Q : int) = {
        q <- Q;
        c <- 1;
        gt <$ sample;
    }

    proc vals() = {
        var gq, xq, yq;
        if (c <= q) {
            gq <$ sample;
            xq <- act gq x0;
            yq <- act gt xq;
            c <- c + 1;
        } else {
            (xq, yq) <- witness;
        }
        return (xq, yq);
    }
}.

module Hybrid_WPR_Real = {
    var q, c : int
  
    proc init(Q : int) = {
        q <- Q;
        c <- 1;
    }

    proc vals() = {
        var gq, hq, xq, yq;
        if (c <= q) {
            gq <$ sample;
            hq <$ sample;
            xq <- act gq x0;
            yq <- act hq xq;
            c <- c + 1;
        } else {
            (xq, yq) <- witness;
        }
        return (xq, yq);
    }
}.

module (B (D : Hybrid_PRF_Adv) : Hybrid_WPR_Adv) (F : H_WPR_Oracles) = {
    module O = {
        var m : (D, R) fmap
      
        proc doit(s : D) = {
            var val : R;
            var tup : R * R;
            if (s \notin m) {
                tup <- F.vals();
                if (s) {
                    val <- tup.`1;            
                } else {
                    val <- tup.`2; 
                }
                m.[s] <- val;
            } else {
                val <- oget m.[s];
            }
            return val;
        }
    }  

    proc solve() = {
        var b;
        b <@ D(O).distinguish();
        return b;
    }
}.


lemma Hybrid_WPR_Real_Hybrid_PRF_0_eq (A <: Hybrid_PRF_Adv{Hybrid_WPR_Real, Hybrid_PRF_0}) (x : int) &m:
  Pr[Hybrid_PRF_IND(Hybrid_PRF_0, A).main(x) @ &m: res] = Pr[Hybrid_WPR_IND(Hybrid_WPR_Real, B(A)).main(x) @ &m: res].
proof.
admit.
qed.
