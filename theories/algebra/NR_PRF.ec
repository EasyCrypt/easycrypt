(* NR-PRF *)
require import Int Real List SmtMap Distr.
require (*--*) GroupAction PRF.

clone import GroupAction.ARegEGA as Ega.

(*
(* Could be MUniform here *)
op dR : { set distr | is_lossless dR } as dR_ll.
*)
clone import MFinite as DR with
    type t <- set.
op dR = DR.dunifin.

(* Setup keyspace, domain, and range *)
type K = group * group.
type D = bool. (* Only one bit for the moment but will be an l-bit word *) 
type R = set.

clone import PRF as PRF_t with
    type D <- D, 
    type R <- R.
    
clone import RF with
    op dR <- fun _=> dR
proof
    dR_ll by (move=> _; exact: DR.dunifin_ll).

op F (k : K) (m : D) =
    if   m
    then act (k.`1 * k.`2) x0
    else act k.`1 x0.

clone import PseudoRF as Prf with
    type K  <- K,
      op F  <- F,
      op dK <- sample `*` sample
proof *.
realize dK_ll.
apply: dprod_ll.
search is_lossless.
split.
+ exact DG.dunifin_ll.
exact DG.dunifin_ll.
qed.

(* Lemma 4.21 *)
(* Start by just considering the case when l = 1, here we will just have two games for an adversary to distinguish *)

(* This adversary attempts to distinguish between the following two games *)
module type WPR_Oracles = {
    proc doit(_ : D): R
}.

module type Adversary1 (O : WPR_Oracles) = {
    proc distinguish() : bool
}.

(* Real PRF *)
module Hybrid0 (A : Adversary1) = {
    var g0, g1 : Ega.group

    module O = {
        proc doit(s) = {
            var yq;

            yq <- act g0 x0;
            if (s) {
                yq <- act g1 yq;
            }
            return yq;
        }
    }

    proc main () : bool = {
        var b : bool;

        (* Sample the key *)
        g0 <$ sample;
        g1 <$ sample;

        (* Allow the adversary to make Q adaptive queries *)
        b <@ A(O).distinguish();
        return b;
    }
}.

module (A (D : Distinguisher) : Adversary1) (F : WPR_Oracles) = {
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

lemma Hybrid0_INDPRF_eq (D <: Distinguisher {Hybrid0, PRF} ) &m:
  Pr[IND(PRF, D).main() @ &m: res] = Pr[Hybrid0(A(D)).main() @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
seq  1  2: (={glob D} /\ PRF.k{1} = (Hybrid0.g0,Hybrid0.g1){2}).
+ conseq />.
+ transitivity {1} (** Which memory should the piece of code operate in? **)
               { PRF.k <@ ProdSampling.S.sample(sample, sample); } (** Which piece of code? **)
               (true ==> ={PRF.k}) (** Left-to-step similarity **)
               (true ==> PRF.k{1} = (Hybrid0.g0, Hybrid0.g1){2}) (** Step-to-right similarity **)=> //.
  + by inline {2} 1; auto.
  transitivity {2}
               { (Hybrid0.g0, Hybrid0.g1) <@ ProdSampling.S.sample2(sample, sample); }
               ( true ==> PRF.k{1} = (Hybrid0.g0, Hybrid0.g1){2})
               (true ==> ={Hybrid0.g0, Hybrid0.g1})=> //.
  + by call ProdSampling.sample_sample2; auto=> /> [].
  by inline {1} 1; auto.
wp.
call (: PRF.k{1} = (Hybrid0.g0,Hybrid0.g1){2}).
+ proc; wp; skip=> />.
  move=> &2 _ @/F /=.
  rewrite comp.
  exact actC.  
by skip.
qed.

(* Ideal Randomness *)
module Hybrid1 (A : Adversary1) = {
    (* Keep track of previous input output pairs *) 
    var queries : (D, R) fmap

    module O = {
        proc doit(s) = {
            var gq, yq;
            
            if (s \notin queries) {
                gq <$ sample;
                yq <- act gq x0;
                queries.[s] <- yq;
            } else {
                yq <- oget queries.[s];
            }
            return yq;
        }
    }

    proc main () : bool = {
        var b : bool;
        queries <- empty;
        b <@ A(O).distinguish();
        return b;
    }
}.

lemma Hybrid1_INDRF_eq (D <: Distinguisher {Hybrid1, RF} ) &m:
    Pr[IND(RF, D).main() @ &m: res] = Pr[Hybrid1(A(D)).main() @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
wp.
sp.
call (: RF.m{1} = Hybrid1.queries{2}). (* maps are equivalently distributed *)
+ proc.
  if.
  + move=> &1 &2.
    case=> h1 h2.
    by subst.
  + seq 1 2 : (x{1} = s{2} /\ RF.m{1} = Hybrid1.queries{2} /\ r{1} = yq{2}).
    + wp.
      rnd (fun x => extract x0 x) (fun g => act g x0).
      skip=> />.
      move=> &2 _.
      split.
      + move=> g _.
        exact extractUniq.
      move=> _.
      split.
      + move=> g _.
        rewrite DG.dunifin1E DR.dunifin1E.
        search (_ / _)%Real.
        rewrite !RField.div1r.
        (* sample MUniform, dR uniform, supports equal cardinality <== finite sizes *)
        admit.
      move=> _ r rin.
      by rewrite extractP.
    wp.
    skip.
    move=> &1 &2.
    case=> eq1.
    case=> eq2 eq3.
    simplify.
    subst.
    split.
    + rewrite get_set_sameE.
      trivial.
    trivial.
  wp.
  by skip.
by skip.
qed.

(* Lemma 4.20 *)
module type Adversary2 = {
    proc solve(x0 : set, ins : (set * set) list, Q : int) : bool
}.

module GameReal (A : Adversary2) = {
    proc main (Q : int) : bool = {
        var gt : group;
        var b : bool;
        var ins : (set * set) list;
        
        gt <$ sample;

        (* FIXME: Get a nice way to sample a list of set tuples such that 
            (xq, Ega.act gt xq) : xq <- Ega.act gq Ega.x0, gq <$ Ega.sample, q \in Q]
        *)

        ins <- []; (*$ dmap (dlist n) (map (fun x => (x, Ega.act gt x)));*) 
        b <@ A.solve(x0, ins, Q);
        return b;
    }
}.

module GameIdeal (A : Adversary2) = {
    proc main (Q : int) : bool = {
        var b : bool;
        var ins : (set * set) list;
        
        (* FIXME: Get a nice way to sample a list of set tuples such that 
            (xq, Ega.act hq xq) : xq <- Ega.act gq Ega.x0, gq, hq <$ Ega.sample, q \in Q]
        *)

        ins <- []; (* dmap (dlist set_dist n) (map (fun x => (x, act gt x)));*) 
        b <- A.solve(x0, ins, Q);
        return b;
    }
}.


module Adv (A : Adversary1) = {
    var queries : (bool, (set * set)) fmap
    var cnt, q : int
    var els : (set * set) list
  
    module O = {
        proc doit(s) : set = {
            var xq, yq : set;
            
            if (q <= cnt) {
                cnt <- 1;
            }

            if (s \notin queries) {
                (xq, yq) <- (oget (onth els cnt));
                cnt <- cnt + 1;
                queries.[s] <- (xq, yq);
            } else {
                (xq, yq) <- (oget queries.[s]);
            }
          
            (* FIXME: why doesn't this work
            if (s) {
                return yq;
            } else {
                return xq;
            }
            *)

            return s ? yq : xq;
        }  
    }
  
    proc solve(x0 : set, ins : (set * set) list, Q : int) = {
        var s, b : bool;
        var xq, yq : set;
        
        els <- ins;
        q <- Q;
        cnt <- 1;
        b <@ A(O).distinguish();
        return b;
    }
}.

