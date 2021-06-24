(* NR-PRF *)
require import Int Real List SmtMap Distr.
require (*--*) GroupAction PRF.

clone import GroupAction.EGA as Ega.

op dR : { set distr | is_lossless dR } as dR_ll.

type K = group * group.
type D = bool.
type R = set.

clone import PRF as PRF_t with
  type D <- D, (* Only one bit for the moment but should be an l-bit word *) 
  type R <- R.

clone import RF with
  op dR <- fun _=> dR
proof
  dR_ll by (move=> _; exact: dR_ll).

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
admit.
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
        proc doit(x) = {
            var yq;

            yq <- act g0 x0;
            if (x) {
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

lemma Hybrid0_INDPRF_eq (D <: Distinguisher {Hybrid0, PRF} ) &m:
  Pr[IND(PRF, D).main() @ &m: res] = Pr[Hybrid0(A(D)).main() @ &m: res].
proof.
byequiv=> //.
proc.
inline *.
seq  1  2: (={glob D} /\ PRF.k{1} = (Hybrid0.g0,Hybrid0.g1){2}).
+ admit. (** DProd sampling **)
wp.
call (: PRF.k{1} = (Hybrid0.g0,Hybrid0.g1){2}).
+ proc; wp; skip=> />.
  move=> &2 _ @/F /=.
  admit. (** We need a commutative group action **)
by skip.
qed.

(* Ideal Randomness *)
module Hybrid1 (A : Adversary1) = {
    (* Keep track of previous input output pairs *) 
    var queries : (bool, Ega.set) fmap

    proc main (Q : int) : bool = {
        var gq : Ega.group;
        var q : int;
        var s, b : bool;
        var yq : Ega.set;

        (* Allow the adversary to make Q adaptive queries *)
        q <- 0;
        while (q <= Q) {
            s <@ A.make_query();

            if (s \notin queries) {
                gq <$ Ega.sample;
                yq <- Ega.act gq Ega.x0;
                queries.[s] <- yq;
            } else {
                yq <- oget queries.[s];
            }

            A.give_response(yq);
            
            q <- q + 1;
        }

        b <@ A.make_guess();
        return b;
    }
}.

(* Lemma 4.20 *)
module type Adversary2 = {
    proc solve(x0 : Ega.set, ins : (Ega.set * Ega.set) list, Q : int) : bool
}.

module GameReal (A : Adversary2) = {
    proc main (Q : int) : bool = {
        var gt : Ega.group;
        var b : bool;
        var ins : (Ega.set * Ega.set) list;
        
        gt <$ Ega.sample;

        (* FIXME: Get a nice way to sample a list of set tuples such that 
            (xq, Ega.act gt xq) : xq <- Ega.act gq Ega.x0, gq <$ Ega.sample, q \in Q]
        *)

        ins <- []; (*$ dmap (dlist n) (map (fun x => (x, Ega.act gt x)));*) 
        b <@ A.solve(Ega.x0, ins, Q);
        return b;
    }
}.

module GameIdeal (A : Adversary2) = {
    proc main (Q : int) : bool = {
        var b : bool;
        var ins : (Ega.set * Ega.set) list;
        
        (* FIXME: Get a nice way to sample a list of set tuples such that 
            (xq, Ega.act hq xq) : xq <- Ega.act gq Ega.x0, gq, hq <$ Ega.sample, q \in Q]
        *)

        ins <- []; (* dmap (dlist set_dist n) (map (fun x => (x, act gt x)));*) 
        b <- A.solve(Ega.x0, ins, Q);
        return b;
    }
}.


module Adv (A : Adversary1) = {
    var queries : (bool, (Ega.set * Ega.set)) fmap
  
    proc solve(x0 : Ega.set, ins : (Ega.set * Ega.set) list, Q : int) = {
        var cnt, q : int;
        var s, b : bool;
        var xq, yq : Ega.set;

        cnt <- 1;
        q <- 1;
        while (q <= Q) {
            s <@ A.make_query();

            if (s \notin queries) {
                xq <- (oget (onth ins cnt)) .` 1;
                yq <- (oget (onth ins cnt)) .` 2;
                cnt <- cnt + 1;
                queries.[s] <- (xq, yq);
            } else {
                xq <- (oget queries.[s]) .` 1;
                yq <- (oget queries.[s]) .` 2;
            }
            
            if (s) {
                A.give_response(yq);
            } else {
                A.give_response(xq);
            }

            q <- q + 1;
        }

        b <@ A.make_guess();
        return b;
    }
}.

