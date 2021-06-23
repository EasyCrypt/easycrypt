(* NR-PRF *)
require import Int List SmtMap.
require (*--*) GroupAction PRF.
(*---*) import GroupAction.EGA SmtMap.Map.

print Map.

clone GroupAction.EGA as Ega.

(*
clone include PRF with
  type D <- bool, (* Only one bit for the moment but should be an l-bit word *) 
  type R <- Ega.set.

clone include RF.
clone PseudoRF as Prf with
  type K <- Ega.group * Ega.group,
  op F <- (fun (g : Ega.group * Ega.group) (b : bool) =>
    b ? Ega.act (Ega.( * ) (g .` 1) (g .` 2)) Ega.x0 : Ega.act (g .` 1) Ega.x0).
*)

(* Lemma 4.21 *)
(* Start by just considering the case when l = 1, here we will just have two games for an adversary to distinguish *)

(* This adversary attempts to distinguish between the following two games *)
module type Adversary1 = {
    proc make_query () : bool
    proc give_response (x : Ega.set) : unit
    proc make_guess () : bool
}.

(* Real PRF *)
module Hybrid0 (A : Adversary1) = {
    proc main (Q : int) : bool = {
        var g0, g1 : Ega.group;
        var q : int;
        var s, b : bool;
        var yq : Ega.set;

        (* Sample the key *)
        g0 <$ Ega.sample;
        g1 <$ Ega.sample;

        (* Allow the adversary to make Q adaptive queries *)
        q <- 0;
        while (q <= Q) {
            s <@ A.make_query();

            yq <- Ega.act g0 Ega.x0;
            if (s) {
                yq <- Ega.act g1 yq;
            }

            A.give_response(yq);
            
            q <- q + 1;
        }
        b <@ A.make_guess();
        return b;
    }
}.

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

