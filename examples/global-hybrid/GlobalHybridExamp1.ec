(* GlobalHybridExamp1.ec *)

(* We use theories/crypto/GlobalHybrid.ec to relate the probabilities
   of a "real" and an "ideal" game returning true.

   The real game initializes a boolean to true, and then loops m - 1
   times, where at each iteration it has a 1 / 2^n probability of
   setting the boolean to false. Once the loop terminates, it returns
   the boolean.

   The ideal game always returns true. *)

require import AllCore Real Distr StdOrder StdBigop GlobalHybrid.
import RealOrder Bigreal BRA.

op n : {int | 1 <= n} as ge1_n.

type t.  (* we want t to have 2 ^ n elements, including def *)

op def : t.

op [lossless] dt : t distr.

axiom mu1_dt (x : t) : mu1 dt x = 1%r / (2 ^ n)%r.

lemma dt_uni : is_uniform dt.
proof. move => x y _ _; by rewrite !mu1_dt. qed.

lemma dt_fu : is_full dt.
proof.
rewrite funi_ll_full.
move => x y; by rewrite !mu1_dt.
rewrite dt_ll.
qed.

op m : {int | 1 <= m} as ge1_m.

module GReal = {
  proc main() : bool = {
    var b <- true;
    var i : int <- 1;
    var x : t;
    while (i < m) {
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

module GIdeal = {
  proc main() : bool = {
    return true;
  }
}.

(* we want to prove:

lemma GReal_GIdeal &m :
  `|Pr[GReal.main() @ &m : res] - Pr[GIdeal.main() @ &m : res]| <=
  (m - 1)%r * (1%r / (2 ^ n)%r).
*)

module Hybrid : HYBRID = {
  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    (* start from i: *)
    while (i < m) {
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

lemma GReal_Hybrid_1 &m :
  Pr[GReal.main() @ &m : res] = Pr[Hybrid.main(1) @ &m : res].
proof.
byequiv => //; proc.
seq 2 1 : (={b, i} /\ i{1} = 1); first auto.
sim.
qed.

lemma Hybrid_m &m :
  Pr[Hybrid.main(m) @ &m : res] = Pr[GIdeal.main() @ &m : res].
proof.
byequiv => //; proc; sp 1 0.
rcondf{1} 1; auto.
qed.

(* we use upto bad reasoning *)

module GBad1 = {
  var bad : bool  (* bad event *)

  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    bad <- false;
    x <$ dt;
    if (x = def) {
      bad <- true;  (* bad event *)
      b <- false;   (* assignment to b *)
    }
    i <- i + 1;
    while (i < m) {  (* rest as usual *)
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

module GBad2 = {
  var bad : bool

  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    bad <- false;
    x <$ dt;
    if (x = def) {
      bad <- true;  (* bad event *)
                    (* but no assignment to b *)
    }
    i <- i + 1;
    while (i < m) {  (* rest as usual *)
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

lemma Hybrid_step (i' : int) &m :
  1 <= i' < m =>
  `|Pr[Hybrid.main(i') @ &m : res] - Pr[Hybrid.main(i' + 1) @ &m : res]| <=
  1%r / (2 ^ n)%r.
proof.
move => [ge1_i' lt_i'_m]. 
have -> : Pr[Hybrid.main(i') @ &m : res] = Pr[GBad1.main(i') @ &m : res].
  byequiv => //; proc; sp 1 2.
  rcondt{1} 1; first auto.
  sim.
have -> : Pr[Hybrid.main(i' + 1) @ &m : res] = Pr[GBad2.main(i') @ &m : res].
  byequiv => //; proc; sp 1 2.
  seq 0 3 : (={i, b}); first auto.
  sim.
rewrite (ler_trans Pr[GBad2.main(i') @ &m : GBad2.bad]).
byequiv
  (_ :
   ={i} ==> GBad1.bad{1} = GBad2.bad{2} /\ (! GBad2.bad{2} => ={res})) :
  GBad1.bad => //.
proc.
seq 5 5 :
  (GBad1.bad{1} = GBad2.bad{2} /\ ={i} /\
   (!GBad2.bad{2} => ={b})); first auto.
case (GBad1.bad{1}).
while (={i}); auto.
while (={i, b}); auto; smt().
smt().
byphoare => //; proc; sp.
seq 3 :
  GBad2.bad
  (1%r / (2 ^ n)%r)
  1%r
  (1%r - (1%r / (2 ^ n)%r))
  0%r.
auto.
wp; rnd (pred1 def); auto; smt(mu1_dt).
conseq (_ : _ ==> _ : = 1%r).
while (true) (m - i) => [z |].
auto; smt(dt_ll).
auto; smt().
hoare; while (true); auto.
trivial.
qed.

lemma GReal_GIdeal &m :
  `|Pr[GReal.main() @ &m : res] - Pr[GIdeal.main() @ &m : res]| <=
  (m - 1)%r * (1%r / (2 ^ n)%r).
proof.
rewrite (GReal_Hybrid_1 &m) -(Hybrid_m &m).
rewrite (hybrid_simp _ _ Hybrid) 1:ge1_m => i ge1_i_lt_m.
by rewrite Hybrid_step.
qed.
