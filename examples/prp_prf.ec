require import Int.
require import AWord.
require import FSet.
require import FMap.
require import Real.
require import Distr.
require import Sum.

const l : int. (* block size *)
const q : int. (* maximum number of queries made by the adversary *)

axiom q_pos : 0 <= q.
axiom Leq : q < 2 ^ l.


clone AWord as Block with op length = l.

(* require Monoid. *)
(* clone Monoid as MInt with *)
(*   type t = int, *)
(*   op (+) = Int.(+), *)
(*   op Z = 0. *)

(* import MInt. *)
(* Fel uses sum_int from sum library *)
type block = Block.word.

op uniform : block distr = Block.Dword.dword.


import Dexcepted.
(* Abstract cipher *)
module type AC = {
 proc f (x : block) : block
 proc init () : unit 
 }.

module type AAC = {
 proc f (x : block) : block
}.

module PRP : AC = {
 var m : (block, block) map
 var s : block set
 var bad : bool
 proc init() : unit ={
  m = FMap.empty;
  s = FSet.empty;
  bad = false;
 }
 proc f (x : block) : block ={
  var y : block;
  if (!mem x (dom m) /\ card s < q) {
   y = $uniform;
   if (mem y s) {
    bad = true;
    y = $uniform \ s;
   }
   s = add y s;
   m.[x] = y;
  }
  return oget (m.[x]);
 }
}.

module PRF : AC = {
 var m : (block, block) map
 var s : block set
 proc init() : unit ={
  m = FMap.empty;
  s = FSet.empty;
 }
 proc f (x : block) : block = {
  var y : block;
  if (!mem x (dom m) /\ card s < q) {
   y = $uniform;
   m.[x] = y;
   s = add y s; 
  }
  return oget (m.[x]);
 }
}.

module type Adv(M : AAC) =
{
 proc a() : bool
}.


module M(C : AC, A_ : Adv) ={
 module A = A_(C)
 proc main() : bool = {
  var b : bool;
  C.init();
  b = A.a();
  return b;
 }
}.

section.

declare module A : Adv {PRP,PRF}.
axiom losslessA :
forall (M0 <: AAC), islossless M0.f => islossless A(M0).a.

equiv eq1 : M(PRF,A).main ~ M(PRP,A).main : 
            ={glob A} ==> card (PRP.s{2}) <= q /\ (!PRP.bad{2} => ={res}).
proof.
 proc.
 call (_ : PRP.bad,
           PRF.m{1} = PRP.m{2} /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) <= q, 
           card (PRP.s{2}) <= q).
 by intros M0 Hmo; apply (losslessA M0) => //.
 proc.
 if;first by smt.
 seq 1 1: 
 ((! PRP.bad{2} /\ ={x,y} /\ PRF.m{1} = PRP.m{2}) /\ ! mem x{1} (dom PRF.m{1}) /\
    card PRF.s{1} < q /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) < q).
 by rnd;skip => //.
 if{2}.
 by wp;rnd{2};wp;skip;progress;smt.
 by wp;skip;progress;smt.
 by skip;smt.
 intros &m2 H;proc;if;wp.
 rnd True.
 wp;skip;progress;by smt.
 skip;by smt.
 intros &m1;proc;if;wp.
 seq 1: ((PRP.bad /\ true) /\ ! mem x (dom PRP.m) /\ card PRP.s < q);last by smt.
 trivial.
 rnd True; skip;by smt.
 if;[rnd True;wp|];skip;by smt.
 by hoare;rnd;skip => //.
 by skip => //.
 inline PRF.init PRP.init;wp;skip;by smt.
qed.

lemma real_le_trans : forall(a b c : real),  
  a <= b => b <= c => a <= c by []. 

lemma prob1 : forall &m, 
 Pr[ M(PRF,A).main() @ &m : res] <= 
 Pr[ M(PRP,A).main() @ &m : res] + 
 Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q].
proof.
 intros => &m.
 apply (real_le_trans _ 
 Pr[ M(PRP,A).main() @ &m : (res || (PRP.bad /\  card PRP.s <= q))] _ _ _).
 byequiv(eq1) => // ;first by smt.
 rewrite Pr [mu_or];by smt.
qed.

(* assumed property *)
lemma sum_prop (n : int):
  0 <= n =>
  int_sum (fun x, x%r * (1%r / (2 ^ l)%r)) (intval 0 (n - 1))
  <= n%r * (n - 1)%r * (1%r / (2 ^ l)%r).
proof.
  move=> leq0_n.
  cut ->: int_sum (fun x, x%r * (1%r/(2^l)%r)) (intval 0 (n - 1))
          = int_sum (fun x, x%r) (intval 0 (n - 1)) * (1%r/(2^l)%r).
    rewrite /int_sum /intval.
    move: leq0_n; elim/Induction.induction n.
      cut ->: Interval.interval 0 (0 - 1) = FSet.empty by smt.
      by rewrite !Monoid.Mrplus.sum_empty; smt.
      move=> n leq0_n IH; cut ->: n + 1 - 1 = n by smt.
      cut:= Monoid.Mrplus.sum_ij_le_r 0 n (fun x, x%r * (1%r/(2^l)%r)) _=> //.
      rewrite /Monoid.Mrplus.sum_ij IH=> -> /=.
      cut:= Monoid.Mrplus.sum_ij_le_r 0 n (fun x, x%r) _=> //.
      rewrite /Monoid.Mrplus.sum_ij=> -> /=.
      smt.
  cut ->: int_sum (fun x, x%r) (intval 0 (n - 1)) = (n - 1)%r * n%r / 2%r.
    rewrite /int_sum /intval.
    move: leq0_n; elim/Induction.induction n.
      cut ->: Interval.interval 0 (0 - 1) = FSet.empty by smt.
      by rewrite !Monoid.Mrplus.sum_empty; smt.
      move=> n leq0_n IH; cut ->: n + 1 - 1 = n by smt.
      cut:= Monoid.Mrplus.sum_ij_le_r 0 n (fun x, x%r) _=> //.
      by rewrite /Monoid.Mrplus.sum_ij IH=> -> /=; smt.
  cut ->: (n - 1)%r * n%r / 2%r = n%r * (n - 1)%r * (1%r / 2%r) by smt.
  cut ->: n%r * (n - 1)%r * (1%r / 2%r) * (1%r / (2^l)%r) = (n%r * (n - 1)%r * (1%r / (2^l)%r)) * 1%r / 2%r by smt.
  cut ->: forall x, 0%r <= x => x * 1%r / 2%r <= x; first last; last 2 smt.
  cut ->: n%r * (n - 1)%r = (n * (n - 1))%r by smt.
  cut ->: forall x y, 0%r <= x => 0%r <= y => 0%r <= x * y; smt.  
qed.

lemma prob2 : forall &m, 
Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q] <= 
q%r * (q-1)%r * (1%r / (2^l)%r).
proof.
 intros => &m.
 fel 1 (card PRP.s) (fun x, (x%r)* (1%r/(2^l)%r)) 
     q PRP.bad [PRP.f : (! mem x (dom PRP.m) /\ card PRP.s < q)] => //. 
  apply sum_prop;by smt.
  inline PRP.init;wp;skip;by smt.
  proc;if;wp.
  seq 1 : (mem y PRP.s) 
          ((card PRP.s)%r * (1%r / (2^l)%r)) (1%r) 
          (1%r - ((card PRP.s)%r * (1%r / (2^l)%r))) (0%r)
          (!PRP.bad /\ ! mem x (dom PRP.m) /\ card PRP.s < q) => //. 
   by rnd => //.
   rnd  (cpMem PRP.s);skip;progress;last trivial.
   delta uniform Block.length;rewrite Block.Dword.mu_cpMemw.
   delta Block.length; by smt.

   hoare;if;[rnd;wp |];skip;by smt.
   conseq [-frame] (_: _: 0%r); last by hoare.
     move=> _ _.
     cut H: forall x y, 0%r <= x => 0%r < y => 0%r <= x * y by smt.
     by apply H; [| rewrite -inv_def sign_inv]; smt.
   intros c;proc;if;last by skip;smt.
 
   wp;seq 1: ((! mem x (dom PRP.m) /\ card PRP.s < q) /\ c = card PRP.s /\
  ! mem x (dom PRP.m) /\ card PRP.s < q /\ in_supp y uniform); first by rnd.
   if;[rnd;wp|];skip;progress;by smt.
         
  intros b c;proc;wp;if;last by skip;smt.
  seq 1:  ((! (! mem x (dom PRP.m) /\ card PRP.s < q) /\ PRP.bad = b /\ 
          card PRP.s = c) /\ ! mem x (dom PRP.m) /\ card PRP.s < q /\ 
          in_supp y uniform);first rnd;skip;by smt.
  if;[wp;rnd|];wp;skip;by smt.
qed.


lemma concl : forall &m, 
 Pr[ M(PRF,A).main() @ &m : res] <= 
 Pr[ M(PRP,A).main() @ &m : res] + q%r * (q-1)%r * (1%r / (2^l)%r).
proof.
 intros &m.
 apply (real_le_trans _  
 (Pr[ M(PRP,A).main() @ &m : res] + 
 Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q]) _).
 by apply (prob1 &m).
 cut H: Pr[M(PRP, A).main() @ &m : PRP.bad /\ card PRP.s <= q] <= 
        q%r * (q - 1)%r * (1%r / (2 ^ l)%r).
 by apply (prob2 &m).
 cut H1: forall (x y z : real), x <= y => z + x <= z + y;first by smt.
 by apply H1 => //.    
qed.

end section.
