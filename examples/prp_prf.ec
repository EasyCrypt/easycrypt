require import Int.
require import AWord.
require import FSet.
require import Map.
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
 fun f (x : block) : block
 fun init () : unit 
 }.

module type AAC = {
 fun f (x : block) : block
}.

module PRP : AC = {
 var m : (block, block) map
 var s : block set
 var bad : bool
 fun init() : unit ={
  m = Map.empty;
  s = FSet.empty;
  bad = false;
 }
 fun f (x : block) : block ={
  var y : block;
  if (!in_dom x m /\ card s < q) {
   y = $uniform;
   if (mem y s) {
    bad = true;
    y = $uniform \ s;
   }
   s = add y s;
   m.[x] = y;
  }
  return proj (m.[x]);
 }
}.

module PRF : AC = {
 var m : (block, block) map
 var s : block set
 fun init() : unit ={
  m = Map.empty;
  s = FSet.empty;
 }
 fun f (x : block) : block = {
  var y : block;
  if (!in_dom x m /\ card s < q) {
   y = $uniform;
   m.[x] = y;
   s = add y s; 
  }
  return proj(m.[x]);
 }
}.

module type Adv(M : AAC) =
{
 fun a() : bool
}.


module M(C : AC, A_ : Adv) ={
 module A = A_(C)
 fun main() : bool = {
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
 fun.
 call (_ : PRP.bad,
           PRF.m{1} = PRP.m{2} /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) <= q, 
           card (PRP.s{2}) <= q).
 by intros M0 Hmo; apply (losslessA M0) => //.
 fun.
 if;first by smt.
 seq 1 1: 
 ((! PRP.bad{2} /\ ={x,y} /\ PRF.m{1} = PRP.m{2}) /\ ! in_dom x{1} PRF.m{1} /\
    card PRF.s{1} < q /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) < q).
 by rnd;skip => //.
 if{2}.
 by wp;rnd{2};wp;skip;progress;smt.
 by wp;skip;progress;smt.
 by skip;smt.
 intros &m2 H;fun;if;wp.
 rnd Fun.cpTrue.
 wp;skip;progress;by smt.
 skip;by smt.
 intros &m1;fun;if;wp.
 seq 1: ((PRP.bad /\ true) /\ ! in_dom x PRP.m /\ card PRP.s < q);last by smt.
 trivial.
 rnd Fun.cpTrue; skip;by smt.
 if;[rnd Fun.cpTrue;wp|];skip;by smt.
 by hoare;rnd;skip => //.
 by skip => //.
 inline PRF.init PRP.init;wp;skip;by smt.
save.

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
 equiv_deno(eq1) => // ;first by smt.
 rewrite Pr mu_or;by smt.
save.

(* assumed property *)
axiom sum_prop :
forall (n : int),
0 <= n =>
int_sum (lambda (x : int), x%r * (1%r / (2 ^ l)%r)) (intval 0 (n - 1)) <=
n%r * (n - 1)%r * (1%r / (2 ^ l)%r).


lemma prob2 : forall &m, 
Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q] <= 
q%r * (q-1)%r * (1%r / (2^l)%r).
proof.
 intros => &m.
 fel 1 (card PRP.s) (lambda x, (x%r)* (1%r/(2^l)%r)) 
     q PRP.bad [PRP.f : (! in_dom x PRP.m /\ card PRP.s < q)] => //. 
  apply sum_prop;by smt.
  inline PRP.init;wp;skip;by smt.
  fun;if;wp.
  seq 1 : (mem y PRP.s) 
          ((card PRP.s)%r * (1%r / (2^l)%r)) (1%r) 
          (1%r - ((card PRP.s)%r * (1%r / (2^l)%r))) (0%r)
          (!PRP.bad /\ ! in_dom x PRP.m /\ card PRP.s < q) => //. 
   by rnd => //.
   rnd  (cpMem PRP.s);skip;progress;last trivial.
   delta uniform Block.length;rewrite Block.Dword.mu_cpMemw.
   delta Block.length; by smt.

   hoare;if;[rnd;wp |];skip;by smt.
   (conseq (_ : _ : 0%r); last hoare=> //); intros=> _ _;
     (cut H: forall x y, 0%r <= x => 0%r < y => 0%r <= x * y; first smt);
     apply H; smt.
   intros c;fun;if;last by skip;smt.
 
   wp;seq 1: ((! in_dom x PRP.m /\ card PRP.s < q) /\ c = card PRP.s /\
  ! in_dom x PRP.m /\ card PRP.s < q /\ in_supp y uniform); first by rnd.
   if;[rnd;wp|];skip;progress;by smt.
         
  intros b c;fun;wp;if;last by skip;smt.
  seq 1:  ((! (! in_dom x PRP.m /\ card PRP.s < q) /\ PRP.bad = b /\ 
          card PRP.s = c) /\ ! in_dom x PRP.m /\ card PRP.s < q /\ 
          in_supp y uniform);first rnd;skip;by smt.
  if;[wp;rnd|];wp;skip;by smt.
save.


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
save.

end section.


