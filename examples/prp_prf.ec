require import Int.
require import Word.
require import FSet.
require import Map.
require import Real.
require import Distr.
require import Sum.

const l : int. (* block size *)
const q : int. (* maximum number of queries made by the adversary *)

axiom q_pos : 0 <= q.
axiom Leq : q < 2 ^ l.


clone Word as Block with op length = l.
(* clone Monoid as Mint with type t = int. *)


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

lemma eq1 : 
forall (A <: Adv{PRP,PRF}), 
 (forall (M0 <: AAC), islossless M0.f => islossless A(M0).a) =>
 equiv [ M(PRF,A).main ~ M(PRP,A).main : ={glob A} ==>card (PRP.s{2}) <= q /\ (!PRP.bad{2} => ={res})].
proof.
 intros A Hll.
 fun.
 call (_ : PRP.bad,
           PRF.m{1} = PRP.m{2} /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) <= q, 
           card (PRP.s{2}) <= q). 
 fun.
 if;first by smt.
 seq 1 1: 
 ((! PRP.bad{2} /\ ={x,y} /\ PRF.m{1} = PRP.m{2}) /\ ! in_dom x{1} PRF.m{1} /\
    card PRF.s{1} < q /\ PRF.s{1} = PRP.s{2} /\ card (PRP.s{2}) < q).
 rnd;skip;trivial.
 if{2}.
 wp;rnd{2};wp;skip;progress;by smt.
 wp;skip;progress;by smt.
 skip;by smt.
 intros &m2 H.
 fun;if;wp.
 rnd 1%r Fun.cpTrue.
 wp;skip;progress;by smt.
 skip;by smt.
 intros &m1;fun;if;wp.
 seq 1: ((PRP.bad /\ true) /\ ! in_dom x PRP.m /\ card PRP.s < q).
 rnd 1%r Fun.cpTrue; skip;by smt.
 if;[rnd 1%r Fun.cpTrue;wp|];skip;by smt.
 skip;by smt.
 inline PRF.init PRP.init;wp;skip;by smt.
save.

lemma real_le_trans : forall(a b c : real),  
  a <= b => b <= c => a <= c by []. 

lemma prob1 : 
forall (A <: Adv{PRP,PRF}) &m, 
 (forall (M0 <: AAC), islossless M0.f => islossless A(M0).a) =>
 Pr[ M(PRF,A).main() @ &m : res] <= 
 Pr[ M(PRP,A).main() @ &m : res] + 
 Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q].
proof.
 intros A &m Hll.
 apply (real_le_trans _ 
 Pr[ M(PRP,A).main() @ &m : (res || (PRP.bad /\  card PRP.s <= q))] _ _ _).
 equiv_deno(eq1 A _);try assumption;trivial;first by smt.
 rewrite Pr mu_or;by smt.
save.


lemma prob2 :
forall (A <: Adv{PRP,PRF}) &m, 
 (forall (M0 <: AAC), islossless M0.f => islossless A(M0).a) =>
Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q] <= 
q%r * (q-1)%r * (1%r / (2^l)%r).
proof.
 intros A &m Hll.
 fel 1 (card PRP.s) (lambda x, (x%r)* (1%r/(2^l)%r)) 
     q PRP.bad [PRP.f : (! in_dom x PRP.m /\ card PRP.s < q)].
 admit. (* need sum properties *)
 by trivial.
 inline PRP.init;wp;skip;by smt.
 fun;if;wp.
 seq 1 : (mem y PRP.s) 
         (!PRP.bad /\ ! in_dom x PRP.m /\ card PRP.s < q) 
         ((card PRP.s)%r * (1%r / (2^l)%r)) (1%r) 
         (1%r - ((card PRP.s)%r * (1%r / (2^l)%r))) (0%r). 
  rnd;skip;by trivial.
  rnd  ((card PRP.s)%r * (1%r / (2^l)%r)) (cpMem PRP.s).
  skip;progress;last trivial.
  delta uniform Block.length;rewrite Block.Dword.mu_cpMemw.
  delta Block.length; by smt.
  if;last by exfalso;smt.
  rnd 1%r (Fun.cpTrue);wp;skip;progress;by smt.
  rnd (1%r - (card PRP.s)%r * (1%r / (2^l)%r)) (cpNot (cpMem PRP.s)).
  skip;progress;last by smt.
  rewrite mu_not.
  cut ->: mu uniform cpTrue = weight uniform;first by smt.
  delta uniform;rewrite Block.Dword.lossless.
  rewrite Block.Dword.mu_cpMemw;delta Block.length;by smt.
  if;first exfalso;by smt.
  bd_hoare;skip;by smt.
  by smt.
  conseq_bd 0%r;first by smt.
  bd_hoare;skip;by trivial.
  intros c;fun;if;last by skip;smt.
  wp;seq 1: ((! in_dom x PRP.m /\ card PRP.s < q) /\ c = card PRP.s /\
  ! in_dom x PRP.m /\ card PRP.s < q /\ in_supp y uniform).
  rnd;skip;by smt.
  if;[rnd;wp|];skip;progress;by smt.
         
  intros b c;fun;wp;if;last by skip;smt.
  seq 1:  ((! (! in_dom x PRP.m /\ card PRP.s < q) /\ PRP.bad = b /\ 
          card PRP.s = c) /\ ! in_dom x PRP.m /\ card PRP.s < q /\ 
          in_supp y uniform);first rnd;skip;by smt.
  if;[wp;rnd|];wp;skip;by smt.
save.


lemma concl : forall (A <: Adv{PRP,PRF}) &m, 
 (forall (M0 <: AAC), islossless M0.f => islossless A(M0).a) =>
 Pr[ M(PRF,A).main() @ &m : res] <= 
 Pr[ M(PRP,A).main() @ &m : res] + q%r * (q-1)%r * (1%r / (2^l)%r).
proof.
 intros A &m Hll.
 apply (real_le_trans _  
 (Pr[ M(PRP,A).main() @ &m : res] + 
 Pr[ M(PRP,A).main() @ &m : PRP.bad /\ card PRP.s <= q]) _).
 apply (prob1 A &m);first by assumption.
 cut H: Pr[M(PRP, A).main() @ &m : PRP.bad /\ card PRP.s <= q] <= 
        q%r * (q - 1)%r * (1%r / (2 ^ l)%r).
 apply (prob2 A &m);first by assumption.
 by smt.
save.
