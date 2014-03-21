require import Map.
require import FSet.
require import Int.
require import Distr.
require import Bool.
require import Real.
require import Pair.
require import AWord.
require import Array.

(** begin bitstrings *)
const k : int. 
const l : int. 
const n : int. 

axiom k_pos : 0 <= k.
axiom l_pos : 0 <= l.

axiom sizes : k + l = n.

clone import AWord as Plaintext with op length = k.
clone import AWord as Ciphertext with op length = n.
clone import AWord as Randomness with op length = l.

type plaintext = Plaintext.word.
type ciphertext = Ciphertext.word.
type randomness = Randomness.word.
(** end bitstrings *)


(** begin distributions *)
op uniform_rand : randomness distr = Randomness.Dword.dword.
op uniform_plain : plaintext distr = Plaintext.Dword.dword.
(** end distributions *)

(** begin random_oracles *)
module type Oracle =
{
  fun init():unit
  fun o(x:randomness):plaintext
}.

module type ARO = {fun o_a (x : randomness) : plaintext}. 

const qO : int.

module RO:Oracle,ARO = {
 var m : (randomness, plaintext) map
 var s : randomness set
 fun init() : unit = {
  m = Map.empty;
  s = FSet.empty;
 }
 fun o(x:randomness) : plaintext = {
  var y : plaintext;
  y = $uniform_plain;
  if (!in_dom x m) m.[x] = y;
  return proj (m.[x]);
 }
 fun o_a(x : randomness) : plaintext ={
  var y : plaintext;
  if (FSet.card s < qO) {
   s = FSet.add x s;
   y =o(x);
  } else {y = Plaintext.zeros;}
  return y;
 }
}.
(** end random_oracles *)

(** begin one_way *)
type pkey.
type skey.
const keypairs: (pkey * skey) distr.

op valid_keys : pkey -> skey -> bool.

axiom valid_keys_def :
 forall (pk : pkey, sk: skey), in_supp (pk,sk) keypairs => valid_keys pk sk.

op f : pkey -> randomness -> randomness.
op finv : skey -> randomness -> randomness.


axiom finvof : forall(pk : pkey, sk : skey, x : randomness),
 valid_keys pk sk => finv sk (f pk x) = x.

axiom fofinv : forall(pk : pkey, sk : skey, x : randomness),
 valid_keys pk sk => f pk (finv sk x) = x.

axiom keypair_lossless : mu keypairs cpTrue = 1%r.

module type Inverter = {
 fun i(pk : pkey, y : randomness) : randomness
}.

module OW(I :Inverter) ={
 fun kg() : (pkey * skey) = {
  var pk : pkey;
  var sk : skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 fun main() : bool ={
   var x : randomness;
   var x' : randomness;
   var y : randomness;
   var pk : pkey;
   var sk : skey;
   (pk,sk) = kg();
   x = $uniform_rand;
   x'  = I.i(pk,(f pk x));
   return (x = x');
  }
}.
(** end one_way *)

(** begin scheme *)
 module type Scheme(R : Oracle) = {
  fun kg() : (pkey * skey)
  fun enc(pk:pkey, m:plaintext) : ciphertext
  fun dec(sk:skey, c:ciphertext) : plaintext option
 }.
(** end scheme *) 

op (||) (x : randomness, y : plaintext) : ciphertext =
 Ciphertext.from_bits ((to_bits x) || (to_bits y)).

op projRand(c : ciphertext) : randomness =
 Randomness.from_bits (sub (to_bits c) 0 l).

op projPlain(c : ciphertext) : plaintext =
 Plaintext.from_bits (sub (to_bits c) l k).

(*lemma projRand_eq : forall (c : ciphertext, i : int),
 0 <= i => i < l => (projRand c).[i] = c.[i].
proof.
 intros c i Hgz Hlel.
 delta;simplify;smt.
qed.
lemma projPlain_eq : forall (c : ciphertext, i : int),
 l <= i => i < k + l => (projPlain c).[i - l] = c.[i].
proof.
 intros c i Hgz Hlel;
 delta; simplify; smt.
qed.*)
lemma projRand_c : forall (r : randomness,p : plaintext),
projRand((r || p)) = r by [].

lemma projPlain_c : forall (r : randomness,p : plaintext),
projPlain((r || p)) = p by [].

lemma proj_merge : forall(c : ciphertext),
(projRand c || projPlain c) = c.
proof.
intros=> c; rewrite /((||) (projRand c) (projPlain c)).
rewrite /projRand Randomness.pcan_to_from; first by smt.
rewrite /projPlain Plaintext.pcan_to_from; first by smt.
rewrite app_sub ?Ciphertext.can_from_to //;
last 3 by smt.
qed.
  
(** begin br93 *)
module BR(R : Oracle) : Scheme(R)= {
 var r : randomness
 fun kg() : (pkey * skey) = {
  var (pk, sk) :pkey * skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  r = $uniform_rand; 
  h  = R.o(r);
  return (f pk r ||   m ^ h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext option = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return (Some (projPlain c ^ h));
 }
}.
(** end br93 *)
module Correct (S : Scheme) ={
 module SE = S(RO)
 fun main() : bool ={
  var pk : pkey;
  var sk : skey;
  var m : plaintext;
  var m' : plaintext option;
  var c : ciphertext;
  (pk,sk) = $keypairs;
  m = $uniform_plain;
  c = SE.enc(pk,m);
  m' = SE.dec(sk,c);
  return (m = proj m');
 }
}.

lemma BR_correct : 
hoare [Correct(BR).main : true ==> res = true].
proof.
 fun.
 inline Correct(BR).SE.dec Correct(BR).SE.enc RO.o.
 do 4! (wp;rnd);rnd;skip;progress.
  by generalize H5;rewrite !projPlain_c !projRand_c !(finvof x1 x2 r) //;smt.
  
  rewrite !projPlain_c !projRand_c !(finvof x1 x2 r);first by smt. 
  by rewrite -Plaintext.xorwA Plaintext.xorwK;smt.

  by generalize H5;rewrite !projPlain_c !projRand_c !(finvof x1 x2 r) //;smt.

  rewrite !projPlain_c !projRand_c !(finvof x1 x2 r);first by smt. 
  by rewrite -Plaintext.xorwA Plaintext.xorwK; smt.
qed.


(** begin cpa *)
module type Adv (R : ARO) = { 
 fun a1(pk : pkey) : plaintext * plaintext
 fun a2(c : ciphertext) : bool
}.

module CPA (S : Scheme, A_: Adv) ={
 module SO = S(RO)
 module A = A_(RO)
  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0 : plaintext;
  var m1 : plaintext;
  var c : ciphertext;
  var b : bool;
  var b' : bool;
  RO.init();
  (pk,sk)  = SO.kg();
  (m0,m1)  = A.a1(pk);
  b = ${0,1};
  c  = SO.enc(pk,b?m0:m1);
  b' = A.a2(c);
  return b = b';
 }
}.
(** end cpa *)

(* First step: replace the call to the hash oracle when computing the cipher  *)
(*             by a randomly sampled value. Intuitively, an adversary can only*)
(*             distinguish if he can manage to query the oracle witht r       *)       

section.

(** begin br2 *)

declare module A : Adv{BR,RO}.
axiom Hll1 : (forall (R<:ARO{A}), islossless R.o_a => islossless A(R).a1).
axiom Hll2 : (forall (R<:ARO{A}), islossless R.o_a => islossless A(R).a2).


local module BR2(R : Oracle) : Scheme(R)= {
 var r : randomness
 fun kg() : (pkey * skey) = {
   var (pk, sk) :pkey * skey;
   (pk,sk) = $keypairs;
   return (pk,sk);
  }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  r = $uniform_rand; 
  h  = $uniform_plain;
  return (f pk r ||   m ^ h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext option = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return Some (projPlain c ^ h);
 }
}.
(** end br2 *)

(* We can prove that the encryption, when called with equal parameters and *)
(* operating in a state where the map of the random oracle is the same,    *)
(* produce the same results and maps that only differ on r, in case the    *)
(* query of r to h is fresh                                                *)

(** begin eq1enc *)
local equiv eq1_enc : 
BR(RO).enc ~ BR2(RO).enc : 
={pk,m,RO.m} ==> 
!in_dom BR2.r{2} RO.m{2} => 
       (={res}/\  BR.r{1} = BR2.r{2} /\ eq_except RO.m{1} RO.m{2} BR2.r{2})
by (fun;inline RO.o;do 2!(wp;rnd);skip;progress;smt).
(** end eq1enc *)


(** begin eq1 *)
local equiv eq1 : 
CPA(BR,A).main ~ CPA(BR2,A).main : 
(glob A){1} = (glob A){2} ==> !mem BR2.r{2} RO.s{2} => ={res}.
proof.
fun.
call
( _ : (!mem BR2.r RO.s){2} => 
       (={RO.s,c} /\  eq_except RO.m{1} RO.m{2} BR2.r{2}
                  /\ (glob A){1} = (glob A){2})
      ==> (!mem BR2.r RO.s){2} => ={res}).
fun (mem BR2.r RO.s) 
    (={RO.s} /\ eq_except RO.m{1} RO.m{2} BR2.r{2});[smt|smt| | | |].
intros => R;apply (Hll2 R) => //.
fun;inline RO.o;if;[smt | wp;rnd | ];wp;skip;progress;smt.
intros &m2 H;fun;if;[inline RO.o;wp;rnd;try (wp;skip=> //);smt|wp;skip=> //].
intros &m1;fun;if;[inline RO.o;wp;rnd;try (wp;skip=> //);smt|wp;skip=> //].
call eq1_enc.
rnd.
call (_ : ={RO.m,RO.s,pk} /\ (glob A){1} = (glob A){2} 
                      /\ (forall x, in_dom x RO.m{2} = mem x RO.s{2}) ==>
     ={RO.m,RO.s,res} /\ (glob A){1} = (glob A){2} 
                      /\ (forall x, in_dom x RO.m{2} = mem x RO.s{2})).
fun (={RO.m,RO.s} /\ (forall x, in_dom x RO.m{2} = mem x RO.s{2}));[smt | smt | ].
fun;inline RO.o;if;[smt | wp;rnd | ];wp;skip;progress=> //=.
  by rewrite mem_add in_dom_set H.
  by rewrite mem_add -H; case (x1 = x{2})=> // -> /=; rewrite rw_eqT.
inline CPA(BR,A).SO.kg RO.init CPA(BR2,A).SO.kg;wp;rnd;wp;skip;progress;smt.
qed.
(** end eq1 *)


lemma real_le_trans : forall(a, b, c : real),  
 Real.(<=) a b => Real.(<=) b  c => a <= c by [].

(** begin prob1 *)
local lemma prob1 :
 forall &m , Pr[CPA(BR,A).main() @ &m: res] <=
             Pr[CPA(BR2,A).main() @ &m : res] +
             Pr[CPA(BR2,A).main() @ &m : mem BR2.r RO.s].
proof.
 intros &m.
 apply (real_le_trans _  
        Pr[CPA(BR2,A).main() @ &m : res \/ mem BR2.r RO.s] _).
 equiv_deno (_ : (glob A){1} = (glob A){2} ==>
 !(mem BR2.r RO.s){2} => res{1} = res{2});
   [ apply (eq1 );try assumption| |];smt.
 cut H:
 (Pr[CPA(BR2,A).main() @ &m : res \/ mem BR2.r RO.s] =
  Pr[CPA(BR2,A).main() @ &m : res] +  Pr[CPA(BR2,A).main() @ &m : mem BR2.r RO.s] -
  Pr[CPA(BR2,A).main() @ &m : res /\ mem BR2.r RO.s]);[rewrite Pr mu_or|];smt.
qed.
(** end prob1 *)

(** begin br3 *)
local module BR3(R : Oracle) : Scheme(R)= {
 var r : randomness 
 fun kg() : (pkey * skey) = {
   var (pk, sk) :pkey * skey;
   (pk,sk) = $keypairs;
   return (pk,sk);
  }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  r = $uniform_rand; 
  h  = $uniform_plain;
  return (f pk r ||  h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext option = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return Some (projPlain c ^ h);
 }
}.
(** end br3 *)

(** begin eq2enc *)
local equiv eq2_enc : 
BR2(RO).enc ~ BR3(RO).enc : 
={pk,m,RO.m} ==> 
={res,RO.m} /\ BR2.r{1} = BR3.r{2}.
proof.
  fun.
  rnd (lambda v, m{2} ^ v); rnd.
  by skip;progress => //;rewrite ?Plaintext.xor_assoc;smt.
qed.
(** end eq2enc *)


(** begin eq2 *)
local equiv eq2 : CPA(BR2,A).main ~ CPA(BR3,A).main : 
(glob A){1} = (glob A){2} ==>  ={res,RO.s} /\ BR2.r{1} = BR3.r{2}.
proof.
 fun.
 seq 4 4: (={b,m0,m1,pk,sk,RO.s,RO.m,glob A}).
  by eqobs_in => //.
  by eqobs_in;call eq2_enc; skip; progress => //.
qed.
(** end eq2 *)


(** begin prob2 *)
local lemma prob2 : forall &m,
Pr[CPA(BR2,A).main() @ &m : res] + Pr[CPA(BR2,A).main() @ &m : mem BR2.r RO.s] = 
Pr[CPA(BR3,A).main() @ &m : res] + Pr[CPA(BR3,A).main() @ &m : mem BR3.r RO.s].
proof.
 intros => &m.
 by congr;
 equiv_deno (_ : ={glob A} ==> ={res,RO.s} /\ BR2.r{1} = BR3.r{2});
 (try  apply eq2 => //);smt.
qed.
(** end prob2 *)

 
(** begin cpa2 *)
local module CPA2 (S : Scheme, A_: Adv) ={
 module SO = S(RO)
 module A = A_(RO)
  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0 : plaintext;
  var m1 : plaintext;
  var c : ciphertext;
  var b : bool;
  var b' : bool;
  RO.init();
  (pk,sk)  = SO.kg();
  (m0,m1)  = A.a1(pk);
  c  = SO.enc(pk,m0);
  b' = A.a2(c);
  b = ${0,1};
  return b = b';
 }
}.
(** end cpa2 *)

(** begin eq3 *)
local equiv eq3 : CPA(BR3,A).main ~ CPA2(BR3,A).main : 
(glob A){1} = (glob A){2} ==>  ={res,BR3.r,RO.s}.
proof.
 fun; swap{2} -2; inline CPA(BR3,A).SO.enc CPA2(BR3,A).SO.enc; eqobs_in.
qed.
(** end eq3 *)

(** begin prob3 *)
local lemma prob3 : 
 forall &m,
Pr[CPA(BR3,A).main() @ &m : res] + Pr[CPA(BR3,A).main() @ &m : mem BR3.r RO.s] =
1%r/2%r + Pr[CPA2(BR3,A).main() @ &m : mem BR3.r RO.s].
proof.
 intros => &m.
 congr.
 by equiv_deno (_ : (glob A){1} = (glob A){2} ==> ={res,BR3.r,RO.s}) => //;
    apply eq3 => //;smt.
 cut ->: (Pr[CPA(BR3, A).main() @ &m : res] = 
          Pr[CPA2(BR3, A).main() @ &m : res]).
 by equiv_deno (_ : (glob A){1} = (glob A){2} ==> ={res,BR3.r,RO.s}) => //;
    apply eq3  => //;smt.
 cut Hbd : (bd_hoare[CPA2(BR3,A).main : true ==> res] = (1%r / 2%r)).
 fun; rnd (lambda b, b = b'); simplify.
 call (_ : true ==> true).
 fun (true);[smt|smt| |].
 by intros => R _;apply (Hll2 R) => //.
 by fun;if;[inline RO.o;wp;rnd (cpTrue)|];wp;skip;smt.
 inline CPA2(BR3,A).SO.enc;do 2! (wp;rnd (cpTrue));wp.
 call (_ : true ==> true).
 fun (true);[smt|smt| |].
 by intros => R _;apply (Hll1 R) => //.
 fun;if;[inline RO.o;wp;rnd (cpTrue)|];wp;skip;smt.
 inline CPA2(BR3,A).SO.kg RO.init.
 wp;rnd (cpTrue);wp;skip;progress;[smt|smt|smt|].
 rewrite Dbool.mu_def.
 case (result);delta charfun;simplify;smt.
 bdhoare_deno Hbd; smt.
qed.
(** end prob3 *)

(** begin inverter *)
module BR_OW(A_ : Adv) : Inverter = {
 module A = A_(RO)
  fun i(pk : pkey,y : randomness) : randomness ={
  var m0 : plaintext;
  var m1 : plaintext;
  var h : plaintext;
  var b : bool;
  var x : randomness;
  RO.init();
  (m0,m1)  = A.a1(pk);
  h = $uniform_plain; 
  b  = A.a2(y || h);
  x = Option.proj (Map.find (lambda p0 p1,f pk p0 = y) RO.m);
   return (x);
 }
}.
(** end inverter *)

(** begin finy *)
lemma f_iny :
forall (x, y : randomness, pk: pkey, sk : skey), 
in_supp (pk,sk) keypairs  =>
f pk x = f pk y => x = y.
proof.
 intros x y pk sk Hsupp Heqf.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite Heqf;smt.
qed.
(** end finy *)

lemma one_way_p_unique :
forall (pk : pkey, sk : skey, z x y : randomness), 
    in_supp (pk, sk) keypairs =>
    f pk x = f pk z => f pk y = f pk z => x = y.
proof.
 intros => pk sk z x y ? Heq1 Heq2.
 by apply (f_iny _ _ pk sk _ _) => //; rewrite Heq1 Heq2 //.
save.

(** begin eq4 *)

local equiv eq4 : CPA2(BR3,A).main ~ OW(BR_OW(A)).main : 
(glob A){1} = (glob A){2} ==>  (mem BR3.r RO.s){1} => res{2}.
proof.
 fun;inline BR_OW(A).i.
 rnd{1}.
 wp.
 call (_:  ={RO.s,RO.m} /\ 
      (forall (x : randomness), in_dom x RO.m{1} = mem x RO.s{1})).
 fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress=> //=.
   by rewrite mem_add in_dom_set H.
   by rewrite mem_add -H; case (x1 = x{2})=> //= -> //=; rewrite rw_eqT.
 inline CPA2(BR3,A).SO.enc;wp;rnd;swap{1} -5.
 wp.
 call (_:  ={RO.s,RO.m} /\ 
      (forall (x : randomness), in_dom x RO.m{1} = mem x RO.s{1})).
 fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress=> //=.
   by rewrite mem_add in_dom_set H.
   by rewrite mem_add -H; case (x1 = x{2})=> //= -> //=; rewrite rw_eqT.
 inline RO.init CPA2(BR3,A).SO.kg OW(BR_OW(A)).kg;swap {2} 3 -2;
 do 2!(wp;rnd);skip;progress=> //; first 2 smt.

 rewrite (find_in_p_unique 
      (lambda (p0:randomness) (p1:plaintext), f x1 p0 = f x1 rL) m_R0 rL _) => //=.
  by rewrite H11. 

  by intros => x y Heq1 Heq2;apply (one_way_p_unique x1 x2 rL) => //.
  by rewrite proj_some.
qed.
(** end eq4 *)

(** begin prob4 *)
local lemma prob4 : 
forall  &m,
Pr[ CPA2(BR3,A).main() @ &m : mem BR3.r RO.s] <= 
Pr[ OW(BR_OW(A)).main () @ &m : res].
proof.
 intros &m.
 equiv_deno (_ : ={glob A} ==>  (mem BR3.r RO.s){1} => res{2}) => //.
 by apply eq4 => //;smt.
qed. 
(** end prob4 *)


lemma Reduction :
forall &m,
 Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r  <= 
Pr[OW(BR_OW(A)).main() @ &m : res].
proof.
 intros &m.
 cut H: 
 (Pr[CPA(BR, A).main() @ &m : res] <= 1%r / 2%r +
  Pr[OW(BR_OW(A)).main() @ &m : res]).
   apply (real_le_trans _ 
   ( Pr[CPA(BR2,A).main() @ &m : res] +
             Pr[CPA(BR2,A).main() @ &m : mem BR2.r RO.s]) _ _ _).
 apply (prob1  &m);assumption.
 rewrite (prob2 &m ) (prob3 &m ).
 cut H1 : (Pr[CPA2(BR3, A).main() @ &m : mem BR3.r RO.s] <=
           Pr[OW(BR_OW(A)).main() @ &m : res]).
 apply (prob4 &m);assumption.
 by smt.
 by smt.
qed.

end section.

(** begin conclusion *)
lemma Security :
forall (A <: Adv {BR, RO}) &m,
(forall (O <: ARO{A}),  islossless O.o_a => islossless A(O).a1) =>
(forall (O <: ARO{A}),  islossless O.o_a => islossless A(O).a2) =>
 exists (I<:Inverter), 
Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
Pr[OW(I).main() @ &m : res].
proof.
 intros A &m Hll1 Hll2.
 exists (BR_OW(A)).
 by apply (Reduction A _ _ &m) => //.
qed.
(** end conclusion *)
