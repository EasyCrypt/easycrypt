require import Map.
require import Set.
require import Int.
require import Distr.
require import Bool.
require import Real.
require import Pair.
require import Word.
require import Array.

(** begin bitstrings *)
const k : int. 
const l : int. 
const n : int. 

axiom k_pos : 0 <= k.
axiom l_pos : 0 <= l.

axiom sizes : k + l = n.

clone import Word as Plaintext with op length = k.
clone import Word as Ciphertext with op length = n.
clone import Word as Randomness with op length = l.

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
  s = Set.empty;
 }
 fun o(x:randomness) : plaintext = {
  var y : plaintext;
  y = $uniform_plain;
  if (!in_dom x m) m.[x] = y;
  return proj (m.[x]);
 }
 fun o_a(x : randomness) : plaintext ={
  var y : plaintext;
  if (Set.card s < qO) {
   s = Set.add x s;
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

op f : pkey -> randomness -> randomness.
op finv : skey -> randomness -> randomness.


axiom finvof : forall(pk : pkey, sk : skey, x : randomness),
 in_supp (pk,sk) keypairs => finv sk (f pk x) = x.

axiom fofinv : forall(pk : pkey, sk : skey, x : randomness),
 in_supp (pk,sk) keypairs => f pk (finv sk x) = x.

axiom keypair_lossless : mu keypairs cpTrue = 1%r.

module type Inverter = {
 fun i(pk : pkey, y : randomness) : randomness
}.

module OW(I :Inverter) ={
 fun main() : bool ={
 var x : randomness;
 var x' : randomness;
 var y : randomness;
 var pk : pkey;
 var sk : skey;
  x = $uniform_rand;
  (pk,sk) = $keypairs;
  x'  = I.i(pk,(f pk x));
  return (x = x');
 }
}.
(** end one_way *)

(** begin scheme *)
 module type Scheme(R : Oracle) = {
  fun kg() : (pkey * skey)
  fun enc(pk:pkey, m:plaintext) : ciphertext
  fun dec(sk:skey, c:ciphertext) : plaintext
 }.
(** end scheme *) 

(** begin br93 *)
op (||) (x : randomness, y : plaintext) : ciphertext =
 Ciphertext.from_array ((to_array x) || (to_array y)).

op projRand(c : ciphertext) : randomness =
 Randomness.from_array (sub (to_array c) 0 l).

op projPlain(c : ciphertext) : plaintext =
 Plaintext.from_array (sub (to_array c) l k).

lemma projRand_eq : forall (c : ciphertext, i : int),
 0 <= i => i < l => (projRand c).[i] = c.[i].
proof.
 intros c i Hgz Hlel.
 delta;simplify;smt.
qed.
lemma projPlain_eq : forall (c : ciphertext, i : int),
 0 <= i => i < k => (projPlain c).[i] = c.[l + i].
proof.
 intros c i Hgz Hlel.
 delta;simplify;smt.
qed.
lemma projRand_c : forall (r : randomness,p : plaintext),
projRand((r || p)) = r by [].

lemma projPlain_c : forall (r : randomness,p : plaintext),
projPlain((r || p)) = p by [].

lemma proj_merge : forall(c : ciphertext),
(projRand c || projPlain c) = c.
proof.
intros c.
apply Ciphertext.extensionality.
delta Ciphertext.(==)(||);simplify.
intros i Hpos Hle.
rewrite (Ciphertext.from_array_get
     (Array.(||) (to_array (projRand c)) (Plaintext.to_array (projPlain c))) i _ _ _);try smt.
elim (append_get<:bool> (to_array (projRand c)) 
          (Plaintext.to_array (projPlain c)) i).
intros H1 H2.
case (i < l);intros H3;first smt.
rewrite H2; smt.
qed.

module Rnd ={
   var r : randomness
}.
 
module BR(R : Oracle) : Scheme(R)= {
 fun kg() : (pkey * skey) = {
  var (pk, sk) :pkey * skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  Rnd.r = $uniform_rand; 
  h  = R.o(Rnd.r);
  return (f pk Rnd.r ||   m ^^ h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return (projPlain c ^^ h);
 }
}.
(** end br93 *)
module Correct (S : Scheme) ={
 module SE = S(RO)
 fun main() : bool ={
  var pk : pkey;
  var sk : skey;
  var m : plaintext;
  var m' : plaintext;
  var c : ciphertext;
  (pk,sk) = $keypairs;
  m = $uniform_plain;
  c = SE.enc(pk,m);
  m' = SE.dec(sk,c);
  return (m = m');
 }
}.

lemma BR_correct : 
hoare [Correct(BR).main : true ==> res = true].
proof.
 fun.
 inline Correct(BR).SE.dec Correct(BR).SE.enc RO.o.
 do 4! (wp;rnd);rnd;skip;progress;[ | |smt|smt].
  rewrite (projPlain_c (f x1 r) 
 (Plaintext.(^^) m (proj (Map.__get (Map.__set RO.m{hr} r y) r)))).
 rewrite (projRand_c (f x1 r) 
 (Plaintext.(^^) m (proj (Map.__get (Map.__set RO.m{hr} r y) r))));smt.
 rewrite (projRand_c (f x1 r) 
 (Plaintext.(^^) m (proj (Map.__get (Map.__set RO.m{hr} r y) r))));smt.
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

(** begin br2 *)
 module BR2(R : Oracle) : Scheme(R)= {
  fun kg() : (pkey * skey) = {
   var (pk, sk) :pkey * skey;
   (pk,sk) = $keypairs;
   return (pk,sk);
  }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  Rnd.r = $uniform_rand; 
  h  = $uniform_plain;
  return (f pk Rnd.r ||   m ^^ h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return (projPlain c ^^ h);
 }
}.
(** end br2 *)

(* We can prove that the encryption, when called with equal parameters and *)
(* operating in a state where the map of the random oracle is the same,    *)
(* produce the same results and maps that only differ on r, in case the    *)
(* query of r to h is fresh                                                *)

(** begin eq1enc *)
equiv eq1_enc : 
BR(RO).enc ~ BR2(RO).enc : 
={pk,m,RO.m} ==> 
!in_dom Rnd.r{2} RO.m{2} => 
       (={res,Rnd.r} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2})
by (fun;inline RO.o;do 2!(wp;rnd);skip;smt).
(** end eq1enc *)


(** begin eq1 *)
lemma eq1 : forall (A <: Adv {RO,Rnd}), 
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
equiv [ CPA(BR,A).main ~ CPA(BR2,A).main : 
(glob A){1} = (glob A){2} ==> !mem Rnd.r{2} RO.s{2} => ={res}].
proof.
intros A Hll1 Hll2;fun.
call
((!mem Rnd.r RO.s){2} => 
       (={RO.s,c} /\  eq_except RO.m{1} RO.m{2} Rnd.r{2}
                  /\ (glob A){1} = (glob A){2}))
      ((!mem Rnd.r RO.s){2} => ={res}).
fun (mem Rnd.r RO.s) 
    (={RO.s} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2});[smt|smt|assumption| | |].
fun;inline RO.o;if;[smt | wp;rnd | ];wp;skip;progress;smt.
intros &m2 H;fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)| ];
                                     wp;skip;progress;smt.
intros &m1;fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)| ];
                                     wp;skip;progress;smt.
call 
(={pk,m,RO.m}) 
(!in_dom Rnd.r{2} RO.m{2} => 
      (={res,Rnd.r} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2})).
apply eq1_enc.
rnd.
call (={RO.m,RO.s,pk} /\ (glob A){1} = (glob A){2} 
                      /\ dom RO.m{2} = RO.s{2})
     (={RO.m,RO.s,res} /\ (glob A){1} = (glob A){2} 
                      /\ dom RO.m{2} = RO.s{2}).
fun (={RO.m,RO.s} /\ dom RO.m{2} = RO.s{2});[smt | smt | ].
fun;inline RO.o;if;[smt | wp;rnd | ];wp;skip;progress;smt.
inline CPA(BR,A).SO.kg RO.init CPA(BR2,A).SO.kg;wp;rnd;wp;skip;progress;smt.
qed.
(** end eq1 *)


lemma real_le_trans : forall(a, b, c : real),  
 Real.(<=) a b => Real.(<=) b  c => a <= c by [].

(** begin prob1 *)
lemma prob1_1 :
 forall (A <: Adv {Rnd,RO}),
(forall (O <: ARO), islossless O.o_a => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o_a => islossless A(O).a2) =>
 forall &m , Pr[CPA(BR,A).main() @ &m: res] <=
             Pr[CPA(BR2,A).main() @ &m : res] +
             Pr[CPA(BR2,A).main() @ &m : mem Rnd.r RO.s].
proof.
 intros A Hlossless1 Hlossless2 &m.
 apply (real_le_trans _  
        Pr[CPA(BR2,A).main() @ &m : res \/ mem Rnd.r RO.s] _).
 equiv_deno (_ : (glob A){1} = (glob A){2} ==>
 !(mem Rnd.r RO.s){2} => res{1} = res{2});
   [ apply (eq1(A) _ _);try assumption| |];smt.
 cut H:
 (Pr[CPA(BR2,A).main() @ &m : res \/ mem Rnd.r RO.s] =
  Pr[CPA(BR2,A).main() @ &m : res] +  Pr[CPA(BR2,A).main() @ &m : mem Rnd.r RO.s] -
  Pr[CPA(BR2,A).main() @ &m : res /\ mem Rnd.r RO.s]);[pr_or|];smt.
qed.
(** end prob1 *)

(** begin br3 *)
 module BR3(R : Oracle) : Scheme(R)= {
  fun kg() : (pkey * skey) = {
   var (pk, sk) :pkey * skey;
   (pk,sk) = $keypairs;
   return (pk,sk);
  }

 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  Rnd.r = $uniform_rand; 
  h  = $uniform_plain;
  return (f pk Rnd.r ||  h);
 }
 
 fun dec(sk:skey, c : ciphertext) : plaintext = {
  var h : plaintext;
  h = R.o(finv sk (projRand c));
  return (projPlain c ^^ h);
 }
}.
(** end br3 *)

(** begin eq2enc *)
equiv eq2_enc : 
BR2(RO).enc ~ BR3(RO).enc : 
={pk,m,RO.m} ==> 
={res,Rnd.r,RO.m}.
proof.
  fun.
  rnd (lambda v, m{2} ^^ v)(lambda v, m{2} ^^ v).
  rnd.
  skip;progress;smt.
qed.
(** end eq2enc *)


(** begin eq2 *)
lemma eq2 : forall (A <: Adv {RO,Rnd}), 
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
equiv [ CPA(BR2,A).main ~ CPA(BR3,A).main : 
(glob A){1} = (glob A){2} ==>  ={res,Rnd.r,RO.s}].
proof.
intros A Hll1 Hll2;fun.
call (={Rnd.r,RO.s,RO.m,c} /\ (glob A){1} = (glob A){2}) 
     (={Rnd.r,RO.s,RO.m,res} /\ (glob A){1} = (glob A){2}).
fun (={Rnd.r,RO.s,RO.m});[smt|smt|].
fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
call (={pk,m,RO.m}) (={res,Rnd.r,RO.m}).
apply eq2_enc.
rnd.
call (={RO.s,RO.m,pk} /\ (glob A){1} = (glob A){2}) 
     (={RO.s,RO.m,res} /\ (glob A){1} = (glob A){2}).
fun (={RO.s,RO.m});[smt|smt|].
fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
inline RO.init CPA(BR2,A).SO.kg CPA(BR3,A).SO.kg.
wp;rnd;wp;skip;progress.
qed.
(** end eq2 *)


(** begin prob2 *)
lemma prob2 : forall (A <: Adv {RO,Rnd}) &m,
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
Pr[CPA(BR2,A).main() @ &m : res] + Pr[CPA(BR2,A).main() @ &m : mem Rnd.r RO.s] = 
Pr[CPA(BR3,A).main() @ &m : res] + Pr[CPA(BR3,A).main() @ &m : mem Rnd.r RO.s].
proof.
 intros => A &m H1 H2.
cut H: (Pr[CPA(BR2,A).main() @ &m : res] = Pr[CPA(BR3,A).main() @ &m : res] /\
(Pr[CPA(BR2,A).main() @ &m : mem Rnd.r RO.s] = 
Pr[CPA(BR3,A).main() @ &m : mem Rnd.r RO.s])).

split;
 (equiv_deno (_ : (glob A){1} = (glob A){2} ==> ={res,Rnd.r,RO.s});
  [apply (eq2 A);assumption|trivial| smt]).
elim H => Heq1 Heq2;rewrite Heq1 Heq2 //.
save.
(** end prob2 *)

 
(** begin cpa2 *)
module CPA2 (S : Scheme, A_: Adv) ={
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
lemma eq3 : forall (A <: Adv {RO,Rnd}), 
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
equiv [ CPA(BR3,A).main ~ CPA2(BR3,A).main : 
(glob A){1} = (glob A){2} ==>  ={res,Rnd.r,RO.s}].
proof.
 intros => A Hloss1 Hloss2.
 fun.
 swap{2} -2. 
 call (={Rnd.r,RO.s,RO.m,c} /\ (glob A){1} = (glob A){2})
      (={Rnd.r,RO.s,RO.m,res} /\ (glob A){1} = (glob A){2}).
 fun (={Rnd.r,RO.s,RO.m});[smt|smt|].
 fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
 inline CPA(BR3,A).SO.enc CPA2(BR3,A).SO.enc.
 do 3! (wp;rnd).
 call (={RO.s,RO.m,pk} /\ (glob A){1} = (glob A){2})
      (={RO.s,RO.m,res} /\ (glob A){1} = (glob A){2}).
 fun (={RO.s,RO.m});[smt|smt|].
 fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
 inline RO.init CPA(BR3,A).SO.kg CPA2(BR3,A).SO.kg.
 wp;rnd;wp;skip;progress.      
qed.
(** end eq3 *)

(** begin prob3 *)
lemma prob3 : 
 forall (A <: Adv {RO,Rnd}) &m,
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
Pr[CPA(BR3,A).main() @ &m : res] + Pr[CPA(BR3,A).main() @ &m : mem Rnd.r RO.s] =
1%r/2%r + Pr[CPA2(BR3,A).main() @ &m : mem Rnd.r RO.s].
proof.
 intros => A &m H1 H2.
 cut H:
 (Pr[CPA(BR3,A).main() @ &m : res] = Pr[CPA2(BR3,A).main() @ &m : res] /\
 (Pr[CPA(BR3,A).main() @ &m : mem Rnd.r RO.s] = 
 Pr[CPA2(BR3,A).main() @ &m : mem Rnd.r RO.s])).
 split;
 (equiv_deno (_ : (glob A){1} = (glob A){2} ==> ={res,Rnd.r,RO.s});
  [apply (eq3 A);assumption|trivial| smt]).
  elim H => Heq1 Heq2;rewrite Heq1 Heq2 //.
 cut Hleq:  (Pr[CPA2(BR3,A).main() @ &m : res] = 1%r/2%r).
 cut Hbd : (bd_hoare[CPA2(BR3,A).main : true ==> res] = (1%r / 2%r)).
 fun; rnd (1%r / 2%r) (lambda b, b = b'); simplify.
 call (true) (true).
 fun (true);[smt|smt|assumption|].
 fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)|];wp;skip;smt.
 inline CPA2(BR3,A).SO.enc;do 2! (wp;rnd 1%r (cpTrue));wp.
 call (true) (true).
 fun (true);[smt|smt|assumption|].
 fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)|];wp;skip;smt.
 inline CPA2(BR3,A).SO.kg RO.init.
 wp;rnd 1%r (cpTrue);wp;skip;progress;[smt|smt|smt|].
 rewrite Dbool.mu_def.
 case (result);delta charfun;simplify;smt.
 bdhoare_deno Hbd; smt.
 rewrite Hleq //.
save.
(** end eq3 *)

(** begin prob2 *)
lemma prob2 : forall (A <: Adv {RO,Rnd}) &m,
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
Pr[CPA(BR2,A).main() @ &m : res] = Pr[CPA(BR3,A).main() @ &m : res] /\
(Pr[CPA(BR2,A).main() @ &m : mem Rnd.r RO.s] = 
Pr[CPA(BR3,A).main() @ &m : mem Rnd.r RO.s]).
proof.
 intros => A &m H1 H2.
split;
 (equiv_deno (_ : (glob A){1} = (glob A){2} ==> ={res,Rnd.r,RO.s});
  [apply (eq2 A);assumption|trivial| smt]).
save.





(** begin conclusion *)
lemma Conclusion :
forall (A <: Adv {Rnd, RO}) &m,
(forall (O <: ARO),  islossless O.o_a => islossless A(O).a1) =>
(forall (O <: ARO),  islossless O.o_a => islossless A(O).a2) =>
 exists (I<:Inverter), 
Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
Pr[OW(I).main() @ &m : res].
(** end conclusion *)