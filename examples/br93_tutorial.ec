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
axiom l_pos : 0 <= k.

axiom sizes : k + l = n.

clone Word as Plaintext with op length = k.
clone Word as Ciphertext with op length = n.
clone Word as Randomness with op length = l.

type plaintext = Plaintext.word.
type ciphertext = Ciphertext.word.
type randomness = Randomness.word.

import Plaintext.
import Ciphertext.
import Randomness.
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

(* begin scheme *)
 module type Scheme(R : Oracle) = {
 fun kg() : (pkey * skey)
  fun enc(pk:pkey, m:plaintext) : ciphertext
  fun dec(sk:skey, c:ciphertext) : plaintext
 }.
(* end scheme *) 

(* begin br93 *)
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
save.


lemma projPlain_eq : forall (c : ciphertext, i : int),
 0 <= i => i < k => (projPlain c).[i] = c.[l + i].
proof.
 intros c i Hgz Hlel.
 delta;simplify;smt.
save.

lemma projRand_c : forall (r : randomness,p : plaintext),
projRand((r || p)) = r by [].

lemma projPlain_c : forall (r : randomness,p : plaintext),
projPlain((r || p)) = p by [].

lemma proj_merge : forall(c : ciphertext),
(projRand c || projPlain c) = c.
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
rewrite (H2 _ _); smt.
save.


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
(* end br93 *)
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
save.


(* begin cpa *)
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
(* end cpa *)

(* First step: replace the call to the hash oracle when computing the cipher  *)
(*             by a randomly sampled value. Intuitively, an adversary can only*)
(*             distinguish if he can manage to query the oracle witht r       *)       
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

(* We can prove that the encryption, when called with equal parameters and *)
(* operating in a state where the map of the random oracle is the same,    *)
(* produce the same results and maps that only differ on r, in case the    *)
(* query of r to h is fresh                                                *)

equiv eq1_enc : 
BR(RO).enc ~ BR2(RO).enc : 
={pk,m,RO.m} ==> 
!in_dom Rnd.r{2} RO.m{2} => (={res} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2})
by (fun;inline RO.o;do 2!(wp;rnd);skip;progress;smt).

lemma eq1 : forall (A <: Adv {RO,Rnd}), 
(forall (R<:ARO), islossless R.o_a => islossless A(R).a1) =>
(forall (R<:ARO), islossless R.o_a => islossless A(R).a2) =>
equiv [ CPA(BR,A).main ~ CPA(BR2,A).main : 
(glob A){1} = (glob A){2} ==> !mem Rnd.r{2} RO.s{2} => ={res}].
intros A Hll1 Hll2;fun.
call
((!mem Rnd.r RO.s){2} => 
       (={RO.s,c} /\  eq_except RO.m{1} RO.m{2} Rnd.r{2} 
                     /\ (glob A){1} = (glob A){2}))
      ((!mem Rnd.r RO.s){2} => ={res}).
fun (mem Rnd.r RO.s) 
    (={RO.s} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2});[smt|smt| assumption | | |].

fun;inline RO.o;if;[smt | wp;rnd | ];wp;skip;progress;smt.

intros &m2 H;fun;if;[inline RO.o;wp;rnd 1%r (cPtrue)| ];wp;skip;progress;smt.

intros &m1;fun;if;[inline RO.o;wp;rnd 1%r (cPtrue)| ];wp;skip;progress;smt.

call 
(={pk,m,RO.m}) 
(!in_dom Rnd.r{2} RO.m{2} => (={res} /\ eq_except RO.m{1} RO.m{2} Rnd.r{2})).
apply eq1_enc.
rnd.






lemma Conclusion :
forall (A <: Adv {Rnd, RO}) &m :
(forall (O <: ARO),  islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO),  islossless O.o => islossless A(O).a2) =>
 exists (I<:Inverter), 
Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
Pr[OW(I).main() @ &m : res].
