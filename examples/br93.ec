require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
require import ISet.
require import Int.
require import Distr.
require import Bool.
require import Real.
require import Pair.
require import Word.


op k : int. (* size of message *)
op l : int. (* size of randmness *)
op n : int. (* size of cipher *)

axiom sizes : k + l = n.

op qH : int. (* bound on adversary calls to hash H *)

clone Word as Plaintext with op length = k.
clone Word as Ciphertext with op length = n.
clone Word as Randomness with op length = l.

type plaintext = Plaintext.word.
type ciphertext = Ciphertext.word.
type randomness = Randomness.word.

import Plaintext.
import Ciphertext.
import Randomness.

type pkey.
type skey.
op keypairs: (pkey * skey) distr.
op f : pkey -> randomness -> randomness.
op finv : skey -> randomness -> randomness.

axiom finvof : forall(pk : pkey, sk : skey, x : randomness),
 in_supp (pk,sk) keypairs => finv sk (f pk x) = x.

axiom fofinv : forall(pk : pkey, sk : skey, x : randomness),
 in_supp (pk,sk) keypairs => f pk (finv sk x) = x.

axiom keypair_lossless : mu keypairs cpTrue = 1%r.

op uniform : plaintext distr = Plaintext.Dword.dword.
op uniform_rand : randomness distr = Randomness.Dword.dword.

clone RandOrcl as RandOrcl_BR with 
type from = randomness, 
type to = plaintext,
op dsample = uniform,
op qO = qH,
op default = Plaintext.zeros.

import RandOrcl_BR.
import ROM.
import WRO_Set.

module type Scheme(RO : Oracle) = {
 fun kg() : (pkey * skey)
 fun enc(pk:pkey, m:plaintext): ciphertext 
}.

module type Adv(ARO : ARO)  = {
 fun a1 (p : pkey) : (plaintext * plaintext) {ARO.o} 
 fun a2 (c : ciphertext) : bool {ARO.o}
}.


module CPA(S : Scheme, A_ : Adv) = {
 module ARO = ARO(RO)
 module A = A_(ARO)
 module SO = S(RO)
  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0, m1 : plaintext;
  var c : ciphertext;
  var b,b' : bool;
  ARO.init();
  (pk,sk)  = SO.kg();
  (m0,m1)  = A.a1(pk);
  b = ${0,1}; 
  c  = SO.enc(pk,b?m0:m1);
  b' = A.a2(c);
  return b = b';
 } 
}.

op (||) (x : randomness, y : plaintext) : ciphertext =
 Ciphertext.from_array ((to_array x) || (to_array y)).


module M = {
 var r : randomness
}.

module BR(R : Oracle) : Scheme(R) = {
 fun kg():(pkey * skey) = {
  var (pk, sk): pkey * skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  M.r = $uniform_rand; 
  h  = R.o(M.r);
  return ((f pk M.r) ||   m ^^ h);
 }
}.


  (* Step 1: replace the hash call by a random value *)

module BR2(R : Oracle) : Scheme(R) = {
 fun kg():(pkey * skey) = {
  var (pk, sk): (pkey * skey);
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  M.r = $uniform_rand; 
  h = $uniform; 
  return ((f pk M.r) || h);
 }
}.

lemma eq1_enc :
 equiv [ BR(RO).enc ~ BR2(RO).enc : 
={pk,RO.m} ==>
!in_dom M.r{2} RO.m{2} => (={res} /\ eq_except RO.m{1} RO.m{2} M.r{2}) ].
proof.
 fun;inline RO.o.
 wp;rnd (lambda v, m{1} ^^ v)(lambda v,m{1} ^^ v).
 wp;rnd;skip;progress;smt.
save.

module CPA2(S : Scheme, A_ : Adv) = {
 module ARO = ARO(RO)
 module A = A_(ARO)
 module SO = S(RO)
  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0, m1 : plaintext;
  var c : ciphertext;
  var b,b' : bool;
  ARO.init();
  (pk,sk)  = SO.kg();
  (m0,m1)  = A.a1(pk);
  c  = SO.enc(pk,m0);
  b' = A.a2(c);
  b = ${0,1}; 
  return b = b';
 } 
}.


lemma eq1 : forall (A <: Adv {M,RO,ARO}), 
(forall (O <: ARO), islossless O.o =>  islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o =>  islossless A(O).a2) =>
 equiv [ CPA(BR,A).main ~ CPA2(BR2,A).main : 
(glob A){1} = (glob A){2} ==>
 (!mem M.r ARO.log){2} => ={res}].
proof.
 intros A HALossless1 HALossless2.
 fun.
swap{2} -2.
 call ((!mem M.r ARO.log){2} => 
       (={ARO.log,c} /\  eq_except RO.m{1} RO.m{2}  M.r{2} 
                     /\ (glob A){1} = (glob A){2}))
      ((!mem M.r ARO.log){2} => ={res}).
 fun (mem M.r ARO.log) 
     (={ARO.log} /\ eq_except RO.m{1} RO.m{2} M.r{2});
      [smt|smt|assumption| | |].
 fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
 intros &m H;fun;if;[inline RO.o;wp;rnd 1%r cpTrue|];wp;skip;progress;smt.
 intros &m;fun;if;[inline RO.o;wp;rnd 1%r cpTrue|];wp;skip;progress;smt.
 call (={pk,RO.m})
      (!in_dom M.r{2} RO.m{2} =>
       (={res} /\ eq_except RO.m{1} RO.m{2} M.r{2})).
 apply (eq1_enc).
 rnd.
 call (={p,ARO.log,RO.m} /\ (glob A){1} = (glob A){2} /\
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2}))
(={res,ARO.log,RO.m} /\ (glob A){1} = (glob A){2} /\
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2})).
 fun ( ={RO.m,ARO.log} /\
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2}));[smt|smt|].
  fun;if;[smt|inline RO.o;wp;rnd|];wp;skip;progress;smt.
  inline CPA(BR,A).SO.kg CPA2(BR2,A).SO.kg.
  inline CPA(BR,A).ARO.init CPA2(BR2,A).ARO.init RO.init;wp;rnd;wp;skip.
  progress;smt.
save.


lemma real_le_trans : forall(a, b, c : real),  
 Real.(<=) a b => Real.(<=) b  c => a <= c by [].


lemma prob1_1 : 
 forall (A <: Adv {M,RO,ARO}), 
(forall (O <: ARO), islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o => islossless A(O).a2) =>
 forall &m,Pr[CPA2(BR2,A).main()  @ &m : res] = 1%r / 2%r.
proof.
 intros A Hlossless1 Hlossless2.
 intros &m.
 cut H1 : (bd_hoare[CPA2(BR2,A).main : true ==> res] = (1%r / 2%r)).
 fun; rnd (1%r / 2%r) (lambda b, b = b'); simplify.
 call (true) (true).
 fun (true);[smt|smt|assumption|].
 fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)|];wp;skip;smt.
 inline CPA2(BR2,A).SO.enc;do 2! (wp;rnd 1%r (cpTrue));wp.
 call (true) (true).
 fun (true);[smt|smt|assumption|].
 fun;if;[inline RO.o;wp;rnd 1%r (cpTrue)|];wp;skip;smt.
 inline CPA2(BR2,A).SO.kg CPA2(BR2,A).ARO.init RO.init.
 wp;rnd 1%r (cpTrue);wp;skip;progress;[smt|smt|smt|].
 rewrite Dbool.mu_def.
 case (result);delta charfun;simplify;smt.
 bdhoare_deno H1; smt.
save.

lemma prob1_2 :
 forall (A <: Adv {M,RO,ARO}) &m,
(forall (O <: ARO), islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o => islossless A(O).a2) =>
Pr[CPA(BR,A).main() @ &m: res] <=
1%r/2%r + Pr[CPA2(BR2,A).main() @ &m : mem M.r ARO.log].
proof.
 intros A &m Hlossless1 Hlossless2.
 rewrite -(prob1_1 A _ _ &m);[assumption | assumption | ].
 apply (real_le_trans _ 
             Pr[CPA2(BR2,A).main() @ &m : res \/ mem M.r ARO.log] _).
 equiv_deno (_ : (glob A){1} = (glob A){2} ==>
 !(mem M.r ARO.log){2} => res{1} = res{2});
   [ apply (eq1 A _ _);try assumption| |];smt.
 cut H:
 (Pr[CPA2(BR2,A).main() @ &m : res \/ mem M.r ARO.log] =
  Pr[CPA2(BR2,A).main() @ &m : res] +  Pr[CPA2(BR2,A).main() @ &m : mem M.r ARO.log] -
  Pr[CPA2(BR2,A).main() @ &m : res /\ mem M.r ARO.log]);[pr_or|];smt.
save.

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

module BR_OW(A_ : Adv) : Inverter = {
 module ARO = ARO(RO)
 module A = A_(ARO)
  fun i(pk : pkey,y : randomness) : randomness ={
  var m0 : plaintext;
  var m1 : plaintext;
  var h : plaintext;
  var b : bool;
  var x : randomness;
  ARO.init();
  (m0,m1)  = A.a1(pk);
  h = $uniform; 
  b  = A.a2(y || h);
  x = Option.proj (Map.find (lambda p0 p1,f pk p0 = y) RO.m);
   return (x);
 }
}.


lemma f_iny :
forall (x, y : randomness, pk: pkey, sk : skey), 
in_supp (pk,sk) keypairs  =>
f pk x = f pk y => x = y.
proof.
 intros x y pk sk Hsupp Heqf.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite Heqf;smt.
save.


lemma eq2 : forall (A <: Adv {M,RO,ARO}), 
(forall (O <: ARO), islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o => islossless A(O).a2) =>
 equiv [ CPA2(BR2,A).main ~ OW(BR_OW(A)).main : 
 (glob A){1} = (glob A){2} ==> (mem M.r{1} ARO.log{1} => res{2})].
proof.
 intros A Hlossless1 Hlossless2.
 fun.
 rnd{1}.
 inline  BR_OW(A).i.
 inline CPA2(BR2, A).ARO.init RO.init CPA2(BR2, A).SO.kg 
 BR_OW(A).ARO.init.
 inline CPA2(BR2,A).SO.enc.
 seq 11 9:
 (={pk,sk,RO.m,ARO.log} /\ pk0{2} = pk{2} /\ 
  in_supp (pk{2},sk{2}) keypairs /\
(glob A){1} = (glob A){2}  /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1}) /\
 M.r{1} = x{2} /\ y0{2} = f pk{2} x{2}).
 call 
 (={c,RO.m,ARO.log} /\ (glob A){1} = (glob A){2} /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1}))
 (={RO.m,ARO.log,res} /\ (glob A){1} = (glob A){2} /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1})).
 fun (={RO.m,ARO.log} /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1}));[smt|smt|].
 fun;if;[smt|inline RO.o;wp;rnd |];wp;skip;progress;smt.
 wp;rnd;swap{1} -7;wp.
 call (={p,RO.m,ARO.log} /\ (glob A){1} = (glob A){2} /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1}))
      (={res,RO.m,ARO.log} /\ (glob A){1} = (glob A){2}  /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1})).
 fun (={RO.m,ARO.log}  /\ (forall x, in_dom x RO.m{1} = mem x ARO.log{1}));[smt|smt|].
 fun;if;[smt|inline RO.o;wp;rnd |];wp;skip;progress;smt.
 do 2! (wp;rnd);skip;progress;try smt.
wp;skip;progress.
elim (find_in
      (lambda (p0:randomness) (p1:to), f pk{2} p0 = f pk{2} x{2})
      RO.m{2}
      _); first exists x{2}; split;smt.
intros x2 Hfind.
rewrite Hfind.
elim (find_cor
      (lambda (p0:randomness) (p1:to), f pk{2} p0 = f pk{2} x{2})
      RO.m{2}
      x2 _).
assumption.
delta;simplify.
intros Hin_dom Hf.
rewrite (Option.proj_def<:from> x2).
apply (f_iny _ _ pk{2} sk{2} _ _);smt.
save.


lemma Reduction (A <: Adv {M,RO,ARO}) &m : 
(forall (O <: ARO), islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o => islossless A(O).a2) =>
Pr[CPA(BR,A).main() @ &m : res] <= 1%r / 2%r + Pr[OW(BR_OW(A)).main() @ &m : res].
proof.
 intros Hlossless1 Hlossless2.
 apply (real_le_trans _  
               (1%r/2%r + Pr[CPA2(BR2,A).main() @ &m : mem M.r ARO.log]) _).
 apply (prob1_2 A &m _ _ );assumption.
 cut H: (Pr[CPA2(BR2,A).main() @ &m : mem M.r ARO.log] <=
         Pr[OW(BR_OW(A)).main() @ &m : res]).
 equiv_deno (_ : (glob A){1} = (glob A){2} ==>
 (mem M.r ARO.log){1} => res{2});trivial.
 apply (eq2 A);assumption.
 by smt.
save.

lemma Conclusion (A <: Adv {M,RO,ARO}) &m :
(forall (O <: ARO), islossless O.o => islossless A(O).a1) =>
(forall (O <: ARO), islossless O.o => islossless A(O).a2) =>
exists (I<:Inverter), Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
                      Pr[OW(I).main() @ &m : res].
proof.
 intros Hlossless1 Hlossless2;exists (BR_OW(A)).
 cut aux : 
 (forall (x, y:real), x <= 1%r / 2%r + y => x - 1%r / 2%r  <= y);first smt.
 apply (aux _ _ _).
 apply (Reduction A &m _ _);assumption.
save.
