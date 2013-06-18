require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
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

axiom keypair_lossless : mu keypairs cPtrue = 1%r.

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
 fun init() : unit
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
  SO.init();
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
 fun init() : unit = {
  M.r = $uniform_rand; 
 }

 fun kg():(pkey * skey) = {
  var (pk, sk): pkey * skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  h  = R.o(M.r);
  return ((f pk M.r) ||   m ^^ h);
 }
}.


  (* Step 1: replace the hash call by a random value *)

module BR2(R : Oracle) : Scheme(R) = {
 fun init() : unit = {
  M.r = $uniform_rand; 
 }

 fun kg():(pkey * skey) = {
  var (pk, sk): (pkey * skey);
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 fun enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  h = $uniform; 
  return ((f pk M.r) || m ^^ h);
 }
}.

lemma eq1_enc :
 equiv [ BR(RO).enc ~ BR2(RO).enc : 
={pk,RO.m,m,M.r} ==>
!in_dom M.r{2} RO.m{2} => (={res} /\ eq_except RO.m{1} RO.m{2} M.r{2}) ].
proof.
 fun.
 inline RO.o.
 wp;rnd;wp;skip;progress;trivial.
save.


lemma eq1 : forall (A <: Adv {M,RO,ARO}), 
(forall (O <: ARO),
 islossless O.o =>  islossless A(O).a1) =>
(forall (O <: ARO),
 islossless O.o =>  islossless A(O).a2) =>
 equiv [ CPA(BR,A).main ~ CPA(BR2,A).main : 
(glob A){1} = (glob A){2} ==>
 (!mem M.r ARO.log){2} => ={res}].
proof.
 intros A HALossless1 HALossless2.
 fun.
 call ((!mem M.r ARO.log){2} => 
       (={ARO.log,c} /\  eq_except RO.m{1} RO.m{2}  M.r{2} 
                     /\ (glob A){1} = (glob A){2}))
      ((!mem M.r ARO.log){2} => ={res}).
 fun (mem M.r ARO.log) 
     (={ARO.log} /\ eq_except RO.m{1} RO.m{2} M.r{2});
      [trivial|trivial|assumption| | |].
 fun.
 if;[trivial| |wp;skip;trivial].
 inline RO.o;wp;rnd;wp;skip;progress;trivial.
 intros &m H. fun. 
 if.
 inline RO.o;wp;rnd 1%r cPtrue;wp;skip;progress;trivial.
 wp;skip;progress;trivial.
 intros &m;fun;if.
 inline RO.o.
 wp;rnd 1%r cPtrue;wp;skip;progress;trivial.
 wp;skip;progress;trivial.
 (* this is a bug *)
 call (pk{1} = pk{2} /\ RO.m{1} = RO.m{2} /\ m{1} = m{2} /\
      M.r{1} = M.r{2})
      (!in_dom M.r{2} RO.m{2} =>
       (res{1} = res{2} /\ eq_except RO.m{1} RO.m{2} M.r{2})).
 (* apply (eq1_enc). *)
 rnd.
 call (p{1} = p{2} /\ (glob A){1} = (glob A){2} /\
 ARO.log{1} = ARO.log{2} /\ 
 RO.m{1} = RO.m{2} /\ 
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2}))
(res{1} = res{2} /\ (glob A){1} = (glob A){2} /\
 ARO.log{1} = ARO.log{2} /\
 RO.m{1} = RO.m{2} /\
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2})).
 fun ( ARO.log{1} = ARO.log{2} /\
  RO.m{1} = RO.m{2} /\ 
 (forall (x : randomness), mem x ARO.log{2} <=> in_dom x RO.m{2})).
  trivial.
  trivial.
  fun.
  if;[trivial| |wp;skip;trivial].
  inline RO.o;wp;rnd;wp;skip;progress;trivial.
  inline CPA(BR,A).SO.kg CPA(BR2,A).SO.kg.
  wp;rnd.
  inline CPA(BR,A).ARO.init CPA(BR,A).SO.init RO.init
  CPA(BR2,A).ARO.init CPA(BR2,A).SO.init RO.init.
  rnd;wp;skip;progress;try trivial.
save.


lemma prob1_1 :
 forall (A <: Adv {BR,BR2,RO,ARO}),
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m ,
Pr[CPA(BR,A).main() @ &m: res] <=
Pr[CPA(BR2,A).main() @ &m : res \/ mem M.r ARO.log].
proof.
 intros A Hlossless1 Hlossless2 &m.
 equiv_deno (_ : (glob A){1} = (glob A){2} ==>
 !(mem M.r ARO.log){2} => res{1} = res{2}).
 apply (eq1(<:A) _ _).
 assumption.
 assumption.
 trivial.
 trivial.
save.


lemma prob1_2 :
 forall (A <: Adv {BR,BR2,RO,ARO}),
 forall &m,
Pr[CPA(BR2,A).main() @ &m : res \/ mem M.r ARO.log] <=
Pr[CPA(BR2,A).main() @ &m : res ] + 
Pr[CPA(BR2,A).main() @ &m :  mem M.r ARO.log].
proof.
intros A &m.
cut H:
(Pr[CPA(BR2,A).main() @ &m : res \/ mem M.r ARO.log] =
 Pr[CPA(BR2,A).main() @ &m : res] +  Pr[CPA(BR2,A).main() @ &m : mem M.r ARO.log] -
 Pr[CPA(BR2,A).main() @ &m : res /\ mem M.r ARO.log]).
pr_or;trivial.
rewrite H.
cut Hge:(0%r <= (Pr[CPA(BR2,A).main() @ &m : res /\ mem M.r ARO.log])).
trivial.
generalize Hge.
generalize (Pr[CPA(BR2,A).main() @ &m : res /\ mem M.r ARO.log]).
generalize (Pr[CPA(BR2,A).main() @ &m : res]).
generalize (Pr[CPA(BR2,A).main() @ &m : mem M.r ARO.log]).
trivial.
save.

lemma real_le_trans : forall(a, b, c : real),  
 Real.(<=) a b => Real.(<=) b  c => a <= c by [].

lemma prob1_3 :
 forall (A <: Adv {BR,BR2,RO,ARO}),
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m,
Pr[CPA(BR,A).main() @ &m: res] <=
Pr[CPA(BR2,A).main() @ &m : res ] + 
Pr[CPA(BR2,A).main() @ &m :  mem M.r ARO.log].
proof.
 intros A Hlossless1 Hlossless2 &m.
 apply (real_le_trans _
         Pr[CPA(BR2,A).main() @ &m : res \/ mem M.r ARO.log] _ _ _).
 apply (prob1_1 (<:A) _ _ &m );try assumption;trivial.
 apply (prob1_2 (<:A)  &m).
save.

(* Step 2: replace r ^^ m by r. This step is justified by optimistic sampling *)

module BR3(R : Oracle) : Scheme(R) = {
 var r : randomness
 fun init() : unit = {
  r = $uniform_rand; 
 }

   fun kg():(pkey * skey) = {
   var (pk, sk): (pkey * skey);
  (pk,sk) = $keypairs;
   return (pk,sk);
 }
 
   fun enc(pk:pkey, m:plaintext): ciphertext = {
   var h : plaintext;
  h = $uniform; 
   return ((f pk r) ||  h);
 }
}.

lemma eq2_enc :
 equiv [ BR2(RO).enc ~ BR3(RO).enc : 
 pk{1} = pk{2} /\ RO.m{1} = RO.m{2} /\ m{1} = m{2} /\ M.r{1} = M.r{2} ==>
 res{1} = res{2} /\ RO.m{1} = RO.m{2}].
proof.
 fun.
 rnd (lambda v, m{2} ^^ v)(lambda v,m{2} ^^ v);skip.
 progress;trivial.
save.

lemma eq2 : forall (A <: Adv {BR2,BR3,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA(BR2,A).main ~ CPA(BR3,A).main : 
 (glob A){1} = (glob A){2} ==>
 res{1} = res{2} /\ 
  ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}].
proof.
 intros A Hlossless1 Hlossless2.
 fun.
 call (ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 c{1} = c{2} /\ (glob A){1} = (glob A){2})
(ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 res{1} = res{2}).
 fun ((ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2})).
 trivial.
 trivial.
 fun.
 if;[trivial| |].
 inline RO.o.
 wp;rnd;wp;skip;trivial.
 wp;skip;trivial.
 call (pk{1} = pk{2} /\ RO.m{1} = RO.m{2} /\ m{1} = m{2} /\ M.r{1} = M.r{2})
      (res{1} = res{2} /\ RO.m{1} = RO.m{2}).
 apply eq2_enc.
 rnd.
 call (ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 p{1} = p{2} /\ (glob A){1} = (glob A){2})
(ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 res{1} = res{2}/\ (glob A){1} = (glob A){2}).
 fun ((ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2})).
 trivial.
 trivial.
 fun.
 if;[trivial| |wp;skip;trivial].
 inline RO.o.
 wp;rnd;wp;skip;trivial.
 inline CPA(BR2, A).SO.init CPA(BR2, A).SO.kg CPA(BR2, A).ARO.init RO.init 
        CPA(BR3, A).SO.init CPA(BR3, A).SO.kg CPA(BR3, A).ARO.init.
 wp;rnd;wp;rnd;wp;skip;progress;trivial.
save.

lemma prob2_1 : 
 forall (A <: Adv {BR2,BR3,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m,
Pr[CPA(BR2,A).main() @ &m: res] =
Pr[CPA(BR3,A).main() @ &m : res].
proof.
 intros A Hlossless1 Hlossless2 &m.
 equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
 res{1} = res{2} /\ ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}).
 apply (eq2(<:A) _ _).
 assumption.
 assumption.
 trivial.
 trivial.
save.

lemma prob2_2 : 
 forall (A <: Adv {BR2,BR3,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m,
Pr[CPA(BR2,A).main() @ &m: mem M.r ARO.log] =
Pr[CPA(BR3,A).main() @ &m : mem M.r ARO.log].
proof.
 intros A Hlossless1 Hlossless2 &m.
 equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
 res{1} = res{2} /\ ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}).
 apply (eq2(<:A) _ _).
 assumption.
 assumption.
 trivial.
 trivial.
save.


(* Step 3: modify the cpa game so the sampling of b is done at the end *)
module CPA2(S : Scheme, A_ : Adv) = {
 module ARO = ARO(RO)
 module A = A_(ARO)
 module SO = S(RO)
  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0 : plaintext;
  var m1 : plaintext;
  var c : ciphertext;
  var b : bool;
  var b' : bool;
  ARO.init();
  SO.init();
  (pk,sk)  = SO.kg();
  (m0,m1)  = A.a1(pk);
  c  = SO.enc(pk,b?m0:m1);
  b' = A.a2(c);
  b = {0,1};
  return b = b';
 } 
}.

lemma eq3 : forall (A <: Adv {BR3,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA(BR3,A).main ~ CPA2(BR3,A).main : 
 (glob A){1} = (glob A){2} ==>
 res{1} = res{2} /\ 
  ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}].
proof.
 intros A Hlossless1 Hlossless2.
 fun.
 swap{2} -1.
 call (ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 c{1} = c{2} /\ (glob A){1} = (glob A){2})
(ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 res{1} = res{2}).
 fun ((ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2})).
 trivial.
 trivial.
 fun.
 if;[trivial| |].
 inline RO.o.
 wp;rnd;wp;skip;trivial.
 wp;skip;trivial.
 inline CPA(BR3, A).SO.enc CPA2(BR3, A).SO.enc.
 wp.
 swap{2} -2.
 wp;rnd;wp;rnd;wp.
 call (ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 p{1} = p{2} /\ (glob A){1} = (glob A){2})
(ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ 
 res{1} = res{2}/\ (glob A){1} = (glob A){2}).
 fun ((ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2})).
 trivial.
 trivial.
 fun.
 if;[trivial| |wp;skip;trivial].
 inline RO.o.
 wp;rnd;wp;skip;trivial.

 inline CPA2(BR3, A).SO.init CPA2(BR3, A).SO.kg CPA2(BR3, A).ARO.init RO.init 
         CPA(BR3, A).SO.init CPA(BR3, A).SO.kg CPA(BR3, A).ARO.init.
 wp;rnd;wp;rnd;wp;skip;progress;trivial.
save.

lemma prob3_1 : 
 forall (A <: Adv {BR3,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m,
Pr[CPA2(BR3,A).main()  @ &m : res] = 1%r / 2%r.
proof.
 intros A Hlossless1 Hlossless2.
 intros &m.
 cut H1 : (bd_hoare[CPA2(BR3,A).main : true ==> res] = (1%r / 2%r)).
 fun; rnd (1%r / 2%r) (lambda b, b = b'); simplify.
 call (true) (true).
 fun (true).
 trivial.
 trivial.
 assumption.
 fun.
 if.
 inline RO.o;wp;rnd 1%r (cPtrue);wp;skip;trivial.
 wp;skip;trivial.
 inline CPA2(BR3,A).SO.enc;wp;rnd 1%r (cPtrue);wp.
 call (true) (true).
 fun (true).
 trivial.
 trivial.
 assumption.
 fun.
 if.
 inline RO.o;wp;rnd 1%r (cPtrue);wp;skip;trivial.
 wp;skip;trivial.
 inline CPA2(BR3,A).SO.kg CPA2(BR3,A).SO.init CPA2(BR3,A).ARO.init RO.init.
 wp;rnd 1%r (cPtrue);rnd 1%r (cPtrue);wp;skip;progress.
 trivial.
 trivial.
 trivial.
 rewrite (Dbool.mu_def  (lambda b, b = result)).
 case (result);delta charfun;simplify;trivial.
 intros &m1. 
 bdhoare_deno H1; trivial.
save.


lemma prob3_2 : 
 forall (A <: Adv {BR3,CPA,CPA2,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m, 
Pr[CPA(BR3,A).main() @ &m: res] =
Pr[CPA2(BR3,A).main() @ &m : res].
proof.
 intros A Hlossless1 Hlossless2 &m.
 equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
 res{1} = res{2} /\ ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}).
 apply (eq3(<:A) _ _).
 assumption.
 assumption.
 trivial.
 trivial.
save.

lemma prob3_3 : 
 forall (A <: Adv {BR3,CPA,CPA2,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 forall &m,
Pr[CPA(BR3,A).main() @ &m: mem M.r ARO.log] =
Pr[CPA2(BR3,A).main() @ &m : mem M.r ARO.log].
proof.
 intros A Hlossless1 Hlossless2 &m.
 equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
 res{1} = res{2} /\ ARO.log{1} = ARO.log{2} /\ M.r{1} = M.r{2}).
 apply (eq3(<:A) _ _).
 assumption.
 assumption.
 trivial.
 trivial.
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
  x = proj (Map.find (lambda p,f pk (Pair.fst p) = y) RO.m);
   return (x);
 }
}.


lemma f_iny :
forall (x, y : randomness, pk: pkey, sk : skey), 
in_supp (pk,sk) keypairs  =>
f pk x = f pk y => x = y.
proof.
 intros x y pk sk Hsupp Heqf.
 rewrite <- (finvof pk sk x _);first trivial.
 rewrite <- (finvof pk sk y _);first trivial.
 rewrite Heqf.
 trivial.
save.


lemma eq4 : forall (A <: Adv {BR3,CPA2,RO,ARO}), 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA2(BR3,A).main ~ OW(BR_OW(A)).main : 
 (glob A){1} = (glob A){2} ==> (mem M.r{1} ARO.log{1} => res{2})].
proof.
 intros A Hlossless1 Hlossless2.
 fun.
 rnd{1}.
 inline  BR_OW(A).i.
 inline CPA2(BR3, A).SO.init CPA2(BR3, A).ARO.init RO.init CPA2(BR3, A).SO.kg 
 BR_OW(A).ARO.init.
 inline CPA2(BR3,A).SO.enc.
 seq 11 9:
 (pk{1} = pk{2} /\ sk{1} = sk{2} /\ pk0{2} = pk{2} /\ 
  in_supp (pk{2},sk{2}) keypairs /\
(glob A){1} = (glob A){2}  /\
 RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ dom RO.m{1} = ARO.log{1} /\ 
 M.r{1} = x{2} /\ y0{2} = f pk{2} x{2}).
 call ((glob A){1} = (glob A){2} /\ c{1} = c{2} /\
 RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ dom RO.m{1} = ARO.log{1})
((glob A){1} = (glob A){2} /\ dom RO.m{1} = ARO.log{1} /\
 RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ res{1} = res{2}).
 fun (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ dom RO.m{1} = ARO.log{1}).
 trivial.
 trivial.
 fun.
 if;[trivial|inline RO.o;wp;rnd |];wp;skip;progress;trivial.
 wp.
 rnd.
 wp.
call ((glob A){1} = (glob A){2} /\ p{1} = p{2} /\
 RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2}  /\ dom RO.m{1} = ARO.log{1})
((glob A){1} = (glob A){2}  /\ dom RO.m{1} = ARO.log{1} /\
 RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ res{1} = res{2}).
 fun (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2}  /\ dom RO.m{1} = ARO.log{1}).
 trivial.
 trivial.
 fun.
 if;[trivial|inline RO.o;wp;rnd |];wp;skip;progress;trivial.
 wp;rnd;rnd;wp;skip.
 progress;trivial.
wp;skip.
progress.
elim (find_some2<:from,to>
      (lambda (p : (from * to)), f pk{2} (fst p) = f pk{2} x{2})
      RO.m{2}
      x{2} _).
split;trivial.
intros x2 Hfind.
rewrite Hfind.
elim (find_some1<:from,to>
      (lambda (p : (from * to)), f pk{2} (fst p) = f pk{2} x{2})
      RO.m{2}
      x2 _).
assumption.
delta;simplify.
intros Hin_dom Hf.
rewrite (proj_def<:from> x2).
apply (f_iny x{2} x2 pk{2} sk{2} _ _);trivial.
save.


lemma Reduction (A <: Adv {CPA,CPA2, BR, BR2, BR3, OW, RO, ARO}) &m : 
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
Pr[CPA(BR,A).main() @ &m : res] <=
 1%r / 2%r + Pr[OW(BR_OW(A)).main() @ &m : res].
 intros Hlossless1 Hlossless2.
 apply (real_le_trans 
 (Pr[CPA(BR, A).main() @ &m : res])
 (Pr[CPA(BR2,A).main() @ &m : res ] + 
  Pr[CPA(BR2,A).main() @ &m : mem M.r ARO.log])
 (1%r / 2%r + Pr[OW(BR_OW(A)).main() @ &m : res]) _ _).
  apply (prob1_3(<:A) _ _ &m);try assumption.
  rewrite (prob2_1(<:A) _ _ &m);try assumption.
  rewrite (prob2_2(<:A) _ _ &m);try assumption.
  rewrite (prob3_2(<:A) _ _ &m);try assumption.
  rewrite (prob3_3(<:A) _ _ &m);try assumption.
  rewrite (prob3_1(<:A) _ _ _ &m);try assumption.
  cut aux: (forall (a b c : real), b <= c => a + b <= a + c).
  trivial.
  apply (aux (1%r/2%r) (Pr[CPA2(BR3,A).main() @ &m : mem M.r ARO.log])
 Pr[OW(BR_OW(A)).main() @ &m : res] _).
  equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
  mem M.r{1} ARO.log{1} => res{2}).
  apply (eq4(<:A) _ _);try assumption.
  trivial.
  trivial.
save.

lemma Conclusion (A <: Adv {CPA,CPA2, BR, BR2, BR3, OW, RO, ARO}) &m :
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a1 : true ==> true] = 1%r) =>
(forall (O <: ARO),
 bd_hoare[ O.o : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 exists (I<:Inverter), 
Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
Pr[OW(I).main() @ &m : res].
proof.
 intros Hlossless1 Hlossless2.
 exists (<:BR_OW(A)).
 cut aux : 
(forall (x, y:real), x <= 1%r / 2%r + y => x - 1%r / 2%r  <= y). 
 trivial.
 apply (aux
 Pr[CPA(BR,A).main() @ &m : res]
 Pr[OW(BR_OW(A)).main() @ &m : res] _).
  apply (Reduction (<:A) &m _ _);assumption.
save.
