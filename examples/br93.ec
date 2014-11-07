require import ROM.
require import Array.
require import FMap.
require import FSet.
require import Int.
require import Distr.
require import Bool.
require import Real.
require import AWord.


op k : int. (* size of message *)
op l : int. (* size of randmness *)
op n : int. (* size of cipher *)

axiom sizes : k + l = n.

op qH : int. (* bound on adversary calls to hash H *)

clone AWord as Plaintext with op length = k.
clone AWord as Ciphertext with op length = n.
clone AWord as Randomness with op length = l.

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

axiom keypair_lossless : mu keypairs True = 1%r.

op uniform : plaintext distr = Plaintext.Dword.dword.
op uniform_rand : randomness distr = Randomness.Dword.dword.

clone import ROM.SetLog as RandOrcl_BR with 
  type from  <- randomness, 
  type to    <- plaintext,
  op dsample <- fun (x:randomness), uniform,
  op qH      <- qH.
import Lazy.
import Types.

module type Scheme(RO : Oracle) = {
 proc kg() : (pkey * skey)
 proc enc(pk:pkey, m:plaintext): ciphertext 
}.

module type Adv(ARO : ARO)  = {
 proc a1 (p : pkey) : (plaintext * plaintext) {ARO.o} 
 proc a2 (c : ciphertext) : bool {ARO.o}
}.


module CPA(S : Scheme, A_ : Adv) = {
 module ARO = Log(RO)
 module A = A_(ARO)
 module SO = S(RO)
  proc main(): bool = {
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

op (||) (x:randomness) (y:plaintext):ciphertext =
 Ciphertext.from_bits ((to_bits x) || (to_bits y)).


module M = {
 var r : randomness
}.

module BR(R : Oracle) : Scheme(R) = {
 proc kg():(pkey * skey) = {
  var (pk, sk): pkey * skey;
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 proc enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  M.r = $uniform_rand; 
  h  = R.o(M.r);
  return ((f pk M.r) ||   m ^ h);
 }
}.


  (* Step 1: replace the hash call by a random value *)

module BR2(R : Oracle) : Scheme(R) = {
 proc kg():(pkey * skey) = {
  var (pk, sk): (pkey * skey);
  (pk,sk) = $keypairs;
  return (pk,sk);
 }
 
 proc enc(pk:pkey, m:plaintext): ciphertext = {
  var h : plaintext;
  M.r = $uniform_rand; 
  h = $uniform; 
  return ((f pk M.r) || h);
 }
}.

lemma eq1_enc :
 equiv [ BR(RO).enc ~ BR2(RO).enc : 
={pk,RO.m} ==>
!mem M.r{2} (dom RO.m{2}) => (={res} /\ eq_except RO.m{1} RO.m{2} M.r{2}) ].
proof.
 proc;inline RO.o.
 wp;rnd ((^) m{1}) ((^) m{1}).
 wp;rnd;skip;progress => //; smt.
qed.

module CPA2(S : Scheme, A_ : Adv) = {
 module ARO = Log(RO)
 module A = A_(ARO)
 module SO = S(RO)
  proc main(): bool = {
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
  return b' = b;
 } 
}.


lemma lossless_ARO_init : islossless Log(RO).init.
proof. by apply (Log_init_ll RO); apply RO_init_ll. qed.

lemma lossless_ARO_o : islossless Log(RO).o.
proof. by apply (Log_o_ll RO); apply RO_o_ll; apply Plaintext.Dword.lossless. qed.

section.

declare module A : Adv {M,RO,Log}.

axiom lossless1 : (forall (O <: ARO), islossless O.o =>  islossless A(O).a1).
axiom lossless2 : (forall (O <: ARO), islossless O.o =>  islossless A(O).a2).

equiv eq1 :  CPA(BR,A).main ~ CPA2(BR2,A).main : 
(glob A){1} = (glob A){2} ==>
 (!mem M.r Log.qs){2} => ={res}.
proof.
 proc.
 swap{2} -2.
 call (_ : (mem M.r Log.qs), 
           (={Log.qs} /\ eq_except RO.m{1} RO.m{2} M.r{2})).
 intros => O Hll;apply (lossless2 O) => //.
 proc;inline RO.o;wp;rnd;wp;skip;progress => //; first 5 last; last 6 smt.
  case ((x = M.r){2}); first smt.
  by apply (absurd (mem x (dom RO.m)){2})=> //; smt.
 intros _ _;apply lossless_ARO_o.
 intros &m; proc; wp; call (RO_o_ll _); auto; smt.
 call eq1_enc.
 rnd.
 call  (_: ={RO.m,Log.qs} /\
 (forall (x : randomness), mem x Log.qs{2} <=> mem x (dom RO.m{2}))).
  proc;inline RO.o;wp;rnd;wp;skip;progress;smt.
  inline CPA(BR,A).SO.kg CPA2(BR2,A).SO.kg.
  inline CPA(BR,A).ARO.init CPA2(BR2,A).ARO.init RO.init;wp;rnd;wp;skip.
  progress;by smt.
qed.

lemma foo1 : forall (b:bool), mu {0,1} ((=) b) = 1%r / 2%r.
proof. intros b; apply (Bool.Dbool.mu_x_def b). qed. 

lemma foo2 : mu uniform_rand True = 1%r.
proof. apply Randomness.Dword.lossless. qed.

lemma foo3 : mu uniform True = 1%r.
proof. apply Plaintext.Dword.lossless. qed.

lemma prob1_1 : 
 forall &m,Pr[CPA2(BR2,A).main()  @ &m : res] = 1%r / 2%r.
proof.
 intros &m.
 byphoare (_ : true ==> res); trivial.
   proc.
   rnd ((=) b').
   conseq ( _ : ==> true).
    progress;apply foo1.
   call ( _ :true). 
   intros => O Hll;apply (lossless2 O) => //.

    apply lossless_ARO_o.   
   inline CPA2(BR2,A).SO.enc;do 2! (wp;rnd (True));wp.
   conseq ( _ : ==> true).
     rewrite foo2; rewrite foo3;progress.
   call (_ : true).
   intros => O Hll;apply (lossless1 O) => //.
     apply lossless_ARO_o.  
   inline CPA2(BR2,A).SO.kg.
   wp;rnd (True);wp.
   conseq ( _ : ==> true).
     progress;apply keypair_lossless. 
   call lossless_ARO_init;skip;trivial.
qed.

lemma prob1_2 : forall &m,
Pr[CPA(BR,A).main() @ &m: res] <=
1%r/2%r + Pr[CPA2(BR2,A).main() @ &m : mem M.r Log.qs].
proof.
 intros &m.
 rewrite -(prob1_1 &m) //.
 apply (Real.Trans _ 
             Pr[CPA2(BR2,A).main() @ &m : res \/ mem M.r Log.qs]).
 byequiv (eq1 ) => //;progress;smt.
 rewrite Pr [mu_or].  smt.
qed.

module type Inverter = {
 proc i(pk : pkey, y : randomness) : randomness
}.

module OW(I :Inverter) ={
 proc main() : bool ={
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
 module ARO = Log(RO)
 module A = A_(ARO)
  proc i(pk : pkey,y : randomness) : randomness ={
  var m0 : plaintext;
  var m1 : plaintext;
  var h : plaintext;
  var b : bool;
  var x : randomness;
  ARO.init();
  (m0,m1)  = A.a1(pk);
  h = $uniform; 
  b  = A.a2(y || h);
  x = oget (FMap.find (fun p0 p1,f pk p0 = y) RO.m);
   return (x);
 }
}.

lemma f_iny x  y pk sk: 
in_supp (pk,sk) keypairs  =>
f pk x = f pk y => x = y.
proof.
 move=> Hsupp Heqf.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite -(finvof pk sk _ _);first smt.
 rewrite Heqf;smt.
qed.

equiv eq2 : CPA2(BR2,A).main ~ OW(BR_OW(A)).main : 
 (glob A){1} = (glob A){2} ==> (mem M.r{1} Log.qs{1} => res{2}).
proof.
 proc.
 rnd{1}.
 inline  BR_OW(A).i.
 inline CPA2(BR2, A).ARO.init RO.init CPA2(BR2, A).SO.kg 
 BR_OW(A).ARO.init.
 inline CPA2(BR2,A).SO.enc.
 seq 11 9:
 (={pk,sk,RO.m,Log.qs} /\ pk0{2} = pk{2} /\ 
  in_supp (pk{2},sk{2}) keypairs /\
(glob A){1} = (glob A){2}  /\ (forall x, mem x (dom RO.m){1} = mem x Log.qs{1}) /\
 M.r{1} = x{2} /\ y0{2} = f pk{2} x{2}).

 call (_ : ={RO.m,Log.qs} /\ (forall x, mem x (dom RO.m){1} = mem x Log.qs{1})).
 proc;inline RO.o;wp;rnd;wp;skip;progress=> //.
   by rewrite dom_set !mem_add H.
   by rewrite mem_add; rewrite -H; case (x1 = x{2})=> //=;
      intros=> ->; smt.
 wp;rnd;swap{1} -7;wp.
 call (_: ={RO.m,Log.qs}  /\ (forall x, mem x (dom RO.m){1} = mem x Log.qs{1})).
 proc;inline RO.o;wp;rnd;wp;skip;progress=> //.
   by rewrite dom_set !mem_add H.
   by rewrite mem_add; rewrite -H; case (x1 = x{2})=> //=;
      intros=> ->; smt.
 do 2! (wp;rnd);skip;progress;smt.
 wp;skip;progress;first smt.
 pose eq_test:= fun p0 (p1:plaintext), p0 = x{2}.
 cut ->: (fun p0 (p1:plaintext), f pk{2} p0 = f pk{2} x{2}) = eq_test.
   apply fun_ext=> y //=.
   apply fun_ext=> y' //=.
   rewrite eq_iff /eq_test; split=> //=.
   by apply (f_iny _ _ _ sk{2} H).
 cut: exist eq_test RO.m{2}.
   by rewrite /exist; exists x{2}=> //=; rewrite H0.
 cut find_cor: forall y, find eq_test RO.m{2} = Some y => x{2} = y.
   by rewrite /eq_test; move=> y /find_cor.
 rewrite find_in /oget.
 by case {-1}(find eq_test RO.m{2}) (Logic.eq_refl (find eq_test RO.m{2})).
qed.

lemma Reduction &m : 
Pr[CPA(BR,A).main() @ &m : res] <= 1%r / 2%r + Pr[OW(BR_OW(A)).main() @ &m : res].
proof.
 apply (Real.Trans _  
               (1%r/2%r + Pr[CPA2(BR2,A).main() @ &m : mem M.r Log.qs])).
 apply (prob1_2 &m) => //.
 cut H: (Pr[CPA2(BR2,A).main() @ &m : mem M.r Log.qs] <=
         Pr[OW(BR_OW(A)).main() @ &m : res]).
   byequiv eq2 => //.
 by smt.
qed.

lemma Conclusion  &m :
exists (I<:Inverter), Pr[CPA(BR,A).main() @ &m : res] - 1%r / 2%r <= 
                      Pr[OW(I).main() @ &m : res].
proof.
 exists (BR_OW(A)). 
 by cut h := Reduction &m => //;smt.
qed.

end section.
