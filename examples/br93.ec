require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
require import Int.
require import Distr.
require import Bool.
require import Real.


module type ARO = {
 fun h_a(x : bitstring) : bitstring
}.

module type RO = {
 fun init(): unit
 fun h(x : bitstring) : bitstring
}.

type pkey.
type skey.

op k : int. (* size of message *)

module type Scheme(R : RO) = {
   fun init(): unit 
   fun kg() : (pkey * skey)
   fun enc(pk:pkey, m:bitstring): bitstring 
   fun dec(sk:skey, c:bitstring): bitstring 
  }.

module type Adv (O : ARO) = {
 fun a1 (p : pkey) : (bitstring * bitstring) 
 fun a2 (c : bitstring) : bool 
}.

 module O : RO,ARO = {
  var mH : (bitstring,bitstring) map
  var sH : bitstring set
  fun init() :unit ={
   mH = Map.empty;
   sH = Set.empty;
  }

    fun h(x:bitstring): bitstring = {
    var r : bitstring;
   r = $Dbitstring.dbitstring(k);
    if (!in_dom x mH) {
    mH.[x] = r;
   }
     return (proj(mH.[x]));
  }
  
    fun h_a(x:bitstring): bitstring = {
    var r : bitstring;
   sH = add x sH;
    r := h(x);
    return r;
  }
 }.


module CPA(S : Scheme, A : Adv) = {
 module SO = S(O)
 module AO = A(O)


  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0 : bitstring;
  var m1 : bitstring;
  var c : bitstring;
  var b : bool = false;
  var b' : bool;
  var s:bitstring;
  SO.init();
  (pk,sk) := SO.kg();
  (m0,m1) := AO.a1(pk);
  b = $Dbool.dbool;
  if (length m0 = k /\ length m1 = k) { 
   c := SO.enc(pk,b?m0:m1);
   b':= AO.a2(c);
  } else {
   b' = true;
  }
  return b = b';
 }
 
}.

op l : int. (* size of randmness *)
op n : int. (* size of cipher *)

op keypairs: (pkey * skey) distr.
op f : pkey -> bitstring -> bitstring.
op finv : skey -> bitstring -> bitstring.

 (* module type Scheme(R : RO) = { *)
 (*    fun init(): unit  *)
 (*    fun kg() : (pkey * skey) *)
 (*    fun enc(pk:pkey, m:bitstring): bitstring  *)
 (*    fun dec(sk:skey, c:bitstring): bitstring  *)
 (*   }. *)


module BR(R : RO) : Scheme(R) = {
 var r : bitstring
 fun init() : unit = {
  r = $Dbitstring.dbitstring(l); 
 R.init();
 }

   fun kg():(pkey * skey) = {
   var pk, sk:(pkey * skey);
  (pk,sk) = $keypairs;
   return (pk,sk);
 }
 
   fun enc(pk:pkey, m:bitstring): bitstring = {
   var h : bitstring;
   h := R.h(r);
   return ((f pk r) || m ^^ h);
 }
   fun dec(sk:skey, c:bitstring): bitstring ={
   var v : bitstring;
   var t : bitstring;
   v := R.h(finv sk (sub c 0 l)); 
  t = sub c (l+1) k;
   return (t ^^ v);
 }
}.



  (* Step 1: replace the hash call by a random value *)

module BR2(R : RO) : Scheme(R) = {
 var r : bitstring
 fun init() : unit = {
  r = $Dbitstring.dbitstring(l); 
 R.init();
 }

   fun kg():(pkey * skey) = {
   var pk, sk:(pkey * skey);
  (pk,sk) = $keypairs;
   return (pk,sk);
 }
 
   fun enc(pk:pkey, m:bitstring): bitstring = {
   var h : bitstring;
  h = $Dbitstring.dbitstring(k); 
   return ((f pk r) || m ^^ h);
 }
   fun dec(sk:skey, c:bitstring): bitstring ={
   var v : bitstring;
   var t : bitstring;
   v := R.h(finv sk (sub c 0 l)); 
  t = sub c (l+1) k;
   return (t ^^ v);
 }
}.

lemma eq_except_dom : forall(x, y : 'a, m1, m2 : ('a,'b) map), 
 Map.eq_except m1 m2 x => x <> y => 
(Map.in_dom y m1 <=> Map.in_dom y m2)
by [].


lemma eq_except_dom2 : forall(x, y : 'a, m1, m2 : ('a,'b) map), 
 Map.eq_except m1 m2 x => x <> y => 
(!(Map.in_dom y m1) <=> !(Map.in_dom y m2))
by [].


lemma eq1 : forall (A <: Adv {BR,BR2,CPA,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA(BR,A).main ~ CPA(BR2,A).main : 
(glob A){1} = (glob A){2} ==>
 (!mem BR2.r O.sH){2} => res{1} = res{2}].
proof.
 intros A HALossless.
 fun.
 app 5 5:
( m0{1} = m0{2}/\ m1{1} = m1{2} /\ b{1} = b{2} /\
  pk{1} = pk{2} /\ (glob A){1} = (glob A){2} /\
 O.sH{1} = O.sH{2} /\ BR.r{1} = BR2.r{2} /\
 O.mH{1} = O.mH{2} /\ 
(forall (x : bitstring), mem x O.sH{2} <=> in_dom x O.mH{2})
).
rnd.
call (p{1} = p{2} /\ (glob A){1} = (glob A){2} /\
 O.sH{1} = O.sH{2} /\ 
O.mH{1} = O.mH{2} /\ 
(forall (x : bitstring), mem x O.sH{2} <=> in_dom x O.mH{2}))
(res{1} = res{2} /\ (glob A){1} = (glob A){2} /\
 O.sH{1} = O.sH{2} /\
O.mH{1} = O.mH{2} /\
(forall (x : bitstring), mem x O.sH{2} <=> in_dom x O.mH{2})).
fun ( O.sH{1} = O.sH{2} /\
O.mH{1} = O.mH{2} /\ 
(forall (x : bitstring), mem x O.sH{2} <=> in_dom x
 O.mH{2}));try trivial.
fun.
inline O.h.
wp;rnd;wp;skip;simplify;progress (try trivial).
inline CPA(BR, A).SO.init  O.init  CPA(BR, A).SO.kg
       CPA(BR2, A).SO.init O.init CPA(BR2, A).SO.kg.
wp;rnd;wp;rnd;wp;skip;simplify;trivial.
if.
trivial.
 call ((!mem BR2.r O.sH){2} => 
 O.sH{1} = O.sH{2} /\
 eq_except O.mH{1} O.mH{2}  BR2.r{2} /\ 
 (glob A){1} = (glob A){2} /\ c{1} = c{2})
((!mem BR2.r O.sH){2} => res{1} = res{2}).
 fun (mem BR2.r O.sH) 
(O.sH{1} = O.sH{2} /\ eq_except O.mH{1} O.mH{2}
 BR2.r{2}).
trivial.
trivial.
assumption.
 fun.
 simplify.
 inline O.h.
 wp;rnd;wp;skip;trivial.
 admit. (* inline does not still work in bd_hoare *)
 admit. (* inline does not still work in bd_hoare *)
 inline CPA(BR, A).SO.enc CPA(BR2, A).SO.enc  O.h.
 wp;rnd;wp;skip;progress (try trivial).
wp;skip;progress(try trivial).
save.


lemma prob1_1 :
forall (A <: Adv {BR,BR2,CPA,O}),
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} =>
Pr[CPA(BR,A).main() @ &m1: res] <=
Pr[CPA(BR2,A).main() @ &m2 : res || mem BR2.r O.sH].
proof.
intros A Hlossless &m1 &m2 Hglob.
equiv_deno (_ : (glob A){1} = (glob A){2} ==>
  !(mem BR2.r O.sH){2} => res{1} = res{2}).
apply (eq1(<:A) _).
assumption.
assumption.
trivial.
save.


lemma prob1_2 :
forall (A <: Adv {BR,BR2,CPA,O}),
forall &m,
Pr[CPA(BR2,A).main() @ &m : res || mem BR2.r O.sH] <=
Pr[CPA(BR2,A).main() @ &m : res ] + 
Pr[CPA(BR2,A).main() @ &m :  mem BR2.r O.sH].
proof.
admit. (*wait for cesar *)
save.

lemma real_le_trans : forall(a, b, c : real),  
      Real.(<=) a b => Real.(<=) b  c => a <= c
by [].

lemma prob1_3 :
forall (A <: Adv {BR,BR2,CPA,O}),
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} =>
Pr[CPA(BR,A).main() @ &m1: res] <=
Pr[CPA(BR2,A).main() @ &m2 : res ] + 
Pr[CPA(BR2,A).main() @ &m2 :  mem BR2.r O.sH].
proof.
intros A Hlossless &m1 &m2 Hglob.
apply (real_le_trans 
           Pr[CPA(BR,A).main() @ &m1: res] 
           Pr[CPA(BR2,A).main() @ &m2 : res || mem BR2.r O.sH]
           (Pr[CPA(BR2,A).main() @ &m2 : res] + 
              Pr[CPA(BR2,A).main() @ &m2 : mem BR2.r O.sH]) _ _).
apply (prob1_1 (<:A) _ &m1 &m2 _);try trivial;assumption.
apply (prob1_2 (<:A) &m2).
save.

module BR3(R : RO) : Scheme(R) = {
 var r : bitstring
 fun init() : unit = {
  r = $Dbitstring.dbitstring(l); 
 R.init();
 }

   fun kg():(pkey * skey) = {
   var pk, sk:(pkey * skey);
  (pk,sk) = $keypairs;
   return (pk,sk);
 }
 
   fun enc(pk:pkey, m:bitstring): bitstring = {
   var h : bitstring;
  h = $Dbitstring.dbitstring(k); 
   return ((f pk r) || h);
 }
   fun dec(sk:skey, c:bitstring): bitstring ={
   var v : bitstring;
   var t : bitstring;
   v := R.h(finv sk (sub c 0 l)); 
  t = sub c (l+1) k;
   return (t ^^ v);
 }
}.

lemma eq2 : forall (A <: Adv {BR2,BR3,CPA,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA(BR2,A).main ~ CPA(BR3,A).main : 
(glob A){1} = (glob A){2} ==>
 res{1} = res{2} /\ 
O.sH{1} = O.sH{2} /\ BR2.r{1} = BR3.r{2}].
proof.
intros A Hlossless.
fun.
app 5 5: 
(O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\ BR2.r{1} =
  BR3.r{2} /\ m0{1} = m0{2} /\ m1{1} = m1{2} /\  b{1} = b{2} /\
 (glob A){1} = (glob A){2} /\ pk{1} = pk{2}).
rnd.
call (O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\ 
      p{1} = p{2} /\ (glob A){1} = (glob A){2})
(O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\ 
 res{1} = res{2}/\ (glob A){1} = (glob A){2}).
fun ((O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2})).
trivial.
trivial.
fun.
inline O.h.
wp;rnd;wp;skip;simplify;trivial.
inline CPA(BR2, A).SO.init CPA(BR2, A).SO.kg O.init 
       CPA(BR3, A).SO.init CPA(BR3, A).SO.kg.
wp;rnd;wp;rnd;wp;skip;trivial.
if.
trivial.
call (O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\ 
      c{1} = c{2} /\ (glob A){1} = (glob A){2})
(O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\ 
 res{1} = res{2}).
fun ((O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2})).
trivial.
trivial.
fun.
inline O.h.
wp;rnd;wp;skip;simplify;trivial.
inline CPA(BR2, A).SO.enc CPA(BR3, A).SO.enc.
wp.
rnd (lambda v, m{2} ^^ v)(lambda v, m{2} ^^ v).
simplify;wp;skip;progress (try (case (b{2});trivial)).
wp;skip;progress(try trivial).
save.


lemma prob2_1 : 
forall (A <: Adv {BR2,BR3,CPA,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} => 
Pr[CPA(BR2,A).main() @ &m1: res] =
Pr[CPA(BR3,A).main() @ &m2 : res].
proof.
intros A Hlossless &m1 &m2 Hglob.
equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
                 res{1} = res{2} /\ O.sH{1} = O.sH{2} /\ BR2.r{1} = BR3.r{2}).
apply (eq2(<:A) _).
assumption.
assumption.
trivial.
save.

lemma prob2_2 : 
forall (A <: Adv {BR2,BR3,CPA,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} => 
Pr[CPA(BR2,A).main() @ &m1: mem BR2.r O.sH] =
Pr[CPA(BR3,A).main() @ &m2 : mem BR3.r O.sH].
proof.
intros A Hlossless &m1 &m2 Hglob.
equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
                 res{1} = res{2} /\ O.sH{1} = O.sH{2} /\ BR2.r{1} = BR3.r{2}).
apply (eq2(<:A) _).
assumption.
assumption.
trivial.
save.


module CPA2(S : Scheme, A : Adv) = {
 module SO = S(O)
 module AO = A(O)


  fun main(): bool = {
  var pk:pkey;
  var sk:skey;
  var m0 : bitstring;
  var m1 : bitstring;
  var c : bitstring;
  var b : bool = false;
  var b' : bool;
  var s:bitstring;
  SO.init();
  (pk,sk) := SO.kg();
  (m0,m1) := AO.a1(pk);
  if (length m0 = k /\ length m1 = k) { 
   c := SO.enc(pk,m0);
   b':= AO.a2(c);
  } else {
   b' = true;
  }
  b = $Dbool.dbool;
  return b = b';
 }
 
}.

lemma eq3 : forall (A <: Adv {BR3,CPA,CPA2,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 equiv [ CPA(BR3,A).main ~ CPA2(BR3,A).main : 
(glob A){1} = (glob A){2} ==>
 res{1} = res{2} /\ 
O.sH{1} = O.sH{2} /\ BR3.r{1} = BR3.r{2}].
proof.
intros A Hlossless.
fun.
swap{2} -1.
app 5 5: (b{1} = b{2} /\ O.sH{1} = O.sH{2} /\ pk{1} = pk{2} /\
         O.mH{1} = O.mH{2} /\ m0{1} = m0{2} /\ m1{1} = m1{2} /\ 
         (glob A){1} = (glob A){2} /\ BR3.r{1} = BR3.r{2}).
rnd;simplify.
call (p{1} = p{2} /\ O.sH{1} = O.sH{2} /\ 
      O.mH{1} = O.mH{2} /\ (glob A){1} = (glob A){2})
     (res{1} = res{2} /\ O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2} /\
      (glob A){1} = (glob A){2}).
fun ( O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2}).
trivial.
trivial.
fun.
inline O.h.
wp;rnd;wp;skip;trivial.
inline CPA(BR3, A).SO.init  CPA(BR3, A).SO.kg  O.init
       CPA2(BR3, A).SO.init CPA2(BR3, A).SO.kg.
wp;rnd;wp;rnd;wp;skip;trivial.
if.
trivial.
call (c{1} = c{2} /\ O.sH{1} = O.sH{2} /\ 
      O.mH{1} = O.mH{2} /\ (glob A){1} = (glob A){2})
     (res{1} = res{2} /\ O.sH{1} = O.sH{2}).
fun ( O.sH{1} = O.sH{2} /\ O.mH{1} = O.mH{2}).
trivial.
trivial.
fun.
inline O.h.
wp;rnd;wp;skip;trivial.
inline CPA(BR3, A).SO.enc CPA2(BR3, A).SO.enc.
wp;rnd;wp;skip;trivial.
wp;skip;trivial.
save.


lemma prob3_1 : 
 forall (A <: Adv {BR3,CPA,CPA2,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
 bd_hoare[CPA2(BR3,A).main : true ==> res] = (1%r/2%r).
proof.
intros A Hlossless.
fun.
rnd (1%r/2%r) (lambda (x:bool), x=b').
app 4: (true) 1%r.
admit. (*wait for cesar *)
admit.
save.


lemma prob3_2 : 
forall (A <: Adv {BR3,CPA,CPA2,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} => 
Pr[CPA(BR3,A).main() @ &m1: res] =
Pr[CPA2(BR3,A).main() @ &m2 : res].
proof.
intros A Hlossless &m1 &m2 Hglob.
equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
                 res{1} = res{2} /\ O.sH{1} = O.sH{2} /\ BR3.r{1} = BR3.r{2}).
apply (eq3(<:A) _).
assumption.
assumption.
trivial.
save.

lemma prob3_3 : 
forall (A <: Adv {BR3,CPA,CPA2,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} => 
Pr[CPA(BR3,A).main() @ &m1: mem BR3.r O.sH] =
Pr[CPA2(BR3,A).main() @ &m2 : mem BR3.r O.sH].
proof.
intros A Hlossless &m1 &m2 Hglob.
equiv_deno (_ : (glob A){1} = (glob A){2} ==> 
                 res{1} = res{2} /\ O.sH{1} = O.sH{2} /\ BR3.r{1} = BR3.r{2}).
apply (eq3(<:A) _).
assumption.
assumption.
trivial.
save.

lemma sofar : 
forall (A <: Adv {BR,BR2,BR3,CPA,CPA2,O}), 
(forall (O <: ARO),
 bd_hoare[ O.h_a : true ==> true] = 1%r =>
 bd_hoare[ A(O).a2 : true ==> true] = 1%r) =>
forall &m1 &m2, (glob A){m1} = (glob A){m2} => 
Pr[CPA(BR,A).main() @ &m1: res] <=
1%r/2%r +
Pr[CPA2(BR3,A).main() @ &m2 : mem BR3.r O.sH].
proof.
intros A Hlossless &m1 &m2 Hglob.
(* boring *)
admit.
save.