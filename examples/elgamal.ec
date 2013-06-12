require import Int.
require import Bool.
type group. 
type skey       = int.
type pkey       = group.
type keys       = skey * pkey.
type plaintext  = group.
type ciphertext = group * group.

op q : int.
op g : group.

(* If we use the native modulo "alt-ergo" is not able
   to perform the proof.
   So we declare an operator (%%) which stand for the modulo ...
*)

op ( %% ) :int -> int -> int.
op ( * ) : group -> group -> group.
op ( ^ ) : group -> int -> group.
op log   : group -> int.
op ( / ) (g1 g2 : group) : group = 
  g ^ (log g1 - log g2).
  

axiom q_pos : 0 < q.

axiom group_pow_add : 
 forall (x, y:int), g ^ (x + y) = g ^ x * g ^ y.

axiom group_pow_mult :
 forall (x, y:int),  (g ^ x) ^ y = g ^ (x * y).

axiom log_pow : 
 forall (g':group), g ^ log(g') = g'.

axiom pow_mod : 
 forall (z:int), g ^ (z%%q) = g ^ z.

axiom mod_add : 
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small : 
 forall (x:int), 0 <= x => x < q => x%%q = x.

axiom mod_sub : 
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q. 

axiom mod_bound : 
 forall (x:int), 0 <= x%%q && x%%q < q. 

axiom mul_div : forall (g1 g2:group), (g1 * g2) / g1 = g2.

module type Adv = { 
  fun a1(pk:pkey)      : plaintext * plaintext 
  fun a2(c:ciphertext) : bool                  
}.

module type Scheme = { 
  fun kg () : skey * pkey 
  fun enc(pk:pkey, m:plaintext) : ciphertext 
  fun dec(sk:skey, c:ciphertext) : plaintext
}.

module ValidScheme(S:Scheme) = {
  fun main (m:plaintext) : bool = {
    var sk : skey;
    var pk : pkey;
    var c  : ciphertext;
    var d  : plaintext;

    (sk,pk)  = S.kg();
    c        = S.enc(pk, m);
    d        = S.dec(sk, c); 

    return (m = d);
  }
}.

module CPA (S:Scheme, A:Adv) = {
  fun main() : bool = {
    var sk : skey;
    var pk : pkey;
    var m0 : plaintext;
    var m1 : plaintext;
    var c  : ciphertext;
    var b  : bool;
    var b' : bool;

    (sk,pk)  = S.kg();
    (m0,m1)  = A.a1(pk);
    b        = ${0,1};
    c        = S.enc(pk, b ? m1 : m0);
    b'       = A.a2(c);
 
    return (b = b');
  } 
}.

module ElGamal : Scheme = {
  fun kg() : skey * pkey = {
    var x : int; (* FIXME notation = $[0..q-1] *)
    x = $[0..q-1];
    return (x, g^x);
  }

  fun enc(pk:pkey, m:plaintext) : ciphertext = {
    var y : int;
    y = $[0..q-1];
    return (g^y, (pk^y) * m);
  }

  fun dec(sk:skey, c:ciphertext) : plaintext = {
    var gxy : group;
    var gy  : group;
    var gxym : group;
    (gy, gxym) = c;
    gxy        = gy ^ sk;
    return gxym / gxy;
  }

}.

(** First we prove that the scheme is valid *)

lemma valid_ElGamal : hoare [ ValidScheme(ElGamal).main : true ==> res ].
proof.
  fun.
  inline ElGamal.kg ElGamal.enc ElGamal.dec.
  wp.
  rnd.
  wp.
  rnd.
  skip.
  simplify.
  intros &m1 x Hx y Hy.
  rewrite (group_pow_mult y x); rewrite (group_pow_mult x y). 
  rewrite (Int.Comm.Comm y x).
  rewrite (mul_div (g ^ (x * y)) (m{m1}));split.
save.

(* No we try to prove IND-CPA security *)

module type Inverter = { 
  fun inv (gx:group, gy:group, gz:group) : bool
}.

module DDH0 (I:Inverter) = { 
  fun main() : bool = {
    var x : int;
    var y : int;
    var d : bool;

    x  = $[0..q-1];
    y  = $[0..q-1];
    d  = I.inv(g^x, g^y, g^(x*y));

    return d;
  }     
}.

module DDH1(I:Inverter) = {
  fun main() : bool = {
    var x : int;
    var y : int;
    var z : int;
    var d : bool;

    x  = $[0..q-1];
    y  = $[0..q-1];
    z  = $[0..q-1]; 
    d  = I.inv(g^x, g^y, g^z);

    return d;
  }     
}.    

module Inv (A:Adv) : Inverter = { 
  fun inv (gx:group, gy:group, gz:group) : bool = {
    var m0 : plaintext;
    var m1 : plaintext; 
    var c : ciphertext;
    var b : bool;
    var b' : bool;
 
    (m0, m1)  = A.a1(gx);
    b         = ${0,1};
    c         = (gy, gz * (b ? m1 : m0));
    b'        = A.a2(c);
    return (b = b');
  }
}.

module G1(A:Adv) = { 
  fun main() : bool = {
    var x : int;
    var y : int;
    var z : int;
    var gx : group;
    var gy : group;
    var gz : group;
    var d  : bool;
    var b  : bool;
    var b' : bool;
    var m0 : plaintext;
    var m1 : plaintext;
    var c : ciphertext;
 
    x         = $[0..q-1];
    y         = $[0..q-1];
    gx        = g^x;
    gy        = g^y;
    (m0, m1)  = A.a1 (gx);
    b         = ${0,1};
    z         = $[0..q-1];
    gz        = g^z;
    c         = (gy, gz * (b ? m1 : m0) );
    b'        = A.a2 (c);

    return (b = b');
  }
}.

module G2(A:Adv) = {
  fun main () : bool = { 
    var x : int;
    var y : int;
    var z : int;
    var gx : group;
    var gy : group;
    var gz : group;
    var d  : bool;
    var b  : bool;
    var b' : bool;
    var m0 : plaintext;
    var m1 : plaintext;
    var c : ciphertext;
  
    x         = $[0..q-1];
    y         = $[0..q-1];
    gx        = g^x;
    gy        = g^y;
    (m0, m1)  = A.a1(gx);
    z         = $[0..q-1];
    gz        = g^z;
    c         = (gy, gz); 
    b'         = A.a2 (c);
    b         = ${0,1};

    return (b = b');
  }
}.
 
equiv equiv1 (A<:Adv) :  
   CPA(ElGamal,A).main ~ DDH0(Inv(A)).main : 
      (glob A){1}=(glob A){2} ==> res{1} = res{2}.
proof.
 fun.
 inline ElGamal.kg ElGamal.enc Inv(A).inv.
 wp.
 call (c{1} = c{2} /\ (glob A){1} = (glob A){2}) (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
 fun true;try (simplify;split).
 swap{1} 7 -5. 
 wp;rnd.
 call (pk{1} = pk{2} /\ (glob A){1} = (glob A){2}) (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
 fun true;try (simplify;split).
 wp; *rnd;skip. simplify;trivial. 

(* Just to test tactic *)
(* intros &m1 &m2 Heq.
 subst;simplify.
 intros x Hx y Hy rL rR A0 A1 H;elim H;clear H; intros H1 H2.
 subst.
 elimT tuple2_ind rR.
 intros a b _;simplify.
 intros b1 _;split.
 trivial.
 intros _ r1L r2L A0 A2 H;elim H;clear H;intros H1 H2.
 subst;simplify.
 split. *)
save.

lemma Pr1 (A<:Adv) &m : 
   Pr[CPA(ElGamal,A).main() @ &m : res] = 
   Pr[DDH0(Inv(A)).main() @ &m : res].
proof.
 equiv_deno (equiv1 (<:A));trivial.
save.

lemma Pr2 (A<:Adv) &m : 
   Pr[G1(A).main() @ &m : res] = 
   Pr[DDH1(Inv(A)).main() @ &m : res].
proof.
 equiv_deno (_: (glob A){1}=(glob A){2} ==> res{1} = res{2});try trivial.
  fun. inline{2} Inv(A).inv.
  swap{1} 7 -4;wp.
  call (c{1} = c{2} /\ (glob A){1} = (glob A){2})
      (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
    fun true;try (simplify;split).
  wp;rnd.
  call (pk{1} = pk{2} /\ (glob A){1} = (glob A){2}) 
             (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
    fun true;try (simplify;split).
  wp;*rnd;skip;trivial. 
save.

lemma Fact3 (A<:Adv) &m : 
  Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].
proof.
 equiv_deno (_: (glob A){1}=(glob A){2} ==> res{1} = res{2});try trivial.
 fun. 
 swap{2} 10 -4;wp.
 call (c{1} = c{2} /\ (glob A){1} = (glob A){2})
      (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
    fun true;try (simplify;split).
 wp; rnd (lambda (z:int), (z + log(if b then m1 else m0){2}) %% q)
     (lambda (z:int), (z - log(if b then m1 else m0){2}) %% q).
 wp;rnd;simplify.
 call (pk{1} = pk{2} /\ (glob A){1} = (glob A){2}) 
             (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
   fun true;try (simplify;split).
 wp;*rnd;skip; progress trivial.
save.

require import Real.

lemma Pr4_aux (A<:Adv) :
   (bd_hoare[A.a1 : true ==> true] = 1%r) =>
   (bd_hoare[A.a2 : true ==> true] = 1%r) =>
   bd_hoare [G2(A).main : true ==> res] <= (1%r / 2%r)
(*   Pr[G2(A).main() @ &m : res] = 1%r / 2%r *).
proof.
 intros Ha1 Ha2.
 fun.
 rnd (1%r / 2%r) (lambda b,  b = b'). 
 admit.
save.

lemma Pr4 (A<:Adv) &m : 
   (bd_hoare[A.a1 : true ==> true] = 1%r) =>
   (bd_hoare[A.a2 : true ==> true] = 1%r) =>
   Pr[G2(A).main() @ &m : res] = 1%r / 2%r.
proof.
 admit. (* TODO : how to use the previous lemma to do this *)
save.

lemma Conclusion1 (A<:Adv) &m : 
   (bd_hoare[A.a1 : true ==> true] = 1%r) =>
   (forall &m, bd_hoare[A.a2 : true ==> true] = 1%r) =>
 `| Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r / 2%r | = 
 `| Pr[DDH0(Inv(A)).main() @ &m :res] - Pr[DDH1(Inv(A)).main() @ &m :res] |.
proof. 
  intros Ha1 Ha2.
  rewrite (Pr1 (<:A) &m).
  rewrite <- (Pr4 (<:A) &m _ _);try assumption.
  rewrite <- (Fact3 (<:A) &m).
  rewrite (Pr2 (<:A) &m);trivial.
save.

lemma Conclusion (A<:Adv) &m :
   (bd_hoare[A.a1 : true ==> true] = 1%r) =>
   (bd_hoare[A.a2 : true ==> true] = 1%r) =>
   exists (I<:Inverter), 
   `| Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r / 2%r | = 
   `| Pr[DDH0(I).main() @ &m :res] - Pr[DDH1(I).main() @ &m :res] |.
proof.
  intros Ha1 Ha2.
  exists (<:Inv(A)).
  apply (Conclusion1 (<:A) &m _ _);assumption.
save.

