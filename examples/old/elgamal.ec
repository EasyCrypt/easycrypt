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
 forall (z:int), g ^ (z %% q) = g ^ z.

axiom mod_add : 
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small : 
 forall (x:int), 0 <= x => x < q => x%%q = x.

lemma nosmt mod_sub : 
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q
by [].

lemma nosmt mod_bound : 
 forall (x:int), 0 <= x%%q && x%%q < q
by [].

axiom mul_div : forall (g1 g2:group), (g1 * g2) / g1 = g2.

module type Adv = { 
  fun a1(pk:pkey)      : plaintext * plaintext {*}
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
    var (sk,pk) : skey * pkey;
    var m0,m1   : plaintext;
    var c       : ciphertext;
    var b,b'    : bool;

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
    var x : int;
    x = $[0..q-1];
    return (x, g^x);
  }

  fun enc(pk:pkey, m:plaintext) : ciphertext = {
    var y : int;
    y = $[0..q-1];
    return (g^y, (pk^y) * m);
  }

  fun dec(sk:skey, c:ciphertext) : plaintext = {
    var gxy,gy,gxym : group;
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
  do (wp;rnd); skip => /= &m1 x Hx y Hy.
  rewrite (group_pow_mult y x); rewrite (group_pow_mult x y). 
  rewrite (Int.Comm.Comm y x).
  rewrite (mul_div (g ^ (x * y)) (m{m1}));split.
save.

(* No we prove IND-CPA security *)

module type Inverter = { 
  fun inv (gx:group, gy:group, gz:group) : bool
}.

module DDH0 (I:Inverter) = { 
  fun main() : bool = {
    var x,y : int;
    var d : bool;

    x  = $[0..q-1];
    y  = $[0..q-1];
    d  = I.inv(g^x, g^y, g^(x*y));

    return d;
  }     
}.

module DDH1(I:Inverter) = {
  fun main() : bool = {
    var x,y,z : int;
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
    var m0,m1 : plaintext;
    var c     : ciphertext;
    var b,b'  : bool;
 
    (m0, m1)  = A.a1(gx);
    b         = ${0,1};
    c         = (gy, gz * (b ? m1 : m0));
    b'        = A.a2(c);
    return (b = b');
  }
}.

module G1(A:Adv) = { 
  fun main() : bool = {
    var x,y,z    : int;
    var gx,gy,gz : group;
    var d,b,b'   : bool;
    var m0,m1    : plaintext;
    var c        : ciphertext;
 
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
    var x,y,z    : int;
    var gx,gy,gz : group;
    var d,b,b'   : bool;
    var m0,m1    : plaintext;
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
 
equiv equiv1_A2 (A<:Adv) : A.a2 ~ A.a2 : ={c, glob A} ==> ={res, glob A}.
proof.
  fun true;trivial.
save.

equiv equiv1 (A<:Adv) :  
   CPA(ElGamal,A).main ~ DDH0(Inv(A)).main : 
      true ==> res{1} = res{2}.
proof.
  fun.
  inline ElGamal.kg ElGamal.enc Inv(A).inv.
  wp.
  call (equiv1_A2 A).
  swap{1} 7 -5. 
  wp;rnd.
  call (_ : true).
  wp; do rnd; skip. 
  by smt. 
save.

lemma Pr1 (A<:Adv) &m : 
   Pr[CPA(ElGamal,A).main() @ &m : res] = 
   Pr[DDH0(Inv(A)).main() @ &m : res].
proof.
  by equiv_deno (equiv1 (A)); trivial.
save.

lemma Pr2 (A<:Adv) &m : 
   Pr[G1(A).main() @ &m : res] = 
   Pr[DDH1(Inv(A)).main() @ &m : res].
proof.
  equiv_deno (_: true ==> ={res});trivial.
  fun. inline{2} Inv(A).inv.
  swap{1} 7 -4;wp.
  call (equiv1_A2 A).
  wp;rnd.
  call (_ : true).
  by wp;do rnd.
save.

lemma Fact3 (A<:Adv) &m : 
  Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].
proof.
  equiv_deno (_: true ==> ={res});try trivial.
  fun. 
  swap{2} 10 -4;wp.
  call (equiv1_A2 A).
  wp; rnd (lambda (z:int), (z + log(if b then m1 else m0){2}) %% q)
     (lambda (z:int), (z - log(if b then m1 else m0){2}) %% q).
  wp;rnd => /=.
  call ( _ : true).
  by wp;do rnd;skip;progress => //; smt.
save.

require import Real.

lemma Pr4_aux (A<:Adv) :
   (islossless A.a1) => (islossless A.a2) =>
   bd_hoare [G2(A).main : true ==> res] = (1%r / 2%r).
proof.
  intros Ha1 Ha2;fun.
  rnd ((=) b'); conseq  (_ : ==> true) .
    intros &m;progress.
    by apply (Dbool.mu_x_def (b'{m})).
  call Ha2.
  cut H1 : mu [0..Int.(-) q 1] Fun.cpTrue = 1%r by smt.
  wp; rnd Fun.cpTrue; conseq (_ : _ ==> true) => //.
  call Ha1.
  wp; rnd Fun.cpTrue; conseq (_ : _ ==> true) => //.
  by rnd Fun.cpTrue; conseq (_ : _ ==> true).
save.

lemma Pr4 (A<:Adv) &m : 
   (islossless A.a1) => (islossless A.a2) =>
   Pr[G2(A).main() @ &m : res] = 1%r / 2%r.
proof.
 intros Ha1 Ha2.
 by bdhoare_deno (Pr4_aux A _ _).
save.

lemma Conclusion1 (A<:Adv) &m : 
   (islossless A.a1) => (islossless A.a2) =>
 `| Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r / 2%r | = 
 `| Pr[DDH0(Inv(A)).main() @ &m :res] - Pr[DDH1(Inv(A)).main() @ &m :res] |.
proof. 
  intros Ha1 Ha2.
  by rewrite (Pr1 A &m) -(Pr4 A &m _ _) // -(Fact3 A &m) (Pr2 A &m).
save.

lemma Conclusion (A<:Adv) &m :
   (islossless A.a1) => (islossless A.a2) =>
   exists (I<:Inverter), 
   `| Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r / 2%r | = 
   `| Pr[DDH0(I).main() @ &m :res] - Pr[DDH1(I).main() @ &m :res] |.
proof.
  intros Ha1 Ha2; exists (Inv(A)).
  by apply (Conclusion1 A &m).
save.
