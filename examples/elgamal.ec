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

    (sk,pk) := S.kg();
    c       := S.enc(pk, m);
    d       := S.dec(sk, c); 

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

    (sk,pk) := S.kg();
    (m0,m1) := A.a1(pk);
    b        = ${0,1};
    c       := S.enc(pk, b ? m1 : m0);
    b'      := A.a2(c);
 
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

lemma valid_ElGamal : hoare [ ValidScheme(ElGamal).main : true ==> res ]
proof.
  fun.
  inline ElGamal.kg ElGamal.enc ElGamal.dec.
  wp.
  rnd. (* Bizare d'appeller la variable x (plutot que y) *)
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
    d := I.inv(g^x, g^y, g^(x*y));

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
    d := I.inv(g^x, g^y, g^(x*y));

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
 
    (m0, m1) := A.a1(gx);
    b         = ${0,1};
    c         = (gy, gz * (b ? m1 : m0));
    b'       := A.a2(c);
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
    (m0, m1) := A.a1 (gx);
    b         = ${0,1};
    z         = $[0..q-1];
    gz        = g^z;
    c         = (gy, gz * (b ? m1 : m0) );
    b'       := A.a2 (c);

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
    (m0, m1) := A.a1(gx);
    z         = $[0..q-1];
    gz        = g^z;
    c         = (gy, gz); 
    b'        := A.a2 (c);
    b         = ${0,1};

    return (b = b');
  }
}.
 
lemma equiv1 : forall (A<:Adv), 
  equiv[CPA(ElGamal,A).main ~ DDH0(Inv(A)).main : 
         (glob A){1}=(glob A){2} ==> res{1} = res{2} ]
proof.
 intros A;fun.         
 inline ElGamal.kg ElGamal.enc Inv(A).inv.
 wp.
 call (c{1} = c{2} /\ (glob A){1} = (glob A){2}) (res{1}=res{2} /\ (glob A){1} = (glob A){2}).
 fun true;try (simplify;split).
 wp.
(*
 simplify.
 : equiv [A2.a2 ~ A2.a2 : 
claim Pr1 : INDCPA.Main[res] = DDH0.Main[res] 
auto.
       
claim Pr2 : G1.Main[res] = DDH1.Main[res] 
auto.

timeout 3.

equiv Fact3 : G1.Main ~ G2.Main : (true).
 swap{2} [10-10] -4;auto.
 rnd ((z + log(if b then m0 else m1){2}) %% q), 
     ((z - log(if b then m0 else m1){2}) %% q).
 trivial; auto; trivial.
save.

claim Pr3 : G1.Main[res] = G2.Main[res]
using Fact3.

claim Pr4 : G2.Main[res] = 1%r / 2%r
compute.

claim Conclusion : 
 | INDCPA.Main[res] - 1%r / 2%r | = | DDH0.Main[res] - DDH1.Main[res] |.

*)