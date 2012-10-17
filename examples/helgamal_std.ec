(* 
** We prove that Hashed ElGamal is IND-CPA secure in the standard model
** under the assumptions that the underlying family of hash functions 
** is entropy-smoothing and the hardness of the DDH problem 
*)

prover "alt-ergo".

type group. 
type hkey.      (* Hash keys *)
type state.

cnst k : int.   (* Message size *)
cnst q : int.   (* Order of the group *)
cnst g : group. (* A generator *)

op [^] : (group, int) -> group as pow. 

op H : (hkey, group) ->  bitstring{k}. (* The family of hash functions *)

pop KG_h : () -> hkey. (* Key generation *)

axiom pow_mul : forall (x, y:int), (g ^ x) ^ y = g ^ (x * y).

(** Various type-synonyms used in the proof *)
type pkey    = hkey * group.
type skey    = hkey * int.
type message = bitstring{k}.
type cipher  = group * bitstring{k}.

adversary A1(pk:pkey)           : message * message * state { }.
adversary A2(s:state, c:cipher) : bool { }.

game INDCPA = {
  fun KG() : skey * pkey = {
    var x : int = [0..q-1];
    var hk : hkey = KG_h();
    return ((hk, x), (hk, g ^ x));
  } 

  fun Enc(pk:pkey, m:message): cipher = {
    var y : int = [0..q-1];
    var alpha : group;
    var hk1 : hkey;
    var h : message;
    (hk1, alpha) = pk;
    h = H(hk1, alpha ^ y);
    return (g ^ y, h ^^ m);
  }

  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun Main() : bool = {
    var sk : skey;
    var pk : pkey;
    var k1,k2 : hkey;
    var x1 : int;
    var alpha : group;
    var m0, m1 : message;
    var c : cipher;
    var b, b' : bool;
    var s : state;
    (sk, pk) = KG();
    (m0, m1, s) = A1(pk);
    b = {0,1};
    c = Enc(pk, b ? m0 : m1);
    b' = A2(s, c);
    return b = b';
  }
}.

game DDH0 = {
  abs A1 = A1 {}
  abs A2 = A2 {}

  fun B (alpha, beta, gamma : group) : bool = {
    var m0, m1, h : message;
    var b, b' : bool;
    var s : state;
    var hk : hkey = KG_h();
    (m0, m1, s) = A1((hk, alpha));
    b = {0,1};
    h = H(hk, gamma);
    b' = A2(s, (beta, h ^^ (b ? m0 : m1)));
    return b = b';
  }
  
  fun Main () : bool = {
    var x, y : int;
    var d : bool;
    x = [0..q-1];
    y = [0..q-1];
    d = B(g ^ x, g ^ y, g ^ (x * y));
    return d;
  }
}.

game DDH1 = DDH0 
  where Main = { 
    var x, y, z : int;
    var d : bool;
    x = [0..q-1];
    y = [0..q-1];
    z = [0..q-1];
    d = B(g ^ x, g ^ y, g ^ z);
    return d;
  }.

game ES0 = {
  abs A1 = A1 {}
  abs A2 = A2 {}

  fun D(hk1:hkey, h:bitstring{k}) : bool = {
    var x, y :int;
    var m0, m1 : message;
    var b, b' : bool;
    var s : state;
    x = [0..q-1];
    y = [0..q-1];
    (m0, m1, s) = A1((hk1, g ^ x));
    b = {0,1};
    b' = A2(s, (g ^ y, h ^^ (b ? m0 : m1)));
    return b = b';
  }

  fun Main() : bool = {
    var h : bitstring{k};
    var d : bool;
    var hk : hkey = KG_h();
    h = {0,1}^k;
    d = D(hk, h);
    return d;
  }
}.

game ES1 = ES0 
  where Main = {
    var z : int;
    var d : bool;
    var hk : hkey = KG_h();
    z = [0..q-1];
    d = D(hk, H(hk, g ^ z));
    return d;
  }.

game G_half = {
  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun Main () : bool = {
    var x, y : int;
    var b, b' : bool;
    var h : bitstring{k};
    var m0, m1 : message;
    var s : state;
    var hk : hkey = KG_h();
    x = [0..q-1];
    y = [0..q-1];
    (m0, m1, s) = A1((hk, g ^ x));
    h = {0,1}^k;
    b' = A2(s, (g ^ y, h));
    b = {0,1};
    return b = b';
  }
}.

equiv ES0_G_half : ES0.Main ~ G_half.Main : true ==> ={res}.
proof.
 inline{1} D.
 swap{2} -2; swap{1} 2 1; swap{1} [3-4] 4; auto.
 rnd (h ^^ (if b then m0 else m1){2}).
 rnd; auto; trivial.
save.

claim claim1 : INDCPA.Main[res] = DDH0.Main[res]
auto.

claim claim2 : DDH1.Main[res] = ES1.Main[res]
auto.

claim claim3 : ES0.Main[res] = G_half.Main[res]
using ES0_G_half.

claim claim4 : G_half.Main[res] = 1%r/2%r
compute.

claim Conclusion : 
  | INDCPA.Main[res] - 1%r/2%r | <= 
  | DDH0.Main[res] - DDH1.Main[res] | + | ES0.Main[res] - ES1.Main[res] |.
