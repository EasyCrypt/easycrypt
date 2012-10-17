type pkey.
type skey.
type ciphertext.

cnst j, k : int.
cnst eps : real.

op nth : (bitstring{k}, int) -> int.
op [**] : (ciphertext, ciphertext) -> ciphertext as otimes.
op dec : (skey, ciphertext) -> int.
op key_pair : (pkey, skey) -> bool.

pop KG : () -> pkey * skey.
pop enc : (pkey, int) -> ciphertext.
pop Lap : (int, int, real) -> int.

axiom Lap(v1:int, k:int, eps:real, v2:int) :
  x1 = Lap(v1, k, eps) ~ x2 = Lap(v2, k, eps) :
  |v1 - v2| <= k  ==[exp(eps);0%r]==> x1 = x2.

axiom wp2_KG() : kp = KG() ~ kp' = KG() : 
  true ==[1%r;0%r]==> key_pair(fst(kp), snd(kp)) && kp = kp'.

aspec wp_enc(pk:pkey, sk:skey, a:int) : x = enc(pk,a) :
  key_pair(pk, sk) ==> dec(sk, x) = a.


axiom wp2_enc(pk1,pk2:pkey, sk:skey, a:int,a':int) : x = enc(pk1, a) ~ y = enc(pk2, a'): 
  a = a' && pk1 = pk2 && key_pair(pk1, sk) ==> dec(sk, x) = a && x = y.

axiom dec_homo : 
  forall (x,y:ciphertext, pk:pkey, sk:skey), 
    key_pair(pk, sk) => dec(sk, x ** y) = dec(sk, x) + dec(sk, y).

axiom eps_pos : 0%r <= eps.


axiom nth_bool : forall (v:bitstring{k}, i:int), nth(v, i) = 0 || nth(v, i) = 1. 

pred adjacent(v1,v2:bitstring{k}, j:int) = 
 forall (i:int), i <> j => nth(v1, i) = nth(v2, i).


adversary 
 B(pk:pkey, enc_vA,enc_vA':ciphertext list, enc_nB:ciphertext, nB,h:int) : bool {}.

game SIMCDP_1 = {
  var vA, vB : bitstring{k}
  var pk : pkey

  abs B = B { }

  fun f(v:bitstring{k}, sk:skey) : 
   ciphertext list * ciphertext list * ciphertext * int * int = {
    var x, y, c, enc_nA, enc_nB : ciphertext;
    var nA, nB : int; 
    var enc_vA, enc_vA' : ciphertext list = [];
    var i, h : int = 0;
    c = enc(pk, 0); 
    while (i <= k) {
      x = enc(pk, nth(v, i));
      y = enc(pk, 1 - nth(v, i));
      enc_vA  = x :: enc_vA;
      enc_vA' = y :: enc_vA';
      if (nth(vB, i) = 1) {
        c = c ** x;
      } else {
        c = c ** y;
      }
      i = i + 1;
    }
    nB = Lap(0, 1, eps);
    enc_nB = enc(pk, nB);
    c = c ** enc_nB;
    h = Lap(dec(sk, c), 1, eps);
    return (enc_vA, enc_vA', enc_nB, nB, h);
  }

  fun Main() : bool = {
    var _enc_nB : ciphertext;
    var _enc_vA, _enc_vA' : ciphertext list;
    var _nB, _h : int; 
    var b : bool;
    var kp : pkey * skey;
    kp = KG();
    pk = fst(kp);
    (_enc_vA, _enc_vA', _enc_nB, _nB, _h) = f(vA, snd(kp));
    b = B(pk, _enc_vA, _enc_vA', _enc_nB, _nB, _h);
    return b;
  }
}.

game SIMCDP_2 = {
  var vA, vB : bitstring{k}
  var pk : pkey
  
  abs B = B { }

  fun F(v:bitstring{k}, sk:skey) : 
   ciphertext list * ciphertext list * ciphertext * int * int = {
    var x, y, c, enc_nA, enc_nB : ciphertext;
    var nA, nB : int; 
    var enc_vA, enc_vA' : ciphertext list = [];
    var i, h : int = 0;
    while (i <= k) {
      x = enc(pk, 0);
      y = enc(pk, 0);
      enc_vA  = x :: enc_vA;
      enc_vA' = y :: enc_vA';
      if (nth(vB, i) = 1) {
        h = h + nth(v, i);
      } else {
        h = h + (1 - nth(v, i));
      }
      i = i + 1;
    }
    nB = Lap(0, 1, eps);
    enc_nB = enc(pk, 0);
    h = Lap(h + nB, 1, eps);
    return (enc_vA, enc_vA', enc_nB, nB, h);
  }

  fun Main() : bool = {
    var _sk : skey;
    var _enc_nB : ciphertext;
    var _enc_vA, _enc_vA' : ciphertext list;
    var _nB, _h : int; 
    var b : bool;
    var kp : pkey * skey;
    kp = KG();
    pk = fst(kp);
    (_enc_vA, _enc_vA', _enc_nB, _nB, _h) = F(vA, snd(kp));
    b = B(pk, _enc_vA, _enc_vA', _enc_nB, _nB, _h);
    return b;
  }
}.

game INDCPA_1 = {
  var vA, vB : bitstring{k}
  var pk : pkey

  abs B = B { }

  fun Enc(n:int) : ciphertext = {
    var c : ciphertext = enc(pk, n);
    return c;
  }

  fun A() : bool = {
    var x, y, c, enc_nA, enc_nB : ciphertext;
    var nA, nB : int; 
    var enc_vA, enc_vA' : ciphertext list = [];
    var i, h : int = 0;
    var b : bool;
    while (i <= k) {
      x = Enc(nth(vA, i));
      y = Enc(1 - nth(vA, i));
      enc_vA  = x :: enc_vA;
      enc_vA' = y :: enc_vA';
      if (nth(vB, i) = 1) {
        h = h + nth(vA, i);
      } else {
        h = h + (1 - nth(vA, i));
      }
      i = i + 1;
    }
    nB = Lap(0, 1, eps);
    enc_nB = Enc(nB);
    h = Lap(h + nB, 1, eps);
    b = B(pk, enc_vA, enc_vA', enc_nB, nB, h);
    return b;
   }

  fun Main() : bool = {
    var b : bool;
    var kp : pkey * skey;
    kp = KG();
    pk = fst(kp);
    b = A();
    return b; 
  }
}.

game INDCPA_2 = INDCPA_1 where 
  Enc = {
    var c : ciphertext = enc(pk, 0);
    return c;
  }.

prover "alt-ergo", cvc3.

equiv SIMCDP_INDCPA_1 : SIMCDP_1.Main ~ INDCPA_1.Main : ={vA,vB} ==> ={res}.
 inline{1} f.
 inline{2} A.
 inline{2} Enc. wp.
 auto.
 rnd.
 wp.
 apply: wp2_enc(pk{1}, pk{2}, sk{1}, nB{1}, n{2}).
 trivial.
 while:
  (={vA,vB,pk,kp,enc_vA,enc_vA',i} && v{1} = vA{2} && key_pair(pk{1}, sk{1}) &&
   dec(sk{1}, c{1}) = h{2}).
 inline{2} Enc.
 wp.
 apply: wp2_enc(pk{1}, pk{2}, sk{1}, 1 - nth(v{1}, i{1}), n_1{2}).
 wp.
 apply: wp2_enc(pk{1}, pk{2}, sk{1}, nth(v{1}, i{1}), n_0{2}).
 trivial.
 apply{1}: wp_enc(pk{1},sk{1},0).
wp.
 apply: wp2_KG().
trivial.
save.






equiv SIMCDP_INDCPA_2 : SIMCDP_2.Main ~ INDCPA_2.Main : ={vA,vB} ==> ={res}.
 inline{1} F; inline{2} A.
 inline{2} Enc.
 auto;trivial.
 while : (={vA,vB,pk,kp,enc_vA,enc_vA',i,h} && v{1} = vA{2}).
 inline{2} Enc; trivial.
 trivial.
 save.

claim slack_1 : SIMCDP_1.Main[res] = INDCPA_1.Main[res]
using SIMCDP_INDCPA_1.

claim slack_2 : SIMCDP_2.Main[res] = INDCPA_2.Main[res]
using SIMCDP_INDCPA_2.

claim slack : 
  | SIMCDP_1.Main[res] - SIMCDP_2.Main[res] | = 
  | INDCPA_1.Main[res] - INDCPA_2.Main[res] |.


equiv F_DP : SIMCDP_2.F ~ SIMCDP_2.F : 
 adjacent(v{1},v{2},j) && ={vB,pk,sk} ==[exp(eps);0%r]==> ={res}.
 apply: Lap(h{1} + nB{1}, 1, eps, h{2} + nB{2}); trivial.
 while : (adjacent(v{1},v{2},j) && ={vB,pk,sk,enc_vA,enc_vA',i} &&
  if i{1} <= j then h{1} = h{2} else h{1} - h{2} <= 1 && h{2} - h{1} <= 1); trivial.
save.


