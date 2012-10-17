prover "alt-ergo", cvc3.
timeout 1.

type group.

cnst q    : int.
cnst g    : group.
cnst k    : int.

type skey    = int.
type pkey    = group.
type key     = skey * pkey.
type message = bitstring{k}.
type cipher  = group * bitstring{k}.

op [^]  : (group, int) -> group   as pow.

axiom pow_mul : 
  forall (x, y:int), 
    (g ^ x) ^ y = g ^ (x * y).

adversary A1(pk:pkey)  : message * message { group -> message}.
adversary A2(c:cipher) : bool              { group -> message}.

game INDCPA = {
  var L  : (group, bitstring{k}) map
  var LA : group list

  fun H(x:group) : message = {
    var h : message = {0,1}^k;
    if (!in_dom(x,L)) { L[x] = h; }
    return L[x];
  }
   
  fun H_A(x:group) : message = {
    var m : message;
    LA = x :: LA;
    m = H(x);
    return m;
  }

  fun KG() : key = {
    var pk : int = [0..q-1];
    return (pk, g ^ pk);
  } 

  fun Enc(pk:pkey, m:message): cipher = {
    var y : int = [0..q-1];
    var he : message;
    he = H(pk ^ y);
    return (g ^ y, he ^^ m);
  }

  abs A1 = A1 {H_A}
  abs A2 = A2 {H_A}
  
  fun Main() : bool = {
    var sk : skey;
    var pk : pkey;
    var m0, m1 : message;
    var c : cipher;
    var b, b' : bool;

    L = empty_map;
    LA = [];
    (sk,pk) = KG();
    (m0,m1) = A1(pk);
    b = {0,1};
    c = Enc(pk, b? m0 : m1);
    b' = A2(c);
    return (b = b');
  }
}.

game G1 = INDCPA 
  var y' : group
  where  Main = {
    var m0, m1 : message;
    var c : cipher;
    var b, b' : bool;
    var x, y : int;
    var hy : message;
    var alpha : group;

    L = empty_map;
    LA = [];
    x = [0..q-1]; alpha = g ^ x; 
    y = [0..q-1]; y' = alpha ^ y;
    (m0,m1) = A1(alpha);
    b = {0,1};
    hy = H(y');
    b' = A2((g ^ y, hy ^^ (b? m0 : m1)));
    return b = b';
  }.

equiv CPA_G1_H : INDCPA.H ~ G1.H : (={L,LA}).
proof.
 trivial.
save.

equiv CPA_G1_H_A : INDCPA.H_A ~ G1.H_A : (={L,LA}).
proof.
 call using CPA_G1_H.
 trivial.
save.

equiv CPA_G1_A1 : INDCPA.A1 ~ G1.A1 : (={L,LA}) by auto using CPA_G1_H_A.

equiv CPA_G1_A2 : INDCPA.A2 ~ G1.A2 : (={L,LA}) by auto using CPA_G1_H_A.

equiv CPA_G1 : INDCPA.Main ~ G1.Main : true ==> ={res}.
proof.
 inline{1} KG, Enc.
 derandomize.
 call using  CPA_G1_A2.
 wp.
 call using  CPA_G1_H.
 wp.
 call using CPA_G1_A1.
 wp.
 swap{1} -1.
 *rnd.
 trivial.
save.

claim Pr1 : INDCPA.Main[res] = G1.Main[res]
using CPA_G1.

(* Fix the value of H(y'), apply Fundamental Lemma *)
game G2 = G1 
  where Main = {
    var m0, m1 : message;
    var c : cipher;
    var b, b' : bool;
    var x, y : int;
    var h : message;
    var alpha : group;

    L = empty_map;
    LA = [];
    x = [0..q-1]; alpha = g ^ x; 
    y = [0..q-1]; y' = alpha ^ y;
    (m0,m1) = A1(alpha);
    b = {0,1};
    h = {0,1}^k;
    b' = A2((g ^ y, h ^^ (b? m0 : m1)));
    return (b = b');
  }.

equiv G1_G2_H_A :  G1.H_A ~ G2.H_A : 
 ( ={y',L,LA} && (in_dom(y',L){1} => mem(y',LA){1} )).
proof.
 inline H.
 trivial.
save.

equiv G1_G2_A1 : G1.A1 ~ G2.A1 :
 ( ={y',L,LA} && (in_dom(y',L){1} => mem(y',LA){1} )) by auto using G1_G2_H_A.
  
equiv G1_G2_H_A : G1.H_A ~ G2.H_A : 
  upto (mem(y',LA)) 
  with ( ={y',LA} &&
    forall (w:group), 
      w <> y'{1} => (L{1}[w] = L{2}[w] && (in_dom(w,L){1} <=> in_dom(w,L){2})) ). 
proof.
 inline H.
 trivial.
save.

equiv G1_G2_A2 : G1.A2 ~ G2.A2 : 
  upto (mem(y',LA)) 
  with ( ={y',LA} &&
    forall (w:group), 
      w <> y'{1} => (L{1}[w] = L{2}[w] && (in_dom(w,L){1} <=> in_dom(w,L){2})) ) 
by auto using G1_G2_H_A.

equiv Fact2 : G1.Main ~ G2.Main : 
 true ==>  
    mem(y',LA){1} = mem(y',LA){2} && (!mem(y',LA){1} => ={res}).
 call using G1_G2_A2.
 inline H.
 wp.
 rnd.
 wp.
 rnd.
 call using G1_G2_A1.
 trivial.
save.

claim Pr2 : | G1.Main[res] - G2.Main[res] | <= G2.Main[mem(y',LA)]
using Fact2.


(* Remove dependance on mb using optimistic sampling *)
game G3 = G2 
  where Main = {
    var m0, m1 : message;
    var b, b' : bool;
    var x, y : int;
    var h : message;
    var alpha : group;

    L = empty_map;
    LA = [];
    x = [0..q-1]; alpha = g ^ x;
    y = [0..q-1]; y' = alpha ^ y;
    (m0,m1) = A1(alpha);
    h = {0,1}^k;
    b' = A2((g ^ y, h));
    b = {0,1};
    return (b = b');
  }. 

equiv G2_G3_H_A : G2.H_A ~ G3.H_A : (={L,LA}).
 inline H.
 trivial.
save.

equiv G2_G3_A1 : G2.A1 ~ G3.A1 : (={L,LA}) by auto using G2_G3_H_A.

equiv G2_G3_A2 : G2.A2 ~ G3.A2 : (={L,LA}) by auto using G2_G3_H_A.

equiv Fact3 : G2.Main ~ G3.Main : true ==> ={res,y',LA}.
 swap{2} -2.
 call using G2_G3_A2.
 rnd (h ^^ (if b then m0 else m1){2}).
 rnd.
 call using G2_G3_A1.
 trivial. 
save.

claim Pr3_1 : G2.Main[res] = G3.Main[res] 
using Fact3.

claim Pr3_2 : G2.Main[mem(y',LA)] = G3.Main[mem(y',LA)]
using Fact3.

claim Pr3_3 : G3.Main[res] = 1%r / 2%r 
compute.


(* Build an adversary against LCDH *)
game LCDH = {
  var L : (group, bitstring{k}) map
  var LA : group list

  fun H(x:group) : message = {
    var h : message = {0,1}^k;
    if (! in_dom(x, L) ) { L[x] = h; }
    return L[x];
  }
   
  fun H_A(x:group) : message = {
    var m : message;
    LA = x :: LA;
    m = H(x);
    return m;
  }
       
  abs A1 = A1 {H_A}
  abs A2 = A2 {H_A}
  
  fun B(gx:group, gy:group) : group list = {
    var m0, m1 : message;
    var h : message;
    var b' : bool;

    L = empty_map;
    LA = [];
    (m0,m1) = A1(gx);
    h = {0,1}^k;
    b' = A2((gy, h));
    return LA;
  }

  fun Main() : bool = {
   var x, y : int;
   var L' : group list;
   x = [0..q-1]; y = [0..q-1];
   L' = B(g ^ x, g ^ y);
   return (mem(g ^ (x * y), L'));
  }
}. 

equiv G3_LCDH_H_A : G3.H_A ~ LCDH.H_A : (={L,LA}).
inline H.
trivial.
save.

equiv G3_LCDH_A1 : G3.A1 ~ LCDH.A1 : (={L,LA}) by auto using G3_LCDH_H_A.

equiv G3_LCDH_A2 : G3.A2 ~ LCDH.A2 : (={L,LA}) by auto using G3_LCDH_H_A.

equiv G3_LCDH : G3.Main ~ LCDH.Main : true ==> mem(y',LA){1} = res{2}.
inline{2} B.
rnd{1}.
wp.
call using G3_LCDH_A2.
rnd.
call using G3_LCDH_A1.
wp.
rnd.
wp.
rnd.
wp.
trivial.
save.

claim Pr4 : G3.Main[mem(y',LA)] = LCDH.Main[res] 
using  G3_LCDH.

claim Conclusion : | INDCPA.Main[res] - 1%r/2%r | <= LCDH.Main[res].

