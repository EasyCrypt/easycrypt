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


claim Pr1 : INDCPA.Main[res] = G1.Main[res]
auto.

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



equiv G1_G2_A1 : G1.A1 ~ G2.A1 :
 ( ={y',L,LA} && (in_dom(y',L){1} => mem(y',LA){1} )) by auto.
  
equiv Fact2 : G1.Main ~ G2.Main : 
 true ==>  
    mem(y',LA){1} = mem(y',LA){2} && (!mem(y',LA){1} => ={res}).
 auto upto (mem(y',LA)) 
 with ( ={y',LA} &&
  forall (w:group), 
    w <> y'{1} => (L{1}[w] = L{2}[w] && (in_dom(w,L){1} <=> in_dom(w,L){2})) ) .
 trivial.
 call using G1_G2_A1;trivial.
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

equiv Fact3 : G2.Main ~ G3.Main : true ==> ={res,y',LA}.
 swap{2} -2; auto.
 rnd (h ^^ (if b then m0 else m1){2}); rnd; auto; trivial.
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

  fun H = INDCPA.H
  fun H_A = INDCPA.H_A
          
  fun A1 = INDCPA.A1
  fun A2 = INDCPA.A2
  
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

claim Pr4 : G3.Main[mem(y',LA)] = LCDH.Main[res] 
auto.

claim Conclusion : | INDCPA.Main[res] - 1%r/2%r | <= LCDH.Main[res].

