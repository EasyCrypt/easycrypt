cnst k : int.
cnst n : int.

type t.
type plaintext = bitstring{k}.
type ciphertext.
type skey.
type pkey.

adversary KG() : pkey * skey {}.

adversary A(pk:pkey) : bool 
 { 
  (plaintext, plaintext) -> ciphertext; 
  t -> plaintext; 
  (bitstring{k}, bitstring{n}) -> bitstring{k} 
 }.

adversary Enc(pk:pkey,m:plaintext) : ciphertext {t -> plaintext}.

adversary H(x:t) : plaintext {(plaintext, bitstring{n}) -> plaintext}.

adversary Sim(x:bitstring{k}, y:bitstring{n}) : bitstring{k} {t -> plaintext}.

game INDCPA' = {
 var b : bool
 var pk : pkey
 var LH : (t,plaintext) map

 fun H(x:t) : plaintext = {
   if (!in_dom(x,LH)) {
     LH[x] = {0,1}^k;
   }
   return LH[x];
 }

 abs KG = KG {}

 abs Enc = Enc {H}

 fun LR(m0, m1:plaintext) : ciphertext = {
   var c : ciphertext;
   c = Enc(pk, b ? m0 : m1);
   return c;
 }
 
 (** BEGIN A' *)
 abs f = Sim {H}

 abs A  = A {LR, H, f}

 fun A'(pk':pkey) : bool = {
   var b' : bool;
   b' = A(pk');
   return b';
 }
 (** END A'   *)

 fun Main () : bool = {
   var sk : skey;
   var b' : bool; 

   LH = empty_map;
   b = {0,1};
   (pk, sk) = KG();
   b' = A'(pk);
   return (b = b');
 }
}.


game INDCPA = {
 var b : bool
 var pk : pkey

 var L : (plaintext * bitstring{n}, plaintext) map

 fun f(x:bitstring{k}, y:bitstring{n}) : bitstring{k} = {
   if (!in_dom((x,y),L)) {
     L[(x,y)] = {0,1}^k;
   }
   return L[(x,y)];
 }

 abs H = H {f}

 abs KG = KG {}

 abs Enc = Enc {H}

 fun LR(m0, m1:plaintext) : ciphertext = {
   var c : ciphertext;
   c = Enc(pk, b ? m0 : m1);
   return c;
 }

 abs A = A {LR, H, f}

 fun Main () : bool = {
   var sk : skey;
   var b' : bool; 

   L = empty_map;
   b = {0,1};
   (pk, sk) = KG();
   b' = A(pk);
   return (b = b');
 }

}.

game Real = {
 var L : (plaintext * bitstring{n}, plaintext) map

 fun f(x:plaintext, y:bitstring{n}) : plaintext = {
   if (!in_dom((x,y),L)) {
     L[(x,y)] = {0,1}^k;
   }
   return L[(x,y)];
 }

 abs H = H {f}

 (* BEGIN D(H,f) *)
 var pk : pkey
 var b : bool

 abs KG = KG {}
 abs Enc = Enc {H}

 fun LR(m0, m1:plaintext) : ciphertext = {
   var c : ciphertext;
   c = Enc(pk, b ? m0 : m1);
   return c;
 }

 abs A = A {LR, H, f}

 fun D() : bool = {
   var sk : skey;
   var b' : bool;
   b = {0,1};
   (pk, sk) = KG();
   b' = A(pk);
   return (b = b');
 }
 (** END D(H,f)    *)

 fun Main() : bool = {
   var b' : bool;
   L = empty_map;
   b' = D();
   return b';
 }
}.

game Ideal = {
 var L : (t, plaintext) map

 fun H(x:t) : plaintext = {
   if (!in_dom(x,L)) {
     L[x] = {0,1}^k;
   }
   return L[x];
 }

 abs f = Sim {H}

 (** BEGIN D(H,f) *)
 var pk : pkey
 var b : bool

 abs KG = KG {}
 abs Enc = Enc {H}

 fun LR(m0, m1:plaintext) : ciphertext = {
   var c : ciphertext;
   c = Enc(pk, b ? m0 : m1);
   return c;
 }

 abs A = A {LR, H, f}

 fun D() : bool = {
   var sk : skey;
   var b' : bool;
   b = {0,1};
   (pk, sk) = KG();
   b' = A(pk);
   return (b = b');
 }
 (** END D(H,f)    *)

 fun Main() : bool = {
   var b' : bool;
   L = empty_map;
   b' = D();
   return b';
 }
}.

prover "alt-ergo".

equiv left  : INDCPA.Main ~ Real.Main : true ==> ={res}.
 inline{2} D; wp.
 app 3 3 ={b,pk,sk,L}.
 auto (true); trivial.
 auto.
save. 

equiv right_H : Ideal.H ~ INDCPA'.H : 
 ={b,pk,x} && L{1} = LH{2} ==> ={b,pk,res}.
 derandomize; trivial.
save.

equiv right : Ideal.Main ~ INDCPA'.Main : true ==> ={res}.
 inline{1} D; inline{2} A'; wp.
 app 3 4 ={b,pk,sk} && pk'{2} = pk{1} && L{1} = LH{2}.
 auto (true); trivial.
 auto (={b,pk} && L{1} = LH{2}).
save.

claim Pr_left : INDCPA.Main[res] = Real.Main[res]
 using left.

claim Pr_right : Ideal.Main[res] = INDCPA'.Main[res]
 using right.

claim conclusion : 
  | INDCPA.Main[res]  - 1%r / 2%r | <= 
  | INDCPA'.Main[res] - 1%r / 2%r | + 
  | Real.Main[res] - Ideal.Main[res] |.
