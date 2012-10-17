/*
** PSS.ec: Unforgeability under chosen-message attacks
** of the Probabilistic Signature Scheme.
**  
** Proposed originally by
** M. Bellare & P. Rogaway, "The exact security signatures - 
** How to Sign with RSA and Rabin in Advances" in Cryptology - 
** Eurocrypt 96 Proceedings, Lectures Notes in Computer Sciencia Vol. 1070.
** 
** The original scheme was proposed using two Hash functions and RSA and its 
** security was proved in the random-oracle model. 
**
** On the other hand, D. Pointcheval in his work "Provable Security for Public 
** Key Schemes" - Advances Courses CRM Barcelona, Spain - 2004 made a proof of 
** PSS in wich the signature process involves three Hash functions with a generic trapdoor one-way permutation.
**
** Here we rely on Pointcheval's work.
**
*/

/** Abstract types **/
type message;;
type key_pair;;
type secret_key;;
type public_key;;

/** Constants **/
cnst k0  : int;;   // msg length hash F 
cnst k1  : int;;   // msg length hash G and salt
cnst k2  : int;;   // msg length hash H
cnst k   : int;;   // msg length function f

/** Type abbreviations **/
type salt      = bitstring{k1};;
type msg_hash  = bitstring{k2};;
type g_hash    = bitstring{k1};;
type f_hash    = bitstring{k0};;
type msg_f     = bitstring{k};;
type signature = msg_f;;

/** Constants **/
cnst qH      : int;;            // allotted queries to the hash oracle
cnst qF      : int;;            // allotted queries to the hash oracle
cnst qG      : int;;            // allotted queries to the hash oracle
cnst qS      : int;;            // allotted queries to the signing oracle
cnst dummy   : message;;        // dummy message
cnst e       : msg_f;;          // identity element of f
cnst zero    : bitstring{k1};;  // identity element of xor




/** Operators **/
// Group
op (*)  : msg_f, msg_f -> msg_f  = group_mul;; // xor

// One-way permutation
op f    : public_key, msg_f -> msg_f = f;;
op finv : secret_key, msg_f -> msg_f = finv;;

// Keys 
op pkey : key_pair -> public_key = pkey;;
op skey : key_pair -> secret_key = skey;;    

// Reals
op (^)  : real, int -> real = real_pow;;

op xor : bitstring{k1}, bitstring{k1} ->  bitstring{k1} = xor;; // xor

op constr   : int, msg_hash, g_hash, f_hash -> msg_f  = constr;;
op splitstr : msg_f -> (int * (msg_hash * (g_hash * f_hash))) = splistr;;


/** Axioms **/
prover "alt-ergo";;

axiom qH_nat : { 0 <= qH };;
axiom qF_nat : { 0 <= qF };;
axiom qG_nat : { 0 <= qG };;
axiom qS_nat : { 0 < qS };;

axiom k_nat : { 0 <= k };;
axiom k_nat : { 0 <= k0 };;
axiom k_nat : { 0 <= k1 };;
axiom k_nat : { 0 <= k2 };;
axiom k_nat : { k == 1 + k0 + k1 + k2 };;

axiom finv_left : forall (x:msg_f, kp:key_pair). 
  { x == finv(skey(kp), f(pkey(kp), x)) };;

axiom finv_right : forall (x:msg_f, kp:key_pair). 
  { x == f(pkey(kp), finv(skey(kp), x)) };;

axiom group_mul_comm : forall (x:msg_f, y:msg_f). { x * y == y * x };; 

axiom group_mul_assoc : 
  forall (x:msg_f, y:msg_f, z:msg_f). { x * (y * z) == (x * y) * z };;

axiom group_mul_e_right : forall (x:msg_f). { x * e == x };;

axiom f_homo : forall (x:msg_f, y:msg_f, pk:public_key). 
  { f(pk, x) * f(pk, y) == f(pk, x * y) };;

axiom f_e : forall (pk:public_key). { f(pk, e) == e };;


unset f_homo, f_e, reduction;;

axiom xor_comm : 
 forall (x:bitstring{k1}, y:bitstring{k1}). { xor(x,y) == xor(y,x) };;

axiom xor_assoc :
 forall (x:bitstring{k1}, y:bitstring{k1}, z:bitstring{k1}).
  { xor(xor(x,y),z) == xor(x,xor(y,z)) };;

axiom xor_zero : 
 forall (x:bitstring{k1}). { xor(x,zero) == x };;

axiom xor_cancel : 
 forall (x:bitstring{k1}). { xor(x,x) == zero };;

axiom con_split : 
  forall (a:int, b:msg_hash, c:g_hash, d:f_hash, e:msg_f).
   { constr(a,b,c,d) == e} <=> {(a,(b,(c,d))) == splitstr(e)};;


/** Abstract procedures **/
adversary A(pk:public_key) : msg_f 
  { message, salt -> msg_hash; msg_hash->g_hash; msg_hash->f_hash; message -> signature };;

adversary KG() : key_pair {};; // Not really an adversary


/** Game definitions **/

/*
** Game EF:
**
** This is the standard experiment for an existential forgery under a
** chosen-message attack against PFDH
*/
game EF = {
  var pk : public_key
  var sk : secret_key
  var Hl  : (message * salt, msg_hash) map
  var Gl  : (msg_hash, g_hash) map
  var Fl  : (msg_hash, f_hash) map
  var S  : message list
  var iH, iS, iG, iF : int

  fun H(m:message, r:salt) : msg_hash = {
    var a : msg_hash = {0,1}^k2;
    if ( !in_dom((m,r), Hl) ) {
      iH = iH + 1;
      Hl[(m,r)] = a;
    };
    return Hl[(m,r)];
  }

  fun G(m:msg_hash) : g_hash = {
    var a : g_hash = {0,1}^k1;
    if ( !in_dom(m, Gl) ) {
      iG = iG + 1;
      Gl[m] = a;
    };
    return Gl[m];
  }

  fun F(m:msg_hash) : f_hash = {
    var a : f_hash = {0,1}^k0;
    if ( !in_dom(m, Fl) ) {
      iF = iF + 1;
      Fl[m] = a;
    };
    return Fl[m];
  }

  fun Sign(m:message) : msg_f = {
    var w : msg_hash;
    var s,g : g_hash;
    var t : f_hash;
    var r : salt = {0,1}^k1;
    iS = iS + 1;
    w = H(m,r);
    g = G(w);
    s = xor(r,g);
    t = F(w);
    S = m :: S;
    return finv(sk, constr(0,w,s,t));
  }

  abs A  = A {H,G,F,Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var rr : salt;
    var yy : msg_f;
    var mm : message;
    var bb : int;
    var ww : msg_hash;
    var ss : g_hash;
    var tt : f_hash;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    Hl = empty_map();
    Gl = empty_map();
    Fl = empty_map();
    S = [];
    iH = 0;
    iF = 0;
    iG = 0;
    iS = 0;
    (mm, sigma) = A(pk);
    yy = f(pk,sigma);
    (bb,(ww,(ss,tt))) = splitstr(yy);
    rr = xor(ss,G(ww));
    return ( bb == 0 && w == H(mm,rr) && tt == F(ww) && !in(mm, S));
  }
};;




game OW = {
  var pk : public_key
  var sk : secret_key
  var L  : (message * salt, group) map
  var R  : (int, (int, salt) map) map
  var I  : (message, int) map
  var J  : (int, int) map
  var P  : (message * salt, group) map
  var iM : int
  var y  : group

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( !in_dom((m,r), L) ) {
     if ( in_rng(r, R[I[m]]) ) {
       L[(m,r)] = f(pk, g^a);
     } else {
       L[(m,r)] = y * f(pk, g^a);
     }
     P[(m,r)] = g^a;
    };
    return L[(m,r)];
  }

  fun Sign(m:message) : signature = {
    var h  : group; 
    var r : salt;
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    r = R[I[m]][J[I[m]]];
    J[I[m]] = J[I[m]] + 1;
    h = H(m,r);
    return (P[(m,r)], r);
  }

  abs A = A {H, Sign}
  abs KG = KG {}

  fun Inv(pk':public_key, y':group) : group = {
    var mm : message;
    var sigma : signature;
    var s, h : group;
    var rr, r' : salt;
    var i, j : int;
    pk = pk';
    y = y';
    L = empty_map();
    R = empty_map();
    I = empty_map();
    J = empty_map();
    P = empty_map();
    iM = 0;
    i = 0;
    j = 0;

    /* While Merge */
    while (i < qH + qS) {
      J[i] = 0;
      j = J[i];
      while (j < qS) {
        R[i][j] = {0,1}^k;
        j = j + 1;
      }
      j = 0;
      i = i + 1;
    }
    (mm, sigma) = A(pk);
    (s, rr) = sigma;
    h = H(mm, rr);
    return s * ginv(P[(mm,rr)]);
  }

  fun Main() : bool = {
    var kp : key_pair;
    var a : int = [0..n-1];
    var x, y' : group;
    var pk' : public_key;
    kp = KG();
    pk' = pkey(kp);
    sk = skey(kp);
    y' = g^a;
    x = Inv(pk', y');
    return (f(pk', x) == y');
  }
};;


claim Conclusion : 
 EF.Main[res && iH <= qH + qS && iS <= qS] * (1%r / 4%r) <= OW.Main[res];;




