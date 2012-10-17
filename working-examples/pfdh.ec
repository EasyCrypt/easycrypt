/*
** PFDH.ec: Unforgeability under chosen-message attacks
** of the Probabilistic Full-Domain Hash signature scheme.
** See 
**
** J.-S. Coron. Optimal security proofs for PSS and other signature
** schemes. In Advances in Cryptology – EUROCRYPT 2002, volume 2332 of
** Lecture Notes in Computer Science, pages 272–287, 2002. Springer. 
*/

/** Abstract types **/
type group;;
type message;;
type key_pair;;
type secret_key;;
type public_key;;


/** Constants **/
cnst k   : int;;            // salt length
cnst n   : int;;            // group order
cnst g   : group;;          // group generator
cnst e   : group;;          // group identity element
cnst qH  : int;;            // allotted queries to the hash oracle
cnst qS  : int;;            // allotted queries to the signing oracle
cnst dummy : message;;      // dummy message
cnst zero  : bitstring{k};; // the zero bitstring of length k


/** Type abbreviations **/
type salt      = bitstring{k};;
type signature = group * salt;;


/** Operators **/
// Group
op (*)  : group, group -> group  = group_mul;;
op (^)  : group, int -> group    = group_pow;;
op dlg  : group -> int           = dlg;;
op ginv : group -> group         = group_inv;;

// One-way permutation
op f    : public_key, group -> group = f;;
op finv : secret_key, group -> group = finv;;

// Keys 
op pkey : key_pair -> public_key = pkey;;
op skey : key_pair -> secret_key = skey;;    

// Reals
op (^)  : real, int -> real = real_pow;;


/** Axioms **/
prover "alt-ergo";;

axiom qH_nat : { 0 <= qH };;

axiom qS_nat : { 0 < qS };;

axiom k_nat : { 0 <= k };;

axiom n_nat : { 0 <= n };;

axiom finv_left : forall (x:group, kp:key_pair). 
  { x == finv(skey(kp), f(pkey(kp), x)) };;

axiom finv_right : forall (x:group, kp:key_pair). 
  { x == f(pkey(kp), finv(skey(kp), x)) };;

axiom dlg_pow : forall (x:group). { (g^dlg(x)) == x };;

axiom pow_dlg : forall (a:int). { dlg(g^a) == a%n };;

axiom mod_small : forall (a:int,n:int). { 0 <= a } => { a < n } => { a%n == a };;

axiom group_mul_comm : forall (x:group, y:group). { x * y == y * x };; 

axiom group_mul_assoc : 
  forall (x:group, y:group, z:group). { x * (y * z) == (x * y) * z };;

axiom group_mul_inv_right : forall (x:group). { x * ginv(x) == e };;

axiom group_mul_e_right : forall (x:group). { x * e == x };;

/** REMARK: this holds provided 2 <= qS <= 2^k */
axiom exp_bound : { 1%r / 4%r <= (1%r -  1%r / (2^k)%r)^qS };;

axiom f_homo : forall (x:group, y:group, pk:public_key). 
  { f(pk, x) * f(pk, y) == f(pk, x * y) };;

axiom f_e : forall (pk:public_key). { f(pk, e) == e };;

lemma reduction :  
 forall (x:group, y:group, z:group, pk:public_key).
  { x * f(pk,y) == f(pk,z) } => { f(pk, z * ginv(y)) == x };;

unset exp_bound, f_homo, f_e, reduction;;


/** Abstract procedures **/
adversary A(pk:public_key) : message * signature 
  { message, salt -> group; message -> signature };;

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
  var L  : (message * salt, group) map
  var S  : message list
  var iH, iS : int
  var mm : message
  var rr : salt

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      L[(m,r)] = g^a;
    };
    return L[(m,r)];
  }

  fun Sign(m:message) : signature = {
    var h : group;
    var r : salt = {0,1}^k;
    iS = iS + 1;
    S = m :: S;
    h = H(m, r);
    return (finv(sk, h), r);
  }

  abs A  = A {H, Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var s, h : group;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    L = empty_map();
    S = [];
    iH = 0;
    iS = 0;
    (mm, sigma) = A(pk);
    (s, rr) = sigma;
    h = H(mm, rr);
    return (h == f(pk, s) && !in(mm, S));
  }
};;


/*
** Game G1:
**
** We introduce a matrix R : (int,int) -> {0,1}^k in which we store
** the random salt values used in signature computations. At the end
** of the game, an entry R[i][j] stores the salt value used to answer
** the j-th signature query for the i-th message, or a uniformly
** random value if there were less than j queries for that message.
** Since the message mm in the forgery returned by the adversary is
** fresh, all values in the map R[I[mm]] are uniformly random and the
** probability that the value rr returned by the adversary is
** different from all of them is at least (1 - 1/2^k)%qS.
**
** Invariant: !in(mm, S) => J[I[m]] = 0
**
*/
game G1 = {
  var pk : public_key
  var sk : secret_key
  var L  : (message * salt, group) map
  var R  : (int, (int, salt) map)  map
  var I  : (message, int) map
  var J  : (int, int) map
  var S  : message list
  var iM, iH, iS, i, j : int
  var mm : message
  var rr : salt

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      L[(m,r)] = g^a;
    };
    return L[(m,r)];
  }

  fun Sign(m:message) : signature = {
    var h : group;
    var r : salt;
    var a : int = [0..n-1];
    iS = iS + 1;
    S = m :: S;
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS ) {
      r = {0,1}^k;
      R[I[m]][J[I[m]]] = r;
      J[I[m]] = J[I[m]] + 1;
    }
    else {
      r = {0,1}^k;
    }
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      L[(m,r)] = g^a;
    };
    h = L[(m,r)];
    return (finv(sk, h), r);
  }

  abs A  = A {H, Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var s, h : group;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    L = empty_map();
    R = empty_map();
    I = empty_map();
    J = empty_map(); 
    S = [];
    iM = 0;
    iH = 0;
    iS = 0;
    mm = dummy;
    rr = zero;
    i = 0;
    j = 0;
    while (i < qH + qS) { 
      J[i] = 0;
      i = i + 1;
    }
    (mm, sigma) = A(pk);
    (s, rr) = sigma;
    h = H(mm, rr);
    /* Begin resampling */
    i = 0;
    while (i < qH + qS) {
      j = J[i];
      while (j < qS) {
        R[i][j] = {0,1}^k;
        j = j + 1;
      }
      j = 0;
      i = i + 1;
    }
    i = 0;
    /* End resampling */
    return (h == f(pk, s) && !in(mm, S));
  }
};;

equiv EF_G1_Sign : EF.Sign ~ G1.Sign :
  ={pk,sk,L,S,iH,iS,m} ==> ={pk,sk,L,S,iH,iS,res};;
inline{1} H; case{2}: in_dom(m, I);;

/* in_dom(m{2},I{2}) */
reduce{2} 4 false; [trivial | ];;
case{2}: 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS;;

/* 0 <= I[m] < qH + qS /\ J[I[m]] < qS */
reduce{2} 4 true; [trivial | ];;
derandomize; wp; pop{2} 1; repeat rnd; trivial;;

/* !(0 <= I[m] < qH + qS /\ J[I[m]] < qS) */
reduce{2} 4 false; [trivial | ];;
derandomize; wp; pop{2} 1; repeat rnd; trivial;;

/* !in_dom(m{2},I{2}) */
reduce{2} 4 true; [trivial | ];;
case{2}: 0 <= iM && iM < qH + qS && J[iM] < qS;;

/* 0 <= iM < qH + qS /\ J[iM] < qS */
reduce{2} 6 true; [trivial | ];;
derandomize; wp; pop{2} 1; repeat rnd; trivial;;

/* !(0 <= iM < qH + qS /\ J[iM] < qS) */
reduce{2} 6 false; [trivial | ];;
derandomize; wp; pop{2} 1; repeat rnd; trivial;;
save;;


equiv EF_G1 : EF.Main ~ G1.Main : {true} ==> ={iH,iS,res};;
app 10 19 ={pk,sk,L,S,iS,iH,mm,sigma,s,rr,h};;
call inv ={pk,sk,L,S,iS,iH};;
wp; call inv ={pk,sk,L,S,iS,iH};;
app 7 15 ={pk,sk,L,S,iS,iH}; [ | trivial];;
wp; call inv {true}; trivial;;
wp;;
whilerev{2}: ={pk,sk,L,S,iS,iH} :i{2}-(qH+qS),0;;
trivial;;
trivial;;
wp;;
whilerev{2}: ={pk,sk,L,S,iS,iH}: j{2}-qS,0;;
trivial;;
trivial;;
derandomize; wp; trivial;;
save;;


claim Pr_EF_G1 : 
 EF.Main[res && iH <= qH + qS && iS <= qS] == 
 G1.Main[res && iH <= qH + qS && iS <= qS]
using EF_G1;;

/* TODO: maybe possible using Failure Event Lemma */
claim Pr_G1' : 
 G1.Main[res && iH <= qH + qS && iS <= qS] * (1%r -  1%r / (2^k)%r)^qS <=
 G1.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]]) ]
using admit;;

set exp_bound;;

claim Pr_G1 : 
 G1.Main[res && iH <= qH + qS && iS <= qS] * (1%r / 4%r) <=
 G1.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]]) ];;

unset exp_bound;;


/*
** Game G2:
**
** Eager version of G1
*/
game G2 = {
  var pk : public_key
  var sk : secret_key
  var L  : (message * salt, group) map
  var R  : (int, (int, salt) map)  map
  var I  : (message, int) map
  var J  : (int, int) map
  var S  : message list
  var iM, iH, iS, i, j : int
  var mm : message
  var rr : salt

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      L[(m,r)] = g^a;
    };
    return L[(m,r)];
  }

  fun Sign(m:message) : signature = {
    var h : group;
    var r : salt;
    var a : int = [0..n-1];
    iS = iS + 1;
    S = m :: S;
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS ) {
      r = R[I[m]][J[I[m]]];
      J[I[m]] = J[I[m]] + 1;
    }
    else {
      r = {0,1}^k;
    }
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      L[(m,r)] = g^a;
    };
    h = L[(m,r)];
    return (finv(sk, h), r);
  }

  abs A  = A {H, Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var s, h : group;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    L = empty_map();
    R = empty_map();
    I = empty_map();
    J = empty_map(); 
    S = [];
    iM = 0;
    iH = 0;
    iS = 0;
    mm = dummy;
    rr = zero;
    i = 0;
    j = 0;
    while (i < qH + qS) { 
      J[i] = 0;
      i = i + 1;
    }
    /* Begin resampling */
    i = 0;
    while (i < qH + qS) {
      j = J[i];
      while (j < qS) {
        R[i][j] = {0,1}^k;
        j = j + 1;
      }
      j = 0;
      i = i + 1;
    }
    i = 0;
    /* End resampling */
    (mm, sigma) = A(pk);
    (s, rr) = sigma;
    h = H(mm, rr);
    return (h == f(pk, s) && !in(mm, S));
  }
};;

axiom R_upd_eq :
 forall (r:salt, i:int, j:int,
         R1:(int, (int, salt) map) map, R2:(int, (int, salt) map) map). 
   { in_dom(i, R1) && in_dom(j, R1[i]) && R1[i][j] == r } => 
   (forall (i':int, j':int).
    ({ !(i' == i) } \/ { !(j' == j) }) => 
    ({ in_dom(i', R1) == in_dom(i', R2) }) =>
    ({ in_dom(i', R1) } => { in_dom(j', R1[i']) == in_dom(j', R2[i']) }) =>
    ({ in_dom(i', R1) } => { in_dom(j', R1[i']) } => { R1[i'][j'] == R2[i'][j'] })) =>
   { R1 == upd(R2, i, upd(R2[i], j, r)) };;

equiv auto G1_G2 : G1.Main ~ G2.Main : {true} ==> ={iH,iS,R,I,mm,rr,res}
  eager {
    i = 0;
    while (i < qH + qS) {
      j = J[i];
      while (j < qS) {
        R[i][j] = {0,1}^k;
        j = j + 1;
      }
      j = 0;
      i = i + 1;
    }
    i = 0;
  };;
/* Sign oracle */
case{1}: in_dom(m,I);;

/* in_dom(m, I) */
reduce{1} 4 false; [trivial | ];;
reduce{2} 7 false; [trivial | ];;
swap{2} [4-6] -3;;
app 3 3 ={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\ { in_dom(m{1},I{1}) };;
wp; rnd; trivial;;
case{1}: 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS;;

/* 0 <= I[m] < qH + qS /\ J[I[m]] < qS */
reduce{1} 1 true; [trivial | ];;
reduce{2} 4 true; [trivial | ];;
swap{1} [4-5] 3; wp;;

// Split outter while
strengthenrev: i < I[m];;
// Unroll iteration corresponding to i = I[m]
unrollrev;;

reduce{1} 6 true;;
whilerev{1}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){1} }:i{1}-I{1}[m{1}],0;;
trivial;;
trivial;;
wp;;
whilerev{1}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){1} }:j{1}-qS,0;;
trivial;;
trivial;;
derandomize;wp;trivial;;

reduce{2} 3 true;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:i{2}-I{2}[m{2}],0;;
wp;;
trivial;;
trivial;;
wp;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:j{2}-qS,0;;
trivial;;
trivial;;
derandomize;wp;trivial;;

app 9 6 
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (i == I[m] + 1){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;

wp;;
// Unroll iteration corresponding to J[I[m]] 
unrollrev{2};;

reduce{2} 4 true;;
wp;;

whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:i{2}-I{2}[m{2}],0;;
trivial;;
trivial;;
wp;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:j{2}-qS,0;;
trivial;;
trivial;;
derandomize; wp; trivial;;


whilerev:   
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (i == I[m]){2} } /\
   { (J[I[m]] < j){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
derandomize; wp; rnd; trivial;;

derandomize; wp;;
whilerev:
 (={pk,sk,L,S,iS,iH,mm,rr,i,I,iM,m,a} /\
 { (I[m] < qH + qS){1} } /\ 
 { (i <= I[m]){1} } /\
 { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} } /\
 { r{1} == r_0{2} } /\
 {  (in_dom(I[m],R)){1} && in_dom((J[I[m]]){2},(R[I[m]]){1}) && (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
 (forall (i:int, j:int).
   { !i == (I[m]){1} || !j == (J[I[m]]){2} } => { R{1}[i][j] == R{2}[i][j] }));;
wp;;
whilerev:
 (={pk,sk,L,S,iS,iH,mm,rr,i,j,I,iM,m,a} /\
 { (I[m] < qH + qS){1} } /\ 
 { (i < I[m]){1} } /\
 { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} } /\
 { r{1} == r_0{2} } /\
 {  (in_dom(I[m],R)){1} && in_dom((J[I[m]]){2},(R[I[m]]){1}) && (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
 (forall (i:int, j:int).
  { !i == (I[m]){1} || !j == (J[I[m]]){2} } => { R{1}[i][j] == R{2}[i][j] }));;

set R_upd_eq;;
derandomize; wp; rnd;trivial;;
trivial;;
wp; rnd; trivial;;
unset R_upd_eq;;

whilerev:
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (I[m] < i){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
wp;;
whilerev:
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (I[m] < i){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
derandomize; wp; rnd; trivial;;
trivial;;
trivial;;


/* !(I[m] < qH + qS /\ J[I[m]] < qS) */
reduce{1} 1 false; [trivial | ];;
reduce{2} 4 false; [trivial | ];;
swap{1} [2-3] 3; derandomize; wp;;

whilerev: 
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\
  { r{1} == r_0{2} });;
wp;;
whilerev: 
 (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\
 { r{1} == r_0{2} });;
derandomize; wp; rnd; trivial;;
trivial;;
wp; rnd; trivial;;


/* !in_dom(m,I) */
reduce{1} 4 true; [trivial | ];;
reduce{2} 7 true; [trivial | ];;
swap{2} [4-8] -3;;
app 5 5 ={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\ { in_dom(m{1},I{1}) };;
wp; rnd; trivial;;

case{1}: 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS;;

/* 0 <= I[m] < qH + qS /\ J[I[m]] < qS */
reduce{1} 1 true; [trivial | ];;
reduce{2} 4 true; [trivial | ];;
swap{1} [4-5] 3; wp;;

// Split outter while
strengthenrev: i < I[m];;
// Unroll iteration corresponding to i = I[m]
unrollrev;;

reduce{1} 6 true;;
whilerev{1}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){1} }:i{1}-I{1}[m{1}],0;;
trivial;;
trivial;;
wp;;
whilerev{1}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){1} }:j{1}-qS,0;;
trivial;;
trivial;;
derandomize; wp; trivial;;

reduce{2} 3 true;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:i{2}-I{2}[m{2}],0;;
trivial;;
trivial;;
wp;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:j{2}-qS,0;;
trivial;;
trivial;;
derandomize; wp; trivial;;

app 9 6 
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (i == I[m] + 1){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;

wp;;
// Unroll iteration corresponding to J[I[m]] 
unrollrev{2};;

reduce{2} 4 true;;
wp;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:i{2}-I{2}[m{2}],0;;
trivial;;
trivial;;
wp;;
whilerev{2}: { (0 <= I[m] && I[m] < qH + qS && i <= qH + qS && i <= I[m]){2} }:j{2}-qS,0;;
trivial;;
trivial;;
derandomize; wp; trivial;;

whilerev:   
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (i == I[m]){2} } /\
   { (J[I[m]] < j){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
derandomize; wp; rnd; trivial;;

derandomize; wp;;
whilerev:
 (={pk,sk,L,S,iS,iH,mm,rr,i,I,iM,m,a} /\
 { (I[m] < qH + qS){1} } /\ 
 { (i <= I[m]){1} } /\
 { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} } /\
 { r{1} == r_0{2} } /\
 {  (in_dom(I[m],R)){1} && in_dom((J[I[m]]){2},(R[I[m]]){1}) && (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
 (forall (i:int,j:int). 
  { !i == (I[m]){1} || !j == (J[I[m]]){2} } => { R{1}[i][j] == R{2}[i][j] }));;
wp;;
whilerev:
 (={pk,sk,L,S,iS,iH,mm,rr,i,j,I,iM,m,a} /\
 { (I[m] < qH + qS){1} } /\ 
 { (i < I[m]){1} } /\
 { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} } /\
 { r{1} == r_0{2} } /\
 {  (in_dom(I[m],R)){1} && in_dom((J[I[m]]){2},(R[I[m]]){1}) && (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
 (forall (i:int,j:int). 
  { !i == (I[m]){1} || !j == (J[I[m]]){2} } => { R{1}[i][j] == R{2}[i][j] }));;

set R_upd_eq;;
derandomize; wp; rnd; trivial;;
trivial;;
wp; rnd; trivial;;
unset R_upd_eq;;

whilerev:
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (I[m] < i){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
wp;;
whilerev:
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,iM,m,a} /\
   { (I[m] < i){2} } /\
   { (R[I[m]]){1}[(J[I[m]]){2}] == r{1} } /\
   { J{1} == (upd(J, I[m], J[I[m]] + 1)){2} });;
derandomize; wp; rnd; trivial;;
trivial;;
trivial;;


/* !(I[m] < qH + qS /\ J[I[m]] < qS) */
reduce{1} 1 false; [trivial | ];;
reduce{2} 4 false; [trivial | ];;
swap{1} [2-3] 3; derandomize; wp;;

whilerev: 
  (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\
  { r{1} == r_0{2} });;
wp;;
whilerev: 
 (={pk,sk,L,S,iS,iH,mm,rr,i,j,R,I,J,iM,m,a} /\
 { r{1} == r_0{2} });;
derandomize; wp; rnd; trivial;;
trivial;;
wp; rnd; trivial;;
save;;

/* Prefix */
whilerev: ={kp,pk,sk,L,S,iS,iH,i,j,R,I,J,iM,mm,rr};;
trivial;;
wp; call inv {true}; trivial;;

/* Suffix */
trivial;;
save;;


claim Pr_G1_G2 : 
 G1.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]])] <=
 G2.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]]) ]
using G1_G2;;


/*
** Game G3:
**
** Embed challenge into hash queries
*/
game G3 = {
  var pk : public_key
  var sk : secret_key
  var L  : (message * salt, group) map
  var R  : (int, (int, salt) map)  map
  var I  : (message, int) map
  var J  : (int, int) map
  var S  : message list
  var iM, iH, iS : int
  var mm : message
  var rr : salt
  var y  : group

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
      if ( in_rng(r, R[I[m]]) ) {
        L[(m,r)] = f(pk, g^a);
      } else {
        L[(m,r)] = y * f(pk, g^a);
      }
    };
    return L[(m,r)];
  }

  fun Sign(m:message) : signature = {
    var h : group;
    var r : salt;
    iS = iS + 1;
    S = m :: S;
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS ) {
      r = R[I[m]][J[I[m]]];
      J[I[m]] = J[I[m]] + 1;
    }
    else {
      r = {0,1}^k;
    }
    h = H(m,r);
    return (finv(sk, h), r);
  }

  abs A  = A {H, Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var s, h : group;
    var i, j : int;
    var a : int = [0..n-1];
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    y = g^a;
    L = empty_map();
    R = empty_map();
    I = empty_map();
    J = empty_map(); 
    S = [];
    iM = 0;
    iH = 0;
    iS = 0;
    i = 0;
    j = 0;
    while (i < qH + qS) { 
      J[i] = 0;
      i = i + 1;
    }
    i = 0;
    while (i < qH + qS) {
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
    return (h == f(pk, s) && !in(mm, S));
  }
};;


equiv G2_G3_H : G2.H ~ G3.H :
 ={pk,sk,L,iM,iH,iS,S,R,I,J,m,r} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }) ==>
 ={pk,sk,L,iM,iH,iS,S,R,I,J,res} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) });;
case{1}: in_dom((m,r), L);;

/* in_dom((m,r), L) */
wp; rnd; trivial;;

/* !in_dom((m,r), L) */
reduce 3 true; [trivial | trivial | ];;
case{1}: in_dom(m,I);;

/* in_dom(m, I) */
reduce 2 false; [trivial | trivial | ];;
case{2}: in_rng(r,R[I[m]]);;

/* in_rng(r,R[I[m]]) */
reduce{2} 3 true; [trivial | ];;
wp; rnd (dlg(finv(sk,g^a))), (dlg(f(pk,g^a))); trivial;;

/* !in_rng(r,R[I[m]]) */
reduce{2} 3 false; [trivial | wp];;
rnd (dlg(finv(sk,ginv(y) * g^a))), (dlg(y * f(pk, g^a))); trivial;;

/* !in_dom(m, I) */
reduce 2 true; [trivial | trivial | ];;
case{2}: in_rng(r,R[iM]);;

/* in_rng(r,R[iM]) */
reduce{2} 5 true; [trivial | ];;
wp; rnd (dlg(finv(sk,g^a))), (dlg(f(pk,g^a))); trivial;;

/* !in_rng(r,R[iM]) */
reduce{2} 5 false; [trivial | wp];;
rnd (dlg(finv(sk,ginv(y) * g^a))), (dlg(y * f(pk, g^a))); trivial;;
save;;


equiv G2_G3_Sign : G2.Sign ~ G3.Sign :
 ={pk,sk,L,iM,iH,iS,S,R,I,J,m} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }) ==>
 ={pk,sk,L,iM,iH,iS,S,R,I,J,res} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) });;
inline{2} H; push{1} 4; swap{2} 7 1;;
app 4 7 
 (={pk,sk,L,iM,iH,iS,S,R,I,J,m,r} /\
 { m_0{2} == m{2} } /\
 { r_0{2} == r{2} } /\
 { in_dom(m{2}, I{2}) } /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }));;
derandomize; wp; push{1} 1; repeat rnd; trivial;;
case{1}: in_dom((m,r), L);;

/* in_dom((m,r), L) */
reduce 2 false; trivial;;

/* !in_dom((m,r), L) */
reduce 2 true; [trivial | trivial | ];;
case{2}: in_rng(r, R[I[m]]);;

/* in_rng(r,R[I[m]]) */
reduce{2} 3 true; [trivial | wp];;
rnd (dlg(finv(sk,g^a))), (dlg(f(pk,g^a))); trivial;;

/* !in_rng(r,R[I[m]]) */
reduce{2} 3 false; [trivial | wp];;
rnd (dlg(finv(sk,ginv(y) * g^a))), (dlg(y * f(pk, g^a))); trivial;;
save;;


equiv G2_G3 : G2.Main ~ G3.Main : {true} ==> ={R,I,iH,iS,rr,mm,res};;
call G2_G3_H; wp;;
auto inv
 (={pk,sk,L,iM,iH,iS,S,R,I,J} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) });;
whilerev: (={pk,sk,L,iM,iH,iS,S,R,I,J,i,j});;
wp; whilerev: (={pk,sk,L,iM,iH,iS,S,R,I,J,i,j});;
derandomize; wp; rnd; trivial;;
trivial;;
wp; whilerev: (={pk,sk,L,iM,iH,iS,R,I,J,i,j});;
trivial;;
wp; call inv {true}; rnd{2}; trivial;;
save;;


claim Pr_G2_G3 : 
 G2.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]])] ==
 G3.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]]) ]
using G2_G3;;


/*
** Game G4:
**
** We instrument the hash oracle H to store in a map P the pre-image
** of the answers in which the challenge y is not embedded. We can then
** apply the fundamental lemma to simplify the Signing oracle and use
** the map P instead of finv to accurately simulate the original
** oracle.
**
** Failure event: qH + qS < iH \/ qS < iS
*/
game G4 = {
  var pk : public_key
  var sk : secret_key
  var L  : (message * salt, group) map
  var R  : (int, (int, salt) map)  map
  var I  : (message, int) map
  var J  : (int, int) map
  var P  : (message * salt, group) map
  var iM, iH, iS : int
  var mm : message
  var rr : salt
  var y  : group

  fun H(m:message, r:salt) : group = {
    var a : int = [0..n-1];
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    if ( !in_dom((m,r), L) ) {
      iH = iH + 1;
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
    var h : group;
    var r : salt;
    iS = iS + 1;
    if ( !in_dom(m, I) ) {
      I[m] = iM;
      iM = iM + 1;
    };
    r = R[I[m]][J[I[m]]];
    J[I[m]] = J[I[m]] + 1;
    h = H(m,r);
    return (P[(m,r)], r);
  }

  abs A  = A {H, Sign}
  abs KG = KG {}

  fun Main() : bool = {
    var kp : key_pair;
    var sigma : signature;
    var s, h : group;
    var i, j : int;
    var a : int = [0..n-1];
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    y = g^a;
    L = empty_map();
    R = empty_map();
    I = empty_map();
    J = empty_map(); 
    P = empty_map();
    iM = 0;
    iH = 0;
    iS = 0;
    i = 0;
    j = 0;
    while (i < qH + qS) { 
      J[i] = 0;
      i = i + 1;
    }
    i = 0;
    while (i < qH + qS) {
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
    return (f(pk, s * ginv(P[(mm,rr)])) == y);
  }
};;


equiv G3_G4_Sign : G3.Sign ~ G4.Sign : 
 ({ !(qH + qS < iH || qS < iS){1} } /\ 
  { !(qH + qS < iH || qS < iS){2} } /\
 ={pk,sk,L,iM,iH,iS,R,I,J,y,m} /\
 { 0 <= iM{1} } /\ 
 { (iM{1} <= iH){1} } /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }) /\
 (forall (m:message, r:salt). { in_dom((m,r), P{2}) == in_dom((m,r), L{2}) }) /\
 (forall (i:int). ({ 0 <= i } /\ { i < qH + qS }) <=> { in_dom(i,R{2}) }) /\
 (forall (i:int,j:int). { in_dom(i,R{2}) } => { 0 <= j } => { j < qS } => 
  { in_dom(j, R{2}[i]) }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { !in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == y * f(pk, P[(m,r)])){2} }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == f(pk, P[(m,r)])){2} }) /\
 (forall (m:message). { in_dom(m,I{1}) } => { (0 <= I[m] && I[m] < iM){1} }) /\
 (forall (j:int). { 0 <= j } => { j < qH + qS } => 
    ({ in_dom(j, J{1}) } /\ { 0 <= J{1}[j] } /\ { J{1}[j] <= iS{1} }) )) ==>
 { (qH + qS < iH || qS < iS){1} == (qH + qS < iH || qS < iS){2} } /\
 ({ !(qH + qS < iH || qS < iS){1} } =>
 (={pk,sk,L,iM,iH,iS,R,I,J,y,res} /\
 { 0 <= iM{1} } /\ 
 { (iM <= iH){1} } /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }) /\
 (forall (m:message, r:salt). { in_dom((m,r), P{2}) == in_dom((m,r), L{2}) }) /\
 (forall (i:int). ({ 0 <= i } /\ { i < qH + qS }) <=> { in_dom(i,R{2}) }) /\
 (forall (i:int,j:int). { in_dom(i,R{2}) } => { 0 <= j } => { j < qS } => 
  { in_dom(j, R{2}[i]) }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { !in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == y * f(pk, P[(m,r)])){2} }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == f(pk, P[(m,r)])){2} }) /\
 (forall (m:message). { in_dom(m,I{1}) } => { (0 <= I[m] && I[m] < iM){1} }) /\
 (forall (j:int). { 0 <= j } => { j < qH + qS } => 
    ({ in_dom(j, J{1}) } /\ { 0 <= J{1}[j] } /\ { J{1}[j] <= iS{1} }))) );;
inline H; derandomize;;
case{1}: in_dom(m,I);;

/* in_dom(m,I) */
reduce{1} 5 false; [trivial | ];;
reduce{2} 3 false; [trivial | ];;
reduce{1} 9 false; [trivial | ];;
reduce{2} 8 false; [trivial | ];;
case{1}: 0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS;;

reduce{1} 5 true; [trivial | ];;
wp; rnd; rnd{1}; trivial;;
trivial;;
prover simplify;;
trivial;;
prover "alt-ergo";;

/* !(0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS) */
reduce{1} 5 false; [trivial | ];;
wp; rnd; rnd{1}; trivial;;

/* !in_dom(m,I) */
reduce{1} 5 true; [trivial | ];;
reduce{2} 3 true; [trivial | ];;
reduce{1} 11 false;;
wp; rnd{1}; trivial;;
reduce{2} 10 false; [trivial | ];;

case{1}: 0 <= iM && iM < qH + qS && J[iM] < qS;;
reduce{1} 7 true; [trivial | ];;
wp; rnd; rnd{1}; trivial;;

/* !(0 <= I[m] && I[m] < qH + qS && J[I[m]] < qS) */
reduce{1} 7 false; [trivial | ];;
wp; rnd; rnd{1}; trivial;;
save;;


equiv G3_G4 : G3.Main ~ G4.Main : 
  {true} ==>
  { (qH + qS < iH || qS < iS){1} == (qH + qS < iH || qS < iS){2} } /\
  ({ !(qH + qS < iH || qS < iS){1} } => 
   ={pk,sk,L,iM,iH,iS,R,I,J,y,mm,rr} /\ 
   ({ (res && !in_rng(rr, R[I[mm]])){1} } => { res{2} }));;
app 15 15 
 (={pk,sk,L,R,I,J,iM,iH,iS,y,i,j,a} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 { L{1} == empty_map() } /\
 { R{1} == empty_map() } /\
 { I{1} == empty_map() } /\
 { J{1} == empty_map() } /\
 { P{2} == empty_map() } /\
 { iM{1} == 0 } /\
 { iH{1} == 0 } /\
 { iS{1} == 0 } /\
 { i{1} == 0 } /\
 { j{1} == 0 });;
wp; call inv {true}; rnd; trivial;;
while: 
 (={pk,sk,L,R,I,J,iM,iH,iS,y,i,j,a} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (i':int). { 0 <= i' } => { i' < i{1} } => 
  ({ in_dom(i', J{1}) } /\ { J{1}[i'] == 0 })) /\
 { L{1} == empty_map() } /\
 { R{1} == empty_map() } /\
 { I{1} == empty_map() } /\
 { P{2} == empty_map() } /\
 { iM{1} == 0 } /\
 { iH{1} == 0 } /\
 { iS{1} == 0 } /\
 { 0 <= i{1} } /\
 { j{1} == 0 });;
trivial;;
app 2 2 
 (={pk,sk,L,R,I,J,iM,iH,iS,i,j,y,a} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (i':int). { 0 <= i' } => { i' < qH + qS } => 
  ({ in_dom(i', J{1}) } /\ { J{1}[i'] == 0 })) /\
 (forall (i:int). ({ 0 <= i } /\ { i < qH + qS }) <=> { in_dom(i,R{2}) }) /\
 (forall (i':int,j':int). 
  { 0 <= i' } => { i' < qH + qS } => { 0 <= j' } => { j' < qS } => 
  { in_dom(j', R{2}[i']) }) /\
 { L{1} == empty_map() } /\
 { I{1} == empty_map() } /\
 { P{2} == empty_map() } /\
 { iM{1} == 0 } /\
 { iH{1} == 0 } /\
 { iS{1} == 0 } /\
 { j{1} == 0 });;
whilerev: 
 (={pk,sk,L,R,I,J,iM,iH,iS,y,i,j,a} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (i':int). { 0 <= i' } => { i' < qH + qS } => 
  ({ in_dom(i', J{1}) } /\ { J{1}[i'] == 0 })) /\
 (forall (i':int). ({ 0 <= i' } /\ { i' < i{2} }) <=> { in_dom(i',R{2}) }) /\
 (forall (i':int,j':int). 
  { 0 <= i' } => { i' < i{2} } => { 0 <= j' } => { j' < qS } => 
  { in_dom(j', R{2}[i']) }) /\
 { L{1} == empty_map() } /\
 { I{1} == empty_map() } /\
 { P{2} == empty_map() } /\
 { iM{1} == 0 } /\
 { iH{1} == 0 } /\
 { iS{1} == 0 } /\
 { 0 <= i{1} } /\
 { i{1} <= qH + qS } /\
 { j{1} == 0 });;
wp;;
whilerev: 
 (={pk,sk,L,R,I,J,iM,iH,iS,y,i,j,a} /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (i':int). { 0 <= i' } => { i' < qH + qS } => 
  ({ in_dom(i', J{1}) } /\ { J{1}[i'] == 0 })) /\
 (forall (i':int). 
  (({ 0 <= i' } /\ { i' < i{2} }) \/ 
   ({ 0 < j{2} } /\ { i' == i{2} })) <=> { in_dom(i',R{2}) }) /\
 (forall (i':int,j':int). 
  { 0 <= i' } => { i' < i{2} } => { 0 <= j' } => { j' < qS } => 
  { in_dom(j', R{2}[i']) }) /\
 (forall (j':int). 
  { 0 <= j' } => { j' < j{2} } => { in_dom(j', R{2}[i{2}]) }) /\
 { L{1} == empty_map() } /\
 { I{1} == empty_map() } /\
 { P{2} == empty_map() } /\
 { iM{1} == 0 } /\
 { iH{1} == 0 } /\
 { iS{1} == 0 } /\
 { 0 <= i{1} } /\
 { i{1} <= qH + qS } /\
 { 0 <= j{1} });;
derandomize; wp; rnd; trivial;;
wp; trivial;;
trivial;;

inline H;;
wp; rnd; wp;;
call inv upto { qH + qS < iH || qS < iS } with
 (={pk,sk,L,iM,iH,iS,R,I,J,y} /\
 { 0 <= iM{1} } /\ 
 { (iM <= iH){1} } /\
 (exists (kp:key_pair). { pk{1} == pkey(kp) } /\ { sk{1} == skey(kp) }) /\ 
 (forall (m:message, r:salt). { in_dom((m,r), L{2}) } => { in_dom(m, I{2}) }) /\
 (forall (m:message, r:salt). { in_dom((m,r), P{2}) == in_dom((m,r), L{2}) }) /\
 (forall (i:int). ({ 0 <= i } /\ { i < qH + qS }) <=> { in_dom(i,R{2}) }) /\
 (forall (i:int,j:int). { in_dom(i,R{2}) } => { 0 <= j } => { j < qS } => 
  { in_dom(j, R{2}[i]) }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { !in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == y * f(pk, P[(m,r)])){2} }) /\
 (forall (m:message, r:salt).
   { in_dom((m,r), L{2}) } =>
   { in_dom(I{2}[m], R{2}) } =>
   { in_rng(r, (R[I[m]]){2}) } =>
   { (L[(m,r)] == f(pk, P[(m,r)])){2} }) /\
 (forall (m:message). { in_dom(m,I{1}) } => { (0 <= I[m] && I[m] < iM){1} }) /\
 (forall (j:int). { 0 <= j } => { j < qH + qS } => 
    ({ in_dom(j, J{1}) } /\ { 0 <= J{1}[j] } /\ { J{1}[j] <= iS{1} })));;

set reduction;;

trivial;;
save;;

unset reduction;;


claim Pr_G3_G4 : 
 G3.Main[res && iH <= qH + qS && iS <= qS && !in_rng(rr, R[I[mm]])] <=
 G4.Main[res && iH <= qH + qS && iS <= qS]
using G3_G4;;

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

axiom J_extensionality : forall (J1:(int, int) map, J2:(int, int) map).
    (forall (i:int). { in_dom(i,J1) == in_dom(i,J2) }) => 
    (forall (i:int). { in_dom(i,J1) } => { J1[i] == J2[i] }) => 
    { J1 == J2 };;

equiv G4_OW : G4.Main ~ OW.Main : {true} ==> ={res};;
inline{2} Inv; wp;;
auto inv ={pk,sk,L,R,I,J,P,iM,y};;
app 17 17 ( ={pk,sk,L,R,I,P,iM,y,i,j,a} /\ {i{1} == 0} 
  /\ (forall (i:int). {(0<=i)&&(i<qH+qS)}=>{in_dom(i,J{1}) && J{1}[i]==0}) 
  /\ (forall (i:int). {in_dom(i,J{1})}<=>{(0<=i)&&(i<qH+qS)})
  /\ {J{2} == empty_map()} /\ {j{1} == 0}
  /\ { pk'{2} == pk{1} }
  /\ { y{1} == y'{2} }
  );;
wp;;

whilerev {1} :  ( (forall (it2:int). {(0<=it2) && (it2<i{1})}=>{in_dom(it2,J{1}) && J{1}[it2]==0})
     /\ { 0<= i{1}}  /\ { i{1}<= qH+qS}
     /\ (forall (it:int). {in_dom(it,J{1})}<=>{(0<=it)&&(it<i{1})})
     ):i{1}-(qH+qS),0;;
trivial;;
wp; call inv {true}; rnd; trivial;;
trivial;;

while :  
    ( ={i,j,R,pk,sk,L,I,P,iM,y,a}  /\ { 0<= i{2}} /\ { i{2}<= qH+qS} /\ { 0<= j{1}}
     /\ (forall (i:int). {(0<=i)&&(i<qH+qS)}=>{in_dom(i,J{1}) && J{1}[i]==0})
     /\ (forall (i:int). {in_dom(i,J{1})}<=>{(0<=i)&&(i<qH+qS)})
     /\ (forall (it:int). {(0<=it)&&(it<i{2})}=>{in_dom(it,J{2}) && J{2}[it]==0})
     /\ (forall (it:int). {in_dom(it,J{2})}<=>{(0<=it)&&(it<i{2})})
     /\ { pk'{2} == pk{1} }
     /\ { y{1} == y'{2} }
   );;
wp;;
whilerev :  ( ={i,j,R,pk,sk,L,I,P,iM,y,a} /\ { 0<= i{2}} /\ { i{2}<= qH+qS}
     /\ (forall (i:int). {(0<=i)&&(i<qH+qS)}=>{in_dom(i,J{1}) && J{1}[i]==0})
     /\ (forall (i:int). {in_dom(i,J{1})}<=>{(0<=i)&&(i<qH+qS)})
     /\ (forall (it:int). {(0<=it)&&(it<i{2})}=>{in_dom(it,J{2}) && J{2}[it]==0})
     /\ (forall (it:int). {in_dom(it,J{2})}=>{(0<=it)&&(it<qH+qS)})
     );;
derandomize; wp; rnd; trivial;;
wp; trivial;;
trivial;;
app 1 1 ( ={i,j,R,pk,sk,L,I,P,iM,y,a}
     /\ (forall (i:int). {in_dom(i,J{1})==in_dom(i,J{2})})
     /\ (forall (i:int). {in_dom(i,J{1})}=>{in_dom(i,J{2})}=>{J{1}[i]==J{2}[i]})
     /\ { pk'{2} == pk{1} } 
     /\ { y{1} == y'{2} }
     );;
trivial;;
trivial;;
prover cvc3;;
trivial;;
prover "alt-ergo";;
save;;

claim Pr_G4_OW : G4.Main[res && iH <= qH + qS && iS <= qS] <= OW.Main[res] 
using G4_OW;;

claim Conclusion : 
 EF.Main[res && iH <= qH + qS && iS <= qS] * (1%r / 4%r) <= OW.Main[res];;

/*
** REMARK: The definition of EF-CMA security used in this proof and
** the one in Coron's paper is somewhat weaker than the most natural
** definition for schemes without unique signatures (like PFDH). In
** the definition we use, the adversary must ouput a forgery for an
** entirely fresh message m, for which he has not seen any signature
** (c.f. !in(m,S)), this is called "Weak Existential Unforgeability", 
** while the most natural requirement would be that
** only the forged signature is fresh and allow the adversary to
** obtain other valid signatures for the same message, called 
** "Strong Existential Unforgeability".
**
** QUESTION: Does PFDH allow a tight reduction from the most natural
** interpretation of EF-CMA security to the one-wayness of the
** underlying trapdoor permutation?
**
** ANSWER: B. Santoso, K. Ohta and N. Kunihiro -
** "Optimal Security Proof PFDH under Existential Unforgeability against 
** Strong Adaptive Chosen Message Atack".
**
*/
