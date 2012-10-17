(*
** FDH.ec: Unforgeability under chosen-message attacks of the
** Full-Domain Hash signature scheme.
** See 
**
** J.-S. Coron. On the exact security of Full Domain Hash. In Advances
** in Cryptology – CRYPTO 2000, volume 1880 of Lecture Notes in
** Computer Science, pages 229–235, 2000. Springer.
*)

prover "alt-ergo", cvc3.

(** Abstract Types **)
type group.
type message.
type key_pair.
type secret_key. 
type public_key.

(** Constants **)
cnst n     : int.     (* group order *)
cnst g     : group.   (* group generator *)
cnst q     : int.     (* allotted queries to the hash oracle *)
cnst dummy : message.

(** Operators **)
op [^]   : (group, int) -> group  as group_pow.
op dlg   : group -> int.

(* One-way permutation *)
pop KG   : () -> key_pair.
op pkey  : key_pair -> public_key.
op skey  : key_pair -> secret_key.
op f     : (public_key, group) -> group.
op f_inv : (secret_key, group) -> group.

(** Axioms **)
axiom q_nat : 0 <= q.

axiom f_inv_left : forall (x:group, kp:key_pair),
  x = f_inv(skey(kp), f(pkey(kp), x)).

axiom f_inv_right : forall (x:group, kp:key_pair), 
  x = f(pkey(kp), f_inv(skey(kp), x)).

axiom dlg_pow : forall (x:group), g^dlg(x) = x.

axiom pow_dlg : forall (a:int), dlg(g^a) = a%n.

axiom dlg_lower_bound : forall (x:group), 0 <= dlg(x).

axiom dlg_upper_bound : forall (x:group), dlg(x) <= n-1.

axiom mod_small : forall (a:int,n:int), 0 <= a => a < n => a%n = a.

axiom real_of_bool_mul_le_l : forall (a:bool, b:real), real_of_bool(a) * b <= b.

(*
axiom real_of_bool_mul_le_r : forall (a:bool, b:real), b * real_of_bool(a) <= b.
*)

axiom real_of_bool_and : forall (a:bool, b:bool),
  real_of_bool(a && b) = real_of_bool(a) * real_of_bool(b).

(** Abstract procedures **)
adversary A(pk: public_key) : message * group {message -> group; message -> group}.

(** Game definitions **)

(*
** Game EF:
**
** This is the standard existential forgery experiment for FDH
*)
game EF = {
  var L : (message, group) map
  var S : message list
  var pk : public_key
  var sk : secret_key
  var i : int

  fun H(m:message) : group = {
    var a : int = [0..n-1];
    if (!in_dom(m,L)) {
      L[m] = g^a;
      i = i + 1;
    }
    return L[m];
  }

  fun Sign(m:message) : group = {
    var h : group;
    S = m :: S;
    h = H(m);
    return f_inv(sk, h);
  }

  abs A  = A {H, Sign}
 
  fun Main() : bool = {
    var kp : key_pair;
    var sigma, h : group;
    var m : message;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    L = empty_map;
    S = [];
    i = 0;
    (m, sigma) = A(pk);
    h = H(m);
    return (h = f(pk, sigma) && !mem(m, S));
  }
}.


game G1 = EF 
 var M : (int, message) map
 var I : (message, int) map
 var j : int
 var mm : message
 var sigma : group

 where H = {
   var a : int = [0..n-1];
   if ( !in_dom(m,L) ) {
     L[m] = g^a; 
     M[i] = m;
     I[m] = i;
     i = i + 1;
   }
   return L[m];
 }

 and Main = {
   var kp : key_pair;
   var h : group;
   kp = KG();
   pk = pkey(kp);
   sk = skey(kp);
   L = empty_map;
   M = empty_map;
   I = empty_map; 
   S = [];
   i = 0;
   (mm, sigma) = A(pk);
   h = H(mm);
   j = [0..q];
   return (h = f(pk, sigma) && !mem(mm,S));
 }.

equiv EF_G1 : EF.Main ~ G1.Main: true ==> ={pk,sk,L,S,i,res}.
 inline H; derandomize; wp.
 call (={pk,sk,L,S,i}).
 wp; swap{2} -2; trivial.
save.

claim PrEF_G1 : EF.Main[res && i <= q] = G1.Main[res && i <= q]
using EF_G1.


equiv G1_G1 : G1.Main ~ G1.Main:
  true ==> 
  ={pk,sk,L,S,I,M,i,sigma,mm,res} &&
  (forall (m:message), in_dom(m, I{1}) = in_dom(m, L{1})) &&
  (forall (m:message), in_rng(m, M{1}) = in_dom(m, I{1})) &&
  (forall (m:message), in_dom(m, I{1}) => (0 <= I[m] && I[m] < i){1}) &&
  in_dom(mm{1},I{1}) &&
  (forall (k:int), in_dom(k,M{1}) => (in_dom(M[k],I) && I[M[k]] = k){1}) &&
  ((res && i <= q && in_dom(j,M) && mm = M[j]){1} = 
   (res && i <= q && I[mm] = j)){2}.
 inline H; derandomize; wp.
 call 
  (={pk,sk,L,S,I,M,i} &&
   0 <= i{1} &&
   (forall (m:message), in_dom(m, I{1}) = in_dom(m, L{1}) ) &&
   (forall (m:message), in_rng(m, M{1}) = in_dom(m, I{1}) ) && 
   (forall (m:message), in_dom(m, I{1}) => (0 <= I[m] && I[m] < i){1}) &&
   (forall (k:int), in_dom(k,M{1}) => (in_dom(M[k],I) && I[M[k]] = k){1})).
 timeout 10.
 trivial.
 timeout 3.
save.

claim PrG1_G1b :
  G1.Main[res && i <= q && in_dom(j, M) && mm = M[j]] =
  G1.Main[res && i <= q && j = I[mm]]
using G1_G1.

claim PrG1_G1b2 :
  G1.Main[res && i <= q && 0 <= I[mm] && I[mm] <= q] =
  G1.Main[res && i <= q]
using G1_G1.

claim PrG1_G1 : 
 G1.Main[res && i <= q && 0 <= I[mm] && I[mm] <= q] * 1%r / (q + 1)%r <= 
 G1.Main[res && i <= q && j = I[mm]]
compute.


game G2 = G1 
 var a' : int

 where H = {
   var a : int = [0..n-1];
   if ( !in_dom(m, L) && (i <= j || in_dom(M[j], L)) ) {
     L[m] = g^a; 
     M[i] = m;
     i = i + 1;
  }
  return L[m];
 } 

 and Main = {
   var kp : key_pair;
   var h : group;
   kp = KG();
   pk = pkey(kp);
   sk = skey(kp);
   L = empty_map;
   M = empty_map;
   I = empty_map; 
   S = [];
   i = 0;
   j = [0..q];
   a' = 0;
   mm = dummy;
   sigma = g;
   (mm, sigma) = A(pk);
   h = H(mm);
   if (i <= j) { a' = [0..n-1]; } else { a' = dlg(L[M[j]]); } 
   return (h = f(pk, sigma) && !mem(mm, S));
 }.

equiv G1_G2 : G1.Main ~ G2.Main:
 true ==> ={pk,sk,L,S,M,i,j,mm,res} && (j{2} < i{2} => in_dom(j{2}, M{2})).
 swap{1} -4; inline H; derandomize; wp.
 call 
  (={pk,sk,L,S,M,i,j} && 
   (i{2} <= j{2} || in_dom(M{2}[j{2}], L{2})) && 
   (j{2} < i{2} => in_dom(j{2}, M{2})) ).
 wp; swap{2} -3; trivial.
save.

claim PrG1_G2 :
  G1.Main[res && i <= q && in_dom(j, M) && mm = M[j]] =
  G2.Main[res && i <= q && in_dom(j, M) && mm = M[j]]
using G1_G2.


game G3 = G2
 where H = {
   var h : group;
   var a : int = [0..n-1];
   if ( !in_dom(m,L) && (i <= j || in_dom(M[j], L)) ) {
     if (i = j) {  
       h = g^a'; 
     } else { 
       h = g^a; 
     }
     L[m] = h;
     M[i] = m;   
     i = i + 1;
   }
   return L[m];
 }

 and Main = {
   var kp : key_pair;
   var h : group;
   kp = KG();
   pk = pkey(kp);
   sk = skey(kp);
   L = empty_map;
   M = empty_map;    
   I = empty_map; 
   S = [];
   i = 0;
   j = [0..q];
   a' = 0;
   mm = dummy;
   sigma = g;
   if (i <= j) { a' = [0..n-1]; } else { a' = dlg(L[M[j]]); }
   (mm, sigma) = A(pk);
   h = H(mm);
   return (h = f(pk, sigma) && !mem(mm, S));
 }.

equiv G2_G3 : G2.Main ~ G3.Main : true ==> ={pk,sk,L,S,M,i,j,mm,res} by 
eager { if (i <= j) { a' = [0..n-1]; } else { a' = dlg(L[M[j]]); } }.
(* Oracle H *)
 derandomize.
 case{1}: (i = j && !in_dom(m,L) && (i <= j || in_dom(M[j],L)) ).
 trivial.
 swap{2} 1; trivial.
save.

 (* Prefix *)
 trivial.

 (* Suffix *)
 trivial.
save.

claim PrG2_G3 :  
  G2.Main[res && i <= q && in_dom(j, M) && mm = M[j]] =
  G3.Main[res && i <= q && in_dom(j, M) && mm = M[j]]
using G2_G3.


game G4 = G3
  var P : (message, group) map
  var bad : bool
 
  where H = {
   var h : group; 
   var a : int = [0..n-1];
   if ( !in_dom(m, L) ) { 
     if (i = j) {  
       h = g^a';
     } 
     else 
     {     
       h = f(pk, g^a); 
       P[m] = g^a;
     }
     L[m] = h;
     M[i] = m;
     i = i + 1;
  }
  return L[m];
 }

 and Sign = {
   var h, r : group;
   S = m :: S;
   h = H(m);
   if ( in_dom(j, M) && (m = M[j]) ) { 
     bad = true;
   }
   r = f_inv(sk, h);
   return r;
 }

 and Main = {
   var kp : key_pair;
   var h : group;
   kp = KG();
   pk = pkey(kp);
   sk = skey(kp);
   L = empty_map;
   M = empty_map;  
   P = empty_map;
   S = [];
   bad = false;
   i = 0;
   j = [0..q];
   a' = [0..n-1];
   (mm, sigma) = A(pk);
   h = H(mm);
   return (h = f(pk, sigma) && !mem(mm, S)); 
 }.

equiv H_G3_G4 : G3.H ~ G4.H :
 ={m,pk,sk,L,S,M,i,j,a'} && (i <= j || in_dom(M[j],L)){1} &&
 exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp) ==> 
 ={res,pk,sk,L,S,M,i,j,a'} && (i <= j || in_dom(M[j],L)){1} &&
 exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp).
 wp;rnd (dlg(f_inv(sk{2},g^a))), (dlg(f(pk{2},g^a))); trivial.
save.

equiv S_G3_G4 : G3.Sign ~ G4.Sign : 
 ={m,pk,sk,L,S,M,i,j,a'} && (i <= j || in_dom(M[j],L)){1} &&
 exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp) ==> 
 ={res,pk,sk,L,S,M,i,j,a'} && (i <= j || in_dom(M[j],L)){1} &&
 exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp).
 inline H; derandomize; wp.
 rnd (dlg(f_inv(sk{2},g^a_0))), (dlg(f(pk{2},g^a_0))); trivial.
save.

equiv G3_G4 : G3.Main ~ G4.Main : true ==> 
 ={res,L,S,pk,sk,mm,sigma,M,j,i} && 
 exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp).
 app 9 10 
  (={pk,sk,L,S,M,i,j} && i{1} <= j{1} &&
  exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp)).
 trivial.
 inline H; derandomize; wp.
 auto 
  (={pk,sk,L,S,M,i,j,a'} && (i <= j || in_dom(M[j],L)){1} &&
   exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp)).
 rnd (dlg(f_inv(sk{2},g^a_0))), (dlg(f(pk{2},g^a_0))); trivial.
save.
  
claim PrG3_G4 : 
  G3.Main[res && i <= q && in_dom(j,M) && mm = M[j]] =
  G4.Main[res && i <= q && in_dom(j,M) && mm = M[j]] 
using G3_G4.

equiv G4_G4 : G4.Main ~ G4.Main : true ==> 
 ={res,mm,S,M,j,bad,i} &&
 (res{1} => !mem(mm{1},S{1})) && ((in_dom(j,M) && !mem(M[j],S)){1} => !bad{1}). 
 auto
  (={pk,sk,L,S,M,i,j,a',bad} && 
   (forall (k:int), in_dom(k,M{1}) => k < i{1}) &&
   (forall (m:message), mem(m, S{1}) => in_rng(m, M{1})) && 
   (forall (m:message), in_dom(m, L{1}) = in_rng(m, M{1})) &&
   ((in_dom(j,M) && mem(M[j],S)){1} <=> bad{1})).
 trivial.
save.

claim PrG4_G4 : 
  G4.Main[res && i <= q && in_dom(j,M) && mm = M[j]] = 
  G4.Main[res && i <= q && in_dom(j,M) && mm = M[j] && !bad] 
using G4_G4.


game G5 = G4 
 where Sign = {
   var h, r : group;
   S = m :: S;
   h = H(m);
   if ( in_dom(j,M) && (m = M[j]) ) {
     bad = true;
     r = P[m];
   } else { 
     r = f_inv(sk, h);
   }
   return r;
 }.

equiv G4_G5 :  G4.Main ~ G5.Main : true ==> ={bad} && (!bad{2} => ={res,mm,j,M,i}).
 auto upto (bad) with (={L,S,pk,sk,M,j,i,P,a'}); trivial.
save.

claim PrG4_G5 : 
  G4.Main[res && i<= q && in_dom(j,M) && mm = M[j] && !bad] <=
  G5.Main[res && i<= q && in_dom(j,M) && mm = M[j] && !bad]
using G4_G5.

claim PrG5_G5 : 
  G5.Main[res && i <= q && in_dom(j,M) && mm = M[j] && !bad] <=
  G5.Main[res && i <= q && in_dom(j,M) && mm = M[j]]
same.


game G6 = G3
 var P : (message, group) map
 
 where H = { 
   var h : group; 
   var a : int = [0..n-1];
   if ( !in_dom(m,L) ) {
     if (i = j) {
       h = g^a'; 
     } else {
       h = f(pk,g^a); 
       P[m] = g^a;
     }
     M[i] = m;
     L[m] = h;
     i = i + 1;
   }
   return L[m];
 }

 and Sign = {
   var h : group;
   S = m :: S;
   h = H(m);
   return P[m];
 }
 
 and Main = {
   var kp : key_pair;
   var h : group;
   kp = KG();
   pk = pkey(kp);
   sk = skey(kp);
   L = empty_map;
   M = empty_map;  
   P = empty_map;
   S = [];
   i = 0;
   j = [0..q];
   a' = [0..n-1];
   (mm,sigma) = A(pk);
   h = H(mm);
   return (h = f(pk, sigma) && !mem(mm,S)); 
 }.

equiv G5_G6 : G5.Main ~ G6.Main : true ==> ={res,L,S,mm,j,M,pk,sk,P,a',i,sigma}.
 auto 
  (={pk,sk,L,S,M,i,j,a',P} && 
   (forall (k:int), in_dom(k,M{1}) => k < i{1}) &&
   (forall (m:message), 
    in_dom(m, L{1}) <=> 
    (in_dom(m, P{1}) || (in_dom(j{1},M{1}) && M{1}[j{1}] = m))) &&
   (forall (m:message), 
    in_dom(m,P{1}) && in_dom(m,L{1}) && 
    ((!in_dom(j{1},M{1})) || (m<>M{1}[j{1}])) => 
    f_inv(sk{1}, L{1}[m]) = P{1}[m]) &&
  exists (kp:key_pair), pk{1} = pkey(kp) && sk{1} = skey(kp)). 
 trivial.
save.

claim PrG5_G6 : 
  G5.Main[res && i <= q && in_dom(j,M) && mm = M[j]] =
  G6.Main[res && i <= q && in_dom(j,M) && mm = M[j]]
using G5_G6.


game G7 = {
  var L : (message, group) map
  var M :  (int, message) map
  var P : (message, group) map
  var S : message list
  var pk : public_key
  var sk : secret_key
  var sigma : group
  var mm : message
  var i, j, a' :  int
 
  fun H(m:message) : group = {
    var h : group; 
    var a : int = [0..n-1];
    if (!in_dom(m,L)) { 
      if (i = j) { h = g^a'; } else { h = f(pk,g^a); P[m] = g^a; } 
      M[i] = m;
      L[m] = h;
      i = i + 1;
    }
    return L[m];
  }
 
  fun Sign(m:message) : group = {
    var h : group;
    S = m :: S;
    h = H(m);
    return P[m];
  }
 
  abs A  = A {H,Sign}
 
  fun Main() : bool = {
    var kp : key_pair;
    var h : group;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    L = empty_map;
    M = empty_map;  
    P = empty_map;
    S = [];
    i = 0;
    j = [0..q];
    a' = [0..n-1];
    (mm,sigma) = A(pk);
    h = H(mm);
    return (f_inv(sk, g^a') = sigma);
  } 
}.

equiv G6_G7 : G6.Main ~ G7.Main : true ==> 
 ={L,S,mm,j,M,pk,sk,P,a',sigma,i} && 
 (forall (k:int), in_dom(k,M{1}) => k < i{1}) &&
 (forall (m:message), in_dom(m, L{1}) = in_rng(m, M{1})) &&
 (in_dom(j{1},M{1}) => (in_dom(M[j],L) && L[M[j]] = g^a'){1}) &&
 ((res && in_dom(j,M) && mm = M[j]){1} => res{2}). 
 inline H; derandomize; wp.
 auto 
  (={L,S,j,M,pk,sk,P,a',i} && 
   (forall (k:int), in_dom(k,M{1}) => k < i{1}) &&
   (forall (m:message), in_dom(m, L{1}) = in_rng(m, M{1})) &&
   (in_dom(j{1},M{1}) => (in_dom(M[j],L) && L[M[j]] = g^a'){1})).
 trivial.
save.
 
claim PrG6_G7 : 
  G6.Main[res && i <= q && in_dom(j,M) && mm = M[j]] <= G7.Main[res && i <= q]
using G6_G7.

game OW = {
  var L : (message, group) map
  var P : (message, group) map
  var pk' : public_key
  var y' : group
  var i, j : int 

  fun H(m:message) : group = {
    var h : group; 
    var a : int = [0..n-1];
    if ( !in_dom(m,L) ) {  
      if (i = j) { h = y'; } else { h = f(pk',g^a); P[m] = g^a; }
      L[m] = h;
      i = i + 1;
   }
   return L[m];
 }

 fun Sign(m:message) : group = {
   var h : group;
   h = H(m);
   return P[m];
 }

 abs A = A {H,Sign}

 fun Inv(pk:public_key, y:group) : group = {
   var m : message;
   var sigma : group;
   var h : group;
   L = empty_map;
   P = empty_map;
   i = 0;
   j = [0..q];
   pk' = pk;
   y' = y;
   (m,sigma) = A(pk);
   h = H(m);
   return sigma;
  }

  fun Main() : bool = {
    var kp : key_pair;
    var pk : public_key;
    var sk : secret_key;
    var a : int;
    var x, y : group;
    kp = KG();
    pk = pkey(kp);
    sk = skey(kp);
    a = [0..n-1];
    y = g^a;
    x = Inv(pk, y); 
    return f_inv(sk, y) = x;
  }
}.

equiv G7_OW : G7.Main ~ OW.Main : true ==> ={res}.
 inline Inv, H; derandomize; wp.
 call (={L,P,i,j} && pk{1} = pk'{2} && y'{2} = g^a'{1}).
 wp; swap{2} 3 -1; trivial.
save.

claim PrG7_OW : G7.Main[res && i <= q] <= OW.Main[res]
using G7_OW.

claim Conclusion : EF.Main[res && i <= q] * 1%r/(q + 1)%r <= OW.Main[res].

(*
** REMARK: 
** The security bound can be improved to
** 
** EF.Main[res && i <= q] * 1%r / q%r <= OW.Main[res] + 1%r / n%r * 1%r / q%r
**
** with a slightly different sequence of games---in which the inverter
** does not make the extra call H(m).
*)
