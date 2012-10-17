(*skA -- skB *)

include "ake_game5a.ec".

checkproof.

adversary D () : (message * message * session_string)
{
 () -> public_key;
 bool -> (message * eph_key) option; (* Init: start either with A or B *)
 (bool, message) -> (message * eph_key) option; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE9' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map
 var cantKG : int

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG = 0){
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   pk = pkA;
   cantKG = 1;
  } else{
   if (cantKG = 1){
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    cantKG = 2;
    pk = pkB;
   }
  }
  return pk;
 }

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (cantKG = 2){
   if (b) {
    x = gen_eph_key(0);
    X = out_noclash(skA,x);
    res = Some((X,x));
    seedA[X] = x; 
   } else
   { 
    x = gen_eph_key(0);
    X = out_noclash(skB,x);
    res = Some((X,x));
    seedB[X] = x;
   }
  }
  return res;
 }
 
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (cantKG = 2){  
   if (!b) {
    y = gen_eph_key(0);
    Y = inp(skB,y);
    res = Some ((Y,y));
    seedB[Y] = y;
   } else
   {
    y = gen_eph_key(0);
    Y = inp(skA,y);
    res = Some((Y,y));
    seedA[Y] = y;
   }
  }
  return res;
 }

 abs D = D { KG, Init, Respond, eqS, same_session_string }

 fun Main () : message * message * session_string = {
  var ek : eph_key;
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  (alpha,beta,str) = D();
  return (alpha,beta,str);
 }
}.

op wingame91
(pkA     : public_key, 
 pkB     : public_key, 
 str : session_string,
 alpha : message,
 beta : message) =
 eqS_oracle(str,(pkA,pkB,alpha,beta)).

op wingame92
(pkA     : public_key, 
 pkB     : public_key, 
 str : session_string,
 alpha : message,
 beta : message) =
 eqS_oracle(str,(pkB,pkA,beta,alpha)).

game AKE9_eager1 = 
 AKE9' 
var okA : bool
var okB : bool
where
KG = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okA && cantKG = 0) 
  {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   okA = true;
  } else {
   if (!okB && cantKG = 1) {
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    okB = true;
   } 
  }
  if (cantKG = 0){
   pk = pkA;
   cantKG = 1; 
  } else
  {
  if (cantKG = 1) {
   pk = pkB;
   cantKG = 2;
  }
 }
 return pk;
} and
Main = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  okA = false;
  okB = false;
  (alpha,beta,str) = D();
  return (alpha,beta,str);
}.

op wingame9
(pkA     : public_key, 
 pkB     : public_key, 
 str : session_string,
 alpha : message,
 beta : message) =
wingame91(pkA,pkB,str,alpha,beta) || wingame92(pkA,pkB,str,alpha,beta).


equiv Eq1 : AKE9'.Main ~ AKE9_eager1.Main : true ==> 
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2} by auto
(={pkA,skA,pkB,skB,seedA,seedB,cantKG} &&
 (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2) &&
 (okA{2} <=> cantKG{1} > 0) && (okB{2} <=> cantKG{1} > 1)). 

game AKE9_eager2 = 
 AKE9_eager1 where
Main = {
 var alpha : message; 
 var beta : message; 
 var str : session_string;
 var test : bool;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 seedA = empty_map;
 seedB = empty_map;
 cantKG = 0;
 okA = false;
 okB = false;
 (alpha,beta,str) = D();
 if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 } 
 return (alpha,beta,str);
}.

equiv Eq2 : AKE9_eager1.Main ~ AKE9_eager2.Main : true ==> 
cantKG{1} > 0 => ((let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2}).
derandomize;wp.
call (={pkA,skA,pkB,skB,seedA,seedB,cantKG,okA,okB} &&  (okA{2} <=> cantKG{1} > 0)).
trivial.
save.

game AKE9_eager3 = 
 AKE9_eager2 where
Main = {
 var alpha : message; 
 var beta : message; 
 var str : session_string;
 var test : bool;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 seedA = empty_map;
 seedB = empty_map;
 cantKG = 0;
 okA = false;
 okB = false;
 if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 } 
 (alpha,beta,str) = D();
 return (alpha,beta,str);
}.


equiv Eq3 : AKE9_eager2.Main ~ AKE9_eager3.Main : true ==> 
((let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2}) by 
eager 
{if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 } }.
derandomize.
swap{1} 3 -2.
!3 rnd>>.
trivial.
save.

derandomize.
swap{1} 3 -2.
!3 rnd>>.
trivial.
save.

derandomize.
swap{1} 3 -1.
!3 rnd>>.
trivial.
save.

trivial.
trivial.
save.

game AKE9_eager4 = 
 AKE9_eager3 where
KG = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okB && cantKG = 1) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 } 
 if (cantKG = 0){
 pk = pkA;
  cantKG = 1; 
 } else
 {
  if (cantKG = 1) {
   pk = pkB;
   cantKG = 2;
  }
 }
 return pk;
} and
Main = {
 var alpha : message; 
 var beta : message; 
 var str : session_string;
 var test : bool;
 skB = dummy;
 pkB = gen_public_key(skB);
 seedA = empty_map;
 seedB = empty_map;
 cantKG = 0;
 okB = false;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 (alpha,beta,str) = D();
 return (alpha,beta,str);
}.


equiv Eq4 : AKE9_eager3.Main ~ AKE9_eager4.Main : true ==> 
((let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2}).
call (={pkA,skA,pkB,skB,seedA,seedB,cantKG,okB} && okA{1}).
sp 9 0 .
condt{1}.
trivial.
save.

game AKE9_eager5_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map
 var cantKG : int
 var okB : bool
 (*Context variables *)
 var cantKG_C : int
 var pkA_C     : public_key 


 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 } 
 if (cantKG = 0){
  pk = pkA;
  cantKG = 1; 
 } else
 {
  if (cantKG = 1) {
   pk = pkB;
   cantKG = 2;
  }
 }
 return pk;
}

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (cantKG = 2){
   if (b) {
    x = gen_eph_key(0);
    X = out_noclash(skA,x);
    res = Some((X,x));
    seedA[X] = x; 
   } else
   { 
    x = gen_eph_key(0);
    X = out_noclash(skB,x);
    res = Some((X,x));
    seedB[X] = x;
   }
  }
  return res;
 }
 
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (cantKG = 2){  
   if (!b) {
    y = gen_eph_key(0);
    Y = inp(skB,y);
    res = Some ((Y,y));
    seedB[Y] = y;
   } else
   {
    y = gen_eph_key(0);
    Y = inp(skA,y);
    res = Some((Y,y));
    seedA[Y] = y;
   }
  }
  return res;
 }
 (* Context implementations *)
 fun KG_C() : public_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG_C = 0) {
   pk = pkA_C;
   cantKG_C = 1;
  } else {
   if (cantKG_C = 1) {
    pk = KG();
    pk = KG();
    cantKG_C = 2;
   }
  }
  return pk; 
 }
 
 fun Init_C(b : bool ) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  res = Init(b);
  return res;
 }
 
 fun Respond_C(b : bool,X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  res = Respond(b,X);
  return res;
 }

 abs D = D { KG_C, Init_C, Respond_C, eqS, same_session_string }
 
 fun D'(pkA_ : public_key) : message * message * session_string = {
  var res : message * message * session_string;
  pkA_C = pkA_;
  cantKG_C = 0;
  res = D();
  return res;
 }
 
 fun Main () : message * message * session_string = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  okB = false;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  (alpha,beta,str) = D'(pkA);
  return (alpha,beta,str);
 }
}.


equiv Eq5_KG : AKE9_eager4.KG ~ AKE9_eager5_ctxt.KG_C :
 (={pkA,skA,pkB,skB,seedA,seedB,okB} &&
(pkA_C{2} = pkA{2} && cantKG{1} = cantKG_C{2}) &&
(cantKG_C{2} = 0 => cantKG{2} = 0) &&
(cantKG_C{2} = 1 => cantKG{2} = 0) && (cantKG{2} = 0 => (cantKG_C{2} = 0 || cantKG_C{2} = 1))&&
(cantKG_C{2} = 2 <=> cantKG{2} = 2 && (cantKG = 0 ||cantKG = 1 ||cantKG = 2){2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}).
sp 2 2.
if{2}.
condf{1}.
condt{1}.
trivial.
if{1}.
condt{2}.
inline.
sp.
condt{2}.
rnd>>.
sp 2 2.
condf{1}.
condt.
sp.
!2 condf{2}.
condt{2}.
trivial.
condf{1}.
if.
inline.
sp 0 2.
condf{2}.
condt{2}.
sp.
condf{2}.
condf{2}.
condt{2}.
trivial.
trivial.
save.


equiv Eq5 : AKE9_eager4.Main ~ AKE9_eager5_ctxt.Main : true ==> 
((let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2}).
inline; wp.
call (={pkA,skA,pkB,skB,seedA,seedB,okB} &&
(pkA_C{2} = pkA{2} && cantKG{1} = cantKG_C{2}) &&
(cantKG_C{2} = 0 => cantKG{2} = 0) &&
(cantKG_C{2} = 1 => cantKG{2} = 0) && (cantKG{2} = 0 => (cantKG_C{2} = 0 || cantKG_C{2} = 1))&&
(cantKG_C{2} = 2 <=> cantKG{2} = 2 && (cantKG = 0 ||cantKG = 1 ||cantKG = 2){2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}).
trivial.
save.

adversary D' (_ : public_key) : (message * message * session_string)
{
 () -> public_key;
 bool -> (message * eph_key) option; (* Init: start either with A or B *)
 (bool, message) -> (message * eph_key) option; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.


game AKE9_eager5 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map
 var cantKG : int
 var okB : bool

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 } 
 if (cantKG = 0){
  pk = pkA;
  cantKG = 1; 
 } else
 {
  if (cantKG = 1) {
   pk = pkB;
   cantKG = 2;
  }
 }
 return pk;
}

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (cantKG = 2){
   if (b) {
    x = gen_eph_key(0);
    X = out_noclash(skA,x);
    res = Some((X,x));
    seedA[X] = x; 
   } else
   { 
    x = gen_eph_key(0);
    X = out_noclash(skB,x);
    res = Some((X,x));
    seedB[X] = x;
   }
  }
  return res;
 }
 
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (cantKG = 2){  
   if (!b) {
    y = gen_eph_key(0);
    Y = inp(skB,y);
    res = Some ((Y,y));
    seedB[Y] = y;
   } else
   {
    y = gen_eph_key(0);
    Y = inp(skA,y);
    res = Some((Y,y));
    seedA[Y] = y;
   }
  }
  return res;
 }

 abs D' = D' { KG, Init, Respond, eqS, same_session_string }
 
 fun Main () : message * message * session_string = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  okB = false;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  (alpha,beta,str) = D'(pkA);
  return (alpha,beta,str);
 }
}.

game AKE9_eager6 = AKE9_eager5
where 
 Main = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  okB = false;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  (alpha,beta,str) = D'(pkA);
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  return (alpha,beta,str);
 }.

equiv Eq6 : AKE9_eager5.Main ~ AKE9_eager6.Main : true ==> 
cantKG{1} > 0 => 
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2} by auto.

game AKE9_eager7 = AKE9_eager6
where 
 Main = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  okB = false;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  if (!okB && cantKG = 0) {
   skB = gen_secret_key(0);
   pkB = gen_public_key(skB);
   okB = true;
  } 
  (alpha,beta,str) = D'(pkA);
  return (alpha,beta,str);
 }.


equiv Eq7 : AKE9_eager6.Main ~ AKE9_eager7.Main : true ==> 
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2} 
by eager
{if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 }}.

derandomize.
swap{1} 3 -2.
trivial.
save.

derandomize.
swap{1} 3 -2.
trivial.
save.

derandomize.
trivial.
save.
trivial.
trivial.
save.

game AKE9_eager8 = AKE9_eager7
where 
 Main = {
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skB = dummy;
  pkB = gen_public_key(skB);
  seedA = empty_map;
  seedB = empty_map;
  cantKG = 0;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  (alpha,beta,str) = D'(pkA);
  return (alpha,beta,str);
 } and 
 KG = {
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (cantKG = 0){
  pk = pkA;
  cantKG = 1; 
 } else
 {
  if (cantKG = 1) {
   pk = pkB;
   cantKG = 2;
  }
 }
 return pk;
}.



equiv Eq8 : AKE9_eager7.Main ~ AKE9_eager8.Main : true ==> 
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2} by auto
(={pkA,skA,pkB,skB,seedA,seedB,cantKG} && okB{1}). 

game AKE9_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map
 (* ctxt variables *)
 var pkA_C : public_key
 var pkB_C : public_key
 var cantKG_C : int
 
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (b) {
   x = gen_eph_key(0);
   X = out_noclash(skA,x);
   res = Some((X,x));
   seedA[X] = x; 
  } else
  { 
   x = gen_eph_key(0);
   X = out_noclash(skB,x);
   res = Some((X,x));
   seedB[X] = x;
  }
  return res;
 }
  
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (!b) {
   y = gen_eph_key(0);
   Y = inp(skB,y);
   res = Some ((Y,y));
   seedB[Y] = y;
  } else
  {
   y = gen_eph_key(0);
   Y = inp(skA,y);
   res = Some((Y,y));
   seedA[Y] = y;
   }
  return res;
 }
 (*context implementations *)
 fun KG_C() : public_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG_C = 0) {
   pk = pkA_C;
   cantKG_C = 1;
  } else {
   if (cantKG_C = 1) {
    pk = pkB_C;
    cantKG_C = 2;
   }
  }
  return pk;
 }
 
 fun Init_C(b : bool ) : (message * eph_key) option = {
  var res : (message * eph_key) option = None;
  if (cantKG_C = 2){
   res = Init(b);
  }
  return res;
 }
 
 fun Respond_C(b : bool,X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option = None;
  if (cantKG_C = 2){
   res = Respond(b,X);
  }
  return res;
 }

 abs D' = D' { KG_C, Init_C, Respond_C, eqS, same_session_string }

 fun D''(pkA_ : public_key, pkB_ : public_key) : message * message * session_string = {
  var res : message * message * session_string;
  pkA_C = pkA_;
  pkB_C = pkB_;
  cantKG_C = 0;
  res = D'(pkA_C);
  return res;
 }

 fun Main () : message * message * session_string = {
  var ek : eph_key;
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  seedA = empty_map;
  seedB = empty_map;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  (alpha,beta,str) = D''(pkA,pkB);
  return (alpha,beta,str);
 }
}.

checkproof.

equiv Eq8 : AKE9_eager8.Main ~ AKE9_ctxt.Main : true ==> 
((let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){1} <=>
(let alpha,beta,str = res in
wingame9(pkA,pkB,str,alpha,beta)){2})
by auto (={pkA,skA,pkB,skB,seedA,seedB} &&
(pkA_C{2} = pkA{2} && pkB_C{2} = pkB{2} && cantKG{1} = cantKG_C{2})).




adversary D'' (pkA : public_key, pkB : public_key) : (message * message * session_string)
{
 bool -> (message * eph_key) option; (* Init: start either with A or B *)
 (bool, message) -> (message * eph_key) option; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE9 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (b) {
   x = gen_eph_key(0);
   X = out_noclash(skA,x);
   res = Some((X,x));
   seedA[X] = x; 
  } else
  { 
   x = gen_eph_key(0);
   X = out_noclash(skB,x);
   res = Some((X,x));
   seedB[X] = x;
  }
  return res;
 }
  
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (!b) {
   y = gen_eph_key(0);
   Y = inp(skB,y);
   res = Some ((Y,y));
   seedB[Y] = y;
  } else
  {
   y = gen_eph_key(0);
   Y = inp(skA,y);
   res = Some((Y,y));
   seedA[Y] = y;
   }
  return res;
 }
 
abs D'' = D'' { Init, Respond, eqS, same_session_string }

 fun Main () : message * message * session_string = {
  var ek : eph_key;
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  seedA = empty_map;
  seedB = empty_map;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  (alpha,beta,str) = D''(pkA,pkB);
  return (alpha,beta,str);
 }
}.

