(*ephkA -- skB *)
include "ake_game5a.ec".

adversary D' () :  (message * session_string)
{
 () -> public_key ;
 () -> secret_key;
 () -> message;
 () -> message * eph_key ; (* Init: start either with A or B *)
 message -> message  * eph_key; (* Respond *)
 (message, message) -> unit;
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.



game AKE81' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int
 var cantKG : int

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key ={
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG = 0) {
   sk = gen_secret_key(0);
   skA = sk;
   pk = gen_public_key(sk);
   pkA = pk;
   cantKG = 1;
  } else {
   if (cantKG = 1) {
    sk = gen_secret_key(0);
    skB = sk;
    pk = gen_public_key(sk);
    pkB = pk;
    cantKG = 2;
   }
  }
  return pk;
 }
 
 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (cantKG > 1 && initA_done = 0){
   x = gen_eph_key(0);
   ephKA_X = x;
   X = out_noclash(skA,x);
   incomplete_sessions[(pkA,X)] = (pkB,false);
   initA_done = 1;
  }
  return (X);
 }
 
 fun CorruptA() : secret_key = {
  var sk : secret_key = dummy;
  if (cantKG > 0) {
  sk = skA;
  }
  return sk;
 } 
 
 fun InitB() : message * eph_key = {
  var X : message = dummy_message;
  var x : eph_key = dummy_eph_key;
  if (cantKG > 1 ){
   x = gen_eph_key(0);
   X = out_noclash(skB,x);
   seedB[X] = x;
   incomplete_sessions[(pkB,X)] = (pkA,false);
  }
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message = dummy_message;
 var y : eph_key = dummy_eph_key;
 if (cantKG > 1 ){
  y = gen_eph_key(0);
  Y = inp(skB,y);
  seedB[Y] = y;
  complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 }
  return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (cantKG > 1) {
  if (in_dom((pkB,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkB,X)]);
   if (!in_dom((pkB,X), complete_sessions)) {
    complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
   }
  }
 }
}
 
abs D' = D' { KG, CorruptA, InitA, InitB, RespondB, Complete, eqS, same_session_string }

  
fun Main () : message * session_string = {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 (alpha,str) = D'();
 return (alpha,str);
 }
}.

(* game AKE82 = { *)
(*  var pkA     : public_key  *)
(*  var skA     : secret_key  *)
(*  var pkB     : public_key  *)
(*  var skB     : secret_key  *)
(*  var ephKA_Y : eph_key *)
(*  var seedB   : (message, eph_key) map  *)
(*  var complete_sessions : complete_session_with_status *)
(*  var incomplete_sessions : incomplete_session_with_status *)
(*  fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = { *)
(*   return (same_session_string_oracle(sid1,sid2)); *)
(*  } *)
 
(*  fun eqS(str : session_string, sid : session_id) : bool = { *)
(*   return (eqS_oracle(str,sid)); *)
(*  } *)
 

(*  fun InitB() : message * eph_key = { *)
(*   var X : message; *)
(*   var x : eph_key; *)
(*   x = gen_eph_key(0); *)
(*   X = out_noclash(skB,x); *)
(*   seedB[X] = x;   *)
(*   incomplete_sessions[(pkB,X)] = (pkA,false); *)
(*   return (X,x); *)
(*  } *)
 
 
(*  fun RespondB(X : message) : message * eph_key = { *)
(*  var Y : message; *)
(*  var y : eph_key; *)
(*  y = gen_eph_key(0); *)
(*  Y = inp(skB,y); *)
(*  seedB[Y] = y; *)
(*  complete_sessions[(pkB,Y)] = (pkA,X,false,false);  *)
(*  return (Y,y); *)
(* } *)
 
(* abs D = D { InitB, RespondB, eqS, same_session_string } *)
  
(* fun Main () : message * session_string = { *)
(*  var Y : message;  *)
(*  var alpha : message;  *)
(*  var str : session_string; *)
(*  var test2 : bool; *)
(*  skA = gen_secret_key(0); *)
(*  pkA = gen_public_key(skA); *)
(*  skB = gen_secret_key(0); *)
(*  pkB = gen_public_key(skB); *)
(*  ephKA_Y = gen_eph_key(0); *)
(*  Y = inp(skA,ephKA_Y); *)
(*  seedB  = empty_map; *)
(*  (alpha,str) = D(skA, Y); *)
(*  return (alpha,str); *)
(*  } *)
(* }. *)

op wingame81
(A : public_key,
 B : public_key,
 X : message,
 alpha : message,
 str : session_string,
 complete_session : complete_session_with_status) =
eqS_oracle(str,(A,B,X,alpha)).


(* op wingame82 *)
(* (A : public_key, *)
(*  B : public_key, *)
(*  alpha : message, *)
(*  Y : message, *)
(*  str : session_string, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status) = *)
(* eqS_oracle(str,(B,A,alpha,Y)). *)

(* too strong? *)
 (* && in_dom((B,alpha),incomplete_session) &&  *)
(* A = fst(incomplete_session[(B,alpha)]) &&  *)
(* in_dom((A,Y),complete_session) && session_part(complete_session[(A,Y)]) = B && *)
(* session_msg(complete_session[(A,Y)]) = alpha. *)

game AKE81'_eager_1 =  
 AKE81'
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
} 

and Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okA = false;
 okB = false;
 (alpha,str) = D'();
 return (alpha,str);
 }.




equiv KG : AKE81'.KG ~ AKE81'_eager_1.KG :
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,cantKG} &&
 (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2) &&
 (okA{2} <=> cantKG{1} > 0) && (okB{2} <=> cantKG{1} > 1)).
derandomize.
!2 rnd>>.
trivial.
save.


equiv Eq1 : AKE81'.Main ~ AKE81'_eager_1.Main : true ==> 
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}
 by auto
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,cantKG} &&
 (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2) &&
 (okA{2} <=> cantKG{1} > 0) && (okB{2} <=> cantKG{1} > 1)). 


game AKE81'_eager_2 = AKE81'_eager_1 where 
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okA = false;
 okB = false;
 (alpha,str) = D'();
 cantKG = cantKG;
 if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 }
 return (alpha,str);
}.

equiv Eq1 : AKE81'_eager_1.Main ~ AKE81'_eager_2.Main :
 true ==> 
cantKG{1} > 1 => (wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2} by auto.


game AKE81'_eager_3 = AKE81'_eager_2 where 
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skA = dummy;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okA = false;
 okB = false; 
 if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 }
 (alpha,str) = D'();
 cantKG=cantKG;
 return (alpha,str);
}.

equiv Eq2 : AKE81'_eager_2.Main ~ AKE81'_eager_3.Main:  true ==> 
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}
by eager
{ if (!okA && cantKG = 0) 
 {
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  okA = true;
 }
}.


if{1}.
condf{2};condt{2}.
derandomize;trivial.
if.
trivial.
trivial.
save.

sp 2 0.
if{1}.
condf{2}.
sp 0 2.
condt{2}.
rnd>>.
sp 3 0.
condf{1}.
trivial.
if.
rnd >>.
sp 0 4.
condf{2}.
trivial.
sp 0 2.
condf{2}.
trivial.
save.

sp 2 0;if{1}.
condf{2};sp 0 2;condt{2};rnd>>;sp 3 0;condf{1};trivial.
if.
rnd >>;sp 0 4;condf{2};trivial.
sp 0 2;condf{2};trivial.
save.

sp 1 0.
if{1}.
condf{2};sp 0 1;condt{2};rnd>>;sp 4 0;condf{1};trivial.
if.
rnd>>;sp 0 3;condf{2};trivial.
sp 0 1;condf{2};trivial.
save.

sp 1 0.
if{1}.
sp 1 0.
condf.
trivial.
if.
trivial.
trivial.
save.

sp 2 0.
if.
rnd>>.
derandomize.
trivial.
sp 0 2.
condf{2}.
if.
rnd>>;derandomize;trivial.
if.
sp 2 0;condf{1}.
trivial.
if.
sp 2 0;condf{1}.
trivial.
condf{1}.
trivial.
save.

trivial.
trivial.
save.

game AKE81'_eager_4 = AKE81'_eager_3 where 
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okB = false; 
 okA = true;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 (alpha,str) = D'();
 cantKG=cantKG;
 (* if (!okB && cantKG = 1) { *)
 (*  skB = gen_secret_key(0); *)
 (*  pkB = gen_public_key(skB); *)
 (*  okB = true; *)
 (* }  *)
 return (alpha,str);
} 
and
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
 }.


equiv Eq1 : AKE81'_eager_3.Main ~ AKE81'_eager_4.Main :  true ==> 
cantKG{1} > 1 => ((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2})
by auto
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,cantKG,okA,okB} && okA{1} = true).




game AKE81'_eager_5_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var okB : bool
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int
 var cantKG : int
(*context variables *)
 var cantKG_C : int
 var pkA_C     : public_key 
 var skA_C     : secret_key 

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }

fun KG () : public_key = {
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
 
 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (cantKG > 1 && initA_done = 0){
   x = gen_eph_key(0);
   ephKA_X = x;
   X = out_noclash(skA,x);
   incomplete_sessions[(pkA,X)] = (pkB,false);
   initA_done = 1;
  }
  return (X);
 }
  
 fun InitB() : message * eph_key = {
  var X : message = dummy_message;
  var x : eph_key = dummy_eph_key;
  if (cantKG > 1 ){
   x = gen_eph_key(0);
   X = out_noclash(skB,x);
   seedB[X] = x;
   incomplete_sessions[(pkB,X)] = (pkA,false);
  }
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message = dummy_message;
 var y : eph_key = dummy_eph_key;
 if (cantKG > 1 ){
  y = gen_eph_key(0);
  Y = inp(skB,y);
  seedB[Y] = y;
  complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 }
  return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (cantKG > 1){
  if (in_dom((pkB,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkB,X)]);
   if (!in_dom((pkB,X), complete_sessions)) {
    complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
   }
  }
 }
}


(* Adversary implementations *)
fun KG_C () : public_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG_C = 0){
   pk = pkA_C;
   cantKG_C = 1; 
  } else
  {
   if (cantKG_C = 1) {
    pk = KG();
    pk = KG();
    cantKG_C = 2; 
   }
  }
  return pk;
 }

 fun CorruptA_C() : secret_key = {
  var sk : secret_key = dummy;
  if (cantKG_C > 0){
  sk = skA_C;
  }
  return sk;
 } 

 fun InitA_C() : message ={
  var res : message;
  res = InitA();
  return res;
 }
 
 fun InitB_C() : message * eph_key = {
  var res : message * eph_key;
  res = InitB();
  return res;
 }

 fun RespondB_C(X : message) : message * eph_key = {
  var res : message * eph_key;
  res = RespondB(X);
  return res;
 }
 
 fun Complete_C(X : message, Y : message) : unit = {
  Complete(X,Y);
 }
 


abs D' = D' { KG_C, CorruptA_C, InitA_C, InitB_C, RespondB_C, Complete_C, eqS, same_session_string }

fun D''(pkA_ : public_key, skA_ : secret_key) :  (message * session_string) = {
 var res : message * session_string;
 cantKG_C = 0;
 pkA_C = pkA_;
 skA_C = skA_;
 res = D'();
 return res;
}

fun Main() : message * session_string =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okB = false; 
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 (alpha,str) = D''(pkA,skA);
 cantKG=cantKG;
 return (alpha,str);
} 


}.




equiv Red : AKE81'_eager_4.Main ~ AKE81'_eager_5_ctxt.Main : true ==>
 ((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2})
by auto
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,okB} && okA{1} = true && (pkA_C{2} = pkA{2} && skA_C{2} = skA{2} && cantKG{1} = cantKG_C{2} && 
(cantKG_C{2} = 0 => cantKG{2} = 0) &&
(cantKG_C{2} = 1 => cantKG{2} = 0) && (cantKG{2} = 0 => (cantKG_C{2} = 0 || cantKG_C{2} = 1))&&
(cantKG_C{2} = 2 <=> cantKG{2} = 2 && (cantKG = 0 ||cantKG = 1 ||cantKG = 2){2}) &&
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1}
)).


adversary D'' (pkA : public_key, skA : secret_key) :  (message * session_string)
{
 () -> public_key ;(* KG *)
 () -> message;    (* initA *)
 () -> message * eph_key ; (* InitB *)
 message -> message  * eph_key; (* Respond *)
 (message, message) -> unit (*Complete*);
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.


game AKE81'_eager_5 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var okB : bool
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int
 var cantKG : int

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }

fun KG () : public_key = {
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (!okB&& cantKG = 0 ) {
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
 
 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (cantKG > 1 && initA_done = 0){
   x = gen_eph_key(0);
   ephKA_X = x;
   X = out_noclash(skA,x);
   incomplete_sessions[(pkA,X)] = (pkB,false);
   initA_done = 1;
  }
  return (X);
 }
 
 fun InitB() : message * eph_key = {
  var X : message = dummy_message;
  var x : eph_key = dummy_eph_key;
  if (cantKG > 1 ){
   x = gen_eph_key(0);
   X = out_noclash(skB,x);
   seedB[X] = x;
   incomplete_sessions[(pkB,X)] = (pkA,false);
  }
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message = dummy_message;
 var y : eph_key = dummy_eph_key;
 if (cantKG > 1 ){
  y = gen_eph_key(0);
  Y = inp(skB,y);
  seedB[Y] = y;
  complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 }
  return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (cantKG > 1){
  if (in_dom((pkB,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkB,X)]);
   if (!in_dom((pkB,X), complete_sessions)) {
    complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
   }
  }
 }
}

abs D'' = D'' {KG, InitA, InitB, RespondB, Complete, eqS, same_session_string }


fun Main() : message * session_string =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okB = false; 
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 (alpha,str) = D''(pkA,skA);
 cantKG=cantKG;
 return (alpha,str);
} 
}.

game AKE81'_eager_6 = AKE81'_eager_5 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okB = false; 
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 (alpha,str) = D''(pkA,skA);
 cantKG=cantKG;
 if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 }
 return (alpha,str);
}. 

equiv eq_5_6 : AKE81'_eager_6.Main ~ AKE81'_eager_5.Main : true ==> 
cantKG{2} > 1 => (wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}.
sp.
rnd>>.
derandomize.
wp.
call
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,okB,cantKG} &&
(cantKG{2} > 0 => okB{2})). 
trivial.
save.

game AKE81'_eager_7 = AKE81'_eager_6 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 okB = false; 
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 }
 (alpha,str) = D''(pkA,skA);
 cantKG=cantKG;
 return (alpha,str);
}. 

equiv eq_6_7 : AKE81'_eager_6.Main ~ AKE81'_eager_7.Main : true ==> 
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}
by eager
{ if (!okB && cantKG = 0) {
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  okB = true;
 }}.
if{1}.
condf{2}.
condt{2}.
if.
sp 1 1;if.
condf{1}.
trivial.
condf{1}.
trivial.
condf{1}.
trivial.
if.
rnd>>.
sp 2 2.
condf{2}.
trivial.
condf{2}.
trivial.
save.
derandomize;swap{1} 1 1;!2 rnd>>;trivial.
save.
derandomize;swap{1} 1 1;!2 rnd>>;trivial.
save.
derandomize;swap{1} 1 1;!2 rnd>>;trivial.
save.

sp 2 0.
if.
rnd >>.
sp 2 4.
condf{2}.
condt.
sp 2 0;condf{1}.
trivial.
if{1}.
sp 2 2;condf.
condt{2}.
trivial.
sp 0 2;condf{2}.
condf{2}.
if.
sp 2 0;condf{1}.
trivial.
condf{1}.
trivial.
save.
trivial.
trivial.
save.


game AKE81'_eager_8 = AKE81'_eager_7 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 (alpha,str) = D''(pkA,skA);
 cantKG=cantKG;
 return (alpha,str);
} 
and KG  = {
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

equiv eq_7_8 : AKE81'_eager_7.Main ~ AKE81'_eager_8.Main : true ==> 
cantKG{2} > 1 => (wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2} 
by auto 
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done,cantKG} &&
okB{1} = true). 


game AKE81'_eager_9_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int
  (* context state *)
 var pkA_C     : public_key 
 var skA_C     : secret_key 
 var pkB_C     : public_key
 var cantKG_C  : int 

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (initA_done = 0) {
   ephKA_X = gen_eph_key(0);
   initA_done = 1;
  }
  X = out_noclash(skA,ephKA_X);
  incomplete_sessions[(pkA,X)] = (pkB,false);
  return (X);
 }
 
 fun InitB() : message * eph_key = {
  var X : message = dummy_message;
  var x : eph_key = dummy_eph_key;
  x = gen_eph_key(0);
  X = out_noclash(skB,x);
  seedB[X] = x;
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message = dummy_message;
 var y : eph_key = dummy_eph_key;
 y = gen_eph_key(0);
 Y = inp(skB,y);
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (in_dom((pkB,X), incomplete_sessions)) {
  eph_flag = snd(incomplete_sessions[(pkB,X)]);
  if (!in_dom((pkB,X), complete_sessions)) {
   complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
  }
 }
}

  (* Adversary implementations *)
fun KG_C() : public_key ={
 var sk : secret_key = dummy;
 var pk : public_key = gen_public_key(sk);
 if (cantKG_C = 0){
  pk = pkA_C;
  cantKG_C = 1; 
 } else
 {
  if (cantKG_C = 1) {
   pk = pkB_C;
   cantKG_C = 2;
  }
 }
 return pk;
} 
 fun InitA_C() : message ={
  var res : message = dummy_message;
  if (cantKG_C > 1 && initA_done = 0) {
  res = InitA();
  }
  return res;
 }
 
 fun InitB_C() : message * eph_key = {
  var res : message * eph_key = (dummy_message, dummy_eph_key);
  if (cantKG_C > 1) {
   res = InitB();
  }
  return res;
 }

 fun RespondB_C(X : message) : message * eph_key = {
  var res : message * eph_key = (dummy_message, dummy_eph_key);
  if (cantKG_C > 1) {
   res = RespondB(X);
  }
  return res;
 }
 
 fun Complete_C(X : message, Y : message) : unit = {
    if (cantKG_C > 1) {
     Complete(X,Y);
    }
 }
 

abs D'' = D'' { KG_C, InitA_C, InitB_C, RespondB_C, Complete_C, eqS, same_session_string }

fun D'''(pkA_ : public_key, skA_ : secret_key, pkB_ : public_key) : message * session_string = {
 var res : message * session_string;
 pkA_C = pkA_;
 skA_C = skA_;
 pkB_C = pkB_;
 cantKG_C = 0;
 res = D''(pkA_C,skA_C);
 return res;
}

fun Main() : message * session_string =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 (alpha,str) = D'''(pkA,skA,pkB);
 return (alpha,str);
} 

 

}.
equiv Red : AKE81'_eager_8.InitA ~ AKE81'_eager_9_ctxt.InitA_C :
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done} 
&& (pkA_C{2} = pkA{2} && skA_C{2} = skA{2} && pkB_C{2} = pkB{2} 
&& cantKG{1} = cantKG_C{2} && 
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1})).
sp 1 1.
if.
inline.
sp 0 1.
condt{2}.
trivial.
trivial.
save.


equiv Red : AKE81'_eager_8.Main ~ AKE81'_eager_9_ctxt.Main : true ==>
 ((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}).
inline.
wp.
call
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done} 
&& (pkA_C{2} = pkA{2} && skA_C{2} = skA{2} && pkB_C{2} = pkB{2} 
&& cantKG{1} = cantKG_C{2} && 
(cantKG = 0 ||cantKG = 1 ||cantKG = 2){1})).
trivial.
save.


adversary D''' (pkA : public_key, skA : secret_key, pkB : public_key) :  (message * session_string)
{
 () -> message;    (* initA *)
 () -> message * eph_key ; (* InitB *)
 message -> message  * eph_key; (* Respond *)
 (message, message) -> unit (*Complete*);
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE81'_eager_9 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (initA_done = 0) {
   ephKA_X = gen_eph_key(0);
   initA_done = 1;
  }
  X = out_noclash(skA,ephKA_X);
  incomplete_sessions[(pkA,X)] = (pkB,false);
  return (X);
 }
 
 fun InitB() : message * eph_key = {
  var X : message = dummy_message;
  var x : eph_key = dummy_eph_key;
  x = gen_eph_key(0);
  X = out_noclash(skB,x);
  seedB[X] = x;
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message = dummy_message;
 var y : eph_key = dummy_eph_key;
 y = gen_eph_key(0);
 Y = inp(skB,y);
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (in_dom((pkB,X), incomplete_sessions)) {
  eph_flag = snd(incomplete_sessions[(pkB,X)]);
  if (!in_dom((pkB,X), complete_sessions)) {
   complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
  }
 }
}

abs D''' = D''' { InitA, InitB, RespondB, Complete, eqS, same_session_string }

fun Main() : message * session_string =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 (alpha,str) = D'''(pkA,skA,pkB);
 return (alpha,str);
} 
}.

game AKE81'_eager_10 = AKE81'_eager_9 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 (alpha,str) = D'''(pkA,skA,pkB);
 alpha = alpha;
 if (initA_done = 0) {
  ephKA_X = gen_eph_key(0);
  initA_done = 1;
 }
 return (alpha,str);
}.


equiv eq_9_10 : AKE81'_eager_9.Main ~ AKE81'_eager_10.Main : 
true ==> initA_done{1} = 1 =>
((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}) by auto.

game AKE81'_eager_11 = AKE81'_eager_10 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 if (initA_done = 0) {
  ephKA_X = gen_eph_key(0);
  initA_done = 1;
 }
 (alpha,str) = D'''(pkA,skA,pkB);
 alpha = alpha;
 return (alpha,str);
}.


equiv eq_10_11 : AKE81'_eager_10.Main ~ AKE81'_eager_11.Main : 
true ==> 
((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}) by 
eager 
{ if (initA_done = 0) {
  ephKA_X = gen_eph_key(0);
  initA_done = 1;
 }
}.
sp 1 0.
if.
rnd>>.
sp 3 2.
condf.
trivial.
sp 2 1.
condf.
trivial.
save.
trivial.
trivial.
save.

game AKE81'_eager_12 = AKE81'_eager_11 where
Main =  {
 var alpha : message; 
 var str : session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 ephKA_X = gen_eph_key(0);
 initA_done = 1;
 (alpha,str) = D'''(pkA,skA,pkB);
 alpha = alpha;
 return (alpha,str);
}
and InitA = {
 var X : message = dummy_message;
 X = out_noclash(skA,ephKA_X);
 incomplete_sessions[(pkA,X)] = (pkB,false);
 return (X);
}.

equiv eq_11_12 : AKE81'_eager_11.Main ~ AKE81'_eager_12.Main : 
true ==> 
((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}) by auto
(={pkA,skA,pkB,skB,ephKA_X,seedB,complete_sessions,incomplete_sessions,initA_done} &&
initA_done{1} = 1). 

adversary D (skB : secret_key, pkA : public_key, X : message ) :  (message * session_string)
{
 () -> message * eph_key ; (* Init: start either with A or B *)
 message -> message  * eph_key; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE81_ctxt = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 (* context variables *)
 var pkA_C     : public_key 
 var skA_C     : secret_key 
 var pkB_C     : public_key 
 var X_C : message

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }


 fun InitB() : message * eph_key = {
  var X : message;
  var x : eph_key;
  x = gen_eph_key(0);
  X = out_noclash(skB,x);
  seedB[X] = x;  
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
  var Y : message;
  var y : eph_key;
  y = gen_eph_key(0);
  Y = inp(skB,y);
  seedB[Y] = y;
  complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
  return (Y,y);
 }
 
  (* Adversary implementations *)
 fun InitA_C() : message ={
  return X_C;
 }
 
 fun InitB_C() : message * eph_key = {
  var res : message * eph_key;
  res = InitB();
  return res;
 }
 
 fun RespondB_C(X : message) : message * eph_key = {
  var res : message * eph_key;
  res = RespondB(X);
  return res;
 }
 
 fun Complete_C(X : message, Y : message) : unit = {
 }
 
 abs D''' = D''' { InitA_C, InitB_C, RespondB_C, Complete_C, eqS, same_session_string }
 
 fun D(skA_ : secret_key, pkB_ : public_key, X_ : message) : message * session_string = {
  var alpha : message;
  var str : session_string;
  skA_C = skA_;
  pkA_C = gen_public_key(skA_C);
  pkB_C = pkB_;
  X_C = X_;
  (alpha,str) = D'''(pkA_C,skA_C,pkB_C);
  return (alpha,str);
 }
 
 
 fun Main () : message * session_string = {
  var X : message; 
  var alpha : message; 
  var str : session_string;
  var test2 : bool;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
  ephKA_X = gen_eph_key(0);
  X = out_noclash(skA,ephKA_X);
  seedB  = empty_map;
  (alpha,str) = D(skA, pkB, X);
  return (alpha,str);
 }
}.
op wingame81'
(A : public_key,
 B : public_key,
 X : message,
 alpha : message,
 str : session_string,
 complete_session : complete_session_with_status) =
eqS_oracle(str,(A,B,X,alpha)).

equiv Red : AKE81'_eager_12.Main ~ AKE81_ctxt.Main : true ==>
 ((wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){1} <=>
(wingame81'(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2})
by auto
(={pkA,skA,pkB,skB,ephKA_X,seedB} &&  
(pkA_C{2} = pkA{2} && skA_C{2} = skA{2} && X_C{2} = out_noclash(skA{2}, ephKA_X{2})
)).

game AKE82 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_Y : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 

 fun InitB() : message * eph_key = {
  var X : message;
  var x : eph_key;
  x = gen_eph_key(0);
  X = out_noclash(skB,x);
  seedB[X] = x;  
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message;
 var y : eph_key;
 y = gen_eph_key(0);
 Y = inp(skB,y);
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}


 
abs D = D { InitB, RespondB, eqS, same_session_string }
  
fun Main () : message * session_string = {
 var Y : message; 
 var alpha : message; 
 var str : session_string;
 var test2 : bool;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 ephKA_Y = gen_eph_key(0);
 Y = inp(skA,ephKA_Y);
 seedB  = empty_map;
 (alpha,str) = D(skA, pkB, Y);
 return (alpha,str);
 }
}.