(*ephkA -- skB *)
include "ake_game5'.ec".


adversary D (skB : secret_key, X : message ) :  (message * session_string)
{
 () -> message * eph_key ; (* Init: start either with A or B *)
 message -> message  * eph_key; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE81 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
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
 var X : message; 
 var Y : message; 
 var alpha : message; 
 var str : session_string;
 var test1 : bool;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 skA = gen_secret_key(0);
 pkA = gen_public_key(skA);
 skB = gen_secret_key(0);
 pkB = gen_public_key(skB);
 ephKA_X = gen_eph_key(0);
 X = out_noclash(skA,ephKA_X);
 seedB  = empty_map;
 (alpha,str) = D(skA, X);
 return (alpha,str);
 }
}.

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
 (alpha,str) = D(skA, Y);
 return (alpha,str);
 }
}.

op wingame81
(A : public_key,
 B : public_key,
 X : message,
 alpha : message,
 str : session_string,
 complete_session : complete_session_with_status) =
eqS_oracle(str,(A,B,X,alpha)).


op wingame82
(A : public_key,
 B : public_key,
 alpha : message,
 Y : message,
 str : session_string,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status) =
eqS_oracle(str,(B,A,alpha,Y)).

(* too strong? *)
 (* && in_dom((B,alpha),incomplete_session) &&  *)
(* A = fst(incomplete_session[(B,alpha)]) &&  *)
(* in_dom((A,Y),complete_session) && session_part(complete_session[(A,Y)]) = B && *)
(* session_msg(complete_session[(A,Y)]) = alpha. *)

