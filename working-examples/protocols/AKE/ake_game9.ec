 (*ephkA -- ephkB *)

include "ake_game5'.ec".


adversary D () : (message * message * session_string)
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
 
abs D = D { Init, Respond, eqS, same_session_string }

 fun Main () : message * message * session_string = {
  var ek : eph_key;
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  var test : bool;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0);
  pkB = gen_public_key(skB);
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
