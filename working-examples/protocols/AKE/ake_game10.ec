 (*skA -- skB *)
(*true = A, false = B*)
include "ake_game5'.ec".


adversary E (skA, skB : secret_key, AX : message, AY : message, BX : message, BY : message) : session_string
{
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

game AKE10 = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var ephKA_Y : eph_key
 var ephKB_X : eph_key
 var ephKB_Y : eph_key  
 var XA : message
 var YA : message
 var XB : message
 var YB : message

(* var seed     : (message , eph_key) map*)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 abs E = E { eqS, same_session_string }

 fun Main () : session_string = {
  var b : bool; 
  var ek : eph_key;
  var X : message; 
  var Y : message; 
  var str : session_string;
  var test : bool;
  skA = gen_secret_key(0);
  pkA = gen_public_key(skA);
  skB = gen_secret_key(0); 
  pkB = gen_public_key(skB);
  ephKA_X = gen_eph_key(0);
  ephKA_Y = gen_eph_key(0);
  ephKB_X = gen_eph_key(0);
  ephKB_Y = gen_eph_key(0);
  XA = inp(skA,ephKA_X);
  YA = inp(skA,ephKA_Y);
  XB = inp(skB,ephKB_X);
  YB = inp(skB,ephKB_Y);
  str = E(skA,skB, XA, YA, XB, YB);
  return (str);
 }
}.

op wingame81
(pkA     : public_key, 
 skA     : secret_key,
 pkB     : public_key, 
 skB     : secret_key, 
 ephKA_X : eph_key,
 ephKA_Y : eph_key,
 ephKB_X : eph_key,
 ephKB_Y : eph_key,  
 XA : message,
 YA : message,
 XB : message,
 YB : message,
 str : session_string) =
str = gen_session_string(skA,ephKA_X,pkB,YB) ||
str = gen_session_string(skA,ephKA_X,pkB,XB) ||
str = gen_session_string(skB,ephKB_X,pkA,XA) ||
str = gen_session_string(skB,ephKB_X,pkA,YA).

