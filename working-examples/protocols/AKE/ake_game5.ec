include "ake_proof_reduction45.ec".

game AKE5 = {
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var seed     : (message * part, eph_key) map
 var bad_C      : bool

 fun KG() : public_key  = {
  var sk : secret_key = gen_secret_key(0);
  var pk : public_key = gen_public_key(sk);
   if (!in_dom(pk,skey)) 
   {
    corrupt[pk] = false;
    skey[pk] = sk;
   } else
   {
    bad_C = true;
   }
  return pk;
 } 

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 

 fun Init(A:part, B:part) : message = {
  var x : eph_key = gen_eph_key(0);
  var a : secret_key;
  var X : message;
  if (in_dom(A, skey) && in_dom(B, skey)){
   a = skey[A];
   X = out_noclash(a, x);
   if (!in_dom((X,A), seed)) {
    incomplete_sessions[(A,X)] = (B,false);
    seed[(X,A)] = x;
   }
   else 
   {
    X = dummy_message;
   }
  }
  else {
   X = dummy_message;
  }
  return X;
 }
 
 fun Respond(B:part, A:part, X: message) : message = {
  var y : eph_key; 
  var Y : message = dummy_message;
  if (in_dom(A, skey) && in_dom(B, skey)) {
   y = gen_eph_key(0); 
   Y = inp(skey[B], y);
   if (!in_dom((Y,B), seed)){
    complete_sessions[(B,Y)] = mk_session_descr(A, X, false, false);
    seed[(Y, B)] = y;
   } else {Y = dummy_message;} 
  }
  return Y;
 }
 
 fun Complete(A:part, B:part, X:message, Y:message) : unit = {
  var B' : part;
  var eph_flag : bool;
  if (in_dom((A,X), incomplete_sessions)) {
   B' = fst(incomplete_sessions[(A,X)]);
   eph_flag = snd(incomplete_sessions[(A,X)]);
   if (B' = B && !in_dom((A,X), complete_sessions)) {
    complete_sessions[(A,X)] = mk_session_descr(B,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 }
 
 fun Corrupt(A : part) : secret_key = {
  var a : secret_key = dummy;
  if (in_dom(A,skey))
  {
   corrupt[A] = true;
   a = skey[A];
  }
  return a;
 } 
 
 fun EphKeyReveal(A : part, X : message) : eph_key = { 
  var kr_flagA : bool = false;
  var corr_flagA : bool = false;
  var test_flagA : bool = false;
  var B : part;
  var Y : message;
  var s : session_id;
  var ekey : eph_key;
  corr_flagA = corrupt[A];
  if (!corr_flagA) (* not corrupted*)
  {
   if (in_dom((A,X), complete_sessions)) {
    kr_flagA = session_key_reveal_flag(complete_sessions[(A,X)]);
    B = session_part(complete_sessions[(A,X)]);
    Y = session_msg(complete_sessions[(A,X)]);
    s = mk_sid(A,B,X,Y);
    complete_sessions[(A,X)] = mk_session_descr(B,Y,true,kr_flagA);
    ekey = seed[(X,A)];
   }
     else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions)) {
     B = fst(incomplete_sessions[(A,X)]);
     incomplete_sessions[(A,X)] = (B, true);
     ekey = seed[(X,A)];     
    }
      else {
      (*not in complete, not in incomplete*)
     ekey = dummy_eph_key;
    }
   }
  }
    else (*corrupted*)
  {
   ekey = dummy_eph_key;
  }
  return ekey;  
 }

 abs B = B { KG, Init, Respond, Complete, Corrupt, EphKeyReveal, eqS, same_session_string }

 fun Main () : session_id * session_string = {
  var sidss : session_id * session_string;
  bad_C = false;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corrupt = empty_map;
  pkey = empty_map;
  skey = empty_map;
  seed  = empty_map;
  sidss = B();
  return (sidss);
 }
}.
(*
claim PR_Abstraction :
AKE5_red.Main[wingame5(fst(res),snd(res),corrupt,complete_sessions_B,incomplete_sessions_B)] = 
AKE5.Main[wingame5(fst(res),snd(res),corrupt,complete_sessions,incomplete_sessions)] admit.

claim PRSplit : 
AKE5.Main[wingame5(fst(res),snd(res),corrupt,complete_sessions,incomplete_sessions)]  =
AKE5.Main[wingame5(fst(res),snd(res),corrupt,complete_sessions,incomplete_sessions) && true]. 
*)
