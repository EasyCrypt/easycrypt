(* We allow corruption on A and only ephemeral keys on B *)
(* corresponds to fresh11 *)
include "ake_proof_reduction5'5'_1.ec".



game AKE5'_1 = {
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corruptA : bool
 var seed     : (message * part, eph_key) map
 var pkA : public_key
 var pkB : public_key
 var skA : secret_key
 var skB : secret_key
 var cantKG : int

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 fun KG() : public_key  = {
  var pk : public_key;
  if (cantKG = 0) {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   pk = pkA;
   corruptA = false;
   cantKG = 1;  
  } else {
   if (cantKG = 1){
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    pk = pkB;
    cantKG = 2;
   }
  }
  return pk;
 }
 
 fun Init(b : bool) : message = {
  var x : eph_key = gen_eph_key(0);
  var X : message = dummy_message;
  if (cantKG = 2){
   if (b) {
    X = out_noclash(skA, x);
    if (!in_dom((X,pkA), seed)) {
     incomplete_sessions[(pkA,X)] = (pkB,false);
     seed[(X,pkA)] = x;
    } else {X = dummy_message;}
   }
   else {
    X = out_noclash(skB, x);
    if (!in_dom((X,pkB), seed)) {
     incomplete_sessions[(pkB,X)] = (pkA,false);
     seed[(X,pkB)] = x;
    } else {X = dummy_message;}
   }
  }
   return X;
 }
 
fun Respond(b : bool, X: message) : message = {
 var y : eph_key = gen_eph_key(0);  
 var Y : message = dummy_message;
 if (cantKG = 2){
  if (b){
   Y = inp(skA, y);
   if (!in_dom((Y,pkA), seed)) {
    complete_sessions[(pkA,Y)] = mk_session_descr(pkB, X, false, false);
    seed[(Y, pkA)] = y;
   } else {Y = dummy_message;}
  }
  else
 {
  Y = inp(skB, y);
  if (!in_dom((Y,pkB), seed)) {
   complete_sessions[(pkB,Y)] = mk_session_descr(pkA, X, false, false);
   seed[(Y, pkB)] = y;
  } else {Y = dummy_message;}
 }
}
return Y;
}

fun Complete(b : bool, X, Y : message) : unit ={
 var eph_flag : bool;
 if (b)
 {
  if (in_dom((pkA,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkA,X)]);
   if (!in_dom((pkA,X), complete_sessions)) {
    complete_sessions[(pkA,X)] = mk_session_descr(pkB,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 } else{
  if (in_dom((pkB,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkB,X)]);
   if (!in_dom((pkB,X), complete_sessions)) {
    complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 }
}


 fun Corrupt() : secret_key = {
  if (cantKG = 2){
   corruptA = true;}
  return (skA);
 } 
 
 fun EphKeyReveal(X : message) : eph_key = { 
  var kr_flagA : bool = false;
  var corr_flagA : bool = false;
  var test_flagA : bool = false;
  var B : part;
  var Y : message;
  var s : session_id;
  var ekey : eph_key = dummy_eph_key;
  if (in_dom((pkB,X), complete_sessions)) {
   kr_flagA = session_key_reveal_flag(complete_sessions[(pkB,X)]);
   B = session_part(complete_sessions[(pkB,X)]);
   Y = session_msg(complete_sessions[(pkB,X)]);
   s = mk_sid(pkB,pkA,X,Y);
   complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,true,kr_flagA);
   ekey = seed[(X,pkB)];
  }
    else {(*not in complete*)
   if (in_dom((pkB,X), incomplete_sessions)) {
    B = fst(incomplete_sessions[(pkB,X)]);
    incomplete_sessions[(pkB,X)] = (pkA, true);
    ekey = seed[(X,pkB)];     
   }
  }
  return ekey;  
 }

abs D = D {KG, Init, Respond, Complete, Corrupt, EphKeyReveal, eqS, same_session_string }

 fun Main () : session_id * session_string = {
  var sidss : session_id * session_string;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corruptA = false;
  corruptB = false;
  skA = dummy;
  skB = dummy;
  pkA = gen_public_key(skA);
  pkB =gen_public_key(skA);
  cantKG = 0;
  seed  = empty_map;
  sidss = D();
  return sidss;
 }
}.
