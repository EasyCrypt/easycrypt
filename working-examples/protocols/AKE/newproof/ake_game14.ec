include "ake_game13.ec".

adversary B () : session_id * session_string {
 () -> public_key option;
 (part, part) -> message option;
 (part, part, message) -> message option;
 (part, part, message, message) -> unit;
  part -> secret_key option;
 (part, message) -> eph_key option;
 (secret_key, eph_key) -> msg_seed
}.

game AKE14 = {
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var seed     : (part * message, eph_key) map
(* var tested_session : (session_id, session_key) map*)
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var sess : int
 var part : int

 fun KG() : public_key option = {
  var sk : secret_key = gen_secret_key();
  var pk : public_key = gen_public_key(sk);
  var res : public_key option = None;
  if (!in_dom(pk,skey) && part < qPart) 
  {
   res = Some(pk);
   corrupt[pk] = false;
   skey[pk] = sk;
   part = part + 1;
  }
  return res;
 } 
 
 fun Init = AKE10.Init
 fun MsgSeedReveal = AKE10.MsgSeedReveal
 
 fun Respond(B:part, A:part, X: message) : message option = {
  var y : eph_key = gen_eph_key();  
  var msgs : msg_seed = gen_msg_seed();
  var Y : message option = Some(inp(skey[B], y, msgs));
  if (!in_dom((B,proj(Y)), seed) && in_dom(A, skey) && in_dom(B, skey)
   && sess < qSess) {
   complete_sessions[(B,proj(Y))] = (A, X, false);
   seed[(B,proj(Y))] = y;
   msg_seeds[(skey[B],y)] = msgs;
   sess = sess + 1;
  }
  else {Y = None;}
  return Y;
 }
 
 fun Complete(A:part, B:part, X:message, Y:message) : unit = {
  var x : eph_key = seed[(A,X)];
  var B' : part;
  var eph_flag : bool;
  if (in_dom((A,X), incomplete_sessions)) {
   B' = fst(incomplete_sessions[(A,X)]);
   eph_flag = snd(incomplete_sessions[(A,X)]);
   if (B' = B && !in_dom((A,X), complete_sessions)) {
    complete_sessions[(A,X)] = (B,Y,eph_flag);
    (*get rid of the session in incomplete*)
   }
  }
 }


 fun Corrupt(A : part) : secret_key option = {
   var a : secret_key option = None;
    if (in_dom(A,skey))
    {
     corrupt[A] = true;
     a = Some(skey[A]);
    }
   return a;
  }

  fun EphKeyReveal(A : part, X : message) : eph_key option = { 
   var corr_flagA : bool = false;
   var test_flagA : bool = false;
   var B : part;
   var Y : message;
   var s : session_id;
   var ekey : eph_key option = None;
   if (in_dom((A,X), complete_sessions)) {
    B = session_part(complete_sessions[(A,X)]);
    Y = session_msg(complete_sessions[(A,X)]);
    s = mk_sid(A,B,X,Y);
    complete_sessions[(A,X)] = (B,Y,true);
    ekey = Some (seed[(A,X)]);
   }
     else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions)) {
     B = fst(incomplete_sessions[(A,X)]);
     incomplete_sessions[(A,X)] = (B, true);
     ekey = Some (seed[(A,X)]);     
    }
   }
   return ekey;  
  }

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 abs B = B { KG, Init, Respond, Complete, Corrupt, EphKeyReveal, MsgSeedReveal }

 fun Main () : session_id * session_string = {
  var res : session_id * session_string;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corrupt = empty_map;
  pkey = empty_map;
  skey = empty_map;
  seed = empty_map;
  msg_seeds = empty_map;
  sess = 0;
  part = 0;
  res = B();
  return res;
 }
}.

op wingame13 :
(session_id,
 session_string,
 (part, secret_key) map,
 (part * message, eph_key) map,
 (part, bool) map,
 complete_session_with_status,
 incomplete_session_with_status) -> bool.


axiom wingame13_def :
forall(sid : session_id,
 str : session_string,
 skey : (part, secret_key) map,
 seed : (part * message, eph_key) map,
 crpt : (part, bool) map,
 cs : complete_session_with_status,
 ics : incomplete_session_with_status), 
wingame13(sid,str,skey,seed,crpt,cs,ics) <=> 
(gen_session_string_sid(sid,skey,seed) = str &&
 fresh_sid(sid,crpt,cs,ics) && 
 in_dom(fstpart(sid),skey) &&
  in_dom(sndpart(sid),skey)).
 