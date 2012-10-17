include "ake_game3.ec".

game AKE4 = {
 var b : bool
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (session_string, session_key) map
 var LHT       : (session_string, session_key) map
 var seed     : (part * message, eph_key) map
 var tested_session : (session_id, session_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var keys_revealed : (session_id, bool) map
 var sid_queries : session_id list
 var sess : int
 var part : int

 fun KG = AKE3.KG
 fun Init = AKE3.Init 
 fun Respond = AKE3.Respond
 fun Complete = AKE3.Complete
 fun Corrupt  = AKE3.Corrupt

(* ORACLE *)
(* msg_seeds[(sk,ek)] is typically a hash of sk|ek *)
 (* Auxiliary function *)
 fun iH(lam : session_string) : session_key = {
  var h : session_key = gen_session_key();
  var sk : session_key;
  if (!in_dom(lam, LH) && !in_dom(lam, LHT)) { LH[lam] = h; sk = h;}
  else {
   if (in_dom(lam, LHT)) {
    sk = LHT[lam];
   } else {
    sk = LH[lam];
   }
  }
  return sk;
 }
 
 fun H = AKE3.H


 fun iHT(lam : session_string) : session_key = {
  var h : session_key = gen_session_key();
  var sk : session_key;
  if (!in_dom(lam, LH) && !in_dom(lam, LHT)) { LHT[lam] = h; sk = h;}
  else {
   if (in_dom(lam, LHT)) {
    sk = LHT[lam];
   } else {
    sk = LH[lam];
   }
  }
  return sk;
  
 }

 fun MsgSeedReveal (sk : secret_key, ek : eph_key) : msg_seed = {
  return msg_seeds[(sk,ek)];
 }
 fun compute_key(s : session_id) : session_key = {
  var sstr : session_string = gen_session_string_sid(s,skey,seed);
  var ssskey : session_key;
  ssskey = iH(sstr);
  return ssskey;
 }
 fun compute_keyT(s : session_id) : session_key = {
  var sstr : session_string = gen_session_string_sid(s,skey,seed);
  var ssskey : session_key;
  ssskey = iHT(sstr);
  return ssskey;
 }

fun KeyReveal (s : session_id) : session_key = { 
 var A:part;
 var B:part;
 var X:message;
 var Y:message;
 var B' : part = dummy_part;
 var Y' : message = dummy_msg;
 var eph_flagA : bool = false;
 var eph_flagB : bool = false;
 var A' : part = dummy_part;
 var X' : message = dummy_msg;
 var sstr : session_string = dummy_string;
 var ssskey : session_key = dummy_session_key;
 var matchb : bool = false;
 var h : session_key = dummy_session_key;
 var sidA, sidB : session_id;
 var x : eph_key;
 (A,B,X,Y) = s;
 x = seed[(A,X)];
 sid_queries = s::sid_queries;
 h = gen_session_key();
 if (!coll_session_id(sid_queries,skey,seed)) {
  if (in_dom((A,X), complete_sessions) && 
   !in_dom(s,tested_session) &&
   !in_dom(get_matching_session(s),tested_session)) 
  { (* (A,_,X,_) is completed*)
   B' = session_part(complete_sessions[(A,X)]);
   Y' = session_msg(complete_sessions[(A,X)]);
   sidA = mk_sid(A, B', X, Y');
   if ( B = B' && Y = Y') 
   {(* B = B' /\ Y = Y'*)
    if (!in_dom((B,Y), complete_sessions)) 
    {(*B,_,Y,_ not complete*)
     keys_revealed[s] = true;
     ssskey = compute_key(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions[(B,Y)]);
     X' = session_msg(complete_sessions[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb ) 
     { (*  matches *)
      ssskey = compute_key(s);
      keys_revealed[s] = true;
      keys_revealed[(B,A,Y,X)] = true;
     }
       else 
     {(*not match*)
      keys_revealed[s] = true; 
      ssskey = compute_key(s);
     }
    }
   }(* B = B' /\ Y = Y'*)	
     else
   {  (*   B <> B' \/ Y <> Y'*)
    ssskey = dummy_session_key;
   } 
  }(* (A,_,X,_) is completed*)
  else
  {
   ssskey = dummy_session_key;
  }
 } else
 {
  ssskey = dummy_session_key;
 }
 return ssskey;
} 
fun Test(s : session_id) : session_key =
{
 var A:part = fstpart(s);
 var B:part = sndpart(s);
 var X:message = fstmsg(s);
 var Y:message = sndmsg(s);
 var x : eph_key = seed[(A,X)];
 var B' : part = dummy_part;
 var Y' : message = dummy_msg;
 var kr_flagA : bool = false;
 var kr_flagB : bool = false;
 var corr_flagA : bool = false;
 var corr_flagB : bool = false;
 var eph_flagA : bool = false;
 var eph_flagB : bool = false;
 var A' : part = dummy_part;
 var X' : message = dummy_msg;
 var sstr : session_string = dummy_string;
 var ssskey : session_key = dummy_session_key;
 var matchb : bool = false;
 var h : session_key = dummy_session_key;
 var sidA, sidB : session_id;
 sid_queries = s::sid_queries;
 h = gen_session_key();
 if (!coll_session_id(sid_queries,skey,seed)) {
  if (in_dom(s, tested_session) || 
   in_dom(get_matching_session(s),tested_session)) {
   if(in_dom(s, tested_session)) {
    ssskey = tested_session[s];
   } else {
    ssskey = tested_session[get_matching_session(s)];
   }
  }
    else{(*not a tested session*)
   if (in_dom((A,X), complete_sessions) &&
    fresh_sid_op(s,corrupt,complete_sessions,incomplete_sessions) &&
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)&&
    !keys_revealed[s] && !keys_revealed[get_matching_session(s)]) 
   { (* (A,_,X,_) is completed*)
    B' = session_part(complete_sessions[(A,X)]);
    Y' = session_msg(complete_sessions[(A,X)]);
    if ( B = B' && Y = Y') 
    {(* B = B' /\ Y = Y'*)
     if (in_dom((B,Y), complete_sessions)) 
     { (*B,_,Y_ complete *)
      A' = session_part(complete_sessions[(B,Y)]);
      X' = session_msg(complete_sessions[(B,Y)]);
      sidB = mk_sid(B,A,Y,X);
      matchb = session_match(s, sidB);
      if ( matchb ) 
      { (* matches*)
       if (in_dom(sidB, tested_session)) {
        ssskey = tested_session[sidB];
        tested_session[s] = ssskey;
       }
         else {(* matching session not tested*)
          if (b) {
           ssskey = h;
          }
          else {
           ssskey = compute_keyT(s);
          }
        tested_session[s] = ssskey;
       }
      }
        else 
      {(*not match*)
       if (b) {
        ssskey = h;
       }
       else {
        ssskey = compute_keyT(s);
       }
       tested_session[s] = ssskey;
      }
     }
       else
     {(*B,_,Y,_ not complete*)
      if (b) {
       ssskey = h;
      }
      else {
       ssskey = compute_keyT(s);
      }
      tested_session[s] = ssskey;
     }
    }(* B = B' /\ Y = Y'	*)
      else
    {  (*   B <> B' \/ Y <> Y'*)
     ssskey = dummy_session_key;
    } 
   }(* (A,_,X,_) is completed*)
   else
   {
    ssskey = dummy_session_key;
   }
  }} 
 else
 {
   ssskey = dummy_session_key;
  }
 return ssskey;
 
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
    if (fresh_op(tested_session,corrupt,
       complete_sessions[(A,X) <- (B,Y,true)],incomplete_sessions)){
     complete_sessions[(A,X)] = (B,Y,true);
     ekey = Some (seed[(A,X)]);
    }
   }
    else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions)) {
     B = fst(incomplete_sessions[(A,X)]);
     if(fresh_op(tested_session,corrupt,complete_sessions,
       incomplete_sessions[(A,X) <- (B, true)])) {
      incomplete_sessions[(A,X)] = (B, true);
      ekey = Some (seed[(A,X)]);     
     }
    }
   }
   return ekey;  
}




 abs A = A { KG, Init, Respond, Complete, Corrupt, KeyReveal, H, Test, EphKeyReveal, MsgSeedReveal }
 
 fun Main () : bool = {
  var b' : bool;
  var tt : unit;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corrupt = empty_map;
  pkey = empty_map;
  skey = empty_map;
  LH  = empty_map;
  LHT  = empty_map;
  seed  = empty_map;
  tested_session = empty_map;
  msg_seeds = empty_map;
  keys_revealed = empty_map;
  part = 0;
  sess = 0;
  sid_queries = [];
  b = {0,1};
  b' = A();
  return (b = b');
 }
}.

