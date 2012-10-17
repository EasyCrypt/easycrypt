include "basic_defs.ec".

adversary A () : bool  
{
  () -> public_key option;
  (part, part) -> message option;
  (part, part, message) -> message option;
  (part, part, message, message) -> unit;
  part -> secret_key option;
  session_id -> session_key;
  session_string -> session_key;
  session_id -> session_key;
  (part, message) -> eph_key option;
  (secret_key, eph_key) -> msg_seed
}.


game AKE1 = {
 var b : bool
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (session_string, session_key) map
 var seed     : (part * message, eph_key) map
(* var G : (session_id, session_key) map*)
 var tested_session : (session_id, session_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var keys_revealed : (session_id, bool) map
 var part : int
 var sess : int

 fun KG() : public_key option = {
  var sk : secret_key = gen_secret_key();
  var pk : public_key = gen_public_key(sk);
  var res : public_key option = None;
  if (!in_dom(pk,skey) && part < qPart) 
  {
   corrupt[pk] = false;
   skey[pk] = sk;
   part = part + 1;
   res = Some(pk);
  }
  return res;
 } 

(* ORACLE *)
(* msg_seeds[(sk,ek)] is typically a hash of sk|ek *)
 fun MsgSeedReveal (sk : secret_key, ek : eph_key) : msg_seed = {
  return msg_seeds[(sk,ek)];
 }

 (* Auxiliary function *)
 fun iH(lam:session_string) : session_key = {
  var h : session_key = gen_session_key();
  if (!in_dom(lam, LH)) { LH[lam] = h; }
  return LH[lam];
 }
 
(* ORACLE *)
 fun H(str : session_string) : session_key = {
  var sk : session_key;
  sk = iH(str);
  return sk;
 }

(* ORACLE *)
(*Intializes a session between A and B *)
 fun Init(A:part, B:part) : message option = {
  var x : eph_key = gen_eph_key();
  var X : message option = None;
  var msgs : msg_seed = gen_msg_seed();
  if (in_dom(A, skey) && in_dom(B, skey) && sess < qSess){
   X = Some(out(skey[A], x, msgs));
   if (!in_dom((A,proj(X)), seed)) {
    incomplete_sessions[(A,proj(X))] = (B,false);
    seed[(A,proj(X))] = x;
    msg_seeds[(skey[A],x)] = msgs;
    sess = sess + 1;
   }   
   else 
   { 
    X = None;
   }
  }
  return X;
 }
 
 fun Respond(B:part, A:part, X: message) : message option = {
  var y : eph_key = gen_eph_key();  
  var msgs : msg_seed = gen_msg_seed();
  var Y : message option = Some(inp(skey[B], y, msgs));
  if (!in_dom((B,proj(Y)), seed) && in_dom(A, skey) && in_dom(B, skey)
   && sess < qSess && !in_dom((B,proj(Y)),complete_sessions) &&
   !in_dom((B,A,proj(Y),X),keys_revealed)) {
   complete_sessions[(B,proj(Y))] = (A, X, false);
   keys_revealed[(B,A,proj(Y),X)] = false;
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
   if (B' = B && !in_dom((A,X), complete_sessions)
    && !in_dom((A,B,X,Y),keys_revealed)) {
    complete_sessions[(A,X)] = (B,Y,eph_flag);
    keys_revealed[(A,B,X,Y)] = false;
    (*get rid of the session in incomplete*)
   }
  }
 }
 
 fun Corrupt(A : part) : secret_key option = {
   var a : secret_key option = None;
    if (in_dom(A,skey))
    {
     if (fresh_op(tested_session,corrupt[A <- true],
       complete_sessions,incomplete_sessions)) {
      corrupt[A] = true;
      a = Some(skey[A]);
     }
    }
   return a;
  }

 fun compute_key(s : session_id) : session_key = {
  var sstr : session_string = gen_session_string_sid(s,skey,seed);
  var ssskey : session_key;
  ssskey = iH(sstr);
  return ssskey;
 }

 fun KeyReveal(s : session_id) : session_key = { 
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
   var ssskey : session_key = dummy_session_key;
   var matchb : bool = false;
   var h : session_key = dummy_session_key;
   var sidA, sidB : session_id;
   var x : eph_key;
   (A,B,X,Y) = s;
   x = seed[(A,X)];
   h = gen_session_key();
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
        ssskey = compute_key(sidA);
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
   h = gen_session_key();
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions) &&
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
           ssskey = compute_key(s);
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
           ssskey = compute_key(s);
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
       ssskey = compute_key(s);
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
  seed  = empty_map;
  tested_session = empty_map;
 (* G = empty_map;*)
  msg_seeds = empty_map;
  keys_revealed = empty_map;
  part = 0;
  sess = 0;
  b = {0,1};
  b' = A();
  return (b = b');
 }
}.