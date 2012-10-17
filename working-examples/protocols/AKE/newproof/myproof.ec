include "basic_defs.ec".

checkproof.
adversary A () : bool  
{
  () -> public_key;
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
 var G : (session_id, session_key) map
 var tested_session : (session_id, session_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var keys_revealed : (part * message * part * message, bool) map
 var part : int
 var sess : int

 fun KG() : public_key  = {
  var sk : secret_key = gen_secret_key();
  var pk : public_key = gen_public_key(sk);
  if (!in_dom(pk,skey) && part < qPart) 
  {
   corrupt[pk] = false;
   skey[pk] = sk;
   part = part + 1;
  }
  return pk;
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
   && sess < qSess) {
   complete_sessions[(B,proj(Y))] = (A, X, false);
   keys_revealed[(B,proj(Y),A,X)] = false;
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
    keys_revealed[(A,X,B,Y)] = false;
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
        keys_revealed[(A,X,B,Y)] = true;
        ssskey = compute_key(sidA);
      }
        else { (* B,_,Y_ complete *)
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B, A', Y, X');
       matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
       if ( matchb ) 
       { (*  matches *)
        keys_revealed[(B,Y,A,X)] = true;
        keys_revealed[(A,X,B,Y)] = true;
        ssskey = compute_key(s);
       }
       else 
       {(*not match*)
        keys_revealed[(A,X,B,Y)] = true; 
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
  G = empty_map;
  msg_seeds = empty_map;
  keys_revealed = empty_map;
  part = 0;
  sess = 0;
  b = {0,1};
  b' = A();
  return (b = b');
 }
}.

(*
lemma fresh_sid_lm1 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), incomplete_session) =>  
fresh_sid(sid,corrupt,complete_session,incomplete_session[(A,X) <- (B,flag)]).


lemma fresh_sid_lm2 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid1(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid1(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).
lemma fresh_sid_lm3 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid11(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid11(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm4 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid3(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid3(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm5 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_lm5 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh(ts,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh(ts,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).


lemma fresh_sid_lm8 : 
forall (s : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status, 
 A : part),
fresh_sid(s,corrupt,complete_session,incomplete_session) =>
fresh_sid(s,corrupt[A <- false],complete_session,incomplete_session).

lemma fresh_lm9 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part),
fresh(ts,corrupt,complete_session,incomplete_session) =>
fresh(ts,corrupt[A <- false],complete_session,incomplete_session).

equiv Inv1A : AKE1.A ~ AKE1.A : 
(fresh(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1}) &&
(forall (A : part, X: message), in_dom((A,X),incomplete_sessions{1}) => 
in_dom((A,X),seed{1})) &&
(forall (A : part, X: message), in_dom((A,X),complete_sessions{1}) => 
in_dom((A,X),seed{1})) && ={keys_revealed,msg_seeds,tested_session,G,seed,LH,skey,pkey,corrupt,incomplete_sessions,complete_sessions,b}) by auto.
*)
op coll_session_id : (session_id list,(part,secret_key) map,(part * message, eph_key) map) -> bool.

op matching_session_id (s1,s2: session_id) = s1=s2 || s1 = get_matching_session (s2).


axiom coll_session_id_def : forall (SIDL : session_id list,skey:(part,secret_key) map,seed:(part * message, eph_key) map), 
  (coll_session_id(SIDL,skey,seed) <=>
    (exists(x,x':session_id), mem(x,SIDL)
      && mem(x',SIDL)
      && gen_session_string_sid(x,skey,seed) = gen_session_string_sid(x',skey,seed) 
      && !matching_session_id(x,x'))).


game AKE2 = 
AKE1 
var sid_queries : session_id list
where
KeyReveal = { 
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
     keys_revealed[(A,X,B,Y)] = true;
     ssskey = compute_key(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions[(B,Y)]);
     X' = session_msg(complete_sessions[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb ) 
     { (*  matches *)
      keys_revealed[(B,Y,A,X)] = true;
      keys_revealed[(A,X,B,Y)] = true;
      ssskey = compute_key(s);
     }
       else 
     {(*not match*)
      keys_revealed[(A,X,B,Y)] = true; 
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
} and
  Test =
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
} and 
 Main  = {
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
  G = empty_map;
  msg_seeds = empty_map;
  keys_revealed = empty_map;
  part = 0;
  sess = 0;
  sid_queries = [];
  b = {0,1};
  b' = A();
  return (b = b');
 }.

equiv Eq1 : AKE1.Main ~ AKE2.Main : 
true ==>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, res, sess, part} by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,LH, sess, part}).

checkproof.
claim C1 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE2.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] 
using Eq1.
checkproof.

game AKE3 = 
AKE2 
where
KeyReveal = { 
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
     keys_revealed[(A,X,B,Y)] = true;
     ssskey = compute_key(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions[(B,Y)]);
     X' = session_msg(complete_sessions[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb ) 
     { (*  matches *)
      keys_revealed[(B,Y,A,X)] = true;
      keys_revealed[(A,X,B,Y)] = true;
      ssskey = compute_key(s);
     }
       else 
     {(*not match*)
      keys_revealed[(A,X,B,Y)] = true; 
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
} and
  Test =
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
 }
  else
  {
   ssskey = dummy_session_key;
  }
 return ssskey;
 
}.


equiv Eq2 : AKE2.Main ~ AKE3.Main : 
true ==>
(!coll_session_id(sid_queries{1},skey{1},seed{1})
<=> !coll_session_id(sid_queries{2},skey{2},seed{2})) &&
(!coll_session_id(sid_queries{1},skey{1},seed{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH,sid_queries,res,sess,part})
by auto
upto (coll_session_id(sid_queries,skey,seed)) with
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,LH,sid_queries,sess,part}).

checkproof.
claim C2 : 
AKE2.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE3.Main[coll_session_id(sid_queries,skey,seed)]
using Eq2.

claim sofar1 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE3.Main[coll_session_id(sid_queries,skey,seed)].
checkproof.

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
 var G : (session_id, session_key) map
 var tested_session : (session_id, session_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var keys_revealed : (part * message * part * message, bool) map
 var sid_queries : session_id list
 var sess : int
 var part : int

 fun KG() : public_key  = {
  var sk : secret_key = gen_secret_key();
  var pk : public_key = gen_public_key(sk);
  if (!in_dom(pk,skey) && part < qPart) 
  {
   corrupt[pk] = false;
   skey[pk] = sk;
   part = part + 1;
  }
  return pk;
 } 

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
  && sess < qSess) {
   complete_sessions[(B,proj(Y))] = (A, X, false);
   keys_revealed[(B,proj(Y),A,X)] = false;
   seed[(B,proj(Y))] = y;
   msg_seeds[(skey[B],y)] = msgs;
   sess=sess+1;
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
    keys_revealed[(A,X,B,Y)] = false;
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
     keys_revealed[(A,X,B,Y)] = true;
     ssskey = compute_key(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions[(B,Y)]);
     X' = session_msg(complete_sessions[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb ) 
     { (*  matches *)
      keys_revealed[(B,Y,A,X)] = true;
      keys_revealed[(A,X,B,Y)] = true;
      ssskey = compute_key(s);
     }
       else 
     {(*not match*)
      keys_revealed[(A,X,B,Y)] = true; 
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
  G = empty_map;
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


equiv Eq3iH : AKE3.iH ~ AKE4.iH :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3ck : AKE3.compute_key ~ AKE4.compute_key :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3iH2 : AKE3.iH ~ AKE4.iHT :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3ck2 : AKE3.compute_key ~ AKE4.compute_keyT :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3T : AKE3.Test ~ AKE4.Test :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.


equiv Eq3 : AKE3.Main ~ AKE4.Main : true ==> 
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,res,sid_queries,sess,part}
by auto (={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))).

checkproof.
claim C3_1 : 
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] 
using Eq3.

claim C3_2 : 
AKE3.Main[coll_session_id(sid_queries,skey,seed)] =
AKE4.Main[coll_session_id(sid_queries,skey,seed)]
using Eq3.

claim sofar2 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE4.Main[coll_session_id(sid_queries,skey,seed)].

checkproof.

game AKE5 = 
AKE4
var argLH : session_string list
var argLHT : session_string list
where
H = {
 var sk : session_key;
 argLH = str::argLH;
 sk = iH(str);
 return sk;
 } and
iH = {
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
and 
iHT = {
 var h : session_key = gen_session_key();
 var sk : session_key;
 argLHT = lam::argLHT;
 if (!in_dom(lam, LH) && !in_dom(lam, LHT)) { LHT[lam] = h; sk = h;}
 else {
  if (in_dom(lam, LHT)) {
   sk = LHT[lam];
  } else {
   sk = LH[lam];
  }
  }
  return sk;
 } and
Main  = {
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
  argLH = [];
  argLHT = [];
  sid_queries = [];
  part = 0;
  sess = 0;
  G = empty_map;
  b = {0,1};
  b' = A();
  return (b = b');
 }.

equiv Eq4 : AKE4.Main ~ AKE5.Main : true ==> 
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT,
 sid_queries,res,part,sess} 
by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT,
 sid_queries,part,sess}).

checkproof.
claim C4_1 :
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq4.

claim C4_2 : 
AKE4.Main[coll_session_id(sid_queries,skey,seed)] =
AKE5.Main[coll_session_id(sid_queries,skey,seed)]
using Eq4.

claim sofar3 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE5.Main[coll_session_id(sid_queries,skey,seed)].
checkproof.


game AKE6 = 
AKE5
where
iH = {
 var h : session_key = gen_session_key();
 if (!in_dom(lam, LH)) { LH[lam] = h;}
 return LH[lam];
} and 
iHT = {
 var h : session_key = gen_session_key();
 argLHT = lam::argLHT;
 if (!in_dom(lam, LHT)) { LHT[lam] = h;}
 return LHT[lam];
}.

pred string_coll(m1, m2 : session_string list) = 
exists (x : session_string), mem(x,m1) && mem(x,m2).

op string_coll_op :  (session_string list, session_string list) -> bool.

axiom string_coll_op_def : forall (m1, m2 : session_string list), 
string_coll_op(m1,m2) <=> string_coll(m1,m2).

pred inv(LH : (session_string,session_key) map, LHT : (session_string,session_key) map, 
    argLH : session_string list, argLHT : session_string list, 
    skey : (part,secret_key) map,seed : ((part* message), eph_key) map,
    sid_queries : session_id list) =
 (forall (x : session_string), in_dom(x,LH) => mem(x,argLH))  &&
 (forall (x : session_string), in_dom(x,LHT) => (mem(x,argLHT) || 
   (exists (s : session_id), mem(s,sid_queries) &&
     gen_session_string_sid(s,skey,seed) = x))).

equiv Eq5iH : AKE5.iH ~ AKE6.iH :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={lam,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT, sid_queries,part,sess} && 
inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} && 
inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))) by auto.

equiv Eq5iHT : AKE5.iHT ~ AKE6.iHT :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={lam,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,res,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))) by auto.

equiv Eq5H : AKE5.H ~ AKE6.H :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={str,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))).
call using Eq5iH.
trivial.
save.

equiv Eq5ckT : AKE5.compute_keyT ~ AKE6.compute_keyT :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,res,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))).
call using Eq5iHT.
trivial.
save.

equiv Eq5ck : AKE5.compute_key ~ AKE6.compute_key :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,res,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))).
call using Eq5iH.
trivial.
save.

equiv Eq5KR : AKE5.KeyReveal ~ AKE6.KeyReveal :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} 
 && inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} 
 && inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))).
sp 13 13.
rnd>>.
if.
if.
sp 3 3.
if.
if.
call using Eq5ck;trivial.
trivial.
sp 4 4.
if.
call using Eq5ck;trivial.
call using Eq5ck;trivial.
trivial.
trivial.
trivial.
save.

equiv Eq5T : AKE5.Test ~ AKE6.Test :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} 
&& inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} && 
inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1}))).
sp.
rnd>>.
if.
if.
trivial.
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
wp.
call using Eq5ckT.
trivial.
if.
trivial.
wp.
call using Eq5ckT.
trivial.
if.
trivial.
wp.
call using Eq5ckT.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq5EKR : AKE5.EphKeyReveal ~ AKE6.EphKeyReveal :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5I : AKE5.Init ~ AKE6.Init :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5R : AKE5.Respond ~ AKE6.Respond :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5C : AKE5.Complete ~ AKE6.Complete :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5KG : AKE5.KG ~ AKE6.KG :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5Corr : AKE5.Corrupt ~ AKE6.Corrupt :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})) by auto. 

equiv Eq5 : AKE5.Main ~ AKE6.Main : true ==> 
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2}))
&& (!string_coll(argLH{2},argLHT{2}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, argLH,
 argLHT,res,sid_queries,part,sess}) by auto upto (string_coll(argLH,argLHT)) with
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, LHT, argLH, argLHT,
 sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1},sid_queries{1})).

checkproof.
claim C5_1 :
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[string_coll_op(argLH,argLHT)]
using Eq5.

claim C5_2 :
AKE5.Main[coll_session_id(sid_queries,skey,seed)] <=
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)]
using Eq5.

claim sofar4 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[string_coll_op(argLH,argLHT)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)].

checkproof.

game AKE7 =
AKE6 where
iHT = {
 var h : session_key = gen_session_key();
 argLHT = lam::argLHT;
 return h;
}.

lemma asd : forall 
(s : session_id, 
 sidl : session_id list,
 skey : (public_key, secret_key) map,
 seed : (part * message, eph_key) map),
!coll_session_id(s::sidl,skey,seed) =>
 (! coll_session_id(sidl,skey,seed) &&
 forall (s' : session_id), mem(s', sidl) => 
  (gen_session_string_sid(s', skey, seed) <>
  gen_session_string_sid(s, skey, seed)) || 
  matching_session_id (s,s')).


equiv Eq6Test : AKE6.Test ~ AKE7.Test : 
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,
 sess,part} &&
(forall (str : session_string), in_dom(str,LHT{1}) => 
 (exists (s : session_id), gen_session_string_sid(s,skey{1},seed{1}) = str &&
   in_dom(s,tested_session{1}))) &&
forall (sid : session_id), 
in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})).
sp.
rnd>>.
if.
if.
trivial. 
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
timeout 10.
condt{1}.
sp 3 2.
timeout 3.
trivial.
if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
timeout 10.
condt{1}.
timeout 3.
trivial.

if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
timeout 10.
condt{1}.
timeout 3.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq6 : AKE6.Main ~ AKE7.Main : true ==>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,sess,part,res} by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,G,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), in_dom(str,LHT{1}) => 
 (exists (s : session_id), gen_session_string_sid(s,skey{1},seed{1}) = str &&
   in_dom(s,tested_session{1}))) &&
forall (sid : session_id), 
in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})).
checkproof.
claim C6_1 :
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq6.

claim C6_2 :
AKE6.Main[coll_session_id(sid_queries,skey,seed)] =
AKE7.Main[coll_session_id(sid_queries,skey,seed)]
using Eq6.


claim C6_3 :
AKE6.Main[string_coll_op(argLH,argLHT)] =
AKE7.Main[string_coll_op(argLH,argLHT)]
using Eq6.
checkproof.

op guess_session_string : 
((session_id,session_key) map,
 session_string list,
 (part, secret_key) map,
 (part * message, eph_key) map) -> bool.

axiom guess_session_string_def :
forall(ts : (session_id,session_key) map,
       argLH : session_string list,
       skey : (part, secret_key) map,
       seed : (part * message, eph_key) map),
guess_session_string(ts,argLH,skey,seed) <=> 
exists (s : session_id), in_dom(s,ts) &&
 mem(gen_session_string_sid(s,skey,seed),argLH).

lemma coll_guess : 
forall(ts : (session_id,session_key) map,
       argLH : session_string list,
       argLHT : session_string list,
       skey : (part, secret_key) map,
       seed : (part * message, eph_key) map),
(forall (str : session_string), mem(str,argLHT) =>
 exists (s : session_id), in_dom(s,ts) && 
 gen_session_string_sid(s,skey,seed) = str) &&
 string_coll_op(argLH,argLHT) =>
 guess_session_string(ts,argLH,skey,seed).



equiv Eq6strcoll : AKE7.Main ~ AKE7.Main : 
true ==> string_coll_op(argLH,argLHT){1} => 
         guess_session_string(tested_session,argLH,skey,seed){2}
by auto 
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,G,msg_seeds,keys_revealed, LH, LHT, argLH, argLHT,sid_queries,part,sess} &&
(forall (str : session_string), mem(str,argLHT{1}) =>
 exists (s : session_id), in_dom(s,tested_session{1}) && 
 gen_session_string_sid(s,skey{1},seed{1}) = str)).

checkproof.
claim C6_4 :
AKE7.Main[string_coll_op(argLH,argLHT)] <=
AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq6strcoll.

claim sofar5 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)].
checkproof.

game AKE8 =
AKE7 where
compute_keyT = {
 var ssskey : session_key;
 ssskey = iHT(dummy_session_string);
 return ssskey;
} and   Test =
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
        ssskey = h;
        tested_session[s] = ssskey;
       }
      }
        else 
      {(*not match*)
       ssskey = h;
       tested_session[s] = ssskey;
      }
     }
       else
     {(*B,_,Y,_ not complete*)
      ssskey = h;
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
 }
  else
  {
   ssskey = dummy_session_key;
  }
 return ssskey;
 
}  and
Main  = {
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
  argLH = [];
  argLHT = [];
  sid_queries = [];
  G = empty_map;
  part = 0;
  sess = 0;
  b' = A();
  b = {0,1};
  return (b = b');
 }.

equiv Eq7T : AKE7.Test ~ AKE8.Test : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,G,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part}).
case: b. 
sp.
rnd>>.
inline;derandomize.
wp.
trivial.
sp.
rnd{1}>>.
if{1}.
if{1}.
if{1}.
rnd{2}>>.
!3 condt{2}.
trivial.

rnd{2}>>.
!2 condt{2};condf{2}.
trivial.
if{1}.
sp 2 0.
if{1}.
if{1}.
sp 4 0.
if{1}.
if{1}.
rnd{2}>>.
condt{2};!2 condf{2}.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq7 : AKE7.Main ~ AKE8.Main : true ==>
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,G,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,res}) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,G,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,tested_session}).

checkproof.
claim C7_1 :
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq7.

claim C7_2 :
AKE7.Main[coll_session_id(sid_queries,skey,seed)] =
AKE8.Main[coll_session_id(sid_queries,skey,seed)]
using Eq7.

claim C7_3 :
AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] =
AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq7.

claim C7_4 : 
AKE8.Main[res] = 1%r / 2%r compute.
checkproof.

lemma fresh_sid_lm1 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), incomplete_session) =>  
fresh_sid(sid,corrupt,complete_session,incomplete_session[(A,X) <- (B,flag)]).


lemma fresh_sid_lm2 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid1(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid1(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).
lemma fresh_sid_lm3 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid11(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid11(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm4 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid3(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid3(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm5 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_lm5 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh(ts,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh(ts,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).


lemma fresh_sid_lm8 : 
forall (s : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status, 
 A : part),
fresh_sid(s,corrupt,complete_session,incomplete_session) =>
fresh_sid(s,corrupt[A <- false],complete_session,incomplete_session).

lemma fresh_lm9 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part),
fresh(ts,corrupt,complete_session,incomplete_session) =>
fresh(ts,corrupt[A <- false],complete_session,incomplete_session).

equiv Eq7_fresh : AKE8.Main ~ AKE8.Main : true ==>
res{1} <=> (res{2} && fresh_op(tested_session,corrupt, 
 complete_sessions,incomplete_sessions){1}) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,G,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,tested_session} &&
fresh_op(tested_session,corrupt, 
 complete_sessions,incomplete_sessions){1}).

checkproof.
claim C7_5 : 
AKE8.Main[res] =
AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq7_fresh.

claim sofar6 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
1%r / 2%r +
AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE8.Main[coll_session_id(sid_queries,skey,seed)] +
AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)].
checkproof.

game AKE9 = 
AKE8 
where compute_key = {
  var ssskey : session_key;
  var sstr : session_string option;
  sstr = findelse_h_abs(LH,s,skey,seed);
  if (sstr <> None) {
   ssskey = LH[proj(sstr)];
  } else
  {
   if (in_dom(s,G)) {
     ssskey = G[s];
    } else {
     if (in_dom(get_matching_session(s),G)) {
      ssskey = G[get_matching_session(s)];
     } else {
      ssskey = gen_session_key();
      G[s] = ssskey;     
     }
    }
   } 
  return ssskey;
 } and 
 iH = {
  var sid : session_id option;
  var ssskey : session_key;
  if (in_dom(lam, LH)) { 
   ssskey = LH[lam];
  } else {
   sid = findelse_g_abs(G,lam,skey,seed);
   if (sid <> None) {
    ssskey = G[proj(sid)];
   } else {
    ssskey = gen_session_key();
   }
   LH[lam] = ssskey;
  }
 return ssskey;
}.

equiv Eq8ck : AKE8.compute_key ~ AKE9.compute_key : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s]))).
inline iH.
sp 0 1.
if{2}.
sp.
rnd{1}>>.
condf{1}.
trivial.
if{2}.
sp.
rnd{1}>>.
condf{1}.
trivial.
if{2}.
sp.
rnd{1}>>.
condf{1}.
trivial.
sp.
rnd>>.
trivial.
save.

equiv Eq8iH : AKE8.iH ~ AKE9.iH : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s]))).
if{2}.
rnd{1}>>.
condf{1}.
trivial.
sp 0 1.
if{2}.
rnd{1}>>.
condf{1}.
trivial.
rnd>>.
condt{1}.
trivial.
save.

equiv Eq8 : AKE8.Main ~ AKE9.Main : true ==>
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part}) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s]))).

checkproof.
claim C8_1 :
AKE8.Main[coll_session_id(sid_queries,skey,seed)] =
AKE9.Main[coll_session_id(sid_queries,skey,seed)]
using Eq8.

claim C8_2 :
AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] =
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq8.

claim sofar7 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
1%r / 2%r +
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE9.Main[coll_session_id(sid_queries,skey,seed)] +
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)].
checkproof.

game AKE10 =
AKE9
where
KeyReveal ={
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
     keys_revealed[(A,X,B,Y)] = true;
     ssskey = compute_key(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions[(B,Y)]);
     X' = session_msg(complete_sessions[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb ) 
     { (*  matches *)
      keys_revealed[(B,Y,A,X)] = true;
      keys_revealed[(A,X,B,Y)] = true;
      ssskey = compute_key(s);
     }
       else 
     {(*not match*)
      keys_revealed[(A,X,B,Y)] = true; 
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
 } and Test =
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
    fresh_sid_op(get_matching_session(s),corrupt,complete_sessions,incomplete_sessions)) 
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
        ssskey = h;
        tested_session[s] = ssskey;
       }
      }
        else 
      {(*not match*)
       ssskey = h;
       tested_session[s] = ssskey;
      }
     }
       else
     {(*B,_,Y,_ not complete*)
      ssskey = h;
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
}.


equiv Eq9 : AKE9.Main ~ AKE10.Main : true ==>
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part}) by auto upto
(coll_session_id(sid_queries,skey,seed)).

checkproof.

claim C9_1 :
AKE9.Main[coll_session_id(sid_queries,skey,seed)] <=
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)]
using Eq9.


claim C9_2 :
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)]
using Eq9.

claim sofar8 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
1%r / 2%r +
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)].


claim aux1 :
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] =
2%r * (AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)]).

claim aux2 :
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] +
AKE10.Main[coll_session_id(sid_queries,skey,seed)] =
4%r * (AKE10.Main[coll_session_id(sid_queries,skey,seed)]).

claim sofar9 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] -
1%r / 2%r <=
2%r * (AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)]) +
4%r * (AKE10.Main[coll_session_id(sid_queries,skey,seed)]).

