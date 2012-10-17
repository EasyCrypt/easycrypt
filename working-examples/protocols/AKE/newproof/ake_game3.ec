include "ake_game2.ec".

op coll_session_id : (session_id list,(part,secret_key) map,(part * message, eph_key) map) -> bool.
op matching_session_id (s1,s2: session_id) = s1=s2 || s1 = get_matching_session (s2).


axiom coll_session_id_def : forall (SIDL : session_id list,skey:(part,secret_key) map,seed:(part * message, eph_key) map), 
  (coll_session_id(SIDL,skey,seed) <=>
    (exists(x,x':session_id), mem(x,SIDL)
      && mem(x',SIDL)
      && gen_session_string_sid(x,skey,seed) = gen_session_string_sid(x',skey,seed) 
      && !matching_session_id(x,x'))).

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
