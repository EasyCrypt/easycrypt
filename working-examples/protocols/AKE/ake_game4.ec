include "ake_game3.ec".

game AKE3 = AKE2 where
   KeyReveal = { 
   var A:part = fstpart(s);
   var B:part = sndpart(s);
   var X:message = fstmsg(s);
   var Y:message = sndmsg(s);
   var x : eph_key = seed[(X,A)];
   var B' : part = dummy_part;
   var Y' : message = dummy_msg;
   var test_flagA : bool = false;
   var test_flagB : bool = false;
   var eph_flagA : bool = false;
   var eph_flagB : bool = false;
   var A' : part = dummy_part;
   var X' : message = dummy_msg;
   var sstr : session_string = dummy_string;
   var ssskey : session_key = dummy_session_key;
   var matchb : bool = false;
   var fer : session_id option = None;
   var fer' : session_id option = None;
   var ofeh : session_string option = None;
   var ofeh' : session_string option = None;
   var sid : session_id = dummy_sid; 
   var sidA : session_id = dummy_sid;
   var sidB : session_id = dummy_sid;
   var sestr : session_string = dummy_string;
   var res : session_key;
   var h : session_key = dummy_session_key;
   h = gen_session_key(0);
   if (! in_dom((A,X), complete_sessions)) 
   {(*/session is not complete, cannot key reveal*)
     res = dummy_session_key;
   }
   else
   { (*/ session complete*)
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     sidA = mk_sid(A, B', X, Y');
     eph_flagA = session_eph_flag(complete_sessions[(A,X)]); 
     test_flagA = in_dom(s,tested_session);
     if (B = B' && Y = Y') 
     { (*/ session exists B = B ' && Y = Y'*)
       if (! in_dom((B,Y), complete_sessions)) 
       {(* / there is no completed matching session*)
          if (test_flagA)
          {(*non-fresh session*)
            res = dummy_session_key;
          }
          else
          {(*fresh session*)
            fer = findelse_sid_abs(G,sidA, skey, seed);
            fer' = findelse_sid_abs(tested_session,sidA, skey, seed);
            if (fer <> None || fer' <> None)
            { (* session with the same session string is in G *)
             if (fer <> None) {
              sid = proj(fer);
	      complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
 	      res = G[sid];
             }
             else {
              sid = proj(fer');
	      complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
 	      res = tested_session[sid];
             }
(*    	      G[sidA] = res;*)
(*really necesary? findelse_sid ensures that th*)
            }
                else
            { (* session with the same session string is not in G *)
              ofeh = findelse_h_abs(LH,sidA, skey, seed);
              ofeh' = findelse_h_abs(LHT,sidA, skey, seed);
              if (ofeh <> None ||ofeh' <> None )
              {
                (* session string has been queried to hash*)
               if (ofeh <> None) {
                sestr = proj(ofeh);
		complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
		res = LH[sestr]; (* LH[sestr]*)
               }
                 else
               {
                sestr = proj(ofeh');
		complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
		res = LHT[sestr];
               }
              }
                  else
              {
               (* session string has not been queried to hash*)
                (* use a randomly generated value*)
                G[sidA] = h;
		complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
		res = h;
              }
            }
          } (*fresh session*)
        } (* there is no completed matching session*)
     else
     { (*there is a completed session of the form (B,_,Y,_)*)
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B,A',Y,X');
       test_flagB = in_dom(sidB,tested_session);
       eph_flagB = session_eph_flag(complete_sessions[(B,Y)]); 
       matchb = session_match(sidA,sidB);
       if (!matchb) 
       {(* (B,_,Y,_) is not a matching session*)
         if (test_flagA)
         {(*non-fresh session*)
           res = dummy_session_key;
         }
             else
         {(*fresh session*)
           fer = findelse_sid_abs(G,sidA, skey, seed);
           fer' = findelse_sid_abs(tested_session,sidA, skey, seed);
           if (fer <> None || fer' <> None)
           { (* session with the same session string is in G *)
            if (fer <> None) {
             sid = proj(fer);
             complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	     res = G[sid];
	     G[sidA] = res;
            } else
            {
             sid = proj(fer');
             complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	     res = tested_session[sid];
            }
           }
               else
           { (* session with the same session string is not in G *)
             ofeh = findelse_h_abs(LH,sidA, skey, seed);
             ofeh' = findelse_h_abs(LHT,sidA, skey, seed);
             if (ofeh <> None || ofeh' <> None)
             {
               (* session string has been queried to hash*)
              if  (ofeh <> None) {
               sestr = proj(ofeh);
               complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
               res = LH[sestr];
              } else
              {
               sestr = proj(ofeh');
               complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
               res = LHT[sestr];
              }
             }
                 else
             {(* session string has not been queried to hash*)
               (* use a randomly generated value*)
               G[sidA] = h;
	       complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	       res = h;
             }
           }
         } (*fresh session*)
       } (* (B,_Y,_) is not a matching session*)
         else 
       {(* (B,_Y,_) is a matching session*)
         if (test_flagA || test_flagB ) 
       { (* at least one of the sessions is not fresh*)
         res = dummy_session_key;
       }
       else
       {(* both sessions are fresh*)
         complete_sessions[(B,Y)] = mk_session_descr(A,X,eph_flagB,true);
         complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
         fer = findelse_sid_abs(G,sidA, skey, seed);
         fer' = findelse_sid_abs(tested_session,sidA, skey, seed);
         if (fer <> None || fer' <> None) 
         { (* session with same session string in G*)
          if (fer <> None ) {
          sid = proj(fer);
	  res = G[sid];
          } else
          {
           sid = proj(fer');
	   res = tested_session[sid];
          }

          }
(*	   G[sidA] = res; YL 1/1/2012*)
(*	   G[sidB] = res; YL 1/1/2012*)

         
             else
         { (* session string in H?*)
           ofeh = findelse_h_abs(LH,sidA, skey, seed);
           ofeh' = findelse_h_abs(LHT,sidA, skey, seed);
           if (ofeh <> None || ofeh' <> None)
             { (* session string has been queried to hash*)
              if(ofeh <> None) {
              sestr = proj(ofeh);
               res = LH[sestr];
              }
              else{
               sestr = proj(ofeh');
               res = LHT[sestr];
              }
             }
                 else
             {(* session string has not been queried to hash*)
              G[sidA] = h; 
              G[sidB] = h; 
              res = h;
             } 
           }
         }(* both sessions are fresh*)
       }(* B,Y is a matching session*)
     }(* B,Y exists in completed*)
   } (*session (X, A) is completed*)
   else 
   { (* session does not exist*)
       res = dummy_session_key;
   }
     
 }
 return res;
} and Test =
 {
   var A:part = fstpart(s);
   var B:part = sndpart(s);
   var X:message = fstmsg(s);
   var Y:message = sndmsg(s);
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
   h = gen_session_key(0);
   ssskey = h;
   if (in_dom(s, tested_session)) {
    ssskey = tested_session[s];
    bad = true;
   }
   else{(*not a tested session*)
   if (in_dom((A,X), complete_sessions)) 
   { (* (A,_,X,_) is completed*)
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     kr_flagA = session_key_reveal_flag(complete_sessions[(A,X)]);
     corr_flagA = corrupt[A];    
     eph_flagA = session_eph_flag(complete_sessions[(A,X)]);
     if ( B = B' && Y = Y') 
     {(* B = B' /\ Y = Y'*)
     if (in_dom((B,Y), complete_sessions)) 
      { (*B,_,Y_ complete *)
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B,A,Y,X);
       eph_flagB = session_eph_flag(complete_sessions[(B,Y)]);
       matchb = session_match(s, sidB);
       if ( matchb ) 
       { (* matches*)
         if (in_dom(sidB, tested_session)) {
          ssskey = tested_session[sidB];
          bad = true;
          tested_session[s] = ssskey;
         }
         else {(* matching session not tested*)
          kr_flagB = session_key_reveal_flag(complete_sessions[(B,Y)]);
	  corr_flagB = corrupt[B];
           (* ask yassine how to model freshness, i.e. the message was not produced by the adv..*)
          if (! kr_flagA && !kr_flagB && (!(corr_flagA && eph_flagA) )
           && (!(corr_flagB && eph_flagB) )) 
         {(* fresh*)
   	   ssskey = h;
           tested_session[s] = ssskey;
         } 
	   else
	 {	(*not fresh*)
   	    ssskey = h;
	 }
       }
      }
       else 
       {(*not match*)
         if (! kr_flagA && (!(corr_flagA && eph_flagA)) && (!(corrupt[B'] &&  eph_flagB)))
         {(*fresh*)
	   ssskey = h;
           tested_session[s] = ssskey;
         }
	 else
	 {(*not fresh*)
   	    ssskey = dummy_session_key;
	 }
       }
     }
         else
     {(*B,_,Y,_ not complete*)
      if (in_dom((B',Y),incomplete_sessions)) 
      {
        eph_flagB = snd(incomplete_sessions[(B',Y)]);
      }
      if (! kr_flagA && (!(corr_flagA && eph_flagA)) && (!(corr_flagB && eph_flagB)))
       {(*Fresh*)
           ssskey = h;
           tested_session[s] = ssskey;
       }
       else 
       { (*not fresh*)
   	    ssskey = dummy_session_key;
       }
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
if (b) {
 ssskey= h;
}
return ssskey;
   
}.

pred link_tested_G_LHT 
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
forall (s : session_id),
in_dom(s,tested_session)
 =>
((in_dom(gen_session_string_sid(s,skey,seed), LHT)  && 
 LHT[gen_session_string_sid(s,skey,seed)] = tested_session[s])
 || (let sid' = findelse_sid_abs(G, s, skey, seed) in
         sid' <> None && G[proj(sid')] = tested_session[s])).

pred guess_session_string
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
exists (s : session_id), (in_dom(s,tested_session) &&
in_dom(gen_session_string_sid(s,skey,seed),LH)).

pred test_key_reveal_collision 
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
exists (s : session_id), (in_dom(s,tested_session) && 
 findelse_sid_abs(G,s, skey,seed) <> None). 
 
pred bad (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
guess_session_string(tested_session, skey,seed,LH, G) ||
test_key_reveal_collision(tested_session, skey,seed,LH, G).


op guess_session_string_op : 
  ((session_id, session_key) map, 
  (part, secret_key) map,
  (message * part, eph_key) map,
  (session_string, session_key) map,
  (session_id, session_key) map) ->
  bool.

axiom guess_session_string_op_def : 
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), guess_session_string(tested_session,skey,seed,LH, G) <=> guess_session_string_op(tested_session,skey,seed,LH, G).

op test_key_reveal_collision_op :
          ((session_id, session_key) map,
           (part, secret_key) map,
           ((message*part),eph_key) map,
           (session_string, session_key) map,
           (session_id, session_key) map) -> bool.


axiom test_key_reveal_collision_op_def :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), test_key_reveal_collision(tested_session,skey,seed,LH, G) <=> test_key_reveal_collision_op(tested_session,skey,seed,LH, G).

op bad_op (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) =   test_key_reveal_collision_op(tested_session,skey,seed,LH, G) || guess_session_string_op(tested_session,skey,seed,LH, G).