include "ake_game4.ec".

game AKE3' = AKE3 where
Main  = {
 var b' : bool;
 var tt : unit;
 bad = false;
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
 b' = A();
 b = {0,1};
 return (b = b');
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
    bad = true;
    ssskey = tested_session[s];
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
          bad = true;
          ssskey = tested_session[sidB];
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
   	    ssskey = h;
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
   	    ssskey = h;
       }
     }
   }(* B = B' /\ Y = Y'	*)
     else
     {  (*   B <> B' \/ Y <> Y'*)
      ssskey = h;
     } 
      

 }(* (A,_,X,_) is completed*)
 else
 {
  ssskey = h;
 }
}
return h;
}.

 

equiv FactIndependence : AKE3.Main ~ AKE3'.Main :
true ==> bad{1} = bad{2} && (!bad{1} => ={res}) by auto upto (bad) with 
(={bad} && (!bad{1} => ={complete_sessions, incomplete_sessions, corrupt, pkey, skey,seed, tested_session, G, LH, LHT })).


claim Pr33' : | AKE3.Main[res] - AKE3'.Main[res] | <= AKE3.Main[bad] using FactIndependence. 

claim PR_Hyp : AKE3.Main[bad] = 0%r
admit.

claim Pr1 : AKE3'.Main[res]  = 1%r / 2 %r
compute.

claim PrAKE3 : AKE3.Main[res]  = 1%r / 2 %r.
