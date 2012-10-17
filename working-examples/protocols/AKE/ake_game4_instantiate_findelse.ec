include "ake_game4.ec".

game AKE3_instantiate_findelse = {
 var b : bool var bad : bool
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (session_string, session_key) map
 var LHT     : (session_string, session_key) map
 var seed     : (message * part, eph_key) map
 var G : (session_id, session_key) map
 var tested_session : (session_id, session_key) map
 
 fun KG() : public_key = {
  var sk : secret_key = gen_secret_key(0);
  var pk : public_key = gen_public_key(sk);
  var res : public_key option = None;
   if (!in_dom(pk,skey)) 
   {
    corrupt[pk] = false;
    skey[pk] = sk;
   }
  return pk;
 } 
 
 fun findelse_sid_impl (m : (session_id, session_key) map, sid : session_id) : session_id option = {
  var sid' : session_id;
  var t : bool = false;
  var lG : session_id list = dom(m);
  var res : session_id option = None;
  while (lG <> [] && res = None){
   sid' = hd(lG);
   lG = tl(lG);
   t = same_session_string_abs(sid,sid',skey,seed);
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }

 fun findelse_g_impl(m : (session_id, session_key) map, str : session_string) : session_id option =
 {
  var sid' : session_id;
  var lG : session_id list = dom(m);
  var res : session_id option  = None;
  var t : bool = false;
   while (lG <> [] && !t){
   sid' = hd(lG);
   lG = tl(lG);
   t = eqS_abs(str,sid',skey,seed);
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }

 fun findelse_h_impl(m : (session_string, session_key) map, sid : session_id) : session_string option =
 {
  var str : session_string;
  var listH : session_string list = dom(m);
  var res : session_string option  = None;
  var t : bool = false;
   while (listH <> [] && !t){
   str = hd(listH);
   listH = tl(listH);
   t = eqS_abs(str,sid,skey,seed);
   if (t) {
    res = Some(str);
   }
  }
  return res;
 }


 fun H(lam:session_string) : session_key = {
   var c : bool;
   var res : session_key;
   var findr : session_id option;
   var findr' : session_id option;
   var h : session_key = gen_session_key(0);
   findr = findelse_g_impl(G, lam);
   findr' = findelse_g_impl(tested_session, lam);
   if (in_dom(lam, LH) || in_dom(lam, LHT))
   {
     if (in_dom(lam, LH)) {
     (* // it is in the domain of LH *)
     res=LH[lam];
     }
     else{
      res=LHT[lam];
     }
   }
   else 
   {
     
     if (findr <> None || findr' <> None)
     {
           if (findr <> None)
     {
      res= G[proj(findr)];
     } else
     {
      res= tested_session[proj(findr')];
     }
       (* //LH[lam] = res; *)
     }
     else 
     {
       LH[lam] = h;
       res = h;
     }
   }
   return res;
}

 fun iHT(lam:session_string,h : session_key) : session_key = {
    var c : bool;
    var res : session_key;
    var findr : session_id option;
    findr = findelse_g_impl(G, lam);
    if (in_dom(lam, LHT))
   {
     (* // it is in the domain of LHKR *)
    res=LHT[lam];
   }
     else 
   {
    if (in_dom(lam, LH))
    {
     (* // it is in the domain of LH *)
     res=LH[lam];
    }
      else 
    {
     
     if (findr <> None)
     {
      res= G[proj(findr)];
      (* //LH[lam] = res; *)
     }
       else 
     {(* //not in LH, not in LHKR *)
      LHT[lam] = h;
      res = h;
     }
    }
   }
  return res;
 } 
 

 fun iH(lam:session_string,h : session_key) : session_key = {
   var c : bool;
   var res : session_key;
   var findr : session_id option;
   findr = findelse_g_impl(G, lam);
   if (in_dom(lam, LH) || in_dom(lam,LHT))
   {
    if (in_dom(lam, LH)){
     (* // it is in the domain of LH *)
     res=LH[lam];
   }
   else {
    res=LHT[lam];
   }
  }
   else 
  {
   
   if (findr <> None)
   {
    res= G[proj(findr)];
      (* //LH[lam] = res; *)
   }
     else 
     {
      LH[lam] = h;
      res = h;
     }
    }
    return res;
   }

 fun Init(A:part, B:part) : message option = {
  var x : eph_key = gen_eph_key(0);
  var a : secret_key;
  var X : message option = None;
  if (in_dom(A, skey) && in_dom(B, skey)){
   a = skey[A];
   X = Some(out_noclash(a, x));
   if (!in_dom((proj(X),A), seed)) {
    incomplete_sessions[(A,proj(X))] = (B,false);
    seed[(proj(X),A)] = x;
   }   
   else 
   { 
    X = None;
   }
  }
  return X;
 }
 
 fun Respond(B:part, A:part, X: message) : message option = {
  var y : eph_key = gen_eph_key(0);  
  var Y : message option = Some(inp(skey[B], y));
  if (!in_dom((proj(Y),B), seed) && in_dom(A, skey) && in_dom(B, skey)) {
   complete_sessions[(B,proj(Y))] = mk_session_descr(A, X, false, false);
   seed[(proj(Y), B)] = y;
  }
  else {Y = None;}
  return Y;
 }
 
 fun Complete(A:part, B:part, X:message, Y:message) : unit = {
  var x : eph_key = seed[(X,A)];
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
 
 fun Corrupt(A : part) : secret_key option = {
   var a : secret_key option = None;
   if (in_dom(A,skey))
   {
     corrupt[A] = true;
     a = Some(skey[A]);
   }
   return a;
 }

 fun KeyReveal(s : session_id) : session_key = { 
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
            fer = findelse_sid_impl(G,sidA);
            fer' = findelse_sid_impl(tested_session,sidA);
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
              ofeh = findelse_h_impl(LH,sidA);
              ofeh' = findelse_h_impl(LHT,sidA);
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
           fer = findelse_sid_impl(G,sidA);
           fer' = findelse_sid_impl(tested_session,sidA);
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
             ofeh = findelse_h_impl(LH,sidA);
             ofeh' = findelse_h_impl(LHT,sidA);
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
         fer = findelse_sid_impl(G,sidA);
         fer' = findelse_sid_impl(tested_session,sidA);
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
           ofeh = findelse_h_impl(LH,sidA);
           ofeh' = findelse_h_impl(LHT,sidA);
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
}     


 fun Test(s : session_id) : session_key =
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
   
}

fun EphKeyReveal(A : part, X : message) : eph_key option = { 
   var kr_flagA : bool = false;
   var corr_flagA : bool = false;
   var test_flagA : bool = false;
   var B : part;
   var Y : message;
   var s : session_id;
   var ekey : eph_key option = None;
   corr_flagA = corrupt[A];
   if (!corr_flagA) (* not corrupted*)
   {
    if (in_dom((A,X), complete_sessions)) {
     kr_flagA = session_key_reveal_flag(complete_sessions[(A,X)]);
     B = session_part(complete_sessions[(A,X)]);
     Y = session_msg(complete_sessions[(A,X)]);
     s = mk_sid(A,B,X,Y);
      complete_sessions[(A,X)] = mk_session_descr(B,Y,true,kr_flagA);
      ekey = Some (seed[(X,A)]);
    }
    else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions)) {
     B = fst(incomplete_sessions[(A,X)]);
     incomplete_sessions[(A,X)] = (B, true);
     ekey = Some (seed[(X,A)]);     
    }
   }
  }
   return ekey;  
}




 abs A = A { KG, Init, Respond, Complete, Corrupt, KeyReveal, H, Test, EphKeyReveal }
 
 fun Main () : bool = {
  var b' : bool;
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
  b = {0,1};
  b' = A();
  return (b = b');
 }
}.
(*
claim inst_claim : AKE3_instantiate_findelse.Main[bad_op] = AKE3.Main[bad_op]  
by instantiate.
*)