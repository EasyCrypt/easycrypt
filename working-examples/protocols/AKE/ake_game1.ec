include "basic_defs.ec".

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
  (part, message) -> eph_key option
}.

game AKE = {
 var b : bool
 var bad : bool
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

 fun KG() : public_key  = {
  var sk : secret_key = gen_secret_key(0);
  var pk : public_key = gen_public_key(sk);
  if (!in_dom(pk,skey)) 
  {
   corrupt[pk] = false;
   skey[pk] = sk;
  }
  return pk;
 } 


 fun H(lam:session_string) : session_key = {
  var h : session_key = gen_session_key(0);
  if (!in_dom(lam, LH)) { LH[lam] = h; }
  return LH[lam];
 }

 fun iHT(lam:session_string,h : session_key) : session_key = {
  var res : session_key;
  if (!in_dom(lam, LH))  {
   if (!in_dom(lam, LHT)) { LHT[lam] = h;res = h;}
  }
  else
  {
   res = LH[lam];
  }
  return res;
} 
 

 fun iH(lam:session_string,h : session_key) : session_key = {
   if (!in_dom(lam, LH)) { LH[lam] = h;}
  return LH[lam];
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
   x = seed[(X,A)];
   h = gen_session_key(0);
   if (in_dom((A,X), complete_sessions)) 
   { (* (A,_,X,_) is completed*)
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     sidA = mk_sid(A, B', X, Y');
     eph_flagA = session_eph_flag(complete_sessions[(A,X)]);
     if ( B = B' && Y = Y') 
     {(* B = B' /\ Y = Y'*)
     if (!in_dom((B,Y), complete_sessions)) 
      {(*B,_,Y,_ not complete*)
       if (! in_dom(sidA, tested_session))
       {(*Fresh*)
         complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true); 
         sstr = gen_session_string_sid(sidA,skey,seed);
	 (*sstr = gen_session_string(skey[A], x, B,Y);*)
     	 ssskey = iH(sstr, h);
       }
       else 
       { (*not fresh*)
         ssskey = dummy_session_key;
       }
     }
else
{ (* B,_,Y_ complete *)
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B, A', Y, X');
       matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
       if ( matchb ) 
       { (*  matches *)
	 eph_flagB = session_eph_flag(complete_sessions[(B,Y)]);
         if (! in_dom(sidA, tested_session) && !in_dom(sidB, tested_session) )
         {(* fresh *)
           complete_sessions[(B,Y)] = mk_session_descr(A,X,eph_flagB,true);
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
           sstr = gen_session_string_sid(sidA,skey,seed);
           (*sstr = gen_session_string(skey[A], x, B,Y);*)
   	   ssskey = iH(sstr, h);
         } 
	 else
	 {	(*not fresh*)
   	    ssskey = dummy_session_key;
	 }
       }
       else 
       {(*not match*)
         if (!in_dom(sidA, tested_session) )
         {(*fresh *)
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);    
	   sstr = gen_session_string_sid(sidA,skey,seed);
           (*sstr = gen_session_string(skey[A], x, B,Y);*)
	   ssskey = iH(sstr, h);
         }
	 else
	 {(*not fresh*)
	    ssskey = dummy_session_key;
	 }
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
   var x : eph_key = seed[(X,A)];
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
   if (in_dom(s, tested_session)) {
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
           sstr = gen_session_string_sid(s,skey,seed);
           (*sstr = gen_session_string(skey[A], x, B,Y);*)
   	   ssskey = iH(sstr, h);
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
	   sstr = gen_session_string_sid(s,skey,seed);
           (*sstr = gen_session_string(skey[A], x, B,Y);*)
	   ssskey = iH(sstr, h);
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
	   sstr = gen_session_string_sid(s,skey,seed);        
           (*sstr = gen_session_string(skey[A], x, B,Y);*)
           ssskey = iH(sstr, h);
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
  b = {0,1};
  b' = A();
  return (b = b');
 }
 



}.
