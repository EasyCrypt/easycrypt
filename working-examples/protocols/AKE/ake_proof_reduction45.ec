include "ake_game4_instantiate_findelse.ec".

op eqS_oracle : 
(session_string,  session_id) -> bool.

axiom eqS_abs_oracle :
 forall 
( str : session_string,  
 sid : session_id, 
 skey : (part, secret_key) map, 
 seed : (message* part, eph_key) map), 
eqS_abs(str,sid,skey,seed) = eqS_oracle(str,sid).

op same_session_string_oracle : 
(session_id , session_id)  -> bool.

axiom same_session_string_abs_oracle :
 forall (sid : session_id, 
 sid' : session_id, 
 skey : (part, secret_key) map, 
 seed : (message * part, eph_key) map),
same_session_string_abs(sid,sid',skey,seed) = 
 same_session_string_oracle(sid,sid').

axiom same_session_string_sym :
 forall (sid : session_id, 
 sid' : session_id),
same_session_string_oracle(sid,sid') = same_session_string_oracle(sid',sid).


 (*op findelse_sid_oracle : ((session_id, session_key) map,  session_id) -> 
 session_id option.

 axiom findelse_sid_oracle_abs :
 forall (m' :  (session_id, session_key) map,
 s' : session_id,
 skey' : (part, secret_key) map,
 seed' : (message * part, eph_key) map),
 findelse_sid_oracle(m',s') = findelse_sid_abs(m',s',skey',seed').

 op findelse_g_oracle : ((session_id, session_key) map ,  session_string) -> 
 session_id option.

 axiom findelse_g_abs_oracle :
 forall (m' :  (session_id, session_key) map,
 str : session_string,
 skey' : (part, secret_key) map,
 seed' : (message * part, eph_key) map),
 findelse_g_abs(m',str,skey',seed') = findelse_g_oracle(m',str).

 op findelse_h_oracle : ((session_string, session_key) map ,  session_id) -> session_string option.


 axiom findelse_h_abs_oracle :
 forall (m' :  (session_string, session_key) map,
 sid : session_id,
 skey' : (part, secret_key) map,
 seed' : (message * part, eph_key) map),
 findelse_h_abs(m',sid,skey',seed') = findelse_h_oracle(m',sid).
 *)

adversary B () : session_id * session_string  
{
 () -> public_key; (*KG*)
 (part, part) -> message; (* Init *)
 (part, part, message) -> message; (* Respond *)
 (part, part, message, message) -> unit; (* Complete *)
  part -> secret_key; (*Corrupt*)
 (part, message) -> eph_key; (*EphKeyReveal*)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

op wingame5
(sid : session_id,
 str : session_string,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status) =
eqS_oracle(str,sid) && 
(fresh_sid1_op(sid,corrupt,complete_session,incomplete_session) ||
 fresh_sid11_op(sid,corrupt,complete_session,incomplete_session) ||
 fresh_sid2_op(sid,corrupt) ||
 fresh_sid3_op(sid,corrupt,complete_session,incomplete_session)
).

game AKE5_red = {
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var seed     : (message * part, eph_key) map
  (*we construct implementations of all the oracles in game4 in terms of
  the previous oracles and some auxiliary state; and we construct an
  adversary B against game5 in terms of an adversary A of game 4 *)
 
  (* auxiliary local state: conceptually part of adversary B's state *)
 var complete_sessions_B : complete_session_with_status
 var incomplete_sessions_B : incomplete_session_with_status
 var corrupt_B  : (part, bool) map
 var pkey_B     : (part, public_key) map
 var tested_session_B : (session_id, session_key) map
 var G_B : (session_id, session_key) map
 var LH_B : (session_string, session_key) map
 var LHT_B : (session_string, session_key) map
 var bad : bool
 var b : bool

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
 
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 

 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
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
  else {
   Y = None;
  }
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
    ekey = Some(seed[(X,A)]);
   }
     else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions)) {
     B = fst(incomplete_sessions[(A,X)]);
     incomplete_sessions[(A,X)] = (B, true);
     ekey = Some(seed[(X,A)]);     
    }
   }
  }
  return ekey;  
 }
 
   (* abs A' = A' { KG, Init, Respond, Complete, Corrupt, EphKeyReveal, eqS, same_session_string } *)

 fun Skip(m : (session_id,session_key) map, sid : session_id ) : 
 (session_id,session_key) map * session_id  = 
 {
  return (m, sid);
 }


   (* First, we define removed oracles in game5, this is KeyReveal, Test
   and H in terms of oracles in game5. This is not quite clear in this
   case: the new oracles in game5, eqS, and same_session_string are used
   indirectly, through calls to findelse_sid_oracle, etc. *)

 fun findelse_sid_oracle (m : (session_id, session_key) map, sid : session_id) : session_id option = {
  var sid' : session_id;
  var t : bool = false;
  var lG : session_id list = dom(m);
  var res : session_id option = None;
  while (lG <> [] && res = None){
   sid' = hd(lG);
   lG = tl(lG);
   t = same_session_string(sid,sid');
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }

 fun findelse_g_oracle(m : (session_id, session_key) map, str : session_string) : session_id option =
 {
  var sid' : session_id;
  var lG : session_id list = dom(m);
  var res : session_id option  = None;
  var t : bool = false;
   while (lG <> [] && !t){
   sid' = hd(lG);
   lG = tl(lG);
   t = eqS(str,sid');
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }

 fun findelse_h_oracle(m : (session_string, session_key) map, sid : session_id) : session_string option =
 {
  var str : session_string;
  var listH : session_string list = dom(m);
  var res : session_string option  = None;
  var t : bool = false;
   while (listH <> [] && !t){
   str = hd(listH);
   listH = tl(listH);
   t = eqS(str,sid);
   if (t) {
    res = Some(str);
   }
  }
  return res;
 }

 (* Adversary implementations *)
 fun KeyReveal_B(s : session_id) : session_key = { 
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
  if (! in_dom((A,X), complete_sessions_B)) 
  {(*/session is not complete, cannot key reveal*)
   res = dummy_session_key;
  }
    else
  { (*/ session complete*)
   B' = session_part(complete_sessions_B[(A,X)]);
   Y' = session_msg(complete_sessions_B[(A,X)]);
   sidA = mk_sid(A, B', X, Y');
   eph_flagA = session_eph_flag(complete_sessions_B[(A,X)]); 
   test_flagA = in_dom(sidA,tested_session_B);
   if (B = B' && Y = Y') 
   { (*/ session exists B = B ' && Y = Y'*)
    if (! in_dom((B,Y), complete_sessions_B)) 
    {(* / there is no completed matching session*)
     if (in_dom(s,tested_session_B))
     {(*non-fresh session*)
      res = dummy_session_key;
     }
       else
     {(*fresh session*)
      fer = findelse_sid_oracle(G_B,sidA);
      fer' = findelse_sid_oracle(tested_session_B,sidA);
      if (fer <> None || fer' <> None)
      { (* session with the same session string is in G *)
       if (fer <> None) {
        sid = proj(fer);
	complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
 	res = G_B[sid];
       }
       else {
        sid = proj(fer');
	complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
 	res = tested_session_B[sid];
       }
         (*    	      G[sidA] = res;*)
         (*really necesary? findelse_sid ensures that th*)
      }
        else
      { (* session with the same session string is not in G *)
       ofeh = findelse_h_oracle(LH_B,sidA);
       ofeh' = findelse_h_oracle(LHT_B,sidA);
       if (ofeh <> None ||ofeh' <> None )
       {
        (* session string has been queried to hash*)
        if (ofeh <> None) {
         sestr = proj(ofeh);
	 complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	 res = LH_B[sestr]; (* LH[sestr]*)
        }
        else
        {
         sestr = proj(ofeh');
	 complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	 res = LHT_B[sestr];
        }
       }
         else
       {
        (* session string has not been queried to hash*)
        (* use a randomly generated value*)
        G_B[sidA] = h;
	complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	res = h;
       }
      }
     } (*fresh session*)
    } (* there is no completed matching session*)
      else
    { (*there is a completed session of the form (B,_,Y,_)*)
     A' = session_part(complete_sessions_B[(B,Y)]);
     X' = session_msg(complete_sessions_B[(B,Y)]);
     sidB = mk_sid(B,A',Y,X');
     test_flagB = in_dom(sidB,tested_session_B);
     eph_flagB = session_eph_flag(complete_sessions_B[(B,Y)]); 
     matchb = session_match(sidA,sidB);
     if (!matchb) 
     {(* (B,_,Y,_) is not a matching session*)
      if (test_flagA)
      {(*non-fresh session*)
       res = dummy_session_key;
      }
        else
      {(*fresh session*)
       fer = findelse_sid_oracle(G_B,sidA);
       fer' = findelse_sid_oracle(tested_session_B,sidA);
       if (fer <> None || fer' <> None)
       { (* session with the same session string is in G *)
        if (fer <> None) {
         sid = proj(fer);
         complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	 res = G_B[sid];
	 G_B[sidA] = res;
        } else
        {
         sid = proj(fer');
         complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
	 res = tested_session_B[sid];
        }
       }
         else
       { (* session with the same session string is not in G *)
        ofeh = findelse_h_oracle(LH_B,sidA);
        ofeh' = findelse_h_oracle(LHT_B,sidA);
        if (ofeh <> None || ofeh' <> None)
        {
         (* session string has been queried to hash*)
         if  (ofeh <> None) {
          sestr = proj(ofeh);
          complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
          res = LH_B[sestr];
         } else
         {
          sestr = proj(ofeh');
          complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
          res = LHT_B[sestr];
         }
        }
          else
        {(* session string has not been queried to hash*)
         (* use a randomly generated value*)
         G_B[sidA] = h;
	 complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
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
       complete_sessions_B[(B,Y)] = mk_session_descr(A,X,eph_flagB,true);
       complete_sessions_B[(A,X)] = mk_session_descr(B',Y',eph_flagA,true);
       fer = findelse_sid_oracle(G_B,sidA);
       fer' = findelse_sid_oracle(tested_session_B,sidA);
       if (fer <> None || fer' <> None) 
       { (* session with same session string in G*)
        if (fer <> None ) {
         sid = proj(fer);
	 res = G_B[sid];
        } else
        {
         sid = proj(fer');
	 res = tested_session_B[sid];
        }

       }
         (*	   G[sidA] = res; YL 1/1/2012*)
         (*	   G[sidB] = res; YL 1/1/2012*)

       
         else
       { (* session string in H?*)
        ofeh = findelse_h_oracle(LH_B,sidA);
        ofeh' = findelse_h_oracle(LHT_B,sidA);
        if (ofeh <> None || ofeh' <> None)
        { (* session string has been queried to hash*)
         if(ofeh <> None) {
          sestr = proj(ofeh);
          res = LH_B[sestr];
         }
         else{
          sestr = proj(ofeh');
          res = LHT_B[sestr];
         }
        }
          else
        {(* session string has not been queried to hash*)
         G_B[sidA] = h; 
         G_B[sidB] = h; 
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

 fun Test_B (s : session_id ): session_key =
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
   if (in_dom(s, tested_session_B)) {
    ssskey = tested_session_B[s];
    bad = true;
   }
   else{(*not a tested session*)
   if (in_dom((A,X), complete_sessions_B)) 
   { (* (A,_,X,_) is completed*)
     B' = session_part(complete_sessions_B[(A,X)]);
     Y' = session_msg(complete_sessions_B[(A,X)]);
     kr_flagA = session_key_reveal_flag(complete_sessions_B[(A,X)]);
     corr_flagA = corrupt_B[A];    
     eph_flagA = session_eph_flag(complete_sessions_B[(A,X)]);
     if ( B = B' && Y = Y') 
     {(* B = B' /\ Y = Y'*)
     if (in_dom((B,Y), complete_sessions_B)) 
      { (*B,_,Y_ complete *)
       A' = session_part(complete_sessions_B[(B,Y)]);
       X' = session_msg(complete_sessions_B[(B,Y)]);
       sidB = mk_sid(B,A,Y,X);
       eph_flagB = session_eph_flag(complete_sessions_B[(B,Y)]);
       matchb = session_match(s, sidB);
       if ( matchb ) 
       { (* matches*)
         if (in_dom(sidB, tested_session_B)) {
          ssskey = tested_session_B[sidB];
          bad = true;
          tested_session_B[s] = ssskey;
         }
         else {(* matching session not tested*)
          kr_flagB = session_key_reveal_flag(complete_sessions_B[(B,Y)]);
	  corr_flagB = corrupt_B[B];
           (* ask yassine how to model freshness, i.e. the message was not produced by the adv..*)
          if (! kr_flagA && !kr_flagB && (!(corr_flagA && eph_flagA) )
           && (!(corr_flagB && eph_flagB) )) 
         {(* fresh*)
   	   ssskey = h;
           tested_session_B[s] = ssskey;
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
           tested_session_B[s] = ssskey;
         }
	 else
	 {(*not fresh*)
   	    ssskey = dummy_session_key;
	 }
       }
     }
         else
     {(*B,_,Y,_ not complete*)
      if (in_dom((B',Y),incomplete_sessions_B)) 
      {
        eph_flagB = snd(incomplete_sessions_B[(B',Y)]);
      }
      if (! kr_flagA && (!(corr_flagA && eph_flagA)) && (!(corr_flagB && eph_flagB)))
       {(*Fresh*)
           ssskey = h;
           tested_session_B[s] = ssskey;
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


 fun H_B(lam : session_string) : session_key = {
  var c : bool;
  var res : session_key;
  var findr : session_id option;
  var findr' : session_id option;
  var h : session_key = gen_session_key(0);
  findr = findelse_g_oracle(G_B, lam);
  findr' = findelse_g_oracle(tested_session_B, lam);
  if (in_dom(lam, LH_B) || in_dom(lam, LHT_B))
  {
   if (in_dom(lam, LH_B)) {
    (* // it is in the domain of LH *)
    res=LH_B[lam];
   }
   else{
    res=LHT_B[lam];
   }
  }
  else 
  {
   if (findr <> None || findr' <> None)
   {
    if (findr <> None)
    {
     res = G_B[proj(findr)];
    } else
    {
     res = tested_session_B[proj(findr')];
    }     (* //LH[lam] = res; *)
   }
   else 
   {
    LH_B[lam] = h;
    res = h;
   }
  }
  return res;
 }
 fun KG_B() : public_key  = {
  var pk : public_key;
  pk = KG();
  if (!in_dom(pk, corrupt_B)) {
   corrupt_B[pk] = false;
  }
  return pk;
 }


 fun Init_B (A:part, B:part) : message option = {
  var X : message option;
  X = Init(A,B);
  if (X <> None) {
   incomplete_sessions_B[(A,proj(X))] = (B,false);
  }
  return X;
 }

 fun Respond_B (B:part, A:part, X: message) : message option = {
  var Y : message option;
  Y = Respond(B,A,X);
  if (Y <> None){
   complete_sessions_B[(B,proj(Y))] = mk_session_descr(A, X, false, false);
  }
  return Y;
 }

 fun Complete_B(A:part, B:part, X:message, Y:message) : unit = {
  var B' : part;
  var eph_flag : bool;
  if (in_dom((A,X), incomplete_sessions_B)) {
   B' = fst(incomplete_sessions[(A,X)]);
   eph_flag = snd(incomplete_sessions_B[(A,X)]);
   if (B' = B && !in_dom((A,X), complete_sessions_B)) {
    complete_sessions_B[(A,X)] = mk_session_descr(B,Y,eph_flag,false);
    Complete(A,B,X,Y);
    (*get rid of the session in incomplete*)
   }
  }
 }

 fun Corrupt_B(A : part) : secret_key option = {
  var sk : secret_key option;
  sk = Corrupt(A);
  if (sk <> None) {
   corrupt_B[A] = true;
  }
  return sk;
 }

 fun EphKeyReveal_B(A : part, X : message) : eph_key option = { 
  var ekey : eph_key option;
  var B : part; 
  var Y : message;
  var kr_flagA : bool;
  ekey = EphKeyReveal(A,X);
  if (ekey <> None) {
   if (in_dom((A,X), complete_sessions_B)) {
    B = session_part(complete_sessions_B[(A,X)]);
    Y = session_msg(complete_sessions_B[(A,X)]);
    kr_flagA = session_key_reveal_flag(complete_sessions_B[(A,X)]);
    complete_sessions_B[(A,X)] = mk_session_descr(B,Y,true,kr_flagA);
   } else
   {
    if (in_dom((A,X), incomplete_sessions_B)) {
     B = fst(incomplete_sessions_B[(A,X)]);
     incomplete_sessions_B[(A,X)] = (B, true);
    }
   }
  }

  return ekey;
 }

 abs A = A { KG_B, Init_B, Respond_B, Complete_B, Corrupt_B, KeyReveal_B, H_B, Test_B, EphKeyReveal_B }

fun B () :  session_id * session_string = {
 (* convert test_key_reveal_collision event of game 4 into wining
 event of this game *)
 var b' : bool;
 var dTS : session_id list;
 var s : session_id;
 var found : session_string option ;
 var res : session_id * session_string = (dummy_session_id, dummy_session_string);
 (* run adversary against game 4*)
 (*initialize maps *)
 b = {0,1};
 complete_sessions_B = empty_map;
 incomplete_sessions_B = empty_map;
 pkey_B = empty_map;
 corrupt_B = empty_map;
 tested_session_B = empty_map;
 G_B = empty_map;
 LH_B = empty_map;
 LHT_B = empty_map;
 bad = false;
 b' = A();
 dTS = dom(tested_session_B);
 found = None;
 (* go through tested_session_B and try to find a sid whose session
 string matches the corresponding session string of a sid contained in
 G (which was key revealed) *)
 while (dTS <> [] && found = None){
  s = hd(dTS);
  dTS = tl(dTS);
  found = findelse_h_oracle(LH_B, s);
 }
 if (found <> None) {
  res = (s, proj(found)); 
 }
 return res;
}

 fun Main () : session_id * session_string = {
  var sidss : session_id * session_string;
  var test11 : bool = false;
  var test12 : bool = false;
  var test2 : bool = false;
  var test3 : bool = false;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corrupt = empty_map;
  pkey = empty_map;
  skey = empty_map;
  seed  = empty_map;
  sidss = B();
  return (sidss);
 }
}.

