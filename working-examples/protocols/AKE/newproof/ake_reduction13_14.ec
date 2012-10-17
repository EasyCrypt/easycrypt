include "ake_game14.ec".

game AKE13_14_ctxt = {
 (* variables of AKE13 *)
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var seed     : (part * message, eph_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var sess : int
 var part : int
 (* context variables *)
 (* We use "_C" to denote that a variable belongs to the context:
    all state variables ocurring in adversary implementations
    should either be local, parameters or state variables with
    "_C"
  *)

 var keys_revealed_C : (session_id, bool) map
 var sid_queries_C : session_id list
 var argLHT_C : session_string list
 var argLH_C : session_string list
 var G_C : (session_id,session_key) map
 var LH_C : (session_string, session_key) map
 var LHT_C : (session_string, session_key) map
 var b_c : bool
 var tested_session_C : (session_id, session_key) map
 var complete_sessions_C : complete_session_with_status
 var incomplete_sessions_C : incomplete_session_with_status
 var corrupt_C  : (part, bool) map 

 (*AKE14 implementations *)
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

 fun MsgSeedReveal (sk : secret_key, ek : eph_key) : msg_seed = {
  return msg_seeds[(sk,ek)];
 }

 
 fun Respond(B:part, A:part, X: message) : message option = {
  var y : eph_key = gen_eph_key();  
  var msgs : msg_seed = gen_msg_seed();
  var Y : message option = Some(inp(skey[B], y, msgs));
  if (!in_dom((B,proj(Y)), seed) && in_dom(A, skey) && in_dom(B, skey)
   && sess < qSess && !in_dom((B,proj(Y)),complete_sessions)) {
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


 (*Adversary implementations *)
 fun findelse_g_impl_C(m : (session_id, session_key) map, str : session_string) : session_id option = {
  var sid' : session_id = dummy_session_id;
  var lG : session_id list = dom(m);
  var res : session_id option  = None;
  var t : bool = false;
   while (lG <> [] && !t){
   sid' = hd(lG);
   lG = tl(lG);
   t = eqS_oracle(str,sid');
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }

 fun findelse_sid_impl_C(m : (session_id, session_key) map, sid : session_id) : session_id option = {
  var sid' : session_id = dummy_session_id;
  var lG : session_id list = dom(m);
  var res : session_id option  = None;
  var t : bool = false;
   while (lG <> [] && !t){
   sid' = hd(lG);
   lG = tl(lG);
   t = same_session_string_oracle(sid,sid');
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }


 fun findelse_h_impl_C(m : (session_string, session_key) map, sid : session_id) : session_string option = {
  var str : session_string = dummy_session_string;
  var listH : session_string list = dom(m);
  var res : session_string option  = None;
  var t : bool = false;
   while (listH <> [] && !t){
   str = hd(listH);
   listH = tl(listH);
   t = eqS_oracle(str,sid);
   if (t) {
    res = Some(str);
   }
  }
  return res;
 }

 fun compute_key_C(s : session_id) : session_key = {
  var ssskey : session_key;
  var sstr : session_string option;
  var sid' : session_id option;
  sstr = findelse_h_impl_C(LH_C,s);
  sid' = findelse_sid_impl_C(G_C,s);
  if (sstr <> None) {
   ssskey = LH_C[proj(sstr)];
  } else
  {
   if (sid' <> None) {
    ssskey = G_C[proj(sid')];
   } else {
     ssskey = gen_session_key();
     G_C[s] = ssskey;
    }
   }
  return ssskey;
 }

 fun iH_C(lam : session_string) : session_key = {
  var sid : session_id option;
  var ssskey : session_key;
  if (in_dom(lam, LH_C)) {
   ssskey = LH_C[lam];
  } else {
   sid = findelse_g_impl_C(G_C,lam);
   if (sid <> None) {
    ssskey = G_C[proj(sid)];
   } else {
    ssskey = gen_session_key();
   }
   LH_C[lam] = ssskey;
  }
  return ssskey;
 }

 fun KeyReveal_C(s : session_id) : session_key ={
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
  (A,B,X,Y) = s;
  sid_queries_C = s::sid_queries_C;
  h = gen_session_key();
  if (in_dom((A,X), complete_sessions_C) &&
   !in_dom(s,tested_session_C) &&
   !in_dom(get_matching_session(s),tested_session_C))
  { (* (A,_,X,_) is completed*)
   B' = session_part(complete_sessions_C[(A,X)]);
   Y' = session_msg(complete_sessions_C[(A,X)]);
   sidA = mk_sid(A, B', X, Y');
   if ( B = B' && Y = Y')
   {(* B = B' /\ Y = Y'*)
    if (!in_dom((B,Y), complete_sessions_C))
    {(*B,_,Y,_ not complete*)
     keys_revealed_C[s] = true;
     ssskey = compute_key_C(s);
    }
      else { (* B,_,Y_ complete *)
     A' = session_part(complete_sessions_C[(B,Y)]);
     X' = session_msg(complete_sessions_C[(B,Y)]);
     sidB = mk_sid(B, A', Y, X');
     matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
     if ( matchb )
     { (*  matches *)
      keys_revealed_C[(B,A,Y,X)] = true;
      keys_revealed_C[s] = true;
      ssskey = compute_key_C(s);
     }
       else
     {(*not match*)
      keys_revealed_C[s] = true;
      ssskey = compute_key_C(s);
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
 
 fun Test_C(s : session_id) : session_key = {
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
  sid_queries_C = s::sid_queries_C;
  h = gen_session_key();
  if (in_dom(s, tested_session_C) ||
   in_dom(get_matching_session(s),tested_session_C)) {
   if(in_dom(s, tested_session_C)) {
    ssskey = tested_session_C[s];
   } else {
    ssskey = tested_session_C[get_matching_session(s)];
   }
  }
    else{(*not a tested session*)
   if (in_dom((A,X), complete_sessions_C) &&
    fresh_sid_op(s,corrupt_C,complete_sessions_C,incomplete_sessions_C) &&
    fresh_sid_op(get_matching_session(s),corrupt_C,complete_sessions_C,incomplete_sessions_C)&&
    !keys_revealed_C[s] && !keys_revealed_C[get_matching_session(s)])
   { (* (A,_,X,_) is completed*)
    B' = session_part(complete_sessions_C[(A,X)]);
    Y' = session_msg(complete_sessions_C[(A,X)]);
    if ( B = B' && Y = Y')
    {(* B = B' /\ Y = Y'*)
     if (in_dom((B,Y), complete_sessions_C))
     { (*B,_,Y_ complete *)
      A' = session_part(complete_sessions_C[(B,Y)]);
      X' = session_msg(complete_sessions_C[(B,Y)]);
      sidB = mk_sid(B,A,Y,X);
      matchb = session_match(s, sidB);
      if ( matchb )
      { (* matches*)
       if (in_dom(sidB, tested_session_C)) {
        ssskey = tested_session_C[sidB];
        tested_session_C[s] = ssskey;
       }
         else {(* matching session not tested*)
        ssskey = h;
        tested_session_C[s] = ssskey;
       }
      }
        else
      {(*not match*)
       ssskey = h;
       tested_session_C[s] = ssskey;
      }
     }
       else
     {(*B,_,Y,_ not complete*)
      ssskey = h;
      tested_session_C[s] = ssskey;
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
 
 fun H_C(str : session_string) : session_key = {
  var sk : session_key;
  argLH_C = str::argLH_C;
  sk = iH_C(str);
  return sk;
 }
 
 fun KG_C() : public_key option ={
  var pk : public_key option;
  pk = KG();
  if (pk <> None){
   corrupt_C[proj(pk)] = false;
  }
  return pk;
 }
 
 fun Init_C(A : part, B : part) : message option = {
  var X : message option;
  X = Init(A,B);
  if (X <> None){
   incomplete_sessions_C[(A,proj(X))] = (B,false);
  }
  return X;
 }
 
 fun Respond_C(A : part, B : part, X : message) : message option = {
  var Y : message option;
  Y = Respond(A,B,X);
  if (Y <> None){
   keys_revealed_C[(B,A,proj(Y),X)] = false;
   complete_sessions_C[(B,proj(Y))] = (A,X,false);
  }
  return Y;
 }
 
 fun Complete_C(A:part, B:part, X:message, Y:message) : unit = {
  var B' : part;
  var eph_flag : bool;
  if (in_dom((A,X), incomplete_sessions_C)) {
   B' = fst(incomplete_sessions_C[(A,X)]);
   eph_flag = snd(incomplete_sessions_C[(A,X)]);
   if (B' = B && !in_dom((A,X), complete_sessions_C)) {
    complete_sessions_C[(A,X)] = (B,Y,eph_flag);
    keys_revealed_C[(A,B,X,Y)] = false;
   }
  }
  Complete(A,B,X,Y);
 }

 fun Corrupt_C(A : part) : secret_key option ={
  var sk : secret_key option= None;
  if (fresh_op(tested_session_C,corrupt_C[A <- true],
    complete_sessions_C,incomplete_sessions_C)) {
   sk = Corrupt(A);
   corrupt_C[A] = true;
  }
  return sk;
 }
 

 fun EphKeyReveal_C(A : part, X : message) : eph_key option = {
   var corr_flagA : bool = false;
   var test_flagA : bool = false;
   var B : part;
   var Y : message;
   var ekey : eph_key option = None;
   if (in_dom((A,X), complete_sessions_C)) {
    B = session_part(complete_sessions_C[(A,X)]);
    Y = session_msg(complete_sessions_C[(A,X)]);
    if (fresh_op(tested_session_C,corrupt_C,
       complete_sessions_C[(A,X) <- (B,Y,true)],incomplete_sessions_C)){
     complete_sessions_C[(A,X)] = (B,Y,true);
     ekey = EphKeyReveal(A,X);
    }
   }
    else {(*not in complete*)
    if (in_dom((A,X), incomplete_sessions_C)) {
     B = fst(incomplete_sessions_C[(A,X)]);
     if(fresh_op(tested_session_C,corrupt_C,complete_sessions_C,
       incomplete_sessions_C[(A,X) <- (B, true)])) {
      incomplete_sessions_C[(A,X)] = (B, true);
      ekey = EphKeyReveal(A,X);
     }
    }
   }
   return ekey;
  }

 fun MsgSeedReveal_C (sk : secret_key, ek : eph_key) : msg_seed = {
  var msgs : msg_seed;
  msgs = MsgSeedReveal(sk,ek);
  return msgs;
 }

 

 abs A = A { KG_C, Init_C, Respond_C, Complete_C, Corrupt_C, KeyReveal_C, H_C, Test_C, EphKeyReveal_C, MsgSeedReveal_C }

 fun B() : (session_id * session_string) = {
  var b' : bool;
  var argLH_aux : session_string list;
  var str : session_string;
  var res :  session_id option = None;
  var ret : (session_id * session_string) = (dummy_session_id,dummy_session_string); 
  keys_revealed_C = empty_map;
  sid_queries_C = [];
  argLHT_C = [];
  argLH_C = [];
  G_C = empty_map;
  LH_C = empty_map;
  LHT_C = empty_map;
  b_c = {0,1};
  b' = A();
  argLH_aux = argLH_C;
  while(argLH_aux <> [] && res = None){
   str = hd(argLH_aux);
   argLH_aux = tl(argLH_aux);
   res = findelse_g_impl_C(tested_session_C,str);
  }
  if (res <> None) {
   ret = (proj(res),str);
  }
  return ret;
 }
 
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