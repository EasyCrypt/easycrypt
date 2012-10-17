(*skA -- skB *)
(*true = A, false = B*)
(* first case: initA, respondB*)
include "ake_game5'.ec".

cnst maxInitA : int.
cnst maxRespondB : int.

game AKE_red_5_101' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var cantKG : int
 var initA_done : int
 var respondB_done : int
 var eph_key_initA : eph_key
 var eph_key_respondB : eph_key
 var initMsg : message
 var respMsg : message

 (*Context state *)

 var complete_sessions_C : complete_session_with_status
 var incomplete_sessions_C : incomplete_session_with_status
 var corruptA_C : bool
 var corruptB_C : bool
 var seed_C     : (message * part, eph_key) map
 var pkA_C : public_key
 var pkB_C : public_key
 var skA_C : secret_key
 var skB_C : secret_key
 var cantKG_C : int
 var cantInitA_C : int
 var cantRespondB_C : int
 var indexInitA_C : int
 var indexRespondB_C : int
 var bad : bool
 var initMSG_C : message
 var respondMSG_C : message
 var positionMSG_INIT_C : (message, int) map
 var positionMSG_RESPOND_C : (message, int) map
 
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG () : public_key * secret_key = {
  var pk : public_key = gen_public_key(dummy);
  var sk : secret_key = dummy;
  if (cantKG = 0) {
   sk = gen_secret_key(0);
   pk = gen_public_key(sk);
   skA = sk;
   pkA = pk;
   cantKG = 1;
  } else {
   if (cantKG = 1) {
    sk = gen_secret_key(0);
    pk = gen_public_key(sk);
    skB = sk;
    pkB = pk;
    cantKG = 2;
   }
  }
  return (pk,sk);
 }


 fun InitA () : message ={
  var X : message = dummy_message;
  if (cantKG = 2) {
   if (initA_done = 0) {
    eph_key_initA = gen_eph_key(0);
    X = out_noclash(skA,eph_key_initA);
    initMsg = X;
    initA_done = 1;
  }
 }
 return X;
}

fun RespondB (X : message) : message ={
 var Y : message = dummy_message;
 if (cantKG = 2) {
  if (respondB_done = 0) {
   eph_key_respondB = gen_eph_key(0);
   Y = inp(skB,eph_key_respondB);
   respMsg = Y;
   respondB_done = 1;
  }
 }
 return Y;
}


 (*Adversary implementations *)

 fun KG_C() : public_key  = {
  var k : public_key * secret_key;
  k = KG();
  if (cantKG_C = 0){
   (pkA_C,skA_C) = k;
   corruptA_C = false;
   cantKG_C = 1;
  }
  else {
   if (cantKG_C = 1){
    (pkB_C,skB_C) = k;
    cantKG_C = 2;
    corruptB_C = false;
    if (pkB_C = pkA_C) {bad = true;}
   }
  }
 return (fst(k));
} 

fun Init_C(b : bool) : message = {
 var x : eph_key;
 var X : message = dummy_message;
 if (cantKG = 2){
  if (b) {
   if (cantInitA_C = indexInitA_C) {
    X = InitA();
    if (!in_dom((X,pkA),seed_C) ) {
     initMSG_C = X;
     incomplete_sessions_C[(pkA,X)] = (pkB,false);
    } else {X = dummy_message;bad = true;}
   }
   else {
    x = gen_eph_key(0);
    X = out_noclash(skA_C, x);
    if (!in_dom((X,pkA_C), seed_C) &&  (cantInitA_C <= indexInitA_C ||  
      X <> initMSG_C) ) {
     incomplete_sessions_C[(pkA,X)] = (pkB,false);
     seed_C[(X,pkA)] = x;
    } else {X = dummy_message;bad = true;}
   }
   positionMSG_INIT_C[X] = cantInitA_C;
   cantInitA_C = cantInitA_C + 1;
  }
  else {
   x = gen_eph_key(0);
   X = out_noclash(skB_C, x);
   if (!in_dom((X,pkB_C),seed_C) && (cantRespondB_C <= indexRespondB_C || 
                                    X <> respondMSG_C))
   {
    seed_C[(X,pkB_C)] = x;
    incomplete_sessions_C[(pkB,X)] = (pkA,false);
   } else {bad = true;}
  } 
 }
 return X;
}

fun Respond_C(b : bool, X: message) : message = {
 var y : eph_key;
 var Y : message = dummy_message;
 if (cantKG = 2){
  if (!b) {
   if (cantRespondB_C = indexRespondB_C) {
    Y = RespondB(X);
    if (!in_dom((Y,pkB),seed_C)) {
     respondMSG_C = Y;
     complete_sessions_C[(pkB,Y)] = (pkA,X,false,false);
    } else {X = dummy_message;bad = true;}
   }
   else {
    y = gen_eph_key(0);
    Y = inp(skB_C, y);
    if (!in_dom((Y,pkB_C), seed_C) &&  (cantRespondB_C <= indexRespondB_C ||  
      Y <> respondMSG_C) ) {
     complete_sessions_C[(pkB,Y)] = (pkA,X,false,false);
     seed_C[(Y,pkB)] = y;
    } else {X = dummy_message;bad = true;}
   }
   positionMSG_RESPOND_C[Y] = cantRespondB_C;
   cantRespondB_C = cantRespondB_C + 1;
  }
  else {
   y = gen_eph_key(0);
   Y = inp(skA_C, y);
   if (!in_dom((Y,pkA_C),seed_C) && (cantInitA_C <= indexInitA_C || 
     Y <> initMSG_C))
   {
    seed_C[(Y,pkA_C)] = y;
    complete_sessions_C[(pkA,Y)] = (pkB,X,false,false);
   } else {bad = true;}
  } 
 }
 return Y;
}

fun Complete_C(b : bool, X, Y : message) : unit ={
 var eph_flag : bool;
 if (b)
 {
  if (in_dom((pkA_C,X), incomplete_sessions_C)) {
   eph_flag = snd(incomplete_sessions_C[(pkA_C,X)]);
   if (!in_dom((pkA_C,X), complete_sessions_C)) {
    complete_sessions_C[(pkA_C,X)] = mk_session_descr(pkB_C,Y,eph_flag,false);
      (*get rid of the session in incomplete*)
   }
  }
 } else{
  if (in_dom((pkB_C,X), incomplete_sessions_C)) {
   eph_flag = snd(incomplete_sessions_C[(pkB_C,X)]);
   if (!in_dom((pkB_C,X), complete_sessions_C)) {
    complete_sessions_C[(pkB_C,X)] = mk_session_descr(pkA_C,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 }
}


 fun Corrupt_C(b : bool) : secret_key = {
  var res : secret_key = dummy;
  if (b) {  
   if (cantKG = 1){
    res = skA_C;
    corruptA_C = true;
   }
  } 
  else {
   if (cantKG = 2){
    res = skB_C;
    corruptB_C = true;
   }
  }
  return (res);
 } 
 
 fun EphKeyReveal_C(b : bool, X : message) : eph_key = { 
  var kr_flagA : bool = false;
  var corr_flagA : bool = false;
  var test_flagA : bool = false;
  var B : part;
  var Y : message;
  var s : session_id;
  var ekey : eph_key = dummy_eph_key;
  if(b) {
   if (!corruptA_C){
    if (!in_dom(X,positionMSG_INIT_C) || cantInitA_C <= indexInitA_C || 
        positionMSG_INIT_C[X] <> indexInitA_C){
     if (in_dom((pkA,X), complete_sessions_C)) {
      kr_flagA = session_key_reveal_flag(complete_sessions_C[(pkA,X)]);
      B = session_part(complete_sessions_C[(pkA,X)]);
      Y = session_msg(complete_sessions_C[(pkA,X)]);
      s = mk_sid(pkA,pkB,X,Y);
      complete_sessions_C[(pkA,X)] = mk_session_descr(B,Y,true,kr_flagA);
      ekey = seed_C[(X,pkA)];
     }
       else {(*not in complete*)
      if (in_dom((pkA,X), incomplete_sessions_C)) {
       B = fst(incomplete_sessions_C[(pkA,X)]);
       incomplete_sessions_C[(pkA,X)] = (B, true);
       ekey = seed_C[(X,pkA)];     
      }
     }
    }  else {
     ekey = gen_eph_key(0);
     bad = true;
    }
   }
  }
    else
  {
   if (!corruptB_C){
    if (!in_dom(X,positionMSG_RESPOND_C) || cantRespondB_C <= indexRespondB_C ||
     positionMSG_RESPOND_C[X] <> indexRespondB_C) {
     if (in_dom((pkB_C,X), complete_sessions_C)) {
      kr_flagA = session_key_reveal_flag(complete_sessions_C[(pkB_C,X)]);
      B = session_part(complete_sessions_C[(pkB_C,X)]);
      Y = session_msg(complete_sessions_C[(pkB_C,X)]);
      s = mk_sid(pkB_C,pkA_C,X,Y);
      complete_sessions_C[(pkB_C,X)] = mk_session_descr(B,Y,true,kr_flagA);
      ekey = seed_C[(X,pkB_C)];
     } else {(*not in complete*)
      if (in_dom((pkB_C,X), incomplete_sessions_C)) {
       B = fst(incomplete_sessions_C[(pkB_C,X)]);
       incomplete_sessions_C[(pkB_C,X)] = (B, true);
       ekey = seed_C[(X,pkB_C)];     
      }
     }
    } else {
     ekey = gen_eph_key(0);
     bad = true;  
    }
    
   }
  }
  return ekey;  
 }
 
 
 
 abs C = C {KG_C, Init_C, Respond_C, Complete_C, Corrupt_C, 
            EphKeyReveal_C, eqS, same_session_string }


 fun E() : session_string = {
  var sid : session_id;
  var str : session_string;
  complete_sessions_C = empty_map;
  incomplete_sessions_C = empty_map;
  corruptA_C = false;
  corruptB_C = false;
  seed_C = empty_map;
  skA_C = dummy;
  pkA_C = gen_public_key(skA);
  skB_C = dummy;
  pkB_C = gen_public_key(skA);
  cantKG_C = 0;
  cantInitA_C = 0;
  cantRespondB_C = 0;
  indexInitA_C = [0..maxInitA];
  indexRespondB_C = [0..maxRespondB];
  bad = false;
  initMSG_C = dummy_message;
  respondMSG_C = dummy_message;
  positionMSG_INIT_C = empty_map;
  positionMSG_RESPOND_C = empty_map;
  (sid,str) = C();
  return str;
 }

 fun Main () : session_string = {
  var str : session_string;
  skA = dummy;
  pkA = gen_public_key(skA);
  skB = dummy;
  pkB = gen_public_key(skB);
  cantKG = 0;
  initA_done = 0;
  respondB_done = 0;
  eph_key_initA = dummy_eph_key;
  eph_key_respondB = dummy_eph_key;
  str = E();
  return (str);
 }
}.

game AKE5'_10 = AKE5'  
var cantInitA : int
var indexInitA : int
var positionMsgInit : (message, int) map
var cantRespondB : int
var indexRespondB : int
var positionMsgRespond : (message, int) map
var bad : bool
where  Init = {
 var x : eph_key = gen_eph_key(0);
 var X : message = dummy_message;
 if (cantKG = 2){
  if (b) {
   X = out_noclash(skA, x);
   if (!in_dom((X,pkA), seed)) {
    incomplete_sessions[(pkA,X)] = (pkB,false);
    seed[(X,pkA)] = x;
    positionMsgInit[X] = cantInitA;
    cantInitA = cantInitA + 1;
   } else {X = dummy_message;bad = true;}
  }
  else {
   X = out_noclash(skB, x);
   if (!in_dom((X,pkB), seed)) {
    incomplete_sessions[(pkB,X)] = (pkA,false);
    seed[(X,pkB)] = x;
   } else {X = dummy_message;bad = true;}
  }
 }
 return X;
}
and KG = {
  var pk : public_key = gen_public_key(dummy);
  if (cantKG = 0) {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   pk = pkA;
   corruptA = false;
   cantKG = 1;
  } else {
   if (cantKG = 1){
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    if (pkA = pkB) {bad = true;}
    pk = pkB;
    corruptB = false;
    cantKG = 2;
   }
  }
  return pk;
 }

and Respond = {
 var y : eph_key = gen_eph_key(0);  
 var Y : message = dummy_message;
 if (cantKG = 2){
  if (b){
   Y = inp(skA, y);
   if (!in_dom((Y,pkA), seed)) {
    complete_sessions[(pkA,Y)] = mk_session_descr(pkB, X, false, false);
    seed[(Y, pkA)] = y;
   } else {Y = dummy_message;bad = true;}
  }
  else
  {
   Y = inp(skB, y);
   if (!in_dom((Y,pkB), seed)) {
    complete_sessions[(pkB,Y)] = mk_session_descr(pkA, X, false, false);
    seed[(Y, pkB)] = y;
    positionMsgRespond[Y] = cantRespondB;
    cantRespondB = cantRespondB + 1;
   } else {Y = dummy_message;bad = true;}
  }
 }
 return Y;
}

and EphKeyReveal = { 
  var kr_flagA : bool = false;
  var corr_flagA : bool = false;
  var test_flagA : bool = false;
  var B : part;
  var Y : message;
  var s : session_id;
  var ekey : eph_key = dummy_eph_key;
  if(b) {
   corr_flagA = corruptA;
   if (!corr_flagA) (* not corrupted*)
   {
    if (cantInitA > indexInitA && in_dom(X,positionMsgInit) && positionMsgInit[X] = indexInitA) {
     bad = true;
    }
    if (in_dom((pkA,X), complete_sessions)) {
     kr_flagA = session_key_reveal_flag(complete_sessions[(pkA,X)]);
     B = session_part(complete_sessions[(pkA,X)]);
     Y = session_msg(complete_sessions[(pkA,X)]);
     s = mk_sid(pkA,pkB,X,Y);
     complete_sessions[(pkA,X)] = mk_session_descr(B,Y,true,kr_flagA);
     ekey = seed[(X,pkA)];
    }
      else {(*not in complete*)
     if (in_dom((pkA,X), incomplete_sessions)) {
      B = fst(incomplete_sessions[(pkA,X)]);
      incomplete_sessions[(pkA,X)] = (B, true);
      ekey = seed[(X,pkA)];     
     }
    } 
   }
  }
  else
  {
   corr_flagA = corruptB;
   if (!corr_flagA) (* not corrupted*)
   {
    if (cantRespondB > indexRespondB && in_dom(X,positionMsgRespond) 
        && positionMsgRespond[X] = indexRespondB) {
     bad = true;
    } else {
     
     if (in_dom((pkB,X), complete_sessions)) {
      kr_flagA = session_key_reveal_flag(complete_sessions[(pkB,X)]);
      B = session_part(complete_sessions[(pkB,X)]);
      Y = session_msg(complete_sessions[(pkB,X)]);
      s = mk_sid(pkB,pkA,X,Y);
      complete_sessions[(pkB,X)] = mk_session_descr(B,Y,true,kr_flagA);
      ekey = seed[(X,pkB)];
     }
       else {(*not in complete*)
      if (in_dom((pkB,X), incomplete_sessions)) {
       B = fst(incomplete_sessions[(pkB,X)]);
       incomplete_sessions[(pkB,X)] = (B, true);
       ekey = seed[(X,pkB)];     
      }
     }
    }
   }
  }
  return ekey;  
 }

and Main = {
 var sidss : session_id * session_string;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 corruptA = false;
 corruptB = false;
 bad = false;
 skA = dummy;
 skB = dummy;
 pkA = gen_public_key(skA);
 pkB = gen_public_key(skA);
 cantKG = 0;
 positionMsgInit = empty_map;
 positionMsgRespond = empty_map;
 seed  = empty_map;
 cantInitA = 0;
 cantRespondB = 0;
 indexInitA = [0..maxInitA];
 indexRespondB = [0..maxRespondB];
 sidss = C();
 return sidss;
}.

pred inv (
  pkA2     : public_key,
  skA2     : secret_key, 
  pkB2     : public_key, 
  skB2     : secret_key, 
  cantKG2 : int,
  initA_done2 : int,
  respondB_done2 : int,
  eph_key_initA2 : eph_key,
  eph_key_respondB2 : eph_key,
  initMsg : message,
  respMsg : message,
  complete_sessions_C : complete_session_with_status,
  incomplete_sessions_C : incomplete_session_with_status,
  corruptA_C : bool,
  corruptB_C : bool,
  seed_C     : (message * part, eph_key) map,
  pkA_C : public_key,
  pkB_C : public_key,
  skA_C : secret_key,
  skB_C : secret_key,
  cantKG_C : int,
  cantInitA_C : int,
  cantRespondB_C : int,
  indexInitA_C : int,
  indexRespondB_C : int,
  initMSG_C : message,
  respondMSG_C : message,
  positionMSG_INIT_C : (message, int) map,
  positionMSG_RESPOND_C : (message, int) map,
  cantInitA1 : int,
  indexInitA1 : int,
  positionMsgInit1 : (message, int) map,
  cantRespondB1 : int,
  indexRespondB1 : int,
  positionMsgRespond1 : (message, int) map,
  complete_sessions1 : complete_session_with_status,
  incomplete_sessions1 : incomplete_session_with_status,
  corruptA1 : bool,
  corruptB1 : bool,
  seed1     : (message * part, eph_key) map,
  pkA1 : public_key,
  pkB1 : public_key,
  skA1 : secret_key,
  skB1 : secret_key,
  cantKG1 : int) = 
(cantKG1 = cantKG2 && cantKG_C = cantKG2 && pkA1 = pkA2 && pkA2 = pkA_C && pkB1 = pkB2 && pkB2 = pkB_C && skA1 = skA2 && skA2 = skA_C && skB1 = skB2 && skB2 = skB_C &&
cantInitA_C = cantInitA1 && cantRespondB_C = cantRespondB1 && indexInitA_C = indexInitA1 && indexRespondB_C = indexRespondB1 && 0 <= indexRespondB1 && 0 <= indexInitA1
&&  complete_sessions1 = complete_sessions_C &&
  incomplete_sessions1 = incomplete_sessions_C &&
 corruptA1 = corruptA_C && corruptB1 = corruptB_C &&
positionMSG_INIT_C =  positionMsgInit1 &&
positionMsgRespond1 = positionMSG_RESPOND_C &&
 (forall (X:message), in_dom(X,positionMSG_INIT_C) => 
  positionMSG_INIT_C[X] < cantInitA_C) &&
 (forall (X:message), in_dom(X,positionMSG_RESPOND_C) => 
  positionMSG_RESPOND_C[X] < cantRespondB_C) &&
(forall (X : message,A : part), 
(in_dom((A,X),complete_sessions1) || in_dom((A,X),incomplete_sessions1)) =>
(in_dom((X,A),seed1))) && (cantKG1 = 0 || cantKG1 = 1 || cantKG1 = 2)  
&& (forall (m1, m2 : message), 
in_dom(m1,positionMsgInit1) && 
in_dom(m2, positionMsgInit1) && positionMsgInit1[m1] = positionMsgInit1[m2] 
=> m1 = m2) &&
(forall (m1, m2 : message), 
in_dom(m1,positionMsgRespond1) && 
in_dom(m2,positionMsgRespond1) && positionMsgRespond1[m1] = positionMsgRespond1[m2] 
=> m1 = m2)
) 
&& 
((cantKG1 = 0 || cantKG1 = 1) => 
 (complete_sessions1 = empty_map &&
  incomplete_sessions1 = empty_map &&
  seed1 = empty_map &&
  seed1 = seed_C && cantInitA1 = 0 && cantRespondB1 = 0 &&
 initA_done2 = 0 && respondB_done2 = 0 && positionMsgInit1 = empty_map
 && positionMsgRespond1 = empty_map)) &&
(cantKG1 = 2 => pkA1 <> pkB1) &&
((cantKG1 = 2 && cantInitA1 <= indexInitA1 &&  cantRespondB1 <= indexRespondB1) => 
 seed1 = seed_C &&
 initA_done2 = 0 && 
 respondB_done2 = 0)  &&
((cantKG1 = 2 && cantInitA1 > indexInitA1 &&  cantRespondB1 <= indexRespondB1) => 
 !in_dom((initMSG_C,pkA_C),seed_C) &&
 in_dom(initMSG_C,positionMSG_INIT_C) && positionMSG_INIT_C[initMSG_C] = indexInitA_C && 
 seed1 = upd(seed_C,(initMSG_C,pkA_C),eph_key_initA2) &&
 initMsg = initMSG_C &&
 initA_done2 = 1 && 
 respondB_done2 = 0) &&
((cantKG1 = 2 && cantInitA1 <= indexInitA1 &&  cantRespondB1 > indexRespondB1) => 
 !in_dom((respondMSG_C,pkB_C),seed_C) &&
 respMsg = respondMSG_C &&
 in_dom(respondMSG_C,positionMSG_RESPOND_C) && 
 positionMSG_RESPOND_C[respondMSG_C] = indexRespondB_C &&
 seed1 = upd(seed_C,(respondMSG_C,pkB_C),eph_key_respondB2) &&
 initA_done2 = 0 && 
 respondB_done2 = 1) &&
((cantKG1 = 2 && cantInitA1 > indexInitA1 &&  cantRespondB1 > indexRespondB1) => 
 !in_dom((respondMSG_C,pkB_C),seed_C) &&
 !in_dom((initMSG_C,pkA_C),seed_C) &&
 in_dom(initMSG_C,positionMSG_INIT_C) && positionMSG_INIT_C[initMSG_C] = indexInitA_C &&
 in_dom(respondMSG_C,positionMSG_RESPOND_C) && 
 respMsg = respondMSG_C &&
 initMsg = initMSG_C &&
 positionMSG_RESPOND_C[respondMSG_C] = indexRespondB_C &&
 seed1 = upd(upd(seed_C,(respondMSG_C,pkB_C),eph_key_respondB2),(initMSG_C,pkA_C),eph_key_initA2) &&
 initA_done2 = 1 && 
 respondB_done2 = 1).
 

equiv KG : AKE5'_10.KG ~ AKE_red_5_101'.KG_C : 
!bad{1} && !bad{2} && 
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}).
inline.
sp 1 2.
if.
trivial.
if.
unfold inv.
trivial.
trivial.
save.

equiv INIT : AKE5'_10.Init ~ AKE_red_5_101'.Init_C : 
!bad{1} && !bad{2} && = {b} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}).
sp 0 1.
if{2}.
if{2}.
if{2}.
inline.
sp 0 1.
condt{2}.
condt{2}.
rnd>>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 4.
if.
trivial. 
trivial.
rnd>>.
trivial.
rnd>>.
sp 1 0.
condt{1}.
condf{1}.
sp 1 1.
if.
trivial.
trivial.
trivial.
save.

equiv RESP : AKE5'_10.Respond ~ AKE_red_5_101'.Respond_C : 
!bad{1} && !bad{2} && = {b,X} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}).
sp 0 1.
if{2}.
if{2}.
if{2}.
inline.
sp 0 2.
condt{2}.
condt{2}.
rnd>>.
trivial.
rnd>>.
trivial.
rnd>>.
trivial.
trivial.
save.


equiv COMP : AKE5'_10.Complete ~ AKE_red_5_101'.Complete_C : 
!bad{1} && !bad{2} && = {b,X,Y} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1})).
trivial.
save.

equiv CORRUPT : AKE5'_10.Corrupt ~ AKE_red_5_101'.Corrupt_C : 
!bad{1} && !bad{2} && = {b} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}).
trivial.
save.


equiv EPHKR : AKE5'_10.EphKeyReveal ~ AKE_red_5_101'.EphKeyReveal_C : 
!bad{1} && !bad{2} && = {b,X} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}).
sp 4 4.
if.
sp 1 0.
if.
ifneg{2}.
if.
trivial.
if.
trivial.
unfold inv.
trivial.
if.
trivial.
trivial.
trivial.
sp 1 0.
if.
ifneg{1}.
if.
if.
trivial.
unfold inv.
trivial.
if.
trivial.
trivial.
trivial.
trivial.
save.



equiv ADV : AKE5'_10.C ~ AKE_red_5_101'.C : 
!bad{1} && !bad{2} &&
inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) ==> 
(bad{1} <=> bad{2}) &&
(!bad{1} => inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1}) && ={res}) by auto upto (bad) 
 with
 (inv(pkA{2},skA{2},pkB{2},skB{2},cantKG{2},initA_done{2},respondB_done{2},
 eph_key_initA{2},eph_key_respondB{2},initMsg{2},respMsg{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},
 pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},cantInitA_C{2},cantRespondB_C{2},
 indexInitA_C{2},indexRespondB_C{2},initMSG_C{2},respondMSG_C{2},
 positionMSG_INIT_C{2},positionMSG_RESPOND_C{2},cantInitA{1},indexInitA{1},
 positionMsgInit{1},cantRespondB{1},indexRespondB{1},positionMsgRespond{1},
 complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},seed{1},
 pkA{1},pkB{1},skA{1},skB{1},cantKG{1})).



op fresh_sid3g5'_op : (session_id,bool,bool,complete_session_with_status, incomplete_session_with_status) -> bool.


axiom fcop3g5' :
forall(sid : session_id,
 corruptA, corruptB : bool,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid3g5'_op(sid, corruptA,corruptB,complete_session,incomplete_session)
<=>
fresh_sid3g5'(sid, corruptA,corruptB,complete_session,incomplete_session).

equiv MAIN : AKE5'_10.Main ~ AKE_red_5_101'.Main : true ==> 
!bad{1} => 
 ((eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA
&& cantInitA{1}> indexInitA{1}
&& cantRespondB{1}> indexRespondB{1} 
&& sndpart(fst(res)) = pkB 
&& fresh_sid3g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)
&& positionMsgInit[fstmsg(fst(res))] = indexInitA
&& positionMsgRespond[sndmsg(fst(res))] = indexRespondB){1} 
=> 
positionMsgInit[fstmsg(fst(res))]{1} = positionMSG_RESPOND_C[initMSG_C]{2}
(eqS_oracle(res, (pkA,pkB,initMsg,respMsg))){2}).
inline.
wp.
call using ADV.
wp.
rnd.
rnd.
wp.
trivial.
unfold inv.
trivial.