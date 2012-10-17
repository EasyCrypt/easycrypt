include "ake_game5'.ec".

adversary D () :  (message * session_string)
{
 () -> public_key; (*KG*)
 () -> secret_key; (*corruptA*)
 () -> message; (* Init: start either with A *)
 () -> message * eph_key ; (* Init: start either with B *)
 message -> message  * eph_key; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

axiom  a : forall (x : eph_key, A : secret_key), out_noclash(A,x) <> dummy_message.

cnst maxInit : int.

game AKE_red_5_81' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var ephKA_X : eph_key
 var seedB   : (message, eph_key) map 
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var initA_done : int
 var cantKG : int


 (*Adversary state *)

 var positionMsg_C : (message, int) map
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
 var initAIndex_C : int
 var cantInitA_C : int
 var initMSG_C : message
 var bad : bool

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key ={
  var sk : secret_key = dummy;
  var pk : public_key = gen_public_key(sk);
  if (cantKG = 0) {
   sk = gen_secret_key(0);
   skA = sk;
   pk = gen_public_key(sk);
   pkA = pk;
   cantKG = 1;
  } else {
   if (cantKG = 1) {
    sk = gen_secret_key(0);
    skB = sk;
    pk = gen_public_key(sk);
    pkB = pk;
    cantKG = 2;
   }
  }
  return pk;
 }

 fun InitA() : message = {
  var X : message = dummy_message;
  var x : eph_key;
  if (initA_done = 0){
   x = gen_eph_key(0);
   ephKA_X = x;
   X = out_noclash(skA,x);
   incomplete_sessions[(pkA,X)] = (pkB,false);
   initA_done = 1;
  }
  return (X);
 }
 
 fun CorruptA() : secret_key = {
  return skA;
 } 
 
 fun InitB() : message * eph_key = {
  var X : message;
  var x : eph_key;
  x = gen_eph_key(0);
  X = out_noclash(skB,x);
  if (!in_dom(X,seedB)){
  seedB[X] = x;
  incomplete_sessions[(pkB,X)] = (pkA,false);
  } else {X = dummy_message;x=dummy_eph_key;}
  return (X,x);
 }
 
 
 fun RespondB(X : message) : message * eph_key = {
 var Y : message;
 var y : eph_key;
 y = gen_eph_key(0);
 Y = inp(skB,y);
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}

fun Complete(X : message, Y : message) : unit = {
 var eph_flag : bool;
 if (in_dom((pkB,X), incomplete_sessions)) {
  eph_flag = snd(incomplete_sessions[(pkB,X)]);
  if (!in_dom((pkB,X), complete_sessions)) {
   complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
   (*get rid of the session in incomplete*)
  }
 }
}

(* Adversary Implementations *)
 fun KG_C() : public_key  = {
  var pk : public_key;
  pk = KG();
  if (cantKG_C = 0){
   pkA_C = pk;
   skA_C = CorruptA();
   corruptA_C = false;
   cantKG_C = 1;
  }
  else {
   if (cantKG_C = 1){
    pkB_C = pk;
    cantKG_C = 2;
    corruptB_C = false;
    if (pkB_C = pkA_C) {bad = true;}
   }
  }
 return pk;
} 
 
 fun Init_C(b : bool) : message = {
  var x : eph_key;
  var X : message = dummy_message;
  if (cantKG = 2){
   if (b) {
    if (cantInitA_C = initAIndex_C) {
     X = InitA();
     if (!in_dom((X,pkA),seed_C)) {
      initMSG_C = X;
      incomplete_sessions_C[(pkA,X)] = (pkB,false);
     } else {X = dummy_message;bad = true;}
    }
    else {
     x = gen_eph_key(0);
     X = out_noclash(skA_C, x);
     if (!in_dom((X,pkA_C), seed_C) &&  (cantInitA_C <= initAIndex_C ||  
                                         X <> initMSG_C) ) {
      incomplete_sessions_C[(pkA,X)] = (pkB,false);
      seed_C[(X,pkA)] = x;
     } else {X = dummy_message;bad = true;}
    }
    positionMsg_C[X] = cantInitA_C;
    cantInitA_C = cantInitA_C + 1;
   }
   else {
    (X,x) = InitB();
    if (X <> dummy_message && !in_dom((X,pkB_C),seed_C))
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
 if (cantKG_C = 2){
  if (b){
   y = gen_eph_key(0);
   Y = inp(skA_C, y);
   if (!in_dom((Y,pkA_C), seed_C) && (cantInitA_C <= initAIndex_C || Y <> initMSG_C) ) {
    complete_sessions_C[(pkA,Y)] = mk_session_descr(pkB_C, X, false, false);
    seed_C[(Y, pkA)] = y;
   } else {Y = dummy_message;bad = true;}
  }
  else
  {
   (Y,y) = RespondB(X);
   if (!in_dom((Y,pkB_C),seed_C)){
    complete_sessions_C[(pkB_C,Y)] = mk_session_descr(pkA_C, X, false, false);
    seed_C[(Y,pkB_C)] = y;
   } else {Y = dummy_message;bad = true;}
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
   Complete(X,Y);
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
    res = gen_secret_key(0);
    corruptB_C = true;
    bad = true;
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
    if (cantInitA_C <= initAIndex_C || positionMsg_C[X] <> initAIndex_C){
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
    if (in_dom((pkB_C,X), complete_sessions_C)) {
     kr_flagA = session_key_reveal_flag(complete_sessions_C[(pkB_C,X)]);
     B = session_part(complete_sessions_C[(pkB_C,X)]);
     Y = session_msg(complete_sessions_C[(pkB_C,X)]);
     s = mk_sid(pkB_C,pkA_C,X,Y);
     complete_sessions_C[(pkB_C,X)] = mk_session_descr(B,Y,true,kr_flagA);
     ekey = seed_C[(X,pkB_C)];
    }
      else {(*not in complete*)
     if (in_dom((pkB_C,X), incomplete_sessions_C)) {
      B = fst(incomplete_sessions_C[(pkB_C,X)]);
      incomplete_sessions_C[(pkB_C,X)] = (B, true);
      ekey = seed_C[(X,pkB_C)];     
    }
   }
  }
 }
  return ekey;  
 }
 
 
 
 abs C = C {KG_C, Init_C, Respond_C, Complete_C, Corrupt_C, 
            EphKeyReveal_C, eqS, same_session_string }


 fun D() : message * session_string = {
  var A, B : part;
  var X, Y : message;
  var sid : session_id;
  var str : session_string;
  complete_sessions_C = empty_map;
  incomplete_sessions_C = empty_map;
  corruptA_C = false;
  corruptB_C = false;
  seed_C = empty_map;
  skA_C = dummy;
  pkA_C = gen_public_key(skA_C);
  skB_C = dummy;
  pkB_C = gen_public_key(skB_C);
  cantKG_C = 0;
  cantInitA_C = 0;
  positionMsg_C = empty_map;
  initAIndex_C = [1..maxInit];
  initMSG_C = dummy_message;
  bad = false;
  (sid,str) = C();
  (A,B,X,Y) = sid;
  return (X,str);
 }

fun Main () : message * session_string = {
 var sidss : message * session_string; 
 var alpha : message; 
 var str : session_string;
 skA = dummy;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 initA_done = 0;
 cantKG = 0;
 pkA = gen_public_key(skA);
 skB = dummy;
 pkB = gen_public_key(skB);
 ephKA_X = dummy_eph_key;
 seedB  = empty_map;
 sidss = D();
 (alpha,str) = sidss;
 return (alpha,str);
 }
}.

game AKE5'_1 = AKE5'
var cantInitA : int
var indexInitA : int
var positionMsg : (message, int) map
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
    positionMsg[X] = cantInitA;
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
   } else {Y = dummy_message;bad = true;}
  }
 }
 return Y;
}
and Corrupt = {
  var res : secret_key = dummy;
  if (b) {  
   if (cantKG = 1){
    res = skA;
    corruptA = true;
   }
  } 
  else {
   if (cantKG = 2){
    res = skB;
    corruptB = true;
    bad = true;
   }
  }
  return (res);
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
    if (cantInitA > indexInitA && positionMsg[X] = indexInitA) {
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
 positionMsg = empty_map;
 seed  = empty_map;
 cantInitA = 0;
 indexInitA = [1..maxInit];
 sidss = C();
 return sidss;
}.

checkproof.

pred inv(complete_sessions1   : complete_session_with_status,
  incomplete_sessions1  : incomplete_session_with_status,
  corruptA1             : bool,
  corruptB1             : bool,
  seed1                 : (message * part, eph_key) map,
  pkA1                  : public_key,
  pkB1                  : public_key,
  skA1                  : secret_key,
  skB1                  : secret_key,
  cantKG1               : int,
  positionMsg1          : (message,int) map,
  cantInitA1            : int,
  indexInitA1           : int,
  complete_sessions_C   : complete_session_with_status,
  incomplete_sessions_C : incomplete_session_with_status,
  corruptA_C            : bool,
  corruptB2             : bool,
  seed_C                : (message * part, eph_key) map,
  pkA_C                 : public_key,
  pkB_C                 : public_key,
  skA_C                 : secret_key,
  skB_C                 : secret_key,
  cantKG_C              : int,
  initAIndex_C          : int,
  initMSG_C             : message,
  cantInitA_C           : int,
  positionMsg_C : (message, int) map,
  pkA2 : public_key, 
  skA2     : secret_key,
  pkB2     : public_key,
  skB2     : secret_key,
  ephKA_X2 : eph_key,
  seedB2   : (message, eph_key) map,
  complete_sessions2 : complete_session_with_status,
  incomplete_sessions2 : incomplete_session_with_status,
  initA_done2 : int,
  cantKG2 : int,
 initA_Done2 : int
) =
cantKG_C = cantKG2 && cantKG_C = cantKG1 && pkA1 = pkA2 && pkA2 = pkA_C &&  pkB2 = pkB_C && 
 pkA1 = gen_public_key(skA1) && pkB1 = gen_public_key(skB1) && skA1 = skA_C &&
pkB1 = pkB2 && skB1 = skB2 && skA1 = skA2  && (cantKG1 = 1 ||cantKG1 = 2 || cantKG1 = 0) &&
corruptB1 = corruptB2 && cantInitA1 = cantInitA_C && initAIndex_C > 0 && 
indexInitA1 = initAIndex_C && positionMsg_C = positionMsg1 &&
corruptA1 = corruptA_C &&
(forall (X : message, A : part),
in_dom((A,X), complete_sessions1) ||in_dom((A,X), incomplete_sessions1) =>
in_dom((X,A), seed1)) &&
(cantKG1 = 0 || cantKG1 = 1 => 
    complete_sessions1 = complete_sessions2 
 && complete_sessions_C = complete_sessions1
 && complete_sessions1 = empty_map 
 && incomplete_sessions1 = incomplete_sessions2 
 && incomplete_sessions_C = incomplete_sessions1
 && incomplete_sessions1 = empty_map && positionMsg1 = empty_map
 &&  seed1 = seed_C && seed_C = empty_map && seedB2 = empty_map 
 && initA_done2 = 0  && cantInitA_C = 0) &&
(cantKG1 = 0 => skA1 = dummy && skB1 = dummy) &&
(cantKG1 = 1 => skB1 = dummy && skA_C = skA2) &&
(cantKG1 = 2 && cantInitA_C <= initAIndex_C => 
 complete_sessions_C = complete_sessions1 && 
 incomplete_sessions_C = incomplete_sessions1 &&
 (forall (X : message), (in_dom((pkB_C,X),complete_sessions_C) <=>
                        in_dom((pkB_C,X),complete_sessions2)) &&
  (in_dom((pkB_C,X),complete_sessions_C) =>
  session_part(complete_sessions_C[(pkB_C,X)]) = session_part(complete_sessions2[(pkB_C,X)]) &&
  session_msg(complete_sessions_C[(pkB_C,X)]) = session_msg(complete_sessions2[(pkB_C,X)])) &&
session_key_reveal_flag(complete_sessions_C[(pkB_C,X)]) =
session_key_reveal_flag(complete_sessions2[(pkB_C,X)])) &&
 (forall (X : message), (in_dom((pkB_C,X),incomplete_sessions_C) <=>
                        in_dom((pkB_C,X),incomplete_sessions2)) &&
  (in_dom((pkB_C,X),incomplete_sessions_C) =>
  fst(incomplete_sessions_C[(pkB_C,X)]) = fst(incomplete_sessions2[(pkB_C,X)]))) &&
 (forall (X:message), (in_dom((X,pkB1),seed1) <=> in_dom(X,seedB2)) &&
                      (in_dom((X,pkB1),seed1) => seed1[(X,pkB1)] = seedB2[X])) &&
                     seed1 = seed_C
 (* (forall (X:message), ((in_dom((X,pkA1),seed1) <=> in_dom((X,pkA1),seed_C)) && *)
 (*                  (in_dom((X,pkA1),seed1) =>seed1[(X,pkA1)] = seed_C[(X,pkA1)])))  *)
 && pkA1 <> pkB1 &&
initA_Done2 = 0 &&
(forall (X : message), in_dom((pkA1,X), incomplete_sessions1) => 
in_dom(X,positionMsg1) && in_dom((X,pkA1),seed1) && 
 X = out_noclash(skA_C,seed1[(X,pkA1)]))) &&
 (cantKG1 = 2 && cantInitA_C > initAIndex_C => 
  initA_done2 = 1 &&
 initMSG_C = out_noclash(skA_C,ephKA_X2) && 
 complete_sessions_C = complete_sessions1 && 
 incomplete_sessions_C = incomplete_sessions1 &&
  (forall (X : message), (in_dom((pkB_C,X),complete_sessions_C) <=>
                        in_dom((pkB_C,X),complete_sessions2)) &&
  (in_dom((pkB_C,X),complete_sessions_C) =>
  session_part(complete_sessions_C[(pkB_C,X)]) = session_part(complete_sessions2[(pkB_C,X)]) &&
  session_msg(complete_sessions_C[(pkB_C,X)]) = session_msg(complete_sessions2[(pkB_C,X)])) &&
session_key_reveal_flag(complete_sessions_C[(pkB_C,X)]) =
session_key_reveal_flag(complete_sessions2[(pkB_C,X)])) &&
 (forall (X : message), (in_dom((pkB_C,X),incomplete_sessions_C) <=> 
                        in_dom((pkB_C,X),incomplete_sessions2)) &&
  (in_dom((pkB_C,X),incomplete_sessions_C) => 
  fst(incomplete_sessions_C[(pkB_C,X)]) = fst(incomplete_sessions2[(pkB_C,X)]))) &&
 (forall (X:message), (in_dom((X,pkB1),seed_C) <=> in_dom(X,seedB2)) &&
                      (in_dom((X,pkB1),seed_C) => seed_C[(X,pkB1)] = seedB2[X])) &&
 (forall (X:message), (in_dom((X,pkB1),seed1) <=> in_dom(X,seedB2)) &&
                      (in_dom((X,pkB1),seed1) => seed1[(X,pkB1)] = seedB2[X]))&&
 (forall (X:message),  
   ((in_dom((X,pkA1),seed_C) => in_dom((X,pkA1),seed1)) &&  
    (in_dom((X,pkA1),seed_C) => seed1[(X,pkA1)] = seed_C[(X,pkA1)]))) &&
 (forall (X:message),  
   ((in_dom((X,pkA1),seed1) => in_dom((X,pkA1),seed_C) || (X = initMSG_C &&
      positionMsg1[X] = initAIndex_C)))) &&  
  (forall (X:message),   positionMsg1[X] <> initAIndex_C => X <> initMSG_C) &&
 (in_dom((initMSG_C,pkA1),seed1) && seed1[(initMSG_C,pkA1)] = ephKA_X2) &&
 (in_dom(initMSG_C,positionMsg1) && positionMsg1[initMSG_C] = initAIndex_C)
  && pkA1 <> pkB1).

equiv KG : AKE5'_1.KG ~ AKE_red_5_81'.KG_C :
 !bad{1} &&
      !bad{2} &&
       inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
           seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
           cantInitA{1},indexInitA{1},complete_sessions_C{2},
           incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
           pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
           initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
           skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
           incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2})
     ==>
     (bad{1} <=> bad{2}) && (!bad{1} =>
      ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
                    corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
                    positionMsg{1},cantInitA{1},indexInitA{1},
                    complete_sessions_C{2},incomplete_sessions_C{2},
                    corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
                    skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
                    cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
                    skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
                    incomplete_sessions{2},initA_done{2},cantKG{2},
                    initA_done{2})).

inline.
sp.
if.
rnd>>.
trivial.
if.
rnd>>.
trivial.
trivial.
save.


equiv Init : AKE5'_1.Init ~ AKE_red_5_81'.Init_C : 
 !bad{1} &&
 !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2}) && ={b}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})).
sp 0 1.
if{2}.
if{2}.
if{2}.
inline.
sp 0 1.
condt{2}.
rnd>>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 5.
if.
unfold inv;trivial.
trivial.
rnd >>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 1.
if.
trivial.
unfold inv.
trivial.
trivial.
inline.
rnd>>.
sp 1 1.
condt{1}.
condf{1}.
sp 1 0.
if.
sp 0 3.
condt{2}.
trivial.
unfold inv.
trivial.
sp 0 3.
condf{2}.
trivial.
unfold inv.
trivial.
save.

equiv Respond : AKE5'_1.Respond ~ AKE_red_5_81'.Respond_C : 
 !bad{1} && !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2}) && ={b,X}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})).
sp 0 1.
if{2}.
if{2}.
rnd>>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 1.
if.
trivial.
unfold inv.
trivial.
trivial.
inline.
sp.
rnd>>.
sp 1 0.
condt{1}.
condf{1}.
sp 1 4.
if.
trivial.
unfold inv.
trivial.
trivial.
rnd{1}>>.
sp 1 0.
condf{1}.
trivial.
save.


equiv Complete : AKE5'_1.Complete ~ AKE_red_5_81'.Complete_C :
 !bad{1} && !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2}) && ={b,X,Y}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
  inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})).
if.
if.
sp 1 1.
if.
trivial.
unfold inv.
trivial.
trivial.
trivial.
if.
inline.
sp 1 3.
condt{2}.
sp 0 1.
if.
sp 0 1.
condt{2}.
trivial.
unfold inv.
trivial.
condf{2}.
trivial.
trivial.
save.

equiv Corrupt : AKE5'_1.Corrupt ~ AKE_red_5_81'.Corrupt_C : !bad{1} &&
 !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2}) && ={b}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})) by auto.


equiv EphKeyReveal : AKE5'_1.EphKeyReveal ~ AKE_red_5_81'.EphKeyReveal_C :
 !bad{1} && !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2}) && ={b,X}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})).
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
trivial.
trivial.
unfold inv.
trivial.
trivial.
sp  1 0.
if.
if.
trivial.
unfold inv.
trivial.
if.
trivial.
unfold inv.
trivial.
trivial.
trivial.
save.

checkproof.
(*
equiv ADV : AKE5'_1.C ~ AKE_red_5_81'.C :
 !bad{1} && !bad{2} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2})
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  positionMsg{1},cantInitA{1},indexInitA{1},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA_C{2},corruptB_C{2},seed_C{2},pkA_C{2},pkB_C{2},
  skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},initMSG_C{2},
  cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
  skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
  incomplete_sessions{2},initA_done{2},cantKG{2},
  initA_done{2})) by auto upto (bad) with
(inv(complete_sessions{1},incomplete_sessions{1}, corruptA{1}, corruptB{1}, 
 seed{1}, pkA{1},pkB{1},skA{1}, skB{1}, cantKG{1}, positionMsg{1},cantInitA{1},
 indexInitA{1},complete_sessions_C{2},incomplete_sessions_C{2}, corruptA_C{2},
 corruptB_C{2},seed_C{2}, pkA_C{2},pkB_C{2}, skA_C{2}, skB_C{2}, cantKG_C{2},
 initAIndex_C{2},initMSG_C{2},cantInitA_C{2},positionMsg_C{2}, pkA{2}, skA{2}, pkB{2}, skB{2}, 
 ephKA_X{2},seedB{2},complete_sessions{2}, incomplete_sessions{2},initA_done{2},
 cantKG{2}, initA_done{2})).
*)


op wingame81
(A : public_key,
 B : public_key,
 X : message,
 alpha : message,
 str : session_string,
 complete_session : complete_session_with_status) =
eqS_oracle(str,(A,B,X,alpha)).

op fresh_sid1g5'_op : (session_id,bool,bool,complete_session_with_status, incomplete_session_with_status) -> bool.

axiom fcop15' :
forall(sid : session_id,
 corruptA : bool,
 corruptB : bool,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid1g5'_op(sid, corruptA,corruptB,complete_session,incomplete_session)
<=>
fresh_sid1g5'(sid, corruptA,corruptB,complete_session,incomplete_session).

equiv MAIN : AKE5'_1.Main ~ AKE_red_5_81'.Main : true ==>
((eqS_oracle(snd(res{1}),fst(res{1})) && fstpart(fst(res{1})) = pkA{1}
&& sndpart(fst(res{1})) = pkB{1} &&
fresh_sid1g5'(fst(res{1}),corruptA{1},corruptB{1},complete_sessions{1},incomplete_sessions{1}))
&& positionMsg{1}[fstmsg(fst(res{1}))] = indexInitA{1}) =>
(wingame81(pkA,pkB,out_noclash(skA,ephKA_X),fst(res),snd(res),complete_sessions)){2}.
inline.
wp.
call upto (bad) with 
(inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},positionMsg{1},
 cantInitA{1},indexInitA{1},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA_C{2},corruptB_C{2},seed_C{2},
 pkA_C{2},pkB_C{2},skA_C{2},skB_C{2},cantKG_C{2},initAIndex_C{2},
 initMSG_C{2},cantInitA_C{2},positionMsg_C{2},pkA{2},skA{2},pkB{2},
 skB{2},ephKA_X{2},seedB{2},complete_sessions{2},
 incomplete_sessions{2},initA_done{2},cantKG{2},initA_done{2})).
trivial.
unfold inv.
trivial.

save.

 