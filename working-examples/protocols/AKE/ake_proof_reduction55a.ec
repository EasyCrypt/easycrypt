(* guess participants of the session that will be attacked *)
include "ake_game5.ec".

cnst maxParts : int.

adversary C () : session_id * session_string  
{
 () -> public_key; (* KG *)
  bool -> message; (* Init *)
 (bool, message) -> message; (* Respond *)
 (bool, message, message) -> unit; (* Complete *)
  bool -> secret_key; (*Corrupt*)
 (bool, message) -> eph_key; (*EphKeyReveal*)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

pred fresh_sid1g5'(sid : session_id,
                corruptA : bool,
                corruptB : bool,
                complete_session : complete_session_with_status,
                incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
!corruptB && corruptA && 
((in_dom((A,X),complete_session) && !session_eph_flag(complete_session[(A,X)]))).


pred fresh_sid11g5'(sid : session_id,
                 corruptA : bool,
                 corruptB : bool,
                 complete_session : complete_session_with_status,
                 incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
corruptB && !corruptA && 
((in_dom((B,Y),complete_session) && !session_eph_flag(complete_session[(B,Y)])) ||
(in_dom((B,Y),incomplete_session) && !snd(incomplete_session[(B,Y)]))).


pred fresh_sid2g5'(corruptA : bool,corruptB : bool) =
!corruptA && !corruptB.


pred fresh_sid3g5'(sid : session_id,
                corruptA, corruptB : bool,
                complete_session : complete_session_with_status,
                incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
corruptA && corruptB &&
(in_dom((A,X),complete_session) && !session_eph_flag(complete_session[(A,X)])) &&
((in_dom((B,Y),complete_session) && !session_eph_flag(complete_session[(B,Y)])) ||
(in_dom((B,Y),incomplete_session) && !snd(incomplete_session[(B,Y)]))).


pred wingame5'
(sid : session_id,
 str : session_string,
 corruptA : bool,
 corruptB : bool,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status,
 A : part, B : part) =
eqS_oracle(str,sid) && fstpart(sid) = A && sndpart(sid) = B && 
(fresh_sid1g5'(sid,corruptA,corruptB,complete_session,incomplete_session) ||
 fresh_sid11g5'(sid,corruptA,corruptB,complete_session,incomplete_session) ||
 fresh_sid2g5'(corruptA,corruptB) ||
 fresh_sid3g5'(sid,corruptA,corruptB,complete_session,incomplete_session)) &&
 completed(sid,complete_session).






game AKE5'_red = {
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corruptA : bool
 var corruptB : bool
 var seed     : (message * part, eph_key) map
 var pkA : public_key
 var pkB : public_key
 var skA : secret_key
 var skB : secret_key
 var cantKG : int

(* what follows is conceptually, part of C*)
 var complete_sessions_C : complete_session_with_status
 var incomplete_sessions_C : incomplete_session_with_status
 var corrupt_C  : (part, bool) map
 var pkey_C     : (part, public_key) map
 var skey_C     : (part, secret_key) map
 var seed_C     : (message * part, eph_key) map
 var fstpart_C  : part
 var sndpart_C  : part
 var indexA_C   : int
 var indexB_C   : int
 var cant_KG_C  : int
 var bad_C        : bool

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key  = {
  var pk : public_key;
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
    pk = pkB;
    corruptB = false;
    cantKG = 2;
   }
  }
  return pk;
 }
 
 fun Init(b : bool) : message = {
  var x : eph_key = gen_eph_key(0);
  var X : message = dummy_message;
  if (b) {
   X = out_noclash(skA, x);
   if (!in_dom((X,pkA), seed)) {
    incomplete_sessions[(pkA,X)] = (pkB,false);
    seed[(X,pkA)] = x;
   } else {X = dummy_message;}
  }
  else {
   X = out_noclash(skB, x);
   if (!in_dom((X,pkB), seed)) {
    incomplete_sessions[(pkB,X)] = (pkA,false);
    seed[(X,pkB)] = x;
   } else {X = dummy_message;}
  }
  return X;
 }
 
fun Respond(b : bool, X: message) : message = {
 var y : eph_key = gen_eph_key(0);  
 var Y : message = dummy_message;
 if (b){
  Y = inp(skA, y);
  if (!in_dom((Y,pkA), seed)) {
   complete_sessions[(pkA,Y)] = mk_session_descr(pkB, X, false, false);
   seed[(Y, pkA)] = y;
  } else {Y = dummy_message;}
 }
 else
 {
  Y = inp(skB, y);
  if (!in_dom((Y,pkB), seed)) {
   complete_sessions[(pkB,Y)] = mk_session_descr(pkA, X, false, false);
   seed[(Y, pkB)] = y;
  } else {Y = dummy_message;}
 }
 return Y;
}

fun Complete(b : bool, X, Y : message) : unit ={
 var eph_flag : bool;
 if (b)
 {
  if (in_dom((pkA,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkA,X)]);
   if (!in_dom((pkA,X), complete_sessions)) {
    complete_sessions[(pkA,X)] = mk_session_descr(pkB,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 } else{
  if (in_dom((pkB,X), incomplete_sessions)) {
   eph_flag = snd(incomplete_sessions[(pkB,X)]);
   if (!in_dom((pkB,X), complete_sessions)) {
    complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,eph_flag,false);
    (*get rid of the session in incomplete*)
   }
  }
 }
}


 fun Corrupt(b : bool) : secret_key = {
  if (b) {corruptA = true;} else {corruptB = true;}
  return (b?skA:skB);
 } 
 
 fun EphKeyReveal(b : bool, X : message) : eph_key = { 
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
    if (in_dom((pkA,X), complete_sessions)) {
     kr_flagA = session_key_reveal_flag(complete_sessions[(pkA,X)]);
     B = session_part(complete_sessions[(pkA,X)]);
     Y = session_msg(complete_sessions[(pkA,X)]);
     s = mk_sid(pkA,pkB,X,Y);
     complete_sessions[(pkA,X)] = mk_session_descr(pkB,Y,true,kr_flagA);
     ekey = seed[(X,pkA)];
    }
      else {(*not in complete*)
     if (in_dom((pkA,X), incomplete_sessions)) {
      B = fst(incomplete_sessions[(pkA,X)]);
      incomplete_sessions[(pkA,X)] = (pkB, true);
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
     complete_sessions[(pkB,X)] = mk_session_descr(pkA,Y,true,kr_flagA);
     ekey = seed[(X,pkB)];
    }
      else {(*not in complete*)
     if (in_dom((pkB,X), incomplete_sessions)) {
      B = fst(incomplete_sessions[(pkB,X)]);
      incomplete_sessions[(pkB,X)] = (pkA, true);
      ekey = seed[(X,pkB)];     
     }
    }
   }
  }
  return ekey;  
 }


(*Adversary implementation of oracles of game 5 in terms of oracles of game 5' and adversary state *)

 fun KG_C() : public_key = {
  var sk : secret_key; 
  var pk : public_key; 
  (* var res : public_key option = None; *)
  if (cant_KG_C = indexA_C) {
   pk = KG();
   if (in_dom(pk, skey_C)){
    bad_C = true;
   } else
   {
    corrupt_C[pk] = false;
    fstpart_C = pk;
    cant_KG_C = cant_KG_C + 1;
   }
  }
  else {
   if (cant_KG_C = indexB_C) {
    pk = KG();    
    if (in_dom(pk, skey_C) || pk = fstpart_C){
     bad_C = true;
    } else
    {
     corrupt_C[pk] = false;
     sndpart_C = pk;
     cant_KG_C = cant_KG_C + 1;
    }
   }
   else {
    sk = gen_secret_key(0);
    pk= gen_public_key(sk);
    if (in_dom(pk,skey_C) 
       || (cant_KG_C > indexA_C  && pk = fstpart_C) 
       || (cant_KG_C > indexB_C  && pk = sndpart_C)){
     bad_C = true;
    } else
    {
     corrupt_C[pk] = false;
     skey_C[pk] = sk;
     cant_KG_C = cant_KG_C + 1;
    }
   }
  }
  return pk;
 } 

 fun Init_C(A:part, B:part) : message = {
  var x : eph_key;
  var a : secret_key;
  var X : message = dummy_message;
  if (cant_KG_C<= indexA_C) {
     x = gen_eph_key(0);
     if (in_dom(A, skey_C)  && (in_dom(B, skey_C)))  {
      a = skey_C[A];
      X = out_noclash(a, x);
      if (!in_dom((X,A), seed_C)) {
       incomplete_sessions_C[(A,X)] = (B,false);
       seed_C[(X,A)] = x;
      } else { X = dummy_message; }
     } else { X = dummy_message; }
    }
    if (indexA_C < cant_KG_C  && cant_KG_C <= indexB_C){
     if (A = fstpart_C){
      if (in_dom(B,skey_C) || B = fstpart_C){
       X = Init(true);
       if (X <> dummy_message){
        incomplete_sessions_C[(A,X)] = (B,false);
       }
      }
     }
     if (A <> fstpart_C){
     x = gen_eph_key(0);
     if (in_dom(A, skey_C)  && (in_dom(B, skey_C) || B = fstpart_C))  {
      a = skey_C[A];
      X = out_noclash(a, x);
      if (!in_dom((X,A), seed_C)) {
       incomplete_sessions_C[(A,X)] = (B,false);
       seed_C[(X,A)] = x;
      } else { X = dummy_message; }
     } else { X = dummy_message; }
    } 
   }
   if (indexB_C < cant_KG_C ){
    if (A = fstpart_C && B = sndpart_C
     ||(A = fstpart_C && B = fstpart_C) 
     ||(A = fstpart_C && B <> sndpart_C && B <> fstpart_C && in_dom(B,skey_C))){
     X = Init(true);
     if (X <> dummy_message){
      incomplete_sessions_C[(A,X)] = (B,false);
     }
    } else {
    if ((A = sndpart_C && B = fstpart_C) 
      ||(A = sndpart_C && B = sndpart_C) 
      ||(A = sndpart_C && B <> fstpart_C && B <> sndpart_C) && in_dom(B,skey_C)){
     X = Init(false);
     if (X <> dummy_message){
      incomplete_sessions_C[(A,X)] = (B,false);
     }
    } else {
     x = gen_eph_key(0);
     if (in_dom(A, skey_C) && (in_dom(B,skey_C) || B = fstpart_C || B = sndpart_C))  {
      a = skey_C[A];
      X = out_noclash(a, x);
      if (!in_dom((X,A), seed_C)) {
       incomplete_sessions_C[(A,X)] = (B,false);
       seed_C[(X,A)] = x;
      } else { X = dummy_message; }
     } else { X = dummy_message; }
    }
   }
  }
  return X;
 }

 fun Respond_C (B:part, A : part, X : message ):message ={
  var y : eph_key;
  var Y : message;
  if (cant_KG_C<= indexA_C) {
   if (in_dom(A, skey_C) && in_dom(B, skey_C)) {
    y = gen_eph_key(0);  
    Y = inp(skey_C[B], y);
    if (!in_dom((Y,B), seed_C)){
     complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
     seed_C[(Y, B)] = y;
    } else { Y = dummy_message;}
   } else { Y = dummy_message;}
  }
  if (indexA_C < cant_KG_C  && cant_KG_C <= indexB_C){
   if (B = fstpart_C){
    if (in_dom(A,skey_C) || A = fstpart_C){
     Y = Respond(true, X);
     if (Y <> dummy_message) 
     {
      complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
     }
    } else { Y = dummy_message;}
   }
   if (B <> fstpart_C){
    if ((in_dom(A,skey_C) || A = fstpart_C)&& in_dom(B, skey_C)){
     y = gen_eph_key(0);  
     Y = inp(skey_C[B], y);
     if (!in_dom((Y,B), seed_C))  {
      complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
      seed_C[(Y, B)] = y;
     } else { Y = dummy_message; }
    }  else { Y = dummy_message; }
   }
  }
  if (indexB_C < cant_KG_C ){
   if (B = fstpart_C && A = sndpart_C
    ||(B = fstpart_C && A = fstpart_C)
    ||(B = fstpart_C && A <> sndpart_C && A <> fstpart_C && in_dom(A,skey_C))){
    Y = Respond(true, X);
    if (Y <> dummy_message) 
    {
     complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
    }
   } else {
   if ((B = sndpart_C && A = fstpart_C)
     ||(B = sndpart_C && A = sndpart_C)
     ||(B = sndpart_C && A <> fstpart_C && A <> sndpart_C && in_dom(A,skey_C))){
    Y = Respond(false, X);
    if (Y <> dummy_message) 
    {
     complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
    }
   } else {
    if ((in_dom(B, skey_C) && (A = fstpart_C || A = sndpart_C || in_dom(A,skey_C)))) {
      y = gen_eph_key(0);  
      Y = inp(skey_C[B], y);
      if (!in_dom((Y,B), seed_C)){
       complete_sessions_C[(B,Y)] = mk_session_descr(A, X, false, false);
       seed_C[(Y, B)] = y;
      } else { Y = dummy_message; }
     } else { Y = dummy_message; }
    }
   }
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
    complete_sessions_C[(A,X)] = mk_session_descr(B,Y,eph_flag,false);
    if ((A = fstpart_C && indexA_C < cant_KG_C) || (A = sndpart_C && indexB_C < cant_KG_C)){
     if (A = fstpart_C && indexA_C < cant_KG_C) {
      Complete(true, X, Y);
     } else {
       Complete(false, X, Y);
     }
    }
    (*get rid of the session in incomplete*)
   }
  }
 }

 
 
 fun Corrupt_C(A : part) : secret_key = {
  var a : secret_key = dummy;
  if (indexA_C < cant_KG_C && A = fstpart_C){
   a = Corrupt(true);
   corrupt_C[A] = true;
  }
  else{ 
   if (indexB_C < cant_KG_C && A = sndpart_C){
    a = Corrupt(false);
    corrupt_C[A] = true;
   }
   else{
    if (in_dom(A,skey_C))
    {
     corrupt_C[A] = true;
     a = skey_C[A];
    }
   }
  }
  return a;
 } 
 
 fun EphKeyReveal_C(A : part, X : message) : eph_key = { 
  var kr_flagA : bool = false;
  var corr_flagA : bool = false;
  var test_flagA : bool = false;
  var B : part;
  var Y : message;
  var s : session_id;
  var ekey : eph_key = dummy_eph_key;
  corr_flagA = corrupt_C[A];
  if ((A <> fstpart_C || cant_KG_C <= indexA_C) && (A <> sndpart_C || cant_KG_C <= indexB_C))  {
   if (!corr_flagA) (* not corrupted*)
   {
    if (in_dom((A,X), complete_sessions_C)) {
     kr_flagA = session_key_reveal_flag(complete_sessions_C[(A,X)]);
     B = session_part(complete_sessions_C[(A,X)]);
     Y = session_msg(complete_sessions_C[(A,X)]);
     s = mk_sid(A,B,X,Y);
     complete_sessions_C[(A,X)] = mk_session_descr(B,Y,true,kr_flagA);
     ekey = seed_C[(X,A)];
    }
      else {(*not in complete*)
     if (in_dom((A,X), incomplete_sessions_C)) {
      B = fst(incomplete_sessions_C[(A,X)]);
      incomplete_sessions_C[(A,X)] = (B, true);
      ekey = seed_C[(X,A)];     
     }
    }
   }
  } else
  {
   if (!corr_flagA) (* not corrupted*)
   {
    if (A = fstpart_C && indexA_C < cant_KG_C){
     ekey = EphKeyReveal(true, X); 
    } else 
    {
     ekey = EphKeyReveal(false, X); 
    }
    if (in_dom((A,X), complete_sessions_C)) {
     kr_flagA = session_key_reveal_flag(complete_sessions_C[(A,X)]);
     B = session_part(complete_sessions_C[(A,X)]);
     Y = session_msg(complete_sessions_C[(A,X)]);
     s = mk_sid(A,B,X,Y);
     complete_sessions_C[(A,X)] = mk_session_descr(B,Y,true,kr_flagA);
    } else {
     if (in_dom((A,X), incomplete_sessions_C)) {
      B = fst(incomplete_sessions_C[(A,X)]);
      incomplete_sessions_C[(A,X)] = (B, true);     
     }
    }
   }
  }
  return ekey;  
 }
 
 abs B = B { KG_C, Init_C, Respond_C, Complete_C, Corrupt_C, EphKeyReveal_C, eqS, same_session_string }
 
 fun C() : session_id * session_string = {
  var sidss : session_id * session_string;
  var aux : int;
  cant_KG_C = 0;
  bad_C = false;
  complete_sessions_C = empty_map;
  incomplete_sessions_C = empty_map;
  corrupt_C = empty_map;
  pkey_C = empty_map;
  skey_C = empty_map;
  seed_C = empty_map;
  indexA_C = [1..maxParts];
  indexB_C = [1..maxParts];
  if (indexB_C = indexA_C) { bad_C = true;}
   (* make sure indexA is smaller to simplify invariants *)
  if (indexB_C < indexA_C) {
   aux = indexA_C;
   indexA_C = indexB_C;
   indexB_C = aux;
  }
  (* here we know for sure that indexA_C < indexB_C *)
  sidss = B();
  return sidss;
 }

 fun Main () : session_id * session_string = {
  var sidss : session_id * session_string;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corruptA = false;
  corruptB = false;
  skA = dummy;
  skB = dummy;
  pkA = gen_public_key(skA);
  pkB =gen_public_key(skA);
  cantKG = 0;
  seed  = empty_map;
  sidss = C();
  return sidss;
 }
}.

