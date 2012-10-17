include "ake_proof_reduction55a.ec".


(* Winning condition for Game 5'  *)
(* op wingame5' *)
(* (sid : session_id, *)
(*  str : session_string, *)
(*  corrupt : (part, bool) map, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status, *)
(*  A : part, B : part) = *)
(* eqS_oracle(str,sid) && fstpart(sid) = A && sndpart(sid) = B &&  *)
(* (fresh_sid1_op(sid,corrupt,complete_session,incomplete_session) || *)
(*  fresh_sid11_op(sid,corrupt,complete_session,incomplete_session) || *)
(*  fresh_sid2_op(sid,corrupt) || *)
(*  fresh_sid3_op(sid,corrupt,complete_session,incomplete_session) *)
(* ). *)

(* Adversary *)
(* adversary C () : session_id * session_string  *)
(* {*)
(*  () -> public_key;  KG *)
(*   bool -> message;  Init *)
(*  (bool, message) -> message;  Respond *)
(*  (bool, message, message) -> unit;  Complete *)
(*   bool -> secret_key; Corrupt*)
(*  (bool, message) -> eph_key; EphKeyReveal*)
(* (session_string,session_id) -> bool;  eqS *)
(*  (session_id, session_id) -> bool  same_session_string *)
(*}.*)
(*these are defined in ake_proof_reduction55'.ec*)

game AKE5' = {
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

 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 fun KG() : public_key  = {
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
  if (cantKG = 2){
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
  }
  return X;
 }
 
fun Respond(b : bool, X: message) : message = {
 var y : eph_key = gen_eph_key(0);  
 var Y : message = dummy_message;
 if (cantKG = 2){
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
   }
  }
  return (res);
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

 abs C = C {KG, Init, Respond, Complete, Corrupt, EphKeyReveal, eqS, same_session_string }

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

(* op wingame5'_op : (session_id,session_string,bool,bool,complete_session_with_status, incomplete_session_with_status, part, part) -> bool. *)

(* op fresh_sid1g5'_op : (session_id,bool,bool,complete_session_with_status, incomplete_session_with_status) -> bool. *)

(* axiom wgop5' :  *)
(* forall(sid : session_id, *)
(*  str : session_string, *)
(*  corruptA : bool, *)
(*  corruptB : bool, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status, *)
(*  A : part, B : part),  *)
(* wingame5'(sid, str,corruptA,corruptB,complete_session,incomplete_session,A,B) *)
(* <=> *)
(* wingame5'_op(sid, str,corruptA,corruptB,complete_session,incomplete_session,A,B).  *)

(* axiom fcop15' :  *)
(* forall(sid : session_id, *)
(*  corruptA : bool, *)
(*  corruptB : bool, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status),  *)
(* fresh_sid1g5'_op(sid, corruptA,corruptB,complete_session,incomplete_session) *)
(* <=> *)
(* fresh_sid1g5'(sid, corruptA,corruptB,complete_session,incomplete_session).  *)


(* op fresh_sid11g5'_op : (session_id,bool,bool,complete_session_with_status, incomplete_session_with_status) -> bool. *)

(* axiom fcop115' :  *)
(* forall(sid : session_id, *)
(*  corruptA : bool, *)
(*  corruptB : bool, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status),  *)
(* fresh_sid11g5'_op(sid, corruptA,corruptB,complete_session,incomplete_session) *)
(* <=> *)
(* fresh_sid11g5'(sid, corruptA,corruptB,complete_session,incomplete_session).  *)

(* op fresh_sid2g5'_op : (bool, bool) -> bool. *)

(* axiom fcop2g5' :  *)
(*  forall(corruptA : bool, *)
(*  corruptB : bool), fresh_sid2g5'(corruptA,corruptB) <=> fresh_sid2g5'_op(corruptA,corruptB). *)

(* op fresh_sid3g5'_op : (session_id,bool,bool,complete_session_with_status, incomplete_session_with_status) -> bool. *)

(* axiom fcop3g5' : *)
(* forall(sid : session_id, *)
(*  corruptA, corruptB : bool, *)
(*  complete_session : complete_session_with_status, *)
(*  incomplete_session : incomplete_session_with_status), *)
(* fresh_sid3g5'_op(sid, corruptA,corruptB,complete_session,incomplete_session) *)
(* <=> *)
(* fresh_sid3g5'(sid, corruptA,corruptB,complete_session,incomplete_session). *)


(* op completed_op : (session_id, complete_session_with_status) -> bool. *)
 
(* axiom compop :  *)
(* forall(sid : session_id, *)
(*  complete_session : complete_session_with_status), *)
(* completed(sid, complete_session) <=> *)
(* completed_op(sid, complete_session). *)

(* equiv Csplit : AKE5'.Main ~ AKE5'.Main : *)
(* (={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG}) by *)
(* auto (={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG}). *)


(* claim C : *)
(* AKE5'.Main[wingame5'_op(fst(res), snd(res),corruptA,corruptB,complete_sessions,incomplete_sessions,pkA,pkB)] = *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* (fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions) || *)
(* fresh_sid11g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions) || *)
(* fresh_sid2g5'_op(corruptA,corruptB) || *)
(* fresh_sid3g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)  *)
(* ))] using C. *)

(* claim C2 : *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* (fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions) || *)
(* fresh_sid11g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions) || *)
(* fresh_sid2g5'_op(corruptA,corruptB) || *)
(* fresh_sid3g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)  *)
(* ))] <=  *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid11g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid2g5'_op(corruptA,corruptB))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid3g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))]  compute. *)
(* checkproof. *)
(* claim C3 : *)
(* AKE5'.Main[wingame5'_op(fst(res), snd(res),corruptA,corruptB,complete_sessions,incomplete_sessions,pkA,pkB)] <=  *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions) && completed_op(fst(res),complete_sessions))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid11g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)&& completed_op(fst(res),complete_sessions))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid2g5'_op(corruptA,corruptB)&& completed_op(fst(res),complete_sessions))] + *)
(* AKE5'.Main[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && *)
(* fresh_sid3g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)&& completed_op(fst(res),complete_sessions))] *)
(* compute. *)
(* checkproof. *)
(* cnst maxInitA : int. *)

(* game AKE5'_1 = AKE5'  *)
(* var cantInitA : int *)
(* var indexInitA : int *)
(* var positionMsg : (message, int) map *)
(* var bad : bool *)
(* where  Init = { *)
(*  var x : eph_key = gen_eph_key(0); *)
(*  var X : message = dummy_message; *)
(*  if (cantKG = 2){ *)
(*   if (b) { *)
(*    X = out_noclash(skA, x); *)
(*    if (!in_dom((X,pkA), seed)) { *)
(*     incomplete_sessions[(pkA,X)] = (pkB,false); *)
(*     seed[(X,pkA)] = x; *)
(*     positionMsg[X] = cantInitA;  *)
(*     cantInitA = cantInitA + 1; *)
(*    } else {X = dummy_message;} *)
(*   } *)
(*   else { *)
(*    X = out_noclash(skB, x); *)
(*    if (!in_dom((X,pkB), seed)) { *)
(*     incomplete_sessions[(pkB,X)] = (pkA,false); *)
(*     seed[(X,pkB)] = x; *)
(*    } else {X = dummy_message;} *)
(*   } *)
(*  } *)
(*  return X; *)
(* }  *)
(* and KG = { *)
(*   var pk : public_key = gen_public_key(dummy); *)
(*   if (cantKG = 0) { *)
(*    skA = gen_secret_key(0); *)
(*    pkA = gen_public_key(skA); *)
(*    pk = pkA; *)
(*    corruptA = false; *)
(*    cantKG = 1;   *)
(*   } else { *)
(*    if (cantKG = 1){ *)
(*     skB = gen_secret_key(0); *)
(*     pkB = gen_public_key(skB); *)
(*     if (pkA = pkB) {bad = true;} *)
(*     pk = pkB; *)
(*     corruptB = false; *)
(*     cantKG = 2; *)
(*    }  *)
(*   }  *)
(*   return pk; *)
(*  } *)

(* and Main = { *)
(*  var sidss : session_id * session_string; *)
(*  complete_sessions = empty_map; *)
(*  incomplete_sessions = empty_map; *)
(*  corruptA = false; *)
(*  corruptB = false; *)
(*  bad = false; *)
(*  skA = dummy; *)
(*  skB = dummy; *)
(*  pkA = gen_public_key(skA); *)
(*  pkB = gen_public_key(skA); *)
(*  cantKG = 0; *)
(*  positionMsg = empty_map; *)
(*  seed  = empty_map; *)
(*  cantInitA = 0; *)
(*  sidss = C(); *)
(*  indexInitA = [0..maxInitA]; *)
(*  return sidss; *)
(* }. *)


(* checkproof. *)

(* equiv AKE5'_5'_1 : AKE5'.Main ~ AKE5'_1.Main :  *)
(* true ==> *)
(* (eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&  *)
(* sndpart(fst(res)) = pkB && completed_op(fst(res),complete_sessions) && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)){1} = *)
(* (eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&  *)
(* sndpart(fst(res)) = pkB && completed_op(fst(res),complete_sessions) && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)){2}. *)
(* rnd{2}. *)
(* call *)
(* (={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG}). *)
(* wp. *)
(* trivial. *)
(* save. *)


(* claim C2 : *)
(* AKE5'.Main *)
(* [(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&  *)
(* sndpart(fst(res)) = pkB && completed_op(fst(res),complete_sessions) && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))] = *)
(* AKE5'_1.Main *)
(* [(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&  *)
(* sndpart(fst(res)) = pkB &&  completed_op(fst(res),complete_sessions) && *)
(* fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))]  *)
(* using AKE5'_5'_1. *)
(* checkproof. *)


(*equiv inferred_AKE5'_1_KG_AKE5'_1_KG_5 : AKE5'_1.KG ~ AKE5'_1.KG :
 !bad{1} &&
 !bad{2} &&
(forall (X : message),
 in_dom (X,positionMsg{1}) =>
 0 <= positionMsg{1}[X] && positionMsg{1}[X] <= cantInitA{1}) &&
(forall (X_0 : message),
 in_dom ((pkA{1},X_0),incomplete_sessions{1}) =>
 in_dom (X_0,positionMsg{1})) &&
(cantKG{1} < 2 => incomplete_sessions{1} = empty_map) &&
={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG} &&
0 <= cantInitA{1} && pkA{1} <> pkB{1}
==>
(bad{1} <=> bad{2}) && (!bad{1} =>
 ={res} && (forall (X : message),
  in_dom (X,positionMsg{1}) =>
  0 <= positionMsg{1}[X] &&
  positionMsg{1}[X] <= cantInitA{1}) &&
 (forall (X_0 : message),
  in_dom ((pkA{1},X_0),incomplete_sessions{1}) =>
  in_dom (X_0,positionMsg{1})) &&
 (cantKG{1} < 2 => incomplete_sessions{1} = empty_map) &&
 ={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG} &&
 0 <= cantInitA{1}).
sp 1 1.
if.
rnd >>.
trivial.
*)

(*
equiv C2_dom : AKE5'_1.Main ~ AKE5'_1.Main : 
true ==> 2 <= cantKG{1} && forall (X : message), (in_dom(X,positionMsg){1} => 
           0 <= positionMsg[X]{1} && positionMsg[X]{1} <= cantInitA{1}).
rnd.
call upto (bad) with
((forall (X : message), (in_dom(X,positionMsg){1} => 
           0 <= positionMsg[X]{1} && positionMsg[X]{1} <= cantInitA{1})) &&
((forall (X : message), (in_dom((pkA{1},X),incomplete_sessions{1}) =>
                        in_dom(X,positionMsg{1}))) ) &&
(cantKG{1} = 2 => pkA{1} <> pkB{1}) && (cantKG{1} = 0 || cantKG{1} = 1 || cantKG{1} = 2)
&& (cantKG{1}< 2 => incomplete_sessions{1} = empty_map) && 
={complete_sessions,incomplete_sessions,corruptA,corruptB,seed,pkA,pkB,skA,skB,cantKG,bad} && 
0 <= cantInitA{1} ).
sp.
trivial.
save.

claim c3 : 
AKE5'_1.Main
[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && 
sndpart(fst(res)) = pkB &&  completed_op(fst(res),complete_sessions) &&
fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)) 
&& cantInitA <= maxInitA] =
AKE5'_1.Main
[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && 
sndpart(fst(res)) = pkB &&  completed_op(fst(res),complete_sessions) &&
fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)) 
&& cantInitA <= maxInitA && ] 

using AKE5'_5'_1.


claim C3 :
AKE5'_1.Main
[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&
sndpart(fst(res)) = pkB && completed_op(fst(res),complete_sessions) &&
fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions))]
* 1%r / maxInitA%r <=
AKE5'_1.Main
[(eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA &&
sndpart(fst(res)) = pkB &&  completed_op(fst(res),complete_sessions) &&
fresh_sid1g5'_op(fst(res),corruptA,corruptB,complete_sessions,incomplete_sessions)) &&
positionMsg[fstmsg(fst(res))] = indexInitA] compute.
*)