include "ake_game5'.ec".

adversary D () : (message * message * session_string)
{
 bool -> (message * eph_key) option; (* Init: start either with A or B *)
 (bool, message) -> (message * eph_key) option; (* Respond *)
 (session_string,session_id) -> bool; (* eqS *)
 (session_id, session_id) -> bool (* same_session_string *)
}.

cnst maxInit : int.


game AKE_red_5_91' = {
 var pkA     : public_key 
 var skA     : secret_key 
 var pkB     : public_key 
 var skB     : secret_key 
 var seedA : (message, eph_key) map
 var seedB : (message, eph_key) map
 var cantKG : int
 (*Context State *)
 var complete_sessions_C : complete_session_with_status
 var incomplete_sessions_C : incomplete_session_with_status
 var seed_C     : (message * part, eph_key) map
 var pkA_C : public_key
 var pkB_C : public_key
 var cantKG_C : int
 var bad : bool
 var corruptA : bool
 var corruptB : bool
 
 (* Oracles of game 9 *)
 fun same_session_string(sid1 : session_id, sid2 : session_id) : bool = {
  return (same_session_string_oracle(sid1,sid2));
 }
 
 fun eqS(str : session_string, sid : session_id) : bool = {
  return (eqS_oracle(str,sid));
 }
 
 fun KG() : public_key = {
  var pk : public_key = gen_public_key(dummy);
  if (cantKG = 0){
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   pk = pkA;
   cantKG = 1;
  } else{
   if (cantKG = 1){
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    cantKG = 2;
    pk = pkB;
   }
  }
  return pk;
 }

 fun Init(b : bool) : (message * eph_key) option = {
  var X : message;
  var x : eph_key;
  var res : (message * eph_key) option;
  res = None;
  if (cantKG = 2){
   if (b) {
    x = gen_eph_key(0);
    X = out_noclash(skA,x);
    res = Some((X,x));
    if (!in_dom(X,seedA)) {seedA[X] = x; } else {res = None;}
   } else
   { 
    x = gen_eph_key(0);
    X = out_noclash(skB,x);
    res = Some((X,x));
    if (!in_dom(X,seedB)) {seedB[X] = x; } else {res = None;}
   }
  }
  return res;
 }
 
 
 fun Respond(b : bool, X : message) : (message * eph_key) option = {
  var res : (message * eph_key) option;
  var Y : message;
  var y : eph_key;
  res = None;
  if (cantKG = 2){  
   if (!b) {
    y = gen_eph_key(0);
    Y = inp(skB,y);
    res = Some ((Y,y));
    if (!in_dom(Y,seedB)) {seedB[Y] = y;} else {res = None;}
   } else
   {
    y = gen_eph_key(0);
    Y = inp(skA,y);
    res = Some((Y,y));
    if (!in_dom(Y,seedA)) {seedA[Y] = y;} else {res = None;}
   }
  }
  return res;
 }

 (* Context implementations *)
 fun KG_C() : public_key ={
  var pk : public_key = gen_public_key(dummy);
  if (cantKG_C = 0) {
   pkA_C = KG();
   cantKG_C = 1;
   pk = pkA_C;
  } else{
   if (cantKG_C = 1) {
    pkB_C = KG();
    if (pkA_C = pkB_C) {bad = true;}
    cantKG_C = 2;
    pk = pkB_C;
   }
  }
  return pk;
 }
 
 fun Init_C(b : bool) : message = {
  var msg : message = dummy_message;
  var eph : eph_key;
  var part : public_key = b ? pkA_C : pkB_C;
  var opart : public_key = b ? pkB_C : pkA_C;
  var init : (message*eph_key) option;
  if (cantKG_C = 2){
   init = Init(b);
   if (init <> None){
    (msg,eph) = proj(init);
    if (!in_dom((msg,part),seed_C)){
      seed_C[(msg,part)] = eph;
      incomplete_sessions_C[(part,msg)] = (opart,false);
     } else {msg = dummy_message;}
   }
  }
  return msg;
 }
 
 fun Respond_C(b : bool, X: message) : message = {
  var msg : message = dummy_message;
  var eph : eph_key;
  var resp : (message*eph_key) option;
  var part : public_key = b ? pkA_C : pkB_C;
  var opart : public_key = b ? pkB_C : pkA_C;
  if (cantKG_C = 2){
   resp = Respond(b,X);
   if (resp <> None){
    (msg,eph) = proj(resp);
    if (!in_dom((msg,part),seed_C)){
     seed_C[(msg,part)] = eph;
     complete_sessions_C[(part,msg)] = (opart, X, false, false);
    } else {msg = dummy_message;}
   }
  }
  return msg;
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
   if (in_dom((pkB,X), incomplete_sessions_C)) {
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
   if (cantKG_C = 1){
    corruptA = true;
    res = gen_secret_key(0);
   }
  } 
  else {
   if (cantKG_C = 2){
    res = skB;
    corruptB = true;
    res = gen_secret_key(0);
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
   corr_flagA = corruptA;
   if (!corr_flagA) (* not corrupted*)
   {
    if (in_dom((pkA_C,X), complete_sessions_C)) {
     kr_flagA = session_key_reveal_flag(complete_sessions_C[(pkA_C,X)]);
     B = session_part(complete_sessions_C[(pkA_C,X)]);
     Y = session_msg(complete_sessions_C[(pkA_C,X)]);
     s = mk_sid(pkA_C,pkB_C,X,Y);
     complete_sessions_C[(pkA_C,X)] = mk_session_descr(pkB_C,Y,true,kr_flagA);
     ekey = seed_C[(X,pkA_C)];
    }
      else {(*not in complete*)
     if (in_dom((pkA_C,X), incomplete_sessions_C)) {
      B = fst(incomplete_sessions_C[(pkA_C,X)]);
      incomplete_sessions_C[(pkA_C,X)] = (pkB_C, true);
      ekey = seed_C[(X,pkA_C)];     
     }
    }
   }
  }
    else
  {
   corr_flagA = corruptB;
   if (!corr_flagA) (* not corrupted*)
   {
    if (in_dom((pkB_C,X), complete_sessions_C)) {
     kr_flagA = session_key_reveal_flag(complete_sessions_C[(pkB_C,X)]);
     B = session_part(complete_sessions_C[(pkB_C,X)]);
     Y = session_msg(complete_sessions_C[(pkB_C,X)]);
     s = mk_sid(pkB_C,pkA_C,X,Y);
     complete_sessions_C[(pkB_C,X)] = mk_session_descr(pkA_C,Y,true,kr_flagA);
     ekey = seed_C[(X,pkB_C)];
    }
      else {(*not in complete*)
     if (in_dom((pkB_C,X), incomplete_sessions_C)) {
      B = fst(incomplete_sessions_C[(pkB_C,X)]);
      incomplete_sessions_C[(pkB_C,X)] = (pkA_C, true);
      ekey = seed_C[(X,pkB_C)];     
     }
    }
   }
  }
  return ekey;  
 }

 

 abs C = C {KG_C, Init_C, Respond_C, Complete_C, Corrupt_C, EphKeyReveal_C, eqS, same_session_string }
 
 fun D() : message * message * session_string ={
  var sidss : session_id * session_string;
  bad = false;
  complete_sessions_C = empty_map;
  incomplete_sessions_C = empty_map;
  corruptA = false;
  corruptB = false;
  seed_C = empty_map;
  pkA_C = gen_public_key(dummy);
  pkB_C = gen_public_key(dummy);
  cantKG_C = 0;
  sidss = C();
  return (fstmsg(fst(sidss)),sndmsg(fst(sidss)), snd(sidss));
 }


 fun Main () : message * message * session_string = {
  var ek : eph_key;
  var alpha : message; 
  var beta : message; 
  var str : session_string;
  cantKG = 0;
  seedA = empty_map;
  seedB = empty_map;
  skA = dummy;
  skB = dummy;
  pkA = gen_public_key(skA);
  pkB = gen_public_key(skB);
  (alpha,beta,str) = D();
  return (alpha,beta,str);
 }

}.


game AKE5'_2 = AKE5'
var bad : bool
where KG = {
  var pk : public_key = gen_public_key(dummy);
  if (cantKG = 0) {
   skA = gen_secret_key(0);
   pkA = gen_public_key(skA);
   pk = pkA;
   cantKG = 1;
  } else {
   if (cantKG = 1){
    skB = gen_secret_key(0);
    pkB = gen_public_key(skB);
    if (pkA = pkB) {bad = true;}
    pk = pkB;
    cantKG = 2;
   }
  }
  return pk;
 }
and Main = {
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
  bad = false;
  seed  = empty_map;
  sidss = C();
  return sidss;
 }.


  pred inv( complete_sessions1 : complete_session_with_status,
  incomplete_sessions1 : incomplete_session_with_status,
  corruptA1 : bool,
  corruptB1 : bool,
  seed1     : (message * part, eph_key) map,
  pkA1 : public_key,
  pkB1 : public_key,
  skA1 : secret_key,
  skB1 : secret_key,
  cantKG1 : int,
  pkA2    : public_key,
  skA2     : secret_key, 
  pkB2    : public_key,
  skB2     : secret_key, 
  seedA2 : (message, eph_key) map,
  seedB2 : (message, eph_key) map,
  cantKG2 : int,
  complete_sessions_C : complete_session_with_status,
  incomplete_sessions_C : incomplete_session_with_status,
  corruptA_C : bool,
  corruptB_C : bool,
  seed_C     : (message * part, eph_key) map,
  pkA_C : public_key,
  pkB_C : public_key,
  cantKG_C : int) =
pkA1 = pkA_C &&
pkB1 = pkB_C &&
pkA2 = pkA_C &&
pkB2 = pkB_C &&
skA1 = skA2 &&
skB1 = skB2 &&
cantKG1 = cantKG2 &&
cantKG1 = cantKG_C &&
corruptA1 = corruptA_C &&
corruptB1 = corruptB_C &&
complete_sessions_C = complete_sessions1 &&
incomplete_sessions_C = incomplete_sessions1 &&
seed_C = seed1 &&
(forall (X : message), (in_dom((X,pkA_C),seed_C) <=> in_dom(X,seedA2)) &&
                       (in_dom((X,pkA_C),seed_C) => seed_C[(X,pkA_C)] = seedA2[X])) &&
(forall (X : message), (in_dom((X,pkB_C),seed_C) <=> in_dom(X,seedB2)) &&
                       (in_dom((X,pkB_C),seed_C) => seed_C[(X,pkB_C)] = seedB2[X])) &&
((cantKG1 = 0 || cantKG1 = 1)=> seed_C = empty_map) &&
(cantKG1 = 2 => pkA_C <> pkB_C).


checkproof.
equiv KG :  AKE5'_2.KG ~ AKE_red_5_91'.KG_C :
!(bad{1} || corruptA{1} || corruptB{1}) &&
!(bad{2} || corruptA{2} || corruptB{2}) &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},
  cantKG_C{2})).
sp 1 1.
if.
inline.
sp 0 1.
condt{2}.
rnd>>.
trivial.
unfold inv.
trivial.
if.
inline.
sp 0 1.
condf{2}.
condt{2}.
rnd>>.
sp 1 1.
trivial.
unfold inv;trivial.
trivial.
save.

equiv Init :  AKE5'_2.Init ~ AKE_red_5_91'.Init_C :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={b} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
 corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
 pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
 complete_sessions_C{2},incomplete_sessions_C{2},corruptA{2},
 corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},
  cantKG_C{2})).
case{2}: b.
sp 0 3.
if{2}.
inline.
sp 0 2.
condt{2}.
condt{2}.
rnd>>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 4.
if{2}.
trivial.
trivial.
trivial.
sp 0 3.
if{2}.
inline.
sp 0 2.
if{2}.
condf{2}.
rnd >>.
trivial.
trivial.
trivial.
save.

equiv Respond :  AKE5'_2.Respond ~ AKE_red_5_91'.Respond_C :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={b,X} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
 corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},
 skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
 complete_sessions_C{2},incomplete_sessions_C{2},corruptA{2},
 corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
  complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},
  cantKG_C{2})).
case{2}: b.
sp 0 3.
if{2}.
inline.
sp 0 3.
condt{2}.
condf{2}.
rnd>>.
sp 1 0.
condt{1}.
condt{1}.
sp 1 2.
if.
sp 2 2.
condt{2}.
sp 0 1.
condt{2}.
trivial.
trivial.
trivial.
sp 0 3.
if{2};[|trivial].
inline.
sp 0 3.
condt{2}.
condt{2}.
rnd >>.
trivial.
save.

equiv Complete :  AKE5'_2.Complete ~ AKE_red_5_91'.Complete_C :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={b,X,Y} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})).
trivial.
save.

equiv Corrupt :  AKE5'_2.Corrupt ~ AKE_red_5_91'.Corrupt_C :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={b} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})).
derandomize.
wp.
trivial.
save.

equiv EphKR :  AKE5'_2.EphKeyReveal ~ AKE_red_5_91'.EphKeyReveal_C :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={b,X} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})).
  trivial.
save.

equiv same_session_string : AKE5'_2.same_session_string ~ AKE_red_5_91'.same_session_string :
    !(bad{1} || corruptA{1} || corruptB{1}) &&
     !(bad{2} || corruptA{2} || corruptB{2}) &&
      ={sid1,sid2} &&
       inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
           seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
           skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
           incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
           pkB_C{2},cantKG_C{2})
    ==>
    (bad{1} || corruptA{1} || corruptB{1} <=>
      bad{2} || corruptA{2} || corruptB{2}) &&
     (!(bad{1} || corruptA{1} || corruptB{1}) =>
     ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
                   corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
                   pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
                   complete_sessions_C{2},incomplete_sessions_C{2},corruptA{2},
                   corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2})).
trivial.
save.

    
equiv eqS : AKE5'_2.eqS ~ AKE_red_5_91'.eqS :
 !(bad{1} || corruptA{1} || corruptB{1}) &&
 !(bad{2} || corruptA{2} || corruptB{2}) &&
={str,sid} &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
 seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},
 skB{2},seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},
 incomplete_sessions_C{2},corruptA{2},corruptB{2},seed_C{2},pkA_C{2},
 pkB_C{2},cantKG_C{2})
==>
(bad{1} || corruptA{1} || corruptB{1} <=>
 bad{2} || corruptA{2} || corruptB{2}) &&
(!(bad{1} || corruptA{1} || corruptB{1}) =>
 ={res} && inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},
  corruptB{1},seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},
  pkA{2},skA{2},pkB{2},skB{2},seedA{2},seedB{2},cantKG{2},
  complete_sessions_C{2},incomplete_sessions_C{2},corruptA{2},
  corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2})).
trivial.
save.
checkproof.
equiv ADV : AKE5'_2.C ~ AKE_red_5_91'.C : !(bad{1} || corruptA{1} || corruptB{1}) &&
!(bad{2} || corruptA{2} || corruptB{2}) &&
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
  seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},skB{2}, 
  seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2}) ==>
((bad{1} || corruptA{1} || corruptB{1})<=>(bad{2} || corruptA{2} || corruptB{2}))
&& (!(bad{1} || corruptA{1} || corruptB{1}) =>
inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
  seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},skB{2}, 
  seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2}) && ={res}) by auto upto 
(bad || corruptA || corruptB) with
(inv(complete_sessions{1},incomplete_sessions{1},corruptA{1},corruptB{1},
  seed{1},pkA{1},pkB{1},skA{1},skB{1},cantKG{1},pkA{2},skA{2},pkB{2},skB{2}, 
  seedA{2},seedB{2},cantKG{2},complete_sessions_C{2},incomplete_sessions_C{2},
  corruptA{2},corruptB{2},seed_C{2},pkA_C{2},pkB_C{2},cantKG_C{2})).


op wingame91 :
(public_key,public_key,session_string, message, message) -> bool.

axiom wg91def : forall (pkA     : public_key, 
 pkB     : public_key, 
 str : session_string,
 alpha : message,
 beta : message), wingame91(pkA,pkB,str,alpha,beta) <=> eqS_oracle(str,(pkA,pkB,alpha,beta)).


op fresh_sid2g5'_op : (bool, bool) -> bool.

axiom fcop2g5' :
 forall(corruptA : bool,
 corruptB : bool), (!corruptA && !corruptB) <=> fresh_sid2g5'_op(corruptA,corruptB).

equiv Main : AKE5'_2.Main ~ AKE_red_5_91'.Main : 
true ==> !bad{1} => 
((eqS_oracle(snd(res),fst(res)) && fstpart(fst(res)) = pkA && sndpart(fst(res)) = pkB && 
( fresh_sid2g5'_op(corruptA,corruptB))){1} => 
(let alpha,beta,str = res{2} in
 (eqS_oracle(str,(pkA{2},pkB{2},alpha,beta)) || eqS_oracle(str,(pkA{2},pkB{2},alpha,beta))) && !corruptA{2} && !corruptB{2})).
inline.
wp.
call using ADV.
trivial.
save.

