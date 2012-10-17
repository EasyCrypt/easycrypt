include "ake_game11.ec".



(* We define an instantiation of game10, with concrete implementations 
   for findelse_g and findelse_h *)

game AKE12 = {
 var b : bool
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (session_string, session_key) map
 var LHT       : (session_string, session_key) map
 var seed     : (part * message, eph_key) map
 var tested_session : (session_id, session_key) map
 var msg_seeds : (secret_key * eph_key, msg_seed) map
 var keys_revealed : (session_id, bool) map
 var sid_queries : session_id list
 var sess : int
 var part : int
 var argLHT : session_string list
 var argLH : session_string list
 var G : (session_id,session_key) map

 fun findelse_g_impl(m : (session_id, session_key) map, str : session_string) : session_id option =
 {
  var sid' : session_id = dummy_session_id;
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

 fun findelse_sid_impl(m : (session_id, session_key) map, sid : session_id) : session_id option =
 {
  var sid' : session_id = dummy_session_id;
  var lG : session_id list = dom(m);
  var res : session_id option  = None;
  var t : bool = false;
   while (lG <> [] && !t){
   sid' = hd(lG);
   lG = tl(lG);
   t = same_session_string_abs(sid,sid',skey,seed);
   if (t) {
    res = Some(sid');
   }
  }
  return res;
 }


 fun findelse_h_impl(m : (session_string, session_key) map, sid : session_id) : session_string option =
 {
  var str : session_string = dummy_session_string;
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

 fun compute_key(s : session_id) : session_key = {
  var ssskey : session_key;
  var sstr : session_string option;
  var sid' : session_id option;
  sstr = findelse_h_impl(LH,s);
  sid' = findelse_sid_impl(G,s);
  if (sstr <> None) {
   ssskey = LH[proj(sstr)];
  } else
  {
   if (sid' <> None) {
     ssskey = G[proj(sid')];
    } else {
      ssskey = gen_session_key();
      G[s] = ssskey;
     }
    }
  return ssskey;
 }
fun iH(lam : session_string) : session_key = {
  var sid : session_id option;
  var ssskey : session_key;
  if (in_dom(lam, LH)) {
   ssskey = LH[lam];
  } else {
   sid = findelse_g_impl(G,lam);
   if (sid <> None) {
    ssskey = G[proj(sid)];
   } else {
    ssskey = gen_session_key();
   }
   LH[lam] = ssskey;
  }
 return ssskey;
}

fun KG = AKE11.KG
fun Init = AKE11.Init
fun Respond = AKE11.Respond
fun Complete = AKE11.Complete
fun Corrupt = AKE11.Corrupt
fun KeyReveal = AKE11.KeyReveal
fun Test = AKE11.Test
fun EphKeyReveal = AKE11.EphKeyReveal
fun H = AKE11.H
fun MsgSeedReveal = AKE11.MsgSeedReveal
abs A = A { KG, Init, Respond, Complete, Corrupt, KeyReveal, H, Test, EphKeyReveal, MsgSeedReveal }

fun Main = AKE11.Main
}.


(*TODO: Proof that the implementations satisfy the given axioms *)