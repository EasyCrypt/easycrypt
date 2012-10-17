include "ake_game12.ec".


op eqS_oracle : 
(session_string,  session_id) -> bool.

axiom eqS_abs_oracle :
 forall 
( str : session_string,  
 sid : session_id, 
 skey : (part, secret_key) map, 
 seed : (part * message, eph_key) map), 
eqS_abs(str,sid,skey,seed) = eqS_oracle(str,sid).

op same_session_string_oracle : 
(session_id , session_id)  -> bool.

axiom same_session_string_abs_oracle :
 forall (sid : session_id, 
 sid' : session_id, 
 skey : (part, secret_key) map, 
 seed : (part * message, eph_key) map),
same_session_string_abs(sid,sid',skey,seed) = 
 same_session_string_oracle(sid,sid').

axiom same_session_string_sym :
 forall (sid : session_id, 
 sid' : session_id),
same_session_string_oracle(sid,sid') = same_session_string_oracle(sid',sid).

game AKE13 =
AKE12
where
 findelse_g_impl =
 {
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
and
   findelse_h_impl =
 {
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
and
 findelse_sid_impl =
 {
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
 } and 
Respond = {
  var y : eph_key = gen_eph_key();  
  var msgs : msg_seed = gen_msg_seed();
  var Y : message option = Some(inp(skey[B], y, msgs));
  if (!in_dom((B,proj(Y)), seed) && in_dom(A, skey) && in_dom(B, skey)
   && sess < qSess && !in_dom((B,proj(Y)),complete_sessions)) {
   complete_sessions[(B,proj(Y))] = (A, X, false);
   keys_revealed[(B,A,proj(Y),X)] = false;
   seed[(B,proj(Y))] = y;
   msg_seeds[(skey[B],y)] = msgs;
   sess = sess + 1;
  }
  else {Y = None;}
  return Y;
 } and
Complete = {
  var x : eph_key = seed[(A,X)];
  var B' : part;
  var eph_flag : bool;
  if (in_dom((A,X), incomplete_sessions)) {
   B' = fst(incomplete_sessions[(A,X)]);
   eph_flag = snd(incomplete_sessions[(A,X)]);
   if (B' = B && !in_dom((A,X), complete_sessions) 
    && !in_dom((A,B,X,Y),keys_revealed)) {
    complete_sessions[(A,X)] = (B,Y,eph_flag);
    keys_revealed[(A,B,X,Y)] = false;
    (*get rid of the session in incomplete*)
   }
  }
 }.
 