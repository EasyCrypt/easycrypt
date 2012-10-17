(*ephkA -- skB *)
(*true = A, false = B*)
include "ake_game8.ec".
type group_naxos.
type secret_key_naxos = int.
type public_key_naxos = group_naxos.
type message_naxos = group_naxos.
type part_naxos = public_key_naxos.


type session_id_naxos = (part_naxos * part_naxos * message_naxos * message_naxos).
type session_num_and_partner_naxos   = part_naxos * message_naxos.
type incomplete_session_with_status_naxos  = (session_num_and_partner_naxos, part_naxos * bool) map.
type session_descr_naxos = (part_naxos * message_naxos * bool * bool).
type complete_session_with_status_naxos =  (session_num_and_partner_naxos, session_descr_naxos) map.

op fstpart_naxos(x : session_id_naxos) = let a,b,c,d = x in a.
op sndpart_naxos(x : session_id_naxos) = let a,b,c,d = x in b.
op fstmsg_naxos(x : session_id_naxos) = let a,b,c,d = x in c.
op sndmsg_naxos(x : session_id_naxos) = let a,b,c,d = x in d.

cnst g    : group_naxos.
op [^]  : (group_naxos, int) -> group_naxos   as pow.
axiom pow_mul : 
  forall (x, y:int), 
    (g ^ x) ^ y = g ^ (x * y).

op gdh : (group_naxos , group_naxos , group_naxos) -> bool.
axiom gdh_spec :
 forall (x, y, z : int),
    (gdh(g ^ x, g ^y, g ^z) = true) <=> (x * y) = z.

op mk_session_descr_naxos (x : part_naxos, y : message_naxos, b1 : bool, b2: bool) = 
(x,y,b1,b2). 
op session_part_naxos (x : session_descr_naxos) = let a,b,c,d = x in a.
op session_msg_naxos (x : session_descr_naxos) = let a,b,c,d = x in b.
op session_eph_flag_naxos (x : session_descr_naxos) = let a,b,c,d = x in c.
op session_key_reveal_flag_naxos (x : session_descr_naxos) = let a,b,c,d = x in d.

(*pop gen_secret_key_naxos : int -> secret_key_naxos.*)


(*op gen_public_key_naxos : secret_key_naxos -> public_key_naxos.*)
cnst q :int.

type key_naxos        = secret_key_naxos * public_key_naxos.

type session_string_naxos = part_naxos * part_naxos * group_naxos * group_naxos * group_naxos.
(* A | B | Y^a | X^b | cdh(X,Y) *)

op session_sender (x : session_string_naxos) = let a,b,c,d,e = x in a.
op session_receiver (x : session_string_naxos) = let a,b,c,d,e = x in b.
op session_AY (x : session_string_naxos) = let a,b,c,d,e = x in c.
op session_BX (x : session_string_naxos) = let a,b,c,d,e = x in d.
op session_XY (x : session_string_naxos) = let a,b,c,d,e = x in e.

type eph_key_naxos = int.
cnst dummy_session_string_naxos : session_string_naxos. 
cnst dummy_message_naxos : message_naxos. 
cnst dummy_eph_key_naxos : eph_key_naxos.


(*pop gen_eph_key_naxos : int -> eph_key_naxos.*)

adversary D_naxos (skA' : secret_key_naxos, X' : message_naxos) :  (message_naxos * session_string_naxos)
{
 () -> message_naxos * eph_key_naxos ; (* Init: start either with A or B *)
 message_naxos -> message_naxos  * eph_key_naxos; (* Respond *)
 (session_string_naxos,session_id_naxos) -> bool; (* eqS *)
 (session_id_naxos, session_id_naxos) -> bool (* same_session_string *) 
}.


game AKE81Naxos = {
 var pkA     : public_key_naxos 
 var skA     : secret_key_naxos 
 var pkB     : public_key_naxos 
 var skB     : secret_key_naxos 
 var ephKA_X : eph_key_naxos
 var seedB   : (message_naxos, eph_key_naxos) map 
 var complete_sessions : complete_session_with_status_naxos
 var incomplete_sessions : incomplete_session_with_status_naxos

 var Xch : message_naxos
 var alpha : message_naxos 
 var strch : session_string_naxos

fun gen_secret_key_naxos (i:int) :  secret_key_naxos = {
 var u':int;
  u' = [0..q-1];
 return u';
}

fun gen_eph_key_naxos (i:int) :  secret_key_naxos = {
 var u':int;
  u'= [0..q-1];
 return u';
}

 fun gen_public_key_naxos (sk: secret_key_naxos) : public_key_naxos ={
   return g^sk;
}

 fun session_match_naxos (s : session_id_naxos, s' : session_id_naxos) : bool = {
    var A:part_naxos = fstpart_naxos(s);
    var B:part_naxos = sndpart_naxos(s);
    var X:message_naxos = fstmsg_naxos(s);
    var Y:message_naxos = sndmsg_naxos(s);
    var A':part_naxos = fstpart_naxos(s');
    var B':part_naxos = sndpart_naxos(s');
    var X':message_naxos = fstmsg_naxos(s');
    var Y':message_naxos = sndmsg_naxos(s');
    var res : bool;
 res = (A = B' && A' = B && X = Y' && X' = Y);
 return res;
}

 fun same_session_string(sid1 : session_id_naxos, sid2 : session_id_naxos) : bool = {
  var res : bool = false;
  var b2 : bool; 
  b2 = session_match_naxos(sid1,sid2);
  if ((sid1=sid2) || b2){res = true;}
  return res;
 }
  fun eqS(str : session_string_naxos, sid : session_id_naxos) : bool = {
  var A : part_naxos = session_sender(str);
  var B: part_naxos = session_receiver(str);
  var AY : group_naxos = session_AY(str);
  var BX : group_naxos =  session_BX(str);
  var XY : group_naxos = session_XY(str);
  var sA:part_naxos = fstpart_naxos(sid);
  var sB:part_naxos = sndpart_naxos(sid);
  var sX:message_naxos = fstmsg_naxos(sid);
  var sY:message_naxos = sndmsg_naxos(sid);
  var res : bool; 
  res = (A = sA && B = sB && gdh(A,sY,AY) && gdh(B,sX,BX) && gdh(sX,sY,XY));
  return res ;(*eqS_oracle(str,sid));*)
 }
 

 fun InitB() : message_naxos * eph_key_naxos = {
  var X : message_naxos;
  var x : eph_key_naxos;
  var r : eph_key_naxos;
  x = gen_eph_key_naxos(0);
  r = gen_eph_key_naxos(0);
  X = g^r;
  seedB[X] = x;
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message_naxos) : message_naxos * eph_key_naxos = {
 var Y : message_naxos;
 var y : eph_key_naxos;
 var r : eph_key_naxos;
 y = gen_eph_key_naxos(0);
 r = gen_eph_key_naxos(0);
 Y = g^r;
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}
 
abs D_naxos = D_naxos { InitB, RespondB, eqS, same_session_string }

  
fun Main () : message_naxos * session_string_naxos * message_naxos = {
 var u : int;
 skA = gen_secret_key_naxos(0);
 pkA = gen_public_key_naxos(skA);
 skB = gen_secret_key_naxos(0);
 pkB = gen_public_key_naxos(skB);
 ephKA_X = gen_eph_key_naxos(0);
 u  = gen_eph_key_naxos(0);
 Xch = g^u;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 seedB  = empty_map;
 (alpha,strch) = D_naxos(skA, Xch);
 return (alpha,strch,Xch);
 }
}.

game AKE82Naxos = {
 var pkA     : public_key_naxos 
 var skA     : secret_key_naxos 
 var pkB     : public_key_naxos 
 var skB     : secret_key_naxos 
 var ephKA_Y : eph_key_naxos
 var seedB   : (message_naxos, eph_key_naxos) map 
 var complete_sessions : complete_session_with_status_naxos
 var incomplete_sessions : incomplete_session_with_status_naxos


 var Ych : message_naxos
 var alpha : message_naxos 
 var strch : session_string_naxos

fun gen_secret_key_naxos (i:int) :  secret_key_naxos = {
 var u:int;
  u= [0..q-1];
 return(u);
}

fun gen_eph_key_naxos (i:int) :  secret_key_naxos = {
 var u:int;
  u= [0..q-1];
 return u;
}

 fun gen_public_key_naxos (sk: secret_key_naxos) : public_key_naxos ={
   return g^sk;
}
   fun session_match_naxos (s : session_id_naxos, s' : session_id_naxos) : bool = {
    var A:part_naxos = fstpart_naxos(s);
    var B:part_naxos = sndpart_naxos(s);
    var X:message_naxos = fstmsg_naxos(s);
    var Y:message_naxos = sndmsg_naxos(s);
    var A':part_naxos = fstpart_naxos(s');
    var B':part_naxos = sndpart_naxos(s');
    var X':message_naxos = fstmsg_naxos(s');
    var Y':message_naxos = sndmsg_naxos(s');
    var res : bool;
 res = (A = B' && A' = B && X = Y' && X' = Y);
 return res;
}

  fun same_session_string(sid1 : session_id_naxos, sid2 : session_id_naxos) : bool = {
  var res : bool = false;
  var b2 : bool; 
  b2 = session_match_naxos(sid1,sid2);
  if ((sid1=sid2) || b2){res = true;}
  return res;
 }
  fun eqS(str : session_string_naxos, sid : session_id_naxos) : bool = {
  var A : part_naxos = session_sender(str);
  var B: part_naxos = session_receiver(str);
  var AY : group_naxos = session_AY(str);
  var BX : group_naxos =  session_BX(str);
  var XY : group_naxos = session_XY(str);
  var sA:part_naxos = fstpart_naxos(sid);
  var sB:part_naxos = sndpart_naxos(sid);
  var sX:message_naxos = fstmsg_naxos(sid);
  var sY:message_naxos = sndmsg_naxos(sid);
  var res : bool;
  res = (A = sA && B = sB && gdh(A,sY,AY) && gdh(B,sX,BX) && gdh(sX,sY,XY));
  return res ;(*eqS_oracle(str,sid));*)
 }
 

 fun InitB() : message_naxos * eph_key_naxos = {
  var X : message_naxos;
  var x : eph_key_naxos;
  var r : eph_key_naxos;
  x = gen_eph_key_naxos(0);
  r = gen_eph_key_naxos(0);
  X = g^r;
  seedB[X] = x;  
  incomplete_sessions[(pkB,X)] = (pkA,false);
  return (X,x);
 }
 
 
 fun RespondB(X : message_naxos) : message_naxos * eph_key_naxos = {
 var Y : message_naxos;
 var y : eph_key_naxos;
 var r : eph_key_naxos;
 y = gen_eph_key_naxos(0);
 r = gen_eph_key_naxos(0);
 Y = g^r;
 seedB[Y] = y;
 complete_sessions[(pkB,Y)] = (pkA,X,false,false); 
 return (Y,y);
}
 
abs D_naxos = D_naxos { InitB, RespondB, eqS, same_session_string }
  
fun Main () : message_naxos * session_string_naxos  * message_naxos = {
 var v : eph_key_naxos;
 skA = gen_secret_key_naxos(0);
 pkA = gen_public_key_naxos(skA);
 skB = gen_secret_key_naxos(0);
 pkB = gen_public_key_naxos(skB);
 ephKA_Y = gen_eph_key_naxos(0);
 v = gen_eph_key_naxos(0);
 Ych = g^v;
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 seedB  = empty_map;
 (alpha,strch) = D_naxos(skA, Ych);
 return (alpha,strch,Ych);
 }
}.

op wingame81_naxos
(sA : public_key_naxos,
 sB : public_key_naxos,
 sX : message_naxos,
 alpha : message_naxos,
 str : session_string_naxos
(*,complete_session : complete_session_with_status_naxos*)
) =
let A', B', AY, BX, XY = str in
 (A' = sA && B' = sB && gdh(A',alpha,AY) && gdh(B',sX,BX) && gdh(sX,alpha,XY)).

(*eqS(str,(A,B,X,alpha)).*)


op wingame82_naxos
(sA : public_key_naxos,
 sB : public_key_naxos,
 alpha : message_naxos,
 sY : message_naxos,
 str : session_string_naxos) =
let A, B, AY, BX, XY = str in
 (A = sB && B = sA && gdh(A,sY,AY) && gdh(B,alpha,BX) && gdh(alpha,sY,XY)).

(* too strong? *)
 (* && in_dom((B,alpha),incomplete_session) &&  *)
(* A = fst(incomplete_session[(B,alpha)]) &&  *)
(* in_dom((A,Y),complete_session) && session_part_naxos(complete_session[(A,Y)]) = B && *)
(* session_msg(complete_session[(A,Y)]) = alpha. *)


(*claim inst_claim : AKE81Naxos.Main[wingame81_naxos(pkA,pkB,Xch,alpha,strch)] = AKE81Naxos.Main[wingame81_naxos(pkA,pkB,Xch,alpha,strch)].*)
