(*ephkA -- skB *)
(*true = A, false = B*)
include "ake_game9.ec".
type group_naxos.
type secret_key_naxos = int.
type public_key_naxos = group_naxos.
type message_naxos = group_naxos.
type part_naxos = public_key_naxos.

type eph_key_naxos = int.

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
    (gdh(g ^ x, g ^y, g ^z) = true) <=> (x * y) =x.

op mk_session_descr_naxos (x : part_naxos, y : message_naxos, b1 : bool, b2: bool) = 
(x,y,b1,b2). 
op session_part_naxos (x : session_descr_naxos) = let a,b,c,d = x in a.
op session_msg_naxos (x : session_descr_naxos) = let a,b,c,d = x in b.
op session_eph_flag_naxos (x : session_descr_naxos) = let a,b,c,d = x in c.
op session_key_reveal_flag_naxos (x : session_descr_naxos) = let a,b,c,d = x in d.

(* pop gen_secret_key_naxos : int -> secret_key_naxos. *)


(* op gen_public_key_naxos : secret_key_naxos -> public_key_naxos. *)


type key_naxos        = secret_key_naxos * public_key_naxos.

type session_string_naxos = part_naxos * part_naxos * group_naxos * group_naxos * group_naxos.
(* A | B | Y^a | X^b | cdh(X,Y) *)


op session_sender (x : session_string_naxos) = let a,b,c,d,e = x in a.
op session_receiver (x : session_string_naxos) = let a,b,c,d,e = x in b.
op session_AY (x : session_string_naxos) = let a,b,c,d,e = x in c.
op session_BX (x : session_string_naxos) = let a,b,c,d,e = x in d.
op session_XY (x : session_string_naxos) = let a,b,c,d,e = x in e.


cnst dummy_session_string_naxos : session_string_naxos. 
cnst dummy_message_naxos : message_naxos. 
cnst dummy_eph_key_naxos : eph_key_naxos.

cnst q :int.

(* pop gen_eph_key_naxos : int -> eph_key_naxos. *)

op inp_naxos  : (secret_key_naxos, eph_key_naxos) -> message_naxos.
op out_noclash_naxos : (secret_key_naxos, eph_key_naxos) -> message_naxos.

adversary D_naxos (skA' : secret_key_naxos, skB' : secret_key_naxos, X' : message_naxos, Y' : message_naxos) :   session_string_naxos
{
 (*bool -> (message_naxos * eph_key_naxos) option;*) (* Init: start either with A or B *)
 (*(bool, message_naxos) -> (message_naxos * eph_key_naxos) option; *)(* Respond *)
 (session_string_naxos,session_id_naxos) -> bool; (* eqS *)
 (session_id_naxos, session_id_naxos) -> bool (* same_session_string *)
}.

game AKE9Naxos = {
 var pkA     : public_key_naxos 
 var skA     : secret_key_naxos 
 var pkB     : public_key_naxos 
 var skB     : secret_key_naxos 
 var Xch : message_naxos
 var Ych : message_naxos
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
 

 (*fun Init(b : bool) : (message_naxos * eph_key_naxos) option = {
  var X : message_naxos;
  var x : eph_key_naxos;
  var r : eph_key_naxos;
  var res : (message_naxos * eph_key_naxos) option;
  res = None;
  if (b) {
   x = gen_eph_key_naxos(0);
   r = gen_eph_key_naxos(0);
   X = g^r;
   res = Some((X,x));
   seedA[X] = x; 
   H1[(skA,x)]=r;
  } else
  { 
   x = gen_eph_key_naxos(0);
   r = gen_eph_key_naxos(0);
   X = g^r;
   res = Some((X,x));
   seedB[X] = x;  
   H1[(skB,x)]=r;
  }
  return res;
 }*)

 
 
 (*fun Respond(b : bool, X : message_naxos) : (message_naxos * eph_key_naxos) option = {
   var Y : message_naxos;
   var y : eph_key_naxos;
   var r : eph_key_naxos;
   var res : (message_naxos * eph_key_naxos) option;
   res = None;
   if (!b) {
    y = gen_eph_key_naxos(0);
    r = gen_eph_key_naxos(0);
    Y = g^r;
    res = Some ((Y,y));
    seedB[Y] = y;   
    H1[(skB,y)]=r;
   } else
   {
    y = gen_eph_key_naxos(0);
    r = gen_eph_key_naxos(0);
    Y = g^r;
    res = Some((Y,y));
    seedA[Y] = y;  
    H1[(skA,y)]=r;
   }
   return res;
 }*)

 
abs D_naxos = D_naxos { (*Init, Respond, *)
eqS, same_session_string }

  
fun Main () : session_string_naxos = {
 var u :int;
 var v: int;

 skA = gen_secret_key_naxos(0);
 pkA = gen_public_key_naxos(skA);
 skB = gen_secret_key_naxos(0);
 pkB = gen_public_key_naxos(skB);

u = gen_eph_key_naxos(0); 
v = gen_secret_key_naxos(0);
 Xch = g^u;
 Ych = g^v;
  strch = D_naxos(skA,skB,Xch,Ych);
 return strch;
 }
}.

op wingame91_naxos
(pkA     : public_key_naxos, 
 pkB     : public_key_naxos, 
 alpha : message_naxos,
 beta : message_naxos, 
 str : session_string_naxos) =
let A, B, AY, BX, XY = str in
 (A = pkA && B = pkB && gdh(A,beta,AY) && gdh(B,alpha,BX) && gdh(alpha,beta,XY)).


op wingame92_naxo
(pkA     : public_key_naxos, 
 pkB     : public_key_naxos, 
 alpha : message_naxos,
 beta : message_naxos, 
 str : session_string_naxos) =
(*(B,A,beta,alpha*)
let A, B, AY, BX, XY = str in
(A = pkB && B = pkA && gdh(A,beta,AY) && gdh(B,alpha,BX) && gdh(alpha,beta,XY)).
 
(* (A = pkB && B = pkA && gdh(A,beta,AY) && gdh(B,alpha,BX) && gdh(beta,alpha,XY)).*)