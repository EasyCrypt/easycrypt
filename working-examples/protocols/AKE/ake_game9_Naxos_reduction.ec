(* we simulate the oracle of "ake_game9.ec" given the inputs of CDH *)
(*ephkA -- skB *)
(*true = A, false = B*)
include "ake_game9_Naxos.ec".

adversary D_CDH (x : group_naxos, y : group_naxos) : group_naxos
{
 (group_naxos, group_naxos, group_naxos) -> bool (*gdh_oracle*)
}.




game AKE9NaxosCDH = {
(* The state of the Context *)
 var pkA     : public_key_naxos 
 var skA     : secret_key_naxos 
 var pkB     : public_key_naxos 
 var skB     : secret_key_naxos 
 var Xch : message_naxos
 var Ych : message_naxos
 var beta  : message_naxos
 var strch : session_string_naxos 

 var W: group_naxos
 var U : group_naxos
 var V : group_naxos
 var u : int
 var v : int 


fun gen_secret_key_naxos (i:int) :  secret_key_naxos = {
 var u':int;
  u' = [0..q-1];
 return(u');
}
fun gen_eph_key_naxos (i:int) :  secret_key_naxos = {
 var u':int;
  u'= [0..q-1];
 return u';
}

  fun gen_public_key_naxos (sk: secret_key_naxos) : public_key_naxos ={
   return g^sk;
}



 fun gdh_oracle (X:group_naxos,Y,group_naxos,Z:group_naxos) : bool = {
   return gdh(X,Y,Z);
 }

 fun session_match_naxos_Context(s : session_id_naxos, s' : session_id_naxos) : bool = {
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
  
 fun same_session_string_Context(sid1 : session_id_naxos, sid2 : session_id_naxos) : bool = {
  var res : bool = false;
  var b2 : bool; 
  b2 = session_match_naxos_Context(sid1,sid2);
  if ((sid1=sid2) || b2){res = true;}
  return res;
}

  fun eqS_Context(str : session_string_naxos, sid : session_id_naxos) : bool = {
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
 

(* fun Init_Context(b : bool) : (message_naxos * eph_key_naxos) option = {
  var X : message_naxos;
  var x : eph_key_naxos;
  var r : eph_key_naxos;
  var res : (message_naxos * eph_key_naxos) option;
  res = None;
  if ((cntS = indexS) && ((b && (indexP=1)) || (!b && (indexP=0))))
  {  
 if (b) {
   x = gen_eph_key_naxos(0);
   X = U;
   res = Some((X,x));
   seedA[X] = x; 
  } else
  { 
   x = gen_eph_key_naxos(0);
   X = U;
   res = Some((X,x));
   seedB[X] = x;  
  }
  } else 
  {
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
  }
  cntS = cntS + 1;
  return res;
 }*)

 
 (*fun Respond_Context(b : bool, X : message_naxos) :( message_naxos * eph_key_naxos ) option = {
   var Y : message_naxos;
   var y : eph_key_naxos;
   var r : eph_key_naxos;  
  var res : (message_naxos * eph_key_naxos) option;
  var testR : bool;
  testR=(cntS = indexS) && ((b && (indexP=1)) || (!b && (indexP=0)));
 res = None;
  if (testR)
  {  
  if (!b) {
   y = gen_eph_key_naxos(0);
   Y = U;
   res = Some ((Y,y));
   seedB[Y] = y;   
  } else
  {
   y = gen_eph_key_naxos(0);
   Y = U;
   res = Some((Y,y));
   seedA[Y] = y;  
   }
  }
  else
  {  
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
 }
  return res;
 }*)


abs D_naxos = D_naxos {eqS_Context, same_session_string_Context}


fun D_CDH () : group_naxos = {
  strch = D_naxos(skA,skB,Xch,Ych);
  return(session_XY(strch));
}

fun Main () : group_naxos = {
 skA = gen_secret_key_naxos(0);
 pkA = gen_public_key_naxos(skA);
 skB = gen_secret_key_naxos(0);
 pkB = gen_public_key_naxos(skB);

u = gen_eph_key_naxos(0); 
v = gen_secret_key_naxos(0);
U=g^u;
V=g^v;

Xch = U;
Ych = V;

 W = D_CDH();
 return(W);
 }
}.

equiv Reduction : AKE9Naxos.Main ~ AKE9NaxosCDH.Main :
 true ==>
  ={pkA,pkB,skA,skB} && Xch{1}=U{2} && Ych{1}=V{2}  
          && ((let A', B', AY, BX, XY = strch{1} in
               (A' = pkA{1} && B' = pkB{1} && gdh(A',Ych{1},AY) && 
                gdh(B',Xch{1},BX) && gdh(Xch{1},Ych{1},XY))) => 
               gdh(U{2},V{2},res{2}))

by auto (={pkA,pkB,skA,skB,Xch,Ych} &&  
      Xch{1}=U{2}  && Ych{1}=V{2}).

claim Naxos_CDH_9 :
AKE9Naxos.Main[wingame91_naxos(pkA,pkB,Xch,Ych,strch)] <= AKE9NaxosCDH.Main[gdh(U,V,res)]
using Reduction.

