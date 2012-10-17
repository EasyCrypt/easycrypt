(* we simulate the oracle of "ake_game8.ec" given the inputs of CGH *)
(*ephkA -- skB *)
(*true = A, false = B*)
include "ake_game8_Naxos.ec".



adversary D_CDH (x : group_naxos, y : group_naxos) : group_naxos
{
 (group_naxos, group_naxos, group_naxos) -> bool (*gdh_oracle*)
}.

game AKE81NaxosCDH = {
(* The state of the Context *)
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

 var W:group_naxos (* cdh result *)
 var U : group_naxos (*cdh challenge 1*)
 var V : group_naxos (*cdh challenge 2*)
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
 

 fun InitB_Context() : message_naxos * eph_key_naxos = {
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
 
 
 fun RespondB_Context(X : message_naxos) : message_naxos * eph_key_naxos = {
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
 
abs D_naxos = D_naxos { InitB_Context, RespondB_Context,eqS_Context, same_session_string_Context}


(*fun D_CDH (Uf:group_naxos,Vf:group_naxos) : group_naxos = {*)
fun D_CDH ( ) : group_naxos = {
   var r : eph_key_naxos;
  

   r  = gen_eph_key_naxos(0);
  
   (alpha,strch) = D_naxos(skA, Xch);
   return(session_BX(strch));
}

fun Main () : group_naxos = {
 skA = gen_secret_key_naxos(0);
 pkA = gen_public_key_naxos(skA);
 v = gen_secret_key_naxos(0);
 ephKA_X = gen_eph_key_naxos(0);
 u = gen_eph_key_naxos(0); 
 U=g^u;
 Xch = U; (*Uf*) 
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 seedB  = empty_map;
 V=g^v;
 pkB = V; (* Vf*)
 W = D_CDH( ); (*D_CDH(U,V)*)
 return(W);
 }
}.



equiv Reduction : AKE81Naxos.Main ~ AKE81NaxosCDH.Main :
       true ==> 
         ={seedB,incomplete_sessions,complete_sessions,
             pkA,pkB,ephKA_X,skA,Xch,alpha,strch} 
          && Xch{1}=U{2}  
          && pkB{1}=V{2} 
          && ((let A', B', AY, BX, XY = strch{1} in
               (A' = pkA{1} && B' = pkB{1} && gdh(A',alpha{1},AY) && 
                gdh(B',Xch{1},BX) && gdh(Xch{1},alpha{1},XY))) => 
               gdh(V{2},U{2},res{2}))
by auto (={seedB,incomplete_sessions,complete_sessions,pkA,pkB,ephKA_X,skA,Xch} &&  
      Xch{1}=U{2}  && pkB{1}=V{2}).

(*inline.
  auto (={seedB,incomplete_sessions,complete_sessions,pkA,pkB,ephKA_X,skA,Xch} &&  
      Xch{1}=U{2}  && pkB{1}=V{2}).
rnd{2};trivial.
save.*)

claim Naxos_CDH :
AKE81Naxos.Main[wingame81_naxos(pkA,pkB,Xch,alpha,strch)] <= AKE81NaxosCDH.Main[gdh(V,U,res)]
using Reduction.


 



