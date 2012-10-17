include "ake_proof_reduction45.ec".

lemma hd_tl:
 forall (l:'a list), l <> [] => hd(l) :: tl(l) = l.

equiv findelse_sid_none : AKE5_red.findelse_sid_oracle ~ AKE5_red.Skip :
={m, sid} ==>
res{1} = None =>
(forall (x : session_id), in_dom(x,fst(res{2})) => 
 ! same_session_string_oracle(x,snd(res{2}))).
 while{1} last : (res{1} = None =>
 (forall (x : session_id), in_dom(x,m{2}) && !mem(x, lG{1}) => 
  ! same_session_string_oracle(x,sid{2}) )) && ={m, sid}  : - length(lG{1}), 0;
  inline;trivial.
save.

equiv findelse_sid_some : AKE5_red.findelse_sid_oracle ~ AKE5_red.Skip :
={m, sid} ==>
res{1} <> None =>
 same_session_string_oracle(proj(res{1}),snd(res{2})) && in_dom(proj(res{1}), fst(res{2})).
 while{1} last : 
((res{1} <> None =>
 same_session_string_oracle(proj(res{1}),sid{2}) && in_dom(proj(res{1}), m{2}))
 && (forall (sid : session_id), mem(sid,lG{1}) => in_dom(sid,m{1})) 
 && ={m, sid})  : - length(lG{1}), 0;
 inline; trivial.
save.

equiv findelse_sid_impl_oracle : AKE3_instantiate_findelse.findelse_sid_impl ~  AKE5_red.findelse_sid_oracle : (true).
 while last : (={m,sid,t,lG,res}) : - length(lG{1}), 0.
 inline;autosync;trivial.
 trivial.
save.

equiv findelse_g_impl_oracle : AKE3_instantiate_findelse.findelse_g_impl ~  AKE5_red.findelse_g_oracle : (true).
 while last : (={m,str,t,lG,res}) : - length(lG{1}), 0.
 inline;autosync;trivial.
 trivial.
save.

equiv findelse_h_impl_oracle : AKE3_instantiate_findelse.findelse_h_impl ~  AKE5_red.findelse_h_oracle : (true).
 while last : (={m,sid, t,listH,res}) : - length(lG{1}), 0.
 inline;autosync;trivial.
 trivial.
save.

equiv equiv_H : AKE3_instantiate_findelse.H ~ AKE5_red.H_B :
={lam, corrupt,pkey,skey,bad,seed,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)])))
==> 
={corrupt,pkey,skey,bad,seed,res,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ ( A,X)]) && session_msg
(complete_sessions{2}[ (A,X)]) = session_msg (complete_sessions_B{2}[
( A,X)]) && session_eph_flag ( complete_sessions{2}[ (A,X)]) =
session_eph_flag ( complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 :
part, X_0 : message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=>
in_dom ((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd
(incomplete_sessions_B{2}[(A_0,X_0)]))).
(*derandomize.
app 4 4 ={ corrupt, pkey, skey, seed, bad, lam, h, findr, findr',b} &&
complete_sessions_B{2} = complete_sessions{1} &&
incomplete_sessions_B{2} = incomplete_sessions{1} &&
pkey_B{2} = pkey{2} &&
corrupt_B{2} = corrupt{2} &&
tested_session_B{2} = tested_session{1} &&
G_B{2} = G{1} &&
LH_B{2} = LH{1} &&
(forall (p : part), in_dom(p,corrupt{2}) <=> in_dom(p,skey{2})) &&
LHT_B{2} = LHT{1} &&
(forall (A: part, X : message),
 (in_dom((A,X),complete_sessions{2}) <=> in_dom((A,X),complete_sessions_B{2})) &&
 (in_dom((A,X),complete_sessions{2}) =>
  session_part(complete_sessions{2}[(A,X)]) = session_part (complete_sessions_B{2}[(A,X)]) &&
  session_msg(complete_sessions{2}[(A,X)]) = session_msg (complete_sessions_B{2}[(A,X)]) &&
  session_eph_flag(complete_sessions{2}[(A,X)]) = session_eph_flag (complete_sessions_B{2}[(A,X)]))) &&
(forall (A: part, X : message),
 (in_dom((A,X),incomplete_sessions{2}) <=> in_dom((A,X),incomplete_sessions_B{2})) &&
 (in_dom((A,X),incomplete_sessions{2}) =>
  fst(incomplete_sessions{2}[(A,X)]) = fst(incomplete_sessions_B{2}[(A,X)]) &&
  snd(incomplete_sessions{2}[(A,X)]) = snd (incomplete_sessions_B{2}[(A,X)])
 ));[|trivial].
*(call using findelse_g_impl_oracle);trivial.*)
admit.
save.


equiv ADV_test : AKE3_instantiate_findelse.Test ~ AKE5_red.Test_B :
={s, corrupt,pkey,skey,bad,seed,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)])))
==> 
={corrupt,pkey,skey,bad,seed,res,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ ( A,X)]) && session_msg
(complete_sessions{2}[ (A,X)]) = session_msg (complete_sessions_B{2}[
( A,X)]) && session_eph_flag ( complete_sessions{2}[ (A,X)]) =
session_eph_flag ( complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 :
part, X_0 : message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=>
in_dom ((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd
(incomplete_sessions_B{2}[(A_0,X_0)]))).
(**autosync;trivial.
timeout 5.
trivial.*)
admit.
save.

equiv ADV_KR : AKE3_instantiate_findelse.KeyReveal ~ AKE5_red.KeyReveal_B :
={s, corrupt,pkey,skey,bad,seed, b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)]))) 
==> 
={corrupt,pkey,skey,bad,seed,res,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ ( A,X)]) && session_msg
(complete_sessions{2}[ (A,X)]) = session_msg (complete_sessions_B{2}[
( A,X)]) && session_eph_flag ( complete_sessions{2}[ (A,X)]) =
session_eph_flag ( complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 :
part, X_0 : message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=>
in_dom ((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)]))). 
(*derandomize.
app 1 1
={s, h_0, corrupt,pkey,skey,bad,seed, b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)]))).
rnd;trivial.
autosync.
trivial.
autosync.
autosync.
autosync.
trivial.
ifsync.
ifsync.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.
ifsync.
ifsync.
wp.
call using findelse_h_impl_oracle.
call using findelse_h_impl_oracle.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.
wp.
call using findelse_h_impl_oracle.
call using findelse_h_impl_oracle.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.
wp.
call using findelse_h_impl_oracle.
call using findelse_h_impl_oracle.
wp.
call using findelse_sid_impl_oracle.
call using findelse_sid_impl_oracle.
trivial.

wp.
*call using findelse_h_impl_oracle.
wp.
*call using findelse_sid_impl_oracle.
trivial.

wp.
*call using findelse_h_impl_oracle.
wp.
*call using findelse_sid_impl_oracle.
trivial.

wp.
*call using findelse_sid_impl_oracle.
trivial.

 autosync.
 autosync.
 trivial.
ifsync.
 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.

 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.

 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.

 wp.
 call using findelse_h_impl_oracle.
 call using findelse_h_impl_oracle.
 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.

 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.
 ifsync;[trivial | |]. 

 ifsync.
 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.
timeout 10.
trivial.
timeout 15.
trivial.

 wp.
 call using findelse_h_impl_oracle.
 call using findelse_h_impl_oracle.
 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.
timeout 3.
 wp.
 call using findelse_sid_impl_oracle.
 call using findelse_sid_impl_oracle.
 trivial.
 trivial.
trivial.*)
admit.
save.

equiv ADV : AKE3_instantiate_findelse.A ~ AKE5_red.A :
={corrupt,pkey,skey,bad,seed,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)])))
==>
={corrupt,pkey,skey,bad,seed,b,res} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)])))
 by auto (={corrupt,pkey,skey,bad,seed,b} && complete_sessions_B{2} =
complete_sessions{1} && incomplete_sessions_B{2} =
incomplete_sessions{1} && pkey_B{2} = pkey{2} && corrupt_B{2} =
corrupt{2} && tested_session_B{2} = tested_session{1} && G_B{2} = G{1}
&& LH_B{2} = LH{1} && (forall (p : part), in_dom (p,corrupt{2}) <=>
in_dom (p,skey{2})) && LHT_B{2} = LHT{1} && (forall (A : part, X :
message), (in_dom ((A,X), complete_sessions{2}) <=> in_dom ((A,X),
complete_sessions_B{2})) && (in_dom ((A,X), complete_sessions{2}) =>
session_part (complete_sessions{2}[ (A,X)]) = session_part
(complete_sessions_B{2}[ (A,X)]) && session_msg (complete_sessions{2}[
(A,X)]) = session_msg (complete_sessions_B{2}[ (A,X)]) &&
session_eph_flag ( complete_sessions{2}[ (A,X)]) = session_eph_flag (
complete_sessions_B{2}[ (A,X)]))) && (forall (A_0 : part, X_0 :
message), (in_dom ((A_0,X_0), incomplete_sessions{2}) <=> in_dom
((A_0,X_0), incomplete_sessions_B{2})) && (in_dom ((A_0,X_0),
incomplete_sessions{2}) => fst (incomplete_sessions{2}[ (A_0,X_0)]) =
fst (incomplete_sessions_B{2}[ (A_0,X_0)]) && snd
(incomplete_sessions{2}[ (A_0,X_0)]) = snd (incomplete_sessions_B{2}[
(A_0,X_0)])))).


lemma fresh12disj :
 forall (sid : session_id,
        corrupt : (part, bool) map,
        complete_session : complete_session_with_status,
        incomplete_session : incomplete_session_with_status),
!( fresh_sid1 (sid,corrupt,complete_session,incomplete_session) &&
   fresh_sid2 (sid,corrupt)).

lemma fresh23disj :
 forall (sid : session_id,
        corrupt : (part, bool) map,
        complete_session : complete_session_with_status,
        incomplete_session : incomplete_session_with_status),
!( fresh_sid2 (sid,corrupt) &&
   fresh_sid3 (sid,corrupt,complete_session,incomplete_session)).

lemma fresh31disj :
 forall (sid : session_id,
        corrupt : (part, bool) map,
        complete_session : complete_session_with_status,
        incomplete_session : incomplete_session_with_status),
!( fresh_sid3 (sid,corrupt,complete_session,incomplete_session) &&
   fresh_sid1 (sid,corrupt,complete_session,incomplete_session)).


equiv Reduction : AKE3_instantiate_findelse.Main ~ AKE5_red.Main : 
true ==> 
(guess_session_string_op(tested_session{1},skey{1},seed{1},LH{1},G{1}) && 
fresh_op(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1}))
=>
wingame5(fst(res{2}),snd(res{2}),corrupt{2},complete_sessions_B{2},incomplete_sessions_B{2}).
app 20 20
(guess_session_string(tested_session{1},skey{1},seed{1},LH{1},G{1}) && 
fresh(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1}))
=> wingame5(fst(sidss{2}),snd(sidss{2}),corrupt{2},complete_sessions_B{2},incomplete_sessions_B{2}).
inline B.
app 13 22 
(guess_session_string (tested_session{1},skey{1},seed{1},LH{1},G{1}) <=> 
guess_session_string (tested_session_B{2},skey{2},seed{2},LH_B{2},G_B{2}))
&& 
(fresh(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1}) <=>
fresh(tested_session_B{2},corrupt{2},complete_sessions_B{2},incomplete_sessions_B{2})).
call using ADV.
trivial.
case{1}: !guess_session_string_op(tested_session,skey,seed,LH,G).
(*Nothing to prove *)
app 0 4 !guess_session_string_op(tested_session{1},skey{1},seed{1},LH{1},G{1}).
wp.
while{2} last : !guess_session_string_op (tested_session{1},skey{1},seed{1},LH{1},G{1}) : 
                - length(dTS{2}), 0.
inline.
wp; while{2} last : !guess_session_string_op (tested_session{1},skey{1},seed{1},LH{1},G{1}) : 
                    - length(listH{2}), 0.
trivial.
trivial.
trivial.
trivial.
trivial.
inline.
wp; while{2} last : true : - length(listH{2}), 0.
trivial.
trivial.
trivial.
trivial.
app 0 0 (guess_session_string (tested_session{1},skey{1},seed{1},LH{1},G{1}) <=> 
guess_session_string (tested_session_B{2},skey{2},seed{2},LH_B{2},G_B{2}))
&& 
(fresh(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1}) <=>
fresh(tested_session_B{2},corrupt{2},complete_sessions_B{2},incomplete_sessions_B{2}))
&&       guess_session_string_op (tested_session_B{2},skey{2},seed{2},LH_B{2},G_B{2}).
trivial.

case{1}: !fresh_op(tested_session,corrupt,complete_sessions,incomplete_sessions).
app 0 4 (!fresh_op(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1})).
wp.
while{2} last : (!fresh_op(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1})) : - length(dTS{2}), 0.
inline.
wp.
while{2} last : (!fresh_op(tested_session{1},corrupt{1},complete_sessions{1},incomplete_sessions{1})) : - length(listH{2}), 0.
trivial.
trivial.
trivial.
trivial.
inline.
wp.
while{2} last : true : - length(listH{2}), 0.
trivial.
trivial.
trivial.
trivial.
app 0 0 fresh(tested_session_B{2},corrupt{2},complete_sessions_B{2},
                incomplete_sessions_B{2}) &&
         guess_session_string_op (tested_session_B{2},skey{2},seed{2},
                                  LH_B{2},G_B{2}).
trivial.
app 0 10  wingame5 (fst (sidss{2}),snd (sidss{2}),corrupt{2},
                  complete_sessions_B{2},incomplete_sessions_B{2});[|trivial].

app 0 3 
found{2} <> None && eqS_oracle(proj(found{2}),s{2}) && in_dom(s{2},tested_session_B{2})
&& fresh(tested_session_B{2},corrupt{2},complete_sessions_B{2},
                incomplete_sessions_B{2}).
 while{2} last : 
(found{2}=None => forall (x : session_id), in_dom(x,tested_session_B{2}) && !mem(x,dTS{2}) => 
(forall (y : session_string), in_dom(y,LH_B{2}) => !eqS_oracle(y,x))) && 
(found{2} <> None => eqS_oracle(proj(found{2}),s{2}) && in_dom(s{2},tested_session_B{2}))  && (forall (sid : session_id), mem(sid,dTS{2}) => in_dom(sid,tested_session_B{2})): 
- length(dTS{2}), 0.
inline.
wp.
 while{2} last : 
(t{2} = false  => (res_0{2}=None &&  
(forall (y : session_string), in_dom(y,LH_B{2}) && !mem(y,listH{2}) => !eqS_oracle(y,sid{2})))) &&(t{2} = true => (res_0{2} <> None && eqS_oracle(proj(res_0{2}),sid{2}))) && (forall (y : session_string), mem(y,listH{2}) => in_dom(y,LH_B{2})) && in_dom(sid{2},tested_session_B{2}) &&  (sid{2}=s{2}) && (forall (sid : session_id),mem (sid,dTS{2}) => in_dom (sid,tested_session_B{2})) : 
- length(listH{2}), 0.
inline;trivial.
trivial.
trivial.
trivial.
inline.
wp; while{2} last : true : - length(listH{2}), 0.
trivial.
trivial.
trivial.
(*loop ending *)

trivial.
trivial.
save.

claim badRed : 
AKE3_instantiate_findelse.Main[guess_session_string_op(tested_session,skey,seed,LH,G) 
                   && fresh_op(tested_session,corrupt,complete_sessions,incomplete_sessions)] <= 
AKE5_red.Main[wingame5(fst(res),snd(res),corrupt,complete_sessions_B,incomplete_sessions_B)] using Reduction.
