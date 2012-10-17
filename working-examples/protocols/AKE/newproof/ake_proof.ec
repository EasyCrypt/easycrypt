include "ake_game16.ec".

timeout 10.
checkproof.
equiv Eq1 : AKE1.Main ~ AKE2.Main : 
true ==>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, res, sess, part} by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,LH, sess, part}).

claim C1 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE2.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] 
using Eq1.

equiv Eq2 : AKE2.Main ~ AKE3.Main : 
true ==>
(!coll_session_id(sid_queries{1},skey{1},seed{1})
<=> !coll_session_id(sid_queries{2},skey{2},seed{2})) &&
(!coll_session_id(sid_queries{1},skey{1},seed{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH,sid_queries,res,sess,part})
by auto
upto (coll_session_id(sid_queries,skey,seed)) with
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,LH,sid_queries,sess,part}).

claim C2 : 
AKE2.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE3.Main[coll_session_id(sid_queries,skey,seed)]
using Eq2.

claim sofar1 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE3.Main[coll_session_id(sid_queries,skey,seed)].
unset C2,C2.

equiv Eq3iH : AKE3.iH ~ AKE4.iH :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3ck : AKE3.compute_key ~ AKE4.compute_key :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3iH2 : AKE3.iH ~ AKE4.iHT :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3ck2 : AKE3.compute_key ~ AKE4.compute_keyT :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.

equiv Eq3T : AKE3.Test ~ AKE4.Test :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))) by auto.


equiv Eq3 : AKE3.Main ~ AKE4.Main : true ==> 
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,res,sid_queries,sess,part}
by auto (={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed,sid_queries,sess,part} &&
(forall (x : session_string),
 (in_dom(x,LH{1}) <=>  (in_dom(x,LH{2}) ||  in_dom(x,LHT{2})))) &&
(forall (x : session_string),
in_dom(x,LH{2}) => LH{2}[x] = LH{1}[x]) &&
(forall (x : session_string),
in_dom(x,LHT{2}) => LHT{2}[x] = LH{1}[x]) &&
(forall (x : session_string), !(in_dom(x,LHT{2}) && in_dom(x,LH{2})))).

claim C3_1 : 
AKE3.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] 
using Eq3.

claim C3_2 : 
AKE3.Main[coll_session_id(sid_queries,skey,seed)] =
AKE4.Main[coll_session_id(sid_queries,skey,seed)]
using Eq3.

claim sofar2 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE4.Main[coll_session_id(sid_queries,skey,seed)].

unset C3_1,C3_2,sofar1.

equiv Eq4 : AKE4.Main ~ AKE5.Main : true ==> 
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 sid_queries,res,part,sess} 
by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 sid_queries,part,sess}).

claim C4_1 :
AKE4.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq4.

claim C4_2 : 
AKE4.Main[coll_session_id(sid_queries,skey,seed)] =
AKE5.Main[coll_session_id(sid_queries,skey,seed)]
using Eq4.

claim sofar3 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE5.Main[coll_session_id(sid_queries,skey,seed)].

unset sofar2,C4_1,C4_2.

pred string_coll(m1, m2 : session_string list) = 
exists (x : session_string), mem(x,m1) && mem(x,m2).

op string_coll_op :  (session_string list, session_string list) -> bool.

axiom string_coll_op_def : forall (m1, m2 : session_string list), 
string_coll_op(m1,m2) <=> string_coll(m1,m2).

pred inv(LH : (session_string,session_key) map, LHT : (session_string,session_key) map, 
    argLH : session_string list, argLHT : session_string list, 
    skey : (part,secret_key) map,seed : ((part* message), eph_key) map) =
 (forall (x : session_string), in_dom(x,LHT) => mem(x,argLHT))  &&
 (forall (x : session_string), in_dom(x,LH) => (mem(x,argLH))).

equiv Eq5iHT : AKE5.iHT ~ AKE6.iHT :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={lam,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,res,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))) by auto.

equiv Eq5iH : AKE5.iH ~ AKE6.iH :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={lam,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,res,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))) by auto.

equiv Eq5H : AKE5.H ~ AKE6.H :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) && 
(={str,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
 (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
  argLH, argLHT,res,sid_queries,part,sess} && 
  inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))).
call using Eq5iH.
trivial.
save.

equiv Eq5ckT : AKE5.compute_keyT ~ AKE6.compute_keyT : 
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 argLH, argLHT,sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 argLH, argLHT,sid_queries,res,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))).
call using Eq5iHT.
trivial.
save.

equiv Eq5ck : AKE5.compute_key ~ AKE6.compute_key :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 argLH, argLHT,sid_queries,part,sess} &&
inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT,
 argLH, argLHT,sid_queries,res,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))).
call using Eq5iH.
trivial.
save.

equiv Eq5KR : AKE5.KeyReveal ~ AKE6.KeyReveal :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} && 
  inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))).
sp 13 13.
rnd>>.
if.
if.
sp 3 3.
if.
if.
call using Eq5ck.

trivial.
sp 4 4.
if.
wp.
call using Eq5ck.
trivial.
call using Eq5ck.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq5T : AKE5.Test ~ AKE6.Test :
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
!(string_coll(argLH{1},argLHT{1})) &&
!(string_coll(argLH{2},argLHT{2})) &&
(={s,b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) ==>
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2})) &&
(!string_coll(argLH{1},argLHT{1}) =>
  (={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,res,sid_queries,part,sess} && 
  inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1}))).
sp.
rnd>>.
if.
if.
trivial.
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
wp;call using Eq5ckT.
trivial.
if.
trivial.
wp;call using Eq5ckT.
trivial.
if.
trivial.
wp;call using Eq5ckT.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq5EKR : AKE5.EphKeyReveal ~ AKE6.EphKeyReveal :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5I : AKE5.Init ~ AKE6.Init :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5R : AKE5.Respond ~ AKE6.Respond :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5C : AKE5.Complete ~ AKE6.Complete :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5KG : AKE5.KG ~ AKE6.KG :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5Corr : AKE5.Corrupt ~ AKE6.Corrupt :
(={b,complete_sessions,incomplete_sessions,
 corrupt,pkey,skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, 
 argLH, argLHT,sid_queries,part,sess} && 
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})) by auto. 

equiv Eq5 : AKE5.Main ~ AKE6.Main : true ==> 
(string_coll(argLH{1},argLHT{1}) <=> string_coll(argLH{2},argLHT{2}))
&& (!string_coll(argLH{2},argLHT{2}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, argLH,
 argLHT,res,sid_queries,part,sess}) by auto upto (string_coll(argLH,argLHT)) with
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, LHT, argLH, argLHT,
 sid_queries,part,sess} &&
 inv(LH{1},LHT{1},argLH{1},argLHT{1},skey{1},seed{1})).

claim C5_1 :
AKE5.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[string_coll_op(argLH,argLHT)]
using Eq5.

claim C5_2 :
AKE5.Main[coll_session_id(sid_queries,skey,seed)] <=
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)]
using Eq5.

claim sofar4aux1 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[string_coll_op(argLH,argLHT)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)].

unset C5_1,C5_2, sofar3.

lemma l2 : forall(x : real, n : real), n * x + x = (n+1%r) * x. 
lemma l4 : forall(x : real, n1, n2 : int), n1%r * x + n2%r * x = (n1+n2)%r * x. 

claim sofar4aux2 : 
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[string_coll_op(argLH,argLHT)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)] =
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
AKE6.Main[string_coll_op(argLH,argLHT)] +
AKE6.Main[string_coll_op(argLH,argLHT)].

claim sofar4aux3 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
(AKE6.Main[string_coll_op(argLH,argLHT)] +
AKE6.Main[string_coll_op(argLH,argLHT)]).

claim sofar4 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE6.Main[coll_session_id(sid_queries,skey,seed)] +
2%r *AKE6.Main[string_coll_op(argLH,argLHT)]. 

unset sofar4aux1,sofar4aux2,sofar4aux3.


lemma asd : forall 
(s : session_id, 
 sidl : session_id list,
 skey : (public_key, secret_key) map,
 seed : (part * message, eph_key) map),
!coll_session_id(s::sidl,skey,seed) =>
 (! coll_session_id(sidl,skey,seed) &&
 forall (s' : session_id), mem(s', sidl) => 
  (gen_session_string_sid(s', skey, seed) <>
  gen_session_string_sid(s, skey, seed)) || 
  matching_session_id (s,s')).

equiv Eq6Test : AKE6.Test ~ AKE7.Test : 
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,
 sess,part} &&
(forall (str : session_string), in_dom(str,LHT{1}) => 
 (exists (s : session_id), gen_session_string_sid(s,skey{1},seed{1}) = str &&
   in_dom(s,tested_session{1}))) &&
forall (sid : session_id), 
in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})).
sp.
rnd>>.
if.
if.
trivial. 
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
condt{1}.
sp 3 2.
trivial.
if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
condt{1}.
trivial.
if.
trivial.
inline.
sp.
rnd>>.
sp 1 1.
condt{1}.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq6 : AKE6.Main ~ AKE7.Main : true ==>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,sess,part,res} by auto
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,
 skey,seed,tested_session,msg_seeds,keys_revealed, LH, argLH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), in_dom(str,LHT{1}) => 
 (exists (s : session_id), gen_session_string_sid(s,skey{1},seed{1}) = str &&
   in_dom(s,tested_session{1}))) &&
forall (sid : session_id), 
in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})).

claim C6_1 :
AKE6.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq6.

claim C6_2 :
AKE6.Main[coll_session_id(sid_queries,skey,seed)] =
AKE7.Main[coll_session_id(sid_queries,skey,seed)]
using Eq6.


claim C6_3 :
AKE6.Main[string_coll_op(argLH,argLHT)] =
AKE7.Main[string_coll_op(argLH,argLHT)]
using Eq6.

claim sofar5 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[string_coll_op(argLH,argLHT)].

unset C6_1,C6_2,C6_3,sofar4.

op guess_session_string : 
((session_id,session_key) map,
 session_string list,
 (part, secret_key) map,
 (part * message, eph_key) map) -> bool.

axiom guess_session_string_def :
forall(ts : (session_id,session_key) map,
       argLH : session_string list,
       skey : (part, secret_key) map,
       seed : (part * message, eph_key) map),
guess_session_string(ts,argLH,skey,seed) <=> 
exists (s : session_id), in_dom(s,ts) &&
 mem(gen_session_string_sid(s,skey,seed),argLH).

lemma coll_guess : 
forall(ts : (session_id,session_key) map,
       argLH : session_string list,
       argLHT : session_string list,
       skey : (part, secret_key) map,
       seed : (part * message, eph_key) map),
(forall (str : session_string), mem(str,argLHT) =>
 exists (s : session_id), in_dom(s,ts) && 
 gen_session_string_sid(s,skey,seed) = str) &&
 string_coll_op(argLH,argLHT) =>
 guess_session_string(ts,argLH,skey,seed).


equiv Eq6_test : AKE7.Test ~ AKE7.Test :
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, LHT, argLH, argLHT,sid_queries,part,sess} &&
(forall (str : session_string), mem(str,argLHT{1}) =>
 exists (s : session_id), in_dom(s,tested_session{1}) && 
 gen_session_string_sid(s,skey{1},seed{1}) = str)).
sp.
rnd>>.
if.
if.
if.
trivial.
trivial.
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
inline.
trivial.
if.
trivial.
inline.
trivial.
if.
trivial.
inline.
trivial.
trivial.
trivial.
trivial.
save.


equiv Eq6strcoll : AKE7.Main ~ AKE7.Main : 
true ==> string_coll_op(argLH,argLHT){1} => 
         guess_session_string(tested_session,argLH,skey,seed){2}.
call
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, LHT, argLH, argLHT,sid_queries,part,sess} &&
(forall (str : session_string), mem(str,argLHT{1}) =>
 exists (s : session_id), in_dom(s,tested_session{1}) && 
 gen_session_string_sid(s,skey{1},seed{1}) = str)).
trivial.
save.

claim C6_4 :
AKE7.Main[string_coll_op(argLH,argLHT)] <=
AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq6strcoll.

claim C6_5 : 
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[string_coll_op(argLH,argLHT)] <=
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] .

claim sofar6 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)].

unset C6_4,C6_5,sofar5.

lemma in_dom_upd_elim : 
forall (m : ('a,'b) map, x : 'a, y : 'b, z : 'a),
in_dom(x,upd(m,z,y)) =>
x = z || in_dom(x,m).


equiv Eq7_test : AKE7.Test ~ AKE8.Test :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), mem(str,argLH{1}) =>
(mem(str,argLH{2}) || 
  (exists (sid : session_id), mem(sid,sid_queries{2}) && 
   in_dom(sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] = true &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str))) &&
(forall(str : session_string),mem(str,argLHT{1}) => 
(exists (sid : session_id), mem(sid,sid_queries{2}) && in_dom(sid,tested_session{2}) &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str)) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})) &&
(forall(sid : session_id), in_dom(sid,keys_revealed{1}) && keys_revealed{1}[sid] =>
 mem(sid,sid_queries{1}) || mem(get_matching_session(sid),sid_queries{1})) &&
(forall(sid : session_id), keys_revealed{1}[sid] =>
                              (!in_dom(sid,tested_session{1})) &&
                               !in_dom(get_matching_session(sid),tested_session{1})) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) =>
                              (!keys_revealed{1}[sid] &&
                               !keys_revealed{1}[get_matching_session(sid)]))).
sp.
rnd>>.
if.
if.
if.
trivial.
trivial.
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
if.
trivial.
inline.
trivial.
app 0 0 
={s} &&
 mem (s{2},sid_queries{2}) &&
(forall (r : session_key, str : session_string),
 mem (str,argLHT{1}) =>
 exists (sid : session_id),
 mem (sid,sid_queries{2}) &&
 in_dom (sid,tested_session{2}) &&
 gen_session_string_sid (sid,skey{1},seed{1}) = str).
trivial.
trivial.
if.
trivial.
inline.
trivial.
if.
trivial.
inline.
trivial.
trivial.
trivial.
trivial.
save.



equiv Eq7_keyreveal : AKE7.KeyReveal ~ AKE8.KeyReveal :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), mem(str,argLH{1}) =>
(mem(str,argLH{2}) || 
  (exists (sid : session_id), mem(sid,sid_queries{2}) && 
   in_dom(sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] = true &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str))) &&
(forall(str : session_string),mem(str,argLHT{1}) => 
(exists (sid : session_id), mem(sid,sid_queries{2}) && in_dom(sid,tested_session{2}) &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str)) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})) &&
(forall(sid : session_id), in_dom(sid,keys_revealed{1}) && keys_revealed{1}[sid] =>
 mem(sid,sid_queries{1}) || mem(get_matching_session(sid),sid_queries{1})) &&
(forall(sid : session_id), keys_revealed{1}[sid] =>
                              (!in_dom(sid,tested_session{1})) &&
                               !in_dom(get_matching_session(sid),tested_session{1})) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) =>
                              (!keys_revealed{1}[sid] &&
                               !keys_revealed{1}[get_matching_session(sid)]))).
sp.
rnd>>.
if.
if.
sp 4 4.
if.
if.
inline.
sp.
rnd>>.
sp 1 0.
if.
trivial.
trivial.
sp 4 4.
if.
app 2 2
( ={ssskey} && ={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,skey,seed,msg_seeds,keys_revealed,LH,argLHT,sid_queries,sess,part,A,B,X,Y} &&
 (forall (str : session_string),
  mem (str,argLH{1}) =>
  mem (str,argLH{2}) ||
  (exists (sid : session_id),
   mem (sid,sid_queries{2}) &&
   in_dom (sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] &&
   gen_session_string_sid (sid,skey{1},
    seed{1}) =
   str)) &&
 (forall (str_0 : session_string),
  mem (str_0,argLHT{1}) =>
  exists (sid_0 : session_id),
  mem (sid_0,sid_queries{2}) &&
  in_dom (sid_0,tested_session{2}) &&
  gen_session_string_sid (sid_0,skey{1},
   seed{1}) =
  str_0) &&
 (forall (sid_1 : session_id),
  in_dom (sid_1,tested_session{1}) =>
  mem (sid_1,sid_queries{1})) &&
 (forall (sid_2 : session_id),
  in_dom(sid_2,keys_revealed{1}) &&
  keys_revealed{1}[sid_2] =>
  mem (sid_2,sid_queries{1}) ||
  mem (get_matching_session (sid_2),
  sid_queries{1})) &&
 (forall (sid_3 : session_id),
  in_dom(sid_3,keys_revealed{1}) &&
  keys_revealed{1}[sid_3] =>
  !in_dom (sid_3,tested_session{1}) &&
  !in_dom (get_matching_session (sid_3),
  tested_session{1})) &&
 (forall (sid_4 : session_id),
  in_dom (sid_4,tested_session{1}) =>
  !keys_revealed{1}[sid_4] &&
  !keys_revealed{1}[get_matching_session (
  sid_4)])) && mem((A,B,X,Y){1},sid_queries{1}) && 
  !in_dom((A,B,X,Y){1},tested_session{1}) &&
  !in_dom((B,A,Y,X){1},tested_session{1}).
inline.
sp.
rnd>>.
sp 1 0.
if.
sp.
trivial.
sp.
trivial.
trivial.
inline.
sp.
rnd>>.
sp 1 0.
if.
sp.
trivial.
sp.
trivial.
trivial.
trivial.
trivial.
save.

axiom collisions : 
 forall(sid_queries1, sid_queries2 : session_id list,
        skey1, skey2 : (part, secret_key) map,
        seed1, seed2 : ((part * message), eph_key) map,
        tested_session1, tested_session2 : (session_id, session_key) map,
        argLH1, argLH2 : session_string list,
        keys_revealed1, keys_revealed2 : (session_id, bool) map),
sid_queries1 = sid_queries2 =>
skey1 = skey2 =>
tested_session1 = tested_session2 =>
seed1 = seed2 =>
keys_revealed1 = keys_revealed2 =>
(forall(sid : session_id), in_dom(sid,tested_session1) => mem(sid,sid_queries1)) =>
(forall (str : session_string),
 mem (str,argLH1) =>
 mem (str,argLH2) || (exists (sid : session_id),
  mem (sid,sid_queries2) &&
  in_dom (sid,keys_revealed1) &&
  keys_revealed1[sid] &&
  gen_session_string_sid (sid,skey1,seed1) = str)) =>
(forall(sid : session_id), in_dom(sid,tested_session1) =>
                              (!keys_revealed1[sid] &&
                               !keys_revealed1[get_matching_session(sid)])) =>
guess_session_string (tested_session1,argLH1,skey1,seed1) =>
 guess_session_string (tested_session2,argLH2,skey2,seed2) ||
 coll_session_id (sid_queries2,skey2,seed2).
(*proved in coq: file collisions.v *)


equiv Eq7 : AKE7.Main ~ AKE8.Main :
true ==> guess_session_string(tested_session,argLH,skey,seed){1} =>
(guess_session_string(tested_session,argLH,skey,seed){2} ||
coll_session_id(sid_queries,skey,seed){2}).
app 18 18 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part} &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})) &&
(forall (str : session_string), mem(str,argLH{1}) =>
(mem(str,argLH{2}) || 
  (exists (sid : session_id), mem(sid,sid_queries{2}) && 
   in_dom(sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] = true &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str))) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) =>
                              (!keys_revealed{1}[sid] &&
                               !keys_revealed{1}[get_matching_session(sid)]))).
app 18 18 (={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), mem(str,argLH{1}) =>
(mem(str,argLH{2}) || 
  (exists (sid : session_id), mem(sid,sid_queries{2}) && 
   in_dom(sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] = true &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str))) &&
(forall(str : session_string),mem(str,argLHT{1}) => 
(exists (sid : session_id), mem(sid,sid_queries{2}) && in_dom(sid,tested_session{2}) &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str)) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})) &&
(forall(sid : session_id), in_dom(sid,keys_revealed{1}) && keys_revealed{1}[sid] =>
 mem(sid,sid_queries{1}) || mem(get_matching_session(sid),sid_queries{1})) &&
(forall(sid : session_id), keys_revealed{1}[sid] =>
                              (!in_dom(sid,tested_session{1})) &&
                               !in_dom(get_matching_session(sid),tested_session{1})) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) =>
                              (!keys_revealed{1}[sid] &&
                               !keys_revealed{1}[get_matching_session(sid)]))).
call (={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part} &&
(forall (str : session_string), mem(str,argLH{1}) =>
(mem(str,argLH{2}) || 
  (exists (sid : session_id), mem(sid,sid_queries{2}) && 
   in_dom(sid,keys_revealed{1}) &&
   keys_revealed{1}[sid] = true &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str))) &&
(forall(str : session_string),mem(str,argLHT{1}) => 
(exists (sid : session_id), mem(sid,sid_queries{2}) && in_dom(sid,tested_session{2}) &&
   gen_session_string_sid(sid,skey{1},seed{1}) = str)) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) => mem(sid,sid_queries{1})) &&
(forall(sid : session_id), in_dom(sid,keys_revealed{1}) && keys_revealed{1}[sid] =>
 mem(sid,sid_queries{1}) || mem(get_matching_session(sid),sid_queries{1})) &&
(forall(sid : session_id), keys_revealed{1}[sid] =>
                              (!in_dom(sid,tested_session{1})) &&
                               !in_dom(get_matching_session(sid),tested_session{1})) &&
(forall(sid : session_id), in_dom(sid,tested_session{1}) =>
                              (!keys_revealed{1}[sid] &&
                               !keys_revealed{1}[get_matching_session(sid)]))).
trivial.
trivial.
admit. (*this goal is proved by direct application of the axiom collision*)
save.

equiv Eq7_2 : AKE7.Main ~ AKE8.Main :
true ==> (={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part,res})
by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,b,
 skey,seed,msg_seeds,keys_revealed, LH, argLHT,sid_queries,sess,part}).

claim C7_1 : AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
             AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)
                        || coll_session_id(sid_queries,skey,seed)] using Eq7.

claim C7_2 : 
 AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)
           || coll_session_id(sid_queries,skey,seed)] <=
 AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)] compute.

claim C7_3 : AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
 AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)].
             
claim C7_4 : AKE7.Main[coll_session_id(sid_queries,skey,seed)] =
             AKE8.Main[coll_session_id(sid_queries,skey,seed)] using Eq7_2.

claim C7_5 :
 AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] 
 using Eq7_2.

claim C7_6 :
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE8.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * (AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)]).

claim C7_7 :
2%r * (AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)]) =
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)].

claim C7_8 :
AKE7.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE7.Main[coll_session_id(sid_queries,skey,seed)] +
2%r * AKE7.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
AKE8.Main[coll_session_id(sid_queries,skey,seed)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)].

claim C7_9 : 
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)] =
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 (2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)]
  + AKE8.Main[coll_session_id(sid_queries,skey,seed)]).

lemma lem4 : forall (x : real), 2%r * x + x = 3%r * x.
claim C7_10 : 
 2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)]
  + AKE8.Main[coll_session_id(sid_queries,skey,seed)] =
 3%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)].
unset lem4.

claim C7_11 : 
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 AKE8.Main[coll_session_id(sid_queries,skey,seed)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)] =
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)].

claim sofar7 : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 2%r * AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE8.Main[coll_session_id(sid_queries,skey,seed)].

unset sofar6,C7_11,C7_10,C7_9,C7_8,C7_7,C7_6,C7_5,C7_4,C7_3,C7_2,C7_1.


equiv Eq8T : AKE8.Test ~ AKE9.Test : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part}).
case: b. 
sp.
rnd>>.
inline;derandomize.
wp.
trivial.
sp.
rnd{1}>>.
if{1}.
if{1}.
if{1}.
rnd{2}>>.
!3 condt{2}.
trivial.

rnd{2}>>.
!2 condt{2};condf{2}.
trivial.
if{1}.
sp 2 0.
if{1}.
if{1}.
sp 4 0.
if{1}.
if{1}.
rnd{2}>>.
condt{2};!2 condf{2}.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
condf{1}.
inline{1}.
sp.
rnd>>.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq8 : AKE8.Main ~ AKE9.Main : true ==>
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,res}) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,tested_session}).

claim C8_1 :
AKE8.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] =
AKE9.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq8.

claim C8_2 :
AKE8.Main[coll_session_id(sid_queries,skey,seed)] =
AKE9.Main[coll_session_id(sid_queries,skey,seed)]
using Eq8.

claim C8_3 :
AKE8.Main[guess_session_string(tested_session,argLH,skey,seed)] =
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq8.

claim C8_4 : 
AKE9.Main[res] = 1%r / 2%r compute.

claim sofar8_aux : 
AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
AKE9.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] +
 2%r * AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE9.Main[coll_session_id(sid_queries,skey,seed)].

unset C8_1,C8_1,C8_3.

lemma fresh_sid_lm1 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), incomplete_session) =>  
fresh_sid(sid,corrupt,complete_session,incomplete_session[(A,X) <- (B,flag)]).


lemma fresh_sid_lm2 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid1(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid1(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm3 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid11(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid11(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm4 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid3(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid3(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_sid_lm5 : 
forall (sid : session_id,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh_sid(sid,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh_sid(sid,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).

lemma fresh_lm5 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           Y : message,
           flag : bool),
fresh(ts,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), complete_session) =>  
fresh(ts,corrupt,complete_session[(A,X) <- (B,Y,flag)],incomplete_session).


lemma fresh_sid_lm8 : 
forall (s : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status, 
 A : part),
fresh_sid(s,corrupt,complete_session,incomplete_session) =>
fresh_sid(s,corrupt[A <- false],complete_session,incomplete_session).

lemma fresh_lm9 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part),
fresh(ts,corrupt,complete_session,incomplete_session) =>
fresh(ts,corrupt[A <- false],complete_session,incomplete_session).

lemma fresh_lm10 : 
forall (ts : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status, 
           A : part, 
           X : message,
           B : part,
           flag : bool),
fresh(ts,corrupt,complete_session,incomplete_session) =>
!in_dom((A,X), incomplete_session) =>  
fresh(ts,corrupt,complete_session,incomplete_session[(A,X) <- (B,flag)]).


equiv Eq8_fresh : AKE9.Main ~ AKE9.Main : true ==>
res{1} <=> (res{2} && fresh_op(tested_session,corrupt, 
 complete_sessions,incomplete_sessions){2}) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
 skey,seed,msg_seeds,keys_revealed, LH, argLH,sid_queries,sess,part,tested_session} &&
fresh_op(tested_session,corrupt, 
 complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).

claim C8_5 : 
AKE9.Main[res] =
AKE9.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)]
using Eq8_fresh.

claim sofar8 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE9.Main[coll_session_id(sid_queries,skey,seed)].

unset C8_5,C8_4,sofar8aux.

equiv Eq9ck : AKE9.compute_key ~ AKE10.compute_key : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s])) &&
(forall (str : session_string), in_dom(str,LH{2}) => 
(in_dom(str,LH{1})){1} &&
 (LH[str]){1} = LH[str]{2}) &&
(forall (str : session_string), in_dom(str,LH{1}) => 
 (in_dom(str,LH){2}) || 
 (exists (s : session_id), gen_session_string_sid(s,skey{2},seed{2}) = str &&
 in_dom(s,G{2})))).
inline iH.
derandomize.
rnd>>.
sp 3 0.
if{1}.
sp 1 2.
condf{2}.
condf{2}.
trivial.
sp 1 2.
if{2}.
trivial.
condt{2}.
trivial.
save.

equiv Eq9iH : AKE9.iH ~ AKE10.iH : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s])) &&
(forall (str : session_string), in_dom(str,LH{2}) => 
(in_dom(str,LH{1})){1} &&
 (LH[str]){1} = LH[str]{2}) &&
(forall (str : session_string), in_dom(str,LH{1}) => 
 (in_dom(str,LH){2}) || 
 (exists (s : session_id), gen_session_string_sid(s,skey{2},seed{2}) = str &&
 in_dom(s,G{2})))).
if{2}.
rnd{1}>>.
condf{1}.
trivial.
sp 0 1.
if{2}.
rnd{1}>>.
condf{1}.
trivial.
rnd>>.
condt{1}.
trivial.
save.

equiv Eq9 : AKE9.Main ~ AKE10.Main : true ==>
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,argLH,sid_queries,sess,part}).
rnd.
call
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,argLH,sid_queries,sess,part} &&
(forall (s : session_id), in_dom(s,G{2}) => 
((in_dom(gen_session_string_sid(s,skey,seed),LH{1})){1} &&
 (LH[gen_session_string_sid(s,skey,seed)]){1} =
 G{2}[s])) &&
(forall (str : session_string), in_dom(str,LH{2}) => 
(in_dom(str,LH{1})){1} &&
 (LH[str]){1} = LH[str]{2}) &&
(forall (str : session_string), in_dom(str,LH{1}) => 
 (in_dom(str,LH){2}) || 
 (exists (s : session_id), gen_session_string_sid(s,skey{2},seed{2}) = str &&
 in_dom(s,G{2})))).
trivial.
save.

claim C9_1 :
AKE9.Main[coll_session_id(sid_queries,skey,seed)] =
AKE10.Main[coll_session_id(sid_queries,skey,seed)]
using Eq9.

claim C9_2 :
AKE9.Main[guess_session_string(tested_session,argLH,skey,seed)] =
AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)]
using Eq9.

claim sofar9 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE10.Main[coll_session_id(sid_queries,skey,seed)].

unset C9_1,C9_2,sofar8.

equiv Eq10 : AKE10.Main ~ AKE11.Main : true ==>
((coll_session_id(sid_queries,skey,seed)){1} <=> 
(coll_session_id(sid_queries,skey,seed)){2}) &&
(!(coll_session_id(sid_queries,skey,seed)){1} =>
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part})).
rnd.
 call upto(coll_session_id(sid_queries,skey,seed)) with 
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G,argLHT,LHT}).
trivial.
save.

claim C10_1 :
 AKE10.Main[coll_session_id(sid_queries,skey,seed)] <=
 AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 AKE11.Main[coll_session_id(sid_queries,skey,seed)]
 using Eq10.

claim C10_2 :
 AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
 AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 AKE11.Main[coll_session_id(sid_queries,skey,seed)]
 using Eq10.

claim C10_3 :
 1%r / 2%r +
 2%r * AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE10.Main[coll_session_id(sid_queries,skey,seed)] <=
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 3%r * AKE10.Main[coll_session_id(sid_queries,skey,seed)].

claim C10_4 : 
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 3%r * AKE10.Main[coll_session_id(sid_queries,skey,seed)] <=
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 3%r * (AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]).


claim C10_5 :
 1%r / 2%r +
 2%r * AKE10.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 3%r * AKE10.Main[coll_session_id(sid_queries,skey,seed)] <=
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 3%r * (AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]).

claim sofar10_aux : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 3%r * (AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]).

unset sofar9,C10_1,C10_2,C10_3,C10_4,C10_5.

claim C10_6 :
 3%r * (AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) =
 3%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 3%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

claim C10_7 :
 3%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 3%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] =
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

claim C10_8 :
 3%r * (AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) =
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

unset C10_6,C10_7.

claim sofar10aux2 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

unset C10_8,sofar10aux.

claim C10_9:
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) =
 2%r * AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

claim C10_10 :
 1%r / 2%r +
 2%r * (AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
        AKE11.Main[coll_session_id(sid_queries,skey,seed)]) +
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] =
 1%r / 2%r +
 2%r * AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 2%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

claim sofar10aux3 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 (2%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)]).

unset sofar10aux2, C10_9, C10_10.

lemma lem : forall (x: real), 2%r * x + 6%r * x =  8%r * x. 
claim C10_11 :
 (2%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)] +
 6%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)]) =
 8%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

claim sofar10 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE11.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 8%r * AKE11.Main[coll_session_id(sid_queries,skey,seed)].

unset sofar10aux3, C10_11, lem.

unset C10_5,sofar10aux2.
(* up to here, everything works *)


claim sofar11 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE12.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 8%r * AKE12.Main[coll_session_id(sid_queries,skey,seed)] admit.
(*by instantiate*)
unset sofar10.

equiv Eq12_feg : AKE12.findelse_g_impl ~ AKE13.findelse_g_impl :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
while << : (={m,str,sid',t,lG,res});trivial.
save.


equiv Eq12_feh : AKE12.findelse_h_impl ~ AKE13.findelse_h_impl :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
while << : (={m,str,sid,t,listH,res});trivial.
save.

equiv Eq12_fes : AKE12.findelse_sid_impl ~ AKE13.findelse_sid_impl :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
while << : (={m,sid',sid,t,lG,res});trivial.
save.


equiv Eq12R : AKE12.Respond ~ AKE13.Respond :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
rnd>>.
rnd>>.
sp 1 1.
if.
trivial.
trivial.
save.

equiv Eq12C : AKE12.Complete ~ AKE13.Complete :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
sp 1 1.
if.
sp 2 2.
if.
trivial.
trivial.
trivial.
save.

equiv Eq12CK : AKE12.compute_key ~ AKE13.compute_key :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
app 1 1
(={s,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G,sstr} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
call using Eq12_feh.
trivial.
app 1 1
(={s,complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G,sstr,sid'} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
call using Eq12_fes.
trivial.
if.
trivial.
if.
trivial.
trivial.
save.

equiv Eq12KR : AKE12.KeyReveal ~ AKE13.KeyReveal :
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).
sp.
rnd>>.
if.
sp 3 3.
if.
if.
call using Eq12CK.
trivial.
sp 4 4.
if.
wp.
call using Eq12CK.
trivial.
call using Eq12CK.
trivial.
trivial.
trivial.
save.

equiv Eq12 : AKE12.Main ~ AKE13.Main : true ==>
={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,tested_session,
skey,seed,msg_seeds,keys_revealed,LH,argLH,sid_queries,sess,part,G} &&
(forall(A : part ,X : message), !in_dom((A,X),complete_sessions{2}) => 
 forall (B : part, Y : message), !in_dom((A,B,X,Y), keys_revealed{2}))).


claim C12_1 :
AKE12.Main[guess_session_string(tested_session,argLH,skey,seed)] =
AKE13.Main[guess_session_string(tested_session,argLH,skey,seed)] 
using Eq12.

claim C12_2:
AKE12.Main[coll_session_id(sid_queries,skey,seed)] =
AKE13.Main[coll_session_id(sid_queries,skey,seed)]
using Eq12.

claim C12_3 : 
 1%r / 2%r +
 2%r * AKE12.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 8%r * AKE12.Main[coll_session_id(sid_queries,skey,seed)] =
 1%r / 2%r +
 2%r * AKE13.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 8%r * AKE13.Main[coll_session_id(sid_queries,skey,seed)].

claim sofar12 : 
 AKE1.Main[res && fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions)] <=
 1%r / 2%r +
 2%r * AKE13.Main[guess_session_string(tested_session,argLH,skey,seed)] +
 8%r * AKE13.Main[coll_session_id(sid_queries,skey,seed)].

unset C12_1,C12_2,C12_3,sofar11.

checkproof.
equiv Eq13feg : AKE13.findelse_g_impl ~ AKE13_14_ctxt.findelse_g_impl_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
while << : (={m,str,sid',t,lG,res});trivial.
save.

equiv Eq13feh : AKE13.findelse_h_impl ~ AKE13_14_ctxt.findelse_h_impl_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
while << : (={m,str,sid,t,listH,res});trivial.
save.

equiv Eq13fes : AKE13.findelse_sid_impl ~ AKE13_14_ctxt.findelse_sid_impl_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
while << : (={m,sid',sid,t,lG,res});trivial.
save.

equiv Eq13ck : AKE13.compute_key ~ AKE13_14_ctxt.compute_key_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
app 1 1 
(={s,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part,sstr} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
call using Eq13feh.
trivial.
app 1 1 
(={s,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part,sstr,sid'} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
call using Eq13fes.
trivial.
if.
trivial.
if.
trivial.
if.
trivial.
trivial.
save.

(* equiv Eq12iH : AKE13.iH ~ AKE13_14_ctxt.iH_C : *)
(* (={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} &&  *)
(* keys_revealed_C{2} = keys_revealed{1} && *)
(* sid_queries_C{2} = sid_queries{1} && *)
(* argLHT_C{2} = argLHT{1} && *)
(* argLH_C{2} = argLH{1} && *)
(* b_c{2} = b{1} && *)
(* tested_session_C{2} = tested_session{1} && *)
(* G_C{2} = G{1} && *)
(* LH_C{2} = LH{1} && *)
(* complete_sessions_C{2} = complete_sessions{2} && *)
(* incomplete_sessions_C{2} = incomplete_sessions{2} && *)
(* corrupt_C{2} = corrupt{2} &&  *)
(* (forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) && *)
(* fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1}). *)
(* if. *)
(* trivial. *)
(* derandomize;wp. *)
(* call using Eq12feg. *)
(* trivial. *)
(* save. *)

equiv Eq13KR : AKE13.KeyReveal ~ AKE13_14_ctxt.KeyReveal_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
sp.
rnd>>.
if.
sp 3 3.
if.
if.
call using Eq12ck.
trivial.
sp 4 4.
if.
swap{2} 2 1.
swap{2} 1 1.
wp.
call using Eq12ck.
trivial.
call using Eq12ck.
trivial.
trivial.
trivial.
save.

equiv Eq13T : AKE13.Test ~ AKE13_14_ctxt.Test_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
sp.
rnd>>.
if.
if.
trivial.
trivial.
if.
sp 2 2.
if.
if.
sp 4 4.
if.
if.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
save.

equiv Eq13H : AKE13.H ~ AKE13_14_ctxt.H_C :
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
inline iH, iH_C.
sp 2 2.
if.
trivial.
derandomize; rnd>>;wp.
call using Eq13feg.
trivial.
save.

checkproof.

equiv Eq13R : AKE13.Respond ~ AKE13_14_ctxt.Respond : 
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
rnd>>.
rnd>>.
sp 1 1.

equiv Eq13 : AKE13.Main ~ AKE13_14_ctxt.Main : 
true ==> (guess_session_string(tested_session,argLH,skey,seed){1} =>
 wingame13(fst(res),snd(res),skey,seed,corrupt,
  complete_sessions,incomplete_sessions){2}).
inline B.
wp.
sp.
derandomize.
rnd>>.
sp;wp.
app 1 1
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
call (={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} && 
keys_revealed_C{2} = keys_revealed{1} &&
sid_queries_C{2} = sid_queries{1} &&
argLHT_C{2} = argLHT{1} &&
argLH_C{2} = argLH{1} &&
b_c{2} = b{1} &&
tested_session_C{2} = tested_session{1} &&
G_C{2} = G{1} &&
LH_C{2} = LH{1} &&
complete_sessions_C{2} = complete_sessions{2} &&
incomplete_sessions_C{2} = incomplete_sessions{2} &&
corrupt_C{2} = corrupt{2} && 
(forall (str : session_string), in_dom(str,LH{1}) => mem(str,argLH{1})) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1} &&
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,complete_sessions{1})) && 
(forall (p : part * message), !in_dom(p,seed{1}) => !in_dom(p,incomplete_sessions{1}))).
trivial.
app 0 2 
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} &&
         keys_revealed_C{2} = keys_revealed{1} &&
          sid_queries_C{2} = sid_queries{1} &&
           argLHT_C{2} = argLHT{1} &&
            argLH_C{2} = argLH{1} &&
             b_c{2} = b{1} &&
              tested_session_C{2} = tested_session{1} &&
               G_C{2} = G{1} &&
                LH_C{2} = LH{1} &&
                complete_sessions_C{2} = complete_sessions{2} &&
                 incomplete_sessions_C{2} = incomplete_sessions{2} &&
                  corrupt_C{2} = corrupt{2} && 
(res_0{2} = None <=> forall (str : session_string), mem(str,argLH_C{2}) =>  
 ( forall (sid : session_id),in_dom(sid,tested_session_C{2}) =>
  gen_session_string_sid(sid,skey{2},seed{2}) <> str
)) &&
(res_0{2} <> None <=>  (
  gen_session_string_sid(proj(res_0{2}),skey{2},seed{2}) = str{2} &&
  in_dom(proj(res_0{2}),tested_session_C{2}) &&
  mem(str{2},argLH_C{2}))) &&
fresh_op(tested_session,corrupt, complete_sessions,incomplete_sessions){1}).
sp 1 1.
while{2} :
((res_0{2} = None => forall (x : session_string), mem(x,argLH_C{2}) && 
 !mem(x,argLH_aux{2}) => 
(forall (y : session_id), in_dom(y,tested_session_C{2}) => 
 gen_session_string_sid(y,skey,seed){2} <> x)) && 
(res_0{2} <> None => gen_session_string_sid(proj(res_0),skey,seed){2} = str{2} &&
 mem(str{2},argLH_C{2})) && 
(forall(s : session_string), mem(s,argLH_aux{2}) => mem(s,argLH_C{2}))) : 
- length(argLH_aux{2}), 0. 
inline.
sp.
wp.
 while{2} : 
(t{2} = false  => (res_1{2}=None &&  
(forall (y : session_id), in_dom(y,tested_session_C{2}) && !mem(y,lG{2}) => 
gen_session_string_sid(y,skey{2},seed{2}) <> str_0{2}))) &&
(t{2} = true => (res_1{2} <> None && 
                 gen_session_string_sid(proj(res_1{2}),skey{2},seed{2}) = str_0{2})) && 

(forall (y : session_id), mem(y,lG{2}) => in_dom(y,tested_session_C{2})) && 
mem(str_0{2},argLH_C{2}) &&  
(str_0{2}=str{2}) && 
(forall (str : session_string),mem (str,argLH_aux{2}) => mem(str,argLH_C{2})) : 
- length(lG{2}), 0.
trivial.
trivial.
trivial.
trivial.
save.

claim C12_1 : 
 AKE12.Main[guess_session_string(tested_session,argLH,skey,seed)] <=
 AKE12_13_ctxt.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
                    complete_sessions,incomplete_sessions)] 
using Eq12.


claim C12_2 : 
 AKE12_13_ctxt.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
                    complete_sessions,incomplete_sessions)] <=
 AKE13.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
                    complete_sessions,incomplete_sessions)] admit.
(* this should be justified by "abstraction" *)


equiv Eq13 : AKE13.Main ~ AKE14.Main :
true ==> ={res,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part}
by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part}).

claim C13 : 
AKE13.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions)] =
AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions)] using Eq13.


equiv Eq14 : AKE14.Main ~ AKE14.Main :
true ==>
wingame13(fst(res),snd(res),skey,seed,corrupt,
  complete_sessions,incomplete_sessions){1} <=>
(wingame13(fst(res),snd(res),skey,seed,corrupt,
  complete_sessions,incomplete_sessions){2} && 
 sess{2} <= qSess &&
 part{2} <= qPart) by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part} &&
sess{2} <= qSess &&
 part{2} <= qPart).

claim C14 : 
 AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
                    complete_sessions,incomplete_sessions)] =
 AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
                    complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart] using Eq14.


equiv Eq14part : AKE14.Main ~ AKE14.Main :
true ==>
(wingame13(fst(res),snd(res),skey,seed,corrupt,
  complete_sessions,incomplete_sessions){1} && 
 sess{1} <= qSess &&
 part{1} <= qPart) <=>
(wingame13(fst(res),snd(res),skey,seed,corrupt,
  complete_sessions,incomplete_sessions){2} && 
 sess{2} <= qSess &&
 part{2} <= qPart && 
(fstpart(fst(res)) = sndpart(fst(res)) ||  fstpart(fst(res)) <> sndpart(fst(res))){2})
 by auto
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,msg_seeds,sess,part}).


claim C14_2 : 
AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart] <=
AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && 
(fstpart(fst(res)) = sndpart(fst(res)) || fstpart(fst(res)) <> sndpart(fst(res)))] 
using Eq14part.

claim C14_3 : 
AKE14.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && 
(fstpart(fst(res)) = sndpart(fst(res)) || fstpart(fst(res)) <> sndpart(fst(res)))] <=
AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) = sndpart(fst(res))) || 
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)))] compute.

claim C14_4 : 
AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) = sndpart(fst(res))) || 
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)))] <=
AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) = sndpart(fst(res)))] +
AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
&& sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)))] compute.

claim C14_5 : 
 AKE13.Main[wingame13(fst(res),snd(res),skey,seed,corrupt,
 complete_sessions,incomplete_sessions)] <=
 AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) = sndpart(fst(res)))] +
 AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)))].

(* From now on, we start two different branches *) 
(* a-) the winning session is (A,X,B,Y) and A <> B (game15) *)
(* b-) the winning session is (A,X,B,Y) and A = B *)


(* Note: I will consider that the case where A<>B we have that part > 1 *)
(* I should be able to prove this the following way: we changed the wining 
   event to insist that the given sid (A,X,B,Y) is such that (A,X) and (B,Y)
 are in completed sessions. Then we show that if (A,_) is in completed 
 sessions then it is also the case that A is in pkey. Then we show that if there are
 two different elements in the domain of pkey, then part > 1. The reasoning should 
 be straightforward, except for the fact that the sid comes from the domain of tested
 sessions and right now, I'm not sure whether it is the case that both (A,X) and (B,Y)
 are in completed sessions *)

equiv Eq15 : AKE14.Main ~ AKE15.Main :
true ==>
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1){1} =>
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart){2}.
sp.
!2 rnd{2}>>.
call 
(={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,
  msg_seeds,sess,part,posPart} && 
 (forall(x : part),in_dom(x,posPart{2}) => 0 <= posPart{2}[x] && posPart{2}[x] <= part{2})).
trivial.
save.

claim C15_1 : 
 AKE14.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)))] 
<=
 AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA < qPart &&
 0 <= indexA && indexB < qPart)] using Eq15.

claim C15_2 : 
(AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart)])
<=
 (qPart+1)%r *
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA)]) compute.

claim C15_3 : 
 (qPart+1)%r *
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA)]) <=
 (qPart+1)%r *  (qPart+1)%r *
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB)]) compute.

claim C15_4 : 
(AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart)]) <=
 (qPart+1)%r *  (qPart+1)%r *
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB)]).


equiv Eq15_2 : AKE15.Main ~ AKE15.Main :
true ==>
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB){1} <=>
((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB) ||
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB)){2} by auto.

claim C15_5 : 
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB)]) <=
 (AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB) ||
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB))]) using Eq15_2.

claim C15_6 :
 (AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB) ||
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB))]) <=
AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB))] +
AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB)] compute.

equiv Eq15_3 : AKE15.Main ~ AKE15.Main :
true ==>
((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB)){1} => false{2} by auto
((forall(x, y: part), in_dom(x,posPart{1}) && in_dom(y,posPart{1}) 
&& posPart{1}[x] = posPart{1}[y] => x = y) &&
={complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,
msg_seeds,sess,part,posPart}).

claim C_6 : 
AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB))] <=
AKE15.Main[false] using Eq15_3.

claim C_7 : AKE15.Main[false] = 0%r compute.

claim C_8 :
AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB))] = 0%r.


claim C_9 :
 AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA < qPart &&
 0 <= indexA && indexB < qPart)] <= 
(qPart+1)%r *  (qPart+1)%r *
 (AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB)]) compute.

claim C15_10 :
 (AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB) ||
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB))]) <=
AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB)] compute.

claim C15_11 :
(qPart+1)%r *  (qPart+1)%r *
 (AKE15.Main[((wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA = indexB) ||
(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB))]) <=
(qPart+1)%r *  (qPart+1)%r *
AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB)] compute.



claim C_12 :
AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) 
 && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA < qPart &&
 0 <= indexA && indexB < qPart)] <=
(qPart+1)%r *  (qPart+1)%r *
AKE15.Main[(wingame13(fst(res),snd(res),skey,seed,corrupt,complete_sessions,incomplete_sessions) && sess <= qSess && part <= qPart && fstpart(fst(res)) <> sndpart(fst(res)) &&
 part > 1 && 
 0 <= posPart[fstpart(fst(res))]  && posPart[fstpart(fst(res))] <= qPart &&
 0 <= posPart[sndpart(fst(res))]  && posPart[sndpart(fst(res))] <= qPart &&
 0 <= indexA && indexA <= qPart &&
 0 <= indexA && indexB <= qPart && 
 posPart[fstpart(fst(res))] = indexA &&
 posPart[sndpart(fst(res))] = indexB && indexA <> indexB)] compute.


