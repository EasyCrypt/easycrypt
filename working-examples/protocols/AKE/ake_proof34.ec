include "ake_game4.ec".


lemma link_update_skey :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : part,
           sk : secret_key),
link_tested_G_LHT(tested_session,skey,seed,LHT,G) && !in_dom(p, skey) => link_tested_G_LHT(tested_session,upd(skey,p,sk),seed,LHT,G).

timeout 10.
lemma link_update_seed :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : message * part,
           ek : eph_key),
link_tested_G_LHT(tested_session,skey,seed,LHT,G) && !in_dom(p, seed) => link_tested_G_LHT(tested_session,skey,upd(seed,p,ek),LHT,G).
timeout 3.

lemma guess_update_skey :
 forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : part,
           sk : secret_key),
guess_session_string(tested_session,skey,seed,LH, G) && !in_dom(p, skey) =>  guess_session_string(tested_session,upd(skey,p,sk),seed,LH, G).

lemma guess_update_seed :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : (message * part),
           ek : eph_key),
guess_session_string(tested_session,skey,seed,LH, G) && !in_dom(p, seed) =>  guess_session_string(tested_session,skey,upd(seed,p,ek),LH, G).


lemma bad_update_skey :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : part,
           sk : secret_key),
bad(tested_session,skey,seed,LH, G) && !in_dom(p, skey) =>  bad(tested_session,upd(skey,p,sk),seed,LH, G).

lemma bad_update_seed :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : message * part,
           ek : eph_key),
bad(tested_session,skey,seed,LH, G) && !in_dom(p, seed) =>  bad(tested_session,skey,upd(seed,p,ek),LH, G).

lemma bad_update_tested_session :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) && !in_dom(sid, tested_session) =>  bad(upd(tested_session,sid,sk),skey,seed,LH, G).

lemma bad_update_G :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) && !in_dom(sid, G) =>  bad(tested_session,skey,seed,LH, upd(G,sid,sk)).

lemma bad_update_G' :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) && in_dom(sid, G) && 
G[sid] = sk =>  bad(tested_session,skey,seed,LH, upd(G,sid,sk)).

lemma bad_update_LH :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           str : session_string,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) && !in_dom(str, LH) =>  bad(tested_session,skey,seed,upd(LH,str,sk), G).

lemma bad_aux_1 : 
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sid' : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) &&
!in_dom(sid,G) &&
sid = sid' => 
bad(tested_session,skey,seed,LH, upd(upd(G,sid,sk),sid',sk)).

lemma bad_aux_2 : 
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sid' : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) &&
!in_dom(sid,G) &&
!in_dom(sid',G) &&
sid <> sid' => 
bad(tested_session,skey,seed,LH, upd(upd(G,sid,sk),sid',sk)).

timeout 10.
lemma bad_update_G2 :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map,
           sid : session_id,
           sid' : session_id,
           sk : session_key),
bad(tested_session,skey,seed,LH, G) &&  
((sid <> sid' => !in_dom(sid,G) && !in_dom(sid',G)) ||
 (sid = sid' => !in_dom(sid,G))) =>
 bad(tested_session,skey,seed,LH, upd(upd(G,sid,sk),sid',sk)).
timeout 3.

lemma findelse_sid_abs_none_dom:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map),
findelse_sid_abs(m',s',skey',seed') = None =>
!in_dom(s',m').


lemma findelse_sid_abs_none_dom_matching:
forall (m' :  (session_id, session_key) map,
        s' : session_id, 
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map),
findelse_sid_abs(m',s',skey',seed') = None =>
let s = mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s')) in
!in_dom(s,m').


lemma bad_op_def :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), bad(tested_session,skey,seed,LH, G) <=> bad_op(tested_session,skey,seed,LH, G).

equiv Fact_EKR : AKE2.EphKeyReveal ~ AKE3.EphKeyReveal : 
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, A, X}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2}))))) ==> 
(bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2}, seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) =>(
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, res}
&& LHT{2} = empty_map && (forall ( str : session_string), in_dom (
str,LHT{1}) => findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None && ( findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None => tested_session{1}[ proj ( findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None => G{1}[ proj (
findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1}, seed{1},LHT{1}, G{1})
&& ( forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) &&
in_dom (str_0,LHT{2}))))).
*autosync;
(wp;
trivial).
save.

equiv FactTest : AKE2.Test ~ AKE3.Test : 
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, s}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2}))))) ==> 
(bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2}, seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) =>(
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, res}
&& LHT{2} = empty_map && (forall ( str : session_string), in_dom (
str,LHT{1}) => findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None && ( findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None => tested_session{1}[ proj ( findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None => G{1}[ proj (
findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1}, seed{1},LHT{1}, G{1})
&& ( forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) &&
in_dom (str_0,LHT{2}))))).
app 0 0 (!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
(={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, s}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2})))))).
trivial.
app 50 50 
((bad(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) <=>
bad(tested_session{2}, skey{2}, seed{2}, LH{2},G{2})) && (
!bad(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, ssskey}
&& LHT{2} = empty_map && (forall ( str : session_string), in_dom (
str,LHT{1}) => findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None && ( findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None => tested_session{1}[ proj ( findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None => G{1}[ proj (
findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1}, seed{1},LHT{1}, G{1})
&& ( forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) &&
in_dom (str_0,LHT{2}))))).
inline;derandomize;wp;rnd.
trivial.
expand bad,link_tested_G_LHT.
expand guess_session_string, test_key_reveal_collision.
trivial.
timeout 30.
trivial.
trivial.
save.

timeout 3.

equiv FactTest : AKE2.KeyReveal ~ AKE3.KeyReveal : 
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, s}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2})))) ==> 
(bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2}, seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) =>(
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, res}
&& LHT{2} = empty_map && (forall ( str : session_string), in_dom (
str,LHT{1}) => findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None && ( findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None => tested_session{1}[ proj ( findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None => G{1}[ proj (
findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1}, seed{1},LHT{1}, G{1})
&& ( forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) &&
in_dom (str_0,LHT{2}))))).
app 0 0 (!bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, s}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2}))))).
trivial.
derandomize.
app 1 1 (!bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) &&
!bad(tested_session{2}, skey{2},seed{2}, LH{2},G{2}) &&
(bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) <=>
bad(tested_session{2}, skey{2},seed{2}, LH{2},G{2})) && (
!bad(tested_session{1}, skey{1},seed{1}, LH{1},G{1}) =>
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, s}
&& LHT{2} = empty_map && (forall (str : session_string), in_dom
(str,LHT{1}) => findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None && ( findelse_g_abs ( tested_session{1},str,
skey{1},seed{1}) <> None => tested_session{1}[ proj (findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str,skey{1}, seed{1}) <> None => G{1}[proj
(findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1},seed{1},LHT{1}, G{1}) &&
(forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) && in_dom (
str_0,LHT{2})))) && ={ h_0 }).
trivial.
app 50 50 ((bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) <=>
bad_op(tested_session{2}, skey{2}, seed{2}, LH{2},G{2})) && (
!bad_op(tested_session{1}, skey{1}, seed{1}, LH{1},G{1}) =>(
={b,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,tested_session,LH,G, res}
&& LHT{2} = empty_map && (forall ( str : session_string), in_dom (
str,LHT{1}) => findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None && ( findelse_g_abs ( tested_session{1}, str,skey{1},
seed{1}) <> None => tested_session{1}[ proj ( findelse_g_abs (
tested_session{1}, str,skey{1}, seed{1}))] = LHT{1}[str]) ||
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None && (
findelse_g_abs ( G{1},str, skey{1}, seed{1}) <> None => G{1}[ proj (
findelse_g_abs ( G{1},str, skey{1}, seed{1}))] = LHT{1}[str])) &&
link_tested_G_LHT( tested_session{1}, skey{1}, seed{1},LHT{1}, G{1})
&& ( forall ( str_0 : session_string), !(in_dom ( str_0,LH{2}) &&
in_dom (str_0,LHT{2})))))).
inline session_match.
*autosync.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
save.

equiv Fact2 : AKE2.Main ~ AKE3.Main : 
  true ==> ((bad_op(tested_session{1}, skey{1},seed{1},LH{1}, G{1}) <=> bad_op(tested_session{2}, skey{2},seed{2},LH{2}, G{2}))  
            && (! bad_op(tested_session{1}, skey{1},seed{1},LH{1}, G{1}) => ={res}))
by auto upto (bad_op(tested_session, skey,seed,LH, G))
 with 
 ((bad_op(tested_session{1}, skey{1}, seed{1}, LH{1}, G{1}) <=>
  bad_op(tested_session{2}, skey{2}, seed{2}, LH{2}, G{2})) &&
  ((! bad_op(tested_session{1}, skey{1}, seed{1}, LH{1}, G{1})) =>
(={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, tested_session, LH, G} )
&& LHT{2} = empty_map
 && (forall (str : session_string), in_dom(str, LHT{1}) => (findelse_g_abs(tested_session{1},str,skey{1},seed{1}) <> None  && (findelse_g_abs(tested_session{1},str,skey{1},seed{1}) <> None  =>tested_session{1}[proj(findelse_g_abs(tested_session{1},str,skey{1},seed{1}))] =  LHT{1}[str])) 
|| (findelse_g_abs(G{1},str,skey{1},seed{1}) <> None  && (findelse_g_abs(G{1},str,skey{1},seed{1}) <> None  =>G{1}[proj(findelse_g_abs(G{1},str,skey{1},seed{1}))] =  LHT{1}[str])))
&& link_tested_G_LHT(tested_session{1},skey{1},seed{1},LHT{1},G{1}) &&        (forall(str : session_string), ! (in_dom(str,LH{2}) && in_dom(str,LHT{2}))))).


claim Pr2 : |AKE2.Main[res] - AKE3.Main[res]| <= 
AKE3.Main[bad_op(tested_session, skey, seed, LH, G)] using Fact2.





