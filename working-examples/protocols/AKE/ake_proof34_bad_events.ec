include "ake_game4.ec".

pred link_tested_G_LHT 
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
forall (s : session_id),
in_dom(s,tested_session)
 =>
((in_dom(gen_session_string_sid(s,skey,seed), LHT)  && 
 LHT[gen_session_string_sid(s,skey,seed)] = tested_session[s])
 || (let sid' = findelse_sid_abs(G, s, skey, seed) in
         sid' <> None && G[proj(sid')] = tested_session[s])).

lemma link_update_skey :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : part,
           sk : secret_key),
link_tested_G_LHT(tested_session,skey,seed,LHT,G) && !in_dom(p, skey) => link_tested_G_LHT(tested_session,upd(skey,p,sk),seed,LHT,G).


lemma link_update_seed :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LHT : (session_string, session_key) map,
           G : (session_id, session_key) map,
           p : message * part,
           ek : eph_key),
link_tested_G_LHT(tested_session,skey,seed,LHT,G) && !in_dom(p, seed) => link_tested_G_LHT(tested_session,skey,upd(seed,p,ek),LHT,G).


pred guess_session_string
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
exists (s : session_id), (in_dom(s,tested_session) &&
in_dom(gen_session_string_sid(s,skey,seed),LH)).

pred test_key_reveal_collision 
          (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
exists (s : session_id), (in_dom(s,tested_session) && 
 findelse_sid_abs(G,s, skey,seed) <> None). 
 
pred bad (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) = 
guess_session_string(tested_session, skey,seed,LH, G) ||
test_key_reveal_collision(tested_session, skey,seed,LH, G).

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



op guess_session_string_op : 
  ((session_id, session_key) map, 
  (part, secret_key) map,
  (message * part, eph_key) map,
  (session_string, session_key) map,
  (session_id, session_key) map) ->
  bool.

axiom guess_session_string_op_def : 
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), guess_session_string(tested_session,skey,seed,LH, G) <=> guess_session_string_op(tested_session,skey,seed,LH, G).

op test_key_reveal_collision_op :
          ((session_id, session_key) map,
           (part, secret_key) map,
           ((message*part),eph_key) map,
           (session_string, session_key) map,
           (session_id, session_key) map) -> bool.


axiom test_key_reveal_collision_op_def :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), test_key_reveal_collision(tested_session,skey,seed,LH, G) <=> test_key_reveal_collision_op(tested_session,skey,seed,LH, G).

op bad_op (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map) =   test_key_reveal_collision_op(tested_session,skey,seed,LH, G) || guess_session_string_op(tested_session,skey,seed,LH, G).


lemma bad_op_def :
forall (tested_session : (session_id, session_key) map,
           skey : (part, secret_key) map,
           seed : ((message*part),eph_key) map,
           LH : (session_string, session_key) map,
           G : (session_id, session_key) map), bad(tested_session,skey,seed,LH, G) <=> bad_op(tested_session,skey,seed,LH, G).

