include "ake_game3.ec".


equiv INV_Main : AKE1.Main ~ AKE2.Main : 
(={s,b, bad, complete_sessions, incomplete_sessions, corrupt, pkey,
skey, seed, tested_session, G} &&
(forall(str : session_string), (in_dom(str,LH{2}) || in_dom(str,LHT{2})) <=> in_dom(str,LH{1})) &&
(forall(str : session_string), in_dom(str,LH{1}) => 
          ((LH{1}[str] = LH{2}[str] && in_dom(str,LH{2}) ) || (LH{1}[str] = LHT{2}[str] && in_dom(str,LHT{2})))) && 
(forall(str : session_string), ! (in_dom(str,LH{2}) && in_dom(str,LHT{2}))) && 
LHT{1} = empty_map &&
(forall (sid : session_id), in_dom(sid,tested_session{1}) =>
 (in_dom(gen_session_string_sid(sid,skey{1},seed{1}), LH{1}) ||
  findelse_sid_abs(G{1},sid,skey{1},seed{1}) <> None))) ==> ={res}.



equiv INV_Main : AKE1.Main ~ AKE2.Main : true ==> ={res} by auto 
(={b, bad, complete_sessions, incomplete_sessions, corrupt, pkey,
skey, seed, tested_session, G} &&
(forall(str : session_string), (in_dom(str,LH{2}) || in_dom(str,LHT{2})) <=> in_dom(str,LH{1})) &&
(forall(str : session_string), in_dom(str,LH{1}) => 
          ((LH{1}[str] = LH{2}[str] && in_dom(str,LH{2}) ) || (LH{1}[str] = LHT{2}[str] && in_dom(str,LHT{2})))) && 
(forall(str : session_string), ! (in_dom(str,LH{2}) && in_dom(str,LHT{2}))) && 
LHT{1} = empty_map &&
(forall (sid : session_id), in_dom(sid,tested_session{1}) =>
 (in_dom(gen_session_string_sid(sid,skey{1},seed{1}), LH{1}) ||
  findelse_sid_abs(G{1},sid,skey{1},seed{1}) <> None))).

claim Pr23 : AKE1.Main[res] = AKE2.Main[res] using INV_Main.

