type message.
type secret_key.
type public_key.
type part = public_key.
type key        = secret_key * public_key.

type session.
type eph_key.
type session_string.
type session_key.
type session_id = (part * part * message * message).

cnst dummy : secret_key.

pop gen_secret_key : () -> secret_key.

op gen_public_key : secret_key -> public_key.

axiom gpk_iny : forall (x1,x2 : secret_key),
                gen_public_key(x1) = gen_public_key(x2) => x1 = x2.


cnst dummy_session_key : session_key.
cnst dummy_session_string : session_string. 
cnst dummy_message : message. 
cnst dummy_eph_key : eph_key.
type msg_seed.
pop gen_msg_seed : () -> msg_seed.

(* unit *)

pop gen_session_key : () -> session_key. (* = gsk.*)


cnst dummy_session_id : session_id. (* remove *)

op dom : ('a, 'b) map -> 'a list.

axiom dom_def : forall (m : ('a,'b) map, x : 'a),
   in_dom(x,m) <=> mem(x,dom(m)).

op get_matching_session (s : session_id) =
let A,B,X,Y = s in (B,A,Y,X).

op mk_sid (X : part, Y : part, x : message, y : message) = (X, Y, x, y).

op fstpart(x : session_id) = let a,b,c,d = x in a.
op sndpart(x : session_id) = let a,b,c,d = x in b.
op fstmsg(x : session_id) = let a,b,c,d = x in c.
op sndmsg(x : session_id) = let a,b,c,d = x in d.

pop gen_eph_key : () -> eph_key.

op inp  : (secret_key, eph_key, msg_seed) -> message.
op out : (secret_key, eph_key, msg_seed) -> message.

op gen_session_string_sid : 
  (session_id, (part,   secret_key) map, (part * message, eph_key) map) -> session_string.

axiom gen_session_string_upd_skey : forall (sid : session_id, skey : (part,   secret_key) map, seed :(part * message, eph_key) map, p : part, sk : secret_key, str : session_string),
! in_dom(p, skey) && 
gen_session_string_sid(sid,skey,seed) = str =>
gen_session_string_sid(sid,upd(skey,p,sk),seed) = str.


axiom gen_session_string_upd_seed : forall (sid : session_id, skey : (part,   secret_key) map, seed :( part * message, eph_key) map, p : part * message, ek : eph_key, str : session_string),
! in_dom(p, seed) && 
gen_session_string_sid(sid,skey,seed) = str =>
gen_session_string_sid(sid,skey,upd(seed,p,ek)) = str.

type incomplete_session_with_status  = (part * message, part * bool) map.
type session_descr = (part * message * bool).

op mk_session_descr (x : part, y : message, b1 : bool, b2: bool) = 
(x,y,b1,b2). 
op session_part (x : session_descr) = let a,b,c = x in a.
op session_msg (x : session_descr) = let a,b,c = x in b.
op session_eph_flag (x : session_descr) = let a,b,c = x in c.

op same_session_string_abs  
(s : session_id , s' : session_id, skey : (part, secret_key) map, seed : (part * message, eph_key) map) = gen_session_string_sid(s, skey, seed) = gen_session_string_sid(s', skey, seed).



op eqS_abs : 
  (session_string,  session_id, (part, secret_key) map, (part * message, eph_key) map) -> bool.

axiom eqS_def1 :
forall 
  ( str : session_string,  
    sid : session_id, 
    skey : (part, secret_key) map, 
    seed : (part * message, eph_key) map), 
    eqS_abs(str,sid,skey,seed) =>
    gen_session_string_sid(sid,skey,seed)=str.

axiom eqS_def2 :
forall 
  ( str : session_string,  
    sid : session_id, 
    skey : (part, secret_key) map, 
    seed : (part * message, eph_key) map),
    gen_session_string_sid(sid,skey,seed)=str => eqS_abs(str,sid,skey,seed).

op findelse_sid_abs : ((session_id, session_key) map,  session_id,(part, secret_key) map, (part * message, eph_key) map) -> session_id option.

axiom findelse_sid_abs_none1:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
findelse_sid_abs(m',s',skey',seed') = None =>
(forall (x : session_id), in_dom(x,m') => same_session_string_abs(x,s',skey',seed') = false ).

axiom findelse_sid_abs_none2:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
(forall (x : session_id), in_dom(x,m') => same_session_string_abs(x,s',skey',seed') = false) =>
findelse_sid_abs(m',s',skey',seed') = None.

axiom findelse_sid_abs_some:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map,
        opres : session_id option),
( findelse_sid_abs(m',s',skey',seed') = opres  &&  opres <> None ) =>
( same_session_string_abs(proj(opres),s',skey',seed') &&  in_dom(proj(opres),m') ).

(* YL 1/01/2012: The following axiom should be a Lemma and its necessity has to be checked. *)
axiom findelse_sid_abs_ident:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
findelse_sid_abs(m',s',skey',seed') <> None => upd(m', s', m'[proj(findelse_sid_abs(m',s',skey',seed'))]) = m'.

axiom findelse_sid_skey_update :
forall (m :  (session_id, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p : part,
        sk : secret_key),
!in_dom(p,skey) =>
findelse_sid_abs(m,sid,skey,seed) = findelse_sid_abs(m,sid,upd(skey,p,sk),seed).


axiom findelse_sid_seed_update :
forall (m :  (session_id, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p :  part * message,
        ek : eph_key),
!in_dom(p,seed) =>
findelse_sid_abs(m,sid,skey,seed) = findelse_sid_abs(m,sid,skey,upd(seed,p,ek)).


op findelse_g_abs : ((session_id, session_key) map ,  session_string, (part, secret_key) map, (part * message, eph_key) map) -> session_id option.

axiom findelse_g_abs_none_1:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
	(forall (sid : session_id), in_dom(sid,m') => !eqS_abs(str,sid,skey',seed') )
 	 => findelse_g_abs(m',str,skey',seed') = None.

axiom findelse_g_abs_none_2:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
findelse_g_abs(m',str,skey',seed') = None 
  => 
(forall (sid : session_id), in_dom(sid,m') => !eqS_abs(str,sid,skey',seed')).

axiom findelse_g_abs_some:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map,
        res : session_id option),
( findelse_g_abs(m',str,skey',seed') = res  && res <> None) =>
 (eqS_abs(str,proj(res),skey',seed') && in_dom(proj(res),m')).

axiom findelse_g_update_1 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        sid : session_id,
        sesskey : session_key),
gen_session_string_sid(sid,skey,seed) = str => findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) <> None.

axiom findelse_g_update_2 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        sid : session_id,
        sesskey : session_key),
( gen_session_string_sid(sid,skey,seed) <>  str &&  findelse_g_abs(m, str, skey, seed) <> None ) => 
findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) <> None.


(* JM: this axiom should be a lemma*)
axiom findelse_sid_g_skey_update :
 forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p : part,
        sk : secret_key),
 !in_dom(p,skey) =>
 findelse_g_abs(m,str,skey,seed) = findelse_g_abs(m,str,upd(skey,p,sk),seed).


axiom findelse_sid_g_seed_update :
forall (m :  (session_id, session_key) map,
        sid : session_id,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p : part,
        X : message,
        e : eph_key),
 !in_dom((p,X),seed)  =>
 findelse_g_abs(m,str,skey,seed) = findelse_g_abs(m,str,skey,upd(seed, (p, X), e)).


axiom findelse_sid_g :
forall (m :  (session_id, session_key) map, 
        sid : session_id,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map),
gen_session_string_sid(sid,skey,seed) = str =>  findelse_sid_abs(m,sid,skey,seed) = findelse_g_abs(m,str,skey,seed) .



axiom findelse_sid_g2 : (*YL : added 1/1/2012 validity and necessity to be checked*)
forall (m :  (session_id, session_key) map, 
        sid : session_id,
	sid': session_id,
	opsid : session_id option,
        fer_sid : session_id option,
          h : session_key,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map),
(findelse_g_abs(upd(upd(m,sid,h),sid',h),str,skey,seed) = opsid && 
 findelse_sid_abs(m,sid,skey,seed) = fer_sid &&
 opsid <> fer_sid) => ( findelse_g_abs(m,str,skey,seed) = opsid &&
  	   	     	  upd(upd(m,sid,h),sid',h)[proj(opsid)] = m[proj(opsid)]).




op findelse_h_abs : ((session_string, session_key) map ,  session_id,(part, secret_key) map, (part * message, eph_key) map) -> session_string option.


axiom findelse_h_abs_None_1:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
 findelse_h_abs(m',sid,skey',seed') = None  =>
(forall (str : session_string), in_dom(str,m') => 
!eqS_abs(str,sid,skey',seed') ).

axiom findelse_h_abs_None_2:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map),
(forall (str : session_string), in_dom(str,m') => 
!eqS_abs(str,sid,skey',seed') ) =>
 findelse_h_abs(m',sid,skey',seed') = None .

axiom findelse_h_abs_some:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (part * message, eph_key) map,
        str : session_string option ),
( findelse_h_abs(m',sid,skey',seed') = str  &&  str <> None) =>
 (eqS_abs(proj(str),sid,skey',seed') &&  in_dom(proj(str),m')  ).

axiom findelse_sid_h_skey_update :
forall (m :  (session_string, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p : part,
        sk : secret_key),
 !in_dom(p,skey) =>
 findelse_h_abs(m,sid,skey,seed) = findelse_h_abs(m,sid,upd(skey,p,sk),seed).


axiom findelse_sid_h_seed_update :
forall (m :  (session_string, session_key) map,
        sid : session_id,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        p : part,
        X : message,
        e : eph_key),
 !in_dom((p,X),seed)  =>
 findelse_h_abs(m,sid,skey,seed) = findelse_h_abs(m,sid,skey,upd(seed, (p, X), e)).


axiom findelse_h_eqS:
forall (m :  (session_string, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        str : session_string option ),
( findelse_h_abs(m,sid,skey,seed) = str  &&  str <> None) =>
(gen_session_string_sid(sid,skey,seed) = proj(str) &&  in_dom(proj(str),m) ).

(*( findelse_h_abs(m,sid,skey,seed) = str  &&  str <> None) =>
( gen_session_string(skey[fstpart(sid)],seed[(fstmsg(sid),fstpart(sid))],sndpart(sid),sndmsg(sid)) = proj(str) &&  in_dom(proj(str),m) )*)

(*
axiom isSome_id_ax : forall (x : session_id), isSome_id(Some(x)) = true.
axiom isSome_string_ax : forall (x : session_string), isSome_string(some(x)) = true.
*)

axiom findelse_g_update3 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        sid : session_id,
        sesskey : session_key),
str <> gen_session_string_sid(sid,skey,seed) => 
findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) = findelse_g_abs(m, str, skey, seed).

axiom findelse_h_update_2 : 
forall (m :  (session_string, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (part * message, eph_key) map,
        sesskey : session_key,
        str : session_string),
str <> gen_session_string_sid(sid,skey,seed) => 
findelse_h_abs(upd(m,str,sesskey), sid, skey, seed) = findelse_h_abs(m, sid, skey, seed).



type complete_session_with_status =  (part * message, session_descr) map.

cnst dummy_part : part.
cnst dummy_msg : message.
cnst dummy_string : session_string.
cnst dummy_sid : session_id.

(* JM Axiom about inequality of matching sessions and
   about equality of genereated strings of matching sessions
*)

axiom match_string_eq :
forall (s : session_id,s' : session_id, 
        skey : (part, secret_key) map, 
        seed : (part * message, eph_key) map),
s = mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s')) =>
 gen_session_string_sid(s,skey,seed) = gen_session_string_sid(s',skey,seed).

axiom get_upd_map_jm :
  forall (m: ('a,'b) map, a1, a2 : 'a, b: 'b, c : 'b),
    ((a1 = a2 => b = c) &&
    (a1 <> a2 => m[a2] = c))
    => m[a1<-b][a2] = c. 

op session_match (s : session_id, s' : session_id) =
(s = mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s'))).

(*
axiom in_dom_upd_map_jm :
  forall (m: ('a,'b) map, a1, a2 : 'a, b: 'b, c : 'b),
    ((a1 = a2) ||
    (a1 <> a2 => in_dom(a2,m)))
    => in_dom(a2,m[a1<-b]). 
*)

pred completed(sid : session_id, 
               complete_session : complete_session_with_status) =
let A,B,X,Y = sid in
(in_dom((A,X), complete_session) && 
 let B', Y',flag1 = complete_session[(A,X)] in
 B = B' && Y = Y').

pred fresh_sid1(sid : session_id,
                corrupt : (part, bool) map,
                complete_session : complete_session_with_status,
                incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
!corrupt[B] && corrupt[A] && 
((in_dom((A,X),complete_session) && !session_eph_flag(complete_session[(A,X)]))).

pred fresh_sid11(sid : session_id,
                 corrupt : (part, bool) map,
                 complete_session : complete_session_with_status,
                 incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
corrupt[B] && !corrupt[A] && 
((in_dom((B,Y),complete_session) && !session_eph_flag(complete_session[(B,Y)])) ||
(in_dom((B,Y),incomplete_session) && !snd(incomplete_session[(B,Y)]))).


pred fresh_sid2(sid :session_id,
                corrupt : (part, bool) map) =
let A,B,X,Y = sid in
!corrupt[A] && !corrupt[B].


pred fresh_sid3(sid : session_id,
                corrupt : (part, bool) map,
                complete_session : complete_session_with_status,
                incomplete_session : incomplete_session_with_status) =
let A,B,X,Y = sid in
corrupt[A] && corrupt[B] &&
(in_dom((A,X),complete_session) && !session_eph_flag(complete_session[(A,X)])) &&
((in_dom((B,Y),complete_session) && !session_eph_flag(complete_session[(B,Y)])) ||
(in_dom((B,Y),incomplete_session) && !snd(incomplete_session[(B,Y)]))).



(* || *)
(* (in_dom((A,X),complete_session) && in_dom((B,Y),incomplete_session) && !session_eph_flag(complete_session[(B,Y)]) && !session_eph_flag(complete_session[(A,X)])) *)
pred fresh_sid(sid : session_id,
               corrupt : (part, bool) map,
               complete_session : complete_session_with_status,
               incomplete_session : incomplete_session_with_status) =
(fresh_sid1(sid,corrupt,complete_session,incomplete_session) ||
fresh_sid11(sid,corrupt,complete_session,incomplete_session) ||
fresh_sid2(sid,corrupt) ||
fresh_sid3(sid,corrupt,complete_session,incomplete_session)) && completed(sid,complete_session).

op fresh_sid_op : (session_id,(part, bool) map,complete_session_with_status,
incomplete_session_with_status) -> bool.

axiom fresh_sid_def : 
forall (sid : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid_op(sid, corrupt , complete_session,incomplete_session) <=>
fresh_sid(sid, corrupt , complete_session,incomplete_session).

pred fresh(tested_sessions : (session_id, session_key) map,
           corrupt : (part, bool) map,
           complete_session : complete_session_with_status,
           incomplete_session : incomplete_session_with_status) =
forall (sid :session_id), in_dom(sid,tested_sessions) => 
fresh_sid(sid,corrupt,complete_session,incomplete_session) && 
fresh_sid(get_matching_session(sid),corrupt,complete_session,incomplete_session) .

pred fresh_sid'(sid : session_id,
               corrupt : (part, bool) map,
               complete_session : complete_session_with_status,
               incomplete_session : incomplete_session_with_status) =
completed(sid, complete_session) &&
(let A,B,X,Y = sid in
(corrupt[A] => (in_dom((A,X),complete_session)&& !session_eph_flag(complete_session[(A,X)]))) &&
(corrupt[B] => (in_dom((B,Y),complete_session)&& !session_eph_flag(complete_session[(B,Y)])) ||
              (in_dom((B,Y),incomplete_session) && !snd(incomplete_session[(B,Y)])))). 
(*
lemma asd : 
forall (sid : session_id,
        corrupt : (part, bool) map,
        complete_session : complete_session_with_status,
        incomplete_session : incomplete_session_with_status),
fresh_sid(sid,corrupt,complete_session,incomplete_session) <=>
fresh_sid'(sid,corrupt,complete_session,incomplete_session).
*)
op fresh_sid3_op : (session_id, (part, bool) map,complete_session_with_status,incomplete_session_with_status) -> bool.
 
axiom fresh3_def : 
forall (sid : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid3_op(sid, corrupt , complete_session,incomplete_session) <=>
fresh_sid3(sid, corrupt , complete_session,incomplete_session).

op fresh_sid2_op : (session_id, (part, bool) map) -> bool.
 
axiom fresh2_def : 
forall (sid : session_id,
 corrupt : (part, bool) map),
fresh_sid2_op(sid, corrupt) <=>fresh_sid2(sid, corrupt).

op fresh_sid1_op : (session_id, (part, bool) map,complete_session_with_status,incomplete_session_with_status) -> bool.
 
axiom fresh1_def : 
forall (sid : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid1_op(sid, corrupt , complete_session,incomplete_session) <=>
fresh_sid1(sid, corrupt , complete_session,incomplete_session).

op fresh_sid11_op : (session_id, (part, bool) map,complete_session_with_status,incomplete_session_with_status) -> bool.

axiom fresh11_def : 
forall (sid : session_id,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh_sid11_op(sid, corrupt , complete_session,incomplete_session) <=>
fresh_sid11(sid, corrupt , complete_session,incomplete_session).


op fresh_op : ((session_id, session_key) map,(part, bool) map,complete_session_with_status,incomplete_session_with_status)-> bool.

axiom fresh_def :
 forall (tested_sessions : (session_id, session_key) map,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status),
fresh(tested_sessions,corrupt, complete_session,incomplete_session) <=>
fresh_op(tested_sessions,corrupt, complete_session,incomplete_session).


op completed(s : session_id, cs : complete_session_with_status) =
let A,B,X,Y = s in
in_dom((A,X),cs) && in_dom((B,Y),cs).

cnst qPart : int.
cnst qSess : int.

axiom qPart_range : qPart > 1.
axiom qSess_range : qSess > 0.
