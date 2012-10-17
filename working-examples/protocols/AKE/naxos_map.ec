type session
//type status //status, includes a bottom value
type secret_key
type public_key

type part = public_key

cnst dummy : secret_key

pop gen_secret_key : int -> secret_key;;


op gen_public_key : secret_key -> public_key = gpk

type key        = secret_key * public_key
type message
type session_string
type session_key
cnst dummy_session_key : session_key
cnst dummy_session_string : session_string // remove
cnst dummy_message : message // remove

pop gen_session_key : int -> session_key // = gsk;;

type session_id // = (part * (part * (message * message)))
cnst dummy_session_id : session_id // remove
op mk_sid : part, part, message, message -> session_id = mk_sid
op fstpart : session_id -> part = fstpart
op sndpart : session_id -> part = sndpart
op fstmsg : session_id -> message = fstmsg
op sndmsg : session_id -> message = sndmsg;;

axiom part_eq_dec : 
forall (p1 : part, p2 : part). { p1 == p2 } \/ { p1 <> p2 };;

axiom message_eq_dec : 
forall (m1 : message, m2 : message). { m1 == m2 } \/ { m1 <> m2 };;

axiom session_string_eq_dec : 
forall (str1 : session_string, str2 : session_string). {str1 == str2} \/ {str1 <> str2}


axiom session_neq_sym : 
forall (str1 : session_string, str2 : session_string). {str1 <> str2} => {str2 <> str1}
    
lemma session_id_eq_dec : 
forall (sid1 : session_id, sid2 : session_id). {sid1 == sid2} \/ {sid1 <> sid2}

lemma session_id_neq_sym : 
forall (sid1 : session_id, sid2 : session_id). {sid1 <> sid2} => {sid2 <> sid1}

op isSome_id : session_id option -> bool = isSome_id

axiom isSome_id_def : forall (x : session_id option) . 
      {isSome_id(x)} <=> {x <> none }

axiom isSome_id_def1 : forall (x : session_id) . 
      {isSome_id(some(x)) == true}


axiom isSome_none : {isSome_id(none) == false}

axiom isSome_some : forall (x : session_id option).
{isSome_id(x) == true} => (exists (y : session_id). { x == some(y) })

op isSome_string : session_string option -> bool = isSome_string

axiom isSome_string_def : forall (x : session_string option) . {isSome_string(x)} <=> {x <> none }

axiom isSome_string_some : forall (x : session_string option).
({isSome_string(x) == true} => 
(exists (y : session_string). { x == some(y) }))


axiom isSome_string_none : {isSome_string(none) == false}

axiom session_id_proj :
forall (s: session_id). { mk_sid(fstpart(s),sndpart(s),fstmsg(s),sndmsg(s)) == s }

axiom session_id_proj_fstpart :
forall (A : part, B: part, X : message, Y : message).
{ fstpart(mk_sid(A,B,X,Y)) == A }

axiom session_id_proj_sndpart :
forall (A : part, B: part, X : message, Y : message).
{ sndpart(mk_sid(A,B,X,Y)) == B }

axiom session_id_proj_fstmsg :
forall (A : part, B: part, X : message, Y : message).
{ fstmsg(mk_sid(A,B,X,Y)) == X }

axiom session_id_proj_sndmsg :
forall (A : part, B: part, X : message, Y : message).
{ sndmsg(mk_sid(A,B,X,Y)) == Y }

axiom session_id_eq : 
forall (s: session_id,s': session_id). {(s == s') == ((fstpart(s) == fstpart(s'))
  && (sndpart(s) == sndpart(s')) && (fstmsg(s) == fstmsg(s')) && (sndmsg(s) == sndmsg(s')))}

axiom G_eq :
forall (m: (session_id, session_key) map, a: session_id, b: session_key, sid: session_id, k: session_key).
       	   ({upd(m,a,b)[sid] == k}) 
	   <=> 
	   ({sid == a && (b == k)} \/ {sid <> a && (m[sid] == k)})

/* alternative definition for match
op session_match : session_id,session_id -> bool = session_match

axiom session_match_abs :
forall (sid : session_id, sid' : session_id).
{session_match(sid,sid') == true} <=> {(fstpart(sid) == sndpart(sid'))
&& (fstmsg(sid) == sndmsg(sid')) && (fstpart(sid') == sndpart(sid)) &&
(fstmsg(sid') == sndmsg(sid)) }
*/

// POV of A
type eph_key
pop gen_eph_key : int -> eph_key;;

op inp  : secret_key, eph_key -> message = inp
op out_noclash : secret_key, eph_key -> message = out_noclash


type session_num_and_partner   = part * message

op gen_session_string : secret_key, eph_key, part, message ->
session_string = gen_session_string

/*
axiom gen_session_string_inj : 
forall (sk1 : secret_key, 
        eph1 : eph_key,
        p1 : part, 
        m1 : message,
        sk2 : secret_key, 
        eph2 : eph_key,
        p2 : part, 
        m2 : message). 
{gen_session_string(sk1,eph1,p1,m1) == gen_session_string(sk2,eph2,p2,m2)} =>
( { sk1 == sk2 } /\ { eph1 == eph2 } /\ { p1 == p2 } /\ { m1 == m2 }) 
*/
op gen_session_string_sid : 
  session_id, (part,   secret_key) map, (message * part, eph_key) map -> session_string = gen_session_string_sid
axiom gen_session_string_sid_abs :
forall (sid : session_id, skey : (part,   secret_key) map, seed :
  (message * part, eph_key) map).
{gen_session_string_sid(sid,skey,seed)==gen_session_string(skey[fstpart(sid)],seed[(fstmsg(sid),fstpart(sid))],sndpart(sid),sndmsg(sid))}

/*
axiom gen_session_string_sid_inj :
forall (sid : session_id,sid' : session_id, skey : (part,secret_key) map, seed : (message * part, eph_key) map).
{gen_session_string_sid(sid,skey,seed)==gen_session_string_sid(sid',skey,seed)}
=> ({sid == sid'})
/* \/ {(fstpart(sid) == sndpart(sid'))
&& (fstmsg(sid) == sndmsg(sid')) && (fstpart(sid') == sndpart(sid)) &&
(fstmsg(sid') == sndmsg(sid)) })*/
// must be added \/ {session_match(sid,sid') == true})
*/
// Sessions with status
// the bool represents eph key reveal

type incomplete_session_with_status  = (session_num_and_partner, part * bool) map 
type session_descr // = (part * (message * (bool * (bool * bool))))
op mk_session_descr : part, message, bool, bool, bool -> session_descr = mk_session_descr
op session_part : session_descr -> part = session_part
op session_msg : session_descr -> message = session_msg
op session_eph_flag : session_descr -> bool = session_eph_flag
op session_key_reveal_flag : session_descr -> bool = session_key_reveal_flag
op session_test_flag : session_descr -> bool = session_test_flag

axiom session_descr_proj :
forall (s: session_descr). 
    { mk_session_descr(session_part(s),session_msg(s),
      session_eph_flag(s),session_key_reveal_flag(s), session_test_flag(s)) == s }


axiom session_descr_part : 
forall (A : part, X : message, ef : bool, krf : bool, tf : bool).
{ session_part(mk_session_descr(A,X,ef,krf,tf)) == A}

axiom session_descr_msg : 
forall (A : part, X : message, ef : bool, krf : bool, tf : bool).
{ session_msg(mk_session_descr(A,X,ef,krf,tf)) == X}

axiom session_descr_eph : 
forall (A : part, X : message, ef : bool, krf : bool, tf : bool).
{ session_eph_flag(mk_session_descr(A,X,ef,krf,tf)) == ef}

axiom session_descr_key_reveal_flag : 
forall (A : part, X : message, ef : bool, krf : bool, tf : bool).
{ session_key_reveal_flag(mk_session_descr(A,X,ef,krf,tf)) == krf}

axiom session_descr_test_flag : 
forall (A : part, X : message, ef : bool, krf : bool, tf : bool).
{ session_test_flag(mk_session_descr(A,X,ef,krf,tf)) == tf}

axiom session_descr_eq : 
forall (s: session_descr,s': session_descr). {(s == s') == ((session_part(s) == session_part(s'))
  && (session_msg(s) == session_msg(s')) && (session_eph_flag(s) == session_eph_flag(s')) && 
     (session_key_reveal_flag(s) == session_key_reveal_flag(s')) && (session_test_flag(s)== session_test_flag(s')))}

op same_session_string_abs : 
session_id , session_id, (part, secret_key) map, (message * part, eph_key) map  -> bool = same_session_string_abs


axiom same_string_def1 :
forall (sid : session_id, 
        sid' : session_id, 
        skey : (part, secret_key) map, 
        seed : (message * part, eph_key) map).
{same_session_string_abs(sid,sid',skey,seed) } =>
{gen_session_string_sid(sid,skey,seed)==gen_session_string_sid(sid',skey,seed)}

axiom same_string_def2 :
forall (sid : session_id, 
        sid' : session_id, 
        skey : (part, secret_key) map, 
        seed : (message * part, eph_key) map).
{gen_session_string_sid(sid,skey,seed)==gen_session_string_sid(sid',skey,seed)} =>
{same_session_string_abs(sid,sid',skey,seed) }

op eqS_abs : 
  session_string,  session_id, (part, secret_key) map, (message* part, eph_key) map -> bool = eqS_abs

axiom eqS_def1 :
forall 
  ( str : session_string,  
    sid : session_id, 
    skey : (part, secret_key) map, 
    seed : (message* part, eph_key) map). 
    { eqS_abs(str,sid,skey,seed) } =>
    {gen_session_string_sid(sid,skey,seed)==str}

axiom eqS_def2 :
forall 
  ( str : session_string,  
    sid : session_id, 
    skey : (part, secret_key) map, 
    seed : (message* part, eph_key) map).
    {gen_session_string_sid(sid,skey,seed)==str} => { eqS_abs(str,sid,skey,seed) }



op findelse_sid_abs : (session_id, session_key) map,  session_id,(part, secret_key) map, (message * part, eph_key) map -> session_id option = findelse_sid_abs

axiom findelse_sid_abs_none1:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
{ findelse_sid_abs(m',s',skey',seed') == none } =>
(forall (x : session_id). {in_dom(x,m')} => {!same_session_string_abs(x,s',skey',seed')} )

axiom findelse_sid_abs_none2:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
(forall (x : session_id). {in_dom(x,m')} => {!same_session_string_abs(x,s',skey',seed')} ) =>
{ findelse_sid_abs(m',s',skey',seed') == none } 


axiom findelse_sid_abs_some:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map,
        opres : session_id option).
({ findelse_sid_abs(m',s',skey',seed') == opres } /\ { opres <> none }) =>
( {same_session_string_abs(proj(opres),s',skey',seed')} /\ { in_dom(proj(opres),m') })

// YL 1/01/2012: The following axiom should be a Lemma and its necessity has to be checked.
axiom findelse_sid_abs_ident:
forall (m' :  (session_id, session_key) map,
        s' : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
{findelse_sid_abs(m',s',skey',seed') <> none } => {upd(m', s', m'[proj(findelse_sid_abs(m',s',skey',seed'))]) == m'}

op findelse_g_abs : (session_id, session_key) map ,  session_string, (part, secret_key) map, (message * part, eph_key) map -> session_id option = findelse_g_abs

axiom findelse_g_abs_none_1:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
	(forall (sid : session_id). {in_dom(sid,m')} => {!eqS_abs(str,sid,skey',seed')} )
 	 =>
	{ findelse_g_abs(m',str,skey',seed') == none }

axiom findelse_g_abs_none_2:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
{ findelse_g_abs(m',str,skey',seed') == none } 
  => 
(forall (sid : session_id). {in_dom(sid,m')} => {!eqS_abs(str,sid,skey',seed')} )

axiom findelse_g_abs_some:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map,
        res : session_id option).
({ findelse_g_abs(m',str,skey',seed') == res } /\ {res <> none}) =>
 {eqS_abs(str,proj(res),skey',seed')} /\ { in_dom(proj(res),m') } 

/*
axiom findelse_g_abs_some_2:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map,
        res : session_id option).
( {eqS_abs(str,proj(res),skey',seed')} /\ { in_dom(proj(res),m') } )
 =>
(exists (res' : session_id option).{findelse_g_abs(m',str,skey',seed') == res' } /\ {res' <> none})

/*axiom findelse_g_abs_ident:
forall (m' :  (session_id, session_key) map,
        str : session_string,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
{ findelse_g_abs(m',str,skey',seed') <> none} => {upd(m',proj(findelse_g_abs(m',str,skey',seed')),m'[proj(findelse_g_abs(m',str,skey',seed'))]) == m'}*/
*/

axiom findelse_g_update_1 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        sid : session_id,
        sesskey : session_key).
{gen_session_string_sid(sid,skey,seed) == str} => {findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) <> none}

lemma findelse_g_update_2 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        sid : session_id,
        sesskey : session_key).
({ gen_session_string_sid(sid,skey,seed) <>  str} /\  { findelse_g_abs(m, str, skey, seed) <> none }) => 
{findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) <> none}


// JM: this axiom should be a lemma
axiom findelse_sid_g_skey_update :
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        p : part,
        sk : secret_key).
{ !in_dom(p,skey)} =>
{ findelse_g_abs(m,str,skey,seed) == findelse_g_abs(m,str,upd(skey,p,sk),seed)}


axiom findelse_sid_g_seed_update :
forall (m :  (session_id, session_key) map,
        sid : session_id,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        p : part,
        X : message,
        e : eph_key).
{ !in_dom((X,p),seed) } =>
{ findelse_g_abs(m,str,skey,seed) == findelse_g_abs(m,str,skey,upd(seed, (X, p), e))}


axiom findelse_sid_g :
forall (m :  (session_id, session_key) map, 
        sid : session_id,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map).
{gen_session_string_sid(sid,skey,seed) == str} => { findelse_sid_abs(m,sid,skey,seed) == findelse_g_abs(m,str,skey,seed) }



axiom findelse_sid_g2 : // YL : added 1/1/2012 validity and necessity to be checked
forall (m :  (session_id, session_key) map, 
        sid : session_id,
	sid': session_id,
	opsid : session_id option,
        fer_sid : session_id option,
          h : session_key,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map).
({findelse_g_abs(upd(upd(m,sid,h),sid',h),str,skey,seed) == opsid} /\ 
 {findelse_sid_abs(m,sid,skey,seed) == fer_sid} /\
 {opsid <> fer_sid}) => ( {findelse_g_abs(m,str,skey,seed) == opsid} /\
  	   	     	  {upd(upd(m,sid,h),sid',h)[proj(opsid)] == m[proj(opsid)]})




op findelse_h_abs : (session_string, session_key) map ,  session_id,(part, secret_key) map, (message * part, eph_key) map -> session_string option = findelse_h_abs;;


axiom findelse_h_abs_none_1:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
{ findelse_h_abs(m',sid,skey',seed') == none } =>
(forall (str : session_string). {in_dom(str,m')} => 
{!eqS_abs(str,sid,skey',seed')} )

axiom findelse_h_abs_none_2:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map).
(forall (str : session_string). {in_dom(str,m')} => 
{!eqS_abs(str,sid,skey',seed')} ) =>
{ findelse_h_abs(m',sid,skey',seed') == none }

axiom findelse_h_abs_some:
forall (m' :  (session_string, session_key) map,
        sid : session_id,
        skey' : (part, secret_key) map,
        seed' : (message * part, eph_key) map,
        str : session_string option ).
({ findelse_h_abs(m',sid,skey',seed') == str } /\ { str <> none}) =>
 ({eqS_abs(proj(str),sid,skey',seed')} /\ { in_dom(proj(str),m') } )


axiom findelse_h_eqS:
forall (m :  (session_string, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        str : session_string option ).
({ findelse_h_abs(m,sid,skey,seed) == str } /\ { str <> none}) =>
({gen_session_string_sid(sid,skey,seed) == proj(str)} /\ { in_dom(proj(str),m) })

/*({ findelse_h_abs(m,sid,skey,seed) == str } /\ { str <> none}) =>
( {gen_session_string(skey[fstpart(sid)],seed[(fstmsg(sid),fstpart(sid))],sndpart(sid),sndmsg(sid)) == proj(str)} /\ { in_dom(proj(str),m) })*/

axiom isSome_id_ax : forall (x : session_id) . {isSome_id(some(x)) == true}
axiom isSome_string_ax : forall (x : session_string) . {isSome_string(some(x)) == true}

axiom findelse_g_update3 : 
forall (m :  (session_id, session_key) map,
        str : session_string,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        sid : session_id,
        sesskey : session_key).
{str <> gen_session_string_sid(sid,skey,seed)} => 
  {findelse_g_abs(upd(m,sid,sesskey), str, skey, seed) == findelse_g_abs(m, str, skey, seed)}

axiom findelse_h_update_2 : 
forall (m :  (session_string, session_key) map,
        sid : session_id,
        skey : (part, secret_key) map,
        seed : (message * part, eph_key) map,
        sesskey : session_key,
        str : session_string).
{str <> gen_session_string_sid(sid,skey,seed)} => 
  {findelse_h_abs(upd(m,str,sesskey), sid, skey, seed) == findelse_h_abs(m, sid, skey, seed)}



type complete_session_with_status =  (session_num_and_partner, session_descr) map  
;;

cnst dummy_part : part
cnst dummy_msg : message
cnst dummy_string : session_string
cnst dummy_sid : session_id

// JM Axiom about inequality of matching sessions and
// about equality of genereated strings of matching sessions

axiom match_neq :
forall (s : session_id, s' : session_id).
{s == mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s'))} =>
{ s <> s'} 
 
axiom match_string_eq :
forall (s : session_id,s' : session_id, skey : (part, secret_key) map, seed : (message * part, eph_key) map).
{s == mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s'))} =>
{ gen_session_string_sid(s,skey,seed) == gen_session_string_sid(s',skey,seed)} 

// Declaration of adversaries
adversary A () : bool  
{
  unit -> public_key;
  part, part -> message;
  part, part, message -> message;
  part, part, message, message -> unit;
  part -> secret_key;
  session_id -> session_key;
  session_string -> session_key
} 

game AKE = {
 var b : bool
 var complete_sessions : complete_session_with_status
 var incomplete_sessions : incomplete_session_with_status
 var corrupt  : (part, bool) map
 var pkey     : (part, public_key) map
 var skey     : (part, secret_key) map
 var LH       : (session_string, session_key) map
 var seed     : (message * part, eph_key) map
 var G : (session_id, session_key) map


 fun KG(x:unit) : public_key = {
  var sk : secret_key = gen_secret_key(0);
  var pk : public_key = gen_public_key(sk);
  if (!in_dom(pk,skey)) 
  {
    corrupt[pk] = false;
    skey[pk] = sk;
  };
  return pk;
} 


 fun H(lam:session_string) : session_key = {
  var h : session_key = gen_session_key(0);
  if (!in_dom(lam, LH)) { LH[lam] = h; };
  return LH[lam];
 }
 
 fun iH(lam:session_string,h : session_key) : session_key = {
  if (!in_dom(lam, LH)) { LH[lam] = h; };
  return LH[lam];
} 

 fun Init(A:part, B:part) : message = {
  var x : eph_key = gen_eph_key(0);
  var a : secret_key;
  var X : message;
  if (in_dom(A, skey) && in_dom(B, skey)){
   a = skey[A];
   X = out_noclash(a, x);
   if (!in_dom((X,A), seed)) {
    incomplete_sessions[(A,X)] = (B,false);
    seed[(X,A)] = x;
   }
  else 
  {
   X = dummy_message;
  }
 }
 else {
  X = dummy_message;
 }
  return X;
 }

 fun Respond(B:part, A:part, X: message) : message = {
  var y : eph_key = gen_eph_key(0);  
  var Y : message = inp(skey[B], y);
  if (!in_dom((Y,B), seed) && in_dom(A, skey) && in_dom(B, skey)) {
  complete_sessions[(B,Y)] = mk_session_descr(A, X, false, false,false);
  seed[(Y, B)] = y;
  }
  else {
   Y = dummy_message;
  }
  return Y;
 }

 fun Complete(A:part, B:part, X:message, Y:message) : unit = {
   var x : eph_key = seed[(X,A)];
   var B' : part;
   var eph_flag : bool;
   if (in_dom((A,X), incomplete_sessions)) {
     B' = fst(incomplete_sessions[(A,X)]);
     eph_flag = snd(incomplete_sessions[(A,X)]);
     if (B' == B && !in_dom((A,X), complete_sessions)) {
       complete_sessions[(A,X)] = mk_session_descr(B,Y,eph_flag,false,false);
       //get rid of the session in incomplete
     };
   };
   return;
 }

 fun Corrupt(A : part) : secret_key = {
   var a : secret_key = dummy;
   if (in_dom(A,skey))
   {
     corrupt[A] = true;
     a = skey[A];
   };
   return a;
 }



 fun session_match (s : session_id, s' : session_id) : bool =
 {
   return (s == mk_sid (sndpart(s'), fstpart(s'), sndmsg(s'), fstmsg(s')));
 }



 fun KeyReveal(s : session_id) : session_key = { 
   var A:part = fstpart(s);
   var B:part = sndpart(s);
   var X:message = fstmsg(s);
   var Y:message = sndmsg(s);
   var x : eph_key = seed[(X,A)];
   var B' : part = dummy_part;
   var Y' : message = dummy_msg;
   var test_flagA : bool = false;
   var test_flagB : bool = false;
   var eph_flagA : bool = false;
   var eph_flagB : bool = false;
   var A' : part = dummy_part;
   var X' : message = dummy_msg;
   var sstr : session_string = dummy_string;
   var ssskey : session_key = dummy_session_key;
   var matchb : bool = false;
   var h : session_key = dummy_session_key;
   var sidA, sidB : session_id;
   h = gen_session_key(0);
   if (in_dom((A,X), complete_sessions)) 
   { // (A,_,X,_) is completed
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     sidA = mk_sid(A, B', X, Y');
     eph_flagA = session_eph_flag(complete_sessions[(A,X)]);
     test_flagA = session_test_flag(complete_sessions[(A,X)]);    
     if ( B == B' && Y == Y') 
     {// B == B' /\ Y == Y'
     if (in_dom((B,Y), complete_sessions)) 
      { //B,_,Y_ complete 
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B, A', Y, X');
       matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
       if ( matchb ) 
       { // matches
         test_flagB = session_test_flag(complete_sessions[(B,Y)]);
	 eph_flagB = session_eph_flag(complete_sessions[(B,Y)]);
         if (! test_flagA && ! test_flagB )
         {// fresh
           complete_sessions[(B,Y)] = mk_session_descr(A,X,eph_flagB,true,test_flagB);
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
           sstr = gen_session_string_sid(sidA,skey,seed);
           /*sstr = gen_session_string(skey[A], x, B,Y);*/
   	   ssskey = iH(sstr, h);
         } 
	 else
	 {	//not fresh
   	    ssskey = dummy_session_key;
	 }
       }
       else 
       {//not match
         if (!test_flagA )
         {//fresh
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);    
	   sstr = gen_session_string_sid(sidA,skey,seed);
           /*sstr = gen_session_string(skey[A], x, B,Y);*/
	   ssskey = iH(sstr, h);
         }
	 else
	 {//not fresh
	    ssskey = dummy_session_key;
	 }
       }
     }
         else
     {//B,_,Y,_ not complete
       if (!test_flagA )
       {//Fresh
         complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA); 
         sstr = gen_session_string_sid(sidA,skey,seed);
	 /*sstr = gen_session_string(skey[A], x, B,Y);*/
     	 ssskey = iH(sstr, h);
       }
       else 
       { //not fresh
         ssskey = dummy_session_key;
       }
     }
   }// B == B' /\ Y == Y'	
     else
     {  //   B <> B' \/ Y <> Y'
       ssskey = dummy_session_key;
     } 
      

 }// (A,_,X,_) is completed
 else
 {
   ssskey = dummy_session_key;
 }
return ssskey;
}     

/*
 fun Test(s : session_id) : session_key
 {
   var A:part = fstpart(s);
   var B:part = sndpart(s);
   var X:message = fstmsg(s);
   var Y:message = sndmsg(s);
   var x : eph_key = seed[(X,A)];
   var B' : part = dummy_part;
   var Y' : message = dummy_msg;
   var kr_flagA : bool = false;
   var kr_flagB : bool = false;
   var corr_flagA : bool = false;
   var corr_flagB : bool = false;
   var A' : part = dummy_part;
   var X' : message = dummy_msg;
   var sstr : session_string = dummy_string;
   var ssskey : session_key = dummy_session_key;
   var matchb : bool = false;
   var h : session_key = dummy_session_key;
   var sidA, sidB : session_id;
   h = gen_session_key(0);
   if (in_dom((A,X), complete_sessions)) 
   { // (A,_,X,_) is completed
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     sidA = mk_sid(A, B', X, Y');
     kr_flagA = session_key_reveal_flag(complete_sessions[(A,X)]);
//   corr_flagA = corrupt[A];    
     if ( B == B' && Y == Y') 
     {// B == B' /\ Y == Y'
     if (in_dom((B,Y), complete_sessions)) 
      { //B,_,Y_ complete 
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B, A', Y, X');
       matchb = session_match( mk_sid (A, B', X,Y'),mk_sid(B,A',Y,X'));
       if ( matchb ) 
       { // matches
         kr_flagB = session_key_reveal(complete_sessions[(B,Y)]);
//	 corr_flagB = corrupt[B];
         if (! test_flagA && ! test_flagB )
         {// fresh
           complete_sessions[(B,Y)] = mk_session_descr(A,X,eph_flagB,true,test_flagB);
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
           sstr = gen_session_string_sid(sidA,skey,seed);
           /*sstr = gen_session_string(skey[A], x, B,Y);*/
   	   ssskey = iH(sstr, h);
         } 
	 else
	 {	//not fresh
   	    ssskey = dummy_session_key;
	 }
       }
       else 
       {//not match
         if (!test_flagA )
         {//fresh
           complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);    
	   sstr = gen_session_string_sid(sidA,skey,seed);
           /*sstr = gen_session_string(skey[A], x, B,Y);*/
	   ssskey = iH(sstr, h);
         }
	 else
	 {//not fresh
	    ssskey = dummy_session_key;
	 }
       }
     }
         else
     {//B,_,Y,_ not complete
       if (!test_flagA )
       {//Fresh
         complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA); 
         sstr = gen_session_string_sid(sidA,skey,seed);
	 /*sstr = gen_session_string(skey[A], x, B,Y);*/
     	 ssskey = iH(sstr, h);
       }
       else 
       { //not fresh
         ssskey = dummy_session_key;
       }
     }
   }// B == B' /\ Y == Y'	
     else
     {  //   B <> B' \/ Y <> Y'
       ssskey = dummy_session_key;
     } 
      

 }// (A,_,X,_) is completed
 else
 {
   ssskey = dummy_session_key;
 }
return ssskey;
   
 }*/
 abs A = A { KG, Init, Respond, Complete, Corrupt, KeyReveal, H }
 
 fun Main () : bool = {
  var b' : bool;
  var tt : unit;
  complete_sessions = empty_map();
  incomplete_sessions = empty_map();
  corrupt = empty_map();
  pkey = empty_map();
  skey = empty_map();
  LH  = empty_map();
  seed  = empty_map();
  G = empty_map();
  b = {0,1};
  b' = A();
  return (b == b');
 }
 



};;

game AKE1 = AKE where
   KeyReveal = { 
   var A:part = fstpart(s);
   var B:part = sndpart(s);
   var X:message = fstmsg(s);
   var Y:message = sndmsg(s);
   var x : eph_key = seed[(X,A)];
   var B' : part = dummy_part;
   var Y' : message = dummy_msg;
   var test_flagA : bool = false;
   var test_flagB : bool = false;
   var eph_flagA : bool = false;
   var eph_flagB : bool = false;
   var A' : part = dummy_part;
   var X' : message = dummy_msg;
   var sstr : session_string = dummy_string;
   var ssskey : session_key = dummy_session_key;
   var matchb : bool = false;
   var fer : session_id option = none;
   var ofeh : session_string option = none;
   var sid : session_id = dummy_sid; 
   var sidA : session_id = dummy_sid;
   var sidB : session_id = dummy_sid;
   var sestr : session_string = dummy_string;
   var res : session_key;
   var h : session_key = dummy_session_key;
   h = gen_session_key(0);
   if (! in_dom((A,X), complete_sessions)) 
   {//session is not complete, cannot key reveal
     res = dummy_session_key;
   }
   else
   { // session complete
     B' = session_part(complete_sessions[(A,X)]);
     Y' = session_msg(complete_sessions[(A,X)]);
     sidA = mk_sid(A, B', X, Y');
     eph_flagA = session_eph_flag(complete_sessions[(A,X)]); 
     test_flagA = session_test_flag(complete_sessions[(A,X)]);
     if (B == B' && Y == Y') 
     { // session exists B == B ' && Y == Y'
       if (! in_dom((B,Y), complete_sessions)) 
       {// there is no completed matching session
          if (test_flagA)
          {//non-fresh session
            res = dummy_session_key;
          }
          else
          {//fresh session
            fer = findelse_sid_abs(G,sidA, skey, seed);
            if (isSome_id(fer))
            { // session with the same session string is in G 
              sid = proj(fer);
	      complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
 	      res = G[sid];
//    	      G[sidA] = res;//really necesary? findelse_sid ensures that th
            }
                else
            { // session with the same session string is not in G 
              ofeh = findelse_h_abs(LH,sidA, skey, seed);
              if (isSome_string(ofeh))
              {
                // session string has been queried to hash
                sestr = proj(ofeh);
		complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
		res = iH(sestr,h);
              }
                  else
              {// session string has not been queried to hash
                // use a randomly generated value
                G[sidA] = h;
		complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
		res = h;
              }
            }
          } //fresh session
        } // there is no completed matching session
     else
     { //there is a completed session of the form (B,_,Y,_)
       A' = session_part(complete_sessions[(B,Y)]);
       X' = session_msg(complete_sessions[(B,Y)]);
       sidB = mk_sid(B,A',Y,X');
       test_flagB = session_test_flag(complete_sessions[(B,Y)]);
       eph_flagB = session_eph_flag(complete_sessions[(B,Y)]); 
       matchb = session_match(sidA,sidB);
       if (!matchb) 
       {// (B,_,Y,_) is not a matching session
         if (test_flagA)
         {//non-fresh session
           res = dummy_session_key;
         }
             else
         {//fresh session
           fer = findelse_sid_abs(G,sidA, skey, seed);
           if (isSome_id(fer))
           { // session with the same session string is in G 
             sid = proj(fer);
             complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
	     res = G[sid];
	     G[sidA] = res;
           }
               else
           { // session with the same session string is not in G 
             ofeh = findelse_h_abs(LH,sidA, skey, seed);
             if (isSome_string(ofeh))
             {
               // session string has been queried to hash
               sestr = proj(ofeh);
               complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
               res = iH(sestr,h);
             }
                 else
             {// session string has not been queried to hash
               // use a randomly generated value
               G[sidA] = h;
	       complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
	       res = h;
             }
           }
         } //fresh session
       } // (B,_Y,_) is not a matching session
         else 
       {// (B,_Y,_) is a matching session
         if (test_flagA || test_flagB ) 
       { // at least one of the sessions is not fresh
         res = dummy_session_key;
       }
       else
       {// both sessions are fresh
         complete_sessions[(B,Y)] = mk_session_descr(A,X,eph_flagB,true,test_flagB);
         complete_sessions[(A,X)] = mk_session_descr(B',Y',eph_flagA,true,test_flagA);
         fer = findelse_sid_abs(G,sidA, skey, seed);
         if (isSome_id(fer)) 
         { // session with same session string in G
           sid = proj(fer);
	   res = G[sid];
//	   G[sidA] = res; YL 1/1/2012
//	   G[sidB] = res; YL 1/1/2012

         }
             else
         { // session string in H?
           ofeh = findelse_h_abs(LH,sidA, skey, seed);
           if (isSome_string(ofeh))
             { // session string has been queried to hash
               sestr = proj(ofeh);
               res = iH(sestr,h);
             }
                 else
             {// session string has not been queried to hash
              G[sidA] = h; 
              G[sidB] = h; 
              res = h;
             } 
           }
         }// both sessions are fresh
       }// B,Y is a matching session
     }// B,Y exists in completed
   } //session (X, A) is completed
   else 
   { // session does not exist
       res = dummy_session_key;
   }
     
 }
 return res;
}
and H = {
   var c : bool;
   var res : session_key;
   var findr : session_id option;
   var h : session_key = gen_session_key(0);
   findr = findelse_g_abs(G, lam, skey, seed);
   if (in_dom(lam, LH))
   {
     // it is in the domain of LH
     res=LH[lam];
   }
   else 
   {
     
     if (isSome_id(findr))
     {
       res= G[proj(findr)];
       //LH[lam] = res;
     }
     else 
     {
       LH[lam] = h;
       res = h;
     }
   }
   return res;
} and iH = {
   var c : bool;
   var res : session_key;
   var findr : session_id option;
   findr = findelse_g_abs(G, lam, skey, seed);
   if (in_dom(lam, LH))
   {
     // it is in the domain of LH
     res=LH[lam];
   }
   else 
   {
     
     if (isSome_id(findr))
     {
       res= G[proj(findr)];
       //LH[lam] = res;
     }
     else 
     {
       LH[lam] = h;
       res = h;
     }
   }
   return res;
}


pred invariant1 (LH1: (session_string, session_key) map, 
                 LH2: (session_string, session_key) map) =
forall (str : session_string). 
 {in_dom(str,LH2) } =>  ({in_dom(str,LH1)} /\ {LH1[str] == LH2[str]});;


pred invariant2 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map,
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map) =
forall (str : session_string, fer_sid : session_id). 
(({ findelse_g_abs(G2,str,skey2, seed2) == some(fer_sid)})
=> ({ in_dom(str,LH1)} /\ { LH1[str] == G2[fer_sid] }));;

//{ eqS_abs(str,fer_sid,skey1, seed1)} /\ { in(fstpart(fer_sid),part1) } /\ { in(fstpart(fer_sid),part1) }

pred  invariant3 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string). 
{in_dom(str,LH1)} => ({ in_dom(str, LH2)}  \/ {findelse_g_abs(G2,str,skey2, seed2) <> none});;

pred  invariant4 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string). 
({ in_dom(str, LH2)}  \/ {findelse_g_abs(G2,str,skey2, seed2) <> none}) => {in_dom(str,LH1)};;

pred invariant5 (seed : (message * part, eph_key ) map,
                 skey :  (part, secret_key ) map) =
forall (X: message, A : part).
{ in_dom((X, A), seed) } => { in_dom(A, skey) }

//KG, Init, Respond, Complete, Corrupt, KeyReveal 

equiv INV_H : AKE.H ~ AKE1.H :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, lam }) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, res})
wp;
rnd;
expand invariant2;
trivial;;
save;;

equiv INV_Respond : AKE.Respond ~ AKE1.Respond :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, A, B, X }) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, res})
wp;
rnd;
expand invariant2;
trivial;;
save;;

equiv INV_Complete : AKE.Complete ~ AKE1.Complete :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, A, B, X, Y}) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{2},skey{2}) /\
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed})
wp;
expand invariant2;
trivial;;
save;;

equiv INV_KeyReveal : AKE.KeyReveal ~ AKE1.KeyReveal :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2},  seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{1},skey{1}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, s }) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{1},skey{1}) /\
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, res})
wp;
inline;
wp;
rnd;
derandomize;
wp;
expand invariant2;
trivial;;
save;;

equiv INV_Init : AKE.Init ~ AKE1.Init :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{1},skey{1}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, A, B }) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2},LH{1}, skey{2}, seed{2}) /\
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  invariant5(seed{1},skey{1}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, res})
wp;
rnd;
expand invariant2;
trivial;;
save;;

equiv INV_KG : AKE.KG ~ AKE1.KG :
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 invariant5(seed{1},skey{1}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed}) ==>
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 invariant5(seed{1},skey{1}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, res})
wp;
rnd;
expand invariant2;
trivial;;
save;;

equiv auto INV_Main : AKE.Main ~ AKE1.Main : {true} ==> ={ res }
inv (invariant1(LH{1},LH{2}) /\
     invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\
     invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
     invariant5(seed{1},skey{1}) /\
    ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed });;

claim Pr1 : AKE.Main[res] == AKE1.Main[res] using INV_Main;;

/* equiv auto INV_Respond : AKE.Respond ~ AKE1.Respond : */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, A, B, X }) ==> */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */

/* equiv auto INV_Complete : AKE.Complete ~ AKE1.Complete : */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, A, B, X, Y}) ==> */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants});; */

/* equiv INV_KeyReveal : AKE.KeyReveal ~ AKE1.KeyReveal : */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2},  seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, s }) ==> */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res}) */
/* admit;; */
/* save;; */
/* /* inline;wp;rnd; */ */
/* /* expand invariant2;trivial;; */ */
/* /* save;; */ */





/* wp;; */
/* rnd;; */
/* trivial;; */
/* expand invariant2;; */
/* expand invariant5;; */
/* trivial;; */



/* equiv auto INV_Corrupt : AKE.Corrupt ~ AKE1.Corrupt : */
/* (invariant1(LH{1},LH{2}) /\ */
/*      invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*      invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*      invariant5(seed{1},skey{1}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, A}) ==> */
/* (invariant1(LH{1},LH{2}) /\ */
/*      invariant2(G{2}, LH{1}, skey{2}, seed{2}) /\ */
/*      invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*      invariant5(seed{1},skey{1}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */






//






/* wp;; */
/* rnd;; */
/* trivial;; */
/* expand invariant3;; trivial;; */
/* expand invariant2; trivial;; */



/* equiv INV_H : AKE.H ~ AKE1.H : */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, participants{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, lam}) ==> */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, participants{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */
/* wp;; */
/* rnd;; */
/* trivial;; */
/* expand invariant1;; */
/* expand;; */
/* trivial;; */
/* trivial;; */

/* equiv auto INV_iH : AKE.iH ~ AKE1.iH : */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, lam, h}) ==> */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */

/* equiv auto INV_KeyReveal : AKE.KeyReveal ~ AKE1.KeyReveal : */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, s }) ==> */
/*   (invariant1(LH{1},LH{2}) /\ */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*   ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */



/* equiv INV_KG : AKE.KG ~ AKE1.KG : */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, participants{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants}) ==> */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, participants{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */
/* wp;; */
/* rnd;; */
/* trivial;; */
/* expand invariant3;; trivial;; */
/* expand invariant2; trivial;; */

/* equiv auto INV_Main : AKE.Main ~ AKE1.Main : {true} ==> ={ res } */
/* inv (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants });; */






/*
pred invariant2 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string, sid : session_id). 
({ in_dom(sid,G2) } /\ {eqS_abs(str,sid,skey2,seed2) }) =>
({ in_dom(str,LH1)} /\ { LH1[str] == G2[sid] });;

pred  invariant3 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string). 
{in_dom(str,LH1)} => ({ in_dom(str, LH2)}  \/ (exists (sid : session_id). { in_dom(sid,G2) } /\ {eqS_abs(str,sid,skey2,seed2) }))

pred  invariant4 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string, sid : session_id). 
({ in_dom(str, LH2)}  \/ ({ in_dom(sid,G2) } /\ {eqS_abs(str,sid,skey2,seed2) })) => {in_dom(str,LH1)}
*/


/* pred invariant5(incomplete_sessions : incomplete_session_with_status, */
/*                 complete_sessions : complete_session_with_status,  */
/*                 seed2 : (message * part, eph_key ) map ) = */
/* forall (X : message,  */
/*         A : part).  */
/* { in_dom((X,A), seed2) } <=>  */
/* ({ in_dom((A,X), incomplete_sessions) }  \/ { in_dom((A,X), complete_sessions)}) */

/* pred invariant6 (G2 : (session_id, session_key) map, */
/*                  complete_sessions : complete_session_with_status) = */
/* forall (sid : session_id). */
/* { in_dom(sid, G2) } => { in_dom( (fstpart(sid),fstmsg(sid)), complete_sessions) } */
/* ;; */

/* /*lemma inv4 : forall (G2 : (session_id, session_key) map,  */
/*                      LH1: (session_string, session_key) map,  */
/*                      LH2: (session_string, session_key) map,  */
/*                      skey2 : (part, secret_key ) map, */
/*                      seed2 : (message * part, eph_key ) map ). */
/* (invariant1(LH1,LH2) /\ */
/* invariant2(G2,LH1, skey2, seed2) /\  */
/* invariant3(G2,LH1, LH2, skey2, seed2)) => */
/* invariant4(G2,LH1, LH2, skey2, seed2) Yassine 1/12 */
/* */ */


/* //prover "alt-ergo";; */
/* timeout 3;; */

/* equiv auto INV_KG : AKE.KG ~ AKE1.KG : */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants}) ==> */
/*  (invariant1(LH{1},LH{2}) /\ */
/*  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\ */
/*  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res}) */

/*

equiv auto INV_H : AKE.H ~ AKE1.H :
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, lam}) ==>
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});;


equiv auto INV_iH : AKE.iH ~ AKE1.iH :
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, lam, h}) ==>
 (invariant1(LH{1},LH{2}) /\
 invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});;

equiv auto INV_KeyReveal : AKE.KeyReveal ~ AKE1.KeyReveal :
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, s }) ==>
  (invariant1(LH{1},LH{2}) /\
  invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\ 
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});;


inline
derandomize
wp
rnd
expand invariant2
trivial
save;;
*/
/* equiv auto INV_Init : AKE.Init ~ AKE1.Init :  */
/*   (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, A, B }) ==>  */
/*   (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2},LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res}) */
/* /* wp */ */
/* /* rnd */ */
/* /* trivial */ */
/* /* save */ */
/* /* ;; */ */


/* equiv auto INV_Respond : AKE.Respond ~ AKE1.Respond :  */
/*   (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2},LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, A, B, X }) ==>  */
/*   (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2},LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants, res});; */
/* /* wp */ */
/* /* rnd */ */
/* /* trivial */ */
/* /* save */ */
/* /* ;; */ */




/* app 10 10 (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants }) */
/* rnd;wp;trivial;; */
/* auto inv   (invariant1(LH{1},LH{2}) /\  */
/*   invariant2(G{2}, LH{1}, skey{1}, skey{2}, seed{1}, seed{2}) /\  */
/*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\  */
/*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, participants });; */
/* save;; */



/*
pred  invariant5 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str: session_string). 
( { in_dom(str, LH1) } /\ { !in_dom(str,LH2) } => 
 ({ findelse_g_abs(G2,str,skey2,seed2) <> none} /\ {in_dom(proj (findelse_g_abs(G2,str,skey2,seed2)), G2) })
)

pred invariant7 (LH1: (session_string, session_key) map, 
*/

//findelse_g_abs(m',str,skey',seed') == none
//(gen_session_string(skey2[fstpart(sid)],seed2[(fstmsg(sid),fstpart(sid))],sndpart(sid),sndmsg(sid)) == str} /\ {in_dom(sid, G2)}) => 
//{in_dom(str,LH1) };;

/*
equiv auto INVARIANT1_H : AKE.H ~ AKE1.H : 
(invariant1(G{2},LH{2}, skey{2}, seed{2}) /\
invariant2(LH{1},LH{2}) /\ 
invariant3(G{2},LH{1}, skey{2}, seed{2}) /\ 
invariant4(G{2},LH{1}, skey{2}, seed{2}) /\
invariant5(G{2},LH{1}, LH{2}, skey{2}, seed{2}) /\
invariant6(LH{1}, LH{2}) /\
={skey, seed, complete_sessions, lam}) ==>
(invariant1(G{2},LH{2}, skey{2}, seed{2}) /\
invariant2(LH{1},LH{2}) /\ 
invariant3(G{2},LH{1}, skey{2}, seed{2}) /\ 
invariant4(G{2},LH{1}, skey{2}, seed{2}) /\
={skey, seed, complete_sessions})
*/
//{};; 
//equiv auto Fact1 : AKE.KeyReveal ~ AKE1.KeyReveal : ={s, LH, skey, seed, complete_sessions } ==> {res{1} ==// res{2}};;
//equiv auto Fact4 : G3.Main ~ LCDH.Main : {true} ==> {(in(y',LA)){1} == res{2}} 
