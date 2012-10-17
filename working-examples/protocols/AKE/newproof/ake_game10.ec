include "ake_game9.ec".

game AKE10 = 
AKE9
var G : (session_id,session_key) map
where compute_key = {
  var ssskey : session_key;
  var sstr : session_string option;
  var sid' : session_id option;
  sstr = findelse_h_abs(LH,s,skey,seed);
  sid' = findelse_sid_abs(G,s,skey,seed);
  if (sstr <> None) {
   ssskey = LH[proj(sstr)];
  } else
  {
   if (sid' <> None) {
    ssskey = G[proj(sid')];
   } else {
    ssskey = gen_session_key();
    G[s] = ssskey;     
   }
  } 
 return ssskey;
 } and 
 iH = {
  var sid : session_id option;
  var ssskey : session_key;
  if (in_dom(lam, LH)) { 
   ssskey = LH[lam];
  } else {
   sid = findelse_g_abs(G,lam,skey,seed);
   if (sid <> None) {
    ssskey = G[proj(sid)];
   } else {
    ssskey = gen_session_key();
   }
   LH[lam] = ssskey;
  }
 return ssskey;
} and
Main  = {
  var b' : bool;
  var tt : unit;
  complete_sessions = empty_map;
  incomplete_sessions = empty_map;
  corrupt = empty_map;
  pkey = empty_map;
  skey = empty_map;
  LH  = empty_map;
  LHT  = empty_map;
  seed  = empty_map;
  tested_session = empty_map;
  msg_seeds = empty_map;
  keys_revealed = empty_map;
  G = empty_map;
  argLH = [];
  argLHT = [];
  sid_queries = [];
  part = 0;
  sess = 0;
  b' = A();
  b = {0,1};
  return (b = b');
 }.
