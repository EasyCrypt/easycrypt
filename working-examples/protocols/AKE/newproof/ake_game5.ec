include "ake_game4.ec".

game AKE5 = 
AKE4
var argLH : session_string list
var argLHT : session_string list
where
H = {
 var sk : session_key;
 sk = iH(str);
 return sk;
 } and
iH = {
  var h : session_key = gen_session_key();
  var sk : session_key;
  argLH = lam::argLH;
  if (!in_dom(lam, LH) && !in_dom(lam, LHT)) { LH[lam] = h; sk = h;}
  else {
   if (in_dom(lam, LHT)) {
    sk = LHT[lam];
   } else {
    sk = LH[lam];
   }
  }
  return sk;
 }
and 
iHT = {
 var h : session_key = gen_session_key();
 var sk : session_key;
 argLHT = lam::argLHT;
 if (!in_dom(lam, LH) && !in_dom(lam, LHT)) { LHT[lam] = h; sk = h;}
 else {
  if (in_dom(lam, LHT)) {
   sk = LHT[lam];
  } else {
   sk = LH[lam];
  }
  }
  return sk;
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
  argLH = [];
  argLHT = [];
  sid_queries = [];
  part = 0;
  sess = 0;
  b = {0,1};
  b' = A();
  return (b = b');
 }.
