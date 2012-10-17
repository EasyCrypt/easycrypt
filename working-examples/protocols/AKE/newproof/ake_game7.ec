include "ake_game6.ec".

game AKE7 =
AKE6 where
iHT = {
 var h : session_key = gen_session_key();
 argLHT = lam::argLHT;
 return h;
}.
