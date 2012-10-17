include "ake_game5.ec".

game AKE6 = 
AKE5
where
iH = {
 var h : session_key = gen_session_key();
 argLH = lam::argLH;
 if (!in_dom(lam, LH)) { LH[lam] = h;}
 return LH[lam];
} and 
iHT = {
 var h : session_key = gen_session_key();
 argLHT = lam::argLHT;
 if (!in_dom(lam, LHT)) { LHT[lam] = h;}
 return LHT[lam];
}.

