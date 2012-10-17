include "ake_game7.ec".

game AKE8 =
AKE7 
where 
H = {
 var sk : session_key;
 argLH = str::argLH;
 sk = iH(str);
 return sk;
} and
iH = {
 var h : session_key = gen_session_key(); 
 if (!in_dom(lam, LH)) { LH[lam] = h;}
 return LH[lam];
} and 
iHT = {
 var h : session_key = gen_session_key();
 argLHT = lam::argLHT;
 return h;
}.