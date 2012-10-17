checkproof.
include "IND-CPA_common.ec".
checkproof.

game G4 = G3
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var t : bitstring{p}; 
    var tmp : bitstring{k};

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    (m0, m1) = A1(pk);
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    t = low_bits(tmp);    
    hs = {0,1}^p;
    rs = hs ^^ t;
    b' = A2(c);
    return true;
  }.

equiv G3_G4 : G3.Main ~ G4.Main : true ==> 
     mem(ss,domHA){1} = mem(ss,domHA){2} && (!mem(ss, domHA){1} => ={rs, domGA}).
 call upto (mem(ss, domHA))
 with (={Gm, domGA, domHA, ss, hs} && eq_except(Hm{1}, Hm{2}, ss{1})).
 inline H, KG;*(wp; rnd).
 call (={Gm, domGA, Hm, domHA} && 
       forall(w:bitstring{ku}), in_dom(w, Hm){1} => (mem(w, domHA){1}));trivial.
save.

claim Pr_G3_G4_Aux : 
  |G3.Main[mem(rs, domGA)] - G4.Main[mem(rs, domGA)]| <= G4.Main[mem(ss, domHA)] 
using G3_G4.

claim Pr_G3_G4 : 
  G3.Main[mem(rs, domGA)] <= G4.Main[mem(ss, domHA)] + G4.Main[mem(rs, domGA)].

claim Pr_INDCPA_G4 : 
  | INDCPA.Main[res] - 1%r/2%r | <= G4.Main[mem(ss, domHA)] +  G4.Main[mem(rs, domGA)].

unset Pr_G3_G4_Aux, Pr_G3_G4, Pr_INDCPA_G3. 


(* We have to bound  G4.Main[mem(ss, domHA)] and G4.Main[mem(rs, domGA)].
   We focus on G4.Main[mem(rs, domGA)] *)

game G5 = G4
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var t : bitstring{p}; 
    var tmp : bitstring{k};

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    (m0, m1) = A1(pk);
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    t = low_bits(tmp);    
    b' = A2(c);
    rs = {0,1}^p;
    hs = rs ^^ t;
    return true;
  }.

equiv G4_G5 : G4.Main ~ G5.Main : true ==> ={rs, domGA} && (length(domGA){2} <= qG).
 inline KG; swap{1} -2; wp.
 rnd (rs ^^ t{2}).
 *(auto (={Gm, domGA, Hm, domHA} && (length(domGA){2} <= qG));*rnd).
save.

claim Pr_G4_G5 : G4.Main[mem(rs, domGA)] = G5.Main[mem(rs, domGA) && length(domGA) <= qG] 
using G4_G5.

claim Pr_G5 : G5.Main[mem(rs, domGA) && length(domGA) <= qG] <= qG%r/(2^p)%r compute.

game Gspow = {

  (* The Inverter *)
  var Gm  : t_Gm
  var domGA : t_domGA
  var Hm  :t_Hm
  var domHA : t_domHA
  
  fun G(x : bitstring{p}) : bitstring{ku} = {
    var g : bitstring{ku} = {0,1}^(ku);
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x];
  }
  
  fun G_A(x : bitstring{p}) : bitstring{ku} = {
    var kp : bitstring{ku};
    if (length(domGA) < qG){
      domGA = x :: domGA;
      kp = G(x);
    } else { 
      kp = bs0_ku; 
    }
    return kp;
  }

  fun H(x : bitstring{ku}) :  bitstring{p} = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) { Hm[x] = h; }
    return Hm[x];
  }
  
  fun H_A(x : bitstring{ku}) : bitstring{p} = {
    var _p : bitstring{p};
    domHA = x :: domHA;
    _p = H(x);
    return _p;
  }

  fun KG() : key = {
    var x : key = kg();
    return x;
  }

  abs A1 = A1 {G_A, H_A}
  abs A2 = A2 {G_A, H_A}
  
  fun I(pk : pkey, c : cipher) : t_domHA = {
    var g, s : bitstring{ku};
    var h, t, r : bitstring{p}; 
    var m0, m1 : message;
    var b' : bool;
    var tmp : bitstring{k};
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (m0, m1) = A1(pk);
    b' = A2(c);
    return domHA;
  }

  fun Main() : bool = {
    var pk : pkey;
    var sk : skey;
    var y : bitstring{k};
    var l : t_domHA;
    (pk, sk) = KG();
    y = {0,1}^k;
    l = I(pk, y);
    return mem(high_bits(finv(sk,y)), l);
  }
}.

equiv G4_Gspow : G4.Main ~ Gspow.Main : true ==> mem(ss, domHA){1} => res{2}.
 swap{1} 6 6;inline I,KG.
 auto (={Gm, domGA, Hm, domHA}).
 rnd{1}; wp; rnd; wp.
 apply : validkeys(); trivial.
save.

claim Pr_G4_Gspow : G4.Main[mem(ss, domHA)] <= Gspow.Main[res] 
using G4_Gspow.

claim Conclusion : 
  | INDCPA.Main[res] - 1%r/2%r | <= Gspow.Main[res] + qG%r/(2^p)%r.
