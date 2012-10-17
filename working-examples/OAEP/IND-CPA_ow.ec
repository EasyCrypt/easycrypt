checkproof.
include "IND-CPA_common.ec".
checkproof.

game G4 = G3
  var ts : bitstring{p}
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var h : bitstring{p}; 
    var tmp : bitstring{k};

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    hs = bs0_p; rs = bs0_p;    
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    ts = low_bits(tmp);
    (m0, m1) = A1(pk);   
    h = H(ss);
    rs = h ^^ ts;
    b' = A2(c);
    if (!in_dom(ss, Hm)){ hs ={0,1}^p; } else { hs = Hm[ss]; }
    return true;
  }.

equiv G3_G4 : G3.Main ~ G4.Main : true ==> ={rs,domGA}.
 app 13 15 (={rs,domGA}); [ | if{2};trivial].
 swap{1} 7 -1.
 *(auto (={Gm,Hm,domGA});*rnd).
save.

claim Pr_G3_G4 : G3.Main[mem(rs,domGA)] = G4.Main[mem(rs,domGA)]
using G3_G4.

game G5 = G4
  where H = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) {
      if (x = ss) { h = hs; }
      Hm[x] = h;
    }
    return Hm[x];
  }
  and Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var h : bitstring{p}; 
    var tmp : bitstring{k};

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    hs = bs0_p; rs = bs0_p;    
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    ts = low_bits(tmp);
    if (!in_dom(ss, Hm)){ hs ={0,1}^p; } else { hs = Hm[ss]; }
    (m0, m1) = A1(pk);   
    h = H(ss);
    rs = h ^^ ts;
    b' = A2(c);
    return true;
  }.

equiv G4_G5 : G4.Main ~ G5.Main : true ==> ={rs, domGA}
  by eager {if (!in_dom(ss, Hm)){ hs ={0,1}^p; } else { hs = Hm[ss]; }}.
 derandomize.
 case{1} : (x = ss && !in_dom(x, Hm));[ trivial | ].
 swap{1} 1;trivial.
save.
 inline KG; trivial.
 trivial.
save.

claim Pr_G4_G5 : G4.Main[mem(rs, domGA)] = G5.Main[mem(rs, domGA)] 
using G4_G5.

game G6 = G5 
  var bad1, bad2 : bool
  where  G = {
    var g : bitstring{ku} = {0,1}^(ku);
    bad1 = bad1 || (x = rs && in_dom(ss, Hm));
    bad2 = bad2 || (x = rs && !in_dom(ss, Hm));
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x]; 
  }
  and Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var tmp : bitstring{k};
    
    bad1 = false; bad2 = false;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    ts = low_bits(tmp);
    hs ={0,1}^p;
    rs = hs ^^ ts;
    (m0, m1) = A1(pk);   
    b' = A2(c);
    return true;
  }.

pred in_assoc(M : ('a, 'b) map, a : 'a, b : 'b) =
  in_dom(a, M) => M[a] = b.

equiv G5_G6 : G5.Main ~ G6.Main : true ==> mem(rs, domGA){1} => (bad1 || bad2){2}.
 inline H, KG.
 condt{1} at 13;[trivial | ].
 auto (={Gm, domGA, domHA, hs, ts, ss, hs} &&
       (hs^^ts){1} = rs{2} &&
       (mem(hs^^ts, domGA){1} => (bad1 || bad2){2}) && 
       eq_except(Hm{1}, Hm{2}, ss{1}) &&
       in_assoc(Hm{1}, ss{1}, hs{1}) && in_assoc(Hm{2}, ss{2}, hs{2})).
 rnd{1}.
 auto (={Gm, domGA, Hm, domHA, hs, ts, ss, hs} && 
       (hs^^ts){1} = rs{2} &&
       (mem(hs^^ts, domGA){1} => (bad1 || bad2){2}) && 
       in_assoc(Hm{1}, ss{1}, hs{1}) && in_assoc(Hm{2}, ss{2}, hs{2}));trivial.
save.

claim Pr_G5_G6 : G5.Main[mem(rs, domGA)] <= G6.Main[bad1 || bad2] 
using G5_G6.

claim Pr_G6_bad1_2 : G6.Main[bad1 || bad2] <= G6.Main[bad1] + G6.Main[bad2] 
compute.

claim Pr_INDCPA_G6 : |INDCPA.Main[res] - 1%r/2%r| <= G6.Main[bad1] + G6.Main[bad2].

unset Pr_INDCPA_G3, Pr_G3_G4, Pr_G4_G5, Pr_G5_G6, Pr_G6_bad1_2.

(** We focus on G6.Main[bad2].
    We show that G6.Main[bad2] <= qG/2^p *)
game Q1  = G6
  var bad4 : bool
  where G = {
    var g : bitstring{ku} = {0,1}^(ku);
    bad2 = bad2 || (x=rs && !in_dom(ss, Hm));
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x]; 
  }
  and H = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) {
      if ((x = ss) && !bad2) {
        bad4 = true;
        h = hs;
      }
      Hm[x] = h;
    }
    return Hm[x];
  }
 and Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var tmp : bitstring{k};
    
    bad2 = false;bad4 = false;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    c = {0,1}^k;
    tmp = finv(sk, c);
    ss = high_bits(tmp);
    ts = low_bits(tmp);
    rs ={0,1}^p;
    hs = rs ^^ ts;
    (m0, m1) = A1(pk);   
    b' = A2(c);
    return true;
  }.

equiv G6_Q1 : G6.Main ~ Q1.Main : true ==> ={bad2}. 
 auto upto (bad2) 
 with (={Gm, domGA, Hm, domHA, rs, ss, hs}).
 rnd (rs ^^ ts{2}).
 inline KG;trivial.
save.

claim G6_Q1 : G6.Main[bad2] = Q1.Main[bad2]
using G6_Q1.

game Q2  = Q1
  where H = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) {
      bad4 = bad4 || (x=ss && !bad2);
      Hm[x] = h;
    }
    return Hm[x];
  }.

equiv Q1_Q1 : Q1.Main ~ Q1.Main : true ==> (bad4{1} => !bad2{1}) && ={bad4, bad2} 
by auto ((bad4{1} => (in_dom(ss, Hm){1} && !bad2{1})) && 
         ={Gm, domGA, Hm, domHA, rs, ss, hs, bad2, bad4}).

equiv Q2_Q2 : Q2.Main ~ Q2.Main : true ==> (bad4{1} => !bad2{1}) && ={bad4, bad2}
by auto ((bad4{1} => (in_dom(ss, Hm){1} && !bad2{1})) && 
          ={Gm, domGA, Hm, domHA, rs, ss, hs, bad2, bad4}).

equiv Q1_Q2 : Q1.Main ~ Q2.Main : true ==> ={bad4} && (!bad4{1} => ={bad2})
by auto upto (bad4) with (={Gm, domGA, Hm, domHA, rs, ss, hs, bad2}).

claim Pr_Q1_Q1 : Q1.Main[bad2 && bad4] = Q1.Main[false] using Q1_Q1.

claim Pr_Q1_0  : Q1.Main[false] = 0%r compute.

claim Pr_Q2_Q2 : Q2.Main[bad2 && bad4] = Q2.Main[false] using Q2_Q2.

claim Pr_Q2_0  : Q2.Main[false] = 0%r compute.

claim Q1_split : Q1.Main[bad2] = Q1.Main[bad2 && bad4] + Q1.Main[bad2 && !bad4] 
compute.

claim Q2_split : Q2.Main[bad2] = Q2.Main[bad2 && bad4] + Q2.Main[bad2 && !bad4] 
compute.

claim Pr_Q1_Q2 : Q1.Main[bad2 && !bad4] = Q2.Main[bad2 && !bad4] 
using Q1_Q2.

claim Pr_G6_Q2 : G6.Main[bad2] = Q2.Main[bad2].

unset Pr_G6_Q1, Pr_Q1_Q1, Pr_Q1_0, Pr_Q2_Q2, Pr_Q2_0, Pr_Q1_split, Pr_Q2_split, Pr_Q1_Q2.

game Q3 = Q2
  where H = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) { Hm[x] = h; }
    return Hm[x];
  }
  and G = {
    var g : bitstring{ku} = {0,1}^(ku);
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x];
  }
 and Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    
    bad2 = false;bad4 = false;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    c = {0,1}^k;
    (m0, m1) = A1(pk);   
    b' = A2(c);
    rs ={0,1}^p;
    return true;
  }.

equiv Q2_Q3 : Q2.Main ~ Q3.Main : true ==> 
   (bad2{1} => mem(rs, domGA){2}) && length(domGA{2}) <= qG.
 inline KG;swap{2} -2.
 auto ((bad2{1} => mem(rs, domGA){2}) &&  ={Gm, domGA, Hm, rs} && 
       length(domGA{2}) <= qG &&
       forall (x : bitstring{p}), in_dom(x, Gm){2} => mem(x, domGA){2});trivial.
save.

claim Pr_Q2_Q3 : Q2.Main[bad2] <= Q3.Main[mem(rs, domGA) && length(domGA) <= qG] 
using Q2_Q3.

claim Pr_Q3 : Q3.Main[mem(rs, domGA) && length(domGA) <= qG] <= qG%r/(2^p)%r 
compute.

claim G6_bad2 : G6.Main[bad2] <= qG%r/(2^p)%r.
unset Pr_G6_Q2, Pr_Q2_Q3, Pr_Q3.

(** We now focus on G6.Main[bad1] *)


game P1 = G6 
  remove rs
  var pks:pkey
  var cs:cipher
  where G = {
    var g : bitstring{ku};
    g = {0,1}^ku;
    if (!in_dom (x,Gm)) { Gm[x] = g; }
    return Gm[x];
  }
  and Main = {
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var tmp : bitstring{k};
    bad1 = false; bad2 = false;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pks, sk) = KG ();
    cs = {0,1}^k;
    tmp = finv (sk,cs);
    ss = high_bits (tmp);
    ts = low_bits (tmp);
    hs = bs0_p;
    if(!in_dom(ss, Hm)) { hs = {0,1}^p; }else{ hs = Hm[ss];}
    (m0, m1) = A1 (pks);
    b' = A2 (cs);
    return true;
  }.

axiom high_low_bits :  forall (t:bitstring{k}), (high_bits(t) || low_bits(t)) = t.

equiv G6_P1 : G6.Main ~ P1.Main : true ==>
   bad1{1} => 
    exists (rs:bitstring{p}), mem(rs, domGA{2}) &&
     exists (ss:bitstring{ku}), in_dom(ss,Hm{2}) && cs{2} = f(pks{2},ss || Hm{2}[ss] ^^ rs).
 app 15 15 ( ={Hm,domGA} && cs{2} = f(pks{2},(ss||hs^^rs){1}) && 
              (bad1{1} => mem(rs,domGA){1} && in_dom(ss,Hm){1}) &&
              (in_dom(ss,Hm){1} => Hm[ss]{1} = hs{1})). 
  inline KG;auto (={Gm,domGA,Hm,ss,hs} && (bad1{1} => mem(rs,domGA){1}&&in_dom(ss,Hm){1}) &&
                   (in_dom(ss,Hm){1} => (Hm[ss] = hs){1})).
  condt{2} last;[ trivial | !2(rnd;wp)].
  apply : validkeys();trivial.
 trivial.
save.

op find2_f : (t_domGA,t_Hm, cipher, pkey) -> bitstring{ku} * bitstring{p}.

axiom find2_f_spec : 
  forall (domGA:t_domGA, Hm:t_Hm, c:cipher, pk:pkey),
    (exists (rs:bitstring{p}), mem(rs, domGA) &&
     exists (ss:bitstring{ku}), in_dom(ss,Hm) && c = f(pk,ss || Hm[ss] ^^ rs))=>
    let s,r = find2_f(domGA, Hm, c, pk) in
    f(pk, s || (Hm[s] ^^ r)) = c.

op find2_f_eq (domGA:t_domGA,Hm:t_Hm,c:bitstring{k}, pk:pkey) =
    let s,r = find2_f(domGA, Hm, c, pk) in 
    (f(pk, s || (Hm[s] ^^ r)) = c).
 
claim Pr_G6_P1 : G6.Main[bad1] <= P1.Main[find2_f_eq(domGA, Hm, cs, pks)]
using G6_P1.

game P2 = P1 
  where H = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom (x,Hm)) { Hm[x] = h; }
    return Hm[x];
  }
  and Main = {
    var sk : skey;
    var b' : bool;
    var m0,m1 : message;
    var tmp : bitstring{k};
    bad1 = false; bad2 = false;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pks, sk) = KG ();
    cs = {0,1}^k;
    tmp = finv (sk,cs);
    ss = high_bits (tmp);
    ts = low_bits (tmp);
    hs = bs0_p;
    (m0, m1) = A1 (pks);
    b' = A2 (cs);
    if(!in_dom(ss, Hm)) { hs = {0,1}^p; }else{ hs = Hm[ss];}
    return true;
  }.

equiv P1_P2 : P2.Main ~ P1.Main : true ==> ={domGA,Hm,cs,pks} 
by eager { if(!in_dom(ss, Hm)) { hs = {0,1}^p; }else{ hs = Hm[ss];}}.
 derandomize.
 case{1} : (x = ss && !in_dom(x, Hm));[ trivial | ].
 swap{1} 1; trivial.
save.
 inline KG; trivial.
 trivial.
save.

claim Pr_P1_P2 : 
  P1.Main[find2_f_eq(domGA, Hm, cs, pks)] = P2.Main[find2_f_eq(domGA, Hm, cs, pks)]
using P1_P2.

game Gow = {
  (* Adversary part *)
  var Gm  : t_Gm
  var domGA : t_domGA  
  var Hm  : t_Hm
  var domHA : t_domHA
  
  fun G(x : bitstring{p}) : bitstring{ku} = {
    var g : bitstring{ku} = {0,1}^(ku);
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x];
  }
  
  fun G_A(x : bitstring{p}) : bitstring{ku} = {
    var kp : bitstring{ku};
    if(length(domGA) < qG){
      domGA = x :: domGA;
      kp = G(x);
    }
    else { kp = bs0_ku;}
    return kp;
  }

  fun H(x : bitstring{ku}) :  bitstring{p} = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) { Hm[x] = h; }
    return Hm[x];
  }
  
  abs A1 = A1 {G_A, H}
  abs A2 = A2 {G_A, H}

  fun I(pk : pkey, c : cipher) : bitstring{k} = {
    var s : bitstring{ku};
    var r : bitstring{p}; 
    var m0, m1 : message;
    var b' : bool;
    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (m0, m1) = A1(pk);
    b' = A2(c);
    (s, r) = find2_f(domGA, Hm, c, pk);
    return s || (Hm[s] ^^ r);
  }

  (* The main part *)
  fun KG() : key = {
    var x : key = kg();
    return x;
  }

  fun Main() : bool = {
    var pk : pkey;
    var sk : skey;
    var x, y : bitstring{k};
    (pk, sk) = KG();
    y = {0,1}^k;
    x = I(pk, y);
    return (finv(sk, y) = x);
  }
}.

equiv P2_Gow : P2.Main ~ Gow.Main : true ==> 
     (find2_f_eq(domGA, Hm, cs, pks)){1} = res{2}. 
 inline I, KG;wp.
 app 15 12 (={domGA,Hm} && valid_keys(pk_0,sk){2} && 
              c{2} = y{2} && pks{1} = pk_0{2} && cs{1}=c{2});
           [ | derandomize; trivial].
 auto (={domGA,Hm,Gm}).
 rnd;wp;apply : validkeys ();trivial.
save.

claim Pr_P2_Gow : P2.Main[find2_f_eq(domGA, Hm, cs, pks)] = Gow.Main[res] 
using P2_Gow.

claim Conclusion : |INDCPA.Main[res] - 1%r/2%r| <= Gow.Main[res] +  qG%r/(2^p)%r.
