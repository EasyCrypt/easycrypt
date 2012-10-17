checkproof.

(** Operator needed for OAEP *)

cnst u  : int.
cnst k1 : int.
cnst p  : int.
cnst ku : int = u + k1.
cnst k  : int = ku + p.
cnst qG, qH, qD : int.

axiom p_pos : 0 <= p.
axiom k1_pos : 0 <= k1.
axiom qG_pos : 0 <= qG.
axiom qD_pos : 0 <= qD.
axiom qH_pos : 0 <= qH.

(** ******************************************* *)
(**             Usefull types                   *)
(** ******************************************* *)
type pkey.
type skey.
type key     = pkey * skey.
type message = bitstring{u}.
type cipher  = bitstring{k}.
type t_Gm    = (bitstring{p}, bitstring{ku}) map.
type t_Hm    = (bitstring{ku}, bitstring{p}) map.
type t_domDA = (bool * cipher) list.
type t_domGA = bitstring{p} list.
type t_domHA = bitstring{ku} list.

(** ******************************************* *)
(**        Specification of key generation      *)
(** ******************************************* *)
pop kg         : () -> key.
op  valid_keys : (pkey,skey) -> bool.

axiom validkeys_spec() :
  x=kg() ~ y=kg() : true ==> x=y && valid_keys(fst(x), snd(x)).

(** ******************************************* *)
(**  Specification of the encryption function   *)
(** ******************************************* *)
op f    : (pkey, bitstring{k}) -> bitstring{k}.
op finv : (skey, bitstring{k}) -> bitstring{k}.

axiom fofinv : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => f(pk, finv(sk, m)) = m.

axiom finvof : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => finv(sk, f(pk, m)) = m.

(** ******************************************* *)
(**      Specification on append and split      *)
(** ******************************************* *)
op [||] : (bitstring{u}, bitstring{k1}) -> bitstring{ku} as append_u_k1.
op [||] : (bitstring{ku}, bitstring{p}) -> bitstring{k} as append_ku_p.

axiom append_ku_p() :
   a = {0,1}^ku||{0,1}^p ~ b = {0,1}^k : true ==> (a = b).

axiom append_u_k1() :
  a = {0,1}^u || {0,1}^k1 ~ b = {0,1}^ku : true ==> (a = b).

axiom split_ku() :
  a = {0,1}^ku ~ b = {0,1}^u || {0,1}^k1 : true ==> (a = b).

(** ******************************************* *)
(**    Operator and Axiom about map_to_list     *)
(** ******************************************* *)
op map_to_list : ('a, 'b) map -> 'a list.

axiom equiv_dom_list : 
  forall(M : ('a, 'b) map, x : 'a), 
    in_dom(x, M) <=> mem(x, map_to_list(M)).

axiom bound_length :
  forall(M : ('a, 'b) map, x : 'a, v : 'b), !(in_dom(x, M)) => 
    (length(map_to_list(M[x <- v])) = 1 + length(map_to_list(M))).

(** ********************************************** *)
(** Operator, Lemma and Axiom about high/low bits  *)
(** ********************************************** *)
op high_bits_ku : (bitstring{ku}) -> bitstring{u}.
op low_bits_ku  : (bitstring{ku}) -> bitstring{k1}.

op high_bits_k  : (bitstring{k}) -> bitstring{ku}.
op low_bits_k   : (bitstring{k}) -> bitstring{p}.

axiom high_bits_k_spec : 
  forall(s : bitstring{ku}, t : bitstring{p}),
    high_bits_k(s || t) = s. 

axiom low_bits_k_spec : 
  forall(s : bitstring{ku}, t : bitstring{p}),
    low_bits_k(s || t) = t.

axiom low_bits_ku_spec : 
  forall(x : bitstring{u}, y : bitstring{k1}),
    low_bits_ku(x || y) = y.

axiom high_bits_ku_spec : 
  forall(x : bitstring{u}, y : bitstring{k1}),
    high_bits_ku(x || y) = x.

axiom split_k_spec : 
  forall(x : bitstring{k}), 
    x = (high_bits_k(x) || low_bits_k(x)).

axiom split_ku_spec :
  forall(x : bitstring{ku}),
    x = (high_bits_ku(x) || low_bits_ku(x)).

axiom assoc_xor_app_k :
  forall(x, y : bitstring{k}),
    let x1 = high_bits_k(x) in 
    let x2 = low_bits_k(x) in
    let y1 = high_bits_k(y) in
    let y2 = low_bits_k(y) in
    ((x1 || x2) ^^ (y1 || y2)) = ((x1 ^^ y1) || (x2 ^^ y2)). 

axiom assoc_xor_app_ku :
  forall(x, y : bitstring{ku}),
    let x1 = high_bits_ku(x) in 
    let x2 = low_bits_ku(x) in
    let y1 = high_bits_ku(y) in
    let y2 = low_bits_ku(y) in
    ((x1 || x2) ^^ (y1 || y2)) = ((x1 ^^ y1) || (x2 ^^ y2)). 

lemma assoc_xor_low_k :
  forall(x, y : bitstring{k}),
    (low_bits_k(x ^^ y) = bs0_p) <=> ((low_bits_k(x) ^^ low_bits_k(y)) = bs0_p).

lemma equiv_axlk_0 :
  forall(x, y : bitstring{k}),
    (low_bits_k(x ^^ y) = bs0_p) <=> (low_bits_k(x) = low_bits_k(y)).

lemma assoc_xor_low_ku :
  forall(x, y : bitstring{ku}),
    (low_bits_ku(x ^^ y) = bs0_k1) <=> 
    ((low_bits_ku(x) ^^ low_bits_ku(y)) = bs0_k1).

lemma equiv_axlku_0 :
  forall(x, y : bitstring{ku}),
    (low_bits_ku(x ^^ y) = bs0_k1) <=> (low_bits_ku(x) = low_bits_ku(y)).

lemma assoc_xor_high_k :
  forall(x, y : bitstring{k}),
    (high_bits_k(x ^^ y) = bs0_ku) <=> 
    ((high_bits_k(x) ^^ high_bits_k(y)) = bs0_ku).

lemma equiv_axhk_0 :
  forall(x, y : bitstring{k}),
    (high_bits_k(x ^^ y) = bs0_ku) <=> (high_bits_k(x) = high_bits_k(y)).

lemma assoc_xor_high_ku :
  forall(x, y : bitstring{ku}),
    (high_bits_ku(x ^^ y) = bs0_u) <=> ((high_bits_ku(x) ^^ high_bits_ku(y)) = bs0_u).

lemma equiv_axhku_0 :
  forall(x, y : bitstring{ku}),
    (high_bits_ku(x ^^ y) = bs0_u) <=> (high_bits_ku(x) = high_bits_ku(y)).

(** ******************************************* *)
(**          Definition of eq_except            *)
(** ******************************************* *)
pred eq_except(M1, M2 : ('a, 'b) map, a : 'a) = 
  forall (w: 'a), 
    w <> a => (M1[w] = M2[w] && (in_dom(w,M1) <=> in_dom(w,M2))).

lemma eqe_update_diff : 
  forall(M1, M2 : ('a, 'b) map, a, a' : 'a, b : 'b), 
    eq_except(M1, M2, a) => eq_except(M1[a' <- b], M2[a' <- b], a).

lemma eqe_update_same_L : 
 forall(M1, M2 : ('a, 'b) map, a : 'a, b : 'b), 
    eq_except(M1, M2, a) => eq_except(M1[a <- b], M2, a).

lemma eqe_update_same_R : 
 forall(M1, M2 : ('a, 'b) map, a : 'a, b : 'b), 
    eq_except(M1, M2, a) => eq_except(M1, M2[a <- b], a).

(** ******************************************* *)
(**         Definition of adversaries           *)
(** ******************************************* *)
adversary A1(pk:pkey) : message * message {
  bitstring{p} -> bitstring{ku}; 
  bitstring{ku} -> bitstring{p};
  cipher -> bitstring{u}}.

adversary A2(y:cipher) : bool {
  bitstring{p} -> bitstring{ku}; 
  bitstring{ku} -> bitstring{p};
  cipher -> bitstring{u}}.

(** ******************************************* *)
(**      Definition of the game IND-CCA2        *)
(** ******************************************* *)
game INDCCA = {

  var Gm : t_Gm
  var Hm : t_Hm
  var pks : pkey
  var sks : skey
  var cs : cipher
  var hc, gc, dc : int

  fun G(x : bitstring{p}) : bitstring{ku} = {
    var g : bitstring{ku} = {0,1}^(ku);
    if (!in_dom(x, Gm)) { Gm[x] = g; }
    return Gm[x];
  }

  fun G_A(x : bitstring{p}) : bitstring{ku} = {
    var _ku : bitstring{ku};
    if (gc < qG){
      _ku = G(x);
      gc = gc + 1;
    } else { 
      _ku = bs0_ku; 
    }
    return _ku;
  }

  fun H(x : bitstring{ku}) :  bitstring{p} = {
    var h : bitstring{p} = {0,1}^p;
    if (!in_dom(x, Hm)) { Hm[x] = h; }
    return Hm[x];
  }
  
  fun H_A(x : bitstring{ku}) : bitstring{p} = {
    var _p : bitstring{p};
    if (hc < qH) {
      _p = H(x);
      hc = hc + 1;
    } else {
      _p = bs0_p;
    }
    return _p;
  }

  fun D(x : cipher) : bitstring{u} = {
    var g, s : bitstring{ku};
    var h, t, r : bitstring{p};
    var result : bitstring{u};

    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    h = H(s);
    r = t ^^ h;
    g = G(r);
    result = bs0_u;
    if (low_bits_ku(s ^^ g) = bs0_k1) {
      result = high_bits_ku(s ^^ g);
    }
    return result;
  }

  fun D_A1(x : cipher) : bitstring{u} = {
    var _u : bitstring{u};
    if (dc < qD){
      _u = D(x);
      dc = dc + 1;
    } else {
      _u = bs0_u;
    }
    return _u;
  }
    
  fun D_A2(x : cipher) : bitstring{u} = {
    var _u : bitstring{u};
    if (dc < qD && x <> cs){
      _u = D(x);
      dc = dc + 1;
    } else {
      _u = bs0_u;
    }
    return _u;
  }

  fun KG() : key = {
    var x : key = kg();
    return x;
  }

  fun Enc(pk:pkey, m:message): cipher = {
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    r = {0,1}^p;
    g = G(r);
    s = g ^^ (m || bs0_k1);
    h = H(s);
    t = h ^^ r;
    return f(pk, s || t);
  }

  abs A1 = A1 {G_A, H_A, D_A1}
  abs A2 = A2 {G_A, H_A, D_A2}

  fun Main() : bool = {
    var b, b' : bool;
    var m0, m1 : message;
    cs = bs0_k;
    hc = 0; gc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    (pks, sks) = KG();
    (m0, m1) = A1(pks);
    b = {0,1};
    cs = Enc(pks, b? m1 : m0);
    b' = A2(cs);
    return b = b';
  }
}.

(** ******************************************* *)
(**       Definition of the Game IND-CCA'       *)
(**                                             *)
(** The differents steps are :                  *)
(**     # Inline Encryption function            *)
(**     # Inline call to G and KG               *)
(**     # Add flag bad in G                     *)
(** ******************************************* *)
game INDCCA' = INDCCA 
  var rs, hs, ts : bitstring{p}
  var ss : bitstring{ku}
  var bad : bool
  where G = {
    var g : bitstring{ku} = {0,1}^(ku);
    bad = bad || x = rs;
    if (!in_dom(x, Gm)) { 
      Gm[x] = g;
    }
    return Gm[x];
  }
  and D_A1 = {
    var _u : bitstring{u};
    if (dc < qD){
      _u = D(x);
      dc = dc + 1;
    } else {
      _u = bs0_u;
    }
    return _u;
  }
  and D_A2 = {
    var _u : bitstring{u};
    if (x <> cs){
      _u = D_A1(x);
    } else {
      _u = bs0_u;
    }
    return _u;
  }
  and Main = {
    var b, b' : bool;
    var m0, m1 : message;
    var k : key;
    var g, s : bitstring{ku};
    var h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    (m0, m1) = A1(pks);
    b = {0,1};
    g = {0,1}^ku;
    if (!in_dom(rs, Gm)) { 
      Gm[rs] = g; 
    } else {
      g = Gm[rs];
    }
    s = g ^^ ((b? m1 : m0) || bs0_k1);
    h = H(s);
    t = h ^^ rs;
    cs = f(pks, s || t);
    b' = A2(cs);
    return b = b';
  }.

equiv INDCCA_INDCCA' : INDCCA.Main ~ INDCCA'.Main : true ==> ={res}.
inline Enc, KG, G.
eqobs_in (={Gm, Hm, gc, hc, dc, sks, cs}) (true) (={b, b'}).
swap{1} 13 -4; swap{2} 2 1.
!2 (wp; rnd).
auto (={Gm, Hm, gc, hc, dc, sks, cs}).
trivial.
save.

claim Pr_INDCCA_INDCCA' : INDCCA.Main[res] = INDCCA'.Main[res] 
  using INDCCA_INDCCA'.

(** ******************************************* *)
(**          Definition of the Game G1          *)
(**                                             *)
(** The differents steps are :                  *)
(**     # Add var ss which is an Optimistic     *)      
(**       Sampling between g and s              *)
(**     # Deadcode g                            *)
(**     # Add flag bad1, bad2 and bad3 in D     *)
(**                                             *)
(** These games are upto bad, so we want to     *)
(** show the probability below.                 *)
(**                                             *)
(**     |INDCCA'.res - G1.res| <=  G1.bad       *)
(** ******************************************* *)
game G1 = INDCCA'
  var bad1, bad2, bad3 : bool
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
 
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^ku;
(** Case : in_dom(s, Hm) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
(**   Inline  G *)
      if(in_dom(r, Gm)){
        g_0 = Gm[r];
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          result = high_bits_ku(s ^^ g_0);
        } else {
          result = bs0_u;
        }
      } else {
        Gm[r] = g_0;
        bad = bad || (r = rs);
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          bad1 = true;
          result = high_bits_ku(s ^^ g_0);
        } else {
          result = bs0_u;
        }
      }
    } else {
(** Case : !in_dom(s, Hm) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
(**   Inline G *)
      if(in_dom(r, Gm)){
        bad2 = true;
        g_0 = Gm[r];
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          result = high_bits_ku(s ^^ g_0);
        } else {
          result = bs0_u;
        }
      } else {
        bad3 = bad3 || (r = rs);
        bad = bad || (r = rs);
        Gm[r] = g_0;
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          bad1 = true;
          result = high_bits_ku(s ^^ g_0);
        } else {
          result = bs0_u;
        }
      }
    }
    return result;
  }
  and G = {
    var g : bitstring{ku} = {0,1}^(ku);
    if (!in_dom(x, Gm)) { 
      Gm[x] = g;
      bad = bad || x = rs;
    } else {
      g = Gm[x];
    }
    return g;
  }
  and Main = {
    var b, b' : bool;
    var m0, m1 : message;
    var k : key;
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false; bad1 = false; bad2 = false; bad3 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    b = {0,1};
    return b = b';
  }.

equiv INDCCA'_G1 : INDCCA'.Main ~ G1.Main : 
  true ==> ={bad} &&  (!bad{1} => ={res}).
swap {2} -4.
call upto (bad) with
  (={gc, Hm, hc, dc, sks, rs, cs} && 
  eq_except(Gm{1}, Gm{2}, rs{1}) &&
  (in_dom(rs, Gm){2} <=> bad{2})).
inline H.
wp; rnd; wp.
swap{2} 14 2.
rnd (ss ^^ ((b{2}? m1{2} : m0{2}) || bs0_k1)).
rnd.
auto (={gc, hc, dc, Gm, Hm, sks, rs, cs, bad} && 
      (in_dom(rs, Gm){2} <=> bad{2})).
trivial.
save.

claim Pr_INDCCA'_G1 : 
  |INDCCA'.Main[res] - G1.Main[res]| <=  G1.Main[bad] using INDCCA'_G1.
claim Pr_G1_res : G1.Main[res] = 1%r/2%r compute.
claim Pr_INDCCA_G1 : |INDCCA.Main[res] - 1%r/2%r| <=  G1.Main[bad].

unset Pr_INDCCA_INDCCA', Pr_G1_res, Pr_INDCCA'_G1.

(** ******************************************* *)
(**   Games between G1a and G1d are used to     *)
(**   bound events bad1, bad2 and bad3.         *)
(**   At the end we want to get the game G2,    *)
(**   which is equal to the game G2 in the      *)
(**   Zanella's thesis.                         *)
(** ******************************************* *)


(** ******************************************* *)
(**          Definition of the Game G1a         *)
(**                                             *)
(**  We want to show that game G1 and G1a are   *)
(**    # upto bad1 || bad2                      *)
(**    # bad{1} => bad{2} || bad3{2}            *)
(** ******************************************* *)
game G1a = G1
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
 
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^ku;
(** Case : in_dom(s, Hm) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
(**   Inline G *)
      if(in_dom(r, Gm)){
        g_0 = Gm[r];
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          result = high_bits_ku(s ^^ g_0);
        } else {
          result = bs0_u;
        }
      } else {
        Gm[r] = g_0;
        bad = bad || (r = rs);
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          bad1 = true;
        } 
        result = bs0_u;
      }
    } else {
(** Case : !in_dom(s, Hm) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
(**   Inline G *)
      if(in_dom(r, Gm)){
        bad2 = true;
        g_0 = Gm[r];
        result = bs0_u;
      } else {
        bad3 = bad3 || (r = rs);
        Gm[r] = g_0;
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          bad1 = true;
        } 
        result = bs0_u;
      }
    }
    return result;
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false; bad1 = false; bad2 = false; bad3 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    return true;
  }.

equiv G1_G1a : G1.Main ~ G1a.Main : 
  true ==> ((bad1 || bad2){1} <=> (bad1 || bad2){2}) && 
           (!(bad1 || bad2){2} => (={Gm, Hm, gc, hc, dc, sks, cs} && 
           (bad{1} => (bad{2} || bad3{2})))).
rnd{1}.
auto upto (bad1 || bad2) with 
  (={Gm, Hm, gc, hc, dc, sks, rs, cs} && (bad{1} => bad{2} || bad3{2})).
trivial.
save.

claim Pr_G1_bad : 
  G1.Main[bad] = G1.Main[bad &&  (bad1 || bad2)] + 
                 G1.Main[bad && !(bad1 || bad2)] split.

claim Pr_G1_G1a_1 : 
  G1.Main[bad && (bad1 || bad2)] <= G1a.Main[bad1 || bad2] using G1_G1a.

claim Pr_G1_G1a_2 : 
  G1.Main [bad && !(bad1 || bad2)] <= G1a.Main[bad || bad3] using G1_G1a.

claim Pr_G1a_split_1 : 
  G1a.Main[bad1 || bad2] <= G1a.Main[bad1] + G1a.Main[bad2] compute.

claim Pr_G1a_split_2 : 
  G1a.Main[bad || bad3] <= G1a.Main[bad] + G1a.Main[bad3] split.

claim Pr_G1_G1a : 
  G1.Main[bad] <= G1a.Main[bad]  + G1a.Main[bad1] + 
                  G1a.Main[bad2] + G1a.Main[bad3].

claim Pr_INDCCA_G1a : 
  |INDCCA.Main[res] - 1%r/2%r| <= G1a.Main[bad]  + G1a.Main[bad1] + 
                                  G1a.Main[bad2] + G1a.Main[bad3].

unset Pr_G1_bad, Pr_G1_G1a_1, Pr_G1_G1a_2, Pr_G1a_split_1, 
      Pr_G1a_split_2, Pr_G1_G1a.


(** ******************************************* *)
(**          Definition of the Game G1b         *)
(**                                             *)
(**  The variable g_0 is redefined as an append *)
(**  between 2 random to get the high_bits and  *)
(**  low_bits parts of g_0                      *)
(**                                             *)
(**  We show that game G1a are observationally  *) 
(**  to G1b, so the probability of each event   *)
(**  is equal in both games.                    *)
(** ******************************************* *)
game G1b = G1a
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^u || {0,1}^k1;
    result = bs0_u;
(** Case : in_dom(s, Hm) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
(**   Inline G *)
      if(in_dom(r, Gm)){
        g_0 = Gm[r];
        if(low_bits_ku(s ^^ g_0) = bs0_k1) {
          result = high_bits_ku(s ^^ g_0);
        }
      } else {
        Gm[r] = g_0;
        if (r = rs) {
          bad = true;
        }
        if(low_bits_ku(s) = low_bits_ku(g_0)) {
          bad1 = true;
        } 
      }
    } else {
(** Case :!in_dom(s, Hm) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
(**   Inline G *)
      if(in_dom(r, Gm)){
        bad2 = true;
      } else {
        if (r = rs) {
          bad3 = true;
        }
        Gm[r] = g_0;
        if(low_bits_ku(s) = low_bits_ku(g_0)) {
          bad1 = true;
        } 
      }
    }
    return result;
  }.

equiv G1a_G1b_D : G1a.D ~ G1b.D : 
  (={Gm, Hm, sks, bad, bad1, bad2, bad3, rs}).
app 3 4 (={Gm, Hm, sks, bad, bad1, bad2, bad3, s, t, g_0, rs} && 
        (result{2} = bs0_u{2})).
wp; apply : split_ku(); trivial.
derandomize; trivial.
save.

equiv G1a_G1b : G1a.Main ~ G1b.Main : 
  true ==> ={Gm, Hm, sks, bad, bad1, bad2, bad3, rs, gc, hc, dc, cs} 
  by auto (={Gm, Hm, sks, bad, bad1, bad2, bad3, rs, gc, hc, dc, cs}).

claim Pr_G1ab_bad  : G1a.Main[bad]  = G1b.Main[bad]  using G1a_G1b.
claim Pr_G1ab_bad1 : G1a.Main[bad1] = G1b.Main[bad1] using G1a_G1b.
claim Pr_G1ab_bad2 : G1a.Main[bad2] = G1b.Main[bad2] using G1a_G1b.
claim Pr_G1ab_bad3 : G1a.Main[bad3] = G1b.Main[bad3] using G1a_G1b.

claim Pr_INDCCA_G1b : 
  |INDCCA.Main[res] - 1%r/2%r| <= G1b.Main[bad]  + G1b.Main[bad1] + 
                                  G1b.Main[bad2] + G1b.Main[bad3].

unset Pr_G1ab_bad, Pr_G1ab_bad1, Pr_G1ab_bad2, Pr_G1ab_bad3.

(** ******************************************* *)
(**          Definition of the Game G1c         *)
(**                                             *)
(**  # Optimistic Sampling between r and h_0    *)
(**                                             *) 
(**  Add a condition in the oracle D to bound   *)
(**  the number of call that an adversary can   *)
(**  do to this oracle.                         *)
(** ******************************************* *)
game G1c = G1b
  where D = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    result = bs0_u;
(** Case : length(map_to_list(Gm)) < qD + qG *)
    if(length(map_to_list(Gm)) < qD + qG){
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
(**     Inline G *)
        if(mem(r, map_to_list(Gm))){
          g_0 = Gm[r];
          if(low_bits_ku(s ^^ g_0) = bs0_k1) {
            result = high_bits_ku(s ^^ g_0);
          }
        } else {
          Gm[r] = g_0;
          if (r = rs) {
            bad = true;
          }
          if(low_bits_ku(s) = g_0_l) {
            bad1 = true;
          } 
        }
      } else {
(**   Case : in_dom(s, Hm) *)
        r = {0,1}^p;
        Hm[s] = r ^^ t;
(**     Inline G *)
        if(mem(r, map_to_list(Gm))){
          bad2 = true;
        } else {
          if (r = rs) {
            bad3 = true;
          }
          Gm[r] = g_0;
          if(low_bits_ku(s) = g_0_l) {
            bad1 = true;
          } 
        }
      }
    }
    return result;
  }.

equiv G1b_G1c_D_A1 : G1b.D_A1 ~ G1c.D_A1 : 
  (={Gm, Hm, sks, bad, bad1, bad2, bad3, rs, gc, hc, dc, cs} &&
  (length(map_to_list(Gm{2})) <= dc{2} + gc{2}) &&
  dc{2} <= qD && gc{2} <= qG).
inline D; if.
condt{2} at 8; [trivial | ].
app 5 7 
  (={Gm,Hm,sks,bad,bad1,bad2,bad3,rs,gc,hc,dc,cs,x,x_0,s,t,g_0,result} &&  
  (length(map_to_list(Gm{2})) <= dc{2} + gc{2}) &&
  dc{2} < qD && gc{2} <= qG && g_0{1} = (g_0_h{2} || g_0_l{2})).
derandomize; trivial.
if; [trivial | ].
wp; rnd(t{2} ^^ r); trivial.
trivial.
save.

axiom mtl_empty_spec : 
  forall(M : ('a, 'b) map),
    M = empty_map => map_to_list(M) = [].

lemma length_empty_map :
  forall(M : ('a, 'b) map),
    M = empty_map => length(map_to_list(M)) = 0.

equiv G1b_G1c : G1b.Main ~ G1c.Main : 
  true ==> (={bad,bad1,bad2,bad3})
  by auto (={Gm,Hm,sks,bad,bad1,bad2,bad3,rs,ss,gc,hc,dc,cs} && 
          (length(map_to_list(Gm{2})) <= dc{2} + gc{2}) &&
          (dc{2} <= qD) && (gc{2} <= qG)).

claim Pr_G1bc_bad : 
  G1b.Main[bad] = G1c.Main[bad] using G1b_G1c.
claim Pr_G1bc_bad1 : 
  G1b.Main[bad1] = G1c.Main[bad1] using G1b_G1c.
claim Pr_G1bc_bad2 : 
  G1b.Main[bad2] = G1c.Main[bad2] using G1b_G1c.
claim Pr_G1bc_bad3 : 
  G1b.Main[bad3] = G1c.Main[bad3] using G1b_G1c.

claim Pr_INDCCA_G1c : 
  |INDCCA.Main[res] - 1%r/2%r| <= G1c.Main[bad]  + G1c.Main[bad1] + 
                                  G1c.Main[bad2] + G1c.Main[bad3].

unset Pr_G1bc_bad, Pr_G1bc_bad1, Pr_G1bc_bad2, Pr_G1bc_bad3.

(** ******************************************* *)
(**          Definition of the Game G1d         *)
(**                                             *)
(**   # Inline D in D_A1                        *)
(**   # Replace call to D in D_A2 to D_A1       *)
(** ******************************************* *)
game G1d = G1c
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;  
(**   Case : (length(map_to_list(Gm)) < qD + qG *)       
      if(length(map_to_list(Gm)) < qD + qG){
(**     Case : in_dom(s, Hm) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
(**       Inline G *)
          if(mem(r, map_to_list(Gm))){
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            Gm[r] = g_0;
            if (r = rs) {
              bad = true;
            }
            if(low_bits_ku(s) = g_0_l) {
              bad1 = true;
            } 
          }
        } else {
(**     Case : !in_dom(s, Hm) *)
          r = {0,1}^p;
          Hm[s] = r;
(**       Inline G *)
          if (r = rs) bad3 = true;
          if(mem(r, map_to_list(Gm))){
            bad2 = true;
          } else {
            Gm[r] = g_0;
            if(low_bits_ku(s) = g_0_l) {
              bad1 = true;
            } 
          }
        }
      }
      dc = dc + 1;
    } else {
(** Case : !(dc < qD) *)
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and D_A2 = {
    var _u : bitstring{u};
    if (x <> cs){
      _u = D_A1(x);
    } else {
      _u = bs0_u;
    }
    return _u;
  }.

equiv G1c_G1d : G1c.Main ~ G1d.Main : 
  true ==> ={bad, bad1, bad2, dc} && dc{2} <= qD && (bad3{1} => bad3{2})
  by auto (={Gm, Hm, gc, hc, dc, sks, bad, bad1, bad2, rs, cs} &&
           dc{2} <= qD && (bad3{1} => bad3{2})).

claim Pr_G1cd_bad  : 
  G1c.Main[bad] <= G1d.Main[bad] using G1c_G1d.
claim Pr_G1cd_bad1 : 
  G1c.Main[bad1] <= G1d.Main[bad1 && dc <= qD ] using G1c_G1d.
claim Pr_G1cd_bad2 : 
  G1c.Main[bad2] <= G1d.Main[bad2 && dc <= qD] using G1c_G1d.
claim Pr_G1cd_bad3 : 
  G1c.Main[bad3] <= G1d.Main[bad3 && dc <= qD] using G1c_G1d.

claim Pr_G1d_bad1 : 
  G1d.Main[bad1 && dc <= qD] <= qD%r * (1%r / (2^k1)%r) 
  compute 10 (bad1), (dc).

timeout 30.

unset Pr_INDCCA_G1, Pr_INDCCA_G1a, Pr_INDCCA_G1b, Pr_INDCCA_G1c, 
      Pr_G1d_bad1.

claim Pr_G1d_bad2 : 
  G1d.Main[bad2 && dc <= qD] <= qD%r * ((qD + qG)%r / (2^p)%r) 
  compute 10 (bad2), (dc).

claim Pr_G1d_bad3 : 
  G1d.Main[bad3 && dc <= qD] <= qD%r * ((1%r) / (2^p)%r) 
  compute 10 (bad3), (dc).

timeout 3.

set Pr_INDCCA_G1, Pr_INDCCA_G1a, Pr_INDCCA_G1b, Pr_INDCCA_G1c, 
    Pr_G1d_bad1.

claim Pr_INDCCA_G1d : |INDCCA.Main[res] - 1%r/2%r| <= 
  G1d.Main[bad] + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G1cd_bad, Pr_G1cd_bad1, Pr_G1cd_bad2, Pr_G1cd_bad3, 
      Pr_G1d_bad1, Pr_G1d_bad2, Pr_G1d_bad3.

(** ******************************************* *)
(**          Definition of the Game G2          *)
(**                                             *)
(**   # Remove var bad1, bad2 and bad3          *)
(**   # Remove function KG and Enc              *)
(**                                             *)
(**   We want to bound the event bad            *)
(** ******************************************* *)

game G2 = {
  var Gm : t_Gm
  var Hm : t_Hm
  var pks : pkey
  var sks : skey
  var cs : cipher
  var gc, hc, dc : int
  var rs, hs, ts : bitstring{p}
  var ss : bitstring{ku}
  var bad : bool

  fun G = G1d.G
  fun G_A = G1d.G_A
  fun H = G1d.H
  fun H_A = G1d.H_A

  fun D_A1 (x : cipher) : bitstring{u} = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h, _u : bitstring{u};
    var g_0_l : bitstring{k1};
(** Case : dc < qD *)
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;
(**   Case : length(map_to_list(Gm)) < qD + qG *)
      if(length(map_to_list(Gm)) < qD + qG){
(**     Case : in_dom(s, Hm) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
(**       Inline G *)
          if(mem(r, map_to_list(Gm))){
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            Gm[r] = g_0;
            if (r = rs) {
              bad = true;
            }
          }
        } else {
(**     Case : !in_dom(s, Hm) *)
          r = {0,1}^p;
          Hm[s] = r;
(**       Inline G *)
          if(!mem(r, map_to_list(Gm))){
            Gm[r] = g_0;
          }
        }
      }
      dc = dc + 1;
    } else {
(** Case : !(dc < qD) *)
      result = bs0_u;
    }
    _u = result;
    return _u;
  }

  fun D_A2 = G1d.D_A2
  fun A1 = G1d.A1
  fun A2 = G1d.A2

  fun Main () : bool = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    cs = bs0_k;
    gc = 0;
    hc = 0;
    dc = 0;
    Gm = empty_map;
    Hm = empty_map;
    bad = false;
    k = kg ();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1 (pks);
    hs = H (ss);
    ts = hs ^^ rs;
    cs = f (pks,ss || ts);
    b' = A2 (cs);
    return true;
  }  
}.

equiv G1d_G2 : G1d.Main ~ G2.Main : 
  true ==> ={Gm, Hm, sks, bad, dc, cs}
  by auto (={Gm, Hm, sks, bad, gc, hc, dc, rs, cs}).

claim Pr_G1d_G2_bad : G1d.Main[bad] = G2.Main[bad] using G1d_G2.

claim Pr_INDCCA_G2 : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2.Main[bad] + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G1d_G2_bad.

(** ******************************************* *)
(**   Games between G2a and G2e are used to     *)
(**   bound the probability of bad in the       *)
(**   game G2.                                  *)
(**   To do that we will introduce new events   *)
(**   in games, which are bad4 and bad5         *)
(**   Then we will get the bound :              *)
(**       G2.bad <= G2e.bad + (qD / 2^k1)       *)
(** ******************************************* *)

type t_Gm_bis = (bitstring{p}, bool * bitstring{ku}) map.

(** ******************************************* *)
(**          Definition of the Game G2a         *)
(**                                             *)
(**  We replace the map Gm by Gm_bis which is   *)
(**  of the form : (bs_p, bool * bs_ku).        *)
(**  This map is used to identify which Oracle  *)
(**  modify the value bs_ku.                    *)
(**  This map is equal to the Gm map except for *)
(**  the boolean.                               *)
(**  If the boolean is :                        *)
(**        # False --> Modify by Oracle G       *) 
(**        # True  --> Modify by Oracle D       *)
(** ******************************************* *)
game G2a = G2 
  remove Gm
  var Gm_bis : t_Gm_bis
  var bad4 : bool
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h, _u : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
(** Case : dc < qD *)
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;  
(**   Case : length(map_to_list(Gm_bis)) < qD + qG *)       
      if(length(map_to_list(Gm_bis)) < qD + qG){
(**     Case : in_dom(s, Hm) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
(**       Inline G *)
          if(mem(r, map_to_list(Gm_bis))){
            (d, g_0) = Gm_bis[r];
            if (d = true){
              if(low_bits_ku(s ^^ g_0) = bs0_k1) {
                bad4 = true;
                result = high_bits_ku(s ^^ g_0);
              }
            } else {
              if(low_bits_ku(s ^^ g_0) = bs0_k1) {
                result = high_bits_ku(s ^^ g_0);
              }
            }
          } else {
            Gm_bis[r] = (true, g_0);
            if (r = rs) {
              bad = true;
            }
          }
        } else {
          r = {0,1}^p;
          Hm[s] = r;
            (** Inlining de G *)
          if(!mem(r, map_to_list(Gm_bis))){
            Gm_bis[r] = (true, g_0);
          }
        }
      }    
      dc = dc + 1;
    } else {
(** Case : !(dc < qD) *)
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and G = {
    var g : bitstring{ku};
    var d : bool;
    g = {0,1}^ku;
    if (!in_dom(x,(Gm_bis))){ 
      bad = bad || x = rs;
    } else {
      (d, g) = Gm_bis[x];
    }
    Gm_bis[x] = (false, g);
    return g;   
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm_bis = empty_map; Hm = empty_map;
    bad = false; bad4 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    return true;
  }.

pred eq_dom (M1 : ('a, 'b) map, M2 : ('a, 'c) map) =
 forall(x : 'a), in_dom(x, M1) = in_dom(x, M2).
  
pred eq_map_snd (M1 : ('a, 'b) map, M2 : ('a, ('c * 'b)) map) =
  eq_dom(M1, M2) && forall(x: 'a), in_dom(x, M1) => M1[x] = snd(M2[x]).

axiom eq_map_to_list : 
  forall(M1 : ('a, 'b) map, M2 : ('a, 'c) map), 
     eq_dom(M1, M2) => map_to_list(M1) = map_to_list(M2).

lemma eq_map_rec :
  forall(M : t_Gm, N : t_Gm_bis, x : bitstring{p}, y : bitstring{ku}, 
  b : bool),
    eq_map_snd(M, N) => eq_map_snd(M[x <- y], N[x <- (b, y)]).

lemma eq_map_rec2 :
  forall(M : t_Gm, N : t_Gm_bis, x : bitstring{p}, y : bitstring{ku}, 
  b : bool),
    eq_map_snd(M, N) => in_dom(x, M) =>
    eq_map_snd(M, N[x <- (b, snd(N[x]))]).

equiv G2_G2a : G2.Main ~ G2a.Main : true ==> ={bad} 
  by auto (={Hm, gc, hc, dc, bad, sks, rs, cs} && 
          eq_map_snd(Gm{1}, Gm_bis{2})).

claim Pr_G2_G2a_bad : G2.Main[bad] = G2a.Main[bad] using G2_G2a.
claim Pr_INDCCA_G2a : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2a.Main[bad] + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2_G2a_bad.

(** ******************************************* *)
(**          Definition of the Game G2b         *)
(**                                             *)
(**          These games are upto bad4.         *)
(** ******************************************* *)
game G2b = G2a
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h, _u : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
(** Case : dc < qD *)
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;  
(**   Case : length(map_to_list(Gm_bis)) < qD + qG *)      
      if(length(map_to_list(Gm_bis)) < qD + qG){
(**     Case : in_dom(s, Hm) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
(**       Inline G *)
          if(mem(r, map_to_list(Gm_bis))){
            (d, g_0) = Gm_bis[r];
            if (d = true){
              if(low_bits_ku(s ^^ g_0) = bs0_k1) {
                bad4 = true;
                }
            } else {
              if(low_bits_ku(s ^^ g_0) = bs0_k1) {
                result = high_bits_ku(s ^^ g_0);
              }
            }
          } else {
            Gm_bis[r] = (true, g_0);
            if (r = rs) {
              bad = true;
            }
          }
        } else {
(**     Case : !in_dom(s, Hm) *)
          r = {0,1}^p;
          Hm[s] = r;
(**       Inline G *)
          if(!mem(r, map_to_list(Gm_bis))){
            Gm_bis[r] = (true, g_0);
          }
        }
      }    
      dc = dc + 1;
    } else {
(** Case : !(dc < qD) *)
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm_bis = empty_map; Hm = empty_map; 
    bad = false; bad4 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    return true;
  }.

equiv G2a_G2b : G2a.Main ~ G2b.Main : true ==> ={bad4} && 
  (!bad4{1} => ={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs, res})
by auto upto (bad4) with (={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs}).

claim Pr_G2ab_bad : G2a.Main[bad] <= G2b.Main[bad] + G2b.Main[bad4]   
  using G2a_G2b.

claim Pr_INDCCA_G2b : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2b.Main[bad] + G2b.Main[bad4] + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2ab_bad.

(** ******************************************* *)
(**       Definition of the function P          *)
(** ******************************************* *)
op P : 
  (bitstring{ku}, bitstring{p}, skey, (bool * cipher) list, t_Hm) -> bool.

axiom P_spec :
  forall(g : bitstring{ku}, r : bitstring{p}, sk : skey, 
         L : (bool * cipher) list, H : t_Hm),
    P(g, r, sk, L, H) <=> 
      exists(d: bool, c : cipher), mem((d, c), L) => 
        let s = high_bits_k(finv(sk, c)) in 
        let t = low_bits_k(finv(sk, c)) in
          in_dom(s, H) && (r = t ^^ H[s]) && 
          (low_bits_ku(s ^^ g) = bs0_k1).

(** ******************************************* *)
(**          Definition of the Game G2c         *)
(**                                             *)
(**     # Introduction of the variable bad5     *)
(**     # Put while instruction before the call *)
(**       to the adversary A1 to prepare the    *)
(**       next Eager Sampling.                  *)
(** ******************************************* *)
game G2c = G2b 
  remove bad4
  var bad5, Cdef : bool
  var LD : (bool * cipher) list
  var Ltmp : bitstring{p} list
  var a : bitstring{p}
  var c : bitstring{ku}
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result, g_0_h, _u : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
(** Case : dc < qD *)
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      LD = (Cdef, x)::LD;
      result = bs0_u;  
(**   Case : length(map_to_list(Gm_bis)) < qD + qG *)       
      if(length(map_to_list(Gm_bis)) < qD + qG){
(**     Case : in_dom(s, Hm) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
(**       Inline G *)
          if(mem(r, map_to_list(Gm_bis))){
            (d, g_0) = Gm_bis[r];
            if (d <> true){
              if(low_bits_ku(s ^^ g_0) = bs0_k1) {
                result = high_bits_ku(s ^^ g_0);
              }
            }
          } else {
            Gm_bis[r] = (true, g_0);
            if (r = rs) {
              bad = true;
            }
          }
        } else {
(**     Case : !in_dom(s, Hm) *)
          r = {0,1}^p;
          Hm[s] = r;
          if(!mem(r, map_to_list(Gm_bis))){
            Gm_bis[r] = (true, g_0);
          }
        }
      }    
      dc = dc + 1;
    } else {
(** Case : !(dc < qD) *)
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and G = {
    var g : bitstring{ku};
    var d : bool;
    g = {0,1}^ku;
    if (!in_dom(x,(Gm_bis))) { 
      bad = bad || x = rs;
      Gm_bis[x] = (false, g);
    } else {
      (d, g) = Gm_bis[x];
      if(d = true){
        Gm_bis[x] = (false, g);
        bad5 = bad5 || P(g, x, sks, LD, Hm);
      }
    }
    return snd(Gm_bis[x]);   
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
(** Init variable to help the eager *)
    hs = bs0_p; ts = bs0_p; a = bs0_p; c = bs0_ku;
(** End of init helping variables *)
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm_bis = empty_map; Hm = empty_map;
    LD = []; Ltmp = [];
    Cdef = false;
    bad = false; bad5 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    Ltmp = map_to_list(Gm_bis);
    while (Ltmp <> []){
      a = hd(Ltmp);
      if(fst(Gm_bis[a]) = true){
        c = {0,1}^u || {0,1}^k1;
        Gm_bis[a] = (true, c);
      }
      Ltmp = tl(Ltmp);
    }
    a = bs0_p;
    c = bs0_ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

op phi : (skey, t_Gm_bis, t_Hm, (bool * cipher) list) -> bool.

axiom phi_spec :
  forall(sk : skey, G : t_Gm_bis, H : t_Hm, D : (bool * cipher) list),
    phi(sk, G, H, D) <=>
    exists(d : bool, c : cipher), mem((d, c), D) &&
      let s = high_bits_k(finv(sk, c)) in 
      let t = low_bits_k(finv(sk, c)) in
      let r = t ^^ H[s] in
        in_dom(r, G) && in_dom(s, H) && fst(G[r]) &&
        low_bits_ku(s ^^ snd(G[r])) = bs0_k1.

pred eq_ext (M1, M2 : ('a, 'b) map) =
  forall(x : 'a),
    in_dom(x, M1) = in_dom(x, M2) && M1[x] = M2[x].

axiom eq_ext_spec : 
  forall(M1, M2 : ('a, 'b) map),
    eq_ext(M1, M2) => M1 = M2.

lemma eq_ext_spec_2 :
  forall(M1, M2 : ('a, bool * 'b) map, x : 'a),
    eq_ext(M1, M2) => in_dom(x, M1) => in_dom(x, M2) =>
    eq_ext(M1, M2[x <- (fst(M1[x]), snd(M1[x]))]).

equiv G2b_G2c_D_A1 : G2b.D_A1 ~ G2c.D_A1 :
  (={Gm_bis, Hm, sks, bad, rs, gc, hc, dc, cs} &&
  (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})))).
if.
sp.
!2rnd>>.
sp.
if.
if.
trivial.
trivial.
trivial.
trivial.
save.

equiv G2b_G2c_D_A2 : G2b.D_A2 ~ G2c.D_A2 : 
  (={Gm_bis, Hm, sks, bad, rs, gc, hc, dc, cs} &&
  (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2}))))
by auto (={Gm_bis, Hm, sks, bad, rs, gc, hc, dc, cs} &&
     (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})))).

equiv G2b_G2c : G2b.Main ~ G2c.Main : true ==> 
  (={Gm_bis, Hm, pks, sks, bad, rs, gc, hc, dc, cs} &&
  (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})))).
call (={Gm_bis, Hm, pks, sks, bad, rs, gc, hc, dc, cs} && 
     (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})))).
inline H.
wp; !2rnd; wp.
call (={Gm_bis, Hm, pks, sks, bad, rs, gc, hc, dc, cs} && 
     (bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})))).
condf{2} last.
trivial.
trivial.
save.

claim Pr_G2bc_bad : G2b.Main[bad] = G2c.Main[bad] using G2b_G2c.
claim Pr_G2bc_bad4 : 
  G2b.Main[bad4] <= G2c.Main[bad5 || phi(sks, Gm_bis, Hm, LD)] 
  using G2b_G2c.
claim Pr_G2b_G2c : 
  G2b.Main[bad] + G2b.Main[bad4] <= 
  G2c.Main[bad] + G2c.Main[bad5 || phi(sks, Gm_bis, Hm, LD)].
claim Pr_INDCCA_G2c : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2c.Main[bad] + G2c.Main[bad5 || phi(sks, Gm_bis, Hm, LD)] + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2bc_bad, Pr_G2bc_bad4, Pr_G2b_G2c.

(** ******************************************* *)
(**          Definition of the Game G2d         *)
(**                                             *)
(**     # Put while instruction after the call  *)
(**       to the adversary A2.                  *)
(**     # We prove this by using the tactic :   *)
(**               Eager Sampling                *)
(**     # We define c as {0,1}^u || {0,1}^k1    *)
(**       to have the same syntax than g        *)
(** ******************************************* *)
game G2d = G2c
  where G = {
    var g, g_smpl : bitstring{ku};
    var d : bool;
    g = {0,1}^u || {0,1}^k1;
    if (!in_dom (x,Gm_bis)) {
      bad = bad || x = rs;
      Gm_bis[x] = (false,g);
    } else {
      (d, g_smpl) = Gm_bis[x];
      if (d = true) {
        Gm_bis[x] = (false,g);
        bad5 = bad5 || P (g,x,sks,LD,Hm);
      }
    }
    return snd (Gm_bis[x]);
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
(** Init variable to help the eager *)
    hs = bs0_p; ts = bs0_p; a = bs0_p; c = bs0_ku;
(** End of init helping variables *)
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm_bis = empty_map; Hm = empty_map; 
    LD = []; Ltmp = [];
    Cdef = false;
    bad = false; bad5 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    Ltmp = map_to_list(Gm_bis);
    while (Ltmp <> []){
      a = hd(Ltmp);
      if(fst(Gm_bis[a]) = true){
        c = {0,1}^u || {0,1}^k1;
        Gm_bis[a] = (true, c);
      }
      Ltmp = tl(Ltmp);
    }
    a = bs0_p;
    c = bs0_ku;
    return true;
  }. 

(** ******************************************* *)
(**                                             *)
(**   Add some rules to help us in the proof    *)    
(**   below, which is about an Eager sampling   *)
(**                                             *)
(** ******************************************* *)

(** ******************************************* *)
(**   Definition and Operator for split_list    *)    
(** ******************************************* *)
op split_list : ('a list, 'a) -> ('a list * 'a list).

axiom split_list_spec :
  forall(L : 'a list, x : 'a),
    let L1 = fst(split_list(L, x)) in
    let L2 = snd(split_list(L, x)) in
    mem(x, L) => L = L1 ++ x::L2 && !mem(x, L2).

(** ******************************************* *)
(**   Definition and Predicate for eq_except    *)    
(**   for lists.                                *)
(** ******************************************* *)
pred eq_except_list (Ltmp1, Ltmp2, L2 : 'a list, r : 'a) =
  exists(l1 : 'a list), Ltmp1 = l1++r::L2 && Ltmp2 = l1++L2.

axiom eq_head :
  forall(Ltmp1, Ltmp2, L2 : 'a list, r : 'a), 
    eq_except_list(Ltmp1, Ltmp2, L2, r) => length(Ltmp2) > length(L2) => 
    hd(Ltmp1) = hd(Ltmp2).

axiom eq_except_list_rec :
  forall(Ltmp1, Ltmp2, L2 : 'a list, r : 'a), 
    eq_except_list(Ltmp1, Ltmp2, L2, r) => length(Ltmp2) > length(L2) => 
    eq_except_list(tl(Ltmp1), tl(Ltmp2), L2, r).

axiom avoid_dbl : 
  forall(Mtmp1 : ('a, 'b) map, r : 'a, b : 'b),
    !(in_dom(r, Mtmp1)) => 
    let L2 = snd(split_list(map_to_list(Mtmp1[r <- b]), r)) in 
    eq_except_list(map_to_list(Mtmp1[r <- b]), map_to_list(Mtmp1), L2, r).

axiom eq_L2 :
  forall(Ltmp_L, Ltmp_R, L2 : 'a list, r : 'a),
    eq_except_list(Ltmp_L,Ltmp_R,L2,r) =>
    length (Ltmp_L) <=length (L2) + 1 => Ltmp_L = r::L2 && Ltmp_R = L2.

lemma eq_length_plus_one : 
  forall(Ltmp1, Ltmp2, L2 : 'a list, r : 'a), 
    eq_except_list(Ltmp1, Ltmp2, L2, r) =>
    length(Ltmp1) = length(Ltmp2) + 1.

(** ******************************************* *)
(**       Add some rules to the list type       *)
(** ******************************************* *)
axiom length_tl_spec :
  forall(L : 'a list), L <> [] => length(tl(L)) < length(L).

axiom mem_tl :
  forall(x : 'a, L : 'a list), mem(x, tl(L)) => mem(x, L).

axiom mem_hd :
  forall(L : 'a list), L <> [] => mem(hd(L), L).

axiom list_not_empty_spec :
  forall(l : 'a list),
  l <> [] => l = hd(l)::tl(l).

lemma pos_on_L1 :
  forall(Ltmp, l, L2 : 'a list, x : 'a), Ltmp = l++x::L2 => 
  length(Ltmp) > length(L2) + 1 => tl(Ltmp) =tl(l)++x::L2.

lemma pos_on_x :
  forall(Ltmp, l, l2 : 'a list, x : 'a), 
  length(Ltmp) <= length(l2) + 1 => Ltmp = l++x::l2 => Ltmp = x::l2.

(** ******************************************* *)
(**        Add some rules for map_to_list       *)
(** ******************************************* *)
axiom eq_update_map_to_list : 
  forall(M : ('a, ('b * 'c)) map, x : 'a, y : 'b, z : 'c),
  in_dom(x, M) => map_to_list(M) = map_to_list(M[x <- (y, z)]).

axiom eq_map_to_list_upd :
  forall(Mtmp1 : ('a, 'b) map, L2 : 'a list, r : 'a, b, c : 'b), 
  map_to_list(Mtmp1[r <- b]) = map_to_list(Mtmp1[r <- c]).

axiom eq_upd_M2:
  forall(Mtmp1, Mtmp2 : ('a, 'b) map, r : 'a, a : 'b),
    in_dom(r, Mtmp1) && Mtmp1[r] = a && eq_except(Mtmp1, Mtmp2, r) =>
    Mtmp1 = Mtmp2[r <- a]. 
(** ******************************************* *)
(**              End of rules                   *)
(** ******************************************* *)

equiv G2c_G2d : G2d.Main ~ G2c.Main : true ==> 
   ={Gm_bis, Hm, gc, hc, dc, bad, bad5, sks, rs, cs, LD}
   by eager {
     Ltmp = map_to_list(Gm_bis); 
     while(Ltmp <>[]) {
       a = hd(Ltmp);
       if(fst(Gm_bis[a]) = true){
         c = {0,1}^u || {0,1}^k1 ;
         Gm_bis[a] = (true, c);
       }
       Ltmp = tl(Ltmp);
     }
     a = bs0_p;
     c = bs0_ku;
   }.
(** *************************************************** *)
(**                   Oracle D_A1                       *)
(** *************************************************** *)

(** Case : dc < qD *)
  if{1}.
  condt{2} at 5; [wp | ].
  while{2} : true : length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  swap{2} [5 - 11] -4; swap [3 - 5] 2.
  app 4 4 (={Gm_bis, Hm, pks, sks, gc, hc, dc, rs, hs, ts, ss, cs, bad, 
           bad5, LD, Cdef, Ltmp, a, c, x, s, t, LD, result} && 
           dc{1} < qD); [trivial | ].

(** Case : length(map_to_list(Gm_bis)) < qD + qG *)
  case{1} : length(map_to_list(Gm_bis)) < qD + qG.
  condt{1} at 4; [trivial | ].
  condt{2} at 8; [wp | ].
  while{2} : (forall(x : bitstring{p}), 
    mem(x, Ltmp{2}) => in_dom(x, Gm_bis{2})) && 
    length(map_to_list(Gm_bis{1})) = length(map_to_list(Gm_bis{2})) :
    length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].

(** Case : in_dom(s, Hm) *)
  case{1} : in_dom(s, Hm).
  condt{1} at 4; [trivial | ].
  condt{2} at 8; [wp | ].
  while{2} : true : length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  swap{1} 4 -3; swap{2} 8 -7.
  app 1 1 (={Gm_bis, Hm, pks, sks, gc, hc, dc, rs, hs, ts, ss, cs, bad, 
    bad5, LD, Cdef, Ltmp, a, c, x, s, t, LD, result, r} && 
    dc{1} < qD); [trivial | ].

(** Case : mem(r, map_to_list(Gm_bis)) *)
  case{1} : mem(r, map_to_list(Gm_bis)).
  condt{1} at 4; [trivial | ].
  condt{2} at 8; [wp | ].
  while{2} : (map_to_list(Gm_bis{1}) = map_to_list(Gm_bis{2})) && 
    forall(x : bitstring{p}), mem(x, Ltmp{2}) => in_dom(x, Gm_bis{2}) :
    length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  wp.
(** ******************************************* *)
(**   Introduce new map of type t_Gm_bis. Its   *)
(**   goal is to indicate if the value write    *)
(**   in the map comes from oracle G or D.      *)
(** ******************************************* *)
  let{1} Gm_bis' : t_Gm_bis = Gm_bis.
  while : fst(Gm_bis[r]{1}) = fst(Gm_bis'[r]{1}) && 
    (fst(Gm_bis[r]{1}) = false => snd(Gm_bis[r]{1}) = snd(Gm_bis'[r]{1})) &&
    ={Ltmp, Gm_bis};
    [derandomize; trivial | trivial].

(** Case : !mem(r, map_to_list(Gm_bis)) *)
  condf{2} at 8; [wp | ].
  while{2} : (map_to_list(Gm_bis{1}) = map_to_list(Gm_bis{2})) && 
    forall(x : bitstring{p}), mem(x, Ltmp{2}) => in_dom(x, Gm_bis{2}) :
    length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  condf{1} at 4; [trivial | ].
  swap{1} [5 - 7] 4; wp.
(** ******************************************* *)
(**   Split the while in 3 part : L1 ++ r::L2   *)
(** ******************************************* *)
  let{2} Gaux : t_Gm_bis = Gm_bis[r <- (true, bs0_ku)].
  let{1} at 5 L1 : t_domGA = fst(split_list(map_to_list(Gm_bis), r)).
  let{1} at 6 L2 : t_domGA = snd(split_list(map_to_list(Gm_bis), r)).
  let{2} at 2 L1 : t_domGA = fst(split_list(map_to_list(Gaux), r)).
  let{2} at 3 L2 : t_domGA = snd(split_list(map_to_list(Gaux), r)).
  splitw last : length(Ltmp) > length(L2).
(** Ltmp = L2 and we focus on L2*)
  while : eq_except(Gm_bis{1}, Gm_bis{2}, r{1}) && ={Ltmp, r} && 
    Gm_bis[r]{1} = (true, g_0{2}) && !(mem(r{1}, Ltmp{2})) && 
    in_dom(r{1}, Gm_bis{1}).
  derandomize; trivial.
  splitw{1} last : length(Ltmp) > length(L2) + 1.
  condt{1} last.
(** Ltmp = r::L2 and we focus on r*)
  while{1} : ={r} && in_dom(r, Gm_bis){1} && !in_dom(r, Gm_bis){2} && 
    fst(Gm_bis[r]{1}) = true && mem(r, Ltmp){1} &&
    (exists(l : bitstring{p} list), Ltmp{1} = l++r{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
    [derandomize; trivial | trivial].
  condf{1} last.
  derandomize; wp.
(** Ltmp = L1 ++ r::L2 and we focus on L1*)
timeout 5.
  while : eq_except(Gm_bis{1}, Gm_bis{2}, r{1}) && ={L2, r} && 
    eq_except_list(Ltmp{1}, Ltmp{2}, L2{2}, r{2}) && 
    fst(Gm_bis[r]{1}) = true && !(mem(r{1}, L2{2}));
    [trivial | trivial].
timeout 3.
(** Case : !in_dom(s, Hm) *)
  condf{1} at 4; [trivial | ].
  condf{2} at 8; [wp | ].
  while{2} : ={Hm, s} : length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].

(** Case : !mem(r, map_to_list(Gm_bis)) *)
  swap{2} [8-9] -4; swap{2} [1-3] 6; swap{1} [1-3] 2.
  app 2 2 (={Gm_bis,Hm,pks,sks,gc,hc,dc,rs,hs,ts,ss,cs,bad,bad5,
             LD,Cdef,Ltmp,a,c,x,s,t,LD,result,r} && dc{1} < qD).
  trivial.
  case : !mem(r, map_to_list(Gm_bis)).
  condt{2} at 8.
  derandomize; wp.
  while{2} : !in_dom(r{2}, Gm_bis{2}) && !mem(r{2}, Ltmp{2}) :
      length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  condt{1} at 4; [trivial | ].
  swap{2} [5-7] -4; swap{1} [5-6] 4; wp.
  let{2} Gaux : t_Gm_bis = Gm_bis[r <- (true, bs0_ku)].
  let{1} at 5 L1 : t_domGA = fst(split_list(map_to_list(Gm_bis), r)).
  let{1} at 6 L2 : t_domGA = snd(split_list(map_to_list(Gm_bis), r)).
  let{2} at 2 L1 : t_domGA = fst(split_list(map_to_list(Gaux), r)).
  let{2} at 3 L2 : t_domGA = snd(split_list(map_to_list(Gaux), r)).
  splitw last: length(Ltmp) > length(L2).
(** Ltmp = L2 and we focus on L2*)
  while : eq_except(Gm_bis{1}, Gm_bis{2}, r{1}) && ={Ltmp, r} && 
    Gm_bis[r]{1} = (true, g_0{2}) && !(mem(r{1}, Ltmp{2})) && 
    in_dom(r{1}, Gm_bis{1}).
  derandomize; trivial.
  splitw{1} last: length(Ltmp) > length(L2) + 1.
  condt{1} last.
(** Ltmp = r::L2 and we focus on r*)
  while{1} : ={r} && in_dom(r, Gm_bis){1} && !in_dom(r, Gm_bis){2} && 
    fst(Gm_bis[r]{1}) = true && mem(r, Ltmp){1} &&
    (exists(l : bitstring{p} list), Ltmp{1} = l++r{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
    [derandomize; trivial | trivial].
  condf{1} last; derandomize; wp.
(** Ltmp = L1 ++ r::L2 and we focus on L1*)
timeout 5.
  while : eq_except(Gm_bis{1}, Gm_bis{2}, r{1}) && ={L2, r} && 
    eq_except_list(Ltmp{1}, Ltmp{2}, L2{2}, r{2}) && 
    fst(Gm_bis[r]{1}) = true && !(mem(r{1}, L2{2}));
    [derandomize; trivial | trivial].
timeout 3.
  wp; !2rnd{2}; wp.
  while : ={Ltmp, Gm_bis, r} && in_dom(r{2}, Gm_bis{2});
    [derandomize; trivial | trivial].

(** Case !(length(map_to_list(Gm_bis)) < qD + qG) *)
  derandomize; wp.
  while : ={Ltmp, Gm_bis} &&  !length (map_to_list (Gm_bis{1})) < qD + qG;
    [derandomize; trivial | trivial].

(** Case !(dc < qD) *)
  derandomize; wp.
  while : ={Ltmp, Gm_bis};  [derandomize; trivial | trivial].
  save.

(** *************************************************** *)
(**                     Oracle G                        *)
(** *************************************************** *)

(** Case : !in_dom(x, Gm_bis) *)
  case{1} : !in_dom(x, Gm_bis).
  swap{2} 5 -4.
  condt{1} at 2; [derandomize; trivial | wp].
  let{2} Gaux : t_Gm_bis = Gm_bis[x <- (false, bs0_ku)].
  let{1} at 4 L1 : t_domGA = fst(split_list(map_to_list(Gm_bis), x)).
  let{1} at 5 L2 : t_domGA = snd(split_list(map_to_list(Gm_bis), x)).
  let{2} at 2 L1 : t_domGA = fst(split_list(map_to_list(Gaux), x)).
  let{2} at 3 L2 : t_domGA = snd(split_list(map_to_list(Gaux), x)).
  splitw{1} last : length(Ltmp) > length(L2) + 1.
  splitw{2} last : length(Ltmp) > length(L2).
  condt{1} at 8.
  while{1} : ={x} && in_dom(x, Gm_bis){1} && !in_dom(x, Gm_bis){2} && 
    fst(Gm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{p} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1.
  derandomize; trivial.
  derandomize; trivial.
  while : ={Ltmp, x} && eq_except(Gm_bis{1}, Gm_bis{2}, x{1}) && 
    !mem(x{1}, Ltmp{2}) && Gm_bis[x]{1} = (false, g){1} && 
    in_dom(x, Gm_bis){1} && !in_dom(x, Gm_bis){2}.
  derandomize; trivial.
  condf{1} at 9.
  wp.
  while{1} : ={x} && in_dom(x, Gm_bis){1} && !in_dom(x, Gm_bis){2} && 
    fst(Gm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{p} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1.
  derandomize; trivial.
  derandomize; trivial.
  wp.
  while : ={L1, L2, x} && !mem(x{1}, Ltmp{2}) && 
     Gm_bis[x]{1} = (false, g){1} &&
    eq_except(Gm_bis{1}, Gm_bis{2}, x{1}) &&
    eq_except_list(Ltmp{1}, Ltmp{2}, L2{1}, x{1}) &&
    in_dom(x, Gm_bis){1} && !in_dom(x, Gm_bis){2}.
  derandomize; trivial.
  swap{2} 4 -3.
  wp.
  apply : append_u_k1().
  trivial.

(** Case : in_dom(x, Gm_bis) *)
  condf{1} at 2; [derandomize; trivial | wp].
  case{1} : !fst(Gm_bis[x]); rnd{2}; wp.
  while : ={Gm_bis, Ltmp, x} && in_dom(x, Gm_bis){1} && 
    Gm_bis[x]{1} = (false, g_smpl){1}.
  derandomize; trivial.
  derandomize; trivial.
  let{1} at 4 L1 : t_domGA = fst(split_list(map_to_list(Gm_bis), x)).
  let{1} at 5 L2 : t_domGA = snd(split_list(map_to_list(Gm_bis), x)).
  let{2} at 2 L1 : t_domGA = fst(split_list(map_to_list(Gm_bis), x)).
  let{2} at 3 L2 : t_domGA = snd(split_list(map_to_list(Gm_bis), x)).
  splitw : length(Ltmp) > length(L2) + 1.  
  splitw last : length(Ltmp) > length(L2).
  while : ={Ltmp, x} && !mem(x, Ltmp){1} && 
    eq_except(Gm_bis{1}, Gm_bis{2}, x{1}) && in_dom(x, Gm_bis){1} && 
    in_dom(x, Gm_bis){2} && Gm_bis[x]{1} = (false, g){1} && 
    Gm_bis[x]{2} = (true, g{1}).
  derandomize; trivial.
  condt last.
  while{1} : ={x} && in_dom(x, Gm_bis){1} && in_dom(x, Gm_bis){2} && 
    fst(Gm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{p} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
    [derandomize; trivial | derandomize; trivial].
  while{2} : ={x} && in_dom(x, Gm_bis){1} && in_dom(x, Gm_bis){2} && 
    fst(Gm_bis[x]{2}) = true && mem(x, Ltmp){2} &&
    (exists(l : bitstring{p} list), Ltmp{2} = l++x{2}::L2{2}) :
    length(Ltmp{2}), length(L2{2}) + 1;
    [derandomize; trivial | trivial].
  condf last.
  condt{2} at 6; wp.
  while{2} : ={x} && in_dom(x, Gm_bis){1} && in_dom(x, Gm_bis){2} && 
    fst(Gm_bis[x]{2}) = true && mem(x, Ltmp){2} &&
    (exists(l : bitstring{p} list), Ltmp{2} = l++x{2}::L2{2}) :
    length(Ltmp{2}), length(L2{2}) + 1.
  derandomize; trivial.
  trivial.
  derandomize.
  !2rnd>>; !2rnd{1}>>; wp.
  while : ={Ltmp, L2, x} && 
   (exists(l : bitstring{p} list), Ltmp{1} = l++x{1}::L2{1}) &&
    eq_except(Gm_bis{1}, Gm_bis{2}, x{1}) && 
    in_dom(x, Gm_bis){1} && 
    in_dom(x, Gm_bis){2} && Gm_bis[x]{1} = (false, g){1} && 
    fst(Gm_bis[x]{2}) = true;
    [trivial | trivial].
  save.
(** *************************************************** *)
(**                 Function Main                       *)
(** *************************************************** *)
  trivial.
  trivial.
  save.

claim Pr_G2cd_bad : G2c.Main[bad] = G2d.Main[bad] using G2c_G2d.
claim Pr_G2cd_bad5 : 
  G2c.Main[bad5 || phi(sks, Gm_bis, Hm, LD)] = 
  G2d.Main[bad5 || phi(sks, Gm_bis, Hm, LD)] using G2c_G2d.
claim Pr_G2d_bad5 : 
  G2d.Main[bad5 || phi(sks, Gm_bis, Hm, LD)] <= 
  qD%r * (1%r / (2^k1)%r) admit.
claim Pr_INDCCA_G2d : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2d.Main[bad] + qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2cd_bad, Pr_G2cd_bad5, Pr_G2d_bad5,
      eq_head, eq_except_list_rec, avoid_dbl, eq_L2, eq_length_plus_one,
      length_tl_spec, mem_tl, mem_hd, list_not_empty_spec, pos_on_L1, 
      pos_on_x, eq_update_map_to_list, eq_map_to_list_upd, eq_upd_M2.


(** ******************************************* *)
(**          Definition of the Game G2e         *)
(**                                             *)
(**     # Oracle G is under the form of a ROM   *)
(**     # We remove the while in the main code  *)
(** ******************************************* *)
game G2e = G2d
  remove a, c, Ltmp
  var Gm : t_Gm 
  where G = {
    var g, g_smpl : bitstring{ku};
    var d : bool;
    g = {0,1}^ku;
    if (!in_dom(x,(Gm_bis)))
    { 
      bad = bad || x = rs;
      Gm_bis[x] = (false, g);
    } else {
      (d, g_smpl) = Gm_bis[x];
      if(d = true){
        Gm_bis[x] = (false, g);
        bad5 = bad5 || P(g, x, sks, LD, Hm);
      }
    }
    return snd(Gm_bis[x]);   
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm = empty_map; Gm_bis = empty_map; Gm = empty_map;
    LD = []; 
    Cdef = false;
    bad = false; bad5 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

set list_not_empty_spec.

equiv G2d_G2e_G : G2d.G ~ G2e.G : 
  (={Gm_bis, Hm, gc, bad, bad5, sks, rs, LD}).
app 1 1(={Gm_bis, Hm, gc, bad, bad5, sks, rs, LD, x, g}).
apply : append_u_k1(); trivial.
case : !in_dom(x, Gm_bis).
trivial.
trivial.
save.

equiv G2d_G2e : G2d.Main ~ G2e.Main : true ==> 
  ={Hm, gc, hc, dc, sks, bad, bad5, hs, rs, ss, ts, cs, Cdef}.
  app 25 23 (={Gm_bis, Hm, gc, hc, dc, sks, bad, bad5, hs, rs, ss, ts, 
             cs, Cdef, LD}).
  call (={Gm_bis, Hm, gc, hc, dc, sks, bad, bad5, hs, rs, ss, ts, cs, 
          Cdef, LD}).
  inline H; derandomize; wp.
  call (={Gm_bis, Hm, gc, hc, dc, sks, bad, bad5, hs, rs, ss, ts, cs, 
          Cdef, LD}).
  inline KG; trivial.
  wp.
  while{1} : ={Hm, gc, hc, dc, sks, bad, bad5, hs, rs, ss, ts, cs, Cdef} : 
    length(Ltmp{1}), 0.
  derandomize; trivial.
  trivial.
  save.

claim Pr_G2de_bad : G2d.Main[bad] = G2e.Main[bad] using G2d_G2e.
claim Pr_INDCCA_G2e: |INDCCA.Main[res] - 1%r/2%r| <= 
  G2e.Main[bad] + qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2de_bad, struct_list_not_empty.

(** ******************************************* *)
(**          Definition of the Game G3          *)
(**                                             *)
(**     # Remove variable bad5, Gm_bis          *)
(**     # Remove cond on the length of Gm_bis   *)
(**       in D_A1.                              *)
(**     # g_0 in D_A1 is resample as {0,1}^ku   *)
(**     # Return bottom in D_A1 when :          *)
(**         * !in_dom(r, Gm)                    *)
(**         * !in_dom(s, Hm)                    *)
(** ******************************************* *)
game G3 = G2e
  remove bad5, Gm_bis
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        if(mem(r, map_to_list(Gm))){
          g_0 = Gm[r];
          if(low_bits_ku(s ^^ g_0) = bs0_k1) {
            result = high_bits_ku(s ^^ g_0);
          }
        } else {
          if (r = rs) {
            bad = true;
          }
        }
      } else {
(**   Case :  !in_dom(s, Hm) *)
        r = {0,1}^p;
        Hm[s] = r;
      }
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and G = {
    var g : bitstring{ku};
    g = {0,1}^(ku);
    if (!in_dom(x, Gm)) { 
      Gm[x] = g;
      bad = bad || x = rs;
    } else {
      g = Gm[x];
    }
    return g;
  }
 and G_A = {
    var _ku : bitstring{ku};
    if(gc < qG) {
      _ku = G (x);
      gc = gc + 1;
    } else {
      _ku = bs0_ku;
    }
    return _ku;
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm = empty_map; Gm = empty_map;
    LD = []; 
    Cdef = false;
    bad = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

pred eq_map_snd_false (M : ('a, 'b) map, Mb : ('a, (bool * 'b)) map) =
  forall(x : 'a), 
    (in_dom(x, M) => (in_dom(x, Mb) && Mb[x] = (false, M[x]))) &&
    (in_dom(x, Mb) => (fst(Mb[x]) <=> !in_dom(x, M))).

op nb_true : ('a, (bool * 'b)) map -> int.

axiom nb_true_upd_true :
  forall(Mb : ('a, (bool * 'b)) map, x : 'a, y : 'b),
    !in_dom(x, Mb) => nb_true(Mb[x <- (true, y)]) = nb_true(Mb) + 1.

axiom nb_true_upd_false :
  forall(Mb : ('a, (bool * 'b)) map, x : 'a, y : 'b),
    !in_dom(x, Mb) => nb_true(Mb[x <- (false, y)]) = nb_true(Mb).

axiom nb_true_erase_false :
  forall(Mb : ('a, (bool * 'b)) map, x : 'a, y : 'b),
    in_dom(x, Mb) => fst(Mb[x]) => 
    nb_true(Mb[x <- (false, y)]) = nb_true(Mb) - 1.

lemma diff_map_fst_true : 
  forall(M : ('a, 'b) map, Mb : ('a, bool * 'b) map, x : 'a),
    !in_dom(x, M) => in_dom(x, Mb) => eq_map_snd_false(M, Mb) => fst(Mb[x]).

axiom nbtrue_em_nil : 
  forall(M : ('a, bool * 'b) map),
  M = empty_map => nb_true(M) = 0.

axiom mtl_em_nil :
  forall(M : ('a, 'b) map),
  M = empty_map => map_to_list(M) = [].

set eq_update_map_to_list.

equiv G2e_G3_GA : G2e.G_A ~ G3.G_A : 
  (={Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef} &&
  length(map_to_list(Gm_bis{1})) <= length(map_to_list(Gm{2})) + 
  nb_true(Gm_bis{1}) && length(map_to_list(Gm{2})) <= gc{2} &&
  nb_true(Gm_bis{1}) <= dc{2} && eq_map_snd_false(Gm{2}, Gm_bis{1}) &&
  gc{2} <= qG && (bad{1} => bad{2})).
  inline G.
  if; [case{1} : in_dom(x, Gm_bis); [trivial | trivial] | trivial].
save. 

equiv G2e_G3_DA1 : G2e.D_A1 ~ G3.D_A1 : 
  (={Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef} &&
  length(map_to_list(Gm_bis{1})) <= length(map_to_list(Gm{2})) + 
  nb_true(Gm_bis{1}) && length(map_to_list(Gm{2})) <= gc{2} &&
  nb_true(Gm_bis{1}) <= dc{2} && eq_map_snd_false(Gm{2}, Gm_bis{1}) &&
  gc{2} <= qG && (bad{1} => bad{2})) by auto.

equiv G2e_G3 : G2e.Main ~ G3.Main : true ==> bad{1} => bad{2}
by auto  (={Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef} &&
  length(map_to_list(Gm_bis{1})) <= length(map_to_list(Gm{2})) + 
  nb_true(Gm_bis{1}) && length(map_to_list(Gm{2})) <= gc{2} &&
  nb_true(Gm_bis{1}) <= dc{2} && eq_map_snd_false(Gm{2}, Gm_bis{1}) &&
  gc{2} <= qG && (bad{1} => bad{2})).

claim Pr_G2e3_bad : G2e.Main[bad] <= G3.Main[bad] using G2e_G3.
claim Pr_INDCCA_G3: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3.Main[bad] + qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G2e3_bad,
      nb_true_upd_true, nb_true_upd_false, nb_true_erase_false, 
      diff_map_fst_true, nbtrue_em_nil, mtl_em_nil.

(** ******************************************* *)
(**         Definition of the Game G3a          *)
(**                                             *)
(**    * Inline calls to H in Oracle D          *)
(** ******************************************* *)
type t_Hm_bis = (bitstring{ku}, bool * bitstring{p}) map.

print G3.D_A1.
game G3a = G3
  remove Hm
  var Hm_bis : t_Hm_bis
  var bad1 : bool
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r, h_0 : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm_bis)){
        (d, h_0) =  Hm_bis[s];
        if(d = true){
          r = t ^^ h_0;
          if(mem(r, map_to_list(Gm))){
            bad1 = true;
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            if(r = rs){
              bad1 = true; 
              bad = true;
            }
          }
        } else {
          r = t ^^ h_0;
          if(mem(r, map_to_list(Gm))){
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            if(r = rs){
              bad = true;
            }
          }
        }
      } else {
(**   Case :  !in_dom(s, Hm) *)
        r = {0,1}^p;
        Hm_bis[s] = (true, r);
      }
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and H = {
    var h : bitstring{p};
    var d : bool;
    h = {0,1}^p;
    if (!in_dom(x,(Hm_bis))){ 
      Hm_bis[x] = (false, h);
    } else {
      (d, h) = Hm_bis[x];
    }
    Hm_bis[x] = (false, h);
    return h;   
  }
 and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm_bis = empty_map; Gm = empty_map;
    LD = []; 
    Cdef = false;
    bad = false;
    bad1 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

equiv G3_G3a_DA1 : G3.D_A1 ~ G3a.D_A1 : 
  (={Gm, gc, hc, dc, bad, sks, rs} && eq_map_snd(Hm{1}, Hm_bis{2})).
if.
app 5 5 (={Gm, gc, hc, dc, bad, sks, rs, s, t, result} && 
         eq_map_snd(Hm{1}, Hm_bis{2})).
trivial.
if.
case{2} : !fst(Hm_bis[s]).
condf{2}.
trivial.
trivial.
condt{2}.
trivial.
trivial.
trivial.
trivial.
save.

equiv G3_G3a : G3.Main ~ G3a.Main : true ==> ={bad} 
  by auto (={Gm, gc, hc, dc, bad, sks, rs, cs, ss} && 
          eq_map_snd(Hm{1}, Hm_bis{2})).

claim Pr_G3_G3a : G3.Main[bad] = G3a.Main[bad] using G3_G3a.

claim Pr_INDCCA_G3a: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3a.Main[bad] + qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3_G3a.

(** ******************************************* *)
(**         Definition of the Game G3b          *)
(** ******************************************* *)

game G3b = G3a
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r, h_0 : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm_bis)){
        (d, h_0) =  Hm_bis[s];
        if(d = true){
          r = t ^^ h_0;
          if(mem(r, map_to_list(Gm))){
            bad1 = true;
          } else {
            if(r = rs){
              bad1 = true; 
            }
          }
        } else {
          r = t ^^ h_0;
          if(mem(r, map_to_list(Gm))){
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            if(r = rs){
              bad = true;
            }
          }
        }
      } else {
(**   Case :  !in_dom(s, Hm) *)
        r = {0,1}^p;
        Hm_bis[s] = (true, r);
      }
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and H = {
    var h : bitstring{p};
    var d : bool;
    h = {0,1}^p;
    if (!in_dom(x,(Hm_bis))){ 
      Hm_bis[x] = (false, h);
    } else {
      (d, h) = Hm_bis[x];
    }
    Hm_bis[x] = (false, h);
    return h;   
  }
 and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm_bis = empty_map; Gm = empty_map;
    LD = [];
    Cdef = false;
    bad = false;
    bad1 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

equiv G3a_G3b : G3a.Main ~ G3b.Main : true ==> ={bad1} && 
  (!bad1{1} => ={Gm, Hm_bis, gc, hc, dc, bad, sks, rs, cs, ss, res})
by auto upto (bad1) with (={Gm, Hm_bis, gc, hc, dc, bad, sks, rs, cs, ss}).

claim Pr_G3ab_bad : G3a.Main[bad] <= G3b.Main[bad] + G3b.Main[bad1]   
  using G3a_G3b.

claim Pr_INDCCA_G3b: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3b.Main[bad] + G3b.Main[bad1] +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3ab_bad.

op Q : 
  (bitstring{p}, bitstring{ku}, skey, (bool * cipher) list, t_Gm) -> bool.

axiom Q_spec :
  forall(h : bitstring{p}, s : bitstring{ku}, sk : skey, 
         L : (bool * cipher) list, G : t_Gm),
    Q(h, s, sk, L, G) <=> 
      exists(d: bool, c : cipher), mem((d, c), L) => 
        let s = high_bits_k(finv(sk, c)) in 
        let t = low_bits_k(finv(sk, c)) in
        let r = t ^^ bs0_p in
        (s = high_bits_k(finv(sk, c))) &&
        (in_dom(r, G) || (r = t ^^ bs0_p)).

op mu : (skey, t_Hm_bis, t_Gm, (bool * cipher) list) -> bool.

axiom mu_spec :
  forall(sk : skey, H : t_Hm_bis, G : t_Gm, D : (bool * cipher) list),
    mu(sk, H, G, D) <=>
    exists(d : bool, c : cipher), mem((d, c), D) &&
      let s = high_bits_k(finv(sk, c)) in 
      let t = low_bits_k(finv(sk, c)) in
      let r = t ^^ snd(H[s]) in
        in_dom(s, H) && fst(H[s]) &&
        (in_dom(r, G) || (r = t ^^ snd(H[s]))).

(** ******************************************* *)
(**          Definition of the Game G3c         *)
(**                                             *)
(**     # Introduction of the variable bad2     *)
(**     # Put while instruction before the call *)
(**       to the adversary A1 to prepare the    *)
(**       next Eager Sampling.                  *)
(** ******************************************* *)
game G3c = G3b 
  remove bad1
  var bad2 : bool
  var Ltmp : bitstring{ku} list
  var a : bitstring{ku}
  var c : bitstring{p}
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r, h_0 : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm_bis)){
        (d, h_0) =  Hm_bis[s];
        if(d = true){
          r = t ^^ h_0;
        } else {
          r = t ^^ h_0;
          if(mem(r, map_to_list(Gm))){
            g_0 = Gm[r];
            if(low_bits_ku(s ^^ g_0) = bs0_k1) {
              result = high_bits_ku(s ^^ g_0);
            }
          } else {
            if(r = rs){
              bad = true;
            }
          }
        }
      } else {
(**   Case :  !in_dom(s, Hm) *)
        r = {0,1}^p;
        Hm_bis[s] = (true, r);
      }
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and H = {
    var h : bitstring{p};
    var d : bool;
    h = {0,1}^p;
    if (!in_dom(x,(Hm_bis))){ 
      Hm_bis[x] = (false, h);
    } else {
      (d, h) = Hm_bis[x];
      if(d = true){
        Hm_bis[x] = (false, h);
        bad2 = bad2 || Q(h, x, sks, LD, Gm);
      }
    }
    return snd(Hm_bis[x]);   
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0; a = bs0_ku; c = bs0_p;
    Hm_bis = empty_map; Gm = empty_map;
    LD = []; Ltmp = [];
    Cdef = false;
    bad = false;
    bad2 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    Ltmp = map_to_list(Hm_bis);
    while (Ltmp <> []){
      a = hd(Ltmp);
      if(fst(Hm_bis[a]) = true){
        c = {0,1}^p;
        Hm_bis[a] = (true, c);
      }
      Ltmp = tl(Ltmp);
    }
    a = bs0_ku;
    c = bs0_p;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

equiv G3b_G3c_D_A1 : G3b.D_A1 ~ G3c.D_A1 :
  (={Gm, Hm_bis, gc, hc, dc, bad, sks, rs, cs} &&
  (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).
if.
sp.
rnd>>.
sp.
if.
trivial.
trivial.
trivial.
save.

equiv G3b_G3c_D_A2 : G3b.D_A2 ~ G3c.D_A2 : 
  (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} &&
  (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2}))))
by auto (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} &&
     (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).

equiv G3b_G3c_H : G3b.H ~ G3c.H : 
  (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} &&
  (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).
rnd>>.
if.
trivial.
case{2} : fst(Hm_bis[x]) = true.
condt{2} at 2.
trivial.
trivial.
trivial.
save.

equiv G3b_G3c : G3b.Main ~ G3c.Main : true ==> 
  (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} &&
  (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).
call (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} && 
     (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).
inline H.
wp; !2rnd; wp.
call (={Gm, Hm_bis, sks, bad, gc, hc, dc, rs, cs} && 
     (bad1{1} => (bad2{2} || mu(sks{2}, Hm_bis{2}, Gm{2}, LD{2})))).
condf{2} last.
trivial.
trivial.
(** Delete this axiom when rewrite Oracle H to avoid double affectation 
  * in LH with the same value
  *)
axiom x :
  forall(M : ('a, bool * 'b) map, a : 'a, b : 'b, x : bool),
    M[a <- (x, b)][a <- (x, b)] = M[a <- (x, b)].
trivial.
save.

claim Pr_G3bc_bad : G3b.Main[bad] = G3c.Main[bad] using G3b_G3c.
claim Pr_G3bc_bad1 : 
  G3b.Main[bad1] <= G3c.Main[bad2 || mu(sks, Hm_bis, Gm, LD)] 
  using G3b_G3c.
claim Pr_G3b_G3c : 
  G3b.Main[bad] + G3b.Main[bad1] <= 
  G3c.Main[bad] + G3c.Main[bad2 || mu(sks, Hm_bis, Gm, LD)].
claim Pr_INDCCA_G3c: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3c.Main[bad] + G3c.Main[bad2 || mu(sks, Hm_bis, Gm, LD)] + 
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3bc_bad, Pr_G3bc_bad1, Pr_G3b_G3c.

(** ******************************************* *)
(**          Definition of the Game G3d         *)
(**                                             *)
(**     # Introduction of the variable bad2     *)
(**     # Put while instruction before the call *)
(**       to the adversary A1 to prepare the    *)
(**       next Eager Sampling.                  *)
(** ******************************************* *)
game G3d = G3c 
  where H = {
    var h, h_smpl : bitstring{p};
    var d : bool;
    h = {0,1}^p;
    if (!in_dom(x,(Hm_bis))){ 
      Hm_bis[x] = (false, h);
    } else {
      (d, h_smpl) = Hm_bis[x];
      if(d = true){
        Hm_bis[x] = (false, h);
        bad2 = bad2 || Q(h, x, sks, LD, Gm);
      }
    }
    return snd(Hm_bis[x]);   
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0; a = bs0_ku; c = bs0_p;
    Hm_bis = empty_map; Gm = empty_map;
    LD = []; Ltmp = [];
    Cdef = false;
    bad = false;
    bad2 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    Ltmp = map_to_list(Hm_bis);
    while (Ltmp <> []){
      a = hd(Ltmp);
      if(fst(Hm_bis[a]) = true){
        c = {0,1}^p;
        Hm_bis[a] = (true, c);
      }
      Ltmp = tl(Ltmp);
    }
    a = bs0_ku;
    c = bs0_p;
    return true;
  }. 

equiv G3c_G3d : G3d.Main ~ G3c.Main : true ==> 
   ={Gm, Hm_bis, gc, hc, dc, bad, bad2, sks, rs, cs, ss, LD}
   by eager {
     Ltmp = map_to_list(Hm_bis); 
     while(Ltmp <>[]) {
       a = hd(Ltmp);
       if(fst(Hm_bis[a]) = true){
         c = {0,1}^p ;
         Hm_bis[a] = (true, c);
       }
       Ltmp = tl(Ltmp);
     }
     a = bs0_ku;
     c = bs0_p;
   }.
(** *************************************************** *)
(**                   Oracle D_A1                       *)
(** *************************************************** *)
(** Case : dc < qD *)
  if{1}.
  condt{2} at 5; [wp | ].
  while{2} : true : length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  swap{2} [5 - 9] -4; swap 3 2.
  app 4 4 (={Gm, Hm_bis, pks, sks, gc, hc, dc, rs, hs, ts, ss, cs, bad, 
           bad2, LD, Cdef, Ltmp, a, c, x, s, t, result} && 
           dc{1} < qD); [trivial | ].
(** Case : in_dom(s, Hm_bis) *)
  case{1} : in_dom(s, Hm_bis).
  condt{1} at 2; [trivial | ].
  condt{2} at 6; [wp | ].
  while{2} : (map_to_list(Hm_bis{1}) = map_to_list(Hm_bis{2})) && 
    forall(x : bitstring{ku}), mem(x, Ltmp{2}) => in_dom(x, Hm_bis{2}) :
    length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  wp.
  let{1} Hm_bis' : t_Hm_bis = Hm_bis.
  while : fst(Hm_bis[s]{1}) = fst(Hm_bis'[s]{1}) && 
    (fst(Hm_bis[s]{1}) = false => snd(Hm_bis[s]{1}) = snd(Hm_bis'[s]{1})) &&
    ={Ltmp, Hm_bis};
    [derandomize; trivial | trivial].
(** Case : !mem(s, map_to_list(Hm_bis)) *)
  condf{2} at 6; [wp | ].
  while{2} : (map_to_list(Hm_bis{1}) = map_to_list(Hm_bis{2})) && 
    forall(x : bitstring{ku}), mem(x, Ltmp{2}) => in_dom(x, Hm_bis{2}) :
    length(Ltmp{2}), 0;
    [derandomize; trivial | trivial].
  condf{1} at 2; [trivial | ].
  swap{2} 6 -4.
  swap{1} [4 - 5] 4; wp.
(** ******************************************* *)
(**   Split the while in 3 part : L1 ++ s::L2   *)
(** ******************************************* *)
  let{2} Haux : t_Hm_bis = Hm_bis[s <- (true, bs0_p)].
  let{1} at 4 L1 : t_domHA = fst(split_list(map_to_list(Hm_bis), s)).
  let{1} at 5 L2 : t_domHA = snd(split_list(map_to_list(Hm_bis), s)).
  let{2} at 2 L1 : t_domHA = fst(split_list(map_to_list(Haux), s)).
  let{2} at 3 L2 : t_domHA = snd(split_list(map_to_list(Haux), s)).
  splitw last : length(Ltmp) > length(L2).
(** Ltmp = L2 and we focus on L2*)
  while : eq_except(Hm_bis{1}, Hm_bis{2}, s{1}) && ={Ltmp, s} && 
    Hm_bis[s]{1} = (true, r{2}) && !(mem(s{1}, Ltmp{2})) && 
    in_dom(s{1}, Hm_bis{1}).
  derandomize; trivial.
  splitw{1} last : length(Ltmp) > length(L2) + 1.
  condt{1} last.
(** Ltmp = r::L2 and we focus on s*)
(** METTRE le set avant le eager *)
set eq_head, eq_except_list_rec, avoid_dbl, eq_L2, eq_length_plus_one,
    length_tl_spec, mem_tl, mem_hd, list_not_empty_spec, pos_on_L1, 
    pos_on_x, eq_update_map_to_list, eq_map_to_list_upd, eq_upd_M2.
  while{1} : ={s} && in_dom(s, Hm_bis){1} && !in_dom(s, Hm_bis){2} && 
    fst(Hm_bis[s]{1}) = true && mem(s, Ltmp){1} &&
    (exists(l : bitstring{ku} list), Ltmp{1} = l++s{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
    [derandomize; trivial | trivial].
  condf{1} last.
  derandomize; wp.
(** Ltmp = L1 ++ s::L2 and we focus on L1*)
timeout 5.
  while : eq_except(Hm_bis{1}, Hm_bis{2}, s{1}) && ={L2, s} && 
    eq_except_list(Ltmp{1}, Ltmp{2}, L2{2}, s{2}) && 
    fst(Hm_bis[s]{1}) = true && !(mem(s{1}, L2{2}));
    [trivial | trivial].
timeout 3.
(** Case !(dc < qD) *)
  derandomize; wp.
  while : ={Ltmp, Hm_bis};  [derandomize; trivial | trivial].
  save.

(** *************************************************** *)
(**                     Oracle H                        *)
(** *************************************************** *)
(** Case : !in_dom(x, Hm_bis) *)
  case{1} : !in_dom(x, Hm_bis).
  swap{2} 5 -4.
  condt{1} at 2; [derandomize; trivial | wp].
  let{2} Haux : t_Hm_bis = Hm_bis[x <- (false, bs0_p)].
  let{1} at 3 L1 : t_domHA = fst(split_list(map_to_list(Hm_bis), x)).
  let{1} at 4 L2 : t_domHA = snd(split_list(map_to_list(Hm_bis), x)).
  let{2} at 2 L1 : t_domHA = fst(split_list(map_to_list(Haux), x)).
  let{2} at 3 L2 : t_domHA = snd(split_list(map_to_list(Haux), x)).
  splitw{1} last : length(Ltmp) > length(L2) + 1.
  splitw{2} last : length(Ltmp) > length(L2).
  condt{1} at 7.
  while{1} : ={x} && in_dom(x, Hm_bis){1} && !in_dom(x, Hm_bis){2} && 
    fst(Hm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{ku} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
  [derandomize; trivial | trivial].
  while : ={Ltmp, x} && eq_except(Hm_bis{1}, Hm_bis{2}, x{1}) && 
    !mem(x{1}, Ltmp{2}) && Hm_bis[x]{1} = (false, h){1} && 
    in_dom(x, Hm_bis){1} && !in_dom(x, Hm_bis){2}.
  derandomize; trivial.
  condf{1} at 8; wp.
  while{1} : ={x} && in_dom(x, Hm_bis){1} && !in_dom(x, Hm_bis){2} && 
    fst(Hm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{ku} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
  [derandomize; trivial | trivial].
  while : ={L1, L2, x} && !mem(x{1}, Ltmp{2}) && 
     Hm_bis[x]{1} = (false, h){1} &&
    eq_except(Hm_bis{1}, Hm_bis{2}, x{1}) &&
    eq_except_list(Ltmp{1}, Ltmp{2}, L2{1}, x{1}) &&
    in_dom(x, Hm_bis){1} && !in_dom(x, Hm_bis){2};
  [derandomize; trivial | trivial].
(** Case : in_dom(x, Hm_bis) *)
  condf{1} at 2; [derandomize; trivial | wp].
  case{1} : !fst(Hm_bis[x]); rnd{2}; wp.
  while : ={Hm_bis, Ltmp, x} && in_dom(x, Hm_bis){1} && 
    Hm_bis[x]{1} = (false, h_smpl){1};
  [derandomize; trivial | trivial].
  let{1} at 4 L1 : t_domHA = fst(split_list(map_to_list(Hm_bis), x)).
  let{1} at 5 L2 : t_domHA = snd(split_list(map_to_list(Hm_bis), x)).
  let{2} at 2 L1 : t_domHA = fst(split_list(map_to_list(Hm_bis), x)).
  let{2} at 3 L2 : t_domHA = snd(split_list(map_to_list(Hm_bis), x)).
  splitw : length(Ltmp) > length(L2) + 1.  
  splitw last : length(Ltmp) > length(L2).
  while : ={Ltmp, x} && !mem(x, Ltmp){1} && 
    eq_except(Hm_bis{1}, Hm_bis{2}, x{1}) && in_dom(x, Hm_bis){1} && 
    in_dom(x, Hm_bis){2} && Hm_bis[x]{1} = (false, h){1} && 
    Hm_bis[x]{2} = (true, h{1}).
  derandomize; trivial.
  condt last.
  while{1} : ={x} && in_dom(x, Hm_bis){1} && in_dom(x, Hm_bis){2} && 
    fst(Hm_bis[x]{1}) = false && mem(x, Ltmp){1} &&
    (exists(l : bitstring{ku} list), Ltmp{1} = l++x{1}::L2{1}) :
    length(Ltmp{1}), length(L2{1}) + 1;
    [derandomize; trivial | derandomize; trivial].
  while{2} : ={x} && in_dom(x, Hm_bis){1} && in_dom(x, Hm_bis){2} && 
    fst(Hm_bis[x]{2}) = true && mem(x, Ltmp){2} &&
    (exists(l : bitstring{ku} list), Ltmp{2} = l++x{2}::L2{2}) :
    length(Ltmp{2}), length(L2{2}) + 1;
    [derandomize; trivial | trivial].
  condf last.
  condt{2} at 6; wp.
  while{2} : ={x} && in_dom(x, Hm_bis){1} && in_dom(x, Hm_bis){2} && 
    fst(Hm_bis[x]{2}) = true && mem(x, Ltmp){2} &&
    (exists(l : bitstring{ku} list), Ltmp{2} = l++x{2}::L2{2}) :
    length(Ltmp{2}), length(L2{2}) + 1;
  [derandomize; trivial | trivial].
  derandomize.
  swap{1} 1; wp.
  while : ={Ltmp, L2, x} && 
   (exists(l : bitstring{ku} list), Ltmp{1} = l++x{1}::L2{1}) &&
    eq_except(Hm_bis{1}, Hm_bis{2}, x{1}) && 
    in_dom(x, Hm_bis){1} && 
    in_dom(x, Hm_bis){2} && Hm_bis[x]{1} = (false, h){1} && 
    fst(Hm_bis[x]{2}) = true;
    [trivial | trivial].
  save.
(** *************************************************** *)
(**                 Function Main                       *)
(** *************************************************** *)
  trivial.
  trivial.
  save.

claim Pr_G3cd_bad : G3c.Main[bad] = G3d.Main[bad] using G3c_G3d.
claim Pr_G3cd_bad2 : 
  G3c.Main[bad2 || mu(sks, Hm_bis, Gm, LD)] = 
  G3d.Main[bad2 || mu(sks, Hm_bis, Gm, LD)] using G3c_G3d.

(** CHECK if this proba is right *)
claim Pr_G3d_bad2 : 
  G3d.Main[bad2 || mu(sks, Hm_bis, Gm, LD)] <= 
  qD%r * ((qG + 1)%r / (2^p)%r) admit.
claim Pr_INDCCA_G3d: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3d.Main[bad] + 
  qD%r * ((qG + 1)%r / (2^p)%r) +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3cd_bad, Pr_G3cd_bad2, Pr_G3d_bad2,
      eq_head, eq_except_list_rec, avoid_dbl, eq_L2, eq_length_plus_one,
      length_tl_spec, mem_tl, mem_hd, list_not_empty_spec, pos_on_L1, 
      pos_on_x, eq_update_map_to_list, eq_map_to_list_upd, eq_upd_M2.

(** ******************************************* *)
(**          Definition of the Game G3e         *)
(** ******************************************* *)
game G3e = G3d 
  remove a, c, Ltmp
  var Hm : t_Hm
  where Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm_bis = empty_map; Gm = empty_map; Hm = empty_map;
    LD = [];
    Cdef = false;
    bad = false;
    bad2 = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

set list_not_empty_spec.

equiv G3d_G3e : G3d.Main ~ G3e.Main : true ==> 
  ={Gm, gc, hc, dc, sks, bad, bad2, hs, rs, ss, ts, cs, Cdef}.
  app 25 23 (={Gm, Hm_bis, gc, hc, dc, sks, bad, bad2, hs, rs, ss, ts, 
             cs, Cdef, LD}).
  call (={Gm, Hm_bis, gc, hc, dc, sks, bad, bad2, hs, rs, ss, ts, cs, 
          Cdef, LD}).
  inline H; derandomize; wp.
  call (={Gm, Hm_bis, gc, hc, dc, sks, bad, bad2, hs, rs, ss, ts, cs, 
          Cdef, LD}).
  trivial.
  wp.
  while{1} : ={Gm, gc, hc, dc, sks, bad, bad2, hs, rs, ss, ts, cs, Cdef} : 
    length(Ltmp{1}), 0.
  derandomize; trivial.
  trivial.
  save.

claim Pr_G3de_bad : G3d.Main[bad] = G3e.Main[bad] using G3d_G3e.
claim Pr_INDCCA_G3e: |INDCCA.Main[res] - 1%r/2%r| <= 
  G3e.Main[bad] + 
  qD%r * ((qG + 1)%r / (2^p)%r) +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3de_bad, list_not_empty_spec.

(** ******************************************* *)
(**          Definition of the Game G4          *)
(** ******************************************* *)
game G4 = G3e
  remove bad2, Hm_bis
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r, h : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm)){
        h = Hm[s];
        r = t ^^ h;
(**     Inline G *)
        if(mem(r, map_to_list(Gm))){
          g_0 = Gm[r];
          if(low_bits_ku(s ^^ g_0) = bs0_k1) {
            result = high_bits_ku(s ^^ g_0);
          }
        } else {
          if (r = rs) {
            bad = true;
          }
        }
      } 
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and H = {
    var h : bitstring{p};
    h = {0,1}^p;
    if (!in_dom(x, Hm)) { 
      Hm[x] = h;
    } else {
      h = Hm[x];
    }
    return h;
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm = empty_map; Gm = empty_map;
    LD = [];
    Cdef = false;
    bad = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

set eq_update_map_to_list, list_not_empty_spec, 
    nb_true_upd_true, nb_true_upd_false, nb_true_erase_false, 
    diff_map_fst_true, nbtrue_em_nil, mtl_em_nil,
    eq_head, eq_except_list_rec, avoid_dbl, eq_L2, eq_length_plus_one,
    length_tl_spec, mem_tl, mem_hd, list_not_empty_spec, pos_on_L1, 
    pos_on_x, eq_update_map_to_list, eq_map_to_list_upd, eq_upd_M2.

checkproof.

equiv G3e_G4_H : G3e.H ~ G4.H : 
  (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad} &&
  eq_map_snd_false(Hm{2}, Hm_bis{1})).
trivial.
save.

equiv G3e_G4_HA : G3e.H_A ~ G4.H_A : 
  (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad,LD} &&
  eq_map_snd_false(Hm{2}, Hm_bis{1})).
if;[ | trivial].
auto using G3e_G4_H.
save.

equiv G3e_G4_DA1 : G3e.D_A1 ~ G4.D_A1 : 
  (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad,LD} &&
    eq_map_snd_false(Hm{2}, Hm_bis{1})).
if.
app 5 5 (={x,s,t,g_0,LD,result,Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad} &&
    eq_map_snd_false(Hm{2}, Hm_bis{1})).
trivial.
if{1}.
sp 1 0.
if{1}.
condf{2};trivial.
condt{2}.
trivial.
condf{2}.
trivial.
print eq_map_snd_false.

lemma eq_map_snd_false_upd_t_aux :
  forall(Hm:t_Hm, Hm_bis:t_Hm_bis, s:bitstring{ku},r:bitstring{p}),
  !in_dom (s,Hm_bis) =>
  eq_map_snd_false(Hm,Hm_bis) => 
  let M = Hm in
  let Mb = Hm_bis[s <- (true,r)] in
  (forall (x :bitstring{ku}),
         (in_dom (x,M) => in_dom (x,Mb) && Mb[x] = (false,M[x])) &&
          (in_dom (x,Mb) => fst (Mb[x]) <=> !in_dom (x,M))).

lemma eq_map_snd_false_upd_t :
  forall(Hm:t_Hm, Hm_bis:t_Hm_bis, s:bitstring{ku},r:bitstring{p}),
  !in_dom (s,Hm_bis) =>
  eq_map_snd_false(Hm,Hm_bis) => 
  eq_map_snd_false(Hm,Hm_bis[s <- (true,r)]).
unset eq_map_snd_false_upd_t_aux.
trivial.
trivial.
save.

equiv G3e_G4_DA2 : G3e.D_A2 ~ G4.D_A2 : 
  (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad,LD} &&
    eq_map_snd_false(Hm{2}, Hm_bis{1})).
if.
call using  G3e_G4_DA1.
trivial.
trivial.
save.

equiv G3e_G4 : G3e.Main ~ G4.Main : true ==> bad{1} = bad{2}.
call (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad,LD} &&
    eq_map_snd_false(Hm{2}, Hm_bis{1})).
wp.
call using G3e_G4_H.
call (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef,bad,LD} &&
    eq_map_snd_false(Hm{2}, Hm_bis{1})).
trivial.
save.

claim Pr_G3e4_bad : G3e.Main[bad] = G4.Main[bad] using G3e_G4.

claim Pr_INDCCA_G4: |INDCCA.Main[res] - 1%r/2%r| <= 
  G4.Main[bad] + 
  qD%r * ((qG + 1)%r / (2^p)%r) +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G3e4_bad.

(** ******************************************* *)
(**          Definition of the Game G5          *)
(** ******************************************* *)
game G5 = G4
  var badH : bool
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var t, r, h : bitstring{p};
    var result : bitstring{u};
    var _u : bitstring{u};
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0 = {0,1}^ku;
      LD = (Cdef,x) :: LD;
      result = bs0_u;
(**   Case : in_dom(s, Hm) *)
      if(in_dom(s, Hm)){
        h = Hm[s];
        r = t ^^ h;
(**     Inline G *)
        if(mem(r, map_to_list(Gm))){
          g_0 = Gm[r];
          if(low_bits_ku(s ^^ g_0) = bs0_k1) {
            result = high_bits_ku(s ^^ g_0);
          }
        } 
      } 
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and H = {
   var h : bitstring{p};
   h = {0,1}^p;
   if (!in_dom (x,Hm)) {
     Hm[x] = h;
     badH = badH || x = ss;
   } else h = Hm[x];
   return Hm[x];
  }
  and Main = {
    var b' : bool;
    var m0, m1 : message;
    var k : key;
    hs = bs0_p; ts = bs0_p; cs = bs0_k; 
    gc = 0; hc = 0; dc = 0;
    Hm = empty_map; Gm = empty_map;
    LD = [];
    Cdef = false;
    bad = false;
    k = kg();
    (pks, sks) = k;
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = {0,1}^p;
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    Cdef = true;
    b' = A2(cs);
    return true;
  }. 

equiv G4_G5_D_A1 : G4.D_A1 ~ G5.D_A1 : 
  (={Gm, Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}) by auto.

equiv G4_G5_H_A : G4.H_A ~ G5.H_A : 
  (={Gm, Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}) by auto.

equiv G4_G5 : G4.Main ~ G5.Main : 
  true ==> (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}).
inline H.
app 16 16 (={Gm, Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}).
call (={Gm, Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}).
trivial.
call (={Gm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}).
inline H.
wp.
rnd.
wp.
call (={Gm, Hm, gc, hc, dc, sks, hs, rs, ss, ts, cs, Cdef}).
trivial.


claim Pr_G45_bad : G4.Main[bad] <= G5.Main[badH] + 
  ((qD * qG)%r + (2 * qD)%r + qG%r) / (2^p)%r admit.
claim Pr_G5_badH : G5.Main[badH] <= G5.Main[in_dom(ss, Hm)] admit.
claim Pr_INDCCA_G5: |INDCCA.Main[res] - 1%r/2%r| <= 
  G5.Main[in_dom(ss, Hm)] + 
  ((qD * qG)%r + (2 * qD)%r + qG%r) / (2^p)%r +
  qD%r * (qG + 1)%r / (2^p)%r +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).

unset Pr_G45_bad, Pr_G5_badH.

(** ******************************************* *)
(**    Operator needed to define the Oracle D   *)
(** ******************************************* *)
op find : (t_Gm, t_Hm, cipher, pkey) -> bitstring{p} * bitstring{ku}.

axiom find_spec :
  forall(Gm : t_Gm, Hm : t_Hm, c : cipher, pk : pkey),
    (exists(rs : bitstring{p}), in_dom(rs, Gm) &&
    exists(ss : bitstring{ku}), in_dom(ss, Hm) && 
    c = f(pk, ss || (rs ^^ Hm[ss])) && 
    low_bits_ku(ss ^^ Gm[rs]) = bs0_k1) =>
    (let r, s = find(Gm, Hm, c, pk) in
    f(pk, s || (r ^^ Hm[s])) = c &&
    low_bits_ku(s ^^ Gm[r]) = bs0_k1).

op get_nth : (int, 'a list) -> 'a.
print axiom.
axiom get_nth_spec1 :
  forall(n : int, L : 'a list),
    0 = n && L <> [] => get_nth(n, L) = hd(L).
axiom get_nth_spec2 :
  forall(n : int, L : 'a list),
    0 < n && L <> [] => get_nth(n, L) = get_nth(n-1, tl(L)).
checkproof.

(** ******************************************* *)
(**          Definition of the Game PDOW        *)
(** ******************************************* *)
print high_bits_ku.
game Gpdow = {
  var Gm : t_Gm
  var Hm : t_Hm
  var pks : pkey
  var sks : skey
  var cs : cipher
  var gc, hc, dc : int

  fun G = INDCCA.G
  fun G_A = INDCCA.G_A
  fun H = INDCCA.H
  fun H_A = INDCCA.H_A

  fun D_A1 (x : cipher) : bitstring{u} = {
    var _u : bitstring{u};
    var r : bitstring{p};
    var s : bitstring{ku};
    if (dc < qD) {
      (r, s) = find(Gm, Hm, x, pks);
      _u = high_bits_ku(Gm[r] ^^ s);
      dc = dc + 1;
    } else {
      _u = bs0_u;
    }
    return _u;
  }

  fun D_A2 (x : cipher) : bitstring{u} = {
    var _u : bitstring{u};
    if (x <> cs) _u = D_A1 (x);
    else _u = bs0_u;
    return _u;
  }

  fun A1 = G5.A1
  fun A2 = G5.A2

  fun I(pk : pkey, c : cipher) : bitstring{ku} = {
    var L : bitstring{ku} list;
    var n : int;
    var m0, m1 : message;
    var b' : bool;
    Gm = empty_map; Hm = empty_map;
    pks = pk;
    (m0, m1) = A1(pk);
    b' = A2(c);
    L = map_to_list(Hm);
    n = [0..(length(L) - 1)];
    return get_nth(n, L);
  }
  fun Main () : bool = {
    var key : key;
    var s, ss : bitstring{ku};
    var t : bitstring{p};
    hc = 0; gc = 0; dc = 0;
    Gm = empty_map; Hm = empty_map;
    key = kg();
    (pks, sks) = key;
    s = {0,1}^ku;
    t = {0,1}^p;
    ss = I(pks, f(pks, s || t));
    return s = ss;
  }
}.


claim Pr_G5_pdow : 
  G5.Main[in_dom(ss, Hm)] <= (1 / qH)%r * Gpdow.Main[res] admit.

claim Conclusion : |INDCCA.Main[res] - 1%r/2%r| <= 
  (1 / qH)%r * Gpdow.Main[res] + 
  ((qD * qG)%r + (2 * qD)%r + qG%r) / (2^p)%r +
  qD%r * (qG + 1)%r / (2^p)%r +
  qD%r * (1%r / (2^k1)%r) + 
  qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + 
  qD%r * ((1%r) / (2^p)%r).
  









  
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


