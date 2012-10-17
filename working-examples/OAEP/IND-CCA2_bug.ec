checkproof.
(** Misc *)
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

op [||] : (bitstring{u}, bitstring{k1}) -> bitstring{ku} as append_u_k1.
op [||] : (bitstring{ku}, bitstring{p}) -> bitstring{k} as append_ku_p.

op high_bits_ku : (bitstring{ku}) -> bitstring{u}.
op low_bits_ku : (bitstring{ku}) -> bitstring{k1}.

op high_bits_k : (bitstring{k}) -> bitstring{ku}.
op low_bits_k : (bitstring{k}) -> bitstring{p}.

op map_to_list : ('a, 'b) map -> 'a list.

axiom equiv_dom_list : 
  forall(M : ('a, 'b) map, x : 'a), 
    in_dom(x, M) <=> mem(x, map_to_list(M)).

axiom bound_length :
  forall(M : ('a, 'b) map, x : 'a, v : 'b),
    !(in_dom(x, M)) => (length(map_to_list(M[x <- v])) = 1 + length(map_to_list(M))).

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

axiom split_bs_k : 
  forall(x : bitstring{k}), 
    x = (high_bits_k(x) || low_bits_k(x)).

axiom split_bs_ku :
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
    (low_bits_ku(x ^^ y) = bs0_k1) <=> ((low_bits_ku(x) ^^ low_bits_ku(y)) = bs0_k1).

lemma equiv_axlku_0 :
  forall(x, y : bitstring{ku}),
    (low_bits_ku(x ^^ y) = bs0_k1) <=> (low_bits_ku(x) = low_bits_ku(y)).

lemma assoc_xor_high_k :
  forall(x, y : bitstring{k}),
    (high_bits_k(x ^^ y) = bs0_ku) <=> ((high_bits_k(x) ^^ high_bits_k(y)) = bs0_ku).

lemma equiv_axhk_0 :
  forall(x, y : bitstring{k}),
    (high_bits_k(x ^^ y) = bs0_ku) <=> (high_bits_k(x) = high_bits_k(y)).

lemma assoc_xor_high_ku :
  forall(x, y : bitstring{ku}),
    (high_bits_ku(x ^^ y) = bs0_u) <=> ((high_bits_ku(x) ^^ high_bits_ku(y)) = bs0_u).

lemma equiv_axhku_0 :
  forall(x, y : bitstring{ku}),
    (high_bits_ku(x ^^ y) = bs0_u) <=> (high_bits_ku(x) = high_bits_ku(y)).
  
spec append_ku_p() :
   a = {0,1}^ku||{0,1}^p ~ b = {0,1}^k : true ==> (a = b).

spec split_ku() :
  a = {0,1}^ku ~ b = {0,1}^u || {0,1}^k1 : true ==> (a = b).

(** Usefull types *)
type message = bitstring{u}.
type cipher  = bitstring{k}.
type t_Gm    = (bitstring{p}, bitstring{ku}) map.
type t_Hm    = (bitstring{ku}, bitstring{p}) map.
type t_domDA = (bool * cipher) list.
type t_domGA = bitstring{p} list.
type t_domHA = bitstring{ku} list.


(** Specification of key generation *)
type pkey.
type skey.
type key      = pkey * skey.
pop kg        : () -> key.
op valid_keys : (pkey,skey) -> bool.

spec validkeys() :
  x=kg() ~ y=kg() : true ==> x=y && valid_keys(fst(x), snd(x)).

(** Specification of f *)
op f    : (pkey, bitstring{k}) -> bitstring{k}.
op finv : (skey, bitstring{k}) -> bitstring{k}.

axiom fofinv : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => f(pk, finv(sk, m)) = m.

axiom finvof : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => finv(sk, f(pk, m)) = m.

(** The adversary *)
adversary A1(pk:pkey) : message * message 
     { bitstring{p} -> bitstring{ku}; bitstring{ku} -> bitstring{p};
       cipher -> bitstring{u}}.
adversary A2(y:cipher) : bool 
     { bitstring{p} -> bitstring{ku}; bitstring{ku} -> bitstring{p};
       cipher -> bitstring{u}}.


(** The IND-CCA game *)

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
    var kp : bitstring{ku};
    if (gc < qG){
      kp = G(x);
      gc = gc + 1;
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
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false;
    (pks, sks) = KG();
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

(*
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
    
  and Main = {
    var b, b' : bool;
    var m0, m1 : message;
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false;
    (pks, sks) = KG();
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
*)
(*
equiv INDCCA_INDCCA' : INDCCA.Main ~ INDCCA'.Main : true ==> ={res}.
inline Enc, KG, G.
auto (={Gm, Hm, gc, hc, dc, sks, cs}).
swap{1} 13 -4; swap{2} 2 1.
*rnd; wp; rnd.
auto (={Gm, Hm, gc, hc, dc, sks, cs}).
trivial.
save.
*)
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

game G1 = INDCCA'
  var gs : bitstring{ku}
  var bad1, bad2, bad3 : bool
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
 
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^ku;
      (** Dans le cas où in_dom(s, domHA) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
      (** Inlining de G *)
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
        (** Dans le cas où NOT in_dom(s, domHA) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
        (** Inlining de G *)
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
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false; bad1 = false; bad2 = false; bad3 = false;
    (pks, sks) = KG();
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

equiv INDCCA'_G1 : INDCCA'.Main ~ G1.Main : true ==> ={bad} &&  (!bad{1} => ={res}).
swap {2} -4.
call upto (bad) 
  with(={gc, Hm, hc, dc, sks, rs, cs} && eq_except(Gm{1}, Gm{2}, rs{1}) &&
    (in_dom(rs, Gm){2} <=> bad{2})).
inline H, KG; wp.
rnd; wp.
swap{2} 14 2.
rnd (ss ^^ ((b? m1 : m0) || bs0_k1)).
rnd.
auto (={gc, hc, dc, Gm, Hm, sks, rs, cs, bad} && (in_dom(rs, Gm){2} <=> bad{2})).
trivial.
save.

claim Pr_INDCCA'_G1 : 
  |INDCCA'.Main[res] - G1.Main[res]| <=  G1.Main[bad] using INDCCA'_G1.
claim Pr_G1_res : G1.Main[res] = 1%r/2%r compute.
claim Pr_INDCCA_G1 : |INDCCA.Main[res] - 1%r/2%r| <=  G1.Main[bad].

unset Pr_INDCCA_INDCCA', Pr_G1_res, Pr_INDCCA'_G1.

game G2' = G1
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
 
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^ku;
      (** Dans le cas où in_dom(s, domHA) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
      (** Inlining de G *)
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
        (** Dans le cas où NOT in_dom(s, domHA) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
        (** Inlining de G *)
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
   var b, b' : bool;
    var m0, m1 : message;
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map;
    bad = false; bad1 = false; bad2 = false; bad3 = false;
    (pks, sks) = KG();
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    return true;
  }.

equiv G1_G2' : G1.Main ~ G2'.Main : true ==> ((bad1 || bad2){1} <=> (bad1 || bad2){2}) && (!(bad1 || bad2){2} => (={Gm, Hm, gc, hc, dc, sks, cs} && (bad{1} => (bad{2} || bad3{2})))).
rnd{1}.
auto upto (bad1 || bad2) with (={Gm, gc, Hm, hc, dc, sks, rs, cs} && (bad{1} => bad{2} || bad3{2})).
inline KG; trivial.
save.

claim Pr_G1_bad : G1.Main[bad] = 
  G1.Main[bad && (bad1 || bad2)] + G1.Main[bad && !(bad1 || bad2)] split.

claim Pr_G1_G2'_1 : G1.Main[bad && (bad1 || bad2)] <= 
  G2'.Main[bad1 || bad2] using G1_G2'.

claim Pr_G1_G2'_2 : G1.Main [bad && !(bad1 || bad2)] <= 
  G2'.Main[bad || bad3] using G1_G2'.

claim Pr_G2'_1 : G2'.Main[bad1 || bad2] <= 
  G2'.Main[bad1] + G2'.Main[bad2] compute.

claim Pr_G2'_2 : G2'.Main[bad || bad3] <= 
  G2'.Main[bad] + G2'.Main[bad3] split.

claim Pr_G1_G2' : G1.Main[bad] <= 
  G2'.Main[bad] + G2'.Main[bad1] + G2'.Main[bad2] + G2'.Main[bad3].

claim Pr_INDCCA_G2' : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2'.Main[bad] + G2'.Main[bad1] + G2'.Main[bad2] + G2'.Main[bad3].

unset Pr_G1_bad, Pr_G1_G2'_1, Pr_G1_G2'_2, Pr_G2'_1, Pr_G2'_2, Pr_G1_G2'.

game G2'' = G2'
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result : bitstring{u};
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0 = {0,1}^u || {0,1}^k1;
    result = bs0_u;
      (** Dans le cas où in_dom(s, domHA) *)
    if(in_dom(s, Hm)){
      r = t ^^ Hm[s];
      (** Inlining de G *)
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
        (** Dans le cas où NOT in_dom(s, domHA) *)
      h_0 = {0,1}^p;
      Hm[s] = h_0;
      r = t ^^ h_0;
        (** Inlining de G *)
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

equiv G2'_G2''_D : G2'.D ~ G2''.D : (={sks, Gm, Hm, bad, bad1, bad2, bad3, rs}).
app 3 4 (={sks, Gm, Hm, bad, bad1, bad2, bad3, s, t, g_0, rs} && (result{2} = bs0_u{2})).
wp; apply : split_ku(); trivial.
derandomize; trivial.
save.

equiv G2'_G2''_D_A1 : G2'.D_A1 ~ G2''.D_A1 : (={sks, Gm, Hm, bad, bad1, bad2, bad3, rs, dc}).
if; [wp | trivial].
call using G2'_G2''_D; trivial.
save.

equiv G2'_G2''_D_A2 : G2'.D_A2 ~ G2''.D_A2 : (={sks, Gm, Hm, bad, bad1, bad2, bad3, rs, dc, cs}).
if; [call using G2'_G2''_D_A1; trivial | trivial].
save.

equiv G2'_G2'' : G2'.Main ~ G2''.Main : true ==> ={sks, Gm, Hm, bad, bad1, bad2, bad3, rs, gc, hc, dc, cs} 
by auto (={sks, Gm, Hm, bad, bad1, bad2, bad3, rs, gc, hc, dc, cs}).

claim Pr_G2'_G2''_bad  : G2'.Main[bad]  = G2''.Main[bad]  using G2'_G2''.
claim Pr_G2'_G2''_bad1 : G2'.Main[bad1] = G2''.Main[bad1] using G2'_G2''.
claim Pr_G2'_G2''_bad2 : G2'.Main[bad2] = G2''.Main[bad2] using G2'_G2''.
claim Pr_G2'_G2''_bad3 : G2'.Main[bad3] = G2''.Main[bad3] using G2'_G2''.

claim Pr_INDCCA_G2'' : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2''.Main[bad]  + G2''.Main[bad1] + G2''.Main[bad2] + G2''.Main[bad3].

unset Pr_G2'_G2''_bad, Pr_G2'_G2''_bad1, Pr_G2'_G2''_bad2, Pr_G2'_G2''_bad3.

game G2''' = G2''
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    result = bs0_u;
    if(length(map_to_list(Gm)) < qD + qG){
      (** Dans le cas où in_dom(s, domHA) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        (** Inlining de G *)
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
          (** Dans le cas où NOT in_dom(s, domHA) *)
        r = {0,1}^p;
        Hm[s] = r;
          (** Inlining de G *)
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

(*
equiv G2''_G2''' : G2''.Main ~ G2'''.Main : true ==> 
  (={Gm, Hm, bad, bad1, bad2, bad3, sks, gc, hc, dc, rs} && 
  gc{2} <= qG && dc{2} <= qD).
call (={Gm, Hm, bad, bad1, bad2, bad3, sks, gc, hc, dc, rs} && gc{2} <= qG && dc{2} <= qD).

(** BUG : lorsque l'on tente de faire un call sur l'equiv suivant.
  * This is a bug (please report): term_of_exp lsymbol : r_1_2 || r_0_2: 
  * append_u_k1(r_13, r_03) : 
  * Why.Ty.TypeMismatch bitstring_k1 and bitstring_p
*)

equiv G2''_G2''' : G2''.Main ~ G2'''.Main : true ==> (={bad, bad1, bad2, bad3} && (length(map_to_list(Gm{2})) < qD + qG)).
admit.
save.

claim Pr_G2''_G2'''_bad : 
  G2''.Main[bad] = G2'''.Main[bad] using G2''_G2'''.
claim Pr_G2''_G2'''_bad1 : 
  G2''.Main[bad1] = G2'''.Main[bad1] using G2''_G2'''.
claim Pr_G2''_G2'''_bad2 : 
  G2''.Main[bad2] = G2'''.Main[bad2] using G2''_G2'''.
claim Pr_G2''_G2'''_bad3 : 
  G2''.Main[bad3] = G2'''.Main[bad3] using G2''_G2'''.
claim Pr_INDCCA_G2''' : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2'''.Main[bad] + G2'''.Main[bad1] + G2'''.Main[bad2] + G2'''.Main[bad3].

unset Pr_G2''_G2'''_bad, Pr_G2''_G2'''_bad1, Pr_G2''_G2'''_bad2, 
      Pr_G2''_G2'''_bad3.

game Gtmp = G2'''
  where D_A1 = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
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
       
      if(length(map_to_list(Gm)) < qD + qG){
        (** Dans le cas où in_dom(s, domHA) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
          (** Inlining de G *)
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
            (** Dans le cas où NOT in_dom(s, domHA) *)
          r = {0,1}^p;
          Hm[s] = r;
            (** Inlining de G *)
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
      dc = dc + 1;
    } else {
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

equiv G2'''_Gtmp_D : G2'''.D ~ Gtmp.D : 
  (={Gm, Hm, dc, sks, bad, bad1, bad2, bad3, rs} && dc{2} <= qD) by auto.

equiv G2'''_Gtmp_D_A1 : G2'''.D_A1 ~ Gtmp.D_A1 : 
  (={Gm, Hm, dc, sks, bad, bad1, bad2, bad3, rs} && dc{2} <= qD) by auto.

equiv G2'''_Gtmp_D_A2 : G2'''.D_A2 ~ Gtmp.D_A2 : (={Gm, Hm, dc, sks, bad, bad1, bad2, bad3, rs, cs}  && dc{2} <= qD) by auto.

equiv G2'''_Gtmp : G2'''.Main ~ Gtmp.Main : 
  true ==> ={Gm, Hm, gc, hc, dc, sks, bad, bad1, bad2, bad3, rs, cs} &&
           dc{2} <= qD.
inline KG.
auto (={Gm, Hm, gc, hc, dc, sks, bad, bad1, bad2, bad3, rs, cs} &&
     dc{2} <= qD).
trivial.
save.

claim G2'''_Gtmp_bad  : G2'''.Main[bad] <= 
                        Gtmp.Main[bad] using G2'''_Gtmp.
claim G2'''_Gtmp_bad1 : G2'''.Main[bad1] <= 
                        Gtmp.Main[bad1 && dc <= qD ] using G2'''_Gtmp.
claim G2'''_Gtmp_bad2 : G2'''.Main[bad2] <= 
                        Gtmp.Main[bad2 && dc <= qD] using G2'''_Gtmp.
claim G2'''_Gtmp_bad3 : G2'''.Main[bad3] <= 
                        Gtmp.Main[bad3 && dc <= qD] using G2'''_Gtmp.

claim Pr_Gtmp_bad1 : 
  Gtmp.Main[bad1 && dc <= qD] <= 
  qD%r * (1%r / (2^k1)%r) compute 10 (bad1), (dc).

unset Pr_INDCCA_G2''', Pr_INDCCA_G2'', Pr_INDCCA_G2', Pr_INDCCA_G1, 
      Pr_Gtmp_bad1.
timeout 20.

claim Pr_Gtmp_bad2 : 
  Gtmp.Main[bad2 && dc <= qD] <= qD%r * ((qD + qG)%r / (2^p)%r) 
  compute 10 (bad2), (dc).

(* BUG : Stack_Overflow. *)
claim Pr_Gtmp_bad3 : 
  Gtmp.Main[bad3 && dc <= qD] <= qD%r * ((1%r) / (2^p)%r) admit.

timeout 3.
set Pr_INDCCA_G2''', Pr_INDCCA_G2'', Pr_INDCCA_G2', Pr_INDCCA_G1, 
    Pr_Gtmp_bad1.

claim Pr_INDCCA_Gtmp : |INDCCA.Main[res] - 1%r/2%r| <= 
  Gtmp.Main[bad] + qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + qD%r * ((1%r) / (2^p)%r).

unset Pr_G2'''_Gtmp_bad, Pr_G2'''_Gtmp_bad1, Pr_G2'''_Gtmp_bad2, 
      Pr_G2'''_Gtmp_bad3, Pr_Gtmp_bad1, Pr_Gtmp_bad2, Pr_Gtmp_bad3.

game G2 = Gtmp
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    result = bs0_u;
    if(length(map_to_list(Gm)) < qD + qG){
      (** Dans le cas où in_dom(s, domHA) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        (** Inlining de G *)
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
          (** Dans le cas où NOT in_dom(s, domHA) *)
        r = {0,1}^p;
        Hm[s] = r;
          (** Inlining de G *)
        if(!mem(r, map_to_list(Gm))){
          Gm[r] = g_0;
        }
      }
    }
    return result;
  } 
  and D_A1 = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    if (dc < qD) {
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;
      if(length(map_to_list(Gm)) < qD + qG){
        (** Dans le cas où in_dom(s, domHA) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
          (** Inlining de G *)
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
            (** Dans le cas où NOT in_dom(s, domHA) *)
          r = {0,1}^p;
          Hm[s] = r;
            (** Inlining de G *)
          if(!mem(r, map_to_list(Gm))){
            Gm[r] = g_0;
          }
        }
      }
      dc = dc + 1;
    } else {
      result = bs0_u;
    }
    _u = result;
    return _u;
  }.

equiv Gtmp_G2_D : Gtmp.D ~ G2.D : (={Gm, Hm, sks, bad, dc, rs}).
app 6 6 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result}).
trivial.
if.
if.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result, r}).
trivial.
if.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result, r}).
trivial.
trivial.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result, r}).
trivial.
if.
trivial.
trivial.
app 2 2 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result, r}).
trivial.
trivial.
trivial.
save.

equiv Gtmp_G2_D_A1 : Gtmp.D_A1 ~ G2.D_A1 : (={Gm, Hm, sks, bad, dc, rs}).
if.
app 6 6 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, result}).
trivial.
if.
if.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, r, result}).
trivial.
if.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, t, g_0, r, result}).
trivial.
if.
trivial.
trivial.
app 1 1 (={Gm, Hm, sks, bad, dc, rs, s, r, t, g_0, result, r}).
trivial.
if.
trivial.
trivial.
app 2 2 (={Gm, Hm, sks, bad, dc, rs, s, r, t, g_0, result, r}).
trivial.
case{1} : !mem(r, map_to_list(Gm)).
trivial.
trivial.
trivial.
trivial.
save.

equiv Gtmp_G2_D_A2 : Gtmp.D_A2 ~ G2.D_A2 :(={Gm, Hm, sks, bad, dc, rs, cs}).
if; [call using Gtmp_G2_D_A1; trivial | trivial].
save.

equiv Gtmp_G2 : Gtmp.Main ~ G2.Main : true ==> ={Gm, Hm, sks, bad, dc, cs}
by auto (={Gm, Hm, sks, bad, gc, hc, dc, rs, cs}).

claim Pr_Gtmp_G2_bad : Gtmp.Main[bad] = G2.Main[bad] using Gtmp_G2.

claim Pr_INDCCA_G2 : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2.Main[bad] + qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + qD%r * ((1%r) / (2^p)%r).

unset Pr_Gtmp_G2_bad.

type t_Gm_bis = (bitstring{p}, bool * bitstring{ku}) map.

game G2_1 = G2 
  var Gm_bis : t_Gm_bis
  var bad4 : bool
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    result = bs0_u;
    if(length(map_to_list(Gm_bis)) < qD + qG){
      (** Dans le cas où in_dom(s, domHA) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        (** Inlining de G *)
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
          (** Dans le cas où NOT in_dom(s, domHA) *)
        r = {0,1}^p;
        Hm[s] = r;
          (** Inlining de G *)
        if(!mem(r, map_to_list(Gm_bis))){
          Gm_bis[r] = (true, g_0);
        }
      }
    }
    return result;
  }
  and D_A1 = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;  
       
      if(length(map_to_list(Gm_bis)) < qD + qG){
        (** Dans le cas où in_dom(s, domHA) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
          (** Inlining de G *)
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
    var b, b' : bool;
    var m0, m1 : message;
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map; Gm_bis = empty_map;
    bad = false; bad4 = false;
    (pks, sks) = KG();
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

equiv G2_G2_1 : G2.Main ~ G2_1.Main :
  true ==> ={Hm, gc, hc, dc, bad, sks, rs, cs} && eq_map_snd(Gm{1}, Gm_bis{2}).
call (={Hm, gc, hc, dc, bad, sks, rs, cs} &&  eq_map_snd(Gm{1}, Gm_bis{2})).
inline KG, H.
wp; rnd; wp.
call (={Hm, gc, hc, dc, bad, sks, rs, cs} &&  eq_map_snd(Gm{1}, Gm_bis{2})).
trivial.
save.

claim Pr_G2_G2_1_bad : G2.Main[bad] = G2_1.Main[bad] using G2_G2_1.
claim Pr_INDCCA_G2_1 : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2_1.Main[bad] + qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + qD%r * ((1%r) / (2^p)%r).

unset Pr_G2_G2_1_bad.

game G2_2 = G2_1
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    result = bs0_u;
    if(length(map_to_list(Gm_bis)) < qD + qG){
      (** Dans le cas où in_dom(s, domHA) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        (** Inlining de G *)
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
          (** Dans le cas où NOT in_dom(s, domHA) *)
        r = {0,1}^p;
        Hm[s] = r;
          (** Inlining de G *)
        if(!mem(r, map_to_list(Gm_bis))){
          Gm_bis[r] = (true, g_0);
        }
      }
    }
    return result;
  }
  and D_A1 = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      result = bs0_u;  
       
      if(length(map_to_list(Gm_bis)) < qD + qG){
        (** Dans le cas où in_dom(s, domHA) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
          (** Inlining de G *)
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
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and Main = {
    var b, b' : bool;
    var m0, m1 : message;
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map; Gm_bis = empty_map;
    bad = false; bad4 = false;
    (pks, sks) = KG();
    rs = {0,1}^p;
    ss = {0,1}^ku;
    (m0, m1) = A1(pks);
    hs = H(ss);
    ts = hs ^^ rs;
    cs = f(pks, ss || ts);
    b' = A2(cs);
    return true;
  }.

equiv G2_1_G2_2 : G2_1.Main ~ G2_2.Main : true ==> ={bad4} && 
  (!bad4{1} => ={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs, res}).
inline KG, H.
call upto (bad4) with (={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs}).
rnd; wp.
call upto (bad4) with (={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs}).
trivial.
save.

claim Pr_G2_1_G2_2_bad : G2_1.Main[bad] <= G2_2.Main[bad] + G2_2.Main[bad4] using G2_1_G2_2.

claim Pr_INDCCA_G2_2 : |INDCCA.Main[res] - 1%r/2%r| <= 
  G2_2.Main[bad] + G2_2.Main[bad4] + qD%r * (1%r / (2^k1)%r) +
  qD%r * ((qD + qG)%r / (2^p)%r) + qD%r * ((1%r) / (2^p)%r).

unset Pr_G2_1_G2_2_bad.

op op_P : 
  (bitstring{ku}, bitstring{p}, skey, (bool * cipher) list, t_Hm) -> bool.

axiom P :
  forall(g : bitstring{ku}, r : bitstring{p}, 
  sk : skey, L : (bool * cipher) list, H : t_Hm),
    op_P(g, r, sk, L, H) => exists(d: bool, c : cipher), 
      mem((d, c), L) => 
        let s = high_bits_k(finv(sk, c)) in 
        let t = low_bits_k(finv(sk, c)) in
          in_dom(s, H) && 
          (r = t ^^ H[s]) && 
          (low_bits_ku(s ^^ g) = bs0_k1).


game G2_3 = G2_2 
  var bad5 : bool
  var LD : (bool * cipher) list
  var Cdef : bool
  where D = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var d : bool;
    s = high_bits_k(finv(sks, x));
    t = low_bits_k(finv(sks, x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = (g_0_h || g_0_l);
    LD = (Cdef, x)::LD;
    result = bs0_u;
    if(length(map_to_list(Gm_bis)) < qD + qG){
      (** Dans le cas où in_dom(s, domHA) *)
      if(in_dom(s, Hm)){
        r = t ^^ Hm[s];
        (** Inlining de G *)
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
          (** Dans le cas où NOT in_dom(s, domHA) *)
        r = {0,1}^p;
        Hm[s] = r;
          (** Inlining de G *)
        if(!mem(r, map_to_list(Gm_bis))){
          Gm_bis[r] = (true, g_0);
        }
      }
    }
    return result;
  }
  and D_A1 = {
    var g_0, s : bitstring{ku};
    var h_0, t, r : bitstring{p};
    var result, g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    var d : bool;
    if (dc < qD){
      s = high_bits_k(finv(sks, x));
      t = low_bits_k(finv(sks, x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = (g_0_h || g_0_l);
      LD = (Cdef, x)::LD;
      result = bs0_u;  
       
      if(length(map_to_list(Gm_bis)) < qD + qG){
        (** Dans le cas où in_dom(s, domHA) *)
        if(in_dom(s, Hm)){
          r = t ^^ Hm[s];
          (** Inlining de G *)
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
      result = bs0_u;
    }
    _u = result;
    return _u;
  }
  and G = {
    var g, tmp_fst : bitstring{ku};
    var d : bool;
    var tmp_snd : bitstring{p};      
    g = {0,1}^ku;
    if (!in_dom(x,(Gm_bis)))
    { 
      bad = bad || x = rs;
      Gm_bis[x] = (false, g);
    } else {
      (d, g) = Gm_bis[x];
      if(d = true){
        Gm_bis[x] = (false, g);
        bad5 = op_P(g, x, sks, LD, Hm);
      }
    }
    return snd(Gm_bis[x]);   
  }
  and Main = {
    var b, b' : bool;
    var m0, m1 : message;
    var g, s : bitstring{ku};
    var r, h, t : bitstring{p}; 
    cs = bs0_k;
    gc = 0; hc = 0; dc = 0;
    Gm = empty_map;  Hm = empty_map; Gm_bis = empty_map;
    LD = [];
    Cdef = false;
    bad = false; bad5 = false;
    (pks, sks) = KG();
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

checkproof.
(*
op op_Phi : (skey, t_Gm_bis, t_Hm, (bool * cipher) list) -> bool.

axiom Phi :
  forall(sk : skey, G : t_Gm_bis, H : t_Hm, D : (bool * cipher) list),
    op_Phi(sk, G, H, D) => exists(d: bool, c : cipher), 
      mem((d, c), D) => 
        let s = high_bits_k(finv(sk, c)) in 
        let t = low_bits_k(finv(sk, c)) in
        let r = t ^^ H[s] in
          in_dom(r, G) && 
          in_dom(s, H) && 
          fst(G[r]) = true &&
          low_bits_ku(s ^^ snd(G[r])) = bs0_k1.

equiv G2_2_G2_3 : G2_2.Main ~ G2_3.Main : true ==> 
   ={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs} && 
   bad4{1} => (bad5{2} || op_Phi(sks, Gm_bis, Hm, LD){2}).
inline KG, H.
call (={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs} && 
   bad4{1} => (bad5{2} || op_Phi(sks, Gm_bis, Hm, LD){2})).

*)
pred phi (sk : 'd, G : ('a, ('c * 'b)) map, H : ('b, 'a) map, 
      D : (bool * cipher) list) =
      exists(d : bool, c : cipher), 
  mem((d, c), D) => 
    let s = high_bits_k(finv(sk, c)) in 
    let t = low_bits_k(finv(sk, c)) in
    let r = t ^^ H[s] in
      in_dom(r, G) && 
      in_dom(s, H) && 
      fst(G[r]) = true &&
      low_bits_ku(s ^^ snd(G[r])) = bs0_k1.


(** BUG : Unexpected Exception : 
      Trans.TransFailure("Simplify_trivial_quantification", _)
*)
equiv G2_2_G2_3 : G2_2.Main ~ G2_3.Main : true ==> 
  ={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs} && 
  bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2})).
inline KG, H.
call (={Gm_bis, Hm, gc, hc, dc, bad, sks, rs, cs} && 
   bad4{1} => (bad5{2} || phi(sks{2}, Gm_bis{2}, Hm{2}, LD{2}))).
