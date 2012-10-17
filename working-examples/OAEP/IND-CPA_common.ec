prover "alt-ergo", vampire, cvc3.
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
cnst qG : int.

axiom p_pos : 0 <= p.
axiom qG_pos : 0 <= qG.

op [||] : (bitstring{u}, bitstring{k1}) -> bitstring{ku} as append_u_k1.
op [||] : (bitstring{ku}, bitstring{p}) -> bitstring{k} as append_ku_p.

op high_bits : (bitstring{k}) -> bitstring{ku}.
op low_bits : (bitstring{k}) -> bitstring{p}.



axiom high_bits_spec : 
  forall(s : bitstring{ku}, t : bitstring{p}),
    high_bits(s || t) = s. 

axiom low_bits_spec : 
  forall(s : bitstring{ku}, t : bitstring{p}),
    low_bits(s || t) = t.

axiom append() :
   a = {0,1}^ku||{0,1}^p ~ b = {0,1}^k : true ==> (a = b).

(** Usefull types *)
type message = bitstring{u}.
type cipher  = bitstring{k}.
type t_Gm = (bitstring{p}, bitstring{ku}) map.
type t_Hm = (bitstring{ku}, bitstring{p}) map.
type t_domGA = bitstring{p} list.
type t_domHA = bitstring{ku} list.

(** Specification of key generation *)

type pkey.
type skey.
type key    = pkey * skey.
pop kg : () -> key.
op valid_keys : (pkey,skey) -> bool.

axiom validkeys() :
  x=kg() ~ y=kg() : true ==> x=y && valid_keys(fst(x), snd(x)).

(** Specification of f *)
op f     : (pkey, bitstring{k}) -> bitstring{k}.
op finv : (skey, bitstring{k}) -> bitstring{k}.

axiom fofinv : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => f(pk, finv(sk, m)) = m.

axiom finvof : 
  forall(pk:pkey, sk:skey, m:bitstring{k}),
    valid_keys(pk,sk) => finv(sk, f(pk, m)) = m.


(** The adversary *)


adversary A1(pk:pkey) : message * message 
     { bitstring{p} -> bitstring{ku}; bitstring{ku} -> bitstring{p} }.
adversary A2(y:cipher) : bool 
     { bitstring{p} -> bitstring{ku}; bitstring{ku} -> bitstring{p} }.


(** The IND-CPA game *)

game INDCPA = {

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

  abs A1 = A1 {G_A, H_A}
  abs A2 = A2 {G_A, H_A}

  fun Main() : bool = {
    var pk : pkey;
    var sk : skey;
    var b, b' : bool;
    var m0, m1 : message;
    var c : cipher;

    Gm = empty_map;  Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    (m0, m1) = A1(pk);
    b = {0,1};
    c = Enc(pk, b? m1 : m0);
    b' = A2(c);
    return b = b';
  }
}.
    
game G1 = INDCPA 
  var rs : bitstring{p}
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b, b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var g, s : bitstring{ku};
    var h, t : bitstring{p}; 

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    (m0, m1) = A1(pk);
    b = {0,1};
    rs = {0,1}^p;
    g = G(rs);
    s = g ^^ ((b ? m1 : m0 ) || bs0_k1);
    h = H(s);
    t = h ^^ rs;
    c = f(pk, s || t);    
    b' = A2(c);
    return b = b';
  }.

equiv INDCPA_G1 : INDCPA.Main ~ G1.Main : true ==> ={res}.
 inline Enc, KG;eqobs_in (={Gm, domGA, Hm, domHA}) (true) (={b, b'}).
 swap{1} [9-10] 2; wp.
 eqobs_in (={Gm, domGA, Hm, domHA}) (true) 
    (={b, g, pk, m0, m1, Gm, domGA, Hm, domHA} && (r{1} = rs{2}));trivial.
save.

claim Pr_INDCPA_G1 : INDCPA.Main[res] = G1.Main[res] using INDCPA_G1.

game G2 = G1
  var ss : bitstring{ku}
  var hs : bitstring{p}
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b, b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var h, t : bitstring{p}; 

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    rs = {0,1}^p;    
    ss = {0,1}^ku;
    (m0, m1) = A1(pk);
    h = H(ss);
    hs = h;
    t = h ^^ rs;
    c = f(pk, ss || t);
    b' = A2(c);
    b = {0,1};
    return b = b';
  }.

equiv G1_G2 : G1.Main ~ G2.Main : true ==>  
  mem(rs,domGA){1} = mem(rs,domGA){2} && (!mem(rs, domGA){1} => ={res}).
 swap{2} -5; swap{2} [6-7] 2.
 auto upto (mem(rs, domGA)) 
 with (={domGA, Hm, domHA, rs} && eq_except(Gm{1}, Gm{2}, rs{1})).
 rnd (ss ^^  ((if b{2} then m1{2} else m0{2}) || bs0_k1));wp.
 eqobs_in (={Gm, domGA, Hm, domHA}) 
          (forall(w:bitstring{p}), in_dom(w, Gm){1} => (mem(w, domGA){1})) 
          (={Gm, domGA, Hm, domHA, pk, sk, m0, m1,b,rs});trivial.
save.

claim Pr_G2_res : G2.Main[res] = 1%r/2%r compute.

claim Pr_G1_G2 : 
  |G1.Main[res] - G2.Main[res]| <= G2.Main[mem(rs, domGA)] using G1_G2.

claim Pr_INDCPA_G2 : 
  | INDCPA.Main[res] - 1%r/2%r | <= G2.Main[mem(rs, domGA)].

unset Pr_INDCPA_G1, Pr_G2_res, Pr_G1_G2.

game G2_1 = G2
  where Main = {
    var pk : pkey;
    var sk : skey;
    var b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var h, t : bitstring{p}; 

    Gm = empty_map; Hm = empty_map;
    domGA = []; domHA = [];
    (pk, sk) = KG();
    t = {0,1}^p;    
    ss = {0,1}^ku;
    (m0, m1) = A1(pk);
    hs = H(ss);
    rs = hs ^^ t;
    c = f(pk, ss || t);
    b' = A2(c);
    return true;
}.

equiv G2_G2_1 : G2.Main ~ G2_1.Main : true ==> ={rs, domGA}.
 rnd{1}; swap 6 3.
 auto (={Gm, domGA, Hm, domHA}).
 rnd (hs{2} ^^ t).
 auto (={Gm, domGA, Hm, domHA}).
 inline KG; trivial.
save.

claim Pr_G2_G2_1 : 
  G2.Main[mem(rs, domGA)] = G2_1.Main[mem(rs, domGA)] using G2_G2_1.

game G2_2 = G2_1
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
    tmp = {0,1}^ku || {0,1}^p;
    ss = high_bits(tmp);
    t = low_bits(tmp);    
    hs = H(ss);
    rs = hs ^^ t;
    c = f(pk, tmp);
    b' = A2(c);
    return true;
  }.

equiv G2_1_G2_2 : G2_1.Main ~ G2_2.Main : true ==> ={rs, domGA}.
 derandomize; auto (={Gm, domGA, Hm, domHA}).
 swap{1} 1; trivial.
save.

claim Pr_G2_1_G2_2 : 
  G2_1.Main[mem(rs, domGA)] = G2_2.Main[mem(rs, domGA)] using G2_1_G2_2.

game G2_3 = G2_2
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
    tmp = {0,1}^k;
    ss = high_bits(tmp);
    t = low_bits(tmp);    
    hs = H(ss);
    rs = hs ^^ t;
    c = f(pk, tmp);
    b' = A2(c);
    return true;
  }.
checkproof.
equiv G2_2_G2_3 : G2_2.Main ~ G2_3.Main : true ==> ={rs, domGA}.
 inline KG.
 eqobs_in (={Gm, domGA, Hm, domHA}) (true) (={rs, domGA}).
 apply : append(3).
 eqobs_in (={Gm, domGA, Hm, domHA}) (true) (={Gm, domGA, Hm, domHA, pk});trivial.
save.

claim Pr_G2_2_G2_3 : 
  G2_2.Main[mem(rs, domGA)] = G2_3.Main[mem(rs, domGA)] using G2_2_G2_3.

game G3 = G2
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
    hs = H(ss);
    rs = hs ^^ t;
    b' = A2(c);
    return true;
  }.

equiv G2_3_G3 : G2_3.Main ~ G3.Main : true ==> ={rs, domGA}.
 inline KG;auto (={Gm, domGA, Hm, domHA}).
 rnd (f(pk{2}, c)), (finv(sk{2}, c)).
 auto (={Gm, domGA, Hm, domHA}).
 apply : validkeys(); trivial.
save.

claim Pr_G2_3_G3 : 
  G2_3.Main[mem(rs, domGA)] = G3.Main[mem(rs, domGA)] using G2_3_G3.

claim Pr_INDCPA_G3 : | INDCPA.Main[res] - 1%r/2%r | <= G3.Main[mem(rs, domGA)].

unset Pr_INDCPA_G2, Pr_G2_G2_1, Pr_G2_1_G2_2, Pr_G2_2_G2_3, Pr_G2_3_G3.
