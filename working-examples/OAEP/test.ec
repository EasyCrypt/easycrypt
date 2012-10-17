

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





game Gtmp = {
  var Gm : t_Gm
  var Hm : t_Hm
  var pks : pkey
  var sks : skey
  var cs : cipher
  var hc : int
  var gc : int
  var dc : int
  var rs : bitstring{p}
  var hs : bitstring{p}
  var ts : bitstring{p}
  var ss : bitstring{ku}
  var bad : bool
  var gs : bitstring{ku}
  var bad1 : bool
  var bad2 : bool
  var bad3 : bool
  fun G (x : bitstring{p}) : bitstring{ku} = {
    var g : bitstring{ku};
    g = {0,1}^ku;
    if (!in_dom (x,Gm))
    { 
        Gm[x] = g;
        bad = bad || x = rs;
    }
    
    return Gm[x];
  }
  fun G_A (x : bitstring{p}) : bitstring{ku} = {
    var kp : bitstring{ku};
    if (gc < qG)
    { 
        kp = G (x);
        gc = gc + 1;
    }
    else
    { 
        kp = bs0_ku;
    }
    return kp;
  }
  fun H (x : bitstring{ku}) : bitstring{p} = {
    var h : bitstring{p};
    h = {0,1}^p;
    if (!in_dom (x,Hm))
    { 
        Hm[x] = h;
    }
    
    return Hm[x];
  }
  fun H_A (x : bitstring{ku}) : bitstring{p} = {
    var _p : bitstring{p};
    if (hc < qH)
    { 
        _p = H (x);
        hc = hc + 1;
    }
    else
    { 
        _p = bs0_p;
    }
    return _p;
  }
  fun D (x : cipher) : bitstring{u} = {
    var g_0 : bitstring{ku};
    var s : bitstring{ku};
    var h_0 : bitstring{p};
    var t : bitstring{p};
    var r : bitstring{p};
    var result : bitstring{u};
    var g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    s = high_bits_k (finv (sks,x));
    t = low_bits_k (finv (sks,x));
    g_0_h = {0,1}^u;
    g_0_l = {0,1}^k1;
    g_0 = g_0_h || g_0_l;
    result = bs0_u;
    if (length (map_to_list (Gm)) < qD + qG)
    {
    
      if (in_dom (s,Hm))
      {
      
        r = t ^^ Hm[s];
        if (mem (r,map_to_list (Gm)))
        {
        
          g_0 = Gm[r];
          if (low_bits_ku (s ^^ g_0) = bs0_k1)
          { 
              result = high_bits_ku (s ^^ g_0);
          }
          
        }
        else
        {
        
          Gm[r] = g_0;
          if (r = rs)
          { 
              bad = true;
          }
          
          if (low_bits_ku (s) = g_0_l)
          { 
              bad1 = true;
          }
          
        }
      }
      else
      {
      
        r = {0,1}^p;
        Hm[s] = r;
        if (mem (r,map_to_list (Gm)))
        { 
            bad2 = true;
        }
        else
        {
        
          if (r = rs)
          { 
              bad3 = true;
          }
          
          Gm[r] = g_0;
          if (low_bits_ku (s) = g_0_l)
          { 
              bad1 = true;
          }
          
        }
      }
    }
    
    return result;
  }
  fun D_A1 (x : cipher) : bitstring{u} = {
    var g_0 : bitstring{ku};
    var s : bitstring{ku};
    var h_0 : bitstring{p};
    var t : bitstring{p};
    var r : bitstring{p};
    var result : bitstring{u};
    var g_0_h : bitstring{u};
    var g_0_l : bitstring{k1};
    var _u : bitstring{u};
    if (dc < qD)
    {
    
      s = high_bits_k (finv (sks,x));
      t = low_bits_k (finv (sks,x));
      g_0_h = {0,1}^u;
      g_0_l = {0,1}^k1;
      g_0 = g_0_h || g_0_l;
      result = bs0_u;
      if (length (map_to_list (Gm)) < qD + qG)
      {
      
        if (in_dom (s,Hm))
        {
        
          r = t ^^ Hm[s];
          if (mem (r,map_to_list (Gm)))
          {
          
            g_0 = Gm[r];
            if (low_bits_ku (s ^^ g_0) = bs0_k1)
            { 
                result = high_bits_ku (s ^^ g_0);
            }
            
          }
          else
          {
          
            Gm[r] = g_0;
            if (r = rs)
            { 
                bad = true;
            }
            
            if (low_bits_ku (s) = g_0_l)
            { 
                bad1 = true;
            }
            
          }
        }
        else
        {
        
          r = {0,1}^p;
          Hm[s] = r;
          if (mem (r,map_to_list (Gm)))
          { 
              bad2 = true;
          }
          else
          {
          
            if (r = rs)
            { 
                bad3 = true;
            }
            
            Gm[r] = g_0;
            if (low_bits_ku (s) = g_0_l)
            { 
                bad1 = true;
            }
            
          }
        }
      }
      
      dc = dc + 1;
    }
    else
    { 
        result = bs0_u;
    }
    _u = result;
    return _u;
  }
  fun D_A2 (x : cipher) : bitstring{u} = {
    var _u : bitstring{u};
    if (x <> cs)
    { 
        _u = D_A1 (x);
    }
    else
    { 
        _u = bs0_u;
    }
    return _u;
  }
  fun KG () : key = {
    var x : key;
    x = kg ();
    return x;
  }
  fun Enc (pk : pkey, m : message) : cipher = {
    var g : bitstring{ku};
    var s : bitstring{ku};
    var r : bitstring{p};
    var h : bitstring{p};
    var t : bitstring{p};
    r = {0,1}^p;
    g = G (r);
    s = g ^^ (m || bs0_k1);
    h = H (s);
    t = h ^^ r;
    return f (pk,s || t);
  }
  abs A1 = A1{G_A, H_A, D_A1}
  abs A2 = A2{G_A, H_A, D_A2}
  fun Main () : bool = {
    var b : bool;
    var b' : bool;
    var m0 : message;
    var m1 : message;
    var g : bitstring{ku};
    var s : bitstring{ku};
    var r : bitstring{p};
    var h : bitstring{p};
    var t : bitstring{p};
    cs = bs0_k;
    gc = 0;
    hc = 0;
    dc = 0;
    Gm = empty_map;
    Hm = empty_map;
    bad = false;
    bad1 = false;
    bad2 = false;
    bad3 = false;
    (pks, sks) = KG ();
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








(*claim Pr_Gtmp_bad1 : 
  Gtmp.Main[bad1 && dc <= qD] <= qD%r * (1%r / (2^k1)%r) 
  compute 10 (bad1), (dc).
*)


(** 
  * Changement des bornes 0 < qG; 0 < qD ====> 0 <= qG; 0 <= qD
  * Car il n'existe pas de Rplus_lt_lt_0_compat, c'était donc pour pouvoir
  * utiliser Rplus_le_le_0_compat.
  
  * ====> Ne passe toujours pas ( penser à remettre 0 < (qG, qD) ).
*)

(*
lemma totoqsd : 
  forall(x, y, z : int, w : real), 
    (0 <= x) => (x < y) => (0 < z) => w <= (x%r / z%r) => w <= (y%r / z%r).
*)
(*
unset all.
set pow2_pos, qD_pos, qG_pos, p_pos, totoqsd.
print axiom.
*)
(*lemma lqs : 
  forall(M : bitstring{p} list) [M],
    0 <= length((M)). *)
(*
lemma totoqsd2 : 
  forall(M : bitstring{p} list, w: real),
     (0 <= length(M)) => 
     (length(M) < (qD + qG)) => 
     w <= (length(M))%r / (2^p)%r => 
     w <= ((qD + qG)%r / (2^p)%r).

unset all.
set totoqsd2.

check map_to_list. *)
(*lemma tototest : 
  forall(M : t_Gm, w : real),
     (length(map_to_list(M)) < (qD + qG)) => 
     w <= (length(map_to_list(M)))%r / (2^p)%r => 
     w <= ((qD + qG)%r / (2^p)%r). *)

claim Pr_Gtmp_bad2 : 
  Gtmp.Main[bad2 && dc <= qD] <= qD%r * ((qD + qG)%r / (2^p)%r) 
  compute 10 (bad2), (dc).
