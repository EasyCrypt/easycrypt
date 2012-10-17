
(** ******************************************* *)
(**         Description of the Proof            *)
(**                                             *)
(**                  TODO                       *)
(**                                             *)
(** ******************************************* *)
checkproof.
(** ******************************************* *)
(**                Constant                     *)
(** ******************************************* *)
cnst k0 : int.
cnst k1 : int.
cnst k  : int = k1 + k0.

(** ******************************************* *)
(**             Usefull types                   *)
(** ******************************************* *)

(* TODO : Choose e in : 1 < e < phi(N) *)
type pkey    = int * int.
type skey    = int.
type key     = (int * int * skey).
type message = bitstring{k}.
type cipher  = bitstring{k}.

(** ******************************************* *)
(**           Operator for Triplet              *)
(** ******************************************* *)
op fst_bis : ('a * 'b * 'c) -> 'a.
op snd_bis : ('a * 'b * 'c) -> 'b.
op thd_bis : ('a * 'b * 'c) -> 'c.

axiom fst_spec :
  forall(a : 'a, b : 'b, c : 'c),
    let triplet = (a, b, c)  in 
    fst_bis(triplet) = a.

axiom snd_spec :
  forall(a : 'a, b : 'b, c : 'c),
    let triplet = (a, b, c)  in 
    snd_bis(triplet) = b.

axiom thd_spec :
  forall(a : 'a, b : 'b, c : 'c),
    let triplet = (a, b, c)  in 
    thd_bis(triplet) = c.

(** ******************************************* *)
(**               Valid_keys                    *)
(** ******************************************* *)
pop kg      : () -> key.
op  valid_keys : (int, int, int) -> bool.

axiom validkeys_spec() :
  x=kg() ~ y=kg() :
  true ==> x=y && valid_keys(fst_bis(x), snd_bis(x), thd_bis(x)).

(** ******************************************* *)
(**       Convertor between int and bits        *)
(** ******************************************* *)
op int_to_bsk  : int -> bitstring{k}.
op bsk_to_int  : bitstring{k} -> int.
op int_to_bsk0 : int -> bitstring{k0}.
op bsk0_to_int : bitstring{k0} -> int.
op int_to_bsk1 : int -> bitstring{k1}.
op bsk1_to_int : bitstring{k1} -> int.

axiom tobsk_toint :
  forall(bs : bitstring{k}),
    int_to_bsk(bsk_to_int(bs)) = bs.

axiom toint_tobsk:
  forall(i : int),
    bsk_to_int(int_to_bsk(i)) = i % 2^k.

axiom tobsk0_toint :
  forall(bs : bitstring{k0}),
    int_to_bsk0(bsk0_to_int(bs)) = bs.

axiom toint_tobsk0:
  forall(i : int),
    bsk0_to_int(int_to_bsk0(i)) = i % 2^k0.

axiom tobsk1_toint :
  forall(bs : bitstring{k1}),
    int_to_bsk1(bsk1_to_int(bs)) = bs.

axiom toint_tobsk1:
  forall(i : int),
    bsk1_to_int(int_to_bsk1(i)) = i % 2^k1.

(** ******************************************* *)
(**         Append between of bitstring         *)
(** ******************************************* *)
op [||] : (bitstring{k1}, bitstring{k0}) -> bitstring{k} as append.

axiom append_spec() :
   a = {0,1}^k1 || {0,1}^k0 ~ b = {0,1}^k : 
   true ==> (a = b).

axiom split_spec() :
  a = {0,1}^k ~ b = {0,1}^k1 || {0,1}^k0 : 
  true ==> (a = b).

(** ******************************************* *)
(**       High_bits / Low_bits Definition       *)
(** ******************************************* *)
op hb : message -> bitstring{k1}.
op lb : message -> bitstring{k0}.

axiom hb_spec :
  forall(m : message),
    hb(m) = int_to_bsk1(bsk_to_int(m) / 2^k0).

axiom lb_spec :
  forall(m : message),
    lb(m) = int_to_bsk0(bsk_to_int(m) / 2^k1).

axiom bit_spec : 
  forall(m : message),
    m = (hb(m) || lb(m)).

(** ******************************************* *)
(**         Definition of adversaries           *)
(**                                             *)
(**   There are two adversaries :               *)
(**     # A : which break partial-domain RSA    *)
(**     # I : which break RSA by using A        *)
(**                                             *)
(**     The first recovers some of the most     *)
(**   significant bits of an encrypted message  *)
(**     The second recovers all bits from the   *)
(**   original message.                         *)
(** ******************************************* *)
adversary A(pk : pkey, c : cipher) : bitstring{k1} {}.

(** ******************************************* *)
(**                 Operator                    *)
(** ******************************************* *)
op is_good : (int, int) -> bool.
op lemma_3 : (int, int, int) -> bitstring{k0} * bitstring{k0}.

axiom lemma_3_spec :
  forall(a, N, c : int, t, u : bitstring{k0}),
    is_good(a, N) => lemma_3(N, a, c) = (t, u) <=>
    let T = bsk0_to_int(t) in
    let U = bsk0_to_int(u) in
    ((((T + a * U) % N) = (c % N)) && 
    0 <= T && T < 2^k0 && 0 <= U && U < 2^k0).

axiom unicity :
  forall(a, N, c : int, t, u : bitstring{k0}),
    let T = bsk0_to_int(t) in
    let U = bsk0_to_int(u) in
    is_good(a, N) => ((T + a * U) % N) = (c % N) => 
    (0 <= T && T < 2^k0) => (0 <= U && U < 2^k0) => 
    lemma_3(N, a, c) = (t, u).

(** ******************************************* *)
(**        Definition of the game RSA           *)
(** ******************************************* *)
game RSA = {
  var Ns, es, alpha : int
  var sks : skey
  var cs1, cs2, cis : cipher
  var ms, ms_alpha : message
  var xs, ys : bitstring{k1}
  var rs : bitstring{k0}

  fun Enc(N, e : int, m : message) : cipher = {
    var c : cipher;
    c = int_to_bsk(bsk_to_int(m)^e % N);
    return c;
  }

  fun KG() : int * int * int = {
    var sk : skey;
    var N, e : int;
    (N, e, sk) = kg();
    return (N, e, sk);
  }

  abs A = A{}

  fun I (N, e, a : int, c1, c2 : cipher) : message = {
    var s : bitstring{k0};
    var res : message;
    var p : int;
    xs = bs0_k1; ys = bs0_k1; rs = bs0_k0; res = bs0_k;
    xs = A((N, e), c1);
    ys = A((N, e), c2);
    p = ((bsk1_to_int(ys) - bsk1_to_int(xs) * a) * 2^k0) % N;
    (rs, s) = lemma_3(N, a, p);
    res = (xs || rs);
    return res;
  }

  fun Main() : bool = {
    var key : key;
    xs = bs0_k1; ys = bs0_k1; rs = bs0_k0; cis = bs0_k;
    key = kg();
    (Ns, es, sks) = key;
    alpha = [1..Ns-1];
    ms = {0,1}^k;
    ms_alpha = int_to_bsk(bsk_to_int(ms) * alpha);
    cs1 = Enc(Ns, es, ms);
    cs2 = Enc(Ns, es, ms_alpha);
    cis = I(Ns, es, alpha, cs1, cs2);    
    return ms = cis;
  }
}.
 
(** ******************************************* *)
(**        Definition of the game RSA'          *)
(**                                             *)
(**     Same as the game RSA except that we     *)
(**   inline the Inverter I and transfer some   *)
(**   variables as global variables.            *)
(** ******************************************* *)

game RSA' = {
  var Ns, es, alpha : int
  var sks : skey
  var cs1, cs2, cis : cipher
  var ms, ms_alpha : message
  var xs, ys : bitstring{k1}
  var rs : bitstring{k0}

  fun Enc(N, e : int, m : message) : cipher = {
    var c : cipher;
    c = int_to_bsk(bsk_to_int(m)^e % N);
    return c;
  }

  fun KG() : int * int * int = {
    var sk : skey;
    var N, e : int;
    (N, e, sk) = kg();
    return (N, e, sk);
  }

  abs A = A{}

  fun Main() : bool = {
    var s : bitstring{k0};
    var key : key;
    var p : int;
    xs = bs0_k1; ys = bs0_k1; rs = bs0_k0; cis = bs0_k;
    key = kg();
    (Ns, es, sks) = key;
    alpha = [1..(Ns-1)];
    ms = {0,1}^k;
    ms_alpha = int_to_bsk(bsk_to_int(ms) * alpha);
    cs1 = Enc(Ns, es, ms);
    cs2 = Enc(Ns, es, ms_alpha);
    xs = A((Ns, es), cs1);
    ys = A((Ns, es), cs2);
    p = ((bsk1_to_int(ys) - bsk1_to_int(xs) * alpha) * 2^k0) % Ns;
    (rs, s) = lemma_3(Ns, alpha, p);
    cis = (xs || rs);
    return ms = cis;
  }
}.
checkproof.
(* Montrer que rs = lb(ms) *)
equiv RSA_RSA' : RSA.Main ~ RSA'.Main : 
  true ==>  (xs = hb(ms) &&
            ys = hb(ms_alpha) &&
            is_good(alpha, Ns)){2} => res{1}.
inline; wp.
(* auto (={alpha, Ns, es, sks, xs, ys, ms, ms_alpha, cs1, cs2, cis, rs} &&
      rs{1} = lb(ms){1}). 
*)
auto (={alpha, Ns, es, sks, xs, ys, ms, ms_alpha, cs1, cs2, cis}).
trivial.
axiom q :
  forall(m1, m2 : message, a : int, k : key),
    let N, e, sk = k in
    let p = (bsk1_to_int(hb(m1)) - bsk1_to_int(hb(m2)) * a) * 2^k0 % N in
    fst(lemma_3(N, a, p)) = lb(m1).
trivial.

trivial.


(* Ne change rien. Juste pour garder en tete que le lemme passe
lemma t :
  forall(m : message),
  exists(X : bitstring{k0}),
  m = (hb(m) || X) => X = lb(m).
*)

(*  Sans doute useless
axiom u :
  forall(m1, m2 : message, a : int, k : key),
    exists(X, Y : bitstring{k0}), 
    let N, e, sk = k in
    let hbEnc_m1 = bsk1_to_int(hb(m1))^e % N in
    let lbEnc_m1 = bsk0_to_int(X)^e % N in
    let hbEnc_am2 = (bsk1_to_int(hb(m1)) * a)^e % N in
    let lbEnc_am2 = (bsk0_to_int(Y) * a)^e % N in
    let c1 = hbEnc_m1 * 2^k1 + lbEnc_m1 in
    let ac2 = hbEnc_am2 * 2^k1 + lbEnc_am2 in
      c1 = ac2 <=>
      hbEnc_m1 * 2^k1 + lbEnc_m1 = hbEnc_am2 * 2^k1 + lbEnc_am2 <=>
      hbEnc_m1 * 2^k1 - hbEnc_am2 * 2^k1 = lbEnc_am2 - lbEnc_m1 <=>

      let C = hbEnc_m1 * 2^k1 - hbEnc_am2 * 2^k1 in
      lbEnc_am2 - lbEnc_m1 = C => is_good(a, N) =>
      let t, u = lemma_3(N, a, C) in
      t = Y && u = X =>
      lb(m1) = X && lb(m2) = Y .
*) 

axiom a : 
  forall(m1, m2 : message, a : int, k : key),
    let N, e, sk = k in
    let am2 = bsk_to_int(int_to_bsk(m2) * a) in
    let hbm1 = high_bits_k(m1) in
    let hbm2 = high_bits_k(am2) in
    let aY = int_to_bsk(bsk_to_int(Y) * a) in
    m1 = am2 => 
    (high_bits_k(m1) || X) = 
    (high_bits_k(am2) || int_to_bsk(bsk_to_int(Y) * a)) =>
    



    m1 = int_to_bsk(bsk_to_int(m2) * a) =>
    let p = (bsk1_to_int(hb(m1)) - bsk1_to_int(hb(m2)) * a) * 2^k0 % N in
      is_good(a, N) =>
      lemma_3(N, a, p) = (lb(m1), lb(m2)) => m1 = (hb(m1) || lb(m1)).
trivial.
      
admit.
save.

claim Pr_RSA'_RSA : 
  RSA'.Main[xs = hb(ms) &&
            ys = hb(ms_alpha) &&
            is_good(alpha, Ns)] <= RSA.Main[res] using RSA_RSA'.

claim Pr_RSA_alpha :
  RSA'.Main[is_good(alpha, Ns)] = (2^(2 * k0 - k + 6))%r admit.

claim Pr_RSA'_split :
  RSA'.Main[xs = hb(ms) &&
            ys = hb(ms_alpha) &&
            is_good(alpha, Ns)] <= 
  RSA'.Main[xs = hb(ms)] *
  (RSA'.Main[ys = hb(ms_alpha)] -
  (2^(2 * k0 - k + 6))%r) admit.


(** ******************************************* *)
(**        Definition of the game Gspow         *)
(** ******************************************* *)
game Gpdow = {
  var Ns, es : int
  var sks : skey
  var cs : cipher
  var ms : message
  var xs : bitstring{k1}
  var rs : bitstring{k0}

  fun Enc(N,e : int, m : message) : cipher = {
    var c : cipher;
    c = int_to_bsk(bsk_to_int(m)^e % N);
    return c;
  }

  fun KG() : int * int * int = {
    var sk : skey;
    var N, e : int;
    (N, e, sk) = kg();
    return (N, e, sk);
  }

  abs A = A{}

  fun Main() : bool = {
    var key : key;
    xs = bs0_k1;
    key = kg();
    (Ns, es, sks) = key;
    ms = {0,1}^k;
    cs  = Enc(Ns, es, ms);
    xs = A((Ns, es), cs);    
    return hb(ms) = xs;
  }
}.

(** ******************************************* *)
(**         Equivalence for event X_OK          *)
(** ******************************************* *)
equiv RSA'_Gpdow_XOK : RSA'.Main ~ Gpdow.Main : true ==> 
  (xs = hb(ms)){1} <=> res{2}.
inline.
app 19 9 (={xs, Ns, es, sks, ms} &&
  (cs1 = int_to_bsk(bsk_to_int(ms)^es % Ns)){1} &&
  cs1{1} = cs{2}).
trivial.
swap{1} 1.
wp; auto (={xs, Ns, es, sks, ms}).
simpl.
save.

claim Pr_RSA'_Gpdow_XOK : 
  RSA'.Main[xs = hb(ms)] = Gpdow.Main[res]
  using RSA'_Gpdow_XOK.

(** ******************************************* *)
(**         Equivalence for event Y_OK          *)
(**                                             *)   
(**  *  Modification of alpha : [1 .. N-1] to   *)
(**     avoid null division in the rnd tactic.  *)
(** ******************************************* *)
checkproof.

axiom div_assoc : 
  forall(a, b, c : int),
    c <> 0 =>
    (a * b) / c = a * (b / c).

equiv RSA'_Gpdow_YOK : RSA'.Main ~ Gpdow.Main : true ==> 
  (ys = hb(ms_alpha)){1} <=> res{2}.
inline.
app 19 9 (={Ns, es, sks} &&
    cs2{1} = int_to_bsk(bsk_to_int(ms_alpha)^es % Ns){1} &&
    cs2{1} = cs{2} &&
    ms{2} = ms_alpha{1}).
wp.
rnd (int_to_bsk(bsk_to_int(ms{2}) * alpha{1})),
    (int_to_bsk(bsk_to_int(ms{2}) * 1 / alpha{1})).
trivial.
wp; auto (={Ns, es, sks}).
simpl. 
save.

claim Pr_RSA'_Gpdow_YOK : 
  RSA'.Main[ys = hb(ms_alpha)] = Gpdow.Main[res]
  using RSA'_Gpdow_YOK.

claim Conclusion :
  RSA'.Main[xs = hb(ms)] * 
  (RSA'.Main[ys = hb(ms_alpha)] -
  (2^(2 * k0 - k + 6))%r) <= 
  Gpdow.Main[res] * (Gpdow.Main[res] - (2^(2 * k0 - k + 6))%r).
