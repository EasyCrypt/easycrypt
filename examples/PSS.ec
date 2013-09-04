require import Fun.
require import Int.
require import Real.
require import FSet.
require import Map.
require import Pair.
require import Distr.

(*** General definitions *)
(** Lengths *)
op k:int.
axiom lt0_k: 0 < k.

op k0:int.
axiom lt0_k0: 0 < k0.

op k1:int.
axiom lt0_k1: 0 < k1.

axiom constraints:
  k0 + k1 < k - 1.

op kg:int = k - k1 - 1.
lemma lt0_kg1: 0 < kg by [].

op kg2:int = k - k0 - k1 - 1.
lemma lt0_kg2: 0 < kg2 by [].

op k':int = k - 1.
lemma lt0_k': 0 < k' by [].

op qS:int.
axiom leq0_qS: 0 <= qS.

op qH:int.
axiom leq0_qH: 0 <= qH.

op qG:int.
axiom leq0_qG: 0 <= qG.

(** Types *)
require AWord.
require import ABitstring.

type message = bitstring.

(* Signatures *)
type signature.
clone import AWord as Signature with
  type word <- signature,
  op length <- k.

(* Nonce *)
type salt.
clone import AWord as Salt with
  type word <- salt,
  op length <- k0.
op sample_salt = Salt.Dword.dword.
axiom saltL: mu sample_salt cpTrue = 1%r.

(* Output of H *)
type htag.
clone import AWord as HTag with
  type word <- htag,
  op length <- k1.
op sample_htag = HTag.Dword.dword.
axiom htagL: mu sample_htag cpTrue = 1%r.

(* Output of G *)
type gtag.
clone import AWord as GTag with
  type word <- gtag,
  op length = kg.
op sample_gtag = GTag.Dword.dword.
axiom gtagL: mu sample_gtag cpTrue = 1%r.

(* Output of G2 [G1 produces an HTag] *)
type g2tag.
clone import AWord as G2Tag with
  type word <- g2tag,
  op length = kg2.

(* Domain of RSA *)
op sample_plain: signature distr.
axiom plainL: mu sample_plain cpTrue = 1%r.

(** Instantiating *)
require PKS.
require OW.
require RandomOracle.

clone import OW as RSA with
  type t <- signature,
  op sample_t <- sample_plain,
  op f_dom = (lambda (pk:pkey) (x:signature), true),
  op f_rng = (lambda (pk:pkey) (x:signature), true),
  op finv_dom = (lambda (sk:skey) (x:signature), true),
  op finv_rng = (lambda (sk:skey) (x:signature), true)
  proof f_rng_sub_finv_dom by smt,
        finv_rng_sub_f_dom by smt,
        f_dom_sample_t by smt.

op ( * ): signature -> signature -> pkey -> signature.
axiom homo_f_mul (x y:signature) pk: f pk ((x * y) pk) = (f pk x * f pk y) pk.

op modulus_p: pkey -> int.
axiom modulus_size pk sk:
  in_supp (pk,sk) keypairs =>
  2^(k-1) <= modulus_p pk < 2^k.

clone import RandomOracle as Gt with
  type from <- htag,
  type to <- gtag,
  op dsample <- sample_gtag.
module G = Gt.ROM.RO.

clone import RandomOracle as Ht with
  type from <- (message * salt),
  type to <- htag,
  op dsample <- sample_htag.
module H = Ht.ROM.RO.

clone import PKS as PKSi with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type signature <- signature.
import EF_CMA.

(*** Defining PSS *)
module PSS(G:Gt.Oracle,H:Ht.Oracle): Scheme = {
  fun init(): unit = {
    G.init();
    H.init();
  }

  fun g1(x:htag):salt = {
    var r:gtag;
    r  = G.o(x);
    return Salt.from_bits (sub (to_bits r) 0 k0);
  }

  fun g2(x:htag):g2tag = {
    var r:gtag;
    r  = G.o(x);
    return G2Tag.from_bits (sub (to_bits r) k0 kg2);
  }

  (* Keygen: make it a wrapped pop *)
  fun keygen():(pkey * skey) = {
    var (pk, sk):(pkey * skey);
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  (* Sign *)
  fun sign(sk:skey, m:message):signature = {
    var r:salt;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    r = $sample_salt;
    w  = H.o((m,r));
    rMask  = g1(w);
    maskedR = rMask ^ r;
    gamma  = g2(w);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return (finv sk y); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:message, s:signature):bool = {
    var y:signature;
    var w:htag;
    var w':htag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var b:bool;

    y = (f pk s);
    b = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    rMask  = g1(w);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = g2(w);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

(* A CMA adversary with access to two random oracles *)
module type CMA_2RO(G:Gt.ARO,H:Ht.ARO,S:AdvOracles) = {
  fun forge(pk:pkey): message * signature { * G.o H.o S.sign}
}.

section. 
  declare module A:CMA_2RO {G,H,EF_CMA,Wrap,OW}.
  axiom adversaryL (G <: Gt.ARO{A}) (H <: Ht.ARO{A}) (S <: AdvOracles{A}):
    islossless G.o => islossless H.o => islossless S.sign =>
    islossless A(G,H,S).forge.

  local module Mem = {
    var pk:pkey
    var sk:skey
    var n:int
    var xstar:signature
    var qs:message set

    fun init(ks:pkey*skey): unit = {
      (pk,sk) = ks;
      qs = FSet.empty;
      n = modulus_p pk;
      xstar = $sample_plain;
    }
  }.

  module type SplitOracle = {
    fun init(ks:pkey*skey): unit { * }
    fun o(c:bool,x:message * salt):htag
  }.

  (** Since the proof mostly works by modifying H,
      with some eager-style interactions with G,
      we will mostly reason in terms of a concrete
      adversary trying to distinguish various
      implementations of G and H through the signing
      oracle. This should allow some abstraction in the
      proof, and in particular in the two eager steps
      on G.
  **)
  module type Gadv (H:SplitOracle, G:Gt.Oracle) = { 
    fun main (ks:pkey * skey) : bool { * G.o H.o }
  }.

  local module Gen (Gadv:Gadv, H:SplitOracle, G:Gt.Oracle) = {
    module GA = Gadv(H,G)
    fun main () : bool = { 
      var keys : pkey * skey;
      var b : bool;
      keys = $keypairs;
      G.init();
      H.init(keys);
      b = GA.main(keys);
      return b;
    }
  }.

  local module GAdv(H:SplitOracle, G:Gt.Oracle) = {

    module Hs = {
      fun o(x:message * salt): htag = {
        var r:htag;
        r = H.o(false,x);
        return r;
      }
    }

    module Ha = {
      fun o(x:message * salt): htag = {
        var r:htag;
        r = H.o(true,x);
        return r;
      }
    }

    module S = {
 
      fun sign(m:message): signature = {
        var r:salt;
        var g:gtag;
        var rMask:salt;
        var maskedR:salt;
        var w:htag;
        var gamma:g2tag;
        var y:signature;

        Mem.qs = add m Mem.qs;
        r = $sample_salt;
        w  = Hs.o((m,r));
        g = G.o(w);
        rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
        maskedR = rMask ^ r;
        gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
        y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
        return finv Mem.sk y;
      } 

      fun fresh(m:message): bool = {
        return !mem m Mem.qs;
      }
    }

    module A = A(G, Ha, S)

    fun main (ks:pkey*skey) : bool = { 
      var m:message;
      var s:signature;
      var y:signature;
      var w:htag;
      var w':htag;
      var g:gtag;
      var maskedR:salt;
      var gamma:g2tag;
      var gamma':g2tag;
      var rMask:salt;
      var r:salt;
      var forged, fresh:bool;

      Mem.init(ks);
      (m,s) = A.forge(Mem.pk);

      y = (f Mem.pk s);
      forged = (sub (to_bits y) 0 1 <> zeros 1);
      w = HTag.from_bits (sub (to_bits y) 1 k1);
      maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
      gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
      g = G.o(w);
      rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
      r = rMask ^ maskedR;
      w'  = Hs.o((m,r));
      gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
      forged =  w = w' /\ gamma = gamma' /\ !forged;

      fresh = S.fresh(m);
      return forged /\ fresh;
    }
  }.

  local lemma lossless_GAdv (H <: SplitOracle{GAdv}) (G <: Gt.Oracle{GAdv}):
    islossless G.o => islossless H.o =>
    islossless GAdv(H, G).main.
  proof strict.
  intros=> GL HL; fun.
  call (_: true ==> true); first by fun.
  wp; call (_: true ==> true); first by fun; call HL.
  wp; call GL.
  wp; call (adversaryL G (<: GAdv(H,G).Ha) (<: GAdv(H,G).S) _ _ _)=> //.
    by fun; call HL.
    fun; wp.
      call GL.
      call (_: true ==> true); first by fun; call HL.
      by rnd; wp; skip; smt.
    by call (_: true ==> true);
      first by fun; rnd; wp; skip; smt.
  qed.

  (** First Transition:
      We rewrite PSS into an adversary against Gen with G and a trivial split oracle H0. *)
  local module H0 : SplitOracle = { 
    fun init(ks:pkey*skey): unit = {
      H.init();
    }
   
    fun o(c:bool,x:message * salt):htag = { 
      var r : htag;
      r = H.o(x);
      return r;
    }
  }.

  local module G0 = Gen(GAdv,H0,G).

  local equiv PSS_G0:
    EF_CMA(Wrap(PSS(G,H)),A(G,H)).main ~ G0.main: ={glob A} ==> ={res}.
  proof strict.
  fun.
  inline G0.main Gen(GAdv,H0,Gt.ROM.RO).GA.main; wp.
  call (_: ={m} /\ Wrap.qs{1} = Mem.qs{2} ==> ={res});
    first by fun; eqobs_in.
  inline Wrap(PSS(Gt.ROM.RO,ROM.RO)).verify PSS(Gt.ROM.RO,ROM.RO).verify
         PSS(Gt.ROM.RO,ROM.RO).g1 PSS(Gt.ROM.RO,ROM.RO).g2.
  swap{1} [18..19] -3. (* Grouping the two calls to G on the left *)
  wp; call (_: ={glob H});
        first by inline H0.o H.o; wp; rnd; wp; skip; smt.
  (* We use seq to cut out the calls to G and limit the scope of the rcond call *)
  wp; seq 12 11: (={glob G, glob H, w, m, maskedR, gamma} /\
                  Wrap.qs{1} = Mem.qs{2} /\
                  b0{1} = forged{2} /\
                  m1{1} = m{2}).
    eqobs_in; inline Wrap(PSS(Gt.ROM.RO,ROM.RO)).init PSS(Gt.ROM.RO,ROM.RO).init
                     ROM.RO.init Gt.ROM.RO.init PSS(Gt.ROM.RO,ROM.RO).keygen
                     H0.init H.init Mem.init.
    call (_: ={glob G, glob H} /\ Wrap.qs{1} = Mem.qs{2} /\ Wrap.sk{1} = Mem.sk{2}).
     fun;eqobs_in.
     fun;inline H0.o H.o. wp 2 5;eqobs_in.
     fun. inline PSS(Gt.ROM.RO, ROM.RO).sign.
       wp 9 8.
       inline PSS(Gt.ROM.RO, ROM.RO).g1 PSS(Gt.ROM.RO, ROM.RO).g2 GAdv(H0, Gt.ROM.RO).Hs.o. 
       eqobs_in. 
       inline Gt.ROM.RO.o.
       seq 12 11 : (proj Gt.ROM.RO.m.[w]{1} = g{2} /\ ={w, maskedR, ROM.RO.m, Gt.ROM.RO.m} /\ sk{1} = Mem.sk{2} /\
                  Wrap.sk{1} = Mem.sk{2} /\ Wrap.qs{1} = Mem.qs{2} /\ (in_dom w Gt.ROM.RO.m){1}).
          wp;rnd;wp;call (_: ={x, glob H} ==> ={res, glob H}).
            fun;inline H.o. wp 2 3;eqobs_in.
          wp;rnd;wp;skip;progress => //;smt.
       wp;rnd{1};wp;skip;progress => //;smt.
    rnd{2}; wp; rnd; wp;
              skip; progress=> //; smt.
    inline Gt.ROM.RO.o; rcondf{1} 9.
      by intros=> &m //=; rnd; wp; rnd; wp; skip; progress=> //; smt.
      by wp; rnd{1}; wp; rnd; wp; skip; progress=> //; smt.
  qed.        

  (** Second Transition:
      The random oracle H is made to loop and sample a bit
      following the distribution of the strong bit of integers
      less than the modulus. *)
  (** H Oracle for G1 *)
  op bool_nu: int -> bool distr.
  
  axiom mu_bool_nu N p:
    2^(k - 1) <= N < 2^k =>
     mu (bool_nu N) p =
     (N%r - (2^(k-1))%r) / N%r * charfun p true + ((2^(k - 1))%r / N%r) * charfun p false.

  local module K = { 
    var pk:pkey
    var sk:skey
    var n :int
    
    fun init(ks:pkey*skey) : unit = { 
      (pk,sk) = ks;
      n = modulus_p pk;
    }   
  }.

  local module H1: SplitOracle = {
    var bad:bool
    
    fun init(ks:pkey*skey): unit = {
      K.init(ks);
      H.init();
      bad = false;
    }

    fun o(c:bool, x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      w = $sample_htag;
      if (!in_dom x H.m) {
        H.m.[x] = HTag.zeros;
        while (i < kg2 && b) {
          b = $bool_nu K.n;
          i = i + 1;
          if (!b) H.m.[x] = w;
        }
      }
      bad = bad \/ b;
      return proj H.m.[x];
    }
  }.

  local module G1 = Gen(GAdv,H1,G).

  local equiv G0_G1_H: H0.o ~ H1.o:
    !H1.bad{2} /\ ={glob H, x} /\ 2^(k - 1) <= K.n{2} < 2^k ==>
    !H1.bad{2} => ={glob H, res} /\ 2^(k - 1) <= K.n{2} < 2^k.
  proof strict.
  fun; inline H.o; case (in_dom x H.m){1}.
    (* in_dom x H.m *)
    rcondf{1} 3; [ | rcondf{2} 4]; first 2 by intros &m; rnd; wp.
    by wp; rnd; wp.

    (* !in_dom x H.m *)
    rcondt{1} 3; [ | rcondt{2} 4]; first 2 by intros &m; rnd; wp.
    wp; while{2} (i <= kg2 /\ eq_except H.m{1} H.m x /\
                  (!b => H.m.[x] = Some w{2}) /\ 2^(k - 1) <= K.n < 2^k){2} (kg2 - i){2}.
      intros=> &m z; wp; rnd (cpTrue); skip; progress=> //; last 6 smt.
        by rewrite mu_bool_nu // /charfun /cpTrue //=; smt.
    by wp; rnd; wp; skip; progress=> //; smt.
  qed.

  lemma Glossless : islossless Gt.ROM.RO.o.
  proof. apply Gt.ROM.lossless_o;smt. qed.

  local equiv G0_G1: G0.main ~ G1.main: true ==> !H1.bad{2} => ={res}.
  proof strict.
    apply ((_ : (forall (Ga<:Gadv{H0,H1,G,K}), 
      (forall (H <: SplitOracle{Ga}) (G <: Gt.Oracle{Ga}),
         islossless G.o => islossless H.o => islossless Ga(H, G).main) => 
      equiv [Gen(Ga,H0,G).main ~ Gen(Ga,H1,G).main : true ==> !H1.bad{2} => ={res}])) GAdv).
     intros Ga Hloosless;fun.
     call (_: H1.bad,  (={glob G, glob H} /\ 2^(k - 1) <= K.n{2} < 2^k), (2^(k - 1) <= K.n{2} < 2^k)).
      conseq * (_ : _ ==> ={res, glob G}) => //;fun;eqobs_in.
      intros _ _;conseq * (_: true ==> true) => //;apply Glossless.
      intros _;conseq * (_: true ==> true) => //;apply Glossless.
     conseq * G0_G1_H => //.
      intros &m1 &m2 H r1 r2 x1 x2 bad;generalize H.
      case bad => //.
     intros _ _;conseq * (_ : true ==> true) => //;fun.
      call (Ht.ROM.lossless_o _) => //;smt.
     intros _;fun.
      wp;conseq * (_ : _ ==> true);first progress => //;smt.  
      wp;seq 3 : (2 ^ (k - 1) <= K.n < 2 ^ k) => //.
      rnd;wp;skip;progress => //;smt.
      if => //.
      while (2 ^ (k - 1) <= K.n < 2 ^ k) (kg2-i).
       intros x;wp. conseq * (_ : _ ==> true); first progress=> //;smt.
       rnd;skip;progress => //. 
      by rewrite mu_bool_nu // /charfun /cpTrue //=; smt.
      wp;skip;progress => //; smt.
      conseq * (_: _ ==> false) => //.
    inline Gt.ROM.RO.init H0.init H1.init H.init K.init.
    wp;rnd;skip;progress => //;smt.
   apply lossless_GAdv.
  qed.

  (** G2 *)
  local module H2 = {
    fun init(ks:pkey*skey): unit = {
      K.init(ks);
      H.init();
    }

    fun o(c:bool, x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      if (!in_dom x H.m) {
        H.m.[x] = htag_dummy;
        while (i < kg2 && b) {
          b = $bool_nu K.n;
          w = $sample_htag;
          i = i + 1;
          if (!b) H.m.[x] = w;
        }
      }
      return proj H.m.[x];
    }
  }.

  local module G2 = Gen(GAdv, H0, G).

  (** G3 *)

  local module H3 = {
    fun init(ks:pkey*skey): unit = {
      K.init(ks);
      H.init();
    }


    fun o (c:bool, x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      if (!in_dom x H.m) {
        H.m.[x] = htag_dummy;
        while (i < kg2 && b) {
          b = $bool_nu K.n;
          w = $sample_htag;
          i = i + 1;
          if (!b) {
            H.m.[x] = w;
            st = G.o(w);
          }
        }
      }
      return proj H.m.[x];
    }
  }.

  local module G3 = Gen(GAdv, H3, G).

  (** G4 *)
  local module H4 = {
    var bad:bool

    fun init(ks:pkey*skey): unit = {
      K.init(ks);
      H.init();
      bad = false;
    }  

    fun o (c:bool, x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      if (!in_dom x H.m) {
        H.m.[x] = htag_dummy;
        while (i < kg2 && b) {
          b = $bool_nu K.n;
          w = $sample_htag;
          st = $sample_gtag;
          i = i + 1;
          if (!b) {
            H.m.[x] = w;
            bad = bad \/ in_dom w G.m;
            G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
          }
        }
      }
      return proj H.m.[x];
    }
  }.

  local module G4 = Gen(GAdv, H4, G).

  (** G5 *)

  local module H5: SplitOracle = {
    var bad:bool
    var m:(message * salt,htag * bool) map

    fun init(ks:pkey*skey): unit = {
      K.init(ks);
      m = Map.empty;
      bad = false;
    }

    fun o(c:bool,x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      if (!in_dom x m) {
        m.[x] = (htag_dummy,c);
        while (i < kg2 && b) {
          b = $bool_nu K.n;
          w = $sample_htag;
          st = $sample_gtag;
          i = i + 1;
          if (!b) {
            m.[x] = (w,c);
            G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
          }
        }
      } else {
        if (!c /\ snd (proj m.[x])) {
          bad = true;
          m.[x] = (HTag.zeros,c);
        }
      }
      return fst (proj m.[x]);
    }
  }.

  local module G5 = Gen(GAdv, H5, G).

(** Proofs *)

  pred eq_proj (m1: ('a,'b) map) (m2: ('a,'b*'c) map) = 
    forall a, in_dom a m1 = in_dom a m2 && 
     (in_dom a m1 => proj (m1.[a]) = fst (proj m2.[a])).

  local lemma equiv_G4_G5_gen (Ga<:Gadv{H4,H5,G,K}) :
      (forall (H6 <: SplitOracle{Ga}) (G6 <: Gt.Oracle{Ga}),
         islossless G6.o => islossless H6.o => islossless Ga(H6, G6).main) => 
      equiv [Gen(Ga,H4,G).main ~ Gen(Ga,H5,G).main : true ==> !H5.bad{2} => ={res}].c
  proof.
   intros Hlossless;fun.
   call (_: H5.bad, 
            eq_proj H.m{1} H5.m{2} /\ ={G.m,K.n} /\ 2^(k - 1) <= K.n{2} < 2^k, 
            ={K.n} /\ 2^(k - 1) <= K.n{2} < 2^k).
   (* G.o *)
   conseq * (_:_ ==> ={res,G.m});first progress => //.
   fun;eqobs_in.
   intros &m2 Hbad;conseq * (Gt.ROM.termination_o 1%r _); apply  gtagL.
   intros &m1;conseq * (Gt.ROM.termination_o 1%r _); apply  gtagL.
   (* H.o *)
   (* equiv *)
   fun.
   seq 2 2 : (!H5.bad{2} /\ eq_proj H.m{1} H5.m{2} /\ ={b,i,c,x,G.m, K.n} /\ 2 ^ (k - 1) <= K.n{2} < 2 ^ k).
     wp => //.
   if. 
     intros => &m1 &m2 [_ [X1 [[ _ [ _ [ _ [-> _ ]]]] _ ]]].
     elim (X1 x{m2}) => -> //.
   while (eq_proj H.m{1} H5.m{2} /\ (in_dom x H5.m){2} /\ !H5.bad{2} /\ ={b,i,x,G.m,K.n}).
     wp; do ? rnd;skip;progress => //.
       intros x';case (x' = x{2}); [intros => -> | intros Hdiff];smt. 
     smt.
   wp;skip;progress => //.
    intros x';case (x' = x{2}); [intros => -> | intros Hdiff];smt.
    smt.
    elim (H6 x{2}) => -> HH;apply HH => //.
   if{2};wp;skip;smt.
   (* lossless 1 *)
   intros &m2 _;conseq * (_ : 2 ^ (k - 1) <= K.n < 2 ^ k ==> true) => //.
     admit. (* should be done for the previous proof *)
   (* lossless 2 *)
   intros &m2;conseq * (_ : H5.bad /\ 2 ^ (k - 1) <= K.n < 2 ^ k ==> H5.bad) => //.
   fun;seq 2 : (i=0 /\ H5.bad /\ 2 ^ (k - 1) <= K.n < 2 ^ k).
     trivial.
     wp;skip;progress => //.
   if.
   while (H5.bad /\ 2 ^ (k - 1) <= K.n < 2 ^ k) (kg2 - i) => //.
     intros z;wp => //=.
     conseq * ( _ : _ ==> true); first progress;smt.
     rnd. conseq (_ : _ ==> true) => //=. apply gtagL.
     rnd. conseq (_ : _ ==> true) => //=. apply htagL.
     rnd cpTrue; skip => //=; progress.
     rewrite mu_bool_nu // /charfun /cpTrue //=; smt.
   wp;skip;progress => //;smt.
   wp;skip => //.
   wp;conseq * ( _ : _ ==> false) => //. 
   intros => //.
   conseq (_ : _ ==> !H5.bad{2} /\ eq_proj H.m{1} H5.m{2} /\ ={G.m, K.n, keys} /\ 2 ^ (k - 1) <= K.n{2} < 2 ^ k).
     smt.
   inline H4.init H5.init Gt.ROM.RO.init K.init H.init;wp;rnd;skip.
   intros &m1 &m2 _ keysL keysR HinL HinR //=;split => [// _].
   cut H := keypair_bounded keysL _ => //; generalize H;progress => //.
   intros x;smt. 
 save.

 local lemma equiv_G4_G5 :
   (forall (G<:Gt.ARO) (H<:Ht.ARO) (S<:AdvOracles), 
     islossless G.o => islossless H.o => islossless S.sign => islossless A(G, H, S).forge) =>
   equiv [Gen(GAdv,H4,G).main ~ Gen(GAdv,H5,G).main : true ==> !H5.bad{2} => ={res}].
 proof.
   intros HLoss;apply (equiv_G4_G5_gen GAdv _).
   apply ( lossless_GAdv _);apply HLoss.
 save.

lemma Bad5 (A <: CMA_2RO) &m:
  Pr[G5(A(G,Ha(H5))).main() @ &m: H5.bad] <= qS%r * (qS + qH)%r/(2^k0)%r.
admit. qed.

(** G6 *)
module H6: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        z = Signature.from_bits (if b then ones 1 else zeros 1 || to_bits w || to_bits st);
        u = if c then (Mem.xstar * finv Mem.sk  z) Mem.pk else finv Mem.sk z;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c) { 
        bad = true;
        m.[x] = (HTag.zeros,c,Signature.zeros);
      }
    }
    return proj H.m.[x];
  }
}.

module G6 = GGen(Hs(H6),SGen(Hs(H6))).

(** G7: No longer using sk to simulate the oracles *)
module H7: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        u = $sample_plain;
        z = if c then (f Mem.pk Mem.xstar * f Mem.pk u) Mem.pk else f Mem.pk u;
        b = (sub (to_bits z) 0 1 = ones 1);
        w = HTag.from_bits (sub (to_bits z) 1 k1);
        st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      bad = true;
      if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
    }
    return (lambda abc, let (a,b,c) = abc in a) (proj m.[x]);
  }
}.

module G7 = GGen(Hs(H7),SGen(Hs(H7))).



















































































(** Proof is up to bad with BAD = (b = true) in final memory *)
lemma equiv_G0_G1 (A <: CMA_2RO):
  equiv [G0(A(G,H)).main ~ G1(A(G,H1)).main: ={glob A} ==> !H1.bad{2} => ={res}].
admit. qed.
    
  module G0 
(** Inlining the oracles that do not need to change *)
module type PartialOracles = {
  fun init(): pkey
  fun sign(m:message): signature
  fun fresh(m:message): bool
}.


module SGen(H:Ht.Oracle): PartialOracles = {
  var pk:pkey
  var sk:skey

  var qs:message set

  fun init(): pkey = {
    G.init();
    H.init();
    qs = FSet.empty;
    (pk,sk) = $keypairs;
    Mem.init(pk,sk);
    return pk;
  }

  fun sign(m:message): signature = {
    var r:salt;
    var g:gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    qs = add m qs;
    r = $sample_salt;
    w  = H.o((m,r));
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return finv sk y;
  } 

  fun fresh(m:message): bool = {
    return !mem m qs;
  }
}.

module GGen(H:Ht.Oracle,O:PartialOracles,A:AdvCMA) = {
  module A = A(O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

module G0 = GGen(H,SGen(H)).

(** H Oracle for G1 *)
op bool_nu: int -> bool distr.
axiom mu_bool_nu N p:
  2^(k - 1) <= N < 2^k =>
  mu (bool_nu N) p =
    ((N%r - (2^(k-1))%r) / N%r) * charfun p true + ((2^(k - 1))%r / N%r) * charfun p false.
lemma bool_nuL N:
  2^(k - 1) <= N < 2^k =>
  mu (bool_nu N) cpTrue = 1%r.
proof.
intros=> bounds; rewrite mu_bool_nu // /charfun /cpTrue /=.
cut ->: forall (a b:real), a / N%r + b / N%r = (a + b) / N%r by smt.
smt.
qed.

module H1: Ht.Oracle = {
  var bad:bool

  fun init(): unit = {
    H.init();
    bad = false;
  }

  fun o(x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    w = $sample_htag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        i = i + 1;
        if (!b)
          H.m.[x] = w;
      }
    }
    bad = bad \/ b;
    return proj H.m.[x];
  }
}.

module G1 = GGen(H1,SGen(H1)).

(** G2 *)
module H2: Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        i = i + 1;
        if (!b)
          H.m.[x] = w;
      }
    }
    return proj H.m.[x];
  }
}.

module G2 = GGen(H2,SGen(H2)).

equiv equiv_G1_G2 (A <: CMA_2RO):
  G1(A(G,H1)).main ~ G2(A(G,H2)).main: ={glob A} ==> ={res}.
admit. 
(** Proof goes by eager (rule for while in figure 3 in the ITP paper) *)
(* We may need to modify H2 so that it samples an initial (useless) value for w *)
(* Swapping statement is "if (b) w = $sample_htag;" *)
qed.

(** G3 *)
module H3: Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o (x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          st = G.o(w);
        }
      }
    }
    return proj H.m.[x];
  }
}.

module G3 = GGen(H3,SGen(H3)).

(** The proof is by two applications of the general eager-lazy transition for G:
      - first, we eagerly sample G,
      - then, we lazily sample it again (with some calls happening in H).        *)
equiv equiv_G2_G3 (A <: CMA_2RO):
  G2(A(G,H2)).main ~ G3(A(G,H3)).main: ={glob A} ==> ={res}.
admit. qed.

(** G4 *)
module H4: Ht.Oracle = {
  var bad:bool

  fun init(): unit = {
    H.init();
    bad = false;
  }

  fun o (x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          bad = bad \/ in_dom w G.m;
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    return proj H.m.[x];
  }
}.

module G4 = GGen(H4,SGen(H4)).

(** Proof is up to failure *)
equiv equiv_G3_G4 (A <: CMA_2RO):
  G3(A(G,H3)).main ~ G4(A(G,H4)).main: ={glob A} ==> !H4.bad{2} => ={res}.
admit. qed.

lemma G3_G4 (A <: CMA_2RO) &m:
  Pr[G3(A(G,H3)).main() @ &m: res] <= Pr[G4(A(G,H4)).main() @ &m: res] + Pr[G4(A(G,H4)).main() @ &m: H4.bad].
proof.
apply (Trans _ Pr[G4(A(G,H4)).main() @ &m: res \/ H4.bad]).
equiv_deno (equiv_G3_G4 A)=> //; smt.
rewrite Pr mu_or; smt.
qed.

(* We will need the invariant that `|dom G.m| <= qG *)
lemma Bad4 (A <: CMA_2RO) &m:
  Pr[G4(A(G,H4)).main() @ &m: H4.bad] <= (qS + qH)%r * (qG + qS + qH)%r/(2^k1)%r.
admit. qed.

(** Splitting the random oracle *)
module type SplitOracle = {
  fun init(): unit
  fun o(c:bool,x:message * salt):htag
}.

module Hs(H:SplitOracle): Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var r:htag;
    r = H.o(false,x);
    return r;
  }
}.

module Ha(H:SplitOracle): Ht.Oracle = {
  fun init(): unit = {
    H.init();
  }

  fun o(x:message * salt): htag = {
    var r:htag;
    r = H.o(true,x);
    return r;
  }
}.

(** G5 *)
module H5: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool) map

  fun init(): unit = {
    bad = false;
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c /\ snd (proj m.[x]))
      {
        bad = true;
        m.[x] = (HTag.zeros,c);
      }
    }
    return fst (proj m.[x]);
  }
}.

module G5 = GGen(Hs(H5),SGen(Hs(H5))).




module H4': SplitOracle' = {
  var bad:bool

  fun init(): pkey * skey = {
    var ks: pkey * skey;
    ks = $keypairs;
    H.init();
    bad = false;
    return ks;
  }

  fun o (c:bool, x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x H.m)
    {
      H.m.[x] = htag_dummy;
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          H.m.[x] = w;
          bad = bad \/ in_dom w G.m;
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    return proj H.m.[x];
  }
}.

module H5': SplitOracle' = {
  var bad:bool
  var m:(message * salt,htag * bool) map

  fun init(): pkey * skey = {
    var ks : pkey * skey;
    ks = $keypairs;
    bad = false;
    m = Map.empty;
    return ks;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    if (!in_dom x m)
    {
      m.[x] = (htag_dummy , c);
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c /\ snd (proj m.[x]))
      {
        bad = true;
        m.[x] = (HTag.zeros,c);
      }
    }
    return fst (proj m.[x]);
  }
}.


(* Remarque pas besoin de A avec les section *)

   

}.


  fun init(): pkey = {
    G.init();
    H.init();
    
    (pk,sk) = $keypairs;
    Mem.init(pk,sk);
    return pk;
  }

module GGen(H:Ht.Oracle,O:PartialOracles,A:AdvCMA) = {
  module A = A(O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o((m,r));
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

pred eq_proj (m1: ('a,'b) map) (m2: ('a,'b*'c) map) = 
 forall a, in_dom a m1 = in_dom a m2 && 
     (in_dom a m1 => proj (m1.[a]) = fst (proj m2.[a])).

equiv equiv_G4_G5_o : H4.o ~ H5.o : 
          !H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) ==>
         !H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={res,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) .
proof.
  fun.
  seq 2 2 : (!H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={b,i,x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G})).
     wp => //.
  if. 
    intros => &m1 &m2 [_ [X1 [ _ [ _ [ -> _ ]]]]].
    elim (X1 x{m2}) => -> //.
  while (eq_proj H.m{1} H5.m{2} /\ !H5.bad{2} /\ ={b,i,x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}).
    wp; do ? rnd;skip;progress => //.
    intros x';case (x' = x{2}); [intros => -> | intros Hdiff];smt.
  skip;progress => //.
    admit. (* We need to allways add a dummy value for x *)
  if{2};wp;skip;smt.
save.
   
equiv equiv_G4_G5 (A <: CMA_2RO{SGen,Gt.ROM.RO, H, H4,H5}):
  G4(A(G,H4)).main ~ G5(A(G,Ha(H5))).main: ={glob A} ==> !H5.bad{2} => ={res}.
proof.
  fun.
  seq 2 2 : (! H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={pk,m,s,glob Gt.ROM.RO,glob A, glob SGen,glob Mem, glob G})).
    call (_: H5.bad,  (eq_proj H.m{1} H5.m{2} /\ ={glob Gt.ROM.RO, glob SGen, glob Mem, glob G}), ={Mem.n}).
    admit.
    (* sign are the same *)
      fun.
      seq 3 3 : (! H5.bad{2} => eq_proj H.m{1} H5.m{2} /\ ={Gt.ROM.RO.m, glob SGen, glob Mem, glob G, r, w}).
        call (_: ! H5.bad{2} /\ (eq_proj H.m{1} H5.m{2} /\ ={x,glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) ==>
               ! H5.bad{2} => (eq_proj H.m{1} H5.m{2} /\ ={res,glob Gt.ROM.RO, glob SGen, glob Mem, glob G})) .
          fun *. inline Hs(H5).o; wp.
          call equiv_G4_G5_o;wp;progress => //.
        rnd;wp;skip;progress => //;smt.
      case H5.bad{2}.
        conseq * ( _ : _ ==> true); first smt.
        wp;inline G.o;wp;rnd;wp;skip => //.
      conseq * ( _ : _ ==> ={y,glob Gt.ROM.RO, glob SGen, glob Mem, glob G} /\ eq_proj H.m{1} H5.m{2});
        first progress => //.
      eqobs_in (={glob Gt.ROM.RO, glob SGen, glob Mem, glob G}) (eq_proj H.m{1} H5.m{2}) : 
                (={y, glob Gt.ROM.RO, glob SGen, glob Mem, glob G});smt.
      admit.
      admit.
    (* H are the same *)
      fun *. inline Ha(H5).o;wp.
      call equiv_G4_G5_o;wp;skip;progress => //;smt.
      admit.
      admit.
    (* G are the same *)
      admit.
      admit.
      admit.
    (* Init *) 
    admit.
  inline SGen(H4).fresh SGen(Hs(H5)).fresh;wp.
  case H5.bad{2}.  
    call (_ : H5.bad{2} ==> H5.bad{2}).
      fun. inline H5.o.
      seq 2 4 : (i{2}=0 /\ i{1}=0 /\ H5.bad{2});[ wp;skip=> // | ].
      transitivity {1} { } (i{1} = 0 ==> true) (i{2} = 0 /\ H5.bad{2} ==> H5.bad{2}) => //.
        if{1}; [ | skip => //].
          while{1} true (kg2 - i{1}).
            intros &m z;wp; conseq * (_:_==> true);first smt.
            do ? (rnd;first smt).
            rnd. admit. (* we need more info on Mem.n, should allow to use mu_bool_nu *)
            skip => //.
        skip => //;smt.
      if{2}.
        wp;while{2} true (kg2 - i{2}).
          intros &m z;wp; conseq * (_:_==> true);first smt.
          do ? (rnd;first smt).
          rnd. admit. (* we need more info on Mem.n, should allow to use mu_bool_nu *)
          skip => //.
        skip => //;smt.
      wp;skip => //.
      conseq (_: _ ==> H5.bad{2}); first smt.
      wp;call (_: true ==> true).
       fun;wp;rnd=> //.
      wp => //.
  inline{2} Hs(H5).o;wp.
  call equiv_G4_G5_o;wp;progress => //.
  eqobs_in (={glob G}) (!H5.bad{2} /\ eq_proj H.m{1} H5.m{2}) : 
       (={m,g,w,gamma,forged, maskedR, glob Gt.ROM.RO, glob SGen, glob Mem, glob G}).
    progress => //.
  elim (H3 _) => //;progress.
  intros &m1 &m2 [H1 H2];elim (H1 _);progress => //.
qed.

lemma Bad5 (A <: CMA_2RO) &m:
  Pr[G5(A(G,Ha(H5))).main() @ &m: H5.bad] <= qS%r * (qS + qH)%r/(2^k0)%r.
admit. qed.

(** G6 *)
module H6: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        b = $bool_nu Mem.n;
        w = $sample_htag;
        st = $sample_gtag;
        z = Signature.from_bits (if b then ones 1 else zeros 1 || to_bits w || to_bits st);
        u = if c then (Mem.xstar * finv Mem.sk  z) Mem.pk else finv Mem.sk z;
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      bad = true;
      if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
    }
    return proj H.m.[x];
  }
}.

module G6 = GGen(Hs(H6),SGen(Hs(H6))).

(** G7: No longer using sk to simulate the oracles *)
module H7: SplitOracle = {
  var bad:bool
  var m:(message * salt,htag * bool * signature) map

  fun init(): unit = {
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
    var b:bool = true;
    var i:int = 0;
    var w:htag;
    var st:gtag;
    var z, u:signature;

    if (!in_dom x H.m)
    {
      while (i < kg2 && b)
      {
        u = $sample_plain;
        z = if c then (f Mem.pk Mem.xstar * f Mem.pk u) Mem.pk else f Mem.pk u;
        b = (sub (to_bits z) 0 1 = ones 1);
        w = HTag.from_bits (sub (to_bits z) 1 k1);
        st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
        i = i + 1;
        if (!b)
        {
          m.[x] = (w,c,u);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      bad = true;
      if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
    }
    return (lambda abc, let (a,b,c) = abc in a) (proj m.[x]);
  }
}.

module G7 = GGen(Hs(H7),SGen(Hs(H7))).

(** Inverter *)
module I(A:CMA_2RO): Inverter = {
  var pk:pkey
  var n:int
  var ystar:signature

  module H = {
    var m:(message * salt,htag * bool * signature) map

    fun init(): unit = { }

    fun o(c:bool,x:message * salt): htag = {
      var b:bool = true;
      var i:int = 0;
      var w:htag;
      var st:gtag;
      var z, u:signature;

      if (!in_dom x H.m)
      {
        while (i < kg2 && b)
        {
          u = $sample_plain;
          z = if c then (ystar * f pk u) pk else f pk u;
          b = (sub (to_bits z) 0 1 = ones 1);
          w = HTag.from_bits (sub (to_bits z) 1 k1);
          st = GTag.from_bits (sub (to_bits z) (k1 + 1) (kg));
          i = i + 1;
          if (!b)
          {
            m.[x] = (w,c,u);
            G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
          }
        }
      }
      else
      {
        if (!c) m.[x] = (HTag.zeros,c,Signature.zeros);
      }
      return (lambda abc, let (a,b,c) = abc in a) (proj m.[x]);
    }
  }     

  module IOracles = {
    var qs:message set

    fun init(): unit = {
      qs = FSet.empty;
      H.m = Map.empty;
    }

    fun sign(m:message): signature = {
      var r:salt;
      var w:htag;
      r = $sample_salt;
      w = H.o(false,(m,r));
      return (lambda abc, let (a,b,c) = abc in c) (proj H.m.[(m,r)]);
    }

    fun fresh(m:message): bool = {
      return !mem m qs;
    }
  }

  module A = A(G,Ha(H),IOracles)

  fun inverter(pk:pkey,y:signature): signature = {
    var m:message;
    var s:signature;

    I.pk = pk;
    n = 3;
    ystar = y;
    (m,s) = A.forge(pk);

    return s;
  }
}.

equiv equiv_G7_OW (A<:CMA_2RO):
  G7(A(G,Ha(H7))).main ~ OW(I(A)).main: ={glob A} ==> ={res}.
proof strict.
  fun. inline{2} I(A).inverter;wp.
 I(A).A.forge.
admit. qed.

section.
declare module A:CMA_2RO {EF_CMA,Wrap,PSS,GGen,SGen,OW,G,Ha,Hs,H,H1,H2,H3,H4,H5,H6,H7}.
local module Ag = A(G).

local equiv equiv_PSS_G0:
  EF_CMA(Wrap(PSS(G,H)),Ag(H)).main ~ G0(Ag(H)).main: ={glob A} ==> ={res}.
proof strict.
fun.
inline Wrap(PSS(Gt.ROM.RO,Ht.ROM.RO)).verify
       PSS(Gt.ROM.RO,Ht.ROM.RO).verify
       PSS(Gt.ROM.RO,Ht.ROM.RO).g2
       Gt.ROM.RO.o
       PSS(Gt.ROM.RO,Ht.ROM.RO).g1.
swap{1} [21..25] -3;
eqobs_in;
rcondf{1} 21.
  intros=> &m; wp; rnd; wp; rnd; wp; call (_: true)=> //; call (_: true)=> //.
    skip; smt.
inline G.o.
wp; rnd{1}; wp;
rnd; wp;
call (_: ={glob Gt.ROM.RO, glob Ht.ROM.RO} /\
         Wrap.sk{1} = SGen.sk{2} /\
         Wrap.pk{1} = SGen.pk{2} /\
         Wrap.qs{1} = SGen.qs{2}).
  fun; inline PSS(Gt.ROM.RO,Ht.ROM.RO).sign
              PSS(Gt.ROM.RO,Ht.ROM.RO).g2 PSS(Gt.ROM.RO,Ht.ROM.RO).g1
              Gt.ROM.RO.o G.o; wp; rnd{1}; wp; rnd; wp;
       call (_: ={glob Ht.ROM.RO}); first by eqobs_in.
       rnd; wp; skip; progress=> //; smt.
  by fun; eqobs_in.
  by fun; eqobs_in.
inline Wrap(PSS(Gt.ROM.RO,Ht.ROM.RO)).init SGen(Ht.ROM.RO).init
       PSS(Gt.ROM.RO,Ht.ROM.RO).init PSS(Gt.ROM.RO,Ht.ROM.RO).keygen
       Mem.init.
wp; rnd{2}; wp; rnd; wp.
call (_: true ==> ={glob Ht.ROM.RO}); first by fun; eqobs_in.
call (_: true ==> ={glob Gt.ROM.RO}); first by fun; eqobs_in.
skip; progress=> //; smt.
qed.

(** Proof is up to bad with BAD = (b = true) in final memory *)
local equiv equiv_G0_G1_H:
  H.o ~ H1.o: ={x, glob H} /\ 2^(k - 1) <= Mem.n{2} < 2^k ==> !H1.bad{2} => ={res, glob H}.
fun; case (in_dom x ROM.RO.m){1}.
  rcondf{1} 2; [ | rcondf{2} 4 ]; first 2 by intros=> &m; rnd; wp.
  by wp; rnd; wp.

  rcondt{1} 2; [ | rcondt{2} 4 ]; first 2 by intros=> &m; rnd; wp.
  wp 2 4; while{2} (2^(k - 1) <= Mem.n < 2^k /\
                    eq_except H.m{1} H.m x /\
                    (!b => H.m.[x] = Some w)){2} (kg2 - i){2}.
    intros=> &m z; seq 1: (kg2 - i <= z /\ 2^(k - 1) <= Mem.n < 2^k /\ eq_except H.m{m} H.m x) 1%r 1%r 1%r 0%r.
      by rnd.
      by rnd (cpTrue); skip;
         intros=> &hr [[[[bounds nBad] [i_bound bad]] kg2_z] h]; rewrite bool_nuL //; smt.
      by wp; skip; progress=> //; smt.
      hoare; wp; skip; progress=> //; smt.
      by progress.
  swap{2} 3 -2; wp; rnd; skip; progress=> //; smt.
qed.

local equiv equiv_G0_G1:
  G0(Ag(H)).main ~ G1(Ag(H1)).main: ={glob A} ==> !H1.bad{2} => ={res}.
proof strict.
(* fun.
inline SGen(ROM.RO).fresh SGen(H1).fresh; wp.


fun; eqobs_in (={glob H}) true: (!H1.bad{1} => ={glob H}).
  fun; case (in_dom x ROM.RO.m){1}.
    rcondf{1} 2; first by intros=> &m; rnd.
    rcondf{2} 4; first by intros=> &m; rnd; wp.
    by wp; rnd; wp.

    rcondt{1} 2; first by intros=> &m; rnd.
    rcondt{2} 4; first by intros=> &m; rnd; wp.
    
*)
admit. qed.

lemma G0_G1 &m:
  Pr[G0(A(G,H)).main() @ &m: res] <= Pr[G1(A(G,H1)).main() @ &m: res] + Pr[G1(A(G,H1)).main() @ &m: H1.bad].
proof.
apply (Trans _ Pr[G1(A(G,H1)).main() @ &m: res \/ H1.bad] _).
equiv_deno (equiv_G0_G1)=> //; smt.
rewrite Pr mu_or; smt.
qed.

(** Maybe we need to fix the event to add a bound on the number of queries in the game *)
lemma Bad1 &m:
  Pr[G1(A(G,H1)).main() @ &m: H1.bad] <= (qS + qH)%r/(2^kg2)%r.
admit. qed.

end section.