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
axiom leq0_k: 0 < k.

op k0:int.
axiom leq0_k0: 0 < k0.

op k1:int.
axiom leq0_k1: 0 < k1.

axiom constraints:
  k0 + k1 <= k - 1.

op kg:int = k - k1 - 1.
lemma leq0_kg1: 0 < kg by [].

op kg2:int = k - k0 - k1 - 1.
lemma leq0_kg2: 0 <= kg2 by [].

op k':int = k - 1.
lemma leq0_k': 0 <= k' by [].

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
  fun forge(pk:pkey): message * signature
}.

(** Inlining the oracles that do not need to change *)
module type PartialOracles = {
  fun init(): pkey
  fun sign(m:message): signature
  fun fresh(m:message): bool
}.

module Mem = {
  var pk:pkey
  var sk:skey
  var n:int
  var xstar:signature

  fun init(pk:pkey,sk:skey): unit = {
    Mem.pk = pk;
    Mem.sk = sk;
    n = 3; (* Use the public key's modulus *)
    xstar = $sample_plain;
  }
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
    (N%r - (2^(k-1))%r / N%r) * charfun p true + ((2^(k - 1))%r / N%r) * charfun p false.

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

(** Proof is up to bad with BAD = (b = true) in final memory *)
lemma equiv_G0_G1 (A <: CMA_2RO):
  equiv [G0(A(G,H)).main ~ G1(A(G,H1)).main: ={glob A} ==> !H1.bad{2} => ={res}].
admit. qed.

lemma G0_G1 (A <: CMA_2RO) &m:
  Pr[G0(A(G,H)).main() @ &m: res] <= Pr[G1(A(G,H1)).main() @ &m: res] + Pr[G1(A(G,H1)).main() @ &m: H1.bad].
proof.
apply (Trans _ Pr[G1(A(G,H1)).main() @ &m: res \/ H1.bad] _).
equiv_deno (equiv_G0_G1 A)=> //; smt.
rewrite Pr mu_or; smt.
qed.

(** Maybe we need to fix the event to add a bound on the number of queries in the game *)
lemma Bad1 (A <: CMA_2RO) &m:
  Pr[G1(A(G,H1)).main() @ &m: H1.bad] <= (qS + qH)%r/(2^kg2)%r.
admit. qed.

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
    m = Map.empty;
  }

  fun o(c:bool,x:message * salt): htag = {
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
          m.[x] = (w,c);
          G.m.[w] = st ^ (GTag.from_bits (to_bits (snd x) || zeros (kg - k0)));
        }
      }
    }
    else
    {
      if (!c /\ snd (proj H5.m.[x]))
      {
        bad = true;
        m.[x] = (HTag.zeros,c);
      }
    }
    return fst (proj m.[x]);
  }
}.

module G5 = GGen(Hs(H5),SGen(Hs(H5))).

equiv equiv_G4_G5 (A <: CMA_2RO):
  G4(A(G,H4)).main ~ G5(A(G,Ha(H5))).main: ={glob A} ==> !H5.bad{2} => ={res}.
admit. qed.

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

end section.