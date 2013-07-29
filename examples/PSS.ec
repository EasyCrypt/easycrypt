require import Bitstring.
require import Int.
require import Distr.

(* Protocol-specific constants *)
op k:int.
axiom leq0_k: 0 <= k.
op k0:int.
axiom leq0_k0: 0 <= k0.
op k1:int.
axiom leq0_k1: 0 <= k1.
axiom constraints:
  0 <= k - k1 - 1.

(* General definitions *)
require        EF_CMA.

clone import EF_CMA.EF_CMA_2ROM as PSS_EF_CMA with
  type PKS.message <- bitstring,
  type PKS.signature <- bitstring,
  type PKS.Gt.from <- bitstring,
  type PKS.Gt.to <- bitstring,
  op PKS.Gt.dsample = Dbitstring.dbitstring (k - k1  -1),
  type PKS.Ht.from <- bitstring,
  type PKS.Ht.to <- bitstring,
  op PKS.Ht.dsample = Dbitstring.dbitstring k1.
import PKS.

op keypairs: (pkey * skey) distr.
axiom keypairsL: weight keypairs = 1%r.

op rsa: pkey -> bitstring -> bitstring.
op rsa': skey -> bitstring -> bitstring.

module PSS(G:Gt.Oracle,H:Ht.Oracle): Scheme = {
  fun g1(x:bitstring):bitstring = {
    var r:bitstring;
    r  = G.o(x);
    return sub r 0 k0;
  }

  fun g2(x:bitstring):bitstring = {
    var r:bitstring;
    r  = G.o(x);
    return sub r k0 (k - k0 - k1 - 1);
  }

  (* Keygen: make it a wrapped pop *)
  fun keygen():(pkey * skey) = {
    var (pk, sk):(pkey * skey);
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  (* Sign *)
  fun sign(sk:skey, m:bitstring):bitstring = {
    var r:bitstring;
    var rMask:bitstring;
    var maskedR:bitstring;
    var w:bitstring;
    var gamma:bitstring;
    var y:bitstring;

    r = $Dbitstring.dbitstring(k0);
    w  = H.o(m || r);
    rMask  = g1(w);
    maskedR = rMask ^^ r;
    gamma  = g2(w);
    y = zeros(1) || w || maskedR || gamma;
    return (rsa' sk m); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:bitstring, s:bitstring):bool = {
    var y:bitstring;
    var w:bitstring;
    var w':bitstring;
    var maskedR:bitstring;
    var gamma:bitstring;
    var gamma':bitstring;
    var rMask:bitstring;
    var r:bitstring;
    var b:bool;

    y = (rsa pk s);
    b = y.[0];
    w = sub y 1 k1;
    maskedR = sub y (k1 + 1) k0;
    gamma = sub y (k1 + k0 + 1) (k - k1 - k0 - 1);
    rMask  = g1(w);
    r = rMask ^^ maskedR;
    w'  = H.o(m || r);
    gamma'  = g2(w);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

module G = Gt.ROM.RO.
module G' = Gt.WRO_Set.ARO(G).
module H = Ht.ROM.RO.
module H' = Ht.WRO_Set.ARO(H).

section.
declare module A:CMA {G', H', Wrap}.
axiom losslessA (G <: Gt.ARO{A}) (H <: Ht.ARO{A}) (O <: Oracles{A}):
  islossless O.sign => islossless H.o => islossless G.o =>
  islossless A(G, H, O).a.

module PSS_bits = PSS(G,H).
module PSS_bors = Wrap(G,H,PSS_bits).
module Initial = EF_CMA(G,H,PSS_bits,A).

lemma terminates: islossless Initial.main.
proof strict.
fun.
call (_: true ==> true);
  first by fun.
call (_: true ==> true); first fun.
  call (_: true ==> true);
    first by fun; call (_: true ==> true)=> //;
               apply Gt.ROM.lossless_o;
               rewrite -/(weight Gt.dsample) /Gt.dsample Dbitstring.weight_pos; smt.
  call (_: true ==> true);
    first by apply Ht.ROM.lossless_o;
             rewrite -/(weight Ht.dsample) /Ht.dsample Dbitstring.weight_pos; smt.
  wp; call (_: true ==> true);
    first by fun; call (_: true ==> true)=> //;
               apply Gt.ROM.lossless_o;
               rewrite -/(weight Gt.dsample) /Gt.dsample Dbitstring.weight_pos; smt.
  wp=> //.
call (_: true ==> true).
  fun true=> //.
    by intros=> G0 H0 O; apply (losslessA G0 H0 O).
    fun; call (_: true ==> true).
      fun; wp; call (_: true ==> true)=> //;
          first by fun; call (_: true ==> true)=> //;
                     apply Gt.ROM.lossless_o=> //;
                     rewrite -/(weight Gt.dsample) /Gt.dsample Dbitstring.weight_pos; smt.
        wp; call (_: true ==> true)=> //;
          first by fun; call (_: true ==> true)=> //;
                     apply Gt.ROM.lossless_o=> //;
                     rewrite -/(weight Gt.dsample) /Gt.dsample Dbitstring.weight_pos; smt.
        call (_: true ==> true)=> //;
          first by apply Ht.ROM.lossless_o=> //;
                   rewrite -/(weight Ht.dsample) /Ht.dsample Dbitstring.weight_pos; smt.
        by rnd=> // _; rewrite -/cpTrue -/(weight (Bitstring.Dbitstring.dbitstring k0))
                               Bitstring.Dbitstring.weight_pos // leq0_k0.
      wp=> //.
    fun; if; try wp=> //.
      call (_: true ==> true); try wp=> //;
        first by apply Ht.ROM.lossless_o=> //;
                 rewrite -/(weight Ht.dsample) /Ht.dsample Dbitstring.weight_pos; smt.
    fun; if; try wp=> //.
      call (_: true ==> true); try wp=> //;
        first by apply Gt.ROM.lossless_o=> //;
                 rewrite -/(weight Gt.dsample) /Gt.dsample Dbitstring.weight_pos; smt.
call (_: true ==> true)=> //; fun;
  call (_: true ==> true);
    first fun; rnd=> // _; apply keypairsL.
  wp; call (_: true ==> true);
    first apply Gt.ROM.lossless_init.
  wp; call (_: true ==> true)=> //;
    apply Ht.ROM.lossless_init.
qed.
