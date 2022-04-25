(* -------------------------------------------------------------------- *)
require import AllCore Int Real Distr DBool CHoareTactic.
require (*--*) DiffieHellman BitWord PKE_CPA.


(* ---------------- Sane Default Behaviours --------------------------- *)
pragma +implicits.

(* ---------------------- Let's Get Started --------------------------- *)
op k : { int | 0 < k } as gt0_k.

clone import BitWord as Bits with
  op n <- k
proof gt0_n by exact/gt0_k
rename
  "word" as "bits"
  "dunifin" as "dbits".
import DWord.

(** Assumption: DDH **)
(*** WARNING: DiffieHellman is not up to speed with latest developments ***)
clone import DiffieHellman as DH.
import DDH FDistr.

(** Assumption Entropy Smoothing *)
theory EntropySmoothing.
  type hkey.

  op dhkey: { hkey distr | is_lossless dhkey } as dhkey_ll.
  hint exact random : dhkey_ll.  

  op cdhkey : { int | 0 <= cdhkey} as ge0_cdhkey.
  schema cost_dhkey `{P} : cost[P: dhkey] = N cdhkey.
  hint simplify cost_dhkey.

  op hash : hkey -> group -> bits.
  op chash : {int | 0 <= chash } as ge0_chash.
  schema cost_hash `{P} {k:hkey, g:group} : cost [P:hash k g] = cost [P: k] + cost[P:g] + N chash.
  hint simplify  cost_hash.

  module type AdvES = {
    proc guess(_: hkey * bits) : bool
  }.

  module ES0 (A:AdvES) = {
    proc main () : bool = {
      var b, hk, h;
      hk <$ dhkey;
      h  <$ dbits;
      b  <@ A.guess(hk,h);
      return b;
    }
  }.

  module ES1 (A:AdvES) = {
    proc main () : bool = {
      var b, hk, z;
      hk <$ dhkey;
      z  <$ dt;
      b  <@ A.guess(hk, hash hk (g ^ z));
      return b;
    }
  }.
end EntropySmoothing.
import EntropySmoothing.

(** Construction: a PKE **)
type pkey = hkey * group.
type skey = hkey * F.t.
type ptxt = bits.
type ctxt = group * bits.

clone import PKE_CPA as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

(** Concrete Construction: Hashed ElGammal **)
module Hashed_ElGamal : Scheme = {
  proc kg() = {
    var hk,sk;

    hk <$ dhkey;
    sk <$ dt;
    return ((hk,g ^ sk), (hk,sk));
  }

  proc enc(pk: pkey, m: ptxt) = {
    var y, h;

    y <$ dt;
    h <- hash pk.`1 (pk.`2 ^ y);
    return (g ^ y, h +^ m);
  }

  proc dec(sk:skey, c:ctxt): ptxt option = {
    var gy, h, hm;

    (gy, hm) <- c;
    h        <- hash sk.`1 (gy ^ sk.`2);
    return Some (h +^ hm);
  }
}.

(** Exact security *)
module DDHAdv(A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
    var hk, m0, m1, b, b', h;
    hk       <$ dhkey;
    (m0, m1) <@ A.choose((hk,gx));
    b        <$ {0,1};
    h        <- hash hk gz;
    b'       <@ A.guess(gy,h +^ (b?m1:m0));
    return b' = b;
  }
}.

module ESAdv(A:Adversary) = {
  proc guess (hk, h) : bool = {
    var x, y, m0, m1, b, b';
    x        <$ dt;
    y        <$ dt;
    (m0, m1) <@ A.choose((hk,g^x));
    b        <$ {0,1};
    b'       <@ A.guess(g^y, h +^ (b?m1:m0));
    return b' = b;
  }
}.

section Security.
  declare module A <: Adversary.
  declare axiom Ac_ll: islossless A.choose.
  declare axiom Ag_ll: islossless A.guess.

  local lemma cpa_ddh0 &m:
      Pr[CPA(Hashed_ElGamal,A).main() @ &m : res]
    = Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 1 1; swap{1} 8 -6; swap{2} 6 -3.
  auto; call (: true).
  auto; call (: true).
  by auto=> /> sk _ y _ hk _ [m0 m1] b _ /=; rewrite pow_pow.
  qed.

  local lemma ddh1_es1 &m:
      Pr[DDH1(DDHAdv(A)).main() @ &m : res]
    = Pr[ES1(ESAdv(A)).main() @ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 7 -3; swap{2} [5..6] -4; swap{2} 4 -1.
  auto; call (: true).
  auto; call (:true).
  by auto.
  qed.

  local module Gb = {
    proc main () : bool = {
      var hk, x, y, v,m0, m1, b, b';
      hk      <$ dhkey;
      x       <$ dt;
      y       <$ dt;
      (m0,m1) <@ A.choose(hk,g^x);
      v       <$ dbits;
      b'      <@ A.guess(g^y, v);
      b       <$ {0,1};
      return b' = b;
    }
  }.

  local lemma es0_Gb &m:
      Pr[ES0(ESAdv(A)).main() @ &m : res]
    = Pr[Gb.main()@ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 2 1. swap{1} [3..4] 4. swap{2} 7 -2.
  auto; call (: true); wp.
  rnd (fun w, w +^ (b0{1} ? m1{1} : m0{1})).
  auto; call (: true).
  by auto=> /> *; split => *; algebra.
  qed.

  local lemma Gb_half &m:
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
  byphoare=> //; proc.
  rnd (pred1 b')=> /=; conseq (_:_ ==> true).
  + by move=> /> b; rewrite dbool1E pred1E.
  call Ag_ll; auto.
  by call Ac_ll; auto=> />; rewrite dhkey_ll dt_ll dbits_ll.
  qed.

  lemma conclusion &m :
       `| Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] - 1%r/2%r |
    <= `| Pr[DDH0(DDHAdv(A)).main() @ &m : res]
          - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |
       + `| Pr[ES0(ESAdv(A)).main() @ &m : res]
            - Pr[ES1(ESAdv(A)).main() @ &m : res]|.
  proof.
  rewrite (cpa_ddh0 &m) (ddh1_es1 &m) (es0_Gb &m) (Gb_half &m).
  smt(@Real).
  qed.
end section Security.

print conclusion.


(* -------------------------------------------------------------------- *)
abstract theory Cost.

clone include AllCore.Cost.
clone include Bool.Cost.
clone include Bits.Cost.
clone include DBool.Cost.
clone include G.Cost.
clone include FDistr.Cost.
clone include PrimeField.Cost.

op cddh = 3 + cxor + chash + cdbool + cdhkey.
op cguess = 3 + 2*cgpow + cxor + cdbool + 2 * cdt.

lemma ex_conclusion (kc kg: int) (A <: Adversary[choose : `{N kc} , guess : `{N kg}]) &m :
  0 <= kc => 0 <= kg =>
  exists (Dddh <: DDH.Adversary [guess : `{N (cddh + kg + kc)}]) 
         (Des <: AdvES[guess: `{N (cguess + kg + kc) }]),
   `|Pr[CPA(Hashed_ElGamal, A).main() @ &m : res] - 1%r / 2%r| <=
   `|Pr[DDH0(Dddh).main() @ &m : res] - Pr[DDH1(Dddh).main() @ &m : res]| +
   `|Pr[ES0(Des).main() @ &m : res] - Pr[ES1(Des).main() @ &m : res]|.
proof.
  move=> ge0_kc ge0_kg.
  exists (DDHAdv(A)); split; last first.
  exists (ESAdv(A)); split; last first.
  apply (conclusion A _ _ &m).
  + conseq (_ : _ : time [N kc]).
    by proc true : time[].
  + conseq (_ : true ==> true : time [N kg]).
    by proc true : time[].
  + proc. move => /=. 
    call (:true; time []); rnd; call(:true; time []); do 2!rnd; skip => />.
    rewrite dt_ll dbool_ll /=. smt (ge0_cg ge0_cxor ge0_cdbool ge0_cdt).
  proc; call (:true; time []); wp; rnd; call(:true; time []); rnd; skip => />.
  rewrite dhkey_ll dbool_ll /=. smt (ge0_cxor ge0_cdbool ge0_chash ge0_cdhkey).
qed.

print ge0_cdt.
end Cost.

