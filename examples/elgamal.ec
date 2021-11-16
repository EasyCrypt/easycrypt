(* -------------------------------------------------------------------- *)
require import AllCore Int Real Distr DBool.
require (*--*) DiffieHellman PKE_CPA.

(* ---------------- Sane Default Behaviours --------------------------- *)
pragma +implicits.

(* ---------------------- Let's Get Started --------------------------- *)
(** Assumption: set DDH *)
(*** WARNING: DiffieHellman is really out of date ***)
clone import DiffieHellman as DH.
import DDH FDistr.

(** Construction: a PKE **)
type pkey = group.
type skey = F.t.
type ptxt = group.
type ctxt = group * group.

clone import PKE_CPA as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

(** Concrete Construction: Hashed ElGammal **)
module ElGamal : Scheme = {
  proc kg(): pkey * skey = {
    var sk;

    sk <$ dt;
    return (g ^ sk, sk);
  }

  proc enc(pk:pkey, m:ptxt): ctxt = {
    var y;

    y <$ dt;
    return (g ^ y, pk ^ y * m);
  }

  proc dec(sk:skey, c:ctxt): ptxt option = {
    var gy, gm;

    (gy, gm) <- c;
    return Some (gm * gy^(-sk));
  }
}.

(** Reduction: from a PKE adversary, construct a DDH adversary *)
module DDHAdv (A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
    var m0, m1, b, b';
    (m0, m1) <- A.choose(gx);
    b        <$ {0,1};
    b'       <@ A.guess(gy, gz * (b?m1:m0));
    return b' = b;
  }
}.

(** We now prove that, for all adversary A, we have:
      `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r |
      = `| Pr[DDH0(DDHAdv(A)).main() @ &m : res]
           - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |.        **)
section Security.
  declare module A <: Adversary.
  declare axiom Ac_ll: islossless A.choose.
  declare axiom Ag_ll: islossless A.guess.

  local lemma cpa_ddh0 &m:
      Pr[CPA(ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 7 -5.
  auto; call (_:true).
  auto; call (_:true).
  by auto=> /> sk _ y _ r b _; rewrite pow_pow.
  qed.

  local module Gb = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b';
      x       <$ FDistr.dt;
      y       <$ FDistr.dt;
      (m0,m1) <@ A.choose(g^x);
      z       <$ FDistr.dt;
      b'      <@ A.guess(g^y, g^z);
      b       <$ {0,1};
      return b' = b;
    }
  }.

  local lemma ddh1_gb &m:
      Pr[DDH1(DDHAdv(A)).main() @ &m : res] =
      Pr[Gb.main() @ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 3 2; swap{1} [5..6] 2; swap{2} 6 -2.
  auto; call (_:true); wp.
  rnd (fun z, z + log (if b then m1 else m0){2})
      (fun z, z - log (if b then m1 else m0){2}).
  auto; call (_:true).
  by auto; progress; algebra.
  qed.

  local lemma Gb_half &m:
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
  byphoare=> //; proc.
  rnd  (pred1 b')=> //=.
  conseq (: _ ==> true).
  + by move=> /> b; rewrite dbool1E pred1E.
  islossless;[ apply Ag_ll | apply Ac_ll].
  qed.

  lemma conclusion &m :
    `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] -
         Pr[DDH1(DDHAdv(A)).main() @ &m : res] |.
  proof.
  by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  qed.
end section Security.

print conclusion.
