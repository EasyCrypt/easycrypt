require import Int.
require import Real.
require import FMap.
require import FSet.

require (*--*) DiffieHellman.
require (*--*) PKE.

(** Assumption: set DDH *)
clone import DiffieHellman as DH.
import DDH.

(** Construction: a PKE **)
type pkey       = group.
type skey       = F.t.
type plaintext  = group.
type ciphertext = group * group.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(** Concrete Construction: Hashed ElGammal **)
module ElGamal : Scheme = {
  proc kg(): pkey * skey = {
    var sk;

    sk = $FDistr.dt;
    return (g ^ sk, sk);
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var y;

    y = $FDistr.dt;
    return (g ^ y, pk^y * m);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gy, gm;

    (gy, gm) = c;
    return Some (gm * gy^(-sk));
  }
}.

(** Correctness of the scheme *)

hoare Correctness: Correctness(ElGamal).main: true ==> res.
proof. proc; inline*; auto; progress; algebra. qed.

(** Exact security *)

module DDHAdv(A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
    var m0, m1, b, b';
    (m0, m1) = A.choose(gx);
    b = ${0,1};
    b' = A.guess(gy, gz * (b?m1:m0));
    return b' = b;
  }
}.

section Security.

  declare module A:Adversary.

  local lemma cpa_ddh0 &m:
      Pr[CPA(ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 7 -5.
    auto;call (_:true);auto;call (_:true);auto;progress;smt.
  qed.

  local module Gb = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b';
      x  = $FDistr.dt;
      y  = $FDistr.dt;
      (m0,m1) = A.choose(g^x);
      z  = $FDistr.dt;
      b' = A.guess(g^y, g^z);
      b  = ${0,1};
      return b' = b;
    }
  }.

  local lemma ddh1_gb &m:
      Pr[DDH1(DDHAdv(A)).main() @ &m : res] =
      Pr[Gb.main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 3 2;swap{1} [5..6] 2;swap{2} 6 -2.
    auto;call (_:true);wp.
    rnd (fun z, z + log(if b then m1 else m0){2})
        (fun z, z - log(if b then m1 else m0){2}).
    auto;call (_:true);auto;progress; (algebra || smt).
  qed.

  axiom Ac_l : islossless A.choose.
  axiom Ag_l : islossless A.guess.

  local lemma Gb_half &m:
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
    byphoare => //;proc.
    rnd  ((=) b')=> //=.
    call Ag_l;auto;call Ac_l;auto;progress;smt.
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
