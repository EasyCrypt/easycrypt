require import Option.
require import Int.
require import Real.

require (*--*) CDH.
require (*--*) AWord.
require (*--*) PKE.

type bits.
op k: int.
op uniform: bits distr.
op (^^): bits -> bits -> bits.

clone import AWord as Bitstring with
  type word <- bits,
  op length <- k,
  op (^)    <- (^^),
  op Dword.dword <- uniform.

(** Assumption: DDH **)
clone import CDH as CDH0.
import DDH.

(** Assumption Entropy Smoothing *)
type hkey.
op sample_hkey : hkey distr.
op hash : hkey -> group -> bits.
axiom sample_hkey_lossless: Distr.weight sample_hkey = 1%r.

module type AdvES = {
  proc guess(_: hkey * bits) : bool
}.

module ES0 (A:AdvES) = {  
  proc main () : bool = {
    var b, hk, h;
    hk = $sample_hkey;
    h = $uniform;
    b = A.guess(hk,h);
    return b;
  }
}.

module ES1 (A:AdvES) = {  
  proc main () : bool = {
    var b, hk, z;
    hk = $sample_hkey;
    z = $FDistr.dt;
    b = A.guess(hk, hash hk (g^z));
    return b;
  }
}.

(** Construction: a PKE **)
type pkey       = hkey*group.
type skey       = hkey*F.t.
type plaintext  = bits.
type ciphertext = group * bits.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext. 

(** Concrete Construction: Hashed ElGammal **)
module Hashed_ElGamal : Scheme = {
  proc kg(): pkey * skey = {
    var hk,sk;

    hk = $sample_hkey;
    sk = $FDistr.dt;
    return ((hk,g ^ sk), (hk,sk));   
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var y, h;

    y = $FDistr.dt;
    h = hash pk.`1 (pk.`2 ^ y);
    return (g ^ y, h ^^ m);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gy, h, hm;

    (gy, hm) = c; 
    h = hash sk.`1 (gy ^ sk.`2);
    return Some (h ^^ hm); 
  }
}.

(** Correctness of the scheme *)
hoare Correctness: Correctness( Hashed_ElGamal).main: true ==> res.
proof. 
  proc; inline*; auto; progress.
  by rewrite !pow_pow F.mulC;smt.
qed.

(** Exact security *)

module DDHAdv(A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
    var hk, m0, m1, b, b', h;
    hk = $sample_hkey;
    (m0, m1) = A.choose((hk,gx));
    b = ${0,1};
    h = hash hk gz;
    b' = A.guess(gy,h ^^ (b?m1:m0));
    return b' = b;
  }
}.

module ESAdv(A:Adversary) = {
  proc guess (hk, h) : bool = {
    var x, y, m0, m1, b, b';
    x = $FDistr.dt;
    y = $FDistr.dt;
    (m0, m1) = A.choose((hk,g^x));
    b = ${0,1};
    b' = A.guess(g^y, h ^^ (b?m1:m0));
    return b' = b;
  }
}.

section Security.

  declare module A:Adversary.

  local lemma cpa_ddh0 &m: 
      Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 1 1;swap{1} 8 -6;swap{2} 6 -3.
    auto;call (_:true); auto;call (_:true);auto;progress;smt.
  qed.

  local lemma ddh1_es1 &m: 
      Pr[DDH1(DDHAdv(A)).main() @ &m : res] = 
      Pr[ES1(ESAdv(A)).main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 7 -3;swap{2} [5..6] -4; swap{2} 4 -1.
    auto;call (_:true); auto;call (_:true);auto.
  qed.

  local module Gb = {
    proc main () : bool = {
      var hk, x, y, v,m0, m1, b, b';
      hk = $sample_hkey;
      x  = $FDistr.dt;
      y  = $FDistr.dt;
      (m0,m1) = A.choose(hk,g^x);
      v  = $uniform;
      b' = A.guess(g^y, v);
      b  = ${0,1};
      return b' = b;
    }
  }.

  local lemma es0_Gb &m:  
      Pr[ES0(ESAdv(A)).main() @ &m : res] = 
      Pr[Gb.main()@ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 2 1. swap{1} [3..4] 4. swap{2} 7 -2.
    auto;call (_:true);wp.
    rnd (fun w, w ^^ (b0{1} ? m1{1} : m0{1})).
    auto;call (_:true);auto;progress;smt.
  qed.

  axiom Ac_l : islossless A.choose.
  axiom Ag_l : islossless A.guess.

  local lemma Gb_half &m: 
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
    byphoare => //;proc.
    rnd => /=. conseq (_:_ ==> true).
    progress; rewrite -(Bool.Dbool.mu_x_def b'{hr}) /Distr.mu_x. 
    by apply Distr.mu_eq => x.
    call Ag_l;auto;call Ac_l;auto;progress;smt. 
  qed.

  lemma conclusion &m :
    `| Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] - 1%r/2%r | <=
    `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] -  
         Pr[DDH1(DDHAdv(A)).main() @ &m : res] | + 
    `| Pr[ES0(ESAdv(A)).main() @ &m : res] - 
         Pr[ES1(ESAdv(A)).main() @ &m : res]|.
  proof.
   rewrite (cpa_ddh0 &m) (ddh1_es1 &m) (es0_Gb &m) (Gb_half &m);smt.
  qed.

end section Security.

print conclusion.
