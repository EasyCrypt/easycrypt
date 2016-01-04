require import Fun Bool Int Real Distr List FSet Array FMap.
require (*--*) AWord ROM.

(** We consider three lengths of bitstrings **)
op k : { int | 0 < k } as k_pos. (* size of message *)
op l : { int | 0 < l } as l_pos. (* size of randomness *)
op n : { int | 0 < n } as n_pos. (* size of cipher *)

axiom sizes : k + l = n.

clone import AWord as Plaintext with
  op length = k
proof leq0_length by smt.

clone import AWord as Ciphertext with
  op length = n
proof leq0_length by smt.

clone import AWord as Randomness with
  op length = l
proof leq0_length by smt.

type plaintext = Plaintext.word.
type ciphertext = Ciphertext.word.
type randomness = Randomness.word.

(* We only need distributions on plaintexts and nonces *)
op uniform      = Plaintext.Dword.dword.
op uniform_rand = Randomness.Dword.dword.

(* We have operators that combine them *)
op (||) (x:randomness) (y:plaintext):ciphertext =
 Ciphertext.from_bits ((to_bits x) || (to_bits y)).

(** Please ignore **)
lemma find_unique x' (p: 'a -> bool) (xs : 'a list):
  (forall (x : 'a), p x => x = x') =>
  mem x' xs => p x' => find p xs = Some x'.
proof.
  move=> p_unique x'_in_m p_x'.
  case {-1}(find p xs) (Logic.eq_refl (find p xs))=> //=.
    smt.
    by move=> x /List.find_cor [] _ /p_unique.
qed.

(*** One way trapdoor permutation (pre-instantiated) ***)
(**  [See theory OW.ec] **)
theory OWTP.
  type pkey, skey.

  op keypairs: (pkey * skey) distr.
  axiom keypair_lossless : is_lossless keypairs.

  op f       : pkey -> randomness -> randomness.
  op finv    : skey -> randomness -> randomness.

  axiom finvof pk sk x:
   support keypairs (pk,sk) =>
   finv sk (f pk x) = x.

  axiom fofinv pk sk x:
   support keypairs (pk,sk) =>
   f pk (finv sk x) = x.

  lemma f_injective sk pk x y:
    support keypairs (pk,sk) =>
    f pk x = f pk y =>
    x = y.
  proof.
    move=> Hsupp Heqf.
    by rewrite -(finvof pk sk) // Heqf finvof.
  qed.

  module type Inverter = {
    proc i(pk:pkey,y:randomness): randomness
  }.

  module OW(I:Inverter) = {
    var r:randomness

    proc main(): bool = {
      var x', pk, sk;

      (pk,sk) = $keypairs;
      r       = $uniform_rand;
      x'      = I.i(pk,f pk r);
      return (r = x');
    }
  }.

  (** f is a secure OWTP if, for any inverter I,
        Adv^{OW}^f(I) = Pr[OW(I).main() @ &m: res]
      is small. **)
end OWTP.
import OWTP.

(*** We make use of a hash function (ROM) from randomness to
     plaintext. We let the adversary query it qH times at most. ***)
op qH : { int | 0 < qH } as qH_pos.

clone import ROM.ListLog as RandOrcl_BR with
  type from  <- randomness,
  type to    <- plaintext,
  op dsample <- fun (x:randomness) => uniform,
  op qH      <- qH.
import Lazy.
import Types.

(*** We can now define what it means to be a CPA-secure public-key encryption scheme ***)
(**  [See theory PKE.ec] **)
module type Scheme(RO : Oracle) = {
  proc kg(): (pkey * skey)
  proc enc(pk:pkey, m:plaintext): ciphertext
}.

module type Adv(ARO: ARO)  = {
  proc a1(p:pkey)      : (plaintext * plaintext)
  proc a2(c:ciphertext): bool
}.

module CPA(S:Scheme, A:Adv) = {
  module ARO = Log(RO)
  module A = A(ARO)
  module SO = S(RO)

  proc main(): bool = {
    var pk, sk, m0, m1, c, b, b';

    ARO.init();
    (pk,sk)  = SO.kg();
    (m0,m1)  = A.a1(pk);
    b = ${0,1};
    c  = SO.enc(pk,b?m0:m1);
    b' = A.a2(c);
    return b' = b;
  }
}.

(** A Scheme E is IND-CPA secure if, for any A,
      Adv^{CPA}_{S}(A) = `|Pr[CPA(S,A).main() @ &m: res] - 1/2|
    is small. **)

module BR(R:Oracle): Scheme(R) = {
  proc kg():(pkey * skey) = {
    var pk, sk;

    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var h, r;

    r = $uniform_rand;
    h = R.o(r);
    return ((f pk r) ||   m ^ h);
  }
}.

(** Given a CPA adversary A, we construct a OW inverter **)
module BR_OW(A:Adv): Inverter = {
  module ARO = Log(RO)
  module A = A(ARO)

  var x:randomness

  proc i(pk:pkey,y:randomness): randomness = {
    var m0,m1,h,b;

    ARO.init();
    (m0,m1) = A.a1(pk);
    h = $uniform;
    b = A.a2(y || h);
    x = oget (find (fun p => f pk p = y) ARO.qs);
    return x;
  }
}.

(** such that Adv^{CPA}_{S}(A) <= Adv^{OW}^{f}(I(A)).
    We now prove this bound. **)
lemma lossless_ARO_init: islossless Log(RO).init.
proof. by apply/(Log_init_ll RO)/RO_init_ll. qed.

lemma lossless_ARO_o : islossless Log(RO).o.
proof. by apply/(Log_o_ll RO)/RO_o_ll/Plaintext.Dword.lossless. qed.

section.
  (* Forall CPA adversary A whose memory footprint is disjoint from that of RO, Log and OW *)
  declare module A : Adv {RO,Log,OW}.

  (* and whose two procedures as lossless provided the random oracle is *)
  axiom a1_ll (O <: ARO{A}): islossless O.o => islossless A(O).a1.
  axiom a2_ll (O <: ARO{A}): islossless O.o => islossless A(O).a2.

  (* the following lemmas hold on the following constructions *)

  (** Step 1: replace RO call with random sampling **)
  local module BR1(R:Oracle): Scheme(R) = {
    var r:randomness

    proc kg = BR(R).kg

    proc enc(pk:pkey, m:plaintext): ciphertext = {
      var h;

      r = $uniform_rand;
      h = $uniform;
      return ((f pk r) || m ^ h);
    }
  }.

  (** The success probability of A in CPA(BR) is bounded by
      the success probability of A in CPA(BR1) plus the probability
      of the adversary querying the RO with the randomness used in
      the challenge encryption. **)
  local lemma BR_BR1 &m:
    Pr[CPA(BR,A).main() @ &m: res]
    <= Pr[CPA(BR1,A).main() @ &m: res]
       + Pr[CPA(BR1,A).main() @ &m: mem BR1.r Log.qs].
  proof.
    byequiv=> //=.
    proc.
    (* Until the adversary queries the ROM with r, knowing that
       the two ROMs agree on all points except r is sufficient
       to prove the equivalence of the adversary's views        *)
    call (_: mem BR1.r Log.qs,
             eq_except RO.m{1} RO.m{2} BR1.r{2}).
      (* Adversary is lossless *)
      exact/a2_ll.
      (* Oracles are equivalent up to the failure event *)
      proc. inline RO.o.
      wp. rnd.
      wp. skip. smt.
      (* Left oracle is lossless *)
      move=> &2 _; exact/lossless_ARO_o.
      (* Right oracle is lossless and preserves bad once set *)
      move=> &1. proc. inline *. wp. rnd. wp. skip. smt. (* or use conseq [-frame]... *)
    (* We return to the main game *)
    inline CPA(BR,A).SO.enc CPA(BR1,A).SO.enc.
    inline RO.o.
    wp. rnd.
    wp. rnd.
    wp. rnd.
    (* The first adversary call is simpler *)
    call (_:    ={Log.qs, RO.m}
             /\ (forall x, mem x Log.qs{1} <=> mem x (dom RO.m){1})).
      proc. inline RO.o.
      wp. rnd.
      wp. skip. smt.
    inline *. auto.
    progress.
      smt.
      smt.
      smt.
      smt.
      smt.
      smt.
  qed.

  (** Step 2: replace h ^ m with h in challenge encryption **)
  local module BR2(R:Oracle): Scheme(R) = {
    var r:randomness

    proc kg():(pkey * skey) = {
      var pk, sk;

      (pk,sk) = $keypairs;
      return (pk,sk);
    }

    proc enc(pk:pkey, m:plaintext): ciphertext = {
      var h;

      r = $uniform_rand;
      h = $uniform;
      return ((f pk r) || h);
    }
  }.

  (* The success probabilities in both games are the same *)
  local lemma BR1_BR2 &m:
    Pr[CPA(BR1,A).main() @ &m: res]
    = Pr[CPA(BR2,A).main() @ &m: res].
  proof.
    byequiv=> //=.
    proc.
    call (_: ={RO.m}).
      proc. inline *. auto.
    inline CPA(BR1,A).SO.enc CPA(BR2,A).SO.enc.
    wp. rnd (fun x => m{2} ^ x).
    rnd.
    wp. rnd.
    call (_: ={RO.m}).
      proc. inline *. auto.
    inline *. auto.
    progress.
      algebra.
      smt.
      smt.
      algebra.
  qed.

  (* The probability of the failure event is the same in both games *)
  local lemma BR1_BR2_bad &m:
    Pr[CPA(BR1,A).main() @ &m: mem BR1.r Log.qs]
    = Pr[CPA(BR2,A).main() @ &m: mem BR2.r Log.qs].
  proof.
    byequiv=> //=.
    proc.
    call (_:    ={Log.qs, RO.m}
             /\ BR1.r{1} = BR2.r{2}).
      proc. inline *. auto.
    inline CPA(BR1,A).SO.enc CPA(BR2,A).SO.enc.
    wp. rnd (fun x => m{2} ^ x).
    rnd. simplify.
    wp. rnd.
    call (_: ={Log.qs, RO.m}).
      proc. inline *. auto.
    inline *. auto.
    progress.
      algebra.
      smt.
      smt.
      algebra.
  qed.

  (** Exercise: What single "equiv" lemma could be used to prove both
      BR1_BR2 and BR1_BR2_bad in one? Prove it and use it to prove
      BR1_BR2_bad and BR1_BR2. **)

  (** We can now prove that the success probability of A in CPA(BR2) is exactly 1/2 **)
  local lemma pr_BR2_res &m: Pr[CPA(BR2,A).main() @ &m: res] = 1%r / 2%r.
  proof.
    byphoare=> //=.
    proc.
    inline CPA(BR2, A).SO.enc.
    swap 6 4; swap 4 5.
    wp.
    rnd (pred1 b')=> //=.
    inline *.
    call (_: true).
      exact a2_ll. (* adversary *)
      exact lossless_ARO_o. (* oracle *)
    auto.
    call (_: true).
      exact a1_ll. (* adversary *)
      exact lossless_ARO_o.
    auto=> //=.
    smt.
  qed.

  local lemma pr_BR_BR2 &m:
    Pr[CPA(BR,A).main() @ &m: res] - 1%r/2%r
    <= Pr[CPA(BR2,A).main() @ &m: mem BR2.r Log.qs].
  proof. smt. qed.

  (** Step 3: Finally, we can do the reduction and prove that whenever
      A queries the RO with the randomness used in the challenge
      encryption, BR_OW(A) inverts the OW challenge. **)
  local lemma BR2_OW &m:
    Pr[CPA(BR2,A).main() @ &m: mem BR2.r Log.qs]
    <= Pr[OW(BR_OW(A)).main() @ &m: res].
  proof.
    byequiv => //=.
    proc; inline *; wp.
    (* simplify postcondition to no longer have find *)
    conseq [-frame]
      (_ : _ ==>
           support keypairs (pk0{2}, sk{2}) /\
           BR2.r{1} = OW.r{2} /\ Log.qs{1} = Log.qs{2} /\
           y{2} = f pk0{2} BR2.r{1}).
      progress.
      rewrite (find_unique OW.r{2} _ Log.qs{2}) => //=.
      progress; first apply (f_injective sk{2} pk0{2} x OW.r{2}) => //.
    (* rest of proof *)
    swap {1} 3 - 2; swap {1} 9 -7; swap {1} 9 3; swap {1} 7 4.
    wp. rnd{1}.
    call (_: ={RO.m, Log.qs}); first by sim.
    auto.
    call (_: ={RO.m, Log.qs}); first by sim.
    auto; smt.
  qed.

  lemma Reduction &m:
    Pr[CPA(BR,A).main() @ &m : res] - 1%r/2%r
    <= Pr[OW(BR_OW(A)).main() @ &m: res].
  proof. smt. qed.
end section.
