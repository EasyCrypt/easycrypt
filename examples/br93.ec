(* -------------------------------------------------------------------- *)
require import AllCore List FSet NewFMap.
require import Distr DBool.
require (*--*) BitWord OW ROM.

(*** We consider a concrete instance:
     - plaintexts are bitstrings of length k > 0
     - nonces are bitstrings of length l > 0
     - ciphertexts are bitstrings of length n = k + l                 ***)
(** A type for plaintexts **)
op k : { int | 0 < k } as gt0_k. (* size of plaintexts *)

clone import BitWord as Plaintext with
  op n <- k
proof gt0_n by exact/gt0_k
rename "word" as "ptxt".

(** A type for nonces **)
op l : { int | 0 < l } as gt0_l. (* size of nonces *)

clone import BitWord as Randomness with
  op n <- l
proof gt0_n by exact/gt0_l
rename "word" as "rand".

(** A type for ciphertexts **)
op n = k + l.                    (* size of ciphertexts *)
lemma gt0_n: 0 < n by smt(gt0_k gt0_l).

clone import BitWord as Ciphertext with
  op n <- n
proof gt0_n by exact/Self.gt0_n
rename "word" as "ctxt".

(** We rename a few things to make them usable...                      **)
op dptxt = Plaintext.DWord.dunifin.
op drand = Randomness.DWord.dunifin.

(** ... and define the concatenation of nonce and plaintext into
    a ciphertext.                                                      **)
op (||) (x:rand) (y:ptxt):ctxt = mkctxt ((ofrand x) ++ (ofptxt y)).

(*** We consider a one-way trapdoor permutation over nonces
     (with abstract keys)                                             ***)
(** Note: this hides a few existential axioms:
      * existence of two types pkey and skey such that
        a lossless distribution dkeys exists on (pkey * skey), and
      * existence of, for each valid pair (pk,sk) in the support
        of dkeys, a bijection `f pk` (and its inverse `finj sk`)       **)
clone import OW as OW_rand with
  type D           <- rand,
  type R           <- rand,
  op   challenge _ <- drand
proof challenge_ll, challenge_uni.
realize challenge_ll by move=> _ _; exact/Randomness.DWord.dunifin_ll.
realize challenge_uni by move=> _ _; exact/Randomness.DWord.dunifin_uni.
(** f is a secure OWTP if, for any inverter I,
      Adv^{OW}^f(I) = Pr[OW(I).main() @ &m: res]
    is small. **)

(*** We make use of a hash function (ROM) from randomness to
  plaintext. We let the adversary query it qH times at most. ***)
(** qH is left abstract, so the result is universally quantified **)
op qH : { int | 0 < qH } as qH_pos.

clone import ROM.ListLog as RandOrcl_BR with
  type from  <- rand,
  type to    <- ptxt,
  op dsample <- fun (x:rand) => dptxt,
  op qH      <- qH.

import Lazy.
import Types.

(*** We can now define what it means to be a CPA-secure public-key
   * encryption scheme ***)
(**  [See theory PKE_CPA.ec, note the issue with oracles] **)
module type Scheme(RO : Oracle) = {
  proc kg(): (pkey * skey)
  proc enc(pk:pkey, m:ptxt): ctxt
}.

module type Adv(ARO: ARO)  = {
  proc a1(p:pkey): (ptxt * ptxt)
  proc a2(c:ctxt): bool
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
    b  <$ {0,1};
    c  <@ SO.enc(pk,b?m0:m1);
    b' <@ A.a2(c);
    return b' = b;
  }
}.

(** A Scheme E is IND-CPA secure if, for any A,
      Adv^{CPA}_{S}(A) = `|Pr[CPA(S,A).main() @ &m: res] - 1/2|
    is small. **)

module (BR : Scheme) (R:Oracle) = {
  proc kg():(pkey * skey) = {
    var pk, sk;

    (pk,sk) <$ dkeys;
    return (pk,sk);
  }

  proc enc(pk:pkey, m:ptxt): ctxt = {
    var h, r;

    r <$ drand;
    h <@ R.o(r);
    return ((f pk r) || m +^ h);
  }
}.

(** Given a CPA adversary A, we construct a OW inverter **)
module BR_OW(A:Adv): Inverter = {
  module ARO = Log(RO)
  module A = A(ARO)

  var x:rand

  proc invert(pk:pkey,y:rand): rand = {
    var m0,m1,h,b;

    ARO.init();

    (m0,m1) <@ A.a1(pk);
    h       <$ dptxt;
    b       <@ A.a2(y || h);
    x       <- nth witness ARO.qs (find (fun p => f pk p = y) ARO.qs);

    return x;
  }
}.

(** such that Adv^{CPA}_{S}(A) <= Adv^{OW}^{f}(I(A)).
    We now prove this bound. **)
lemma ARO_init_ll: islossless Log(RO).init.
proof. by apply/(Log_init_ll RO)/RO_init_ll. qed.

lemma ARO_o_ll : islossless Log(RO).o.
proof. by apply/(Log_o_ll RO)/RO_o_ll/Plaintext.DWord.dunifin_ll. qed.

section.
  (* Forall CPA adversary A whose memory footprint is disjoint from
     that of RO, Log and OW *)
  declare module A : Adv {RO,Log,OW}.

  (* and whose two procedures as lossless provided the random oracle is *)
  axiom a1_ll (O <: ARO{A}): islossless O.o => islossless A(O).a1.
  axiom a2_ll (O <: ARO{A}): islossless O.o => islossless A(O).a2.

  (* the following lemmas hold on the following constructions *)

  (** Step 1: replace RO call with random sampling **)
  local module (BR1:Scheme) (R:Oracle) = {
    var r:rand

    proc kg = BR(R).kg

    proc enc(pk:pkey, m:ptxt): ctxt = {
      var h;

      r <$ drand;
      h <$ dptxt;
      return ((f pk r) || m +^ h);
    }
  }.

  (** The success probability of A in CPA(BR) is bounded by
      the success probability of A in CPA(BR1) plus the probability
      of the adversary querying the RO with the randomness used in
      the challenge encryption. **)
  local lemma BR_BR1 &m:
    Pr[CPA(BR,A).main() @ &m: res]
    <= Pr[CPA(BR1,A).main() @ &m: res]
       + Pr[CPA(BR1,A).main() @ &m: mem Log.qs BR1.r].
  proof.
    byequiv=> //=.
    proc.
    (* Until the adversary queries the ROM with r, knowing that
       the two ROMs agree on all points except r is sufficient
       to prove the equivalence of the adversary's views        *)
    call (_: mem Log.qs BR1.r ,
             eq_except RO.m{1} RO.m{2} (pred1 BR1.r{2})).
      (* Adversary is lossless *)
      exact/a2_ll.
      (* Oracles are equivalent up to the failure event *)
      proc. inline RO.o.
      wp. rnd.
      wp. skip. smt (@NewFMap).
      (* Left oracle is lossless *)
      move=> &2 _; exact/ARO_o_ll.
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
             /\ (forall x, mem Log.qs{1} x <=> mem (dom RO.m){1} x)).
      proc. inline RO.o.
      wp. rnd.
      wp. skip=> /> &2 log_is_dom y _; smt(@NewFMap).
    inline *. auto. progress; smt.
  qed.

  (** Step 2: replace h ^ m with h in challenge encryption **)
  local module (BR2:Scheme) (R:Oracle) = {
    var r:rand

    proc kg():(pkey * skey) = {
      var pk, sk;

      (pk,sk) <$ dkeys;
      return (pk,sk);
    }

    proc enc(pk:pkey, m:ptxt): ctxt = {
      var h;

      r <$ drand;
      h <$ dptxt;
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
    wp. rnd (fun x => m{2} +^ x).
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
    Pr[CPA(BR1,A).main() @ &m: mem Log.qs BR1.r]
    = Pr[CPA(BR2,A).main() @ &m: mem Log.qs BR2.r].
  proof.
    byequiv=> //=.
    proc.
    call (_:    ={Log.qs, RO.m}
             /\ BR1.r{1} = BR2.r{2}).
      proc. inline *. auto.
    inline CPA(BR1,A).SO.enc CPA(BR2,A).SO.enc.
    wp. rnd (fun x => m{2} +^ x).
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

  (** We can now prove that the success probability of A in CPA(BR2) is
    * exactly 1/2 **)
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
      exact ARO_o_ll. (* oracle *)
    auto.
    call (_: true).
      exact a1_ll. (* adversary *)
      exact ARO_o_ll.
    auto=> //=.
    smt.
  qed.

  local lemma pr_BR_BR2 &m:
    Pr[CPA(BR,A).main() @ &m: res] - 1%r/2%r
    <= Pr[CPA(BR2,A).main() @ &m: mem Log.qs BR2.r].
  proof. smt. qed.

  (** Step 3: Finally, we can do the reduction and prove that whenever
      A queries the RO with the randomness used in the challenge
      encryption, BR_OW(A) inverts the OW challenge. **)
  local module OWr (I : Inverter) = {
    var x : rand

    proc main() : bool = {
      var x', pk, sk;

      (pk,sk) <$ dkeys;
      x       <$ drand;
      x'      <@ I.invert(pk,f pk x);
      return (x = x');
    }
  }.

  local lemma globx &m:
    Pr[OW(BR_OW(A)).main() @ &m: res]
    = Pr[OWr(BR_OW(A)).main() @ &m: res].
  proof. by byequiv=> //=; sim. qed.

  local lemma BR2_OW &m:
    Pr[CPA(BR2,A).main() @ &m: mem Log.qs BR2.r]
    <= Pr[OW(BR_OW(A)).main() @ &m: res].
  proof.
    rewrite (globx &m).
    byequiv => //=.
    proc; inline *; wp.
    (* simplify postcondition to no longer have find *)
    conseq [-frame]
      (_ : _ ==>
           support dkeys (pk0{2}, sk{2}) /\
           BR2.r{1} = OWr.x{2} /\ Log.qs{1} = Log.qs{2} /\
           y{2} = f pk0{2} BR2.r{1}).
      progress; pose P := fun p => f _ p = _.
      have h := nth_find witness P Log.qs{2} _.
        by rewrite hasP; exists OWr.x{2}.
      by rewrite (f_pk_inj _ _ _ _ H _ _ h) //; move=> _; rewrite Randomness.DWord.dunifin_fu.
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
