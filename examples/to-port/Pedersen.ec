(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * A formal verification of the Pedersen commitment scheme
 *
 * Pedersen, Torben Pryds
 * "Non-interactive and information-theoretic secure verifiable secret sharing"
 *)
require import Real.
require import DLog.
require import CyclicGroup.

require (*--*) Commitment.

(* Pedersen protocol types *)
theory PedersenTypes.
  type value        = group.
  type message      = F.t.
  type commitment   = group.
  type openingkey   = F.t.
end PedersenTypes.
export PedersenTypes.

(* Instantiate the Commitment scheme with the above types *)
clone import Commitment as CM with
  type CommitmentProtocol.value      <- value,
  type CommitmentProtocol.message    <- message,
  type CommitmentProtocol.commitment <- commitment,
  type CommitmentProtocol.openingkey <- openingkey.
export CommitmentProtocol.

module Pedersen : CommitmentScheme = {
  proc gen() : value = {
    var x, h;
    x =$ FDistr.dt;
    h = g^x;
    return h;
  }

  proc commit(h: value, m: message) : commitment * openingkey = {
    var c, d;
    d =$ FDistr.dt;
    c = (g^d) * (h^m);
    return (c, d);
  }

  proc verify(h: value, m: message, c: commitment, d: openingkey) : bool = {
    var c';
    c' = (g^d) * (h^m);
    return (c = c');
  }
}.


module DLogAttacker(B:Binder) : DLog.Adversary = {
  proc guess(h: group) : F.t option = {

    var x, c, m, m', d, d';
    (c, m, d, m', d') = B.bind(h);
    if ((c = g^d * h^m) /\ (c = g^d' * h^m') /\ (m <> m'))
      x = Some((d - d') * inv (m' - m));
    else
      x = None;

    return x;
  }
}.

section PedersenSecurity.

  (* Correctness *)
  lemma pedersen_correctness:
    hoare[Correctness(Pedersen).main: true ==> res].
  proof.
    proc; inline*; auto.
  qed.

  local module FakeCommit(U:Unhider) = {
    proc main() : bool = {
      var b, b', x, h, c, d;
      var m0, m1 : F.t;

      (* Clearly, there are many useless lines, but their presence helps for the proofs *)
      x =$ FDistr.dt;
      h = g^x;
      (m0, m1) = U.choose(h);
      b =$ {0,1};
      d =$ FDistr.dt;
      c = g^d; (* message independent - fake commitment *)
      b' = U.guess(c);

      return (b = b');
    }
  }.

  local lemma hi_ll (U<:Unhider):
    islossless U.choose =>
    islossless U.guess =>
    islossless FakeCommit(U).main.
  proof.
    move => uc_ll ug_ll; proc.
    call ug_ll; auto; call uc_ll; auto; smt.
  qed.

  (* Perfect hiding *)
  local lemma fakecommit_half (U<:Unhider) &m:
    islossless U.choose =>
    islossless U.guess =>
    Pr[FakeCommit(U).main() @ &m : res] = 1%r/2%r.
  proof.
    move => uc_ll ug_ll; byphoare.
    proc; wp.
    swap 4 3.
    rnd (fun z, z = b'); call ug_ll; auto; call uc_ll; auto.
    progress; smt.
    trivial.
    trivial.
  qed.

  local lemma phi_hi (U<:Unhider) &m:
    Pr[HidingExperiment(Pedersen,U).main() @ &m : res] =
    Pr[FakeCommit(U).main() @ &m : res].
  proof.
    byequiv.
    proc; inline*.
    call (_:true); wp.
    rnd (fun d, (d + x * (b?m1:m0)){2})
        (fun d, (d - x * (b?m1:m0)){2}).
    auto; call (_: true); auto.
    progress; smt.
    trivial.
    trivial.
  qed.

  (* Perfect hiding - QED *)
  lemma pedersen_perfect_hiding (U<:Unhider) &m:
    islossless U.choose =>
    islossless U.guess =>
    Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = 1%r/2%r
  by move => uc_ll ug_ll; rewrite (phi_hi U &m) (fakecommit_half U &m).

  (* Computational binding - QED *)
  lemma pedersen_computational_binding (B<:Binder) &m:
    Pr[BindingExperiment(Pedersen, B).main() @ &m : res] =
    Pr[DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res].
  proof.
    byequiv.
    proc; inline*.
    auto; call (_: true); wp.
    rnd; skip.
    progress.
    pose c := result_R.`1.
    pose m := result_R.`2.
    pose d := result_R.`3.
    pose m':= result_R.`4.
    pose d':= result_R.`5.
    pose x := x0L.
    (* Here the proof needs a hand... *)
    have hand : (c = g ^ d * g ^ x ^ m /\ c = g ^ d' * g ^ x ^ m' /\ m <> m') =>
                    (d - d' + x*m = x*m') by smt.
    smt.
    trivial.
    trivial.
  qed.

  (*
     The following two are to compare probability directly with book discrete
     logarithm experiment. Not strictly necessary though, only for completeness.
  *)
  local lemma std_red_dl_bridge (B<:Binder) &m:
    Pr[DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res] <=
    Pr[DLog.DLogStdExperiment(StdRedAdversary(DLogAttacker(B))).main() @ &m : res].
  proof.
    byequiv.
    proc; auto; inline{2} StdRedAdversary(DLogAttacker(B)).guess; wp.
    seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}); inline*; auto.
    call (_: true); auto.
    if{2}.
    rnd{2}; skip; smt.
    wp; skip; smt.
    trivial.
    trivial.
  qed.

  lemma pedersen_std_computational_binding (B<:Binder) &m:
    Pr[BindingExperiment(Pedersen, B).main() @ &m : res] <=
    Pr[DLog.DLogStdExperiment(StdRedAdversary(DLogAttacker(B))).main() @ &m : res]
  by rewrite(pedersen_computational_binding B &m); apply (std_red_dl_bridge B &m).

end section PedersenSecurity.

print pedersen_correctness.
print pedersen_perfect_hiding.
print pedersen_computational_binding.