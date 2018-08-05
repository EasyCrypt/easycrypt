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
    proc; inline*; wp; rnd; wp; rnd; progress.
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
    move => uc_ll ug_ll; proc => //.
    swap 4 1; call ug_ll; wp; rnd; rnd; call uc_ll; wp; rnd; skip; progress; last 2 by apply FDistr.dt_ll.
    apply DBool.dbool_ll.
  qed.

  (* Perfect hiding *)
  local lemma fakecommit_half (U<:Unhider) &m:
    islossless U.choose =>
    islossless U.guess =>
    Pr[FakeCommit(U).main() @ &m : res] = 1%r/2%r.
  proof.
    move => uc_ll ug_ll; byphoare => //.
    proc; wp.
    swap 4 3.
    rnd (fun z, z = b'); call ug_ll; wp; rnd; call uc_ll; wp; rnd; skip; progress; last 2 by apply FDistr.dt_ll.
    + rewrite DBool.dboolE /=; by case result => //=.
  qed.

  local lemma phi_hi (U<:Unhider) &m:
    Pr[HidingExperiment(Pedersen,U).main() @ &m : res] =
    Pr[FakeCommit(U).main() @ &m : res].
  proof.
    byequiv => //.
    proc; inline*.
    call (_:true); wp.
    rnd (fun d, (d + x * (b?m1:m0)){2})
        (fun d, (d - x * (b?m1:m0)){2}).
    wp; rnd; call (_: true); wp; rnd; skip; progress.
    * case (bL) => bLE.
      + pose k := x0L * result_R.`2;
        rewrite sub_def -addA (addC (-k) k) addfN addf0 //.
      + pose k := x0L * result_R.`1;
        rewrite sub_def -addA (addC (-k) k) addfN addf0 //.
    * apply FDistr.dt_funi.
    * apply FDistr.dt_fu.
    * case (bL) => bLE; first 2 by rewrite sub_def -addA addfN addf0 //.
    * case (bL) => bLE; first 2 by rewrite -mul_pow -pow_pow //.
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
    byequiv => //.
    proc; inline*.
    wp; call (_: true); wp; rnd; skip; simplify; progress.
    (* Human-friendly renaming *)
    move : H1 H2 H3;
      pose c := result_R.`1;
      pose m := result_R.`2;
      pose d := result_R.`3;
      pose m':= result_R.`4;
      pose d':= result_R.`5;
      pose x := x0L;
      move => comm comm' m_neq_m'.
    have m'_neq_m: m' - m <> F.zero by move : m_neq_m'; apply absurd => /=; move => abhyp; rewrite -addf0 -abhyp addC sub_def -addA (addC (-m) m) addfN addf0 //.
    have ->: (d - d') * inv (m' - m) = x <=> (d - d') = x * (m' - m).
      split => lr.
      + rewrite -lr -mulA (F.mulC (inv (m' - m)) (m' - m)) mulfV // mulf1 //.
      + rewrite lr -mulA mulfV // mulf1 //.
    rewrite 2!sub_def -mulfDl mulfN.
    have ->: d + -d' = x * m' + - x * m <=> d + -d' + x * m = x * m'.
      split => lr.
      + rewrite lr -addA (addC (- x * m) (x * m)) addfN addf0 //.
      + rewrite -lr -addA addfN addf0 //.
    have ->: d + -d' + x * m = x * m' <=> d + x * m = d' + x * m'.
      split => lr.
      + rewrite -lr 2!addA (addC d' d) -2!addA (addA d' (-d') (x * m)) addfN (addC F.zero) addf0 //.
      + rewrite (addC d (-d')) -addA lr addA (addC (-d') d') addfN (addC F.zero) addf0 //.
    rewrite pow_bij -2!mul_pow -2!pow_pow -comm comm' //.
  qed.

  (*
     The following two are to compare probability directly with book discrete
     logarithm experiment. Not strictly necessary though, only for completeness.
  *)
  local lemma std_red_dl_bridge (B<:Binder) &m:
    Pr[DLog.DLogExperiment(DLogAttacker(B)).main() @ &m : res] <=
    Pr[DLog.DLogStdExperiment(StdRedAdversary(DLogAttacker(B))).main() @ &m : res].
  proof.
    byequiv => //.
    proc; wp; inline{2} StdRedAdversary(DLogAttacker(B)).guess; wp.
    seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}).
      inline*; wp; call (_: true); wp; rnd; skip; progress.
    if{2}.
    + rnd{2}; skip; progress; first by apply FDistr.dt_ll.
    wp; skip; progress.
  qed.

  lemma pedersen_std_computational_binding (B<:Binder) &m:
    Pr[BindingExperiment(Pedersen, B).main() @ &m : res] <=
    Pr[DLog.DLogStdExperiment(StdRedAdversary(DLogAttacker(B))).main() @ &m : res]
  by rewrite(pedersen_computational_binding B &m); apply (std_red_dl_bridge B &m).

end section PedersenSecurity.

print pedersen_correctness.
print pedersen_perfect_hiding.
print pedersen_computational_binding.