(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * A formal verification of the Schnorr proof of knowledge
 *)
require import Int.
require import Real.
require import Distr.
require import CyclicGroup.

require (*--*) SigmaProtocol.

(* Schnorr protocol types *)
theory SchnorrTypes.
  type statement    = group.
  type witness      = F.t.
  type message      = group.
  type secret       = F.t.
  type challenge    = F.t.
  type response     = F.t.

  op R_DL h w       = (h = g^w).
end SchnorrTypes.
export SchnorrTypes.

(* Instantiate the Sigma scheme with the above types *)
clone import SigmaProtocol as SP with
  type SigmaProtocol.statement <- statement,
  type SigmaProtocol.witness   <- witness,
  type SigmaProtocol.message   <- message,
  type SigmaProtocol.secret    <- secret,
  type SigmaProtocol.challenge <- challenge,
  type SigmaProtocol.response  <- response,
  op   SigmaProtocol.R         = R_DL,
  op   SigmaProtocol.de        = FDistr.dt.
export SigmaProtocol.

module SchnorrPK : SigmaScheme = {
  proc gen() : statement * witness = {
    var h, w;
    w =$ FDistr.dt;
    if (w = F.zero) { (* A loop would be better, however the support for while loops is poor *)
      w = -F.one;
    }
    h = g^w;
    return (h, w);
  }

  proc commit(h: statement, w: witness) : message * secret = {
    var r, a;
    r =$ FDistr.dt;
    a = g^r;
    return (a, r);
  }

  proc test(h: statement, a: message) : challenge = {
    var e;
    e =$ FDistr.dt;
    return e;
  }

  proc respond(sw: statement * witness, ms: message * secret, e: challenge) : response = {
    var z, w, r;
    w = snd sw;
    r = snd ms;
    z = r + e*w;
    return z;
  }

  proc verify(h: statement, a: message, e: challenge, z: response) : bool = {
    var v, v';
    v = a*(h^e);
    v' = g^z;
    return (v = v');
  }
}.

module SchnorrPKAlgorithms : SigmaAlgorithms = {
  proc soundness(h: statement, a: message, e: challenge, z: response, e': challenge, z': response) : witness option = {
    var sto, w, v, v';

    v  = (g^z  = a*(h^e ));
    v' = (g^z' = a*(h^e'));
    if (e <> e' /\ v /\ v') {
      w = (z - z') / (e - e');
      sto = Some(w);
    } else {
      sto = None;
    }

    return sto;
  }

  proc simulate(h: statement, e: challenge) : message * challenge * response = {
    var a, z;

    z  =$ FDistr.dt;
    a  = (g^z) * (h^(-e));

    return (a, e, z);
  }
}.


module Foo = {
  proc foo() : bool = {
    var a;
    a =$ FDistr.dt;
    return a = F.one;
  }

  proc bar() : bool = {
    var b;
    b =$ FDistr.dt;
    return b = F.zero;
  }
}.

section SchnorrPKSecurity.
  (* Completeness *)
  lemma schnorr_proof_of_knowledge_completeness_ll:
    islossless Completeness(SchnorrPK).main.
  proof.
    proc; inline*.
    wp; rnd; wp; rnd; wp; skip; progress by apply FDistr.dt_ll.
  qed.


  lemma schnorr_proof_of_knowledge_completeness h w' &m:
    R h w' =>
    Pr[Completeness(SchnorrPK).main(h, w') @ &m : res] = 1%r.
  proof.
    rewrite /R /R_DL; move => sigmarel.
    byphoare (_: h = x /\ w' = w ==> _) => //.
    proc; inline*; swap 3 -2; swap 8 -7.
    wp; rewrite /snd /=.
    rnd; rnd; skip.
    progress => //. subst x{hr}.
    have <-/=: predT = fun x => mu FDistr.dt (fun (x0 : t) => g ^ x0 * g ^ w{hr} ^ x = g ^ (x0 + x * w{hr})) = 1%r.
      rewrite fun_ext => x; rewrite muE /=.
      have ->/=: (fun (x0 : t) => if g ^ x0 * g ^ w{hr} ^ x = g ^ (x0 + x * w{hr}) then mass FDistr.dt x0 else 0%r) = (fun x0 => mass FDistr.dt x0).
        rewrite fun_ext => z.
        have ->//: g ^ z * g ^ w{hr} ^ x = g ^ (z + x * w{hr}) by rewrite pow_pow mul_pow mulC //.
      rewrite -weightE FDistr.dt_ll /predT //.
    rewrite FDistr.dt_ll //.
  qed.

  (* Special soundness *)
  lemma schnorr_proof_of_knowledge_special_soundness (h: statement) msg ch ch' r r' &m:
    ch <> ch' =>
    g^r  = msg*(h^ch ) =>
    g^r' = msg*(h^ch') =>
    Pr[SpecialSoundnessExperiment(SchnorrPK, SchnorrPKAlgorithms).main(h, msg, ch, r, ch', r') @ &m : (res <> None /\ R h (oget res))] = 1%r.
  proof.
    move => challenges_differ.
    move => accepting_transcript_1.
    move => accepting_transcript_2.
    byphoare (_: h = x /\ msg = m /\ ch = e /\ ch' = e' /\ r = z /\ r' = z' ==> _) => //.
    proc; simplify; inline*.
    auto; rewrite /R /R_DL /oget.
    move => &hr [_] [_] [_] [_] [_] _; subst.
    rewrite challenges_differ accepting_transcript_1 accepting_transcript_2 /=.
    have algebra_part1 : (g ^ z{hr} / (g ^ z'{hr}) = m{hr} * x{hr} ^ e{hr} / m{hr} / x{hr} ^ e'{hr}).
      rewrite accepting_transcript_1 accepting_transcript_2.
      rewrite -3!div_def log_gpow -pow_bij 2!log_mul.
      rewrite sub_def -oppfD addA -2!sub_def //.
    have algebra_part2 : (g ^ z{hr} / (g ^ z'{hr}) = x{hr} ^ e{hr} / (x{hr} ^ e'{hr})).
      rewrite algebra_part1.
      rewrite -3!div_def log_gpow -pow_bij log_mul.
      rewrite addC 2!sub_def addC -addA addfN addf0 addC -sub_def //.
    have algebra_part3 : g ^ z{hr} / g ^ z'{hr} = g ^ z{hr} * g ^ -z'{hr}.
      rewrite pow_opp inv_def -div_def 2!log_pow sub_def -mul_pow -pow_pow gpow_log //.
    have ->//: x{hr} = g ^ ((z{hr} - z'{hr}) / (e{hr} - e'{hr})).
      rewrite div_def 2!sub_def -pow_pow -mul_pow -algebra_part3 algebra_part2.
      rewrite -div_def pow_pow 2!log_pow sub_def; algebra.
  qed.

  (* Special honest verifier zero knowledge *)
  lemma schnorr_proof_of_knowledge_shvzk (D<: SigmaTraceDistinguisher) &m:
    Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameIdeal() @ &m : res] = 
    Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameReal() @ &m : res].
  proof.
    move : FDistr.dt_ll FDistr.dt_fu FDistr.dt1E; rewrite /is_full => dt_ll dt_fu dt_supp.
    byequiv => //.
    proc; inline*.
    seq 27 22: ((glob D){1} = (glob D){2} /\ i{1} = 0 /\ x{1} = h{1} /\ x{2} = h{2} /\ to{1} = Some t{2} /\ ={h, w, e}).
    swap{1} 15 -7; swap{2} 12 -5; swap{1} 11 -3; wp.
    (* Let's play with randomness... *)
    rnd (fun z, z - w{1}*e{1}) (fun r, r + w{1}*e{1}).
    rnd; rnd{1}; wp; rnd; skip; progress => //.
    + rewrite mulN1f sub_def -addA oppK (addC _ eL) -sub_def subff addf0 //.
    + rewrite 2!dt_supp //.
    + rewrite dt_fu //.
    + rewrite mulN1f sub_def -addA oppK -sub_def subff addf0 //.
    + algebra.
    + algebra.
    + rewrite mulN1f sub_def -addA oppK mulC mulN1f -sub_def subff addf0 //.
    + rewrite sub_def -addA -sub_def subff addf0 //.
    + rewrite 2!dt_supp //.
    + rewrite dt_fu //.
    + rewrite sub_def -addA (addC _ (w0L * eL)) -sub_def subff addf0 //.
    + algebra.
    + algebra.
    + rewrite sub_def -addA mulC (addC _ (eL * w0L)) -sub_def subff addf0 //.
    seq 2 0 : ((glob D){1} = (glob D){2} /\ ={x, t}); wp.
    while{1} (to{1} = Some t{2}) (i{1}); progress.
    wp; rnd; wp; skip; progress.
    call (_: true); simplify; skip; progress.
  qed.
  (* The above three theorems prove that the Schnorr proof of knowledge is a Sigma protocol *)

end section SchnorrPKSecurity.

print schnorr_proof_of_knowledge_completeness.
print schnorr_proof_of_knowledge_special_soundness.
print schnorr_proof_of_knowledge_shvzk.