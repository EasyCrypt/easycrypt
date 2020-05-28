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
    w <$ FDistr.dt;
    if (w = F.zero) { (* A loop would be better, however the support for while loops is poor *)
      w <- -F.one;
    }
    h <- g^w;
    return (h, w);
  }

  proc commit(h: statement, w: witness) : message * secret = {
    var r, a;
    r <$ FDistr.dt;
    a <- g^r;
    return (a, r);
  }

  proc test(h: statement, a: message) : challenge = {
    var e;
    e <$ FDistr.dt;
    return e;
  }

  proc respond(sw: statement * witness, ms: message * secret, e: challenge) : response = {
    var z, w, r;
    w <- snd sw;
    r <- snd ms;
    z <- r + e*w;
    return z;
  }

  proc verify(h: statement, a: message, e: challenge, z: response) : bool = {
    var v, v';
    v <- a*(h^e);
    v' <- g^z;
    return (v = v');
  }
}.

module SchnorrPKAlgorithms : SigmaAlgorithms = {
  proc soundness(h: statement, a: message, e: challenge, z: response, e': challenge, z': response) : witness option = {
    var sto, w, v, v';

    v  <- (g^z  = a*(h^e ));
    v' <- (g^z' = a*(h^e'));
    if (e <> e' /\ v /\ v') {
      w <- (z - z') / (e - e');
      sto <- Some(w);
    } else {
      sto <- None;
    }

    return sto;
  }

  proc simulate(h: statement, e: challenge) : message * challenge * response = {
    var a, z;

    z  <$ FDistr.dt;
    a  <- (g^z) * (h^(-e));

    return (a, e, z);
  }
}.

section SchnorrPKSecurity.
  (* Completeness *)
  lemma schnorr_proof_of_knowledge_completeness_ll:
    islossless Completeness(SchnorrPK).main.
  proof. by islossless; apply FDistr.dt_ll. qed.

  lemma schnorr_proof_of_knowledge_completeness h w' &m:
    R h w' =>
    Pr[Completeness(SchnorrPK).main(h, w') @ &m : res] = 1%r.
  proof.
    rewrite /R /R_DL; move => sigmarel.
    byphoare (_: h = x /\ w' = w ==> _) => //; rewrite sigmarel.
    proc; inline*; swap 3 -2; swap 8 -7.
    wp; rewrite /snd /=; auto => &hr />.
    rewrite FDistr.dt_ll => /> *; algebra.
  qed.

  (* Special soundness *)
  lemma schnorr_proof_of_knowledge_special_soundness (h: statement) msg ch ch' r r' &m:
    ch <> ch' =>
    g^r  = msg*(h^ch ) =>
    g^r' = msg*(h^ch') =>
    Pr[SpecialSoundnessExperiment(SchnorrPK, SchnorrPKAlgorithms).main(h, msg, ch, r, ch', r') @ &m : (res <> None /\ R h (oget res))] = 1%r.
  proof.
    move => challenges_differ
            accepting_transcript_1
            accepting_transcript_2.
    byphoare (_: h = x /\ msg = m /\ ch = e /\ ch' = e' /\ r = z /\ r' = z' ==> _) => //.
    proc; simplify; inline*.
    auto; rewrite /R /R_DL /oget => &hr /> ? 2!-> /=.
    rewrite F.div_def -pow_pow F.sub_def -mul_pow pow_opp log_bij.
    rewrite accepting_transcript_1 accepting_transcript_2 !(log_gpow, log_pow, log_mul, inv_def). 
    by field; apply: contra H => heq; ring heq.
  qed.

  (* Special honest verifier zero knowledge *)
  lemma schnorr_proof_of_knowledge_shvzk (D<: SigmaTraceDistinguisher) &m:
    Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameIdeal() @ &m : res] = 
    Pr[SimulateHonestVerifier(SchnorrPK, SchnorrPKAlgorithms, D).gameReal() @ &m : res].
  proof.
  (*  move : FDistr.dt_ll FDistr.dt_fu FDistr.dt1E; rewrite /is_full => dt_ll dt_fu dt_supp. *)
    byequiv => //.
    proc; inline*.
    seq 27 22: ((glob D){1} = (glob D){2} /\ i{1} = 0 /\ x{1} = h{1} /\ x{2} = h{2} /\ 
                 to{1} = Some t{2} /\ ={h, w, e}).
    + swap{1} 15 -7; swap{2} 12 -5; swap{1} 11 -3; wp.
      (* Let's play with randomness... *)
      rnd (fun z, z - w{1}*e{1}) (fun r, r + w{1}*e{1}).
      by seq 2 2 : (#pre  /\ ={w0}); auto => />; progress;algebra.
    by call (_:true); rcondf{1} 1; auto.
  qed.
  (* The above three theorems prove that the Schnorr proof of knowledge is a Sigma protocol *)

end section SchnorrPKSecurity.

print schnorr_proof_of_knowledge_completeness.
print schnorr_proof_of_knowledge_special_soundness.
print schnorr_proof_of_knowledge_shvzk.
