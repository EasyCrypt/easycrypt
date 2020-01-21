(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* A formalisation of generic Sigma protocols *)
require import DBool.
require import Int.
require import Distr.

theory SigmaProtocol.
  type statement.
  type witness. (* witness to the statement *)
  type message.
  type secret. (* this may relate to the message *)
  type challenge.
  type response.

  type transcript = message * challenge * response.
(*   op dm: message   distr. *)
  op de: challenge distr.
(*   op dz: response  distr. *)

  (*
    (x, w) ← gen() should be such that
      - (x, w) in R
      - |w| <= poly(|x|) ← HOW?
  *)
  op slen: int.
  op wlen: int.
  op R (x: statement) (w: witness): bool.

  axiom slen_pos: 0 < slen.
  axiom wlen_pos: 0 < wlen.

  module type SigmaScheme = {
    proc gen() : statement * witness
    proc commit(x: statement, w: witness) : message * secret
    proc test(x: statement, m: message) : challenge
    proc respond(sw: statement * witness, ms: message * secret, e: challenge) : response
    proc verify(x: statement, m: message, e: challenge, z: response) : bool
  }.

  module type SigmaAlgorithms = {
    proc soundness(x: statement, m: message, e: challenge, z: response, e': challenge, z': response) : witness option
    proc simulate(x: statement, e: challenge) : message * challenge * response
  }.

  module Completeness (S: SigmaScheme) = {
    proc main(x: statement, w: witness) : bool = {
      var e, m, s, z, b;

      (m, s) <@ S.commit(x, w);
      e      <@ S.test(x, m);
      z      <@ S.respond((x, w), (m, s), e);
      b      <@ S.verify(x, m, e, z);

      return b;
    }
  }.

  module Run (S: SigmaScheme) = {
    proc main() : statement * message * challenge * response = {
      var x, w, m, s, e, z;

      (x, w) <@ S.gen();
      (m, s) <@ S.commit(x, w);
      e      <@ S.test(x, m);
      z      <@ S.respond((x, w), (m, s), e);

      return (x, m, e, z);
    }
  }.
  
  (*
    Special soundness is supposed to be a PPTA.
    S(m, e, z, e', z') → (x, w) in R
  *)
  module SpecialSoundnessExperiment (S: SigmaScheme, A: SigmaAlgorithms) = {
    proc main(x: statement, m: message, e: challenge, z: response, e': challenge, z': response) : witness option = {
      var s, sto, w, r, v, v';

      sto <@ A.soundness(x, m, e, z, e', z');
      if (e <> e' /\ sto <> None) {
        w  <- oget sto;
        r  <- R x w;
        v  <@ S.verify(x, m, e , z  );
        v' <@ S.verify(x, m, e', z' );
        if (r /\ v /\ v') {
          s <- Some(w);
        } else {
          s <- None;
        }
      } else {
        s <- None;
      }

      return s;
    }
  }.

  (*
    The simulator M is a PPTA that generates
    Sigma Protocol transcripts from (x, e).
    
    M(x, e) → (a, e, z)
    M'(x)   → (a, e, z) more strict but simulatable -- usless to implement?
  *)
  module SpecialHVZKExperiment (S: SigmaScheme, A: SigmaAlgorithms) = {
    proc main(x: statement, e: challenge) : (message * challenge * response) option = {
      var m, z, v, to;

      (m, e, z) <@ A.simulate(x, e);
      v <@ S.verify(x, m, e, z);
      if (v) {
        to <- Some(m, e, z);
      } else {
        to <- None;
      }

      return to;
    }
  }.

  (*
   * Trace is the triple (message, challenge, response).
   * Conventionally, this distinguisher shall say true if the triplet comes
   * from a real execution, otherwise false for an ideal execution.
   *)
  module type SigmaTraceDistinguisher = {
    proc distinguish(x: statement, t: transcript) : bool
  }.

  module SimulateHonestVerifier (S: SigmaScheme, A: SigmaAlgorithms, D: SigmaTraceDistinguisher) = {
    proc gameIdeal() : bool = {
      var b, e, i, m, s, t, to, x, w;

      (x, w) <@ S.gen();
      (m, s) <@ S.commit(x, w);
      e      <$ de;
      to     <@ SpecialHVZKExperiment(S, A).main(x, e);
      i      <- 0; (* rubbish to circumvent some limits of the while/unroll tactic. *)
      while (to = None) {
        to <@ SpecialHVZKExperiment(S, A).main(x, e);
        i  <- i + 1;
      }
      t <- oget to;
      b <@ D.distinguish(x, t);

      return b;
    }

    proc gameReal() : bool = {
      var b, t, m, e, z, x;

      (x, m, e, z) <@ Run(S).main();
      t <- (m, e, z);
      b <@ D.distinguish(x, t);

      return b;
    }
    
    proc main() : bool = {
      var b, b';
      
      b <$ {0,1};
      if (b) {
        b' <@ gameIdeal();
      } else {
        b' <@ gameReal();
      }
      
      return (b' = b);
    }
  }.

end SigmaProtocol.
