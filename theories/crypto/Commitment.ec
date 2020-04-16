(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* A formalisation of generic commitment schemes *)
require import DBool.

theory CommitmentProtocol.
  type value.
  type message.
  type commitment.
  type openingkey.

  module type CommitmentScheme = {
    proc gen() : value
    proc commit(x: value, m: message) : commitment * openingkey
    proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
  }.

  module Correctness (S:CommitmentScheme) = {
    proc main(m: message) : bool = {
      var x, c, d, b;

      x      <@ S.gen();
      (c, d) <@ S.commit(x, m);
      b      <@ S.verify(x, m, c, d);

      return b;
    }
  }.

  (*
    Hiding: The commitment c shall not reveal (almost) anything about the message m.
  *)
  module type Unhider = {
    proc choose(x: value) : message * message
    proc guess(c: commitment) : bool
  }.

  module HidingExperiment (S:CommitmentScheme, U:Unhider) = {
    proc main() : bool = {
      var b, b', m0, m1, x, c, d;

      x        <@ S.gen();
      (m0, m1) <@ U.choose(x);
      b        <$ {0,1};
      (c, d)   <@ S.commit(x, b ? m1 : m0);
      b'       <@ U.guess(c);

      return (b = b');
    }
  }.

  (*
    Hard to generate a commitment of two different messages.
    With only x, a binder (whatever run by the committer or the receiver)
    shall not be able to produce two different messages such that
    both verify with the same commitment.
  *)
  module type Binder = {
    proc bind(x: value) : commitment * message * openingkey * message * openingkey
  }.

  module BindingExperiment (S:CommitmentScheme, B:Binder) = {
    proc main() : bool = {
      var x, c, m, m', d, d', v, v';

      x                 <@ S.gen();
      (c, m, d, m', d') <@ B.bind(x);
      v                 <@ S.verify(x, m , c, d );
      v'                <@ S.verify(x, m', c, d');

      return v /\ v' /\ (m <> m');
    }
  }.
end CommitmentProtocol.
