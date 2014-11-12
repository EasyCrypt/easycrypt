(*** A formalization of pseudo-random functions **)
require import Int.
require import Real.
require import Distr.
require import FSet.
require import FMap.

(** A PRF is a family of functions F from domain D to finite range R
    indexed by a keyspace K equipped with a distribution dK. *)
type D.

type R.

type K.

op dK: K distr.
axiom dK_ll: mu dK True = 1%r.

op F:K -> D -> R.

(** The Real PRF is defined as follows *)
module PRFr = {
  var k:K
  proc init(): unit = { k = $dK; }
  proc f(x:D): R = { return F k x; }
}.

(** Security is expressed with respect to the Random Function defined
    by some uniform distribution on an unspecified subset of R. *)
op uR:R distr.
axiom uR_uf: isuniform uR.

module type PRF = {
  proc init(): unit
  proc f(x:D): R
}.

module type PRFA = {
  proc f(x:D): R
}.

module type Distinguisher(F:PRFA) = {
  proc distinguish(): bool
}.

module IND (F:PRF,D:Distinguisher) = {
  module D = D(F)

  proc main(): bool = {
    var b;

    F.init();
    b = D.distinguish();
    return b;
  }
}.

module PRFi = {
  var m:(D,R) map

  proc init(): unit = { m = FMap.empty; }

  proc f (x:D): R = {
    if (!mem x (dom m)) m.[x] = $uR;
    return (oget m.[x]);
  }
}.

(*** TODO: define notations ***)
(** Advantage of a distinguisher against a PRF oracle F:
      Adv^PRF_F(&m,D) = `|Pr[IND(F,D) @ &m: res] - Pr[IND(PRFi,D) @ &m: res]| **)
(** Advantage of a distinguisher against **the** PRF operator F:
      Adv^PRF_F(&m,D) = `|Pr[IND(PRFr,D) @ &m: res] - Pr[IND(PRFi,D) @ &m: res]| **)

(** Useful lemmas **)
lemma PRFr_init_ll: islossless PRFr.init.
proof. by proc; auto; smt. qed.

lemma PRFr_f_ll: islossless PRFr.f.
proof. by proc. qed.
