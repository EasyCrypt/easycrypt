(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

require Int.
require import FSet.

type word.

const length:int.
axiom leq0_length: Int.(<=) 0 length.

op zeros: word.
op ones: word.

op ( ^ ): word -> word -> word.
op land : word -> word -> word.
op lopp (x:word) = x.

axiom ones_neq0 : ones <> zeros.

axiom xorwA (w1 w2 w3:word):
  w1 ^ (w2 ^ w3) = (w1 ^ w2) ^ w3.
axiom xorwC (w1 w2:word):
  w1 ^ w2 = w2 ^ w1.
axiom xor0w x: zeros ^ x = x.
axiom xorwK (w:word):
  w ^ w = zeros.

lemma nosmt xorw0 (w:word): w ^ zeros = w
by [].

lemma nosmt xorNw (x:word): (lopp x) ^ x = zeros
by [].

axiom landwA x y z: land x (land y z) = land (land x y) z.
axiom landwC x y: land x y = land y x.
axiom land1w x: land ones x = x.
axiom landwDl (x y z:word): land (x ^ y) z = land x z ^ land y z.
axiom landI (x:word): land x x = x.

lemma subwE : ( ^ ) = fun (x y: word), x ^ lopp y.
proof.
  rewrite -ExtEq.fun_ext => x; rewrite -ExtEq.fun_ext => y; smt.
qed.

(** View bitstring as a group *)
clone export Ring.R as Rw with
  type ring <- word,
  op zeror <- zeros,
  op oner  <- ones,
  op ( + ) <- ( ^ ),
  op ([-]) <- lopp,
  op ( * ) <- land,
  op ( - ) <- ( ^ )
  proof * by smt.

require import AlgTactic.

instance boolean_ring with word
  op rzero = zeros
  op rone  = ones
  op add   = ( ^ )
  op opp   = lopp 
  op mul   = land

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrrN    by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof oppE      by smt 
  proof bmulrI    by smt.

require export ABitstring.
op to_bits: word -> bitstring.
op from_bits: bitstring -> word.

axiom length_to_bits w:
  `|to_bits w| = length.
axiom can_from_to w:
  from_bits (to_bits w) = w.
axiom pcan_to_from (b:bitstring):
  `|b| = length =>
  to_bits (from_bits b) = b.

(** Conversion with int *)
import Int.
op to_int   : word -> int.
op from_int : int -> word.

axiom to_from w: from_int (to_int w) = w.
axiom from_to i: to_int (from_int i) = i %% 2^length.

lemma from_to_bound i:
   0 <= i < 2^length =>
   to_int (from_int i) = i.
proof -strict.
 rewrite from_to.
 intros H.
 elim (EuclDiv.ediv_unique i (2^length) 0 i _ _ _) => //;first 2 smt.
 by intros _ <-.
qed.

theory Dword.
  require import Distr.
  require import Real.

  op dword: word distr.
  axiom mu_x_def w: mu_x dword w = 1%r/(2^length)%r.
  axiom lossless: weight dword = 1%r.

  lemma in_supp_def w: in_supp w dword.
  proof -strict.
  rewrite /in_supp mu_x_def;smt.
  qed.

  lemma mu_cpMemw X:
    mu dword (cpMem X) = (card X)%r / (2^length)%r.
  proof -strict.
  by rewrite (mu_cpMem _ _ (1%r/(2^length)%r))=> // x;
     rewrite mu_x_def.
  qed.

  import FSet.Dexcepted.
  lemma lossless_restrw X:
    card X < 2^length =>
    weight (dword \ X) = 1%r.
  proof -strict.
  intros=> card_X; rewrite lossless_restr ?lossless // ?mu_cpMemw;
  cut <-: (forall x y, x * (1%r / y) = x / y) by smt;
  apply (real_lt_trans _ ((2^length)%r* (1%r/(2^length)%r)) _); last smt.
  apply mulrM; last by rewrite from_intM.
  smt.
  qed.
end Dword.
