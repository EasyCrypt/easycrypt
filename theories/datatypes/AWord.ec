(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int IntExtra IntDiv Real RealExtra.
require import Finite FSet StdRing StdOrder.
(*---*) import RField RealOrder.

type word.

const length:int.
axiom leq0_length: 0 < length.

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
proof. by rewrite ExtEq.fun_ext => x; rewrite ExtEq.fun_ext => y /#. qed.

(** View bitstring as a ring *)
require (*--*) Ring.

instance bring with word
  op rzero = zeros
  op rone  = ones
  op add   = Self.( ^ )
  op mul   = land
  op opp   = lopp

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrK     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrK     by smt
  proof oppr_id   by smt.

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
proof. by rewrite from_to; smt. qed.

(** univ *)

theory Univ.
  (** Keeping this for now so as not to break the interface. Everything should be a list instead... **)
  op univ = image from_int (oflist (List.Iota.iota_ 0  (2^length))).

  lemma mem_univ w: mem univ w.
  proof.
    rewrite /univ imageP; exists (to_int w); rewrite to_from mem_oflist List.Iota.mem_iota /=.
    smt.
  qed.

  lemma card_univ: card univ = 2^length.
  proof.
    rewrite /univ cardE imageE.
    rewrite -(List.perm_eq_size (List.map from_int (elems (oflist (List.Iota.iota_ 0 (2^length)))))).
      rewrite -{1}(List.undup_id (List.map from_int (elems (oflist (List.Iota.iota_ 0 (2^length)))))).
        rewrite List.map_inj_in_uniq 2:uniq_elems // => x y.
        rewrite -!memE !mem_oflist !List.Iota.mem_iota /= => -[le0_x lt_x_2length] [le0_y lt_y_2length] eq_from.
        by rewrite -(from_to_bound x _) // -(from_to_bound y) // eq_from.
      exact/oflistK.
    rewrite List.size_map -(List.perm_eq_size (List.Iota.iota_ 0 (2^length))).
      rewrite -{1}(List.undup_id (List.Iota.iota_ 0 (2^length))) 1:List.Iota.iota_uniq//.
      exact/oflistK.
    by rewrite List.Iota.size_iota; smt. (* excuse the non-linear integer arithmetic *)
  qed.

  lemma finite_univ : is_finite (Pred.predT <:word>).
  proof.
    exists (List.map from_int (List.Iota.iota_ 0 (2^length))); split=> [|x].
      by rewrite List.map_inj_in_uniq 2:List.Iota.iota_uniq// => x y; smt.
    rewrite List.mapP; exists (to_int x)=> //=.
    by rewrite List.Iota.mem_iota /=; smt.
  qed.
end Univ.

theory Dword.
  require import Real Distr.
  require (*--*) Mu_mem.

  op dword: word distr.
  axiom mu_x_def w: mu_x dword w = 1%r/(2^length)%r.
  axiom lossless: weight dword = 1%r.

  lemma in_supp_def w: in_supp w dword.
  proof -strict.
  rewrite /in_supp mu_x_def;smt.
  qed.

  lemma mu_cpMemw X:
    mu dword (mem X)%FSet = (card X)%r / (2^length)%r.
  proof.
    rewrite (Mu_mem.mu_mem X dword (1%r/(2^length)%r)) //.
    by move=> x _; rewrite -/(mu_x _ _) mu_x_def.
  qed.

  require import Dexcepted.

  lemma lossless_restrw X:
    card X < 2^length =>
    weight (dword \ (mem X)) = 1%r.
  proof.
  move=> lt_CX_2sx; rewrite dexcepted_ll /is_lossless -/(weight _) ?lossless // ?mu_cpMemw.
  by rewrite ltr_pdivr_mulr /= lte_fromint // powPos.
  qed.
end Dword.
