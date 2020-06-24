(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdOrder StdBigop.
require (*--*) Bigop.
(*---*) import IntID IntOrder Bigint.

(* -------------------------------------------------------------------- *)
type xint = [N of int | Inf].

(* -------------------------------------------------------------------- *)
abbrev ('0) = N 0.
abbrev ('1) = N 1.

op xadd (x y : xint) =
  with x = N x, y = N y => N (x + y)
  with x = N _, y = Inf => Inf
  with x = Inf, y = N _ => Inf
  with x = Inf, y = Inf => Inf.

op xmul (x : xint) (y : xint) =
  with x = N x, y = N y => N (x * y)
  with x = N _, y = Inf => Inf
  with x = Inf, y = N _ => Inf
  with x = Inf, y = Inf => Inf.

abbrev ( +  ) = xadd.
abbrev ( *  ) = xmul.
abbrev ( ** ) = fun (c : int) (x : xint) => N c * x.

(* -------------------------------------------------------------------- *)
lemma add0x : left_id '0 xadd.
proof. by case. qed.

lemma addx0 : right_id '0 xadd.
proof. by case. qed.

lemma addxA : associative xadd.
proof. by case=> [x|] [y|] [z|] => //=; rewrite addrA. qed.

lemma addxC : commutative xadd.
proof. by case=> [x|] [y|] => //=; rewrite addrC. qed.

(* -------------------------------------------------------------------- *)
lemma mul1x : left_id '1 xmul.
proof. by case. qed.

lemma mulx1 : right_id '1 xmul.
proof. by case. qed.

lemma mulxA : associative xmul.
proof. by case=> [x|] [y|] [z|] => //=; rewrite mulrA. qed.

lemma mulxC : commutative xmul.
proof. by case=> [x|] [y|] => //=; rewrite mulrC. qed.

(* -------------------------------------------------------------------- *)
op xle (x y : xint) =
  with x = N x, y = N y => (x <= y)
  with x = N x, y = Inf => true
  with x = Inf, y = N y => false
  with x = Inf, y = Inf => true.

abbrev (<=) = xle.

lemma lexx : reflexive (<=).
proof. by case. qed.

lemma lex_anti (x y : xint) : x <= y <= x => x = y.
proof. by case: x y => [x|] [y|] //=; apply: ler_anti. qed.

lemma lex_trans : transitive (<=).
proof. by case=> [x|] [y|] [z|] //=; apply: ler_trans. qed.

lemma lexInf (x : xint) : x <= Inf.
proof. by case: x. qed.

(* -------------------------------------------------------------------- *)
theory Bigxint.
clone include Bigop
  with type t <- xint,
         op Support.idm <- ('0),
         op Support.(+) <- xadd
  proof *.

realize Support.Axioms.addmA by exact/addxA.
realize Support.Axioms.addmC by exact/addxC.
realize Support.Axioms.add0m by exact/add0x.

lemma nosmt big_morph_N (P : 'a -> bool) (f : 'a -> int) s:
  big P (fun i => N (f i)) s = N (BIA.big P (fun i => f i) s).
proof.
elim: s => [|x s ih] //=.
by rewrite !(big_cons, BIA.big_cons) ih /=; case: (P x).
qed.
end Bigxint.
