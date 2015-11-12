(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int.

(* -------------------------------------------------------------------- *)
lemma lt0n n : (0 <= n) => (0 < n <=> n <> 0).
proof. by rewrite ltz_def => ->. qed.

(* -------------------------------------------------------------------- *)
op b2i (b : bool) = b ? 1 : 0.

lemma b2i0 : b2i false = 0. proof. by []. qed.
lemma b2i1 : b2i true  = 1. proof. by []. qed.

lemma b2i_or b1 b2: b2i (b1 \/ b2) = b2i b1 + b2i b2 - b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|] //=; rewrite oppz0. qed.

lemma b2i_and b1 b2: b2i (b1 /\ b2) = b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|]. qed.

lemma le_b2i b1 b2: (b1 => b2) <=> (b2i b1 <= b2i b2).
proof. by case: b1 b2 => [|] [|]. qed.

lemma b2i_ge0 b: 0 <= b2i b.
proof. by case: b. qed.

lemma b2i_le1 b: b2i b <= 1.
proof. by case: b. qed.

(* -------------------------------------------------------------------- *)
theory IterOp.
  op iter ['a] : int -> ('a -> 'a) -> 'a -> 'a.

  axiom iter0 ['a] n opr (x : 'a): n <= 0 => iter n opr x = x.
  axiom iterS ['a] n opr (x : 'a): 0 <= n => iter (n+1) opr x = opr (iter n opr x).

  lemma iterSr n opr (x : 'a): 0 <= n => iter (n + 1) opr x = iter n opr (opr x).
  proof. by elim/Induction.induction n; smt. qed.

  op iteri ['a] : int -> (int -> 'a -> 'a) -> 'a -> 'a.

  axiom iteri0 ['a] n opr (x : 'a): n <= 0 => iteri n opr x  = x.
  axiom iteriS ['a] n opr (x : 'a): 0 <= n => iteri (n+1) opr x = opr n (iteri n opr x).

  op iterop ['a] (n : int) opr (x z : 'a) : 'a =
    let f = fun i y, if i <= 0 then x else opr x y in
    iteri n f z.

  lemma iterop0 ['a] (n : int) opr (x z : 'a): n <= 0 =>
    iterop n opr x z = z.
  proof. by move=> le0_n; rewrite /iterop /= iteri0. qed.

  lemma iterop1 ['a] opr (x z : 'a): iterop 1 opr x z = x.
  proof. by rewrite /iterop /= (iteriS 0). qed.

  lemma iteropS ['a] (n : int) opr (x z : 'a): 0 <= n =>
    iterop (n+1) opr x z = iter n (opr x) x.
  proof.
    rewrite /iterop; elim n=> /=.
    + by rewrite iter0 // (iteriS 0).
    + move=> i ge0_i ih; rewrite iteriS 1:smt /= ih.
      by rewrite -(iterS _ (opr x)) //; cut ->: ! (i+1 <= 0) by smt.
  qed.
end IterOp.

export IterOp.
