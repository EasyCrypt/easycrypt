(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int.

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
