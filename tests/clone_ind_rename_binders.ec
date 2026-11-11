(* Overriding a defined inductive predicate by a compatible one whose
   constructor binders are named differently must not crash the
   compatibility check (`EcSubst.rename_flocal`). *)
require import AllCore.

theory T.
  inductive p (n : int) =
  | C x of (n = 2 * x).
end T.

inductive q (n : int) =
| C y of (n = 2 * y).

clone T as U with pred p <- q.

lemma foo (n : int) : q n => exists x, n = 2 * x.
proof. by case=> x ->; exists x. qed.
