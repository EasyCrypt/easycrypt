(* A theory override `theory B <- T` maps each item of `B` to the item
   with the same name in `T`. When `T` was itself produced by a clone
   that overrode one of its sub-theories with `theory A <- U`, that
   sub-theory was cleared, and the items of `B.A` used to have no
   target. The cloning now leaves an alias `theory A = U` in place of a
   theory that has been cleared, and theory overrides follow it. *)

require import AllCore.

theory Arr.
  type 'a t.
  op get : 'a t -> int -> 'a.
end Arr.

abstract theory Base.
  theory A.
    type 'a t.
    op get : 'a t -> int -> 'a.
  end A.

  op k : int.
end Base.

abstract theory Leaf.
  clone import Base as B.

  axiom leafax (x : int A.t) : A.get x k = A.get x k.
  lemma leaflm (x : int A.t) : A.get x k = A.get x k by done.
end Leaf.

(* -------------------------------------------------------------------- *)
abstract theory Cleared.
  clone import Base as B with theory A <- Arr.

  expect "
theory B.
  (* no import *) theory A = Arr.
  
  (* import *) op k : int.
end B.
" by print theory B.

  (* `B.A` names `Arr` *)
  op z (x : int B.A.t) : int Arr.t = x.

  clone Leaf as L with theory B <- B.

  expect "
(* Cleared.L.leaflm (shorten name: L.leaflm) *)
lemma leaflm: forall (x : int Arr.t), Arr.get x k = Arr.get x k.
" by print lemma L.leaflm.
end Cleared.

(* -------------------------------------------------------------------- *)
(* With `<=`, the sub-theory is kept, and the result is the same. *)
abstract theory Kept.
  clone import Base as B with theory A <= Arr.
  clone Leaf as L with theory B <- B proof *.
  realize leafax by done.

  expect "
(* Kept.L.leaflm (shorten name: L.leaflm) *)
lemma leaflm: forall (x : int Arr.t), Arr.get x k = Arr.get x k.
" by print lemma L.leaflm.
end Kept.

(* -------------------------------------------------------------------- *)
(* Threading theories through a chain of clones. *)
abstract theory PreludeT.
  clone import Base as B.

  op f (x : int A.t) = A.get x k.
  lemma f_def x : f x = A.get x k by done.
end PreludeT.

abstract theory RowT.
  clone import Base as B.
  clone import PreludeT as PR with theory B <- B.

  op g (x : int A.t) = PR.f x + 1.
  lemma g_def x : g x = A.get x k + 1 by rewrite /g PR.f_def.
end RowT.

abstract theory TopT.
  clone import Base as B.
  clone import PreludeT as PR with theory B <- B.
  clone import RowT as RV with theory B <- B, theory PR <- PR.

  lemma top x : RV.g x = A.get x k + 1 by apply RV.g_def.
end TopT.

abstract theory Chain.
  clone import Base as B with theory A <- Arr.
  clone import PreludeT as PR with theory B <- B.
  clone import RowT as RV with theory B <- B, theory PR <- PR.
  clone import TopT as T with theory B <- B, theory PR <- PR, theory RV <- RV.

  expect "
(* Chain.T.top (shorten name: top) *)
lemma top: forall (x : int Arr.t), g x = Arr.get x k + 1.
" by print lemma T.top.
end Chain.

(* Cloning a theory with aliases: they point into the new theory, not
   into `Chain` (they would be printed `Chain.B` and `Chain.PR`). *)
clone Chain as C with op B.k <- 3.

expect "
theory RV.
  (* no import *) theory B = B.
  
  (* no import *) theory PR = PR.
  
  (* import *) op g (x : int Arr.t) : int = PR.f x + 1.
  
  (* import *) lemma g_def: forall (x : int Arr.t), g x = Arr.get x 3 + 1.
end RV.
" by print theory C.RV.
