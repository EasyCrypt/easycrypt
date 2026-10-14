(* Threading theories through a chain of clones with theory overrides
   `theory B <- B`, when `B` was produced by a clone that overrode its
   sub-theory `A` with `theory A <- Arr`. That sub-theory was cleared:
   each clone that threads `B` gives `theory B.A <- Arr` as well, which
   takes precedence over `theory B <- B` for `B.A`. *)

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

  clone import PreludeT as PR with
    theory B <- B, theory B.A <- Arr.

  clone import RowT as RV with
    theory B <- B, theory B.A <- Arr, theory PR <- PR.

  clone import TopT as T with
    theory B <- B, theory B.A <- Arr, theory PR <- PR, theory RV <- RV.

  expect "
(* Chain.T.top (shorten name: top) *)
lemma top: forall (x : int Arr.t), g x = Arr.get x k + 1.
" by print lemma T.top.
end Chain.

(* With `<=`, the sub-theory is kept, and `theory B <- B` suffices. *)
abstract theory Kept.
  clone import Base as B with theory A <= Arr.
  clone import PreludeT as PR with theory B <- B.
  clone import RowT as RV with theory B <- B, theory PR <- PR.

  expect "
(* Kept.RV.g_def (shorten name: g_def) *)
lemma g_def: forall (x : int Arr.t), g x = Arr.get x k + 1.
" by print lemma RV.g_def.
end Kept.
