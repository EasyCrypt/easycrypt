(* A theory override `theory B <- T` does not override the items of `B`
   that have a more specific override, whatever the order in which the
   two overrides are given. It used to fail with an assertion failure
   when the more specific override came first, and to report a
   duplicate override otherwise. *)

require import AllCore.

theory Arr.
  type 'a t.
  op get : 'a t -> int -> 'a.
end Arr.

theory Arr2.
  type 'a t.
  op get : 'a t -> int -> 'a.
end Arr2.

abstract theory Base.
  theory A.
    type 'a t.
    op get : 'a t -> int -> 'a.
  end A.

  op k : int.
end Base.

abstract theory Leaf.
  clone import Base as B.

  lemma leaflm (x : int A.t) : A.get x k = A.get x k by done.
end Leaf.

clone Base as B0 with theory A <= Arr.

(* The more specific override first... *)
clone Leaf as L1 with theory B.A <- Arr2, theory B <- B0.

expect "
(* L1.leaflm *)
lemma leaflm: forall (x : int Arr2.t), Arr2.get x B0.k = Arr2.get x B0.k.
" by print lemma L1.leaflm.

(* ... or last. *)
clone Leaf as L2 with theory B <- B0, theory B.A <- Arr2.

expect "
(* L2.leaflm *)
lemma leaflm: forall (x : int Arr2.t), Arr2.get x B0.k = Arr2.get x B0.k.
" by print lemma L2.leaflm.

(* The same holds for an override of a single item. *)
clone Leaf as L3 with theory B <- B0, op B.k <- 0.

expect "
(* L3.leaflm *)
lemma leaflm: forall (x : int Arr.t), Arr.get x 0 = Arr.get x 0.
" by print lemma L3.leaflm.

