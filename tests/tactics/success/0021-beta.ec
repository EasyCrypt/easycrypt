(* Removing library dependencies *)
type 'a cpred = 'a -> bool.
op cpEq (x:'a): 'a cpred = (=) x.

(* Minimal case follows *)
type 'a set.

op mem:'a -> 'a set -> bool.

pred (==) (X1 X2:'a set) = forall x, mem x X1 <=> mem x X2.
axiom set_ext: forall (X1 X2:'a set), X1 == X2 => X1 = X2.

op single:'a -> 'a set.
(* These definitions do not matter for the bug,
   but are good for finishing the proof. *)
(*
axiom mem_single_eq: forall (x:'a),
  mem x (single x).
axiom mem_single_neq: forall (x x':'a),
  x <> x' => !mem x (single x'). *)

op filter:'a cpred -> 'a set -> 'a set.
axiom mem_filter: forall x (p:'a cpred) (X:'a set),
  mem x (filter p X) <=> (mem x X /\ p x).

lemma filter_cpEq_in: forall (x:'a) (X:'a set),
  mem x X => filter (cpEq x) X = single x.
proof strict.
intros=> x X x_in_X.
apply (set_ext <:'a> (filter (cpEq x) X) (single x) _).
intros x'.
rewrite mem_filter.
delta cpEq.
beta.
split.
intros=> [x'_in_X x_x'].
admit.
admit.
save.


