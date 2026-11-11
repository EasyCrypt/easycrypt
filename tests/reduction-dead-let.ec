(* A let binding none of whose variables occurs in the body is dropped
   without its value being reduced or evaluated: the value may be a stuck
   term (an opaque operator applied to a variable) that is not a tuple. *)

require import AllCore.

op f : int -> int * int.
op g : int -> int.

(* head reduction: let-tuple on a value that is not a tuple *)
lemma t1 (x : int) : (let (a, b) = f x in 0) = 0.
proof. by move=> /=. qed.

(* head reduction: let-symbol *)
lemma t2 (x : int) : (let a = g x in 0) = 0.
proof. by move=> /=. qed.

(* the binding dies once the body is reduced *)
lemma t3 (x : int) : (let (a, b) = f x in (fun y => 0) a) = 0.
proof. by move=> /=. qed.

(* a chain of bindings only feeding a dead one *)
lemma t4 (x : int) :
  (let a = g x in let (b, c) = f a in let d = g b in 0) = 0.
proof. by move=> /=. qed.

(* the same, in the call-by-value normaliser *)
lemma c1 (x : int) : (let (a, b) = f x in 0) = 0.
proof. by cbv. qed.

lemma c2 (x : int) : (let (a, b) = f x in (fun y => 0) a) = 0.
proof. by cbv. qed.

lemma c3 (x : int) :
  (let a = g x in let (b, c) = f a in let d = g b in 0) = 0.
proof. by cbv. qed.

(* a live binding is still substituted *)
lemma l1 (x : int) : (let (a, b) = (g x, 1) in a + b) = g x + 1.
proof. by move=> /=. qed.

lemma l2 (x : int) : (let (a, b) = (g x, 1) in a + b) = g x + 1.
proof. by cbv. qed.
