require import Int.

(* Abstract operators (no body): a goal below closes only if [simplify]
   actually fires the rule compiled from the corresponding hint. *)

(* --- A conjunction registers one rule per conjunct ------------------- *)

op g : int -> int.

axiom gE :
  g 0 = 4 /\ g 1 = 6 /\ g 2 = 2 /\ g 3 = 6 /\
  g 4 = 4 /\ g 5 = 2 /\ g 6 = 4 /\ g 7 = 2.

hint simplify gE.

lemma g_head : g 0 = 4.
proof. simplify. done. qed.

lemma g_middle : g 3 = 6.
proof. simplify. done. qed.

lemma g_last : g 7 = 2.
proof. simplify. done. qed.

lemma g_all :
  g 0 = 4 /\ g 1 = 6 /\ g 2 = 2 /\ g 3 = 6 /\
  g 4 = 4 /\ g 5 = 2 /\ g 6 = 4 /\ g 7 = 2.
proof. simplify. done. qed.

(* --- Conditions distribute over the conjuncts below them ------------- *)

op h : int -> int.

axiom hE (x : int) : (0 < x => h x = x + 1) /\ h 0 = 7.

hint simplify hE.

lemma h_guarded : h 3 = 4.
proof. simplify. done. qed.

(* The guarded rule must not fire when its condition does not hold. *)
lemma h_guard_blocks : h (-1) = 0.
proof. fail (simplify; done). abort.

(* The unguarded conjunct does not mention [x]; the binder is dropped. *)
lemma h_ground : h 0 = 7.
proof. simplify. done. qed.

(* --- A conjunct may carry its own quantifier ------------------------- *)

op p : int -> int.
op q : int -> int.

axiom pqE : (forall (x : int), p x = x + 1) /\ (forall (y : int), q y = y + 2).

hint simplify pqE.

lemma pq_both (n : int) : p n = n + 1 /\ q n = n + 2.
proof. simplify. done. qed.

(* --- A shared binder unused by one conjunct -------------------------- *)

op r : int -> int.
op s : int -> int.

axiom rsE (x y : int) : r x = x + 3 /\ s y = y + 4.

hint simplify rsE.

lemma rs_both (n : int) : r n = n + 3 /\ s n = n + 4.
proof. simplify. done. qed.

(* --- The single-equation form is unaffected -------------------------- *)

op u : int -> int.

axiom uE (x : int) : u x = x + 5.

hint simplify uE.

lemma u_simplifies (n : int) : u n = n + 5.
proof. simplify. done. qed.

(* --- The [eqtrue] option still registers ----------------------------- *)

op t : int -> bool.

axiom tE (x : int) : t x.

hint simplify [eqtrue] tE.

lemma t_simplifies (n : int) : t n.
proof. simplify. done. qed.

(* --- An explicit priority applies to every conjunct ------------------ *)

op v : int -> int.

axiom vE : v 0 = 1 /\ v 1 = 2.

hint simplify vE @10.

lemma v_both : v 0 = 1 /\ v 1 = 2.
proof. simplify. done. qed.

(* --- Cloning replays the conjunction hint ---------------------------- *)

abstract theory T.
  op w : int -> int.

  axiom wE : w 0 = 1 /\ w 1 = 2 /\ w 2 = 3.

  hint simplify wE.
end T.

clone import T as T1.

lemma clone_all : T1.w 0 = 1 /\ T1.w 1 = 2 /\ T1.w 2 = 3.
proof. simplify. done. qed.

(* --- Per-call addition of a conjunction lemma ------------------------ *)

op z : int -> int.

axiom zE : z 0 = 1 /\ z 1 = 2 /\ z 2 = 3.

lemma z_local : z 0 = 1 /\ z 1 = 2 /\ z 2 = 3.
proof.
  fail (simplify; done).
  simplify hint {zE}.
  done.
qed.
