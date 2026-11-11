require import Int.

(* Abstract operators (no body) so only the user-reduction rules below can
   reduce them. Rules headed by these ops are placed in named DBs (not the
   default one) so kernel conversion never applies them implicitly; a goal
   closes only when [simplify] actually fires the rule. That makes the
   [fail (...)] phrases below faithful witnesses that a disabled rule does
   nothing. *)
op foo : int -> int.   (* default DB        *)
op bar : int -> int.   (* named DB [dbA]    *)
op baz : int -> int.   (* named DB [dbB]    *)
op qux : int -> int.   (* added locally     *)

axiom fooE (x : int) : foo x = x + 1.
axiom barE (x : int) : bar x = x + 2.
axiom bazE (x : int) : baz x = x + 3.
axiom quxE (x : int) : qux x = x + 4.

hint simplify fooE.
hint simplify in dbA : barE.
hint simplify in dbB : bazE.

(* --- Named-database selection (E1) ----------------------------------- *)

lemma select_named_db (x : int) :
  bar x = x + 2.
proof. simplify hint dbA. done. qed.

(* Several databases can be selected at once. *)
lemma select_multiple_dbs (x : int) :
  bar x = x + 2 /\ baz x = x + 3.
proof. simplify hint dbA dbB. split; done. qed.

(* Selection *replaces* the active set: naming [dbA] consults only [dbA],
   so a rule from the unselected [dbB] does not fire and its goal cannot
   close until [dbB] is selected too. *)
lemma selection_replaces_active (x : int) :
  baz x = x + 3.
proof.
  fail (simplify hint dbA; done).
  simplify hint dbB.
  done.
qed.

(* Signed [+d] deltas add databases to the active set for this call
   (no unsigned base: a clause is either a selection or deltas). *)
lemma activate_deltas (x : int) :
  bar x = x + 2 /\ baz x = x + 3.
proof. simplify hint +dbA +dbB. split; done. qed.

(* A [-d] delta removes a database; [-dbB] drops [dbB] so its rule no
   longer fires, until it is added again. *)
lemma deactivate_delta (x : int) :
  baz x = x + 3.
proof.
  fail (simplify hint +dbA +dbB -dbB; done).
  simplify hint +dbB.
  done.
qed.

(* Per-call lemma add via [{ ... }] (targets the default DB), without a
   persistent [hint] command. *)
lemma per_call_lemma_add (x : int) :
  qux x = x + 4.
proof.
  fail (simplify; done).
  simplify hint {quxE}.
  done.
qed.

(* --- Activating / deactivating databases ----------------------------- *)

lemma activate_named_db (x : int) :
  bar x = x + 2.
proof.
  hint +dbA.
  simplify.
  done.
qed.

(* Deactivating a previously-activated DB must disable its rules again. *)
lemma deactivate_named_db (x : int) :
  bar x = x + 2.
proof.
  hint +dbA.
  hint -dbA.
  fail (simplify; done).
  hint +dbA.
  simplify.
  done.
qed.

(* --- Local lemma add / remove / clear -------------------------------- *)

lemma add_local_hint (x : int) :
  qux x = x + 4.
proof.
  hint {quxE}.
  simplify.
  done.
qed.

(* [hint clear] drops the local additions, disabling the lemma again. *)
lemma clear_local_hints (x : int) :
  qux x = x + 4.
proof.
  hint {quxE}.
  hint clear.
  fail (simplify; done).
  hint {quxE}.
  simplify.
  done.
qed.

(* --- Scoped application: [with hint cmd (tac)] ----------------------- *)

lemma scoped_with_hint_db (x : int) :
  bar x = x + 2.
proof. with hint +dbA (simplify). done. qed.

lemma scoped_with_hint_lemma (x : int) :
  qux x = x + 4.
proof. with hint {quxE} (simplify). done. qed.

(* The scoped configuration is restored afterwards: the local add applies
   only inside the wrapped tactic. Here the wrapper just runs [split]; the
   resulting subgoals no longer see the added rule, so each one must
   re-add it to close. *)
lemma scoped_with_hint_restores (x : int) :
  qux x = x + 4 /\ qux x = x + 4.
proof.
  with hint {quxE} (split).
  fail (simplify; done).
  hint {quxE}; simplify; done.
  hint {quxE}; simplify; done.
qed.

(* --- Proof-local defaults -------------------------------------------- *)

lemma local_default_db (x : int) :
  bar x = x + 2.
proof.
  hint dbA.
  simplify.
  done.
qed.

lemma scoped_default_db (x : int) :
  bar x = x + 2.
proof. with hint dbA (simplify). done. qed.

lemma local_default_head_filter (x : int) :
  qux x = x + 4.
proof.
  hint {quxE}.
  hint +[qux].
  simplify.
  done.
qed.

(* Clearing the local default reverts to the active set. *)
lemma clear_local_default (x : int) :
  bar x = x + 2.
proof.
  hint dbA.
  hint clear default.
  simplify hint dbA.
  done.
qed.
