require import AllCore.

module M = {
  proc f(x : int) : int = {
    x <- x * 0;
    return x;
  }
}.

lemma L : hoare[M.f : true ==> true].
proof.
proc.
proc rewrite 1 /=.
abort.

(* -------------------------------------------------------------------- *)
(* [proc rewrite /=] must honor the proof-local simplify context, the way
   [simplify]/[cbv] do.

   Abstract operators (no body) and a rule kept in a named DB, so that
   kernel conversion never reduces [f] on its own: the goals below close
   only if the rule really fired on the *program*. The hint is dropped
   again before the closing [apply], otherwise it is the [apply]'s own
   conversion -- which does see the local context -- that would close the
   goal, and the test would pass even without the rewrite. *)

op f : int -> int.
op g : int -> int.
op P : int -> bool.

axiom fE (x : int) : f x = g x.
axiom Pg : P (g 1).

hint simplify in dbF : fE.

module N = {
  var x : int

  proc p () : unit = {
    x <- f 1;
  }
}.

(* Without the rule, nothing reduces and the postcondition stays on [f]. *)
lemma simpl_needs_the_hint : hoare[N.p : true ==> P N.x].
proof.
proc.
fail (proc rewrite 1 /=; wp; skip => _ _; apply Pg).
abort.

(* [hint +db] activates the database for the rest of the proof. *)
lemma simpl_uses_local_hint_db : hoare[N.p : true ==> P N.x].
proof.
proc.
hint +dbF.
proc rewrite 1 /=.
hint -dbF.
wp; skip => _ _.
apply Pg.
qed.

(* Per-proof lemma addition to the default DB. *)
lemma simpl_uses_local_hint_lemma : hoare[N.p : true ==> P N.x].
proof.
proc.
hint {fE}.
proc rewrite 1 /=.
hint clear.
wp; skip => _ _.
apply Pg.
qed.

(* Scoped form: [with hint ... (proc rewrite /=)]. The context is restored
   on exit, so the closing [apply] cannot benefit from it. *)
lemma simpl_uses_scoped_hint_db : hoare[N.p : true ==> P N.x].
proof.
proc.
with hint +dbF (proc rewrite 1 /=).
wp; skip => _ _.
apply Pg.
qed.

lemma simpl_uses_scoped_hint_lemma : hoare[N.p : true ==> P N.x].
proof.
proc.
with hint {fE} (proc rewrite 1 /=).
wp; skip => _ _.
apply Pg.
qed.
