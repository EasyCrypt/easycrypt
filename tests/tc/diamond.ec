require import AllCore.

(* Diamond inheritance:
       base
       /  \
      tc1  tc2
       \  /
       tc3
   Verify that ancestors are correctly walked through both branches and
   that the SMT auto-axiom inclusion does not double-pull base axioms. *)

type class base = {
  op zero : base
  axiom zero_idem : forall (x : base), x = x
}.

type class tc1 <: base = {
  op f1 : tc1 -> tc1
  axiom f1_id : forall (x : tc1), f1 x = x
}.

type class tc2 <: base = {
  op f2 : tc2 -> tc2
  axiom f2_id : forall (x : tc2), f2 x = x
}.

(* tc3 inherits from tc1 — diamond closes here only on the tc1 side. *)
type class tc3 <: tc1 = {
  op f3 : tc3 -> tc3
  axiom f3_id : forall (x : tc3), f3 x = x
}.

(* Polymorphic lemma: tc3 carrier must satisfy the parent f1_id (lift=1). *)
lemma f1_via_tc3 ['a <: tc3] (x : 'a) : f1 x = x.
proof. by apply f1_id. qed.

(* SMT auto-includes ancestor axioms — base, tc1, tc3 should all be
   reachable from tc3 without duplication. *)
lemma f3_smt ['a <: tc3] (x : 'a) : f3 x = x.
proof. smt(). qed.

lemma f1_smt ['a <: tc3] (x : 'a) : f1 x = x.
proof. smt(). qed.
