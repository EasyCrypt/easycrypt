require import AllCore.

(* Mode #3: bare ops on a parametric-carrier multi-parameter typeclass.
   The unifier's By-args strategy infers the carrier from the (ground)
   type-class arguments when there is a unique matching instance. *)
type class ['a, 'b] embed = {
  op proj : embed -> 'a
  op inj  : 'b -> embed
  axiom dummy : true
}.

(* Concrete instance: pair (int, bool). *)
op proj_pair (p : int * bool) : int = fst p.
op inj_pair  (b : bool) : int * bool = (0, b).

instance (int, bool) embed as pair_inst with (int * bool)
  op proj = proj_pair
  op inj  = inj_pair.

realize dummy by trivial.

(* Bare ops: the carrier (int * bool) is inferred from the (int, bool)
   embed instance — no explicit tvi needed. *)
op test_bare : int = proj (inj true).

(* Same shape inside a lemma. *)
lemma round_trip (b : bool) : proj (inj b) = (0, b).`1.
proof. by rewrite /inj_pair /proj_pair. qed.

(* Even when the user only constrains the result type, the args of the
   typeclass propagate from the unique matching instance. *)
op test_proj_only (s : int * bool) : int = proj s.

(* And when only the source type is fixed: the carrier and target are
   inferred from the unique embed instance. *)
op test_inj_only (b : bool) : int * bool = inj b.
