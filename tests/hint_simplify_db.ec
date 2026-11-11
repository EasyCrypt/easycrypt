require import Int.

(* Abstract operators reduced only by the rules below; the named rule
   lives outside the default DB so closing the goal genuinely depends on
   [simplify] firing the rule (see tests/local_hint_simplify.ec). *)
op wrap_default : int -> int.
op wrap_named : int -> int.

axiom wrap_defaultE (x : int) : wrap_default x = x + 1.
axiom wrap_namedE (x : int) : wrap_named x = x + 2.

hint simplify wrap_defaultE.
hint simplify in named : wrap_namedE.

lemma wrap_default_simplifies (x : int) :
  wrap_default x = x + 1.
proof. simplify. done. qed.

lemma wrap_named_simplifies (x : int) :
  wrap_named x = x + 2.
proof. simplify hint named. done. qed.
