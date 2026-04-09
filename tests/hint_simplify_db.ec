require import Int.

op wrap_default : int -> int.
op wrap_named : int -> int.
op box : int -> int.

axiom wrap_defaultE (x : int) : wrap_default x = x + 1.
axiom wrap_namedE (x : int) : wrap_named x = x + 2.

hint simplify wrap_defaultE.
hint simplify in named: wrap_namedE.

lemma wrap_default_simplifies (x : int) :
  box (wrap_default x) = box (x + 1).
proof.
  simplify.
  trivial.
qed.

lemma wrap_named_simplifies (x : int) :
  box (wrap_named x) = box (x + 2).
proof.
  simplify hint named.
  trivial.
qed.
