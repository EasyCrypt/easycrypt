require import Int.

op wrap_default : int -> int.
op wrap_named : int -> int.
op wrap_local : int -> int.
op box : int -> int.

axiom wrap_defaultE (x : int) : wrap_default x = x + 1.
axiom wrap_namedE (x : int) : wrap_named x = x + 2.
axiom wrap_localE (x : int) : wrap_local x = x + 3.

hint simplify wrap_defaultE.
hint simplify in named: wrap_namedE.

lemma explicit_named_db (x : int) :
  box (wrap_named x) = box (x + 2).
proof.
  simplify hint named.
  trivial.
qed.

lemma activate_named_db (x : int) :
  box (wrap_named x) = box (x + 2).
proof.
  hint +db simplify named.
  simplify.
  trivial.
qed.

lemma deactivate_default_db (x : int) :
  box (wrap_default x) = box (x + 1).
proof.
  hint -db simplify default.
  simplify.
  hint +db simplify default.
  simplify.
  trivial.
qed.

lemma add_remove_clear_local_hints (x : int) :
  box (wrap_local x) = box (x + 3).
proof.
  hint +simplify wrap_localE.
  simplify.
  trivial.
qed.

lemma remove_local_hint (x : int) :
  box (wrap_local x) = box (x + 3).
proof.
  hint +simplify wrap_localE.
  hint -simplify wrap_localE.
  simplify.
  hint +simplify wrap_localE.
  hint clear simplify.
  simplify.
  hint +simplify wrap_localE.
  simplify.
  trivial.
qed.
