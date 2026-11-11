require import Int.

(* [foo]/[bar] are abstract: they have no body, so nothing reduces them
   except the user-reduction rules below. The rules live in a *named* DB
   (not the default one), so kernel conversion never applies them on its
   own -- a goal closes only when [simplify] actually fires the rule.
   This lets [fail (...)] witness that a filtered-out rule does nothing. *)
op foo : int -> int.
op bar : int -> int.
op baz : int -> int.

axiom fooE (x : int) : foo x = x + 1.
axiom barE (x : int) : bar x = x + 2.
axiom bazE (x : int) : baz x = x + 3.

hint simplify in mydb : fooE.
hint simplify in mydb : barE.
hint simplify bazE.            (* default (active) DB *)

(* Include filter: only [foo]-headed rules fire. *)
lemma simplify_include (x : int) :
  foo x = x + 1.
proof. simplify hint mydb +[foo]. done. qed.

(* Exclude filter: every rule except the [bar]-headed ones fires, so
   [foo] still reduces. *)
lemma simplify_exclude (x : int) :
  foo x = x + 1.
proof. simplify hint mydb -[bar]. done. qed.

(* The excluded rule genuinely does nothing: with [foo] filtered out the
   goal cannot be closed, but it can once [foo] is included again. *)
lemma simplify_exclude_disables (x : int) :
  foo x = x + 1.
proof.
  fail (simplify hint mydb -[foo]; done).
  simplify hint mydb +[foo].
  done.
qed.

(* A head filter with no named database filters over the active set
   (the [hint] keyword is mandatory, the database list may be empty). *)
lemma simplify_filter_active_set (x : int) :
  baz x = x + 3.
proof. simplify hint +[baz]. done. qed.

(* Head filters combine with [cbv] the same way. *)
lemma cbv_include (x : int) :
  bar x = x + 2.
proof. cbv hint mydb +[bar]. done. qed.

lemma cbv_exclude_disables (x : int) :
  bar x = x + 2.
proof.
  fail (cbv hint mydb -[bar]; done).
  cbv hint mydb +[bar].
  done.
qed.
