(* `smt(lemmas)` without `maxlemmas` sends the given lemmas and nothing
   else: a lemma by its path, a theory by all its lemmas, including those
   of its sub-theories. *)
require import AllCore.

op f : int -> int.
op g : int -> int.

theory T.
  axiom fP (x : int) : 0 <= f x.

  theory U.
    axiom gP (x : int) : f x <= g x.
  end U.

  abstract theory A.
    module M = { proc m() : int = { return 0; } }.
    axiom mP : hoare[M.m : true ==> res = 0].
  end A.
end T.

lemma t1 (x : int) : 0 <= f x by smt(T.fP).
lemma t2 (x : int) : 0 <= g x by smt(T.fP T.U.gP).
lemma t3 (x : int) : 0 <= g x by smt(@T).
lemma t4 (x : int) : f x <= g x by smt(@T.U).
