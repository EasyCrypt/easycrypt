(* -------------------------------------------------------------------- *)
abstract theory Foo.
  type t.

  theory I.
    axiom irrelevant: forall (x y : t), x = y.
  end I.
end Foo.

clone Foo as Goo with
  type t <- unit
  proof I.* by smt.

(* -------------------------------------------------------------------- *)
abstract theory T.
  axiom L : false.
end T.

clone T as U.

(* -------------------------------------------------------------------- *)
lemma L : false.
proof. by apply U.L. qed.

