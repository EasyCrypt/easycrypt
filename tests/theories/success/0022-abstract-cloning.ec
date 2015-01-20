(* -------------------------------------------------------------------- *)
abstract theory T.
  axiom L : false.
end T.

clone T as U.

(* -------------------------------------------------------------------- *)
lemma L : false.
proof. by apply U.L. qed.
