require import Option Fun Pred Real Distr List.
(*
  (* FIXME: Countability witness for type bool... *)
  op elts = [true;false].

  op dbool (b : bool) = 1%r/2%r.

  lemma dbool_pos b: 0%r <= dbool b by [].

  lemma dbool_sum: SeriesSum.converge (fun i => dbool (nth witness elts i)) 1%r.
  proof. admit. qed.
*)

op dbool: bool distr.
axiom mu_dbool (p : bool -> bool):
  mu dbool p =   (if p true  then 1%r/2%r else 0%r)
               + (if p false then 1%r/2%r else 0%r).

lemma dbool_pred0: mu dbool pred0 = 0%r.
proof. by rewrite mu_dbool. qed.

lemma dbool_predT: mu dbool predT = 1%r.
proof. by rewrite mu_dbool. qed.

lemma dboolb b: mu dbool (pred1 b) = 1%r/2%r.
proof. by case b; rewrite mu_dbool. qed.

lemma dbool_leq b1 b2:
  (b1 => b2) =>
  mu dbool (pred1 b1) <= mu dbool (pred1 b2).
proof. by case b1; case b2=> //=; rewrite 2!dboolb. qed.
