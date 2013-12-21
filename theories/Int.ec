require import Logic.

import why3 "int" "Int" 
  (* Il y a un bug dans ecScope il refuse d'avoir deux operateurs avec des 
     types different et la meme syntaxe *)
  op "prefix -" as "[-]".

theory Abs.

  import why3 "int" "Abs"
    op "abs" as "`|_|".

end Abs.
export Abs.

theory Triangle.
  lemma nosmt triangle_inequality (x y z:int):
     `| x - y | <= `| x - z | + `| y - z |
  by [].
end Triangle.

theory Extrema.
  op min (a b:int) = if (a < b) then a else b.

  lemma nosmt min_is_lb a b:
    min a b <= a /\
    min a b <= b
  by [].

  lemma nosmt min_is_glb x a b:
    x <= a => x <= b =>
    x <= min a b
  by [].

  lemma nosmt min_is_extremum a b:
    min a b = a \/ min a b = b
  by [].

(* This is much more satisfying: it defines the notion,
   and proves that it exists and is unique by giving it a
   functional definition. Still, the above definition
   is---probably---more usable.
   Note that the following could be used for iterated versions,
   for example on sets, with a proof that folding the binary min
   over the set fulfills the axioms. *)
(*op min: int -> int -> int.
  axiom min_is_lb: forall a b, min a b <= a /\ min a b <= b.
  axiom min_is_glb: forall x a b, x <= a => x <= b => x <= min a b.
  lemma min_is_extremum: forall a b, min a b = a \/ min a b = b.

  lemma min_def: forall a b,
    min a b = if (a < b) then a else b. *)

  op max (a b:int) = if (a < b) then b else a.

  lemma nosmt max_is_ub a b:
    a <= max a b /\
    b <= max a b
  by [].

  lemma nosmt max_is_lub x a b:
    a <= x => b <= x =>
    max a b <= x
  by [].

  lemma nosmt max_is_extremum a b:
    max a b = a \/ max a b = b
  by [].
end Extrema.
export Extrema.

theory EuclDiv.
  op (/%): int -> int -> int.
  op (%%): int -> int -> int.

  axiom ediv_spec m d:
    d <> 0 =>
    0 <= m %% d < `|d| /\
    m = (m /% d) * d + (m %% d).

  axiom ediv_unique m d q r:
    d <> 0 =>
    0 <= r < `|d| =>
    m = q * d + r =>
    q = m /% d /\ r = m %% d.

  axiom ediv_Mle : forall (m1 m2 d:int), 0 < d => m1 <= m2 => m1/%d <= m2/%d.

  lemma ediv_pos : forall m d, 0 < d => 0 <= m => 0 <= m /%d.
  proof -strict. 
    intros m d Hd Hm.
    apply (Trans _ (0/%d));last apply ediv_Mle;smt.
    elim (ediv_unique 0 d 0 0 _ _ _) => //;smt.
  qed.
end EuclDiv.

export EuclDiv.

theory Induction.
  axiom nosmt induction (p:int -> bool):
    (p 0) =>
    (forall i, 0 <= i => p i => p (i + 1)) =>
    (forall i, 0 <= i => p i).

  lemma nosmt strongInduction (p:int -> bool):
    (forall j, 0 <= j => (forall k, 0 <= k < j => p k) => p j) =>
    (forall i, 0 <= i => p i).
  proof strict.
  by intros hyp i iVal;
     apply (induction (fun i, forall k, 0 <= k <= i => p k) _ _ i); smt.
  qed.
end Induction.

(* Not sure we should use this one *)
theory Power.
  import why3 "int" "Power"
    op "power" as "^".

  lemma Power_pos (x n:int): 0 <= n => 0 < x => 0 < x ^ n.
  proof -strict.
  by intros n_pos x_pos; elim/Induction.induction n n_pos=> //; smt.
  qed.
end Power.
export Power.

lemma mulMle : forall (x1 x2 y1 y2:int),
   0 <= x1 <= x2 => 0 <= y1 <= y2 => x1 * y1 <= x2 * y2.
proof -strict.
 intros x1 x2 y1 y2 Hx Hy.
 apply (Trans _ (x1 * y2)).
 rewrite ?(Comm.Comm x1) CompatOrderMult; smt.
 apply CompatOrderMult;smt.
qed.

theory ForLoop.
  op range: int -> int -> 'a -> (int -> 'a -> 'a) -> 'a.

  axiom range_base i j (st:'a) f:
    j <= i =>
    range i j st f = st.

  axiom range_ind i j (st:'a) f:
    i < j =>
    range i j st f = range (i + 1) j (f i st) f.

  lemma range_ind_lazy i j (st:'a) f:
    i < j =>
    range i j st f = f (j - 1) (range i (j - 1) st f).
  proof strict.
  intros=> h; cut {h}: 0 < j-i by smt.    (* missing gt0_subr *)
  cut: (j-i) = (j-i) by trivial.          (* missing move: on pseudo proof-terms *)
  generalize {2 3}(j-i) => n.             (* missing negative pattern selector *)
  intros=> eq_iBj_n gt0_n; generalize i j eq_iBj_n.
  cut ge0_n: 0 <= n by smt; generalize ge0_n gt0_n st.
  elim/Induction.induction n; first smt.
  intros=> n ge0_n IH _ st i j.
  case (n = 0); first intros=> -> h.
    by (cut ->: j = i+1 by smt); rewrite range_ind ?range_base; smt.
  intros=> nz_n eq_iBj_Sn; rewrite range_ind; first by smt.
  (rewrite IH; first 2 smt); congr => //.
  by rewrite -range_ind; first smt.
  qed.

  (* General result on boolean accumulation *)
  lemma rangeb_forall i j p b:
    ForLoop.range i j b (fun k b, b /\ p k) =
     (b /\ forall k, i <= k < j => p k).
  proof strict.
  case (i < j)=> i_j; last smt.
  pose n := j - i; cut ->: j = n + i by smt.
  by cut: 0 <= n by smt; elim/Induction.induction n; smt.
  qed.

  (* General result on restricting the range *)
  lemma range_restr (i j:int) (base:'a) f:
    0 <= j - i =>
    ForLoop.range i j base (fun k a, if i <= k < j then f k a else a) = ForLoop.range i j base f.
  proof strict.
  intros=> h; case (0 = j - i)=> h2; first smt.
  pose k:= j - i - 1; cut {1 3}->: j = k + i + 1 by smt.
  cut: k < j - i by smt; cut: 0 <= k by smt.
  by elim/Induction.induction k; smt.
  qed.
end ForLoop.
