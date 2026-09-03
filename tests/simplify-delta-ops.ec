require import AllCore.

(* [g]/[h] are opaque for reduction: [delta] alone never unfolds them
   (and neither does the conversion behind [done]), so a goal that needs
   their body closes only when they are listed in a [delta[...]]
   argument. [f] is transparent and is unfolded by [delta] as usual;
   naming it alone ([delta f], [simplify f]) leaves [g] folded. *)
op f (x : int) = x + 1.
op [opaque] g (x : int) = x + 2.
op [opaque] h (x : int) = x + 3.

(* Opaque, but with an unfold threshold (the [/]): never unfolded by
   [delta] or by conversion, yet unfolded by the [IfApplied] mode that
   [delta f] / [simplify f] use for unlisted operators, provided the
   application reaches the threshold. *)
op [opaque] k  (x : int)   / = x + 5.
op [opaque] k2 (x y : int) / = x + y.

lemma t1 (x : int) : f x + g x = x + 1 + (x + 2).
proof.
  fail (simplify delta; done).
  fail (simplify f; done).
  by simplify delta[g].
qed.

lemma t2 (x : int) : f x + g x + h x = x + 1 + (x + 2) + (x + 3).
proof.
  fail (cbv delta[g]; done).
  by cbv delta[g h].
qed.

lemma t3 (x : int) : f x + g x = x + 1 + (x + 2).
proof.
  fail (delta; done).
  fail (delta f; done).
  by delta[g].
qed.

lemma t4 (x : int) : f x + g x = x + 1 + (x + 2).
proof. by simplify delta[g] hint +core. qed.

(* [delta f]: [f] is forced, [k] unfolds because it is applied to its
   parameter, [g] stays folded. *)
lemma t5 (x : int) : f x + g x + k x = x + 1 + g x + (x + 5).
proof.
  fail (delta; done).
  fail (delta[f]; done).
  by delta f.
qed.

lemma t6 (x : int) : f x + g x + k x = x + 1 + g x + (x + 5).
proof.
  fail (simplify delta; done).
  by simplify f.
qed.

lemma t7 (x : int) : f x + g x + k x = x + 1 + g x + (x + 5).
proof. by cbv f. qed.

(* Below the threshold, [IfApplied] does not fire: [k] unapplied and
   [k2] applied to one of its two parameters stay folded. *)
lemma t8 : k = fun x => x + 5.
proof.
  fail (delta f; done).
  by delta[k].
qed.

lemma t9 (x : int) : k2 x = fun y => x + y.
proof.
  fail (delta f; done).
  by delta[k2].
qed.

lemma t10 (x : int) : k2 x x = x + x.
proof.
  fail (delta; done).
  by delta f.
qed.
