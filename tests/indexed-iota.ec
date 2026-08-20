(* Iota-reduction of match-fix operators and delta-unfolding must
   instantiate the operator's index parameters in BOTH namespaces
   (tindex positions and int-formula occurrences). A tyvars-only
   substitution left the declaration-time idxvar dangling, reducing
   applications at DIFFERENT indices to the same term (false was
   derivable). *)

type {n} 'a ivec = [ INil | ICons of 'a & 'a ivec<:n> ].

op f {n} (d : int) (xs : int ivec<:n>) : int =
  with xs = INil       => n
  with xs = ICons y ys => d.

(* iota lands on the call-site index (cbv path) *)
lemma f5 : f[:5] 0 (INil[:5]<:int>) = 5.
proof. by cbv. qed.

lemma f7 : f[:7] 0 (INil[:7]<:int>) = 7.
proof. by cbv. qed.

(* the old unsound collapse: both sides reduce to their OWN index *)
lemma nocollapse : f[:5] 0 (INil[:5]<:int>) <> f[:7] 0 (INil[:7]<:int>).
proof. by cbv. qed.

(* simplify path (ecReduction iota) *)
lemma f5' : f[:5] 0 (INil[:5]<:int>) = 5.
proof. by simplify. qed.

(* delta-unfold of an indexed plain operator (rewrite /op path) *)
op g {n} ['a] (v : 'a ivec<:n>) : int = n.

lemma gdelta (v : int ivec<:3>) : g v = 3.
proof. by rewrite /g. qed.

(* conversion must not identify distinct index instantiations (the
   applied-operator fast path used to compare heads by path only) *)
op h {n} (x : int) : int.

lemma conv_same : h[:3] 0 = h[:2+1] 0.
proof. trivial. qed.

lemma conv_distinct : h[:3] 0 = h[:5] 0.
proof.
fail by trivial.
abort.
