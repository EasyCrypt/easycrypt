require import AllCore.

(* Companion of hint_simplify_disable_locality.ec, which requires this
   file. The rule of [fE] is exported ([hint simplify] is a theory item);
   switching it off is not: it only holds for the rest of *this* file. *)

op f : int -> int.

axiom fE (x : int) : f x = x + 1.

hint simplify fE.

lemma exported : f 0 = 1.
proof. done. qed.

hint simplify disable fE.

lemma disabled_here : f 0 = 1.
proof. fail done. rewrite fE. done. qed.
