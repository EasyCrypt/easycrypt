require import AllCore.
require import Hint_simplify_disable_lib.

(* The required file switched the rule of [fE] off for itself only: here
   the rule is active, as exported by its [hint simplify fE]. A file must
   never be able to switch off rules in the files requiring it. *)

lemma rule_active_here : f 0 = 1.
proof. done. qed.

lemma rule_active_slash : f 0 = 1.
proof. by rewrite /=. qed.

(* This file can of course switch it off for itself. *)
hint simplify disable fE.

lemma disabled_here : f 0 = 1.
proof. fail done. rewrite fE. done. qed.
