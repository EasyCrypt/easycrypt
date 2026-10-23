require import AllCore.

(* [hint simplify disable L] switches off the user-reduction rules
   compiled from [L] for the rest of the enclosing theory / section of
   the current file, on every simplification path ([simplify], [/=],
   [done], [trivial], [auto], conversion); [hint simplify enable L]
   switches them back on. Both are independent from [hint simplify L],
   which feeds the (exported) database. The operators are abstract, so
   only the rules can reduce them: a goal closes only when a rule
   actually fires. See hint_simplify_disable_locality.ec for the
   file-locality of these switches. *)

op f : int -> int.
op g : int -> int.
op h : int -> int.

axiom fE (x : int) : f x = x + 1.
axiom gE (x : int) : g x = x + 2.
axiom hE (x : int) : h x = x + 3.

hint simplify fE.
hint simplify gE.
hint simplify in mydb : hE.

lemma before : f 0 = 1 /\ g 0 = 2.
proof. done. qed.

hint simplify disable fE.

(* [f] no longer reduces, whatever the path ... *)
lemma disabled_simplify : f 0 = 1.
proof. simplify. rewrite fE. done. qed.

lemma disabled_slash : f 0 = 1.
proof. rewrite /=. rewrite fE. done. qed.

lemma disabled_done : f 0 = 1.
proof. fail done. rewrite fE. done. qed.

lemma disabled_trivial : f 0 = 1.
proof. trivial. rewrite fE. done. qed.

lemma disabled_auto : f 0 = 1.
proof. auto. rewrite fE. done. qed.

lemma disabled_apply : f 0 = 1.
proof. fail (apply eq_refl). rewrite fE. done. qed.

(* ... while the other rules still do. *)
lemma disabled_other : g 0 = 2.
proof. done. qed.

(* An explicit per-call or proof-local addition brings the rule back for
   that call / proof only. *)
lemma explicit_call : f 0 = 1.
proof. simplify hint {fE}. done. qed.

lemma explicit_local : f 0 = 1.
proof. hint {fE}. done. qed.

lemma explicit_local_gone : f 0 = 1.
proof. fail done. rewrite fE. done. qed.

(* Adding the lemma to the database again does not switch it back on:
   the switch and the database content are independent. *)
hint simplify fE.

lemma readded_still_disabled : f 0 = 1.
proof. fail done. rewrite fE. done. qed.

(* [enable] does. *)
hint simplify enable fE.

lemma enabled : f 0 = 1.
proof. done. qed.

(* Several lemmas at once. *)
hint simplify disable fE, gE.

lemma disabled_both : f 0 = 1 /\ g 0 = 2.
proof. fail done. rewrite fE gE. done. qed.

hint simplify enable fE, gE.

lemma enabled_both : f 0 = 1 /\ g 0 = 2.
proof. done. qed.

(* Named databases. *)
lemma named_before : h 0 = 3.
proof. simplify hint mydb. done. qed.

hint simplify in mydb : disable hE.

lemma named_disabled : h 0 = 3.
proof. fail (simplify hint mydb; done). rewrite hE. done. qed.

hint simplify in mydb : enable hE.

lemma named_enabled : h 0 = 3.
proof. simplify hint mydb. done. qed.

(* A switch made inside a theory ends with the theory. *)
theory T.
  hint simplify disable fE.

  lemma in_theory : f 0 = 1.
  proof. fail done. rewrite fE. done. qed.
end T.

lemma after_theory : f 0 = 1.
proof. done. qed.

(* Likewise for sections. *)
section.
  hint simplify disable gE.

  lemma in_section : g 0 = 2.
  proof. fail done. rewrite gE. done. qed.
end section.

lemma after_section : g 0 = 2.
proof. done. qed.

(* A switch made at top level is not undone by closing a theory. *)
hint simplify disable fE.

theory U.
  lemma in_theory_still_disabled : f 0 = 1.
  proof. fail done. rewrite fE. done. qed.
end U.

lemma after_theory_still_disabled : f 0 = 1.
proof. fail done. rewrite fE. done. qed.

(* An [enable] inside a theory ends with the theory as well. *)
theory V.
  hint simplify enable fE.

  lemma in_theory_enabled : f 0 = 1.
  proof. done. qed.
end V.

lemma after_theory_disabled_again : f 0 = 1.
proof. fail done. rewrite fE. done. qed.
