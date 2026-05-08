require import AllCore.
require Subtype.

(* Generic abstract predicates declared outside any section so they
   stay polymorphic instead of being generalized when the section is
   closed.                                                             *)
op P ['c] : int -> 'c -> bool.
op Q ['c] : int -> 'c -> bool.
op R ['o 'i] : 'o -> 'i -> bool.

axiom P_sat ['c] : exists n, P<:'c> n witness.
axiom Q_sat ['c] : exists n, Q<:'c> n witness.
axiom R_sat ['o 'i] : R<:'o, 'i> witness witness.


(* -------------------------------------------------------------------- *)
(* Basic case: subtype inside a section with a single section-declared  *)
(* free type. The subtype must be generalized over [c] at section       *)
(* close so that [val]/[insub] (which gain a [c] tparam) and the type   *)
(* itself stay coherent.                                                *)
(* -------------------------------------------------------------------- *)
theory T1.
section.
declare type c.

subtype carrier = { x : int * c | P x.`1 x.`2 }.

realize inhabited. proof. by have [n hn] := P_sat<:c>; exists (n, witness). qed.

end section.
end T1.

(* After section close, [carrier] is unary. Using it at two distinct
   carrier types in the same lemma produces two distinct types — would
   fail to type-check if [carrier] had stayed monomorphic. *)
lemma test_basic_unary (x : bool T1.carrier) (y : int T1.carrier) :
  T1.val x = (0, witness<:bool>) /\ T1.val y = (1, witness<:int>).
proof. admit. qed.


(* -------------------------------------------------------------------- *)
(* Predicate-only dependency: the carrier mentions no section-declared  *)
(* type, but the predicate does (the polymorphic [Q] is instantiated at *)
(* the section's [c]). The fv collected from the predicate must trigger *)
(* the same generalization.                                             *)
(* -------------------------------------------------------------------- *)
theory T2.
section.
declare type c.

subtype only_pred = { x : int | Q<:c> x witness }.

realize inhabited. proof. exact: Q_sat. qed.

end section.
end T2.

lemma test_pred_dep_unary (x : bool T2.only_pred) (y : int T2.only_pred) :
  T2.val x = 0 /\ T2.val y = 1.
proof.
(* The subtype-cloned [valP] axiom must itself be polymorphic over the
   carrier — instantiating it at two distinct types here would fail to
   type-check if the generalization had not happened. *)
have hx : Q<:bool> (T2.val x) witness by exact: T2.valP.
have hy : Q<:int>  (T2.val y) witness by exact: T2.valP.
admit.
qed.


(* -------------------------------------------------------------------- *)
(* Two nested sections. The subtype is declared in the inner section    *)
(* and depends on free types from BOTH levels. After both closes, it    *)
(* must be generalized over both [outer] and [inner].                   *)
(* -------------------------------------------------------------------- *)
theory T3.
section Outer.
declare type outer.

section Inner.
declare type inner.

subtype pair_carrier = { x : outer * inner | R x.`1 x.`2 }.

realize inhabited.
proof. by exists (witness, witness); exact: R_sat. qed.

end section Inner.
end section Outer.
end T3.

(* Now [pair_carrier] should be binary. *)
lemma test_nested_binary
  (x : (int, bool) T3.pair_carrier)
  (y : (bool, int) T3.pair_carrier)
:
  T3.val x = (0, true) /\ T3.val y = (true, 0).
proof.
(* As in T2, instantiating [valP] at two distinct carrier pairs would
   fail to type-check if the cloned axiom had not been generalized
   over both [outer] and [inner]. *)
have hx : R<:int, bool> (T3.val x).`1 (T3.val x).`2 by exact: T3.valP.
have hy : R<:bool, int> (T3.val y).`1 (T3.val y).`2 by exact: T3.valP.
admit.
qed.
