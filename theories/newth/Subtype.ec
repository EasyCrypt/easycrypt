(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun.
require import Option.

(* -------------------------------------------------------------------- *)
(* This theory defines the subtype [sT] of [T] defined as {x : T | P x} *)
(* where P is a predicate over T. This subtype is defined via an        *)
(* axiomatization of an inversible partial projection from [T] to [sT]  *)
(* that respects [P].                                                   *)
(*                                                                      *)
(* Injection from [sT] to [T] and (partial) projection of [T] to [sT]   *)
(*    val   == generic injection from [sT] to [T]                       *)
(*    insub == generic partial projection from [T] to [sT]              *)
(*                                                                      *)
(*    {x : T | P x} and [sT] are in bijection via val/insub.            *)
(*       1. insub x = None                  if !(P x)                   *)
(*       2. insub x = Some y with val y = x if  (P x)                   *)
(* -------------------------------------------------------------------- *)

type T, sT.
pred P : T.

op insub : T  -> sT option.
op val   : sT -> T.

axiom insubN (x : T): !P x => insub x = None.
axiom insubT (x : T):  P x => omap val (insub x) = Some x.

axiom valP (x : sT): P (val x).
axiom valK: pcancel val insub.

(* -------------------------------------------------------------------- *)
(* EasyCrypt types cannot be empty. We here explicitely provide the     *)
(* inverse element of default inhabitant of [sT]                        *)
op wsT : T.

axiom insubW: insub wsT = Some witness<:sT>.

(* -------------------------------------------------------------------- *)
op insubd (x : T) = odflt witness (insub x).

(* -------------------------------------------------------------------- *)
lemma val_inj: injective val.
proof. by apply/(pcan_inj valK). qed.

lemma valKd: cancel val insubd.
proof. by move=> u; rewrite /insubd valK. qed.

lemma insubP (x : T):           (* We need inductive predicates *)
     (exists u, P x /\ insub x = Some u /\ val u = x)
  \/ (!P x /\ insub x = None).
proof.                          (* this proof script is awful *)
  case (P x)=> [Px | /insubN -> //]; left.
  move: Px => /insubT; case {-2}(insub x) (eq_refl (insub x))=> //.
  by move=> /= u eq_insub eqx; exists u => /=; move: eqx => /someI ->.
qed.

lemma val_insubd x: val (insubd x) = if P x then x else val witness.
proof. by rewrite /insubd; case (insubP x) => [[u] [->] [->]|[-> ->]]. qed.

lemma insubdK (x : T): P x => val (insubd x) = x.
proof. by move=> Px; rewrite val_insubd Px. qed.
