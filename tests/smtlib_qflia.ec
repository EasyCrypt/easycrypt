(* -------------------------------------------------------------------- *)
(* Tests for the smtlib() tactic — QF_NIA (integer arithmetic) goals   *)
(*                                                                      *)
(* These tests exercise the direct SMTLib2 backend (ecSmtLib.ml).      *)
(* The tactic translates the goal + hypotheses to QF_NIA, dispatches   *)
(* them to Z3 (or CVC5), and checks the response.                       *)
(* -------------------------------------------------------------------- *)

require import Int.

(* -------------------------------------------------------------------- *)
(* Basic: reflexivity *)

lemma refl_int (x : int) : x = x.
proof. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Basic linear arithmetic: x + 1 is strictly greater than x *)

lemma lt_succ (x : int) : x < x + 1.
proof. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Hypothesis use: if x <= y then x <= y + 1 *)

lemma le_trans_plus1 (x y : int) : x <= y => x <= y + 1.
proof. move=> h. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Contradictory hypotheses: x < y and y < x cannot both hold *)

lemma contra (x y : int) : x < y => y < x => false.
proof. move=> h1 h2. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Boolean combination: positive operands give positive sum *)

lemma pos_sum (x y : int) : 0 < x => 0 < y => 0 < x + y.
proof. move=> hx hy. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Nonlinear: a square is non-negative (tests QF_NIA path) *)

lemma sq_nonneg (x : int) : 0 <= x * x.
proof. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Transitivity with three hypotheses *)

lemma le3 (x y z : int) : x <= y => y <= z => x <= z.
proof. move=> h1 h2. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Mixed: arithmetic and boolean connectives *)

lemma mixed (x y : int) : x <= y => y <= x => x = y.
proof. move=> h1 h2. smtlib(). qed.

(* -------------------------------------------------------------------- *)
(* Negation: the tactic should FAIL on this false goal.                 *)
(* To test this interactively, remove the admit and observe the         *)
(* counterexample model printed by the smtlib tactic.                   *)
(*                                                                      *)
lemma false_goal (x y : int) : x + y = x => y = 1.   (* FALSE *) 
proof. fail smtlib(). abort.   (* should fail with model: y = 0 *)        

(* ==================================================================== *)
(* Tests for smtlib(lemma ...) — passing named lemmas as hints          *)
(* ==================================================================== *)

(* A helper lemma we will pass explicitly to later goals. *)
lemma add_zero (x : int) : x + 0 = x.
proof. smtlib(). qed.

(* Use add_zero explicitly as a hint. *)
lemma use_add_zero (x : int) : (x + 0) * 2 = x * 2.
proof. smtlib(add_zero). qed.

(* -------------------------------------------------------------------- *)
(* A helper establishing a bound. *)
lemma lower_bound (x : int) : 0 <= x => 1 <= x + 1.
proof. move=> h. smtlib(). qed.

(* Pass lower_bound as a hint to avoid re-deriving it from scratch. *)
lemma use_lower_bound (x : int) : 0 <= x => 2 <= (x + 1) + 1.
proof. move=> h. smtlib(lower_bound). qed.

(* -------------------------------------------------------------------- *)
(* Multiple lemma hints: two axioms that only hold on specific values.
   Neither alone is enough to prove the goal; both are required.
   Without the hints smtlib() cannot know anything about c.            *)

op c : int.

axiom c_lower : 5 <= c.
axiom c_upper : c <= 10.

lemma c_in_range : 5 <= c /\ c <= 10.
proof. smtlib(c_lower c_upper). qed.

lemma c_positive : 0 < c.
proof. smtlib(c_lower). qed.

(* Confirm that smtlib() without hints cannot prove c_positive. *)
lemma c_positive_no_hint : 0 < c.
proof. fail smtlib(). abort.

(* -------------------------------------------------------------------- *)
(* Hint with a universally quantified closed lemma. *)
lemma mul_zero (x : int) : x * 0 = 0.
proof. smtlib(). qed.

lemma use_mul_zero (x y : int) : (x + y) * 0 = 0.
proof. smtlib(mul_zero). qed.
