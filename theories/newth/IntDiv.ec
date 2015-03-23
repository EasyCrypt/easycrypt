(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun Int Ring. import Ring.IntID.

(* -------------------------------------------------------------------- *)
op (%%) : int -> int -> int.
op (%/) : int -> int -> int.

axiom nosmt edivzP (m d : int):
  m = (m %/ d) * m + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).

axiom modz0 m: m %% 0 = m.
axiom divz0 m: m %/ 0 = 0.

(* -------------------------------------------------------------------- *)
lemma divz_eq (m d : int): m = (m %/ d) * m + (m %% d).
proof. by case (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma mod0z d: 0 %% d = 0.
proof. by move: (divz_eq 0 d)=> /= <-. qed.

lemma div0z d: 0 %% d = 0.
proof. by move: (divz_eq 0 d)=> /= <-. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < d => m %/ d = 0.
proof. admit. qed.

lemma nosmt modz_small m d: 0 <= m < d => m %% d = m.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl z1 z2 m: (z1 %% m + z2) %% m = (z1 + z2) %% m by admit.
lemma nosmt modzDr z1 z2 m: (z1 + z2 %% m) %% m = (z1 + z2) %% m by admit.

lemma nosmt modzMl z1 z2 m: ((z1 %% m) * z2) %% m = (z1 * z2) %% m by admit.
lemma nosmt modzMr z1 z2 m: (z1 * (z2 %% m)) %% m = (z1 * z2) %% m by admit.
