(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

pragma +Smt:lazy.

(* -------------------------------------------------------------------- *)
require import Fun Int Ring. import Ring.IntID.

(* -------------------------------------------------------------------- *)

(* FIXME: re-add when old Int.ec is cleaned up *)
(* op (%%) : int -> int -> int. *)

op (%/) : int -> int -> int.

axiom nosmt edivzP (m d : int):
  m = (m %/ d) * m + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).

axiom divz0 m: m %/ 0 = 0.
axiom modz0 m: m %% 0 = m.

(* -------------------------------------------------------------------- *)
lemma edivzW (P : int -> int -> bool):
  (forall m d q r,
        m = (m %/ d) * m + (m %% d)
     => (d <> 0 => 0 <= m %% d < `|d|)
     => P q r)
  => forall m d, P (m %/ d) (m %% d).
proof. by move=> h m d; case: (edivzP m d)=> mE lt_mod; apply/(h m d). qed.

(* -------------------------------------------------------------------- *)
lemma divz_eq (m d : int): m = (m %/ d) * m + (m %% d).
proof. by case (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma mod0z d: 0 %% d = 0.
proof. by move: (divz_eq 0 d)=> /= <-. qed.

lemma div0z d: 0 %% d = 0.
proof. by move: (divz_eq 0 d)=> /= <-. qed.

(* -------------------------------------------------------------------- *)
lemma edivn_eq d q r: 0 <= r < d => (q * d + r) %/ d = q.
proof. admit. qed.

lemma emodn_eq d q r: 0 <= r < d => (q * d + r) %% d = r.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < d => m %/ d = 0.
proof. by move=> /edivn_eq /(_ 0). qed.

lemma nosmt modz_small m d: 0 <= m < d => m %% d = m.
proof. by move/emodn_eq /(_ 0). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl z1 z2 m: (z1 %% m + z2) %% m = (z1 + z2) %% m by admit.
lemma nosmt modzDr z1 z2 m: (z1 + z2 %% m) %% m = (z1 + z2) %% m by admit.

lemma nosmt modzMml z1 z2 m: ((z1 %% m) * z2) %% m = (z1 * z2) %% m by admit.
lemma nosmt modzMmr z1 z2 m: (z1 * (z2 %% m)) %% m = (z1 * z2) %% m by admit.

lemma nosmt modzMl p d: (p * d) %% d = 0 by admit.
lemma nosmt modzMr p d: (d * p) %% d = 0 by admit.

lemma nosmt modzNm z m: (- (z %% m)) %% m = (-z) %% m by admit.
