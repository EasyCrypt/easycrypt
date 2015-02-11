(* -------------------------------------------------------------------- *)
require import Int.

(* -------------------------------------------------------------------- *)
lemma mod0z (z : int): 0 %% z = 0 by admit.
lemma modz_small m d: 0 <= m < d => m %% d = m by admit.

lemma modzDl z1 z2 m: (z1 %% m + z2) %% m = (z1 + z2) %% m by admit.
lemma modzDr z1 z2 m: (z1 + z2 %% m) %% m = (z1 + z2) %% m by admit.

lemma modzMl z1 z2 m: ((z1 %% m) * z2) %% m = (z1 * z2) %% m by admit.
lemma modzMr z1 z2 m: (z1 * (z2 %% m)) %% m = (z1 * z2) %% m by admit.
