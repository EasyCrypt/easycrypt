(* Multi-character bullet tokens (`--`, `++`, `**`) are also usable as
   user-defined binary operator names. *)
require import AllCore.

(* `--` as an integer binop. *)
op ( -- ) (a b : int) : int = a - b - 1.

lemma minusminus_test : 5 -- 2 = 2.
proof. by rewrite /(--). qed.

(* `++` as an integer binop. *)
op ( ++ ) (a b : int) : int = a + b + 1.

lemma plusplus_test : 3 ++ 4 = 8.
proof. by rewrite /(++). qed.

(* `**` as an integer binop. *)
op ( ** ) (a b : int) : int = a * b * 2.

lemma starstar_test : 3 ** 4 = 24.
proof. by rewrite /( ** ). qed.
