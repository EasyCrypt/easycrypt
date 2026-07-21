require import AllCore.

theory T1.
  op o1 : int = 1.
  op shared : int = 10.
  lemma L1 : o1 = 1. proof. by []. qed.
end T1.

theory T2.
  op o2 : int = 2.
  op shared : int = 20.
  lemma L2 : o2 = 2. proof. by []. qed.
end T2.

(* top-level packed alias *)
theory A = T1 + T2.

lemma test1 : A.o1 = 1. proof. by apply A.L1. qed.
lemma test2 : A.o2 = 2. proof. by apply A.L2. qed.

(* name clashes across targets are ambiguous, as with imports;
   resolution is by type when types differ *)

(* single-target alias still works *)
theory B = T1.
lemma test_single : B.o1 = 1. proof. by apply B.L1. qed.

(* enclosing theory: exercises the mc_of_theory_r (require/close) path *)
theory Outer.
  theory S1. op a : int = 3. lemma La : a = 3. proof. by []. qed. end S1.
  theory S2. op b : int = 4. lemma Lb : b = 4. proof. by []. qed. end S2.
  theory P = S1 + S2.
end Outer.

lemma test3 : Outer.P.a + Outer.P.b = 7.
proof. by rewrite Outer.P.La Outer.P.Lb. qed.

(* the GFq pattern: alias inside an abstract theory, cloned with rename *)
abstract theory AT.
  type t.
  op v : t.
  theory U1. op c : int = 5. lemma Lc : c = 5. proof. by []. qed. end U1.
  theory U2. op d : int = 6. lemma Ld : d = 6. proof. by []. qed. end U2.
  theory F = U1 + U2.
end AT.

clone AT as ATI with type t <- int, op v <- 0
  rename "F" as "G".

lemma test4 : ATI.G.c = 5. proof. by apply ATI.G.Lc. qed.
lemma test5 : ATI.G.d = 6. proof. by apply ATI.G.Ld. qed.
