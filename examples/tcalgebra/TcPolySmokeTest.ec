(* ==================================================================== *)
(* Smoke test for TcPoly: instantiate the parametric polynomial         *)
(* library at carrier [int] (which is registered as [idomain] via       *)
(* TcInt) and exercise representative lemmas from each phase. Confirms  *)
(* the registered instances flow end-to-end through TC reduction.       *)
(* ==================================================================== *)
require import AllCore List.
require import TcMonoid TcRing TcBigop TcBigalg TcInt.
require import TcPoly.

(* -------------------------------------------------------------------- *)
(* Phase 1-2: constructors / coefficient formulas. *)
lemma test_polyCE (a : int) (k : int) :
  (polyC<:int> a).[k] = if k = 0 then a else 0.
proof. by rewrite polyCE. qed.

lemma test_polyXE (k : int) :
  (X<:int>).[k] = if k = 1 then 1 else 0.
proof. by rewrite polyXE. qed.

(* -------------------------------------------------------------------- *)
(* Phase 4: multiplication on int polys. *)
lemma test_mulrA (p q r : int poly) :
  polyM p (polyM q r) = polyM (polyM p q) r.
proof. by apply polyM_mulrA. qed.

lemma test_mulrC (p q : int poly) : polyM p q = polyM q p.
proof. by apply polyM_mulrC. qed.

(* -------------------------------------------------------------------- *)
(* Phase 6a: degree arithmetic on int polys. *)
lemma test_degC (a : int) :
  deg (polyC<:int> a) = if a = 0 then 0 else 1.
proof. by rewrite degC. qed.

lemma test_deg0 : deg poly0<:int> = 0.
proof. by rewrite deg0. qed.

lemma test_deg1 : deg poly1<:int> = 1.
proof. by rewrite deg1. qed.

lemma test_degX : deg X<:int> = 2.
proof. by rewrite degX. qed.

(* -------------------------------------------------------------------- *)
(* Phase 6c: polyXn / X^i theory. *)
lemma test_deg_polyXn (i : int) : 0 <= i => deg (exp X<:int> i) = i + 1.
proof. by apply deg_polyXn. qed.

lemma test_lc_polyXn (i : int) : 0 <= i => lc (exp X<:int> i) = 1.
proof. by apply lc_polyXn. qed.

(* -------------------------------------------------------------------- *)
(* Phase 7: idomain-only lemmas — multiplicativity of [deg] / [lc]. *)
lemma test_degM (p q : int poly) :
  p <> poly0 => q <> poly0 => deg (polyM p q) = deg p + deg q - 1.
proof. by apply degM. qed.

lemma test_lcM (p q : int poly) : lc (polyM p q) = lc p * lc q.
proof. by apply lcM. qed.

lemma test_polyM_mulf_eq0 (p q : int poly) :
  polyM p q = poly0 <=> p = poly0 \/ q = poly0.
proof. by apply polyM_mulf_eq0. qed.

(* -------------------------------------------------------------------- *)
(* Concrete computation through the convolution: coefficient at index 0
   of [(X + polyC 1) * (X + polyC (-1))] equals -1. Spot-check that
   [polyM] reduces correctly through the registered comring chain.      *)
lemma test_polyM_at_0 :
  (polyM<:int> (polyD X (polyC 1)) (polyD X (polyC (-1)))).[0] = -1.
proof.
rewrite polyME big_int1 /=.
by rewrite !(polyDE, polyXE, polyCE) /= !(mul0r, mulr0, addr0, mul1r, add0r).
qed.

(* -------------------------------------------------------------------- *)
(* polyL constructor on int. *)
lemma test_polyLE (xs : int list) (k : int) :
  (polyL xs).[k] = nth 0 xs k.
proof. by rewrite polyLE. qed.
