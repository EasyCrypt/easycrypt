(* ==================================================================== *)
(* Smoke test for TcZModP: instantiate ZModRing at p := 5 and exercise *)
(* class lemmas at the carrier zmod (= Z/5Z).                          *)
(* ==================================================================== *)
require import AllCore List Int IntDiv.
require import TcMonoid TcRing TcBigop TcBigalg TcInt.
require import TcZModP.

(* -------------------------------------------------------------------- *)
(* ZModRing at p := 5 (not prime instantiation; ZModField needs prime). *)
clone import ZModRing as Z5 with
  op p <- 5
  proof ge2_p by trivial.

(* Coercion sanity. *)
lemma test_asint_inzmod (n : int) :
  0 <= n < 5 => asint (inzmod n) = n.
proof. by move=> rg; rewrite inzmodK pmod_small. qed.

(* Concrete arithmetic. *)
lemma test_one_plus_one : zmod_add (Z5.inzmod 1) (Z5.inzmod 1) = inzmod 2.
proof. by rewrite -inzmodD //. qed.

(* Class lemma at the carrier zmod. *)
lemma test_addrC (x y : zmod) : zmod_add x y = zmod_add y x.
proof. by apply zmod_addrC. qed.

(* Bare class-op notation. Resolves to the class [(+)] (via the
   resolver's op-preservation filter on chain-rename) when there is
   no carrier-specific abbrev, or to the abbrev when present. Apply
   class-level [addrC] in either case. *)
lemma test_addrC_infix (x y : zmod) : x + y = y + x.
proof. by apply addrC. qed.

lemma test_mulrC_infix (x y : zmod) : x * y = y * x.
proof. by apply mulrC. qed.

(* The bigA family applies through the [comring] instance — exercise   *)
(* via [BigZModRing] or similar. We just call addrA as a sanity check.  *)
lemma test_addrA (x y z : zmod) :
  zmod_add x (zmod_add y z) = zmod_add (zmod_add x y) z.
proof. by apply zmod_addrA. qed.

lemma test_mulrC (x y : zmod) : zmod_mul x y = zmod_mul y x.
proof. by apply zmod_mulrC. qed.

(* -------------------------------------------------------------------- *)
(* ZModField at p := 5 (prime). Exercises the field instance.           *)
clone import ZModField as Z5F with
  op p <- 5
  proof prime_p by admit.

(* unit ↔ nonzero (field-only). *)
lemma test_unitE (x : Z5F.zmod) :
  Z5F.zmod_unit x <=> x <> (Z5F.inzmod 0).
proof. by apply Z5F.unitE. qed.

(* Fermat: x^4 = 1 for every unit in Z/5Z. *)
lemma test_exp_p_minus_1 (x : Z5F.zmod) :
  x <> (Z5F.inzmod 0) => exp x 4 = (Z5F.inzmod 1).
proof.
move=> nz_x.
have ->: (4 = 5 - 1) by trivial.
by apply: Z5F.exp_sub_p_1; apply/Z5F.unitE.
qed.

(* Frobenius: x^5 = x. *)
lemma test_exp_p (x : Z5F.zmod) : exp x 5 = x.
proof. by apply Z5F.exp_p. qed.
