(* -------------------------------------------------------------------- *)
require import Int Xint.
require import FinType.

op (^^) (b1 b2:bool) = b1 = !b2.

lemma xor_false b: b ^^ false = b
by case: b.

lemma xor_true b: b ^^ true = !b
by case: b.

lemma xorA b1 b2 b3: (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3)
by case: b1 b2 b3=> - [] [].

lemma xorC b1 b2: b1 ^^ b2 = b2 ^^ b1
by case: b1 b2=> - [].

lemma xorK b: b ^^ b = false
by case: b.

clone FinType as BoolFin with
  type t    <- bool,
  op enum <- List.(::) true (List.(::) false List."[]"),
  op card <- 2
proof enum_spec by case.

