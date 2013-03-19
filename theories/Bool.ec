import why3 "bool" "Bool"
  op "xorb" as "^^".

op xorb(b0:bool, b1:bool):bool = b0 ^^ b1.

lemma xorb_nilpotent: forall b,
  b ^^ b = false.

lemma xorb_commutative: forall b0 b1,
  b0 ^^ b1 = b1 ^^ b0.

lemma xorb_zero: forall b,
  b ^^ false = b.

lemma xorb_not: forall b,
  b ^^ true = !b.

