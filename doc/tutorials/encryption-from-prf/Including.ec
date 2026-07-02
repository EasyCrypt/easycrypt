require import AllCore BitEncoding.

require BitWord Construction.

clone import BitWord as Bitstring with
  op n <- 256
proof gt0_n by trivial
rename
  "word" as "bits"
  "dunifin" as "dbits".
import DWord.

clone import Construction as C with 
  type ptxt <- bits,
  type nonce <- bits,
  op (+) <- (+^),
  op dptxt <- dbits
proof *.
realize addpA. proof. move => x y z. by rewrite xorwA. qed.
realize addpC. proof. move => x y. by rewrite xorwC. qed.
realize addKp. proof. move => x y. by rewrite xorwK xorwC xorw0. qed.
realize dptxt_ll by exact/dbits_ll.
realize dptxt_uni by exact/dbits_uni.
realize dptxt_fu by exact/dbits_fu.


print E.
