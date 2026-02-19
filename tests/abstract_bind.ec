require import AllCore List Int IntDiv CoreMap Real Number Bool.

require import QFABV.

abstract theory Test.
type t.

op size : int.

axiom size_gt0 : 0 < size.

op add : t -> t -> t.

op w2bits : t -> bool list.

op bits2w : bool list -> t.

op touint : t -> int.

op tosint : t -> int.

op ofint : int -> t.

(*
axiom t_tolistP: forall (bv : t), bits2w (w2bits bv) = bv.
axiom t_oflistP: forall (xs : bool list),
            size xs = Test.size => w2bits (bits2w xs) = xs.
axiom t_touintP: forall (bv : t),
            Test.touint bv = BitEncoding.BS2Int.bs2int (w2bits bv).
axiom t_tosintP: forall (bv : t),
            Test.size = 1 \/
            let v = BitEncoding.BS2Int.bs2int (w2bits bv) in
            if msb bv then Test.tosint bv = v - 2 ^ Test.size
            else Test.tosint bv = v.
axiom t_ofintP: forall (i : int),
           Test.ofint i = bits2w (BitEncoding.BS2Int.int2bs Test.size i).
*)
  
bind bitstring w2bits bits2w touint tosint ofint t size.

realize gt0_size. by apply size_gt0. qed.

realize tolistP by admit.

realize touintP by admit.

realize size_tolist by admit.

realize oflistP by admit.

realize tosintP by admit.

realize ofintP by admit.

bind op t add "add".

realize bvaddP by admit.

end Test.

clone import Test as CTest
  with type t <- bool,
       op size <- 1,
       op add <- (^^).

print CTest.
                           
lemma xor2_false (b: bool) : b ^^ b = CTest.ofint 0.
                           
bdep solve. qed.
