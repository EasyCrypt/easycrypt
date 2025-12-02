require import AllCore List QFABV.


theory FakeWord.
type W.
op size : int.

op to_bits : W -> bool list.
op from_bits : bool list -> W.
op of_int : int -> W.
op to_uint : W -> int.
op to_sint : W -> int.

bind bitstring
  to_bits 
  from_bits 
  to_uint 
  to_sint
  of_int 
  W
  size.

realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W -> W -> W.

bind op W (+^) "xor".
realize bvxorP by admit.

end FakeWord.

type W8.

clone include FakeWord with
  op size <- 8,
  type W <- W8.

module M = {
  proc test (a: W8, b: W8) = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

(*
lemma xor_0 (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b /\ a_ = b_ ==> res = of_int 0].
proof.
  proc.
  proc change 1 : { c <- b +^ a; }.
  wp. skip. move => &h1 &h2.
  have : a{h1} = a_ by admit.
  have : b{h1} = b_ by admit.
  move => A B [] C D.
  have : a{h2} = a_ by smt().
  have : b{h2} = b_ by smt().
  (* move : A B C D. (* Comment or uncomment this line for different modes of working *) *)
  bdep solve.
bdep solve.
qed.
*)
    

lemma xor_com (a_ b_ : W8) : hoare[M.test : a_ = a /\ b_ = b /\ a_ = b_ ==> res = b_ +^ a_].
proof.
  proc.
  proc change 1 : [ d : W8 ] { d <- of_int 0; d <- a +^ d; c <- d +^ b; }.
  circuit.
  circuit.
qed.

