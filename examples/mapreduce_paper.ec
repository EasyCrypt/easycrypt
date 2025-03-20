require import AllCore Bool IntDiv CoreMap List Distr QFABV.
from Jasmin require import JModel JArray.


bind bitstring W8.w2bits W8.bits2w W8.to_uint W8.to_sint W8.of_int W8.t 8.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize ofintP by admit.
realize touintP by admit.
realize tosintP by admit.

bind op W8.t W8.(+^) "xor".
realize bvxorP by admit.

op bool2bits (b : bool) : bool list = [b].
op bits2bool (b: bool list) : bool = List.nth false b 0.

op i2b (i : int) = (i %% 2 <> 0).
op b2si (b: bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize ofintP by admit.
realize touintP by admit.
realize tosintP by auto.

bind op bool (^^) "add".
realize bvaddP by admit.

op predT_bool : bool -> bool = fun _ => true.
op xor1_bool (b: bool) = b ^^ true.

op xor_left (w1 : W8.t) =
  (w1 +^ (W8.of_int 42)) +^ (W8.of_int 213).

op xor_right (w1 : W8.t) =
  w1 +^ ((W8.of_int 42)) +^ (W8.of_int 213).

op xor_left_spec : W8.t -> W8.t.

bind circuit xor_left_spec "XOR_LEFT8".

op predT_W8 : W8.t -> bool = fun _ => true.

module M = {
  proc xor_left_proc (w1: W8.t) = {
    w1 <- w1 +^ (W8.of_int 42);
    w1 <- w1 +^ (W8.of_int 213);
    return w1;
  }

  proc xor_right_proc (w1: W8.t) = {
    var w2 : W8.t;
    w2 <- (W8.of_int 42);
    w2 <- w2 +^ (W8.of_int 213);
    w1 <-w1 +^ w2;
    return w1;
  } 
}.

lemma xor_left_corr (w: W8.t) :
    hoare [ M.xor_left_proc : w = w1 ==> res = xor_left w].
proof.
proc.
bdep 8 8 [w] [w1] [w1] xor_left predT_W8.
admit.
admit.
qed.

lemma xor_left_equiv_xor_right_proc (w: W8.t) : 
    equiv [ M.xor_left_proc ~ M.xor_right_proc : w = arg{1} /\ arg{1} = arg{2} ==> res{1} = res{2} ]. 
proof.
proc.
bdepeq 8 [w1] [w1] {8 : [w1 ~ w1]} predT_W8.
admit.
auto.
qed.

lemma xor_left_equiv_xor_right_proc_lanes (w: W8.t) : 
    equiv [ M.xor_left_proc ~ M.xor_right_proc : w = arg{1} /\ arg{1} = arg{2} ==> res{1} = res{2} ]. 
proof.
proc.
bdepeq 1 [w1] [w1] {1 : [w1 ~ w1]} predT_bool.
admit.
auto.
qed.


lemma xor_left_corr_lanes (w: W8.t) :
    hoare [ M.xor_left_proc : w = w1 ==> res = xor_left w].
proof.
proc.
bdep 1 1 [w] [w1] [w1] xor1_bool predT_bool.
admit.
admit.
qed.

lemma xor_left_corr_spec (w: W8.t) :
    hoare [ M.xor_left_proc : w = w1 ==> res = xor_left w].
proof.
proc.
bdep 8 8 [w] [w1] [w1] xor_left_spec predT_W8.
admit.
admit.
qed.
