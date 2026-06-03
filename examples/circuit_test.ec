require import AllCore Bool IntDiv CoreMap List Distr QFABV.
from Jasmin require import JModel JArray.

require import Bindings.


op sub16 (a b: W16.t) = a - b.

bind op W16.t sub16 "sub".
realize bvsubP by admit.

type word = W32.t.

op ROR_W32(w1 w2: W32.t) = 
  w1 `|>>>|` (W32.to_uint w2).

bind op W32.t ROR_W32 "ror".
realize bvrorP by admit.

print (`|>>|`).

op SHR_W32(w1 w2: W32.t) =
  w1 `|>>|` (W8.of_int (W32.to_uint w2)).

bind op W32.t SHR_W32 "shr".
realize bvshrP by admit.

lemma rw_RORw (w1: W32.t) (i: int) : 
  w1 `|>>|` (W8.of_int i) = ROR_W32 w1 (W32.of_int i).
by admit. qed.

lemma rw_SHLw (w1: W32.t) (i: int) : 
  w1 `>>` (W8.of_int i) = SHR_W32 w1 (W32.of_int i).
by admit. qed.


module M = {
  proc and_or_test (a: W16.t) : W16.t = {
  var b : W16.t;
  b <- W16.andw a (W16.of_int 514);
  b <- W16.orw  b (W16.of_int 1028);
  return b;
  }
 
  proc vp_test (a: W256.t) : W256.t = {
      a <- VPADD_16u16 a a;
    return a;
  }

  proc test_of_list (a: W16.t Array2.t) : W16.t Array2.t = {
    a <- Array2.of_list witness [W16.of_int 2; W16.of_int 2];
    return a;
  }

  proc test_bvinit (a: W16.t) : W16.t = {
    a <- W16.init (fun i => a.[i] ^^ a.[i]);
    return a;
  }
  
  proc test_init (a: W16.t Array2.t) : W16.t Array2.t = {
    a <- Array2.init (fun i => a.[i]);
    return a;
  }

  proc __sigma_0 (w:W32.t) : W32.t = {
    var w1:W32.t;
    var w2:W32.t;
    w1 <- w;
    w2 <- w;
    w <- (w `|>>|` (W8.of_int 7));
    w1 <- (w1 `|>>|` (W8.of_int 18));
    w2 <- (w2 `>>` (W8.of_int 3));
    w <- (w `^` w1);
    w <- (w `^` w2);
    return w;
  }
}.


op ident_W16 (w: W16.t) : W16.t = w.
op predT_W16 (w: W16.t) : bool = true.
op times2_W16 (w: W16.t) : W16.t = w + w.
op const2_W16 (w: W16.t) : W16.t = W16.of_int 2.
op const0_W16 (w: W16.t) : W16.t = W16.of_int 0.

op predT_W32 (w: W32.t) : bool = true.

bind op W32.t W32.(+^) "xor".
realize bvxorP by admit.


bind op [bool & W32.t] W32.init "init".
realize bvinitP by admit.

bind op [W32.t & bool] W32."_.[_]" "get".
realize bvgetP by admit.

op small_sig0 (w : word) : word =
  let x =  w `|>>>|` 7 in
  let y =  w `|>>>|` 18 in
  let z =  w `>>>` 3 in
  x +^ y +^ z.

lemma small_sig (w_: W32.t) : hoare [ M.__sigma_0 : w_ = w ==> res = small_sig0 w_].
proof.
proc.
print (`|>>|`).
proc change 3 : (w `|>>>|` ((to_uint (W8.of_int 7)) %% 32)).auto.
proc change 4 : (w1 `|>>>|` ((to_uint (W8.of_int 18)) %% 32)). auto.
proc change 5 : (w2 `>>>` ((to_uint (W8.of_int 3)) %% 32)). auto.
proc rewrite 3 /=.
proc rewrite 4 /=.
proc rewrite 5 /=.
bdep 32 32 [w_] [w] [w] small_sig0 predT_W32.
admitted.



lemma small_sig_orig (w_: W32.t) : hoare [ M.__sigma_0 : w_ = w ==> res = small_sig0 w_].
proof.
proc.
bdep 32 32 [w_] [w] [w] small_sig0 predT_W32.

op predT_W8 (w: W8.t) : bool = true.
op and2_W8 (w: W8.t) : W8.t = W8.orw (W8.andw w (W8.of_int 2)) (W8.of_int 4).

 
print W16.( [-] ).

lemma test_add_sub (w_: W16.t) :
hoare [ M.and_or_test : (w_ = a) ==> res = w_ ].
    proof.
      proc.
      bdep 8 8 [w_] [a] [b] and2_W8 predT_W8.
      admitted.

lemma test_vp (w_: W256.t) :
hoare [ M.vp_test : (w_ = a) ==> res = w_ ].
    proof.
      proc.
      bdep 16 16 [w_] [a] [a] times2_W16 predT_W16.
      admitted.
    
lemma test_of_list (w_: W16.t Array2.t) :
hoare [ M.test_of_list : (w_ = a) ==> res = w_ ].
    proof.
      proc.
      bdep 16 16 [w_] [a] [a] const2_W16 predT_W16.
      admitted.

lemma test_bvinit (w_: W16.t) :
hoare [ M.test_bvinit : (w_ = a) ==> res = w_ ].
    proof.
      proc.
      bdep 16 16 [w_] [a] [a] const0_W16 predT_W16.
      admitted.

    
