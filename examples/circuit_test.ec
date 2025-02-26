require import AllCore Bool IntDiv CoreMap List Distr QFABV.
from Jasmin require import JModel JArray.

require import Bindings.


op sub16 (a b: W16.t) = a - b.

  bind op W16.t sub16 "sub".
realize bvsubP by admit.

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
}.


op ident_W16 (w: W16.t) : W16.t = w.
op predT_W16 (w: W16.t) : bool = true.
op times2_W16 (w: W16.t) : W16.t = w + w.
op const2_W16 (w: W16.t) : W16.t = W16.of_int 2.
op const0_W16 (w: W16.t) : W16.t = W16.of_int 0.


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

    
