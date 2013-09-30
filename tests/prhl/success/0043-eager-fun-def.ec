require import Int.
require import Distr.

module M = {
  var w:int
  var b : bool
  fun f1 () : int = {
    b = true;
    return w;
  }
   
  fun f2() : int = {
    if (!b) w = $[0..10];
    b = true;
    return w;
  }
}.

lemma foo : eager[if (!M.b) M.w = $[0..10]; , M.f1 ~ 
                  M.f2, if (!M.b) M.w = $[0..10]; :
                  ={M.b,M.w} ==> ={M.b,M.w,res}].
proof.
 eager fun.
 rcondf{2} 4; first intros &m;wp => //.
 eqobs_in.
save.