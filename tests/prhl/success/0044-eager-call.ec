require import Int.
require import Distr.

module M = {
  var w:int
  var b : bool
  fun f1 (x:int) : int = {
    b = true;
    return w + x;
  }
   
  fun f2(x:int) : int = {
    if (!b) w = $[0..10];
    b = true;
    return w + x;
  }

  fun g1(y:int) : int = {
    var r : int;
    if (!b) w = $[0..10];
    r = f1(y);
    return r;
  }

  fun g2(y:int) : int = {
    var r : int;
    r = f2(y);
    if (!b) w = $[0..10];
    return r;
  } 
    
}.

lemma foo1 : equiv [M.g1 ~ M.g2 : ={M.b,M.w,y} ==> ={M.b,M.w,res}].
proof.
 fun.
 eager call (_:  ={M.b,M.w,x} ==> ={M.b,M.w,res}).
 eager fun.
   rcondf{2} 4; first intros &m;wp => //.
   eqobs_in.
 skip => //.
save.

lemma foo : eager[if (!M.b) M.w = $[0..10]; , M.f1 ~ 
                  M.f2, if (!M.b) M.w = $[0..10]; :
                  ={M.b,M.w,x} ==> ={M.b,M.w,res}].
proof.
 eager fun.
 rcondf{2} 4; first intros &m;wp => //.
 eqobs_in.
save.

lemma foo2 : equiv [M.g1 ~ M.g2 : ={M.b,M.w,y} ==> ={M.b,M.w,res}].
proof.
 fun.
 eager call foo.
 skip => //.
save.
