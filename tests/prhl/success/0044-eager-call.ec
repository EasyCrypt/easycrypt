require import Int.
require import Distr.

module M = {
  var w:int
  var b : bool
  proc f1 (x:int) : int = {
    b = true;
    return w + x;
  }
   
  proc f2(x:int) : int = {
    if (!b) w = $[0..10];
    b = true;
    return w + x;
  }

  proc g1(y:int) : int = {
    var r : int;
    if (!b) w = $[0..10];
    r = f1(y);
    return r;
  }

  proc g2(y:int) : int = {
    var r : int;
    r = f2(y);
    if (!b) w = $[0..10];
    return r;
  } 
    
}.

lemma foo1 : equiv [M.g1 ~ M.g2 : ={M.b,M.w,y} ==> ={M.b,M.w,res}].
proof.
 proc.
 eager call (_:  ={M.b,M.w,x} ==> ={M.b,M.w,res}).
 eager proc.
   rcondf{2} 4; first intros &m;wp => //.
   sim.
 skip => //.
qed.

lemma foo : eager[if (!M.b) M.w = $[0..10]; , M.f1 ~ 
                  M.f2, if (!M.b) M.w = $[0..10]; :
                  ={M.b,M.w,x} ==> ={M.b,M.w,res}].
proof.
 eager proc.
 rcondf{2} 4; first intros &m;wp => //.
 sim.
qed.

lemma foo2 : equiv [M.g1 ~ M.g2 : ={M.b,M.w,y} ==> ={M.b,M.w,res}].
proof.
 proc.
 eager call foo.
 skip => //.
qed.
