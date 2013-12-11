require import Int.
require import Distr.

module M = {
  var w:int
  proc f1():unit = {
    var x,y,z : int;
    w = $[0 .. 10];
    x = 1;
    y = 2;
    z = 3;

  }
  proc f2():unit = {
    var x,y,z : int;
    x = 1;
    y = 2;
    z = 3;
    w = $[0..10];
  }
}.

equiv foo : M.f1 ~ M.f2 : true ==> ={M.w}.  
proof.
  proc.
  eager seq 1 1 (H:M.w = $[0..10]; ~ M.w = $[0..10]; : true ==> ={M.w}) : (={M.w,x}).
   rnd => //.   
  swap{1} 1; seq 1 1 : (={x}).
    wp => //.
    conseq * H => //.
  eager seq 1 1 H : (={M.w,y});first 2 (wp;rnd;wp => //).
    wp => //.
  eqobs_in.  
save.


