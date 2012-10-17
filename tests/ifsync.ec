cnst k : int.

game G1 = {
  var x : int
  var y : int
  fun Main () : int = {
   var res : int;
   y = 32;
   if (x = 0) {
    y = [0..k];
   } else
   {
    y = 3;
   }
   return res;
  }
}.


game G2 = {
  var x : int
  var y : int
  fun Main () : int = {
   var res : int;
   y = 23;
   if (x <> 0) {
    y = 3;
   } else
   {
    y = [0..k];
   }
   return res;
  }
}.


equiv Fact : G1.Main ~ G2.Main : ={x} ==> ={x,y}.
proof.
 ifneg{2} at 2.
 ifsync 2 2.
 rnd; trivial.
 trivial.
 trivial.
save.
