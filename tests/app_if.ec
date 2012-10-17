cnst k:int.
adversary A (pk:int) : int {}.

game G1 = {
  var x : int
  var y : int

  abs A = A {}

  fun Main () : int = {
    var res : int;
    x = [0..k];
    y = [0..k];
    res = A(x+y);
    return res;
  }
}.

game G2 = G1 
    where Main = {
    var res : int;
    x = [0..k];
    y = [0..k];
    if (!x=y) { res = A(x+y); }
    else {res = 0; }
    return res;
  }.

equiv G1_G2 : G1.Main ~ G2.Main : 
  true ==> 
     ={x,y} &&
    (x=y){1} = (x=y){2} &&
    (!(x=y){1} => ={res}).
proof.
 rnd>>.
 rnd>>.
 if {2}.
 auto.
 simpl.
save.

claim conclusion :  
      | G1.Main[res = 0] - G2.Main[res = 0] | <= 
         G2.Main[x = y] 
      using G1_G2.
