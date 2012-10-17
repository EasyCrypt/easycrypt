(* Testing NEW SWAP *)
game G = {
  fun f () : int = {
    var x : int;
    var y : int;
    var z : int;
    x = 1;
    x = 2;
    x = 3;
    y = x;
    while (true) {
      z = y;
    }
    return 0;
 }
}.

equiv asd : G.f ~ G.f : true ==> true.
swap -1.
swap -2.
swap -2.
swap -2.
swap -2.
swap -4.
swap 3.
trivial.
while : true; trivial.
save.


