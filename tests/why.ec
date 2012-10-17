game G = {
  var x : int
  var y : int

  fun fx (a:int) : unit = {
    x = a;
  }


  fun fy (a:int) : unit = {
    y = a;
  }
}.

prover "alt-ergo".

equiv test2 : G.fx ~ G.fy : a{1} = x{2} ==> x{1} = x{2} by auto.

(* Should not be able to prove this
equiv test1 : G.fx ~ G.fy : true ==> x{1} = x{2} by auto.
*)