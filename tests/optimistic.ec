cnst k : int.
cnst zero : bitstring{k}.


op [^^^] : (bitstring{k},  bitstring{k}) ->  bitstring{k} as xor_bitstring.


axiom xor_comm :
  forall (x:bitstring{k}, y:bitstring{k}),
    (x ^^^ y) = (y ^^^ x).

axiom xor_assoc :
  forall (x,z,y:bitstring{k}),
   ((x ^^^ y) ^^^ z) = (x ^^^ (y ^^^ z)).

axiom xor_zero : 
  forall (x:bitstring{k}),
   (x ^^^ zero) = x.

axiom xor_cancel :
  forall (x:bitstring{k}),
   (x ^^^ x) = zero.

game G1 = {
  var x, y, z : bitstring{k}

  fun Main () : unit = {
    x = {0,1}^k;
    y = x ^^^ z;
  } 
}.

game G2 = {
  var x, y, z : bitstring{k}

  fun Main () : unit = {
    y = {0,1}^k;
    x = y ^^^ z;
  } 
}.

equiv optimistic_sampling : G1.Main ~ G2.Main : ={z} ==> ={x,y,z}.
wp.
rnd (y ^^^ z{2}).
trivial.
save.
