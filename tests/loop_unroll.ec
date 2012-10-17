cnst k : int.
cnst n : int.

type msg = bool list.
type block = bitstring{k}.
type state = bitstring{n}.

op pad : msg -> block list.
op tail : 'a list -> 'a list.

axiom padnotempty : forall (m:msg), !(pad(m) = []).

axiom tail_length : 
  forall (l:'a list), l <> [] => length(tail(l)) = length(l) - 1. 

game Game1 = {
  var ROmap : (msg, state) map

  fun RO(m : msg) : state = {
    var z : state = {0,1}^n;
    if ( !in_dom(m, ROmap) ) { ROmap[m] = z; }
    return ROmap[m];
  }
}.

game Game2 = Game1
  where RO = {
    var bs : block list = pad(m);
    var z : state;

    while (bs <> []) {
      z = {0,1}^n;
      if ( !in_dom(m, ROmap) ) { ROmap[m] = z; }
      z = ROmap[m];
      bs = tail(bs);
    }

    return ROmap[m];
  }.

prover "alt-ergo".

equiv Game12_RO : Game1.RO ~ Game2.RO : ={m,ROmap} ==> ={res,ROmap}.
proof.
 sp.
 unroll{2}.
 condt{2}.
 rnd>>.
 sp.
 while{2} >> : ={ROmap} : length(bs{2}), 0; trivial.
 save.


