cnst k : int.

cnst a : bitstring{k}.
cnst b : bitstring{k}.

axiom foo : !(a = b).

game G = {
  var P : (bitstring{k},bitstring{k}) map
  var L : bitstring{k} list

  fun PRP(x : bitstring{k}) : bitstring{k} = {
    var y : bitstring{k};
    y = ({0,1}^k \ L);
    if (!in_dom(x, P)) {
      P[x] = y;
      L = y :: L;
    }
    return P[x];
  }

  fun Main() : bool = {
    var x, y : bitstring{k};
    L = [];
    P = empty_map;
    x = PRP(a);
    y = PRP(b);
    return (x = y);
  }

}.

equiv test : G.Main ~ G.Main : true ==> res{1} = false.
 inline PRP.
 wp; rnd; wp; rnd; wp.
 trivial.
save.
