type group.
cnst q : int.
cnst qH : int.
cnst g : group.
cnst k : int.
cnst zero : bitstring{k}.

type secret_key = int.
type public_key = group.
type key        = secret_key * public_key.
type message    = bitstring{k}.
type cipher     = group * bitstring{k}.

op [*]  : (group, group) -> group as group_mult.
op [^]  : (group, int) -> group as group_pow.

op nth     : (int, group list)   -> group.
op find_at : (group, group list) -> int.

axiom nth_length : 
  forall (l:group list, n:int), 0 <= n => n < length(l) => mem(nth(n, l), l).

adversary B(gx, gy:group) : group list {}.

game LCDH = {
  abs B = B {}

  fun Main() : bool = {
    var x, y : int;
    var l : group list;
    x = [0..q-1];
    y = [0..q-1];
    l = B(g^x, g^y);
    return mem(g^(x*y), l);
  }
}.

game CDH = {
  abs B = B {}

  var test : bool

  fun Main(gx, gy:group) : bool = {
    var x, y : int;
    var l:group list;
    var res:bool;
    var i, p : int;

    x = [0..q-1];
    y = [0..q-1];
    l = B(gx,gy);
    test = mem(g^(x*y), l) && length(l) <= qH;
    if (test) {
      p = find_at(g^(x * y), l);
      i = [0..qH];              
      res = (i = p);
    } else {
      res = false;
    }
    return res;
  }
}.

prover "alt-ergo".

axiom qH_pos : 0 < qH.

claim CDH : CDH.Main[res] <= 1%r / qH%r
compute.





