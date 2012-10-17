cnst k : int.

type X.
type Y = bitstring{k}.

cnst x' : X.

adversary D() : bool { X -> Y }.

game Lazy = {
  var T : (X, Y) map

  fun O(x : X) : Y = {
    if (!in_dom(x, T)) { T[x] = {0,1}^k; }
    return T[x];
  }
  
  abs D = D { O }

  fun Main() : bool = {
    var b : bool;
    T = empty_map;
    b = D();
    return b;
  }
}.

game Eager = {
  var T : (X, Y) map
  var y' : Y

  fun O(x : X) : Y = {
    if (!in_dom(x, T)) { 
      if (x = x') { T[x] = y'; } else { T[x] = {0,1}^k; }
    }
    return T[x];
  }
  
  abs D = D { O }

  fun Main() : bool = {
    var b : bool;
    T = empty_map;
    y' = {0,1}^k;
    b = D();
    return b;
  }
}.

game Lazy' = {
  var T : (X, Y) map
  var y' : Y

  fun O(x : X) : Y = {
    if (!in_dom(x, T)) { T[x] = {0,1}^k; }
    return T[x];
  }
  
  abs D = D { O }

  fun Main() : bool = {
    var b : bool;
    y' = bs0_k;
    T = empty_map;
    b = D();
    if (!in_dom(x', T)) { y' = {0,1}^k; } else { y' = T[x']; }
    return b;
  }
}.

game Eager' = {
  var T : (X, Y) map
  var y' : Y

  fun O(x : X) : Y = {
    if (!in_dom(x, T)) { 
      if (x = x') { T[x] = y'; } else { T[x] = {0,1}^k; }
    }
    return T[x];
  }
  
  abs D = D { O }

  fun Main() : bool = {
    var b : bool;
    y' = bs0_k;
    T = empty_map;
    if (!in_dom(x', T)) { y' = {0,1}^k; } else { y' = T[x']; }
    b = D();
    return b;
  }
}.

prover "alt-ergo".
timeout 2.

claim Lazy_Lazy'   : Lazy.Main[res] = Lazy'.Main[res] auto.

claim Eager_Eager' : Eager.Main[res] = Eager'.Main[res] auto.

equiv Lazy'_Eager' : Lazy'.Main ~ Eager'.Main : true ==> ={res}
 by eager { if (!in_dom(x', T)) { y' = {0,1}^k; } else { y' = T[x']; } }.
proof.
 derandomize.
 case{1}: x = x'; [ trivial | swap{1} 1; trivial ].
 save.

 trivial. 

 trivial.
save.

claim Lazy'_Eager' : Lazy'.Main[res] = Eager'.Main[res] using Lazy'_Eager'.

claim Lazy_Eager   : Lazy.Main[res] = Eager.Main[res].
