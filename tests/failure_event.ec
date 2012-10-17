cnst q:int.
cnst k:int.

adversary A() : bool { bitstring{k} -> bitstring{k} } .

game Test = {
  var Y : bitstring{k}
  var L : bitstring{k} list

  fun Orcl(m:bitstring{k}) : bitstring{k} = {
    var res : bitstring{k} = {0,1}^k;
    L = res::L;
    return res;
  }

  abs A = A {Orcl}
	
  fun Main () : bool = {
    var b : bool;
    L = [];
    Y = {0,1}^k;
    b = A ();
    return b; 
  }
}.

game Test2 = {
  var Y : bitstring{k}
  var L : bitstring{k} list
  var bad : bool

  fun Orcl(m:bitstring{k}) : bitstring{k} = {
    var res : bitstring{k} = {0,1}^k;
    if (res = Y) {bad = true;}
    L = res::L;
    return res;
  }

  abs A = A {Orcl}
	
  fun Main () : bool = {
    var b : bool;
    bad = false;
    L = [];
    Y = {0,1}^k;
    b = A ();
    return b; 
  }
}.

(* Fail to compute Test.Orcl[mem(Y,L)] *)
(*claim pr_bad : Test.Main[mem(Y,L) && length(L) <= q] <= q%r * (1%r / (2^k)%r)
compute 2 mem(Y,L), length(L). *)

claim pr_bad : Test2.Main[bad && length(L) <= q] <= q%r * (1%r / (2^k)%r)
compute 2 bad, length(L). 
    
     
