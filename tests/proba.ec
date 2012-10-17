game G1 = {
  var bad : bool
  fun Main () : bool = {
    return true;
  }
}.

game G2 = {
  var bad : bool
  fun Main () : bool = {
    return true;
  }
}.

prover "alt-ergo", cvc3, vampire.

equiv foo : G1.Main ~ G2.Main : true ==> ={res}.
admit.
save.

claim bar1 : G1.Main[res] = G2.Main[res] 
using foo.

claim bar2 : G1.Main[res] = G2.Main[res] 
using foo.

equiv foo1 : G1.Main ~ G2.Main : true ==> bad{1} => bad{2}.
admit.
save.

claim bar11 : G1.Main[bad] <= G2.Main[bad] 
using foo1.
(*
claim bar21 : G2.Main[bad] <= G1.Main[bad] 
using foo1.
*)

equiv foo2 : G1.Main ~ G2.Main : true ==> bad{2} <=> bad{1}.
admit.
save.

(*
claim bar21 : G1.Main[bad] <= G2.Main[bad] 
using foo2.
*)

claim bar22 : G2.Main[bad] <= G1.Main[bad] 
using foo2.

claim bar21 : G2.Main[bad] = G1.Main[bad]
using foo2.


cnst k : int.
cnst h : int.

axiom k_pos : 0 <= k.
axiom h_bound : 0 <= h && h <= k.

game Test0 = {
  var bad : bool
  fun H() : int = {
    return 0;
  }
}.

claim Test0 : Test0.H[bad = bad] = 1%r
compute.

game Test1 = { 
  var bad : bool

  fun H() : int = {
    var h':int;
    h' = [0..	k];  
    if (h = h') { bad = true; }
    return 0;
  }

}.

claim Test1 : Test1.H[false] = 0%r
 compute .

game Test2 = { 
  fun H() : bool = {
    var h':int;
    h' = [0..k];  
    return h = h';
  }
}.

claim Test2 : Test2.H[res] = 1%r / (k + 1)%r
 compute.

game Test3 = { 
  fun H() : bool = {
    var h':int;
    h' = [0..3];  
    return (4 = h');
  }

}.

claim Test3 : Test3.H[res] = 0%r
 compute.


game Test4 = { 
  fun H() : bool = {
    var h1:int;
    var h2:int;
    h1 = [0..k];  
    h2 = [0..k];  
    return h1 = h2;
  }

}.

timeout 10.

claim Test4 : Test4.H[res] = 1%r / (k + 1)%r
 compute.

game Test5 = { 
  var bad : bool

  fun H() : int = {
    var h':int;
    bad = false;
    h' = [0..k];  
    if (h = h') { bad = true; }
    return 0;
  }

}.

claim Test5 : Test5.H[bad] = 1%r / (k + 1)%r
 compute.

claim Test5' : Test5.H[bad] <= 1%r / (k + 1)%r
 compute.
 
game Test6 = {
  fun H() : bool = {
    var b, b' : bool;
    b = {0,1};
    return (b = b');
  }
}.   

claim Test6 : Test6.H[res] = 1%r / 2%r
 compute.
    
game Test7 = {
  fun H() : bool = {
    var b, b' : bool;
    var i : int;
    i = [0..k];
    b = {0,1};
    return (b = b');
  }
}.   

claim Test7 : Test7.H[res] = 1%r /2%r
 compute.

game Test8 = {
  fun H() : bool = {
    var b, b' : bool;
    var i : int;
    i = [0..k];
    b = {0,1};
    b = {0,1};
    return (b = b');
  }
}.   

claim Test8 : Test8.H[res] = 1%r / 2%r
 compute.

cnst q : int.

axiom q_pos : 0 <= q.

game List3 = {
  var L : bool list
  var bad : bool

  fun H() : bool = {
    var h' : bool;
    bad = false;
    h' = {0,1}; 
    if (length(L) <= q) { 
      if (mem (h', L)) { bad = true; }
    }
    return true;
  }
}.

claim List3 : List3.H[bad] <= q%r / 2%r 
admit.
(* compute. *)
(* Doesn't work *)

 
game Test9 = {
  var x, y : int

  fun H() : bool = {
    x = [0..q];
    y = [0..q];
    return true;
  }
}.

timeout 20.

claim Test9 : Test9.H[x = y] = 1%r / (q + 1)%r
 compute.


adversary A() : int {}.

game Test10 = {
var i, j : int

  abs A = A {}
 
  fun H() : bool = {
    i = A();
    if (0  <= i && i <= q) { j = [0..q]; } else { j = i; } 
    return true;
  }
}.

claim Test10 : 1%r / (q + 1)%r <= Test10.H[i = j]
 compute.
