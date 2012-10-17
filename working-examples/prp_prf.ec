cnst l : int. (* block size *)
cnst q : int. (* maximum number of queries made by the adversary *)

type block = bitstring{l}.

axiom l_pos : 0 <= l.
axiom q_pos : 0 < q. 

adversary A() : bool { block -> block }.

game PRP = {
  var L : (block, block) map
  var LA : block list
  var n : int
  var bad : bool

  fun F(x:block) : block = {
    var y : block;
    if (!in_dom(x, L) && length(LA) < q) {
      n = n + 1;
      y = {0,1}^l;
      if (mem(y, LA)) { bad = true; y = ({0,1}^l \ LA); }
      L[x] = y;
      LA = y :: LA;
    }
    return L[x];
  }

  abs A = A {F}

  fun Main() : bool = {
    var b : bool;
    bad = false;
    L = empty_map;
    LA = [];
    n = 0;
    b = A();
    return b;
  }
}.

game PRF = {
  var L : (block, block) map
  var LA : block list
  var n : int
  var bad : bool

  fun F(x:block) : block = {
    var y : block;
    if (!in_dom(x, L) && length(LA) < q) {
      n = n + 1;
      y = {0,1}^l;
      if (mem(y, LA)) { bad = true; }
      L[x] = y;
      LA = y :: LA;
    }
    return L[x];
  }

  abs A = A {F}

  fun Main () : bool = {
    var b : bool;
    bad = false;
    L = empty_map;
    LA = [];
    n = 0;
    b = A();
    return b;
  }
}.


prover "alt-ergo", cvc3.

equiv PRP_PRF_F : PRP.F ~ PRF.F : upto (bad).
proof.
 case{1}: bad.
 if{1}; if{2}; trivial.
 sp; rnd{1}>>; if{1}; trivial.
 sp; rnd{1}>>; if{1}; trivial.
 if; [ | trivial].
 wp; app 2 2 !bad{1} && ={x,y,LA,L,bad,n}; [trivial | ].
 if{1}; trivial.
save.

equiv PRP_PRF : PRP.Main ~ PRF.Main : 
  true ==> ={bad} && (!bad{1} => ={res,LA,L,n}). 
proof.
 (* auto upto (bad) with (={LA,L,n}); trivial. *)
 admit. 
save.

claim PRP_PRF_bad : 
  | PRP.Main[res && n <= q] - PRF.Main[res && n <= q] | <= PRF.Main[bad]
using PRP_PRF.

equiv PRF_post : PRF.Main ~ PRF.Main : true ==> ={bad} && length(LA{2}) <= q
by auto (={bad,LA,L,n} && length(LA{2}) <= q).

claim PRF_bound : PRF.Main[bad] = PRF.Main[bad && length(LA) <= q]
using PRF_post.
 
claim pr_bad : PRF.Main[bad && length(LA) <= q] <= q%r * ((q - 1)%r / (2^l)%r)
compute 3 (bad), (length(LA)).

claim conclusion : 
  | PRP.Main[res && n <= q] - PRF.Main[res && n <= q] | <= 
  q%r * ((q - 1)%r / (2^l)%r).
