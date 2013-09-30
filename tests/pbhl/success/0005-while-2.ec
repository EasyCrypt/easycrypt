
require import List.
require import Int.
require import Distr.
require import Real.

op K : int.
axiom K_def : 0 <= K.

module Test = {
  var ls : int list

  fun test () : int list = {
    var i : int;
    var l : int;
    i = 0;
    while (i<K) {
      l = $Dinter.dinter 0 9;
      ls = l::ls;
      i = i+1;
    }
   
    return ls;
  }

}.


lemma test : bd_hoare [Test.test : true ==> mem 0 res] <= (if mem 0 Test.ls then 1%r else (K%r/10%r)).
fun.
seq 1 : (true) (1%r) (if mem 0 Test.ls then 1%r else (K%r/10%r)) (0%r) (1%r) (i=0);
[wp;trivial|trivial| |trivial|trivial]. 
case (mem 0 Test.ls).
conseq ( _ : _ : (1%r)); [smt|trivial].
conseq ( _ : _ : (if mem 0 Test.ls then 1%r else ((K-i)%r/10%r)) ).
trivial.
while (i <= K); [|skip;smt].
intros Hw.
exists * Test.ls, i;elim * => ls0 i0.
case (mem 0 ls0). (* redundant? *)
conseq ( _ : _ : (1%r)); [smt|trivial].
seq 3 : (l=0) (1%r/10%r) (1%r) (9%r/10%r) ((K-i0-1)%r/10%r) (Test.ls = l :: ls0 /\ i=i0+1 /\ !mem 0 ls0 /\ i<=K).
wp; rnd; skip; smt.
conseq ( _ : _ : = (1%r/10%r) ).
wp. rnd. skip.
admit. (* reasoning on distr *)
trivial.
admit. (* reasoning on distr *)
conseq Hw => //.
smt.
smt.
save.


