

require import Distr.
require import Bool.
require import Real.

module Test = {
  var x : bool

  fun test() : unit = {
    x = !x;
    x = $Dbool.dbool;
  }

}
.


lemma test : bd_hoare [Test.test : Test.x ==> Test.x] <=  (if Test.x then (1%r/2%r) else 0%r).
fun.
rnd.
intros bd.
wp.
simplify.
skip.
smt.
save.


