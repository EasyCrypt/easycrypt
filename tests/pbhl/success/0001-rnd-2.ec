

require import Distr.
require import Bool.
require import Real.

module Test = {
  var x : bool

  proc test() : unit = {
    x = !x;
    x = $Dbool.dbool;
  }

}
.


lemma test : phoare [Test.test : Test.x ==> Test.x] <=  (if Test.x then (1%r/2%r) else 0%r).
proc.
rnd.
intros bd.
wp.
simplify.
skip.
smt.
qed.


