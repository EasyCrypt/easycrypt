
require import List.
require import Int.
require import Distr.
require import Real.

op K : int.

module Test = {
  fun test () : int list = {
    var ls : int list;
    var i : int;
    var l : int;
    (ls,i) = ([],0);
    while (i<K) {
      l = $Dinter.dinter 0 9;
      ls = l::ls;
      i = i+1;
    }
   
    return ls;
  }

}.


lemma test : bd_hoare [Test.test : true ==> mem 0 res] <= (1%r).
fun.
while true.
