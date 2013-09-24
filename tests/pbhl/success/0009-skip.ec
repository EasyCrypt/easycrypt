
module Test={fun test():unit={}}.

require import Real.
lemma test : bd_hoare [Test.test : true ==> true] >= (1%r/2%r). 
fun.
skip.
smt.
trivial.
save.

