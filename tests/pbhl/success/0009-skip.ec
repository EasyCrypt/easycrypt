
module Test={proc test():unit={}}.

require import Real.
lemma test : bd_hoare [Test.test : true ==> true] >= (1%r/2%r). 
proc.
skip.
smt.
trivial.
save.

