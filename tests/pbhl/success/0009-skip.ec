
module Test={proc test():unit={}}.

require import Real.
lemma test : phoare [Test.test : true ==> true] >= (1%r/2%r). 
proc.
skip.
smt.
trivial.
qed.

