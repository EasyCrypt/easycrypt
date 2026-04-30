module Foo = {
   proc foo(i : int) = {
   }
}.

lemma foo_corr : hoare [ Foo.foo : true ==> true] by proc;auto.

lemma foo_eq : equiv [ Foo.foo ~ Foo.foo : ={arg} ==> true ] by sim.

lemma foo_eq_corr:
       equiv [ Foo.foo ~ Foo.foo : ={arg} ==> ={res} ].
       conseq foo_eq foo_corr.
qed.
