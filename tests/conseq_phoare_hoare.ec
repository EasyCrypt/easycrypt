require import Real.

module Foo = {proc foo() = {}}.

lemma foo_ll : islossless Foo.foo by islossless.

op [opaque] p = predT<:int>.

lemma foo_h: hoare [ Foo.foo : true ==> forall j, p j]. 
proof. by proc; auto => /> j; rewrite /p. qed.

lemma foo_p: phoare[ Foo.foo : true ==> forall j, p j] = 1%r.
by conseq foo_ll foo_h.
qed.
