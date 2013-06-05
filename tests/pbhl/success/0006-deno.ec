
require import Real.
require import Bool.



module M = {
  var b : bool
  fun f () : bool = {
    b = $Dbool.dbool;
    return b;
  }
}.


lemma test : forall &m, Pr[M.f() @ &m : res ] = 1%r/2%r
proof.
intros &m.
bdhoare_deno (_ : true ==> _ );
[fun;rnd (1%r/2%r) (lambda (x:bool), x);skip; trivial|trivial|trivial].
save.

