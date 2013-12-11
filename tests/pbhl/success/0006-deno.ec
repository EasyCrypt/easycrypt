
require import Real.
require import Bool.



module M = {
  var b : bool
  proc f () : bool = {
    b = $Dbool.dbool;
    return b;
  }
}.


lemma test : forall &m, Pr[M.f() @ &m : res ] = 1%r/2%r.
proof.
intros &m.
phoare_deno (_ : true ==> _ );
[proc;rnd (1%r/2%r) (fun (x:bool), x);skip; smt|smt|smt].
qed.

