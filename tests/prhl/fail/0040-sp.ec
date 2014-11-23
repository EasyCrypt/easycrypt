require Real.

module M1 = {
  var a:int
}.

module M = {
  module A = M1
  module B = M1
  proc x() : int = {
    A.a = 2; 
    B.a = 1; 
    return B.a;
  }
}.

lemma confuse_vars: phoare [ M.x : true ==> res=1 /\ res=2 ] = 1%r.
  proc.
  (* In this step, M.A.a and M.A.b are treated as different variables.
    (Note the new precondition.) *)
  sp.
  (* In this step, M.A.a and M.A.b are treated as the same variable. *)
  skip => &hr H1;split => //.
qed.
