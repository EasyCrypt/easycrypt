module M = {
  proc f() = {
    var f : int;

    f <- 0;
  }

  proc g() = {}
}.

equiv toto: M.g ~ M.f: true ==> ={res}.
proof.
proc. symmetry.
conseq (:true ==> true) (: true ==> f=0).
abort.
