require import AllCore.

module M = { 
  proc f () : int = { 
    return 0;
  }
}.

op spec = hoare[M.f : true ==> true].

lemma Mf : spec.
proc.
auto.
qed.
