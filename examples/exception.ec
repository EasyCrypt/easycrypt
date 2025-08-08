require import AllCore.

exception toto.
exception tata.

module M ={
  proc truc (x:int) : int = {
    if (x = 3)  {raise toto;} else{ x <- 5; }
  return x;
  }
}.

lemma truc :
hoare [M.truc : true ==> (4 < res) | toto:(res = 3) |tata:(res=2) ].
    proof.
      proc.
      conseq (: _ ==> x = 5).
      + smt.
      + auto.
    qed.
