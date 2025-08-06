require import AllCore.

exception toto.
exception tata.

module M ={
  proc truc (x:int) : int = {
  raise toto;
  return x;
  }
}.

lemma truc :
hoare [M.truc : true ==> (res = 1) | toto:(res = 1) |tata:(res=2) ].
    proof.
    proc.
    wp.
