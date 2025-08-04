require import AllCore.

exception toto.

module M ={
  proc truc (x:int) : int = {
  raise toto;
  return x;
  }
}.

lemma truc :
hoare [M.truc : true ==> (res = 1)].
    proof.
    proc.
    wp.
