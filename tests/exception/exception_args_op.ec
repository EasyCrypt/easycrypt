require import AllCore.

(* exception arg ['a] of 'a. *)

exception evar of int.

op v : int.

module Mv ={
  var i:int

  proc f1 (x:int) : int = {
    i <- 0;
    raise (evar (v + i)) ;
    return x;
  }
}.

lemma testv :
  hoare [Mv.f1 : true ==> false | evar a => a = v].
proof.
  proc. wp. skip => //.
qed.
