(* unroll and split on while loops. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { while (M.a < 10) { M.a <- M.a + 1; } return M.a; }
  proc g() : int = { while (M.a < 10) { M.a <- M.a + 1; } return M.a; }
}.

(* Unroll rewrites the body but the lemma still closes. *)
lemma unroll_then_close :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl conseq (={M.a}) (={M.a} /\ !(M.a{1} < 10)).
- smt(). - smt().
- dcoupl unroll.
  (* body_l becomes [if (a<10) then (a<-a+1; while) else skip] *)
  admit.
qed.

(* Split rewrites the while with an additional predicate. *)
lemma split_then_close :
  equiv[ M.f ~ M.g : ={M.a} ==> true ].
proof.
proc. delay.
dcoupl split (M.a < 5).
(* body_l becomes [while a<10 /\ a<5 do ...; while a<10 do ...] *)
admit.
qed.
