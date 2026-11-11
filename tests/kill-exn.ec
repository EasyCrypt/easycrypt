(* -------------------------------------------------------------------- *)
(* [kill] must take the exceptional postconditions of a [hoare] goal into
   account: a variable they read cannot be killed. *)
require import AllCore.

exception oops of int.

module N = {
  var x : int
  var y : int

  proc f() : unit = {
    N.x <- 1;
    N.y <- 2;
    raise (oops 0);
  }
}.

(* [N.x] is read by the exceptional postcondition: [kill] is rejected
   (otherwise the false judgement below would be provable). *)
lemma kill_exn_read : hoare [N.f : N.x = 0 ==> true | oops _ => N.x = 0].
proof.
proc.
fail kill 1.
abort.

(* [N.y] is read by no postcondition: [kill] applies. *)
lemma kill_exn_unread : hoare [N.f : N.x = 0 ==> true | oops _ => N.x = 1].
proof.
proc.
kill 2.
+ by auto.
by wp; skip.
qed.
