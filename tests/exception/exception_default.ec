(* An exception that is neither named by the postcondition nor covered by
   a default branch [_ => Q] is unconstrained (as if [_ => true]). Moving
   code across a call that may raise is only refused when the goal
   constrains exceptions. *)
require import AllCore.

exception exn1.
exception arg1 of int.

module type T = { proc f() : unit }.

module M = {
  var x, y : int

  proc g() : unit = { raise exn1; }
  proc h() : unit = { M.x <- M.x + 1; }
  proc k() : unit = { g(); }

  (* the example of #1129 *)
  proc f() : unit = { g(); y <- 1; }

  proc fh() : unit = { h(); y <- 1; }

  proc a(i : int) : unit = { raise (arg1 i); }

  proc l() : unit = {
    var i : int;
    i <- 0;
    while (i < 2) { k(); y <- y + 1; i <- i + 1; }
  }
}.

(* -------------------------------------------------------------------- *)
(* wp: an exception with no branch gets [true]; the default branch binds
   no argument. *)
lemma g_none : hoare [M.g : true ==> false].
proof. by proc; wp; skip. qed.

lemma a_default : hoare [M.a : true ==> false | _ => M.x = M.x].
proof. by proc; wp; skip. qed.

(* -------------------------------------------------------------------- *)
(* conseq: a missing default of the premise is [true]: a default of the
   goal must then hold on its own. *)
lemma g_none_conseq : hoare [M.g : true ==> false | exn1 => true].
proof. by conseq g_none. qed.

lemma g_default_false : hoare [M.g : true ==> false | _ => false].
proof. fail by conseq g_none. abort.

(* -------------------------------------------------------------------- *)
(* swap: #1129 *)
lemma honest : hoare [M.f : M.y = 0 ==> false | exn1 => M.y = 0].
proof. by proc; inline M.g; wp; skip. qed.

lemma fake : hoare [M.f : M.y = 0 ==> false | exn1 => M.y = 1].
proof. proc. fail swap 1 1. abort.

(* across a call to an abstract procedure *)
module N (A : T) = {
  proc f() : unit = { A.f(); M.y <- 1; }
}.

section.
declare module A <: T { -M }.

lemma swap_abs : hoare [N(A).f : true ==> true | exn1 => M.y = 0].
proof. proc. fail swap 1 1. abort.
end section.

(* across a call that cannot raise: allowed *)
lemma swap_h : hoare [M.fh : true ==> true | exn1 => M.y = 0].
proof. proc. swap 1 1. abort.

(* when the goal does not constrain exceptions (no branch, or only
   [true] branches): allowed *)
lemma swap_noexn : hoare [M.f : true ==> M.y = 1].
proof. proc. swap 1 1. by inline M.g; wp. qed.

lemma swap_true : hoare [M.f : true ==> M.y = 1 | exn1 => true].
proof. proc. swap 1 1. by inline M.g; wp. qed.

(* -------------------------------------------------------------------- *)
(* fission: a loop body part that may raise through a call *)
lemma fission_exn : hoare [M.l : true ==> true | exn1 => M.y = 0].
proof. proc. fail fission 2 @ 1, 2. abort.

lemma fission_noexn : hoare [M.l : true ==> true].
proof. proc. fission 2 @ 1, 2. abort.
