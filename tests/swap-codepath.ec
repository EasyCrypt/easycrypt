(* `swap` with a code path swaps inside the addressed block only; the
   enclosing `if`/`while` and the sibling branch stay in the goal, so the
   untouched branch is what makes the postconditions below hold. *)
require import AllCore.

module M = {
  var x, y : int
  proc f(b : bool) : unit = {
    if (b) { x <- 1; y <- 2; } else { x <- 5; y <- 6; }
  }
  proc w(b : bool) : unit = {
    x <- 0; y <- 0;
    while (b) { x <- 1; y <- 2; }
  }
}.

module N = {
  proc f(b : bool) : unit = {
    if (b) { M.y <- 2; M.x <- 1; } else { M.y <- 6; M.x <- 5; }
  }
  proc w(b : bool) : unit = {
    M.x <- 0; M.y <- 0;
    while (b) { M.y <- 2; M.x <- 1; }
  }
}.

lemma then_branch : hoare [M.f : !b ==> M.x = 5 /\ M.y = 6].
proof. proc. swap 1.:[1 .. 1] 1. auto. qed.

lemma else_branch : hoare [M.f : b ==> M.x = 1 /\ M.y = 2].
proof. proc. swap 1?:[1 .. 1] 1. auto. qed.

lemma while_body : hoare [M.w : !b ==> M.x = 0 /\ M.y = 0].
proof. proc. swap 3.:[1 .. 1] 1. rcondf 3; auto. qed.

lemma then_branch_ph : phoare [M.f : !b ==> M.x = 5 /\ M.y = 6] = 1%r.
proof. proc. swap 1.:[1 .. 1] 1. auto. qed.

lemma equiv_if : equiv [M.f ~ N.f : ={b} ==> ={M.x, M.y}].
proof. proc. swap{1} 1.:[1 .. 1] 1. swap{1} 1?:[1 .. 1] 1. sim. qed.

lemma equiv_while : equiv [M.w ~ N.w : ={b} ==> ={M.x, M.y}].
proof. proc. swap{1} 3.:[1 .. 1] 1. sim. qed.

(* match arm: the path binds the arm's locals *)
module P = {
  proc m(o : int option) : unit = {
    match o with
    | None   => { M.x <- 5; M.y <- 6; }
    | Some v => { M.x <- v; M.y <- 2; }
    end;
  }
}.

module Q = {
  proc m(o : int option) : unit = {
    match o with
    | None   => { M.x <- 5; M.y <- 6; }
    | Some v => { M.y <- 2; M.x <- v; }
    end;
  }
}.

lemma match_arm : equiv [P.m ~ Q.m : ={o} ==> ={M.x, M.y}].
proof. proc. swap{1} 1#Some.:[1 .. 1] 1. sim. qed.

(* a single position under a path is written without `:` *)
lemma bare_position : equiv [M.f ~ N.f : ={b} ==> ={M.x, M.y}].
proof. proc. swap{1} 1.1 1. swap{1} 1?1 1. sim. qed.
