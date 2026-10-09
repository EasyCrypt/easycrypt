(* Regression for the matchfix termination-check hole.

   `check_body` (ecHiInductive.ml) accepts a recursive call whose decreasing
   argument is a valid structural subterm, but used to return without checking
   the call's OTHER arguments -- so a non-decreasing recursive call hidden in a
   sibling argument escaped. The op below defines `f (S Z) b = ! (f (S Z) b)`
   (i.e. `f x = not (f x)`), which has no total-function solution and makes the
   logic inconsistent. It MUST be rejected by the termination check. *)
require import AllCore.

type t = [ Z | S of t ].

fail op f (n : t) (b : bool) : bool =
  with n = Z   => b
  with n = S k => f k (! (f n b)).
