(* Unit tests for `print proc M.p` and printing a procedure via the
   untyped `print M.p` lookup. Uses the `expect "..." by print ...`
   command (String.trim-based comparison). *)

require import Int.

module type T = { proc o (x : int) : int }.

module M = {
  var g : int

  proc k () : int = {
    return 3;
  }

  proc w () : unit = {
    g <- g + 1;
  }
}.

module F (A : T) = {
  var g : int

  proc run (x : int) : unit = {
    g <@ A.o(x);
  }
}.

module Impl = { proc o (x : int) : int = { return x; } }.
module G = F(Impl).

(* explicit `print proc`, simple body *)
expect "proc k() : int = {
  return 3;
}" by print proc M.k.

(* explicit `print proc`, statement body referencing a module variable *)
expect "proc w() : unit = {
  M.g <- M.g + 1;
}" by print proc M.w.

(* bare `print M.k` finds the procedure via the untyped lookup *)
expect "* In [procedures]:

proc k() : int = {
  return 3;
}" by print M.k.

(* a procedure of an un-instantiated functor prints in suspended mode,
   with the call to the abstract parameter [A] kept abstract *)
expect "(* in functor (A : T) *)
proc run(x : int) : unit = {
  F.g <@ A.o(x);
}" by print proc F.run.

(* once the functor is applied, the call to [A] is resolved concretely *)
expect "proc run(x : int) : unit = {
  F.g <@ Impl.o(x);
}" by print proc G.run.
