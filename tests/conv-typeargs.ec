(* -------------------------------------------------------------------- *)
(* Regression test: conversion must compare operator type-arguments.

   `wrap`'s type parameter ['a] is "phantom": it occurs only in the body,
   so `wrap`'s head type is `int -> int` for every instantiation.  A bug in
   the applied-operator convertibility shortcut (ecReduction.ml) dropped the
   type-argument lists, so `reflexivity` wrongly closed
     wrap<:bool> 0 = wrap<:unit> 0
   even though those are |bool| = 2 and |unit| = 1 — a proof of `false`.
   `reflexivity` must now be rejected here.                              *)
require import AllCore List Finite.

op wrap ['a] (x : int) : int = size (to_seq<:'a> predT).

lemma conv_typeargs_phantom : wrap<:bool> 0 = wrap<:unit> 0.
proof. fail reflexivity. abort.
