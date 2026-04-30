require import AllCore.

(* Multi-parameter typeclass: [embed] takes two type parameters
   ['a, 'b], indexing the source/target of the embedding. *)
type class ['a, 'b] embed = {
  op proj : embed -> 'a
  op inj  : 'b -> embed

  axiom proj_inj :
    forall (x : 'a) (y : 'b), proj (inj y) = x => proj (inj y) = x
}.

(* Polymorphic-over-multi-param lemma. *)
lemma round_trip
  ['a, 'b, 'c <: ('a, 'b) embed]
  (x : 'a) (y : 'b) :
  proj<:'a, 'b, 'c> (inj<:'a, 'b, 'c> y) = x =>
  proj<:'a, 'b, 'c> (inj<:'a, 'b, 'c> y) = x.
proof. by apply proj_inj. qed.

(* Concrete instance: pair (int, bool) carrying both. *)
op proj_pair (p : int * bool) : int = fst p.
op inj_pair  (b : bool) : int * bool = (0, b).

instance (int, bool) embed as pair_inst with (int * bool)
  op proj = proj_pair
  op inj  = inj_pair.

realize proj_inj by trivial.

(* The instance specializes both type parameters; bare ops require
   explicit tvi because the parametric carrier 'self cannot be inferred
   from the source/target alone. *)
op test_proj : int = proj_pair (inj_pair true).
op test_via_tc : int = proj<:int, bool, (int * bool)> (inj<:int, bool, (int * bool)> true).
