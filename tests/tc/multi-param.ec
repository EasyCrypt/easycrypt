require import AllCore.

(* Multi-parameter typeclass: [embed] takes two type parameters
   ['a, 'b], indexing the source/target of the embedding. *)
type class ['a, 'b] embed = {
  op proj : embed -> 'a
  op inj  : 'b -> embed

  axiom proj_inj :
    forall (x : 'a) (y : 'b), proj (inj y) = x => proj (inj y) = x
}.

(* Polymorphic-over-multi-param lemma. The polymorphic body still needs
   an explicit tvi: the carrier is a type parameter ['c], so there is
   no concrete instance to drive By-args inference. *)
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

(* The instance specializes both type parameters. Both forms work:
   the helper-op form and the bare TC op form. *)
op test_proj : int = proj_pair (inj_pair true).
op test_via_tc : int = proj (inj true).

(* Polymorphic lemma applied at the concrete instance. The body uses
   explicit tvi because the apply target is the polymorphic
   [round_trip], not a TC op directly. *)
lemma round_trip_int (x : int) (y : bool) :
  proj<:int, bool, (int * bool)> (inj<:int, bool, (int * bool)> y) = x =>
  proj<:int, bool, (int * bool)> (inj<:int, bool, (int * bool)> y) = x.
proof. by apply (round_trip<:int, bool, (int * bool)>). qed.
