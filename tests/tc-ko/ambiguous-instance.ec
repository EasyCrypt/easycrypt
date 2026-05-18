require import AllCore.

(* Negative: two distinct instances of the same parametric typeclass
   match the goal's args. The By-args strategy must report
   "ambiguous typeclass instance" rather than degrading to a generic
   "free variables" error at close time. *)
type class ['a, 'b] embed = {
  op proj : embed -> 'a
  op inj  : 'b -> embed
  axiom dummy : true
}.

(* First instance: int * bool, with the natural projections. *)
op proj_pair_l (p : int * bool) : int = fst p.
op inj_pair_l  (b : bool) : int * bool = (0, b).

instance (int, bool) embed as pair_inst_l with (int * bool)
  op proj = proj_pair_l
  op inj  = inj_pair_l.

realize dummy by trivial.

(* Second instance: bool * int, with swapped projections. Both match
   (int, bool) embed. *)
op proj_pair_r (p : bool * int) : int = snd p.
op inj_pair_r  (b : bool) : bool * int = (b, 0).

instance (int, bool) embed as pair_inst_r with (bool * int)
  op proj = proj_pair_r
  op inj  = inj_pair_r.

realize dummy by trivial.

(* Bare op: ambiguous, since both instances of (int, bool) embed match. *)
op test_ambiguous : int = proj (inj true).
