(* A theory of polymorphic arrays. *)

(*
 * All operators are only partially specified, as we may choose to match
 * them with different programming language construct.
 * 
 * The user wanting to instantiate it with particular implementation
 * choices should clone it and add axioms to further refine the
 * operators.
 *)

require import Logic.
require import Int.
require Fun. (* For reasoning about higher-order operators *)

(*********************************)
(*             Core              *)
(*********************************)
(* A type *)
type 'x array.

(* Arrays have a non-negative length *)
op length: 'x array -> int.
axiom length_pos: forall (xs:'x array), 0 <= length xs.

(* And a bunch of elements *)
op __get: 'x array -> int -> 'x.

(* Equality is extensional *)
pred (==) (xs0:'x array, xs1:'x array) =
  length xs0 = length xs1 /\
  forall (i:int), 0 <= i => i < length xs0 => xs0.[i] = xs1.[i].

axiom extensionality: forall (xs0:'x array, xs1:'x array),
  xs0 == xs1 => xs0 = xs1.

(*********************************)
(*      Functional Operators     *)
(*********************************)
(* empty *)
op empty: 'x array.

axiom empty_length: length (empty<:'x>) = 0.

lemma empty_unique: forall (xs:'x array),
  length(xs) = 0 => xs = empty.
proof.
intros xs H; apply extensionality; trivial.
save.

(* cons *)
op (::) : 'x -> 'x array -> 'x array.

axiom cons_length: forall (x:'x, xs:'x array),
  length (x::xs) = 1 + length xs.

axiom cons_get: forall (x:'x, xs:'x array, i:int),
  0 <= i => i <= length xs =>
  (x::xs).[i] = (0 = i) ? x : xs.[i - 1].

lemma cons_nonempty: forall (x:'x, xs:'x array),
  x::xs <> empty
by [].

(* snoc *)
op (:::): 'x array -> 'x -> 'x array.

axiom snoc_length: forall (xs:'x array, x:'x),
  length (xs:::x) = length xs + 1.

axiom snoc_get: forall (xs:'x array, x:'x, i:int),
  0 <= i => i <= length xs =>
  (xs:::x).[i] = (i < length xs) ? xs.[i] : x.

lemma snoc_nonempty: forall (xs:'x array, x:'x),
  xs:::x <> empty
by [].

(* append *)
op (||): 'x array -> 'x array -> 'x array.

axiom append_length: forall (xs0 xs1:'x array),
  length (xs0 || xs1) = length xs0  + length xs1.

axiom append_get: forall (xs0 xs1:'x array) (i:int),
  (0 <= i => i < length xs0 => (xs0 || xs1).[i] = xs0.[i]) /\
  (length xs0 <= i => i < length (xs0 || xs1) => (xs0 || xs1).[i] = xs1.[i - length xs0]).

(* sub *)
op sub: 'x array -> int -> int -> 'x array.

axiom sub_length: forall (xs:'x array) (s l:int),
  0 <= s => 0 <= l => s + l <= length xs =>
  length (sub xs s l) = l.

axiom sub_get: forall (xs:'x array) (s l i:int),
  0 <= s => 0 <= l => s + l <= length xs =>
  0 <= i => i <= l =>
  (sub xs s l).[i] = xs.[i + s].

(* fold_left *)
op fold_right: ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state.

axiom fold_right_base: forall (f:'state -> 'x -> 'state) s,
  (fold_right f s empty) = s.

axiom fold_right_ind: forall (f:'state -> 'x -> 'state) s xs,
  0 < length xs =>
  (fold_right f s xs) = fold_right f (f s xs.[0]) (sub xs 1 (length xs - 1)).

(* fold_left *)
op fold_left: ('x -> 'state -> 'state) -> 'x array -> 'state -> 'state.

axiom fold_left_base: forall (f:'x -> 'state -> 'state) s,
  (fold_left f empty s) = s.

axiom fold_left_ind: forall (f:'x -> 'state -> 'state) s xs,
  0 < length xs =>
  (fold_left f xs s) = f xs.[0] (fold_left f (sub xs 1 (length xs - 1)) s).

(* map *)
op map: ('x -> 'y) -> 'x array -> 'y array.

axiom map_length: forall (xs:'x array, f:'x -> 'y),
  length (map f xs) = length xs.

axiom map_get: forall (xs:'x array, f:'x -> 'y, i:int),
  0 <= i => i < length(xs) =>
  (map f xs).[i] = f (xs.[i]).

(* map2 *) (* Useful for bitwise operations *)
op map2: ('x -> 'y -> 'z) -> 'x array -> 'y array -> 'z array.

axiom map2_length: forall (xs:'x array, ys:'y array, f:'x -> 'y -> 'z),
  length xs = length ys =>
  length (map2 f xs ys) = length xs.

axiom map2_get: forall (xs:'x array, ys:'y array, f:'x -> 'y -> 'z, i:int),
  length xs = length ys =>
  0 <= i => i < length xs =>
  (map2 f xs ys).[i] = f (xs.[i]) (ys.[i]).

(* lemmas *)
lemma sub_append_fst: forall (xs0 xs1:'x array),
  sub (xs0 || xs1) 0 (length(xs0)) = xs0.
proof.
intros xs0 xs1; apply extensionality; trivial.
save.

lemma sub_append_snd: forall (xs0 xs1:'x array),
  sub (xs0 || xs1) (length xs0) (length xs1) = xs1.
proof.
intros xs0 xs1; apply extensionality; trivial.
save.

(* Induction Principle *)
axiom induction: forall (p:'x array -> bool),
  p empty =>
  (forall x xs, p xs => p (x::xs)) =>
  (forall xs, p xs).

lemma fold_left_deterministic: forall (f1 f2:'x -> 'state -> 'state) s1 s2 xs1 xs2,
  f1 = f2 => s1 = s2 => xs1 = xs2 =>
  fold_left f1 xs1 s1 = fold_left f2 xs2 s2
by [].

(* This proof needs cleaned up, and the lemma library completed. *)
lemma fold_length: forall (xs:'x array),
  fold_left (lambda x n, n + 1) xs 0 = length xs.
proof.
intros xs.
apply (induction<:'x> (lambda xs', fold_left (lambda x n, n + 1) xs' 0 = length xs') _ _ xs).
trivial.
simplify.
intros x xs' IH.
cut length_def:(length (x::xs') = length xs' + 1); [ trivial | rewrite length_def;rewrite <- IH ].
cut sub_eq:(sub (x::xs') 1 (length (x::xs') - 1) = xs');[ apply extensionality; trivial | ].
cut fold_def:(fold_left (lambda x n, n + 1) xs' 0 = fold_left (lambda x n, n + 1) (sub (x::xs') 1 (length (x::xs') - 1)) 0);[ rewrite sub_eq | ].
apply (fold_left_deterministic<:int,'x> (lambda x n, n + 1) (lambda x n, n + 1) 0 0 xs' xs' _ _).
  apply (Fun.extensionality<:int -> int,'x> (lambda x n, n + 1) (lambda x n, n + 1) _).
  delta beta.
  intros x'. apply Fun.extensionality.
  delta beta. trivial.
trivial.
rewrite fold_def;clear fold_def.
apply (fold_left_ind<:int,'x> (lambda x n, n + 1) 0 (x::xs') _);trivial.
save.

(*********************************)
(*      Imperative Operators     *)
(*********************************)
op __set: 'x array -> int -> 'x -> 'x array.

axiom set_length: forall (xs:'x array, i:int, x:'x),
  0 <= i => i < length xs =>
  length (xs.[i <- x]) = length xs.

axiom set_get: forall (xs:'x array) (i j:int) (x:'x),
  0 <= i => i < length xs =>
  0 <= j => j < length xs =>
  xs.[i <- x].[j] = (i = j) ? x : xs.[j].

(* write: array -> offset -> array -> offset -> length -> array *)
op write: 'x array -> int -> 'x array -> int -> int -> 'x array.

axiom write_length: forall (dst src:'x array) (dOff sOff l:int),
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  length (write dst dOff src sOff l) = length dst.

axiom write_get: forall (dst src:'x array) (dOff sOff l i:int),
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  (0 <= i => i < dOff => (write dst dOff src sOff l).[i] = dst.[i]) /\
  (dOff <= i => i < dOff + l => (write dst dOff src sOff l).[i] = src.[i - dOff + sOff]) /\
  (dOff + l <= i => i < length dst => (write dst dOff src sOff l).[i] = dst.[i]).

(* init *)
op init: int -> 'x -> 'x array.

axiom init_length: forall (x:'x) l,
  0 <= l =>
  length (init l x) = l.

axiom init_get: forall (x:'x) l i,
  0 <= l => 0 <= i => i < l =>
  (init l x).[i] = x.

(*********************************)
(*       Some Mixed Lemmas       *)
(*********************************)
lemma write_append: forall (dst src:'x array),
  length src <= length dst =>
  write dst 0 src 0 (length src) = (src || (sub dst (length src) (length dst - length src))).
proof.
intros dst src H; apply extensionality.
delta beta;split;trivial.
save.
