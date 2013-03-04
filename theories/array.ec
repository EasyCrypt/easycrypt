require import int.

(* We first define the type, its destructors, and its equality *)
type 'x array.

op length: 'x array -> int.
  axiom length_pos: forall (xs:'x array), 0 <= length xs.

op __get: ('x array,int) -> 'x.

pred [==] (xs0:'x array, xs1:'x array) =
  length xs0 = length xs1 /\
  forall (i:int), 0 <= i => i < length xs0 => xs0.[i] = xs1.[i].

axiom extentionality: forall (xs0:'x array, xs1:'x array),
  xs0 == xs1 => xs0 = xs1.

lemma eq_extent: forall (xs0, xs1:'x array),
  length xs0 = length xs1 =>
  (forall (i:int), 0 <= i => i < length xs0 => xs0.[i] = xs1.[i]) =>
  xs0 = xs1.

(* We define the rest (axiomatically, since we don't have proper induction/iteration in the term language) *)
(* A functional theory of arrays: empty, cons, append and sub*)
theory Functional.
  (* empty *)
  cnst empty: 'x array.

  axiom empty_length: length (empty<:'x>) = 0.

  lemma empty_unique: forall (xs:'x array),
    length(xs) = 0 => xs = empty
  proof.
  intros xs H.
  apply extentionality<:'x>(xs,empty,_).
  trivial.
  save.

  (* cons *)
  op [::]: ('x,'x array) -> 'x array.

  axiom cons_length: forall (x:'x, xs:'x array),
    length (x::xs) = 1 + length xs.

  axiom cons_get: forall (x:'x, xs:'x array, i:int),
    0 <= i => i <= length xs =>
    (x::xs).[i] = (0 = i) ? x : xs.[i - 1].

  lemma cons_nonempty: forall (x:'x, xs:'x array),
    x::xs <> empty.

  (* snoc *)
  op [:::]: ('x array,'x) -> 'x array.

  axiom snoc_length: forall (xs:'x array, x:'x),
    length (xs:::x) = length xs + 1.

  axiom snoc_get: forall (xs:'x array, x:'x, i:int),
    0 <= i => i <= length xs =>
    (xs:::x).[i] = (0 < length xs) ? xs.[i] : x.

  lemma snoc_nonempty: forall (xs:'x array, x:'x),
    xs:::x <> empty.

  (* append *)
  op [||]: ('x array,'x array) -> 'x array.

  axiom append_length: forall (xs0, xs1:'x array),
    length (xs0 || xs1) = length xs0  + length xs1.

  axiom append_get: forall (xs0, xs1:'x array, i:int),
    (0 <= i => i < length xs0 => (xs0 || xs1).[i] = xs0.[i]) /\
    (length xs0 <= i => i < length (xs0 || xs1) => (xs0 || xs1).[i] = xs1.[i - length xs0]).

  (* sub *)
  op sub: 'x array -> int -> int -> 'x array.

  axiom sub_length: forall (xs:'x array, s, l:int),
    0 <= s => 0 <= l => s + l <= length xs =>
    length (sub xs s l) = l.

  axiom sub_get: forall (xs:'x array, s, l, i:int),
    0 <= s => 0 <= l => s + l <= length xs =>
    0 <= i => i <= l =>
    (sub xs s l).[i] = xs.[i + s].

  (* map *)
  op map: ('x -> 'x) -> 'x array -> 'x array.

  axiom map_length: forall (xs:'x array, f:'x -> 'x),
    length (map f xs) = length xs.

  axiom map_get: forall (xs:'x array, f:'x -> 'x, i:int),
    0 <= i => i < length(xs) =>
    (map f xs).[i] = f (xs.[i]).

  (* lemmas *)
  lemma sub_append_fst: forall (xs0, xs1:'x array),
    sub (xs0 || xs1) 0 (length(xs0)) = xs0
  proof.
    intros xs0 xs1.
    apply extentionality<:'x> ((sub (xs0 || xs1) 0 (length xs0)),xs0,_).
    trivial.
  save.

  lemma sub_append_snd: forall (xs0, xs1:'x array),
    sub (xs0 || xs1) (length xs0) (length xs1) = xs1
  proof.
    intros xs0 xs1.
    apply extentionality<:'x> ((sub (xs0 || xs1) (length xs0) (length xs1)),xs1,_).
    trivial.
  save.
end Functional.

theory Imperative.
  (* set: array * offset * value -> array *)
  op __set: ('x array,int,'x) -> 'x array.

  axiom set_length: forall (xs:'x array, i:int, x:'x),
    0 <= i => i < length xs =>
    length (xs.[i <- x]) = length xs.

  axiom set_get: forall (xs:'x array, i, j:int, x:'x),
    0 <= i => i < length xs =>
    0 <= j => j < length xs =>
    xs.[i <- x].[j] = (i = j) ? x : xs.[j].

  (* write: array -> offset -> array -> offset -> length -> array *)
  op write: 'x array -> int -> 'x array -> int -> int -> 'x array.

  axiom write_length: forall (dst, src:'x array, dOff, sOff, l:int),
    0 <= dOff => 0 <= sOff => 0 <= l =>
    dOff + l <= length dst =>
    sOff + l <= length src =>
    length (write dst dOff src sOff l) = length dst.

  axiom write_get: forall (dst, src:'x array, dOff, sOff, l, i:int),
    0 <= dOff => 0 <= sOff => 0 <= l =>
    dOff + l <= length dst =>
    sOff + l <= length src =>
    (0 <= i => i < dOff => (write dst dOff src sOff l).[i] = dst.[i]) &&
    (dOff <= i => i < dOff + l => (write dst dOff src sOff l).[i] = src.[i - dOff + sOff]) &&
    (dOff + l <= i => i < length dst => (write dst dOff src sOff l).[i] = dst.[i]).
end Imperative.

theory Mixed.
  import Imperative.
  import Functional.

  lemma write_append: forall (dst, src:'x array),
    length src <= length dst =>
    write dst 0 src 0 (length src) = (src || (sub dst (length src) (length dst - length src)))
  proof.
  intros dst src H.
  apply extentionality<:'x> ((write dst 0 src 0 (length src)),(src || sub dst (length src) (length dst - length src)),_).
  trivial.
  save.
end Mixed.