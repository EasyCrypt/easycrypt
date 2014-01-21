(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
op witness : 'a.                (* All types are inhabited in EC *)

(* -------------------------------------------------------------------- *)
type 'a option = [None | Some of 'a].

op option_rect (v:'a) (f:'b -> 'a) xo =
  with xo = None   => v
  with xo = Some x => f x.

op oapp ['a 'b] (f : 'a -> 'b) d ox : 'b =
  with ox = None   => d
  with ox = Some x => f x.

op odflt (d : 'a) ox =
  with ox = None   => d
  with ox = Some x => x.

op obind ['a 'b] (f : 'a -> 'b option) ox =
  with ox = None   => None
  with ox = Some x => f x.

op omap ['a 'b] (f : 'a -> 'b) ox =
  with ox = None   => None
  with ox = Some x => Some (f x).

op oget (ox : 'a option) = odflt witness<:'a> ox.

lemma nosmt oget_none: oget None<:'a> = witness.
proof. by []. qed.

lemma nosmt oget_some (x : 'a): oget (Some x) = x.
proof. by []. qed.

lemma nosmt someI (x y:'a): Some x = Some y => x = y by [].
