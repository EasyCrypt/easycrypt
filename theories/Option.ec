type 'a option = [
  | None
  | Some of 'a
].

op option_rect (v:'a) (f:'b -> 'a) xo =
  with xo = None   => v
  with xo = Some x => f x.

lemma nosmt option_rect_none (v:'a) (f:'b -> 'a):
  option_rect v f None = v
by iota.

lemma nosmt option_rect_some (v:'a) (f:'b -> 'a) (x:'b):
  option_rect v f (Some x) = f x
by iota.

(** Projection functions *)
op proj_def (d:'a) xo =
  with xo = None   => d
  with xo = Some x => x.

op proj:'a option -> 'a.
axiom proj_some (x:'a): proj (Some x) = x.

lemma nosmt projI (x y:'a) x' y':
  x' = Some x =>
  y' = Some y =>
  proj x' = proj y' =>
  x = y.
proof strict.
by intros=> -> ->; rewrite !proj_some.
qed.

lemma nosmt someI (x y:'a):
  Some x = Some y =>
  x = y
by [].

lemma nosmt some_proj (x:'a option):
  x <> None =>
  Some (proj x) = x
by [].

(** Useful tools *)
(* lift: lift functions to the option type *)
op lift (f:'a -> 'b) xo =
  with xo = None => None
  with xo = Some x => Some (f x).

lemma lift_None (f:'a -> 'b):
  (lift f) None = None
by iota.

lemma lift_Some (f:'a -> 'b) (x:'a):
  (lift f) (Some x) = Some (f x)
by iota.