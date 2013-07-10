import why3 "option" "Option".

op option_rect: 'a -> ('b -> 'a) -> 'b option -> 'a.
axiom nosmt option_rect_none: forall (v:'a) (f:'b -> 'a),
  option_rect v f None = v.
axiom nosmt option_rect_some: forall (v:'a) (f:'b -> 'a) (x:'b),
  option_rect v f (Some x) = f x.

lemma nosmt option_case_eq: forall (p:'a option -> bool) x,
  (x = None => p x) =>
  ((exists y, x = Some y) => p x) =>
  p x
by [].

lemma nosmt option_case: forall (p:'a option -> bool),
  p None =>
  (forall x, p (Some x)) =>
  (forall x, p x).
proof strict.
intros=> p p_none p_some x; apply option_case_eq.
  by intros=> ->.
  by intros=> [y x_some]; rewrite x_some; apply p_some.
qed.

(* NOTE: This (and Why3) assume that all types are inhabited
   and interacts very badly with Coq. Don't use Coq until we
   figure out how Why3 deals with it. *)
op proj:'a option -> 'a.
axiom proj_some: forall (x:'a), proj (Some x) = x.
