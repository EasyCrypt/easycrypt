import why3 "option" "Option".

op option_rect: 'a -> ('b -> 'a) -> 'b option -> 'a.
axiom nosmt option_rect_none (v:'a) (f:'b -> 'a):
  option_rect v f None = v.
axiom nosmt option_rect_some (v:'a) (f:'b -> 'a) (x:'b):
  option_rect v f (Some x) = f x.

lemma nosmt option_free (x:'a option):
  Some x <> None
by [].

lemma nosmt option_lfp (x:'a option):
  x = None \/ (exists y, x = Some y)
by [].

lemma nosmt option_case_eq (p:'a option -> bool) x:
  (x = None => p x) =>
  ((exists y, x = Some y) => p x) =>
  p x
by [].

lemma nosmt option_case (p:'a option -> bool):
  p None =>
  (forall x, p (Some x)) =>
  (forall x, p x).
proof strict.
intros=> p_none p_some x; apply option_case_eq.
  by intros=> ->.
  by intros=> [y x_some]; rewrite x_some; apply p_some.
qed.

(* NOTE: This (and Why3) assume that all types are inhabited
   and interacts very badly with Coq. Don't use Coq until we
   figure out how Why3 deals with it. *)
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
  x = y.
proof strict.
by rewrite -{2}(proj_some x) -{2}(proj_some y)=> some_eq; congr.
qed.

lemma nosmt some_proj (x:'a option):
  x <> None =>
  Some (proj x) = x
by [].

(* lift: lift functions to the option type *)
op lift: ('a -> 'b) -> ('a option -> 'b option).

axiom lift_None (f:'a -> 'b):
  (lift f) None = None.

axiom lift_Some (f:'a -> 'b) (x:'a):
  (lift f) (Some x) = Some (f x).

