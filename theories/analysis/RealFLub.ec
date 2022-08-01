(* -------------------------------------------------------------------- *)
require import AllCore Bool StdRing StdOrder RealLub.
(*---*) import RField RealOrder.

pragma +implicits.

(* lub for functions *)
op flub (F : 'a -> real) : real = lub (fun r => exists a, F a = r).
op is_fub (f: 'a -> real) r = forall x, f x <= r.
op has_fub (f: 'a -> real) = exists r, is_fub f r.

lemma has_fub_lub (f: 'a -> real) :
  has_fub f <=> has_lub (fun r => exists a, f a = r).
proof.
split.
- move => [r ub_r]; split; first (exists (f witness) => /#).
  exists r => /#.
- move => has_lub_imgf; exists (flub f) => ?.
  apply lub_upper_bound => /#.
qed.

lemma flub_upper_bound (F : 'a -> real) x : 
    has_fub F => F x <= flub F.
proof.
move => H; rewrite has_fub_lub in H.
apply lub_upper_bound => /#.
qed.

lemma flub_le_ub (F : 'a -> real) r :
    is_fub F r => flub F <= r.
proof.
move => H.
have ub_r : ub (fun (x : real) => exists (a : 'a), F a = x) r.
  move => y [a] <-; exact H.
apply lub_le_ub => //. 
split; [by exists (F witness) witness| by exists r].
qed.

lemma flub_le (f g: 'a -> real) :
  has_fub g =>
  (forall x, f x <= g x) => flub f <= flub g.
proof.
move => [ym is_ub_ym] le_fg; rewrite ler_lub //=; 1: smt(); 2: exists (f witness) => /#.
split; first exists (g witness) => /#.
exists ym; smt(has_fub_lub).
qed.

lemma flub_scale (f: 'a -> real) c :
  has_fub f =>
  c >= 0%r =>
  flub (fun x => c * f x) = c * flub f.
proof.
move => H ge0_c; rewrite -lub_scaleE => //.
rewrite has_fub_lub in H => //.
apply eq_lub => /#.
qed.

lemma flub_const c :
  flub (fun _ : 'a => c) = c.
proof.
apply eqr_le; split; first apply flub_le_ub => /#.
move => _; apply (@flub_upper_bound (fun _ => c) witness) => /#.
qed.

lemma has_fub_leq (f g: 'a -> real) :
  has_fub g =>
  (forall x, f x <= g x) =>
  has_fub f.
proof. move => [??] /#. qed.

lemma has_fub_scale (f: 'a -> real) c:
  has_fub f =>
  c >= 0%r =>
  has_fub (fun x => c * f x).
proof. move => [ym ub_ym] ge0_c; exists (c * ym) => /#. qed.
