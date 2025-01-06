(* -------------------------------------------------------------------- *)
require import AllCore Bool StdRing StdOrder.
(*---*) import RField RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op down (E : real -> bool) =
  fun x => exists y, E y /\ x <= y.

(* -------------------------------------------------------------------- *)
lemma downK E : down (down E) = down E.
proof.
apply/fun_ext=> x; apply/eq_iff; split; last first.
+ by move=> Ex; exists x; split.
case=> y [[z [Ez le_yz]] le_xy]; exists z.
by split => //; apply/(ler_trans y).
qed.

(* -------------------------------------------------------------------- *)
lemma le_down E : E <= down E.
proof. by move=> x Ex; exists x; split. qed.

(* -------------------------------------------------------------------- *)
lemma has_lub_down E : has_lub (down E) <=> has_lub E.
proof. split; case=> nz hub.
+ split; first by case: nz=> x [y [Ey _]]; exists y.
  by case: hub=> x hub; exists x => y /le_down /hub.
+ split; first by case: nz => x /le_down ?; exists x.
  case: hub => x hub; exists x => y [z [Ez le_zy]].
  by apply/(ler_trans _ le_zy)/hub.
qed.

(* -------------------------------------------------------------------- *)
lemma ler_lub_down (E1 E2 : real -> bool) :
  (E1 <= down E2) => has_lub E2 => nonempty E1 => lub E1 <= lub E2.
proof.
move=> le lub2 [x E1x]; have {x E1x} lub1: has_lub E1.
  split; [exists x | exists (lub E2)]; move=> // y.
  by move/le=> [z] [E2z /ler_trans]; apply; apply/lub_upper_bound.
rewrite lerNgt -subr_gt0; apply/negP => lt_sup.
case: (lub_adherent _ lub1 _ lt_sup)=> x [/le [z [E2z le_xz]]].
rewrite opprD !addrA subrr add0r opprK => lt_S2x.
have := ltr_le_trans _ _ _ lt_S2x le_xz; rewrite ltrNge /=.
by apply/lub_upper_bound.
qed.

(* -------------------------------------------------------------------- *)
lemma ler_lub (E1 E2 : real -> bool) :
     (forall x, E1 x => exists y, E2 y /\ x <= y)
  => has_lub E2 => nonempty E1 => lub E1 <= lub E2.
proof. by move=> le12 lub2 nz1; apply: ler_lub_down. qed.

(* -------------------------------------------------------------------- *)
lemma lub_down E : has_lub E => lub (down E) = lub E.
proof.
move=> lubE; rewrite eqr_le !ler_lub_down //.
+ by move: lubE; rewrite -has_lub_down; case.
+ by rewrite downK le_down.
+ by rewrite has_lub_down.
+ by case: lubE.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_lub (E1 E2 : real -> bool) :
  (forall x, E1 x <=> E2 x) => lub E1 = lub E2.
proof.
move=> eqE; have /fun_ext ->//: forall x, E1 x = E2 x.
by move=> x; apply/eq_iff/eqE.
qed.

(* -------------------------------------------------------------------- *)
lemma lub_le_ub E z : has_lub E => ub E z => lub E <= z.
proof.
move=> hlE ub_Ez; rewrite lerNgt &(negP) => lt_zlE.
case: (lub_adherent _ hlE (lub E - z) _); 1: by rewrite subr_gt0.
move=> e [eE]; rewrite opprB addrCA subrr addr0.
by rewrite ltrNge /=; apply: ub_Ez.
qed.

(* -------------------------------------------------------------------- *)
lemma lub1 x : lub (pred1 x) = x.
proof.
apply eqr_le; split; [apply lub_le_ub => /#|move => _].
apply lub_upper_bound; smt().
qed.

(* -------------------------------------------------------------------- *)

(* used to prove linearity of [flub], where the lub may be a limit *)
op scale_rset (E: real -> bool) c x = exists x0, E x0 /\ c * x0 = x.

lemma lub_scale0 E : nonempty E => lub (scale_rset E 0%r) = 0%r.
proof.
move => [x x_E]; have -> : scale_rset E 0%r = pred1 0%r. 
- (* CD: locally smt() does the job in a fraction of a sectiond *)
  apply/fun_ext => z @/scale_rset @/pred1. 
  by apply/eq_iff; split => />; exists x.
by rewrite lub1.
qed.

lemma has_lub_scale E c : 0%r <= c =>
  has_lub E => has_lub (scale_rset E c).
proof.
move => c_ge0 [[x Ex] ?]; split; 1: smt().
exists (c * lub E) => cx; smt(lub_upper_bound).
qed.

lemma lub_scale E c : has_lub E =>
  c >= 0%r => lub (scale_rset E c) = c * lub E.
proof.
move => has_lubE ge0_c.
case (c > 0%r) => [gt0_c|]; last by smt(lub_scale0).
apply eqr_le; split => [|_].
- apply lub_le_ub; first by apply has_lub_scale.
  smt(lub_upper_bound).
rewrite -ler_pdivl_mull //; apply lub_le_ub => // x Ex.
by rewrite ler_pdivl_mull //; smt(lub_upper_bound has_lub_scale). 
qed.

(* -------------------------------------------------------------------- *)
lemma lub_cBf (E : real -> bool) : nonempty E =>
  lub (fun x => exists y, E y /\ x = (ceil y - floor y)%r)
    = b2r (exists x, E x /\ !isint x).
proof.
case=> z Ez; pose P (x : real) := exists (y : real),
  E y /\ x = (ceil y - floor y)%r.
have hlP: has_lub P; first split.
- exists ((ceil z)%r - (floor z)%r); smt().
  exists 1%r => x [y] [_ ->>]; smt(cBf_eq0P cBf_eq1P).
rewrite RealOrder.eqr_le; split=> [|_].
- apply: lub_le_ub => // x [y] [Ey ->>]; case: (isint y).
  - by move/cBf_eq0P => -> /#.
  - by move=> ^/cBf_eq1P -> Nint_y; rewrite iftrue //; exists y.
- apply: lub_upper_bound => //; case: (exists x, E x /\ !isint x).
  - by case=> x [Ex /cBf_eq1P Nint_x] @/P; exists x; rewrite Nint_x.
  rewrite negb_exists /= => /(_ z); rewrite Ez /=.
  by move/cBf_eq0P => int_z; exists z; rewrite int_z.
qed.
