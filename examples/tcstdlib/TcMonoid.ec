require import Int.

(* -------------------------------------------------------------------- *)
type class monoid = {
  op idm : monoid
  op (+) : monoid -> monoid -> monoid

  axiom addmA: associative (+)
  axiom addmC: commutative (+)
  axiom add0m: left_id idm (+)
}.

(* -------------------------------------------------------------------- *)
section.
declare type m <: monoid.

lemma addm0: right_id idm (+)<:m>.
proof. by move=> x; rewrite addmC add0m. qed.

lemma addmCA: left_commutative (+)<:m>.
proof. by move=> x y z; rewrite !addmA (addmC x). qed.

lemma addmAC: right_commutative (+)<:m>.
proof. by move=> x y z; rewrite -!addmA (addmC y). qed.

lemma addmACA: interchange (+)<:m> (+).
proof. by move=> x y z t; rewrite -!addmA (addmCA y). qed.

lemma iteropE n (x : m): iterop n (+) x idm = iter n ((+) x) idm.
proof.
elim/natcase n => [n le0_n|n ge0_n].
+ by rewrite ?(iter0, iterop0).
+ by rewrite iterSr // addm0 iteropS.
qed.
end section.
