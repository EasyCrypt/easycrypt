require import Int.

(* -------------------------------------------------------------------- *)
type class addmonoid = {
  op idm : addmonoid
  op (+) : addmonoid -> addmonoid -> addmonoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* -------------------------------------------------------------------- *)
lemma addm0 ['a <: addmonoid] : right_id idm (+)<:'a>.
proof. by move=> x; rewrite addmC add0m. qed.

lemma addmCA ['a <: addmonoid] : left_commutative (+)<:'a>.
proof. by move=> x y z; rewrite !addmA (addmC x). qed.

lemma addmAC ['a <: addmonoid] : right_commutative (+)<:'a>.
proof. by move=> x y z; rewrite -!addmA (addmC y). qed.

lemma addmACA ['a <: addmonoid] : interchange (+)<:'a> (+)<:'a>.
proof. by move=> x y z t; rewrite -!addmA (addmCA y). qed.

lemma iteropE ['a <: addmonoid] n x: iterop n (+)<:'a> x idm<:'a> = iter n ((+)<:'a> x) idm<:'a>.
proof.
  elim/natcase n => [n le0_n|n ge0_n].
  + by rewrite ?(iter0, iterop0).
  + by rewrite iterSr // addm0 iteropS.
qed.

(* -------------------------------------------------------------------- *)
abstract theory AddMonoid.
  type t.

  op idm : t.
  op (+) : t -> t -> t.

  theory Axioms.
    axiom nosmt addmA: associative (+).
    axiom nosmt addmC: commutative (+).
    axiom nosmt add0m: left_id idm (+).
  end Axioms.

  instance addmonoid with t
    op idm = idm
    op (+)  = (+).

  realize addmA by exact Axioms.addmA.
  realize addmC by exact Axioms.addmC.
  realize add0m by exact Axioms.add0m.

end AddMonoid.
