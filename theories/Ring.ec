(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun.

(* -------------------------------------------------------------------- *)
theory ZModule.
  type t.

  op zeror : t.
  op ( + ) : t -> t -> t.
  op [ - ] : t -> t.

  axiom addrA: forall (x y z : t), x + (y + z) = (x + y) + z.
  axiom addrC: forall (x y   : t), x + y = y + x.
  axiom add0r: forall (x     : t), zeror + x = x.
  axiom addNr: forall (x     : t), (-x) + x = zeror.

  op ( - ) (x y : t) = x + -y axiomatized by subrE.

  lemma nosmt addr0 (x : t): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN (x : t): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma nosmt addrCA (x y z : t):
    x + (y + z) = y + (x + z).
  proof. by rewrite !addrA (addrC x y). qed.

  lemma nosmt addrAC (x y z : t):
    (x + y) + z = (x + z) + y.
  proof. by rewrite -!addrA (addrC y z). qed.

  lemma nosmt subrr (x : t): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr (x y : t): -x + (x + y) = y.
  proof. by rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr (x y : t): x + (-x + y) = y.
  proof. by rewrite addrA addrN add0r. qed.

  lemma nosmt addrK (y x : t): (x + y) + -y = x.
  proof. by rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK (x y : t): (x + -y) + y = x.
  proof. by rewrite -addrA addNr addr0. qed.

  lemma nosmt addrI (x y z : t): x + y = x + z => y = z.
  proof. by move=> h; rewrite -(addKr x z) -h addKr. qed.

  lemma nosmt addIr (x y z : t): y + x = z + x => y = z.
  proof. by move=> h; rewrite -(addrK x z) -h addrK. qed.

  lemma nosmt opprK (x : t): -(-x) = x.
  proof. by apply (addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 (x : t): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : t): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD (x y : t): -(x + y) = -x + -y.
  proof.
    by apply (addrI (x + y)); rewrite addrA addrN addrAC addrK addrN.
  qed.

  lemma nosmt opprB (x y : t): -(x - y) = y - x.
  proof. by rewrite subrE /= opprD opprK addrC. qed.

  lemma nosmt subr_eq (x y z : t):
    (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite subrE /= addrNK.
    by move=> {x} x /=; rewrite subrE /= addrK.
  qed.

  lemma nosmt subr_eq0 (x y : t): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 (x y : t): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp (x y : t): (- x = - y) <=> (x = y).
  proof.
    move: (can_eq (fun z, -z) (fun z, -z) _ x y) => //=.
    by move=> z /=; rewrite opprK.
  qed.
end ZModule.

(* -------------------------------------------------------------------- *)
theory ComRing.
  type t.

  clone export ZModule with type t <- t.

  op oner  : t.
  op ( * ) : t -> t -> t.

  axiom oner_neq0 : oner <> zeror.
  axiom mulrA     : forall (x y z : t), x * (y * z) = (x * y) * z.
  axiom mulrC     : forall (x y   : t), x * y = y * x.
  axiom mul1r     : forall (x     : t), oner * x = x.
  axiom mulrDl    : forall (x y z : t), (x + y) * z = (x * z) + (y * z).

  lemma nosmt mulr1 (x : t): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr (x y z : t):
    x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.
end ComRing.

(* -------------------------------------------------------------------- *)
theory BoolRing.
  type t.

  clone export ComRing with type t <- t.

  axiom mulrr : forall (x : t), x * x = x.

  lemma nosmt addrK (x : t): x + x = zeror.
  proof.
    apply (addrI (x + x)); rewrite addr0 -{1 2 3 4}mulrr.
    by rewrite -mulrDr -mulrDl mulrr.
  qed.
end BoolRing.

(* -------------------------------------------------------------------- *)
theory IDomain.
  type t.

  clone export ComRing with type t <- t.

  axiom mulf_eq0:
    forall (x y : t), x * y = zeror => x = zeror \/ y = zeror.
end IDomain.

(* -------------------------------------------------------------------- *)
theory Field.
  type t.

  clone export IDomain with type t <- t.

  op inv: t -> t.

  axiom mulVf: forall (x : t), x <> zeror => (inv x) * x = oner.
end Field.
