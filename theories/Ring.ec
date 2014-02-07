(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun.

(* -------------------------------------------------------------------- *)
theory ZModule.
  type class zmodule = {
    op zeror : zmodule
    op ( + ) : zmodule -> zmodule -> zmodule
    op [ - ] : zmodule -> zmodule

    axiom addrA: forall (x y z : zmodule), x + (y + z) = (x + y) + z
    axiom addrC: forall (x y   : zmodule), x + y = y + x
    axiom add0r: forall (x     : zmodule), zeror + x = x
    axiom addNr: forall (x     : zmodule), (-x) + x = zeror
  }.

  op ( - ) ['a <: zmodule] (x y : 'a) = x + -y axiomatized by subrE.

  lemma nosmt addr0 ['a <: zmodule] (x : 'a): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN ['a <: zmodule] (x : 'a): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma nosmt addrCA ['a <: zmodule] (x y z : 'a):
    x + (y + z) = y + (x + z).
  proof. by rewrite !addrA (addrC x y). qed.

  lemma nosmt addrAC ['a <: zmodule] (x y z : 'a):
    (x + y) + z = (x + z) + y.
  proof. by rewrite -!addrA (addrC y z). qed.

  lemma nosmt subrr ['a <: zmodule] (x : 'a): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr ['a <: zmodule] (x y : 'a): -x + (x + y) = y.
  proof. by rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr ['a <: zmodule] (x y : 'a): x + (-x + y) = y.
  proof. by rewrite addrA addrN add0r. qed.

  lemma nosmt addrK ['a <: zmodule] (y x : 'a): (x + y) + -y = x.
  proof. by rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK ['a <: zmodule] (x y : 'a): (x + -y) + y = x.
  proof. by rewrite -addrA addNr addr0. qed.

  lemma nosmt addrI ['a <: zmodule] (x y z : 'a): x + y = x + z => y = z.
  proof. by move=> h; rewrite -(addKr x z) -h addKr. qed.

  lemma nosmt addIr ['a <: zmodule] (x y z : 'a): y + x = z + x => y = z.
  proof. by move=> h; rewrite -(addrK x z) -h addrK. qed.

  lemma nosmt opprK ['a <: zmodule] (x : 'a): -(-x) = x.
  proof. by apply (addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0 ['a <: zmodule]: -zeror<:'a> = zeror.
  proof. by rewrite -(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 ['a <: zmodule](x : 'a): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r ['a <: zmodule](x : 'a): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD ['a <: zmodule](x y : 'a): -(x + y) = -x + -y.
  proof.
    by apply (addrI (x + y)); rewrite addrA addrN addrAC addrK addrN.
  qed.

  lemma nosmt opprB ['a <: zmodule] (x y : 'a): -(x - y) = y - x.
  proof. by rewrite subrE /= opprD opprK addrC. qed.

  lemma nosmt subr_eq ['a <: zmodule] (x y z : 'a):
    (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite subrE /= addrNK.
    by move=> {x} x /=; rewrite subrE /= addrK.
  qed.

  lemma nosmt subr_eq0 ['a <: zmodule] (x y : 'a): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 ['a <: zmodule] (x y : 'a): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp ['a <: zmodule] (x y : 'a): (- x = - y) <=> (x = y).
  proof.
    move: (can_eq (fun z, -z) (fun z, -z) _ x y) => //=.
    by move=> z /=; rewrite opprK.
  qed.
end ZModule.

(* -------------------------------------------------------------------- *)
theory ComRing.
  export ZModule.

  type class ring <: zmodule = {
    op oner  : ring
    op ( * ) : ring -> ring -> ring

    axiom oner_neq0 : oner <> zeror
    axiom mulrA     : forall (x y z : ring), x * (y * z) = (x * y) * z
    axiom mulrC     : forall (x y   : ring), x * y = y * x
    axiom mul1r     : forall (x     : ring), oner * x = x
    axiom mulrDl    : forall (x y z : ring), (x + y) * z = (x * z) + (y * z)
  }.

  lemma nosmt mulr1 ['a <: ring] (x : 'a): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr ['a <: ring] (x y z : 'a):
    x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.
end ComRing.

(* -------------------------------------------------------------------- *)
theory BoolRing.
  export ComRing.

  type class bring <: ring = {
    axiom mulrr : forall (x : bring), x * x = x
  }.

  lemma nosmt addrK ['a <: bring] (x : 'a): x + x = zeror.
  proof. by apply (addrI (x + x)); rewrite addr0 -{1 2 3 4}mulrr -mulrDr -mulrDl mulrr. qed.
end BoolRing.

(* -------------------------------------------------------------------- *)
theory IDomain.
  export ComRing.

  type class idomain <: ring = {
    axiom mulf_eq0: forall (x y : idomain), 
      x * y = zeror => x = zeror \/ y = zeror
  }.
end IDomain.

(* -------------------------------------------------------------------- *)
theory Field.
  export IDomain.

  type class field <: ring = {
    op inv : field -> field

    axiom mulVf : forall (x : field), x <> zeror => (inv x) * x = oner
  }.
end Field.
