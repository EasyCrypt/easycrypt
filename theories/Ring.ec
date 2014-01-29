(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
theory ZModule.
  require import Fun.

  type zmodule.

  op zeror : zmodule.

  op ( + ) : zmodule -> zmodule -> zmodule.
  op [ - ] : zmodule -> zmodule.

  op ( - ) (x y : zmodule) = x + -y axiomatized by subrE.

  axiom nosmt addrA (x y z : zmodule): x + (y + z) = (x + y) + z.
  axiom nosmt addrC (x y   : zmodule): x + y = y + x.
  axiom nosmt add0r (x     : zmodule): zeror + x = x.
  axiom nosmt addNr (x     : zmodule): (-x) + x = zeror.

  lemma nosmt addr0 (x : zmodule): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN (x : zmodule): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma addrCA (x y z): x + (y + z) = y + (x + z).
  proof. by rewrite !addrA (addrC x y). qed.

  lemma addrAC (x y z): (x + y) + z = (x + z) + y.
  proof. by rewrite -!addrA (addrC y z). qed.

  lemma nosmt subrr (x : zmodule): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr (x y : zmodule): -x + (x + y) = y.
  proof. by rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr (x y : zmodule): x + (-x + y) = y.
  proof. by rewrite addrA addrN add0r. qed.

  lemma nosmt addrK (y x : zmodule): (x + y) + -y = x.
  proof. by rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK (x y : zmodule): (x + -y) + y = x.
  proof. by rewrite -addrA addNr addr0. qed.

  lemma nosmt addrI (x y z : zmodule): x + y = x + z => y = z.
  proof. cut := addKr x; smt. qed.

  lemma nosmt addIr (x y z : zmodule): y + x = z + x => y = z.
  proof. cut := addrK x; smt. qed.

  lemma nosmt opprK (x : zmodule): -(-x) = x.
  proof. by apply (addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 (x : zmodule): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : zmodule): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD (x y : zmodule): -(x + y) = -x + -y.
  proof.
    by apply (addrI (x + y)); rewrite addrA addrN addrAC addrK addrN.
  qed.

  lemma nosmt opprB (x y : zmodule): -(x - y) = y - x.
  proof. by rewrite subrE /= opprD opprK addrC. qed.

  lemma nosmt subr_eq x y z : (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite subrE /= addrNK.
    by move=> {x} x /=; rewrite subrE /= addrK.
  qed.

  lemma nosmt subr_eq0 (x y : zmodule): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 (x y : zmodule): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp (x y : zmodule): (- x = - y) <=> (x = y).
  proof.
    move: (can_eq (fun z, -z) (fun z, -z) _ x y) => //=.
    by move=> z /=; rewrite opprK.
  qed.
end ZModule.

(* -------------------------------------------------------------------- *)
theory R.
  require import Fun.

  type ring.

  op zeror : ring.
  op oner  : ring.

  op ( + ) : ring -> ring -> ring.
  op [ - ] : ring -> ring.
  op ( * ) : ring -> ring -> ring.

  op ( - ) (x y : ring) = x + -y axiomatized by subrE.

  axiom nosmt oner_neq0 : oner <> zeror.

  axiom nosmt addrA (x y z : ring): x + (y + z) = (x + y) + z.
  axiom nosmt addrC (x y   : ring): x + y = y + x.
  axiom nosmt add0r (x     : ring): zeror + x = x.
  axiom nosmt addNr (x     : ring): (-x) + x = zeror.

  axiom nosmt mulrA  (x y z : ring): x * (y * z) = (x * y) * z.
  axiom nosmt mulrC  (x y   : ring): x * y = y * x.
  axiom nosmt mul1r  (x     : ring): oner * x = x.
  axiom nosmt mulrDl (x y z : ring): (x + y) * z = x * z + y * z.

  lemma nosmt addr0 (x : ring): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN (x : ring): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma nosmt subrr (x : ring): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr (x y : ring): -x + (x + y) = y.
  proof. by rewrite addrA addNr add0r. qed.

  lemma nosmt addrK (y x : ring): (x + y) + -y = x.
  proof. by rewrite -addrA addrN addr0. qed.

  lemma nosmt addrI (x y z : ring): x + y = x + z => y = z.
  proof. cut := addKr x; smt. qed.

  lemma nosmt addIr (x y z : ring): y + x = z + x => y = z.
  proof. cut := addrK x; smt. qed.

  lemma nosmt opprK (x : ring): -(-x) = x.
  proof. by apply (addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 (x : ring): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : ring): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt mulr1 (x : ring): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr (x y z : ring): x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.
end R.

(* -------------------------------------------------------------------- *)
theory IDomain.
  clone export R.

  axiom nosmt integral (x y : ring):
    x * y = zeror => (x = zeror) \/ (y = zeror).
end IDomain.
