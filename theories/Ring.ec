(* -------------------------------------------------------------------- *)
theory Ring.
  require import Fun.

  type ring.

  op zeror : ring.
  op oner  : ring.

  op ( + ) : ring -> ring -> ring.
  op [ - ] : ring -> ring.
  op ( * ) : ring -> ring -> ring.

  op ( - ) (x y : ring) = x + -y.

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

  lemma nosmt subrr (x : ring): x - x = zeror by apply addrN.

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

  lemma subr0 (x : ring): x - zeror = x.
  proof. by rewrite /Ring.(-) oppr0 addr0. qed.

  lemma sub0r (x : ring): zeror - x = - x.
  proof. by rewrite /Ring.(-) add0r. qed.

  lemma nosmt mulr1 (x : ring): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr (x y z : ring): x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.
end Ring.

(* -------------------------------------------------------------------- *)
theory IDomain.
  clone export Ring.

  axiom nosmt integral (x y : ring):
    x * y = zeror => (x = zeror) \/ (y = zeror).
end IDomain.
