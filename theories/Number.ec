(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require Ring.

(* -------------------------------------------------------------------- *)
theory NumTheory.
  clone import Ring.R.

  op norm : ring -> ring.
  op le   : ring -> ring -> bool.
  op lt   : ring -> ring -> bool.

  axiom ler_norm_add (x y : ring): le (norm (x + y)) (norm x + norm y).
  axiom addr_gt0     (x y : ring): lt zeror x => lt zeror y => lt zeror (x + y).
  axiom norm_eq0     (x   : ring): norm x = zeror => x = zeror.
  axiom ger_leVge    (x y : ring): le zeror x => le zeror y => (le x y) \/ (le y x).
  axiom normrM       (x y : ring): norm (x * y) = norm x * norm y.
  axiom ler_def      (x y : ring): le x y <=> (norm (y - x) = y - x).
  axiom ltr_def      (x y : ring): lt x y <=> (y <> x) /\ le x y.
end NumTheory.
