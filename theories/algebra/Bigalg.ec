(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun Pred Pair Int IntExtra List Ring.
require (*--*) Bigop.

import Ring.IntID.

(* -------------------------------------------------------------------- *)
abstract theory ZModule.
type t.

clone import Ring.ZModule as ZM with type t <- t.

clone include Bigop with
  type t <- t,
  op   Support.idm <- ZM.zeror,
  op   Support.(+) <- ZM.(+)

  proof Support.*.

realize Support.Axioms.addmA. by apply/addrA. qed.
realize Support.Axioms.addmC. by apply/addrC. qed.
realize Support.Axioms.add0m. by apply/add0r. qed.

(* -------------------------------------------------------------------- *)
lemma sumrD P F1 F2 (r : 'a list):
  (big P F1 r) + (big P F2 r) = big P (fun x => F1 x + F2 x) r.
proof. by rewrite big_split. qed.

(* -------------------------------------------------------------------- *)
lemma sumrN P F (r : 'a list):
  - (big P F r) = (big P (fun x => -(F x)) r).
proof. by apply/(big_endo oppr0 opprD). qed.

(* -------------------------------------------------------------------- *)
lemma sumrB P F1 F2 (r : 'a list):
  (big P F1 r) - (big P F2 r) = big P (fun x => F1 x - F2 x) r.
proof. by rewrite subrE sumrN sumrD; apply/eq_bigr=> /= x; rewrite subrE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt sumr_const (P : 'a -> bool) x s:
  big P (fun i => x) s = intmul x (count P s).
proof. by rewrite big_const intmulpE 1:count_ge0 // -iteropE. qed.
end ZModule.

(* -------------------------------------------------------------------- *)
abstract theory ComRing.
type t.

clone import Ring.ComRing as CR with type t <- t.

(* -------------------------------------------------------------------- *)
theory BAdd.
clone include Self.ZModule with
  type t <- t,
    op ZM.zeror  <- CR.zeror,
    op ZM.( + )  <- CR.( + ),
    op ZM.( - )  <- CR.( - ),
    op ZM.([-])  <- CR.([-]),
    op ZM.intmul <- CR.intmul

  proof ZM.*.

realize ZM.addrA. by apply/addrA. qed.
realize ZM.addrC. by apply/addrC. qed.
realize ZM.add0r. by apply/add0r. qed.
realize ZM.addNr. by apply/addNr. qed.
realize ZM.subrE. by apply/subrE. qed.

lemma nosmt sumr_1 (P : 'a -> bool) s:
  big P (fun i => oner) s = CR.ofint (count P s).
proof. by apply/sumr_const. qed.

lemma mulr_suml (P : 'a -> bool) F s x :
  (big P F s) * x = big P (fun i => F i * x) s.
proof. by rewrite big_distrl //; (apply/mul0r || apply/mulrDl). qed.

lemma mulr_sumr (P : 'a -> bool) F s x :
  x * (big P F s) = big P (fun i => x * F i) s.
proof. by rewrite big_distrr //; (apply/mulr0 || apply/mulrDr). qed.

lemma divr_suml (P : 'a -> bool) F s x :
  (big P F s) / x = big P (fun i => F i / x) s.
proof.
rewrite divrE mulr_suml; apply/eq_bigr.
by move=> i _ /=; rewrite divrE.
qed.
end BAdd.

(* -------------------------------------------------------------------- *)
theory BMul.
clone include Bigop with
  type t <- t,
  op   Support.idm <- CR.oner,
  op   Support.(+) <- CR.( * )

  proof Support.*.

realize Support.Axioms.addmA. by apply/mulrA. qed.
realize Support.Axioms.addmC. by apply/mulrC. qed.
realize Support.Axioms.add0m. by apply/mul1r. qed.
end BMul.
end ComRing.
