(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun Pred Pair Int IntExtra List.
require (*--*) Bigop Ring Number.

import Ring.IntID.

(* -------------------------------------------------------------------- *)
abstract theory BigZModule.
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
end BigZModule.

(* -------------------------------------------------------------------- *)
abstract theory BigComRing.
type t.

clone import Ring.ComRing as CR with type t <- t.

(* -------------------------------------------------------------------- *)
theory BAdd.
clone include BigZModule with
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
end BigComRing.

(* -------------------------------------------------------------------- *)
abstract theory BigOrder.
type t.

clone import Number as Num with type t <- t.

clone include BigComRing with
  type t <- t,
  pred CR.unit   <- Num.Domain.unit,
    op CR.zeror  <- Num.Domain.zeror,
    op CR.oner   <- Num.Domain.oner,
    op CR.( + )  <- Num.Domain.( + ),
    op CR.([-])  <- Num.Domain.([-]),
    op CR.( - )  <- Num.Domain.( - ),
    op CR.( * )  <- Num.Domain.( * ),
    op CR.invr   <- Num.Domain.invr,
    op CR.( / )  <- Num.Domain.( / ),
    op CR.intmul <- Num.Domain.intmul,
    op CR.ofint  <- Num.Domain.ofint,
    op CR.exp    <- Num.Domain.exp

    proof *.

realize CR.addrA     . proof. by apply/Num.Domain.addrA. qed.
realize CR.addrC     . proof. by apply/Num.Domain.addrC. qed.
realize CR.add0r     . proof. by apply/Num.Domain.add0r. qed.
realize CR.addNr     . proof. by apply/Num.Domain.addNr. qed.
realize CR.subrE     . proof. by apply/Num.Domain.subrE. qed.
realize CR.divrE     . proof. by apply/Num.Domain.divrE. qed.
realize CR.oner_neq0 . proof. by apply/Num.Domain.oner_neq0. qed.
realize CR.mulrA     . proof. by apply/Num.Domain.mulrA. qed.
realize CR.mulrC     . proof. by apply/Num.Domain.mulrC. qed.
realize CR.mul1r     . proof. by apply/Num.Domain.mul1r. qed.
realize CR.mulrDl    . proof. by apply/Num.Domain.mulrDl. qed.
realize CR.mulVr     . proof. by apply/Num.Domain.mulVr. qed.
realize CR.unitP     . proof. by apply/Num.Domain.unitP. qed.
realize CR.unitout   . proof. by apply/Num.Domain.unitout. qed.
end BigOrder.
