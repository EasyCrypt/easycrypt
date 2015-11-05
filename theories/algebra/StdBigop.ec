(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred Int IntExtra Real Ring List StdRing.
require (*--*) Bigop Bigalg.

(* -------------------------------------------------------------------- *)
theory Bigint.
clone include Bigalg.ComRing with
  type t <- int,
  pred CR.unit (z : int) <- (z = 1 \/ z = -1),
    op CR.zeror  <- 0,
    op CR.oner   <- 1,
    op CR.( + )  <- Int.( + ),
    op CR.( - )  <- Int.( - ),
    op CR.([-])  <- Int.([-]),
    op CR.( * )  <- Int.( * ),
    op CR.invr   <- (fun (z : int) => z),
    op CR.intmul <- IntID.intmul,
    op CR.ofint  <- IntID.ofint,
    op CR.exp    <- IntID.exp

    proof CR.* by smt.

lemma nosmt sumzE ss : sumz ss = BAdd.big predT (fun x => x) ss.
proof. by elim: ss=> [|s ss ih] //=; rewrite BAdd.big_cons -ih. qed.
      
lemma nosmt big_constz (P : 'a -> bool) x s:
  BAdd.big P (fun i => x) s = x * (count P s).
proof. by rewrite BAdd.sumr_const -IntID.intmulz. qed.

lemma nosmt big_count (P : 'a -> bool) s:
    BAdd.big P (fun (x : 'a) => count (pred1 x) s) (undup s)
  = size (filter P s).
proof. admit. qed.
end Bigint.

(* -------------------------------------------------------------------- *)
theory Bigreal.
clone include Bigalg.ComRing with
  type t <- real,
  pred CR.unit (z : real) <- (z <> 0%r),
    op CR.zeror  <- 0%r,
    op CR.oner   <- 1%r,
    op CR.( + )  <- Real.( + ),
    op CR.( - )  <- Real.( - ),
    op CR.([-])  <- Real.([-]),
    op CR.( * )  <- Real.( * ),
    op CR.invr   <- Real.inv,
    op CR.( / )  <- Real.( / ),
    op CR.intmul <- RField.intmul,
    op CR.ofint  <- RField.ofint,
    op CR.exp    <- RField.exp

    proof CR.* by smt.

import Bigint.BAdd Bigint.BMul BAdd BMul.

lemma sumr_ofint (P : 'a -> bool) F s :
  (Bigint.BAdd.big P F s)%r = (BAdd.big P (fun i => (F i)%r) s).
proof.
elim: s => [//|x s ih]; rewrite !big_cons; case: (P x)=> // _.
by rewrite FromInt.Add ih.
qed.

lemma prodr_ofint (P : 'a -> bool) F s :
  (Bigint.BMul.big P F s)%r = (BMul.big P (fun i => (F i)%r) s).
proof.
elim: s => [//|x s ih]; rewrite !big_cons; case: (P x)=> // _.
by rewrite FromInt.Mul ih.
qed.
end Bigreal.

(* -------------------------------------------------------------------- *)
require import Bool.

clone Bigop as BBA with
  type t <- bool,
  op Support.idm <- false,
  op Support.(+) <- Bool.( ^^ )
  proof Support.Axioms.* by (delta; smt).  

clone Bigop as BBM with
  type t <- bool,
  op Support.idm <- true,
  op Support.(+) <- Pervasive.( /\ )
  proof Support.Axioms.* by (delta; smt).  

clone Bigop as BBO with
  type t <- bool,
  op Support.idm <- false,
  op Support.(+) <- Pervasive.( || )
  proof Support.Axioms.* by (delta; smt).  
