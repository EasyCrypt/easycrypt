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
clone include Bigalg.BigOrder with
  type t <- int,
  pred Num.Domain.unit (z : int) <- (z = 1 \/ z = -1),
    op Num.Domain.zeror  <- 0,
    op Num.Domain.oner   <- 1,
    op Num.Domain.( + )  <- Int.( + ),
    op Num.Domain.( - )  <- Int.( - ),
    op Num.Domain.([-])  <- Int.([-]),
    op Num.Domain.( * )  <- Int.( * ),
    op Num.Domain.invr   <- (fun (z : int) => z),
    op Num.Domain.intmul <- IntID.intmul,
    op Num.Domain.ofint  <- IntID.ofint,
    op Num.Domain.exp    <- IntID.exp,

    op Num."`|_|" <- Int."`|_|",
    op Num.( <= ) <- Int.(<=),
    op Num.( <  ) <- Int.(< )

    proof Num.Domain.* by smt, Num.Axioms.* by smt.

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
clone include Bigalg.BigOrder with
  type t <- real,
  pred Num.Domain.unit (z : real) <- (z <> 0%r),
    op Num.Domain.zeror  <- 0%r,
    op Num.Domain.oner   <- 1%r,
    op Num.Domain.( + )  <- Real.( + ),
    op Num.Domain.( - )  <- Real.( - ),
    op Num.Domain.([-])  <- Real.([-]),
    op Num.Domain.( * )  <- Real.( * ),
    op Num.Domain.invr   <- Real.inv,
    op Num.Domain.( / )  <- Real.( / ),
    op Num.Domain.intmul <- RField.intmul,
    op Num.Domain.ofint  <- RField.ofint,
    op Num.Domain.exp    <- RField.exp,

    op Num."`|_|" <- Real.Abs."`|_|",
    op Num.( <= ) <- Real.(<=),
    op Num.( <  ) <- Real.(< )

    proof Num.Domain.* by smt, Num.Axioms.* by smt.

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
