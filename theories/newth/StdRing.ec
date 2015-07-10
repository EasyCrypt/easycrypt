(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real.
require (*--*) Ring.

(* -------------------------------------------------------------------- *)
axiom divr0: forall x, x / 0%r = 0%r.
lemma invr0: inv 0%r = 0%r.
proof. by rewrite -{2}(divr0 1%r) inv_def. qed.

(* -------------------------------------------------------------------- *)
theory RField.
  clone include Ring.Field with
    type t <- real,
    op   zeror <- 0%r,
    op   oner  <- 1%r,
    op   ( + ) <- Real.( + ),
    op   [ - ] <- Real.([-]),
    op   ( - ) <- Real.( - ),
    op   ( * ) <- Real.( * ),
    op   ( / ) <- Real.( / ),
    op   invr  <- Real.inv
    proof * by smt.
  
  lemma ofintR (i : int): ofint i = i%r.
  proof.
    have h: forall i, 0 <= i => ofint i = i%r; 2: smt.
    move=> {i}; elim/Induction.natind; smt.
  qed.
end RField.

(* -------------------------------------------------------------------- *)
instance ring with int
  op rzero = Int.zero
  op rone  = Int.one
  op add   = Int.(+)
  op opp   = Int.([-])
  op mul   = Int.( * )
  op expr  = Int.( ^ )
  op sub   = Int.(-)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt 
  proof exprS     by smt
  proof subrE     by smt.
