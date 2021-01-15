(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Int Real.
require (*--*) Ring.

(* -------------------------------------------------------------------- *)
instance ring with int
  op rzero = CoreInt.zero
  op rone  = CoreInt.one
  op add   = CoreInt.add
  op opp   = CoreInt.opp
  op mul   = CoreInt.mul
  op expr  = Ring.IntID.exp

  proof oner_neq0 by smt()
  proof addr0     by smt()
  proof addrA     by smt()
  proof addrC     by smt()
  proof addrN     by smt()
  proof mulr1     by smt()
  proof mulrA     by smt()
  proof mulrC     by smt()
  proof mulrDl    by smt()
  proof expr0     by smt(Ring.IntID.expr0)
  proof exprS     by smt(Ring.IntID.exprS).

op bid (b:bool) = b.

instance bring with bool
  op rzero = false
  op rone  = true
  op add   = Bool.( ^^ )
  op mul   = (/\)
  op opp   = bid

  proof oner_neq0 by smt()
  proof addr0     by smt()
  proof addrA     by smt()
  proof addrC     by smt()
  proof addrK     by smt()
  proof mulr1     by smt()
  proof mulrA     by smt()
  proof mulrC     by smt()
  proof mulrDl    by smt()
  proof mulrK     by smt()
  proof oppr_id   by smt().
