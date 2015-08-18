(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require export Int.
require import AlgTactic.
require import Ring.
instance ring with int
  op rzero = zeroz
  op rone  = onez
  op add   = (+)
  op opp   = [-]
  op mul   = ( * )
  op expr  = ( ^ )
  op sub   = (-)

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

