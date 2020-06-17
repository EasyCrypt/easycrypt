(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require export Core Int IntExtra Real RealExtra.

(* -------------------------------------------------------------------- *)
schema cost_oget ['a] `{P} {o: 'a option} : 
  cost [P : oget o] = cost [P:o] + 1.
hint simplify cost_oget.
