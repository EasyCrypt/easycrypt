(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real Distr FSet.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op drestr: 'a distr -> 'a fset -> 'a distr.

axiom supp_def (x:'a) d X:
  in_supp x (drestr d X) <=> in_supp x d /\ !mem X x.

axiom mu_x_def_notin (x:'a) d (X:'a fset):
  in_supp x d => !mem X x => mu_x (drestr d X) x = mu_x d x.

lemma nosmt mu_x_def_in (x:'a) d (X:'a fset):
  in_supp x d => mem X x => mu_x (drestr d X) x = 0%r by [].

axiom weight_def (d:'a distr) X:
  weight (drestr d X) = weight d - mu d (mem X).
