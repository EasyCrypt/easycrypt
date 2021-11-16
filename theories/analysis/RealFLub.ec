(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Bool StdRing StdOrder RealLub.
(*---*) import RField RealOrder.

pragma +implicits.

(* lub for functions *)
op flub (F : 'a -> real) : real = lub (fun r => exists a, F a = r).

lemma flub_upper_bound r (F : 'a -> real) x : 
    (forall x, F x <= r) => F x <= flub F.
proof.
move => H. apply lub_upper_bound; 2: by exists x.
split; [by exists (F x) x|exists r => y [a] <-; exact H].
qed.

lemma flub_le_ub (F : 'a -> real) r :
    (forall x, F x <= r) => flub F <= r.
proof.
move => H. 
have ub_r : ub (fun (x : real) => exists (a : 'a), F a = x) r. 
  move => y [a] <-; exact H.
apply RealLub.lub_le_ub => //. 
split; [by exists (F witness) witness| by exists r].
qed.
