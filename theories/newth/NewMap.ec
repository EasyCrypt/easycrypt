(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

type ('a,'b) map.

op cnst : 'b -> ('a, 'b) map.
op "_.[_]"   : ('a,'b) map -> 'a -> 'b.
op "_.[_<-_]": ('a,'b) map -> 'a -> 'b -> ('a,'b) map.

axiom nosmt map_exp (m1 m2:('a,'b) map) : 
  (forall (a:'a), m1.[a] = m2.[a]) => m1 = m2.

axiom cnstP (b:'b) (x:'a) : (cnst b).[x] = b.

axiom nosmt getP (m : ('a,'b) map) (x y : 'a) b:
  m.[x <- b].[y] = if x = y then b else m.[y].

lemma nosmt getP_eq (m : ('a,'b) map) (x : 'a) b:
  m.[x <- b].[x] = b.
proof. by rewrite getP. qed.

lemma nosmt getP_neq (m : ('a,'b) map) (x y : 'a) b: x <> y =>
  m.[x <- b].[y] = m.[y].
proof. by rewrite getP=> ->. qed.






