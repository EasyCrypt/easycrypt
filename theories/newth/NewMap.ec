(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

type ('a,'b) map.

op "_.[_]"   : ('a,'b) map -> 'a -> 'b.
op "_.[_<-_]": ('a,'b) map -> 'a -> 'b -> ('a,'b) map.

lemma select_update (m : ('a,'b) map) (x a : 'a) b:
    m.[a <- b].[x]
  = if a = x then b else m.[x].
smt.