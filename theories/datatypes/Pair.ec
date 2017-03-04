(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

op fst (p:'a * 'b): 'a = p.`1.

op snd (p:'a * 'b): 'b = p.`2.

lemma nosmt pw_eq (x x':'a) (y y':'b):
  x = x' => y = y' => (x,y) = (x',y')
by [].

lemma nosmt pairS (x:'a * 'b): x = (fst x,snd x)
by [].

lemma nosmt fst_pair (y:'b) (x:'a): fst (x,y) = x
by trivial.

lemma nosmt snd_pair (x:'a) (y:'b): snd (x,y) = y
by trivial.
