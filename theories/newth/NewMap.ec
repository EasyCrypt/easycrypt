(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Core Int CoreMap Finite List FSet.

op offun ['a 'b] : ('a -> 'b) -> ('a, 'b) map.

op tofun ['a 'b] (m : ('a, 'b) map) = ("_.[_]") m.

axiom nosmt offunK  (m : ('a, 'b) map) : offun (tofun m) = m.

axiom nosmt tofunK  (f : 'a -> 'b)     : tofun (offun f) = f.

axiom nosmt setE (m : ('a, 'b) map) x b : 
  m.[x <- b] = offun (fun y => if x = y then b else m.[y]).


(* -------------------------------------------------------------------- *)
lemma nosmt map_ext (m1 m2:('a,'b) map) : 
  (forall (a:'a), m1.[a] = m2.[a]) => m1 = m2.
proof.
  move=> H;rewrite -(offunK m1) -(offunK m2);congr.
  by apply/fun_ext/H.
qed.

(* -------------------------------------------------------------------- *)
lemma getE (m : ('a, 'b) map) x: m.[x] = (tofun m) x.
proof. done. qed.

lemma nosmt setP (m : ('a,'b) map) (x y : 'a) b:
  m.[x <- b].[y] = if x = y then b else m.[y].
proof. by rewrite setE getE tofunK. qed.

lemma nosmt setP_eq (m : ('a,'b) map) (x : 'a) b:
  m.[x <- b].[x] = b.
proof. by rewrite setP. qed.

lemma nosmt setP_neq (m : ('a,'b) map) (x y : 'a) b: x <> y =>
  m.[x <- b].[y] = m.[y].
proof. by rewrite setP=> ->. qed.

(* -------------------------------------------------------------------- *)
op cnst ['a 'b] (b : 'b) : ('a, 'b) map = offun (fun (a:'a) => b).

lemma cnstP (b:'b) (x:'a) : (cnst b).[x] = b.
proof. by rewrite getE tofunK. qed.

(* -------------------------------------------------------------------- *)

op map ['a 'b 'c] (f:'a -> 'b -> 'c) (m: ('a, 'b) map) = 
   offun (fun x => f x m.[x]).

lemma mapE (f:'a -> 'b -> 'c) (m : ('a, 'b) map) x:
  (map f m).[x] = f x m.[x].
proof. by rewrite /map getE tofunK. qed.

lemma map_set (f:'a -> 'b -> 'c) (m : ('a, 'b) map) x b:
  map f (m.[x <- b]) = (map f m).[x <- f x b].
proof. apply map_ext=> y;smt (mapE). qed.

(* -------------------------------------------------------------------- *)

op eq_except ['a 'b] (m1 m2 : ('a, 'b) map) (X : 'a -> bool) =
  forall y, !X y => m1.[y] = m2.[y].

lemma nosmt eq_except_refl (m : ('a, 'b) map) X : eq_except m m X.
proof. done. qed.

lemma nosmt eq_except_sym (m1 m2: ('a, 'b) map) X : 
  eq_except m1 m2 X <=> eq_except m2 m1 X.
proof. smt (). qed.

lemma eq_except_trans (m2 m1 m3 : ('a, 'b) map) X:
  eq_except m1 m2 X =>
  eq_except m2 m3 X =>
  eq_except m1 m3 X.
proof. by move=> Hm1 Hm2 x Hx;rewrite (Hm1 _ Hx) (Hm2 _ Hx). qed.

(* -------------------------------------------------------------------- *)

theory FMap.
  
type ('a, 'b) fmap = ('a, 'b option) map.

op map0 ['a 'b] : ('a, 'b) fmap = cnst None.  

lemma map0P ['a 'b] (x:'a) : map0<:'a,'b>.[x] = None.
proof. smt (cnstP). qed.

op rem ['a 'b] (m : ('a, 'b) fmap) x = m.[x <- None].

op "_.[_<-_]" ['a 'b] (m : ('a, 'b) fmap) x (b : 'b) = 
   m.[x <- Some b].

lemma rem_map0 ['a 'b] (x:'a) : rem map0 x = map0<:'a,'b>.
proof. smt (map0P). qed.

lemma nosmt remP ['a 'b] (m : ('a, 'b) fmap) x y: 
  (rem m x).[y] = if x = y then None else m.[y].
proof. smt (). qed.
  
(* -------------------------------------------------------------------- *)
op in_dom (m : ('a, 'b) fmap) (x : 'a) = m.[x] <> None.

lemma finite_map0 ['a 'b] :is_finite (in_dom (map0<:'a,'b>)).
proof.  smt (cnstP). qed.

lemma finite_set (m: ('a, 'b) fmap) x b : 
  is_finite (in_dom m) => is_finite (in_dom m.[x <- b]).
proof. smt (). qed.

abbrev (\in) (x : 'a) (m : ('a, 'b) fmap) = m.[x] <> None. 
abbrev (\notin) (x : 'a) (m : ('a, 'b) fmap) = m.[x] = None.

lemma nosmt set_inP (m:('a, 'b) fmap) x b y :
  y \in m.[x <- b] <=> (x = y \/ y \in m).
proof. move=> /#. qed.

(* -------------------------------------------------------------------- *)
(* Definition of the domain as a finite set                             *)

op dom : ('a, 'b) fmap -> 'a fset.

axiom domP (m: ('a, 'b) fmap) : is_finite (in_dom m) =>
  forall (x:'a), mem (dom m) x = x \in m.

lemma dom_set1P (m: ('a, 'b) fmap) x b y : is_finite (in_dom m) =>
  mem (dom m.[x <- b]) y = (y = x \/ mem (dom m) y).
proof. smt (domP finite_set). qed.

lemma dom_setP (m: ('a, 'b) fmap) x b : is_finite (in_dom m) =>
  dom (m.[x <- b]) = dom m `|` fset1 x.
proof.
rewrite fsetP => fin y;rewrite dom_set1P // in_fsetU in_fset1 /#.
qed.

(* -------------------------------------------------------------------- *)
(* Definition of the codomain as a finite set                           *)

op rng ['a 'b] : ('a, 'b) fmap -> 'b fset.

axiom rngP (m: ('a, 'b) fmap) : is_finite (in_dom m) =>
  forall (b:'b), mem (rng m) b <=> exists x,  m.[x] = Some b.

lemma rng_set1P (m: ('a, 'b) fmap) x b b' : is_finite (in_dom m) =>
  mem (rng m.[x <- b]) b' => (b' = b \/ mem (rng m) b').
proof. smt (rngP finite_set). qed.

theory FMap.
