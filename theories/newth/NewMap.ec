(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore CoreMap Finite List.

(* ==================================================================== *)
theory Map.

(* -------------------------------------------------------------------- *)
op tofun ['a 'b] (m : ('a, 'b) map) = ("_.[_]") m.
op offun ['a 'b] : ('a -> 'b) -> ('a, 'b) map.

axiom nosmt offunE ['a 'b] (m : 'a -> 'b) :
  forall x, (offun m).[x] = m x.

(* -------------------------------------------------------------------- *)
lemma nosmt map_eqP ['a 'b] (m1 m2 : ('a, 'b) map) : 
  (forall x, m1.[x] = m2.[x]) <=> m1 = m2.
proof. smt(). qed.          (* coming from the theory of maps (SMT) *)

(* -------------------------------------------------------------------- *)
lemma offunK ['a 'b] : cancel offun tofun<:'a, 'b>.
proof. by move=> m @/tofun; apply/fun_ext=> x; rewrite offunE. qed.

lemma tofunK ['a 'b] : cancel tofun offun<:'a, 'b>.
proof. by move=> m; apply/map_eqP=> x; rewrite offunE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt setE ['a 'b] (m : ('a, 'b) map) x v : 
  m.[x <- v] = offun (fun y => if x = y then v else m.[y]).
proof. by apply/map_eqP=> y /=; rewrite offunE /#. qed.

lemma nosmt getE ['a 'b] (m : ('a, 'b) map) x : m.[x] = (tofun m) x.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_setE ['a 'b] (m : ('a, 'b) map) (x y : 'a) b :
  m.[x <- b].[y] = if x = y then b else m.[y].
proof. by rewrite setE getE offunK. qed.

lemma nosmt get_set_sameE (m : ('a,'b) map) (x : 'a) b :
  m.[x <- b].[x] = b.
proof. by rewrite get_setE. qed.

lemma nosmt get_set_eqE (m : ('a, 'b) map) (x y : 'a) b :
  x = y => m.[x <- b].[y] = b.
proof. by move=> <-; rewrite get_set_sameE. qed.

lemma nosmt get_set_neqE (m : ('a, 'b) map) (x y : 'a) b :
  x <> y => m.[x <- b].[y] = m.[y].
proof. by rewrite get_setE => ->. qed.

(* -------------------------------------------------------------------- *)
lemma cstE ['a 'b] (b :'b) (x : 'a) : (cst b).[x] = b.
proof. by smt(). qed.

(* -------------------------------------------------------------------- *)
op map ['a 'b 'c] (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) = 
   offun (fun x => f x m.[x]).

lemma mapE ['a 'b 'c] (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) x :
  (map f m).[x] = f x m.[x].
proof. by rewrite /map getE offunK. qed.

lemma map_set (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) x b :
  map f (m.[x <- b]) = (map f m).[x <- f x b].
proof.
apply/map_eqP => y; rewrite mapE !get_setE.
by case: (x = y) => //; rewrite mapE.
qed.

(* -------------------------------------------------------------------- *)
op eq_except ['a 'b] X (m1 m2 : ('a, 'b) map) =
  forall y, !X y => m1.[y] = m2.[y].

lemma nosmt eq_except_refl ['a 'b] X : reflexive (eq_except<:'a, 'b> X).
proof. by []. qed.

lemma nosmt eq_except_sym ['a 'b] X (m1 m2 : ('a, 'b) map) :
  eq_except X m1 m2 => eq_except X m2 m1.
proof. by move=> h x /h ->. qed.

lemma nosmt eq_except_trans ['a 'b] X (m2 m1 m3 : ('a, 'b) map) :
  eq_except X m1 m2 => eq_except X m2 m3 => eq_except X m1 m3.
proof. by move=> h1 h2 x ^/h1 -> /h2 ->. qed.
end Map.

(* -------------------------------------------------------------------- *)
type ('a, 'b) fmap.

op tomap ['a 'b] : ('a, 'b) fmap -> ('a, 'b option) map.
op ofmap ['a 'b] : ('a, 'b option) map -> ('a, 'b) fmap.

op "_.[_]" ['a 'b] (m : ('a, 'b) fmap) x =
  (tomap m).[x].

op "_.[_<-_]" ['a 'b] (m : ('a, 'b) fmap) x v =
  ofmap ((tomap m).[x <- Some v]).

op dom ['a 'b] (m : ('a, 'b) fmap) =
  fun x => m.[x] <> None.

lemma nosmt domE ['a 'b] (m : ('a, 'b) fmap) x :
  dom m x <=> m.[x] <> None.
proof. by []. qed.

abbrev (\in)    ['a 'b] x (m : ('a, 'b) fmap) = (dom m x).
abbrev (\notin) ['a 'b] x (m : ('a, 'b) fmap) = ! (dom m x).

(* -------------------------------------------------------------------- *)
lemma getE ['a 'b] (m : ('a, 'b) fmap) x : m.[x] = (tomap m).[x].
proof. by []. qed.

(* -------------------------------------------------------------------- *)
axiom tomapK ['a 'b] : cancel tomap ofmap<:'a, 'b>.

axiom ofmapK ['a 'b] (m : ('a, 'b option) map) : 
  is_finite (fun x => m.[x] <> None) => tomap (ofmap m) = m.

axiom isfmap_offmap (m : ('a, 'b) fmap) :
  is_finite (fun x => (tomap m).[x] <> None).

(* -------------------------------------------------------------------- *)
op empty ['a 'b] : ('a, 'b) fmap = ofmap (cst None).

lemma nosmt empty_valE ['a, 'b] : tomap empty<:'a, 'b> = cst None.
proof.
by rewrite /empty ofmapK //; exists [] => /= x; rewrite Map.cstE.
qed.

lemma emptyE ['a 'b] x : empty<:'a, 'b>.[x] = None.
proof. by rewrite getE empty_valE Map.cstE. qed.

lemma dom_empty ['a 'b] x : x \notin empty<:'a, 'b>.
proof. by rewrite domE emptyE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_valE ['a 'b] (m : ('a, 'b) fmap) x v :
  tomap m.[x <- v] = (tomap m).[x <- Some v].
proof.
pose s := to_seq (fun x => (tomap m).[x] <> None).
rewrite /"_.[_<-_]" ofmapK //; exists (undup (x :: s)).
split; [by rewrite undup_uniq | move=> y; rewrite mem_undup].
case: (y = x) => [|^neq] ->/=; first by rewrite Map.get_set_sameE.
by rewrite Map.get_set_neqE 1:eq_sym //; apply/mem_to_seq/isfmap_offmap.
qed.

(* --------------------------------------------------------------------- *)
lemma get_setE ['a 'b] (m : ('a, 'b) fmap) (x y : 'a) b :
  m.[x <- b].[y] = if x = y then Some b else m.[y].
proof. by rewrite /"_.[_]" /"_.[_<-_]" set_valE Map.get_setE. qed.

lemma nosmt get_set_sameE (m : ('a,'b) fmap) (x : 'a) b :
  m.[x <- b].[x] = Some b.
proof. by rewrite get_setE. qed.

lemma nosmt get_set_eqE (m : ('a, 'b) fmap) (x y : 'a) b :
  x = y => m.[x <- b].[y] = Some b.
proof. by move=> <-; rewrite get_set_sameE. qed.

lemma nosmt get_set_neqE (m : ('a, 'b) fmap) (x y : 'a) b :
  x <> y => m.[x <- b].[y] = m.[y].
proof. by rewrite get_setE => ->. qed.

(* -------------------------------------------------------------------- *)
op rem ['a 'b] (m : ('a, 'b) fmap) x =
  ofmap (tomap m).[x <- None].

(* -------------------------------------------------------------------- *)
lemma nosmt rem_valE ['a 'b] (m : ('a, 'b) fmap) x :
  tomap (rem m x) = (tomap m).[x <- None].
proof.
rewrite /rem ofmapK //; pose P z := (tomap m).[z] <> None.
apply/(finite_leq P)/isfmap_offmap => y @/P.
by rewrite !Map.get_setE; case: (x = y).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt remE ['a 'b] (m : ('a, 'b) fmap) x y :
  (rem m x).[y] = if x = y then None else m.[y].
proof. by rewrite /rem /"_.[_]" rem_valE Map.get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma dom_set ['a 'b] (m : ('a, 'b) fmap) x b y :
  y \in m.[x <- b] = y \in m \/ y = x.
proof. by rewrite !domE get_setE (eq_sym x y); case: (y = x). qed.

(* -------------------------------------------------------------------- *)
lemma dom_rem ['a 'b] (m : ('a, 'b) fmap) x y :
  y \in (rem m x) = (y \in m /\ y <> x).
proof. by rewrite !domE remE (eq_sym x y); case: (y = x) => //=. qed.

(* -------------------------------------------------------------------- *)
op eq_except ['a 'b] X (m1 m2 : ('a, 'b) fmap) =
  Map.eq_except X (tomap m1) (tomap m2).

lemma eq_except_refl ['a 'b] X : reflexive (eq_except<:'a, 'b> X).
proof. by apply/Map.eq_except_refl<:'a, 'b option>. qed.

lemma eq_except_sym ['a 'b] X (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => eq_except X m2 m1.
proof. by apply/Map.eq_except_sym<:'a, 'b option>. qed.

lemma eq_except_trans ['a 'b] X (m1 m2 m3 : ('a, 'b) fmap) :
  eq_except X m1 m2 => eq_except X m2 m3 => eq_except X m1 m3.
proof. by apply/Map.eq_except_trans<:'a, 'b option>. qed.

lemma eq_exceptP ['a 'b] X (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 <=> (forall x, !X x => m1.[x] = m2.[x]).
proof. by split=> h x /h. qed.
