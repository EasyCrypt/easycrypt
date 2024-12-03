require import AllCore CoreMap.

(* ==================================================================== *)
op tofun ['a 'b] (m : ('a, 'b) map) = ("_.[_]") m.
op offun ['a 'b] : ('a -> 'b) -> ('a, 'b) map.

axiom offunE ['a 'b] (m : 'a -> 'b) :
  forall x, (offun m).[x] = m x.

(* -------------------------------------------------------------------- *)
lemma map_eqP ['a 'b] (m1 m2 : ('a, 'b) map) :
  (forall x, m1.[x] = m2.[x]) <=> m1 = m2.
proof. smt(). qed.          (* coming from the theory of maps (SMT) *)

(* -------------------------------------------------------------------- *)
lemma offunK ['a 'b] : cancel offun tofun<:'a, 'b>.
proof. by move=> m @/tofun; apply/fun_ext=> x; rewrite offunE. qed.

lemma tofunK ['a 'b] : cancel tofun offun<:'a, 'b>.
proof. by move=> m; apply/map_eqP=> x; rewrite offunE. qed.

(* -------------------------------------------------------------------- *)
lemma setE ['a 'b] (m : ('a, 'b) map) x v :
  m.[x <- v] = offun (fun y => if y = x then v else m.[y]).
proof. by apply/map_eqP=> y /=; rewrite offunE /#. qed.

(* -------------------------------------------------------------------- *)
lemma getE ['a 'b] (m : ('a, 'b) map) x : m.[x] = (tofun m) x.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma get_setE ['a 'b] (m : ('a, 'b) map) (x y : 'a) b :
  m.[x <- b].[y] = if y = x then b else m.[y].
proof. by rewrite setE getE offunK. qed.

(* -------------------------------------------------------------------- *)
lemma get_set_sameE (m : ('a,'b) map) (x : 'a) b :
  m.[x <- b].[x] = b.
proof. by rewrite get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma get_set_eqE (m : ('a, 'b) map) (x y : 'a) b :
  y = x => m.[x <- b].[y] = b.
proof. by move=> <-; rewrite get_set_sameE. qed.

(* -------------------------------------------------------------------- *)
lemma get_set_neqE (m : ('a, 'b) map) (x y : 'a) b :
  y <> x => m.[x <- b].[y] = m.[y].
proof. by rewrite get_setE => ->. qed.

(* -------------------------------------------------------------------- *)
lemma cstE ['a 'b] (b :'b) (x : 'a) : (cst b).[x] = b.
proof. by smt(). qed.

(* -------------------------------------------------------------------- *)
op map ['a 'b 'c] (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) =
   offun (fun x => f x m.[x]).

(* -------------------------------------------------------------------- *)
lemma mapE ['a 'b 'c] (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) x :
  (map f m).[x] = f x m.[x].
proof. by rewrite /map getE offunK. qed.

(* -------------------------------------------------------------------- *)
lemma map_set (f : 'a -> 'b -> 'c) (m : ('a, 'b) map) x b :
  map f (m.[x <- b]) = (map f m).[x <- f x b].
proof.
apply/map_eqP => y; rewrite mapE !get_setE.
by case: (y = x) => //; rewrite mapE.
qed.

(* -------------------------------------------------------------------- *)
op eq_except ['a 'b] X (m1 m2 : ('a, 'b) map) =
  forall y, !X y => m1.[y] = m2.[y].

(* -------------------------------------------------------------------- *)
lemma eq_except_refl ['a 'b] X : reflexive (eq_except<:'a, 'b> X).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_sym ['a 'b] X (m1 m2 : ('a, 'b) map) :
  eq_except X m1 m2 => eq_except X m2 m1.
proof. by move=> h x /h ->. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_trans ['a 'b] X (m2 m1 m3 : ('a, 'b) map) :
  eq_except X m1 m2 => eq_except X m2 m3 => eq_except X m1 m3.
proof. by move=> h1 h2 x ^/h1 -> /h2 ->. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_sub ['a 'b] (X Y : 'a -> bool) (m1 m2 : ('a, 'b) map) :
   X <= Y => eq_except X m1 m2 => eq_except Y m1 m2.
proof. by move=> hsub + x hx => -> //; apply: contra (hsub x) hx. qed.

(* -------------------------------------------------------------------- *)
op merge ['a 'b 'c 'd] (f: 'a -> 'b -> 'c -> 'd)
     (m1 : ('a, 'b) map) (m2 : ('a, 'c) map) =
  offun (fun a => f a m1.[a] m2.[a]).

lemma mergeE (f: 'a -> 'b -> 'c -> 'd) m1 m2 x:
  (merge f m1 m2).[x] = f x m1.[x] m2.[x].
proof. by rewrite /merge offunE. qed.
