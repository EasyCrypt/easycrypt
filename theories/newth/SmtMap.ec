(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore CoreMap Finite List FSet StdOrder.

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
  m.[x <- v] = offun (fun y => if y = x then v else m.[y]).
proof. by apply/map_eqP=> y /=; rewrite offunE /#. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt getE ['a 'b] (m : ('a, 'b) map) x : m.[x] = (tofun m) x.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_setE ['a 'b] (m : ('a, 'b) map) (x y : 'a) b :
  m.[x <- b].[y] = if y = x then b else m.[y].
proof. by rewrite setE getE offunK. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_sameE (m : ('a,'b) map) (x : 'a) b :
  m.[x <- b].[x] = b.
proof. by rewrite get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_eqE (m : ('a, 'b) map) (x y : 'a) b :
  y = x => m.[x <- b].[y] = b.
proof. by move=> <-; rewrite get_set_sameE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_neqE (m : ('a, 'b) map) (x y : 'a) b :
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
lemma nosmt eq_except_refl ['a 'b] X : reflexive (eq_except<:'a, 'b> X).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_sym ['a 'b] X (m1 m2 : ('a, 'b) map) :
  eq_except X m1 m2 => eq_except X m2 m1.
proof. by move=> h x /h ->. qed.

(* -------------------------------------------------------------------- *)
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

op rng ['a 'b] (m : ('a, 'b) fmap) =
  fun y => exists x, m.[x] = Some y
axiomatized by rngE.

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
lemma nosmt finite_dom ['a 'b] (m : ('a, 'b) fmap) :
  is_finite (dom m).
proof. exact/isfmap_offmap. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt finite_rng ['a 'b] (m : ('a, 'b) fmap) : is_finite (rng m).
proof.
pose s := map (fun x => oget m.[x]) (to_seq (dom m)).
apply/finiteP; exists s => y; rewrite rngE /= => -[x mxE].
by apply/mapP; exists x => /=; rewrite mem_to_seq 1:finite_dom domE mxE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fmap_eqP ['a 'b] (m1 m2 : ('a, 'b) fmap) :
  (forall x, m1.[x] = m2.[x]) <=> m1 = m2.
proof.
split=> [pw_eq|->] //; rewrite -tomapK -(tomapK m2).
by congr; apply/Map.map_eqP=> x; rewrite pw_eq.
qed.

(* -------------------------------------------------------------------- *)
op empty ['a 'b] : ('a, 'b) fmap = ofmap (cst None).

lemma nosmt empty_valE ['a, 'b] : tomap empty<:'a, 'b> = cst None.
proof.
by rewrite /empty ofmapK //; exists [] => /= x; rewrite Map.cstE.
qed.

(* -------------------------------------------------------------------- *)
lemma emptyE ['a 'b] x : empty<:'a, 'b>.[x] = None.
proof. by rewrite getE empty_valE Map.cstE. qed.

(* -------------------------------------------------------------------- *)
lemma mem_empty ['a 'b] x : x \notin empty<:'a, 'b>.
proof. by rewrite domE emptyE. qed.

(* -------------------------------------------------------------------- *)
lemma mem_rng_empty ['a 'b] y : !rng empty<:'a, 'b> y.
proof. by rewrite rngE /= negb_exists=> /= x; rewrite emptyE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_valE ['a 'b] (m : ('a, 'b) fmap) x v :
  tomap m.[x <- v] = (tomap m).[x <- Some v].
proof.
pose s := to_seq (fun x => (tomap m).[x] <> None).
rewrite /"_.[_<-_]" ofmapK //; apply/finiteP; exists (x :: s).
move=> y /=; rewrite Map.get_setE; case: (y = x) => //=.
by move=> ne_yx h; apply/mem_to_seq/h/isfmap_offmap.
qed.

(* --------------------------------------------------------------------- *)
lemma get_setE ['a 'b] (m : ('a, 'b) fmap) (x y : 'a) b :
  m.[x <- b].[y] = if y = x then Some b else m.[y].
proof. by rewrite /"_.[_]" /"_.[_<-_]" set_valE Map.get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_sameE (m : ('a,'b) fmap) (x : 'a) b :
  m.[x <- b].[x] = Some b.
proof. by rewrite get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_eqE (m : ('a, 'b) fmap) (x y : 'a) b :
  y = x => m.[x <- b].[y] = Some b.
proof. by move=> <-; rewrite get_set_sameE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt get_set_neqE (m : ('a, 'b) fmap) (x y : 'a) b :
  y <> x => m.[x <- b].[y] = m.[y].
proof. by rewrite get_setE => ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_setE (m : ('a, 'b) fmap) x x' b b' :
  m.[x <- b].[x' <- b']
    = (x' = x) ? m.[x' <- b'] : m.[x' <- b'].[x <- b].
proof.
apply/fmap_eqP=> y; rewrite !get_setE; case: (x' = x)=> //= [<<-|].
+ by rewrite !get_setE; case: (y = x').
+ by rewrite !get_setE; case: (y = x')=> //= ->> ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_sameE (m : ('a, 'b) fmap) (x : 'a) b b' :
  m.[x <- b].[x <- b'] = m.[x <- b'].
proof. by rewrite set_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_eqE (m : ('a, 'b) fmap) (x x' : 'a) b b' :
  x' = x => m.[x <- b].[x' <- b'] = m.[x <- b'].
proof. by rewrite set_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_neqE (m : ('a, 'b) fmap) (x x' : 'a) b b' :
  x' <> x => m.[x <- b].[x' <- b'] = m.[x' <- b'].[x <- b].
proof. by rewrite set_setE => ->. qed.

(* -------------------------------------------------------------------- *)
op rem ['a 'b] (m : ('a, 'b) fmap) x =
  ofmap (tomap m).[x <- None].

(* -------------------------------------------------------------------- *)
lemma nosmt rem_valE ['a 'b] (m : ('a, 'b) fmap) x :
  tomap (rem m x) = (tomap m).[x <- None].
proof.
rewrite /rem ofmapK //; pose P z := (tomap m).[z] <> None.
apply/(finite_leq P)/isfmap_offmap => y @/P.
by rewrite !Map.get_setE; case: (y = x).
qed.

(* -------------------------------------------------------------------- *)
lemma remE ['a 'b] (m : ('a, 'b) fmap) x y :
  (rem m x).[y] = if y = x then None else m.[y].
proof. by rewrite /rem /"_.[_]" rem_valE Map.get_setE. qed.

(* -------------------------------------------------------------------- *)
lemma mem_set ['a 'b] (m : ('a, 'b) fmap) x b y :
  y \in m.[x <- b] <=> (y \in m \/ y = x).
proof. by rewrite !domE get_setE; case: (y = x). qed.

(* -------------------------------------------------------------------- *)
lemma mem_rem ['a 'b] (m : ('a, 'b) fmap) x y :
  y \in (rem m x) <=> (y \in m /\ y <> x).
proof. by rewrite !domE remE; case: (y = x) => //=. qed.

(* -------------------------------------------------------------------- *)
op eq_except ['a 'b] X (m1 m2 : ('a, 'b) fmap) =
  Map.eq_except X (tomap m1) (tomap m2).

(* -------------------------------------------------------------------- *)
lemma eq_except_refl ['a 'b] X : reflexive (eq_except<:'a, 'b> X).
proof. by apply/Map.eq_except_refl<:'a, 'b option>. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_sym ['a 'b] X (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => eq_except X m2 m1.
proof. by apply/Map.eq_except_sym<:'a, 'b option>. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_trans ['a 'b] X (m1 m2 m3 : ('a, 'b) fmap) :
  eq_except X m1 m2 => eq_except X m2 m3 => eq_except X m1 m3.
proof. by apply/Map.eq_except_trans<:'a, 'b option>. qed.

(* -------------------------------------------------------------------- *)
lemma eq_exceptP ['a 'b] X (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 <=> (forall x, !X x => m1.[x] = m2.[x]).
proof. by split=> h x /h. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except0 ['a 'b] (m1 m2 : ('a, 'b) fmap) :
  eq_except pred0 m1 m2 <=> m1 = m2.
proof. by rewrite eq_exceptP /pred0 /= fmap_eqP. qed.

(* -------------------------------------------------------------------- *)
lemma eq_exceptSm ['a 'b] X x y (m1 m2 : ('a, 'b) fmap) :
     eq_except X m1 m2
  => eq_except (predU X (pred1 x)) m1.[x <- y] m2.
proof.
move=> eqeX_m1_m2; rewrite eq_exceptP=> x0; rewrite get_setE /predU /pred1.
by move=> /negb_or []; move: eqeX_m1_m2=> /eq_exceptP h /h -> ->.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_exceptmS ['a 'b] X x y (m1 m2 : ('a, 'b) fmap) :
     eq_except X m1 m2
  => eq_except (predU X (pred1 x)) m1 m2.[x <- y].
proof. by move=> h; apply/eq_except_sym/eq_exceptSm/eq_except_sym. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_setl ['a 'b] x y (m : ('a, 'b) fmap) :
  eq_except (pred1 x) m.[x <- y] m.
proof.
have ->: pred1 x = predU pred0 (pred1 x) by exact/fun_ext.
by apply/eq_exceptSm/eq_except0.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_setr ['a 'b] x y (m : ('a, 'b) fmap) :
  eq_except (pred1 x) m m.[x <- y].
proof. by apply/eq_except_sym/eq_except_setl. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_set ['a 'b] X x y y' (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 =>
  eq_except ((y <> y') ? predU X (pred1 x) : X) m1.[x <- y] m2.[x <- y'].
proof.
move=> /eq_exceptP h; case: (y = y') => /= [<-|].
  by apply/eq_exceptP=> z _; rewrite !get_setE h.
move=> ne_y_y'; apply/eq_exceptP=> z; rewrite negb_or.
by case=> /h; rewrite !get_setE => + @/pred1 -> - ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_set_eq ['a 'b] X x y (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => eq_except X m1.[x <- y] m2.[x <- y].
proof. by move=> /(@eq_except_set _ x y y). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_set_same ['a 'b] X x y y' (m1 m2 : ('a, 'b) fmap) :
     y = y'
  => eq_except X m1 m2
  => eq_except X m1.[x <- y] m2.[x <- y'].
proof. by move=> <-; apply/eq_except_set_eq. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_set_neq ['a 'b] X x y y' (m1 m2 : ('a, 'b) fmap) :
     y <> y'
  => eq_except X m1 m2
  => eq_except (predU X (pred1 x)) m1.[x <- y] m2.[x <- y'].
proof. by move=> + /(@eq_except_set _ x y y' _ _)=> ->. qed.

(* -------------------------------------------------------------------- *)
op map ['a 'b 'c] (f : 'a -> 'b -> 'c) (m : ('a, 'b) fmap) = 
  ofmap (Map.map (fun x => omap (f x)) (tomap m)).

(* -------------------------------------------------------------------- *)
lemma map_valE ['a 'b 'c] (f : 'a -> 'b -> 'c) m :
  tomap (map f m) = Map.map (fun k => omap (f k)) (tomap m).
proof.
rewrite /map ofmapK //; pose P z := (tomap m).[z] <> None.
apply/(finite_leq P)/isfmap_offmap => y @/P.
by rewrite Map.getE Map.offunK /=; case: (tomap m).[y].
qed.

(* -------------------------------------------------------------------- *)
lemma mapE ['a 'b 'c] (f : 'a -> 'b -> 'c) m x :
  (map f m).[x] = omap (f x) m.[x].
proof. by rewrite /map /"_.[_]" map_valE Map.mapE. qed.

(* -------------------------------------------------------------------- *)
lemma mem_map ['a 'b 'c] (f : 'a -> 'b -> 'c) m x :
  x \in map f m <=> x \in m.
proof. by rewrite !domE mapE iff_negb; case: (m.[x]). qed.

(* -------------------------------------------------------------------- *)
lemma map_set (f : 'a -> 'b -> 'c) m x b :
  map f (m.[x <- b]) = (map f m).[x <- f x b].
proof.
apply/fmap_eqP => y; rewrite mapE !get_setE.
by case: (y = x) => //; rewrite mapE.
qed.

(* -------------------------------------------------------------------- *)
lemma map_comp ['a 'b 'c 'd]
  (f : 'a -> 'b -> 'c) (g : 'a -> 'c -> 'd) m
: map g (map f m) = map (fun a b => g a (f a b)) m.
proof. by apply/fmap_eqP => a; rewrite !mapE; case: (m.[a]). qed.

(* -------------------------------------------------------------------- *)
op filter ['a 'b] (p : 'a -> 'b -> bool) m =
  ofmap (Map.offun (fun x => oapp (p x) false m.[x] ? m.[x] : None)).

(* -------------------------------------------------------------------- *)
lemma filter_valE ['a 'b] (p : 'a -> 'b -> bool) m :
  tomap (filter p m) =
    Map.offun (fun x => oapp (p x) false m.[x] ? m.[x] : None).
proof.
rewrite /filter ofmapK //; pose P z := (tomap m).[z] <> None.
apply/(finite_leq P)/isfmap_offmap => y @/P.
by rewrite !Map.getE Map.offunK /= getE; case: (tomap m).[y].
qed.

(* -------------------------------------------------------------------- *)
lemma filterE ['a 'b] (p : 'a -> 'b -> bool) m x :
  (filter p m).[x] = oapp (p x) false m.[x] ? m.[x] : None.
proof. by rewrite /filter /"_.[_]" filter_valE Map.offunE. qed.

(* -------------------------------------------------------------------- *)
lemma filter_set (p : 'a -> 'b -> bool) m x b :
  filter p (m.[x <- b]) = p x b ? (filter p m).[x <- b] : rem (filter p m) x.
proof.
apply/fmap_eqP => y; rewrite !filterE !get_setE.
case: (y = x) => [->|] /=; case: (p x b) => /=.
+ by rewrite get_setE.
+ by rewrite remE.
+ by rewrite get_setE=> + -> /=; rewrite filterE.
+ by rewrite remE=> + -> /=; rewrite filterE.
qed.

(* ==================================================================== *)
op fdom ['a 'b] (m : ('a, 'b) fmap) =
  oflist (to_seq (dom m)) axiomatized by fdomE.

(* -------------------------------------------------------------------- *)
lemma mem_fdom ['a 'b] (m : ('a, 'b) fmap) (x : 'a) :
  x \in fdom m <=> x \in m.
proof. by rewrite fdomE mem_oflist mem_to_seq ?isfmap_offmap. qed.  

(* -------------------------------------------------------------------- *)
lemma fdomP ['a 'b] (m : ('a, 'b) fmap) (x : 'a) :
  x \in fdom m <=> m.[x] <> None.
proof. by rewrite mem_fdom. qed.

(* -------------------------------------------------------------------- *)
lemma fdom0 ['a 'b] : fdom empty<:'a, 'b> = fset0.
proof. by apply/fsetP=> x; rewrite mem_fdom mem_empty in_fset0. qed.

(* -------------------------------------------------------------------- *)
lemma fdom_eq0 ['a 'b] (m : ('a, 'b) fmap) : fdom m = fset0 => m = empty.
proof.
rewrite fsetP -fmap_eqP=> h x; rewrite emptyE.
have ->: m.[x] = None <=> x \notin m by done.
by rewrite -mem_fdom h in_fset0.
qed.

(* -------------------------------------------------------------------- *)
lemma fdom_set ['a 'b] (m : ('a, 'b) fmap) x v :
  fdom m.[x <- v] = fdom m `|` fset1 x.
proof.
by apply/fsetP=> y; rewrite in_fsetU1 !mem_fdom mem_set.
qed.

(* -------------------------------------------------------------------- *)
lemma fdom_rem ['a 'b] (m : ('a, 'b) fmap) x :
  fdom (rem m x) = fdom m `\` fset1 x.
proof. 
by apply/fsetP=> y; rewrite in_fsetD1 !mem_fdom mem_rem.
qed.

(* -------------------------------------------------------------------- *)
lemma fdom_map ['a 'b 'c] (f : 'a -> 'b -> 'c) m :
  fdom (map f m) = fdom m.
proof. by apply/fsetP=> x; rewrite !mem_fdom mem_map. qed.

(* -------------------------------------------------------------------- *)
lemma mem_fdom_set ['a 'b] (m : ('a, 'b) fmap) x v y :
  y \in fdom m.[x <- v] <=> (y \in fdom m \/ y = x).
proof. by rewrite fdom_set in_fsetU1. qed.

lemma mem_fdom_rem ['a 'b] (m : ('a, 'b) fmap) x y :
  y \in fdom (rem m x) <=> (y \in fdom m /\ y <> x).
proof. by rewrite fdom_rem in_fsetD1. qed.

(* ==================================================================== *)
op frng ['a 'b] (m : ('a, 'b) fmap) =
  oflist (to_seq (rng m)) axiomatized by frngE.

lemma mem_frng ['a 'b] (m : ('a, 'b) fmap) (y : 'b) :
  y \in frng m <=> rng m y.
proof. by rewrite frngE mem_oflist mem_to_seq ?finite_rng. qed.  

(* -------------------------------------------------------------------- *)
lemma frng0 ['a 'b] : frng empty<:'a, 'b> = fset0.
proof. by apply/fsetP=> x; rewrite mem_frng mem_rng_empty in_fset0. qed.

(* ==================================================================== *)
lemma fmapW ['a 'b] (p : ('a, 'b) fmap -> bool) :
      p empty
   => (forall m k v, !k \in fdom m => p m => p m.[k <- v])
   => forall m, p m.
proof.
move=> h0 hS; suff: forall s, forall m, fdom m = s => p m.
+ by move=> h m; apply/(h (fdom m)).
elim/fset_ind => [|x s x_notin_s ih] m => [/fdom_eq0 ->//|].
move=> fdmE; have x_in_m: x \in fdom m by rewrite fdmE in_fsetU1.
have ->: m = (rem m x).[x <- oget m.[x]].
+ apply/fmap_eqP => y; case: (y = x) => [->|ne_xy].
  - by move/fdomP: x_in_m; rewrite get_set_sameE; case: m.[x].
  - by rewrite get_set_neqE // remE ne_xy.
apply/hS; first by rewrite mem_fdom_rem x_in_m.
apply/ih; rewrite fdom_rem fdmE fsetDK; apply/fsetP.
by move=> y; rewrite in_fsetD1 andb_idr //; apply/contraL.
qed.

(* ==================================================================== *)
op (+) (m1 m2 : ('a,'b) fmap) : ('a,'b) fmap =
  ofmap (Map.offun (fun x=> if x \in m2 then m2.[x] else m1.[x])).

(* -------------------------------------------------------------------- *)
lemma joinE ['a 'b] (m1 m2 : ('a,'b) fmap) (x : 'a):
  (m1 + m2).[x] = if x \in m2 then m2.[x] else m1.[x].
proof.
rewrite /(+) getE ofmapK /= 2:Map.getE 2:Map.offunK //.
apply/finiteP=> /=; exists (elems (fdom m1) ++ elems (fdom m2))=> x0 /=.
rewrite Map.getE Map.offunK /= mem_cat -!memE !mem_fdom !domE.
by case: (m2.[x0]).
qed.

(* -------------------------------------------------------------------- *)
lemma mem_join ['a 'b] (m1 m2 : ('a,'b) fmap) (x : 'a):
  x \in (m1 + m2) <=> x \in m1 \/ x \in m2.
proof. by rewrite domE joinE !domE; case: (m2.[x]). qed.

(* ==================================================================== *)
lemma get_none (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => m.[x] = None.
proof. by rewrite domE. qed.

(* -------------------------------------------------------------------- *)
lemma get_some (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x] = Some (oget m.[x]).
proof. move=> /domE; by case m.[x]. qed.

(* -------------------------------------------------------------------- *)
lemma set_same (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x <- oget m.[x]] = m.
proof.
move=> x_in_m.
apply fmap_eqP => y.
case (y = x) => [->> | ne_y_x].
by rewrite get_set_sameE get_some.
by rewrite get_setE ne_y_x.
qed.

(* -------------------------------------------------------------------- *)
lemma set_eq (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  m.[x] = Some y => m.[x <- y] = m.
proof.
move=> m_get_x_eq_y.
have x_in_m : x \in m by rewrite domE m_get_x_eq_y.
have -> : y = oget m.[x] by rewrite m_get_x_eq_y oget_some.
by rewrite set_same.
qed.

(* -------------------------------------------------------------------- *)
lemma frng_set (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  frng m.[x <- y] = frng (rem m x) `|` fset1 y.
proof.
apply fsetP => z; rewrite in_fsetU in_fset1 2!mem_frng 2!rngE /=.
split => [[x'] | [[x'] | ->]].
case (x' = x) => [-> | ne_x'_x].
by rewrite get_set_sameE /= => ->.
rewrite get_setE ne_x'_x /= => get_x'_some_z.
left; exists x'; by rewrite remE ne_x'_x.
rewrite remE.
case (x' = x) => // ne_x'_x get_x'_some_z.
exists x'; by rewrite get_setE ne_x'_x.
exists x; by rewrite get_set_sameE.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_notp_in (X : 'a -> bool, y : 'a, m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => ! X y => y \in m1 => y \in m2.
proof. move=> /eq_exceptP eq_exc not_X_y; by rewrite 2!domE eq_exc. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_setr_as_l (m1 m2 : ('a, 'b) fmap, x) :
  x \in m1 => eq_except (pred1 x) m1 m2 =>
  m1 = m2.[x <- oget m1.[x]].
proof.
rewrite eq_exceptP -fmap_eqP=> x_in_m1 eqe x'.
rewrite get_setE /oget; case (x' = x)=> [->> |].
by move: x_in_m1; rewrite domE; case (m1.[x]).
by move=> ne_x'_x; rewrite eqe.
qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_set_both (X : 'a -> bool, x, b, b', m : ('a, 'b) fmap):
  X x => eq_except X m.[x <- b] m.[x <- b'].
proof.
move=> X_x; rewrite eq_exceptP=> x' not_X_x'; rewrite !get_setE.
by case (x' = x).
qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_rem (m1 m2 : ('a,'b) fmap, X : 'a -> bool, x) :
   X x => eq_except X m1 m2 => eq_except X m1 (rem m2 x).
proof.
move=> X_x /eq_exceptP eq_exc; rewrite eq_exceptP=> y not_X_y; rewrite remE.
case (y = x)=> [->> // | ne_y_x]; by apply eq_exc.
qed.

(* -------------------------------------------------------------------- *)
lemma rem_id (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => rem m x = m.
proof.
move=> x_notin_m; apply fmap_eqP => y; rewrite remE.
case (y = x) => // ->.
case (None = m.[x]) => // get_not_none.
rewrite eq_sym -domE // in get_not_none.
qed.

(* -------------------------------------------------------------------- *)
lemma map_empty (f : 'a -> 'b -> 'c, m : ('a, 'b) fmap) :
  map f empty = empty.
proof. by rewrite -fmap_eqP=> x; rewrite mapE 2!emptyE. qed.

(* -------------------------------------------------------------------- *)
lemma map_rem (f:'a -> 'b -> 'c, m, x) :
  map f (rem m x) = rem (map f m) x.
proof.
rewrite -fmap_eqP=> z; by rewrite !(mapE,remE); case (z = x).
qed.

(* -------------------------------------------------------------------- *)
lemma map_id (m : ('a,'b) fmap) :
  map (fun _ b => b) m = m.
proof. by rewrite -fmap_eqP=>x; rewrite mapE; case (m.[x]). qed.

(* -------------------------------------------------------------------- *)
lemma le_card_frng_fdom (m : ('a, 'b) fmap) :
  card (frng m) <= card (fdom m).
proof.
elim /fmapW: m=> [| m k v k_notin_m IH].
by rewrite frng0 fdom0 2!fcards0.
rewrite mem_fdom in k_notin_m.
rewrite frng_set rem_id // fdom_set.
rewrite (fcardUI_indep _ (fset1 k)) 1:fsetI1 1:mem_fdom 1:k_notin_m //.
rewrite fcard1 fcardU fcard1 -addzA IntOrder.ler_add //.
rewrite -{2}(addz0 1) IntOrder.ler_add // oppz_le0 fcard_ge0.
qed.
