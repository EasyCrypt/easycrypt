(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore CoreMap Finite List FSet Ring StdOrder.
(*---*) import IntID IntOrder.

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

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_sub ['a 'b] (X Y : 'a -> bool) (m1 m2 : ('a, 'b) map) :
   X <= Y => eq_except X m1 m2 => eq_except Y m1 m2.
proof. by move=> hsub + x hx => -> //; apply: contra (hsub x) hx. qed.

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

lemma get_none (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => m.[x] = None.
proof. by rewrite domE. qed.

lemma get_some (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x] = Some (oget m.[x]).
proof. move=> /domE; by case m.[x]. qed.

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
by congr; apply/Map.map_eqP=> x; rewrite -!getE pw_eq.
qed.

(* -------------------------------------------------------------------- *)
op empty ['a 'b] : ('a, 'b) fmap = ofmap (cst None).

lemma nosmt empty_valE ['a, 'b] : tomap empty<:'a, 'b> = cst None.
proof.
by rewrite /empty ofmapK //; exists [] => /=.
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

(* -------------------------------------------------------------------- *)
lemma domNE ['a 'b] (m : ('a, 'b) fmap, x : 'a) :
  x \notin m <=> m.[x] = None.
proof. by rewrite domE. qed.

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
lemma get_set_id (m : ('a,'b) fmap) x y:
  m.[x] = Some y => m.[x <- y] = m.
proof.
move=> mxE; apply/fmap_eqP=> z; rewrite get_setE.
by case: (z = x) => [->|] //; rewrite mxE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_setE ['a 'b] (m : ('a, 'b) fmap) x x' b b' :
  m.[x <- b].[x' <- b']
    = (x' = x) ? m.[x' <- b'] : m.[x' <- b'].[x <- b].
proof.
apply/fmap_eqP=> y; rewrite !get_setE; case: (x' = x)=> //= [<<-|].
+ by rewrite !get_setE; case: (y = x').
+ by rewrite !get_setE; case: (y = x')=> //= ->> ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_sameE ['a 'b] (m : ('a, 'b) fmap) (x : 'a) b b' :
  m.[x <- b].[x <- b'] = m.[x <- b'].
proof. by rewrite set_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_eqE ['a 'b] (m : ('a, 'b) fmap) (x x' : 'a) b b' :
  x' = x => m.[x <- b].[x' <- b'] = m.[x <- b'].
proof. by rewrite set_setE. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_set_neqE ['a 'b] (m : ('a, 'b) fmap) (x x' : 'a) b b' :
  x' <> x => m.[x <- b].[x' <- b'] = m.[x' <- b'].[x <- b].
proof. by rewrite set_setE => ->. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_get ['a 'b] (m : ('a, 'b) fmap, x : 'a) :
  x \in m => m.[x <- oget m.[x]] = m.
proof.
move=> x_in_m; apply/fmap_eqP=> y; rewrite get_setE.
by case: (y = x) => // ->>; rewrite -some_oget.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt set_get_eq ['a 'b] (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  m.[x] = Some y => m.[x <- y] = m.
proof. by move=> mxE; rewrite -{2}(set_get _ x) ?domE // mxE. qed.

(* -------------------------------------------------------------------- *)
lemma mem_set ['a 'b] (m : ('a, 'b) fmap) x b y :
  y \in m.[x <- b] <=> (y \in m \/ y = x).
proof. by rewrite !domE get_setE; case: (y = x). qed.

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
lemma mem_rem ['a 'b] (m : ('a, 'b) fmap) x y :
  y \in (rem m x) <=> (y \in m /\ y <> x).
proof. by rewrite !domE remE; case: (y = x) => //=. qed.

(* -------------------------------------------------------------------- *)
lemma rem_id (m : ('a, 'b) fmap, x : 'a) :
  x \notin m => rem m x = m.
proof.
move=> x_notin_m; apply/fmap_eqP => y; rewrite remE.
by case (y = x) => // ->>; apply/eq_sym/domNE.
qed.

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

lemma eq_except_sub ['a 'b] (X Y : 'a -> bool) (m1 m2 : ('a, 'b) fmap) :
   X <= Y => eq_except X m1 m2 => eq_except Y m1 m2.
proof. by apply/Map.eq_except_sub<:'a, 'b option>. qed.

(* -------------------------------------------------------------------- *)
lemma eq_exceptP ['a 'b] X (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 <=> (forall x, !X x => m1.[x] = m2.[x]).
proof. by split=> h x /h. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except0 ['a 'b] (m1 m2 : ('a, 'b) fmap) :
  eq_except pred0 m1 m2 <=> m1 = m2.
proof. by rewrite eq_exceptP /pred0 /= fmap_eqP. qed.

(* -------------------------------------------------------------------- *)
lemma eq_except_notp_in (X : 'a -> bool, y : 'a, m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => ! X y => y \in m1 => y \in m2.
proof. move=> /eq_exceptP eq_exc not_X_y; by rewrite 2!domE eq_exc. qed.

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
lemma nosmt eq_except_set_getlr ['a 'b] (m1 m2 : ('a, 'b) fmap, x) :
     x \in m1
  => eq_except (pred1 x) m1 m2
  => m1 = m2.[x <- oget m1.[x]].
proof.
move=> x_in_m1 /eq_exceptP eqm; apply/fmap_eqP => x'; rewrite get_setE.
by case: (x' = x) => [->>|/eqm] //; apply/some_oget.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_setlr (X : 'a -> bool, m : ('a, 'b) fmap, x, b, b'):
  X x => eq_except X m.[x <- b] m.[x <- b'].
proof.
by move=> Xx; apply/eq_exceptP => x' NXx'; rewrite !get_setE; case: (x' = x).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_remr (X : 'a -> bool, m1 m2 : ('a,'b) fmap, x) :
   X x => eq_except X m1 m2 => eq_except X m1 (rem m2 x).
proof.
move=> Xx /eq_exceptP eqm; apply/eq_exceptP => y NXy.
by rewrite remE; case: (y = x) => // _; apply/eqm.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eq_except_reml (X : 'a -> bool, m1 m2 : ('a,'b) fmap, x) :
   X x => eq_except X m1 m2 => eq_except X (rem m1 x) m2.
proof.
by move=> Xx /eq_except_sym ?; apply/eq_except_sym/eq_except_remr.
qed.

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
lemma map_id (m : ('a,'b) fmap) :
  map (fun _ b => b) m = m.
proof. by apply/fmap_eqP => x; rewrite mapE /=; case: m.[x]. qed.

(* -------------------------------------------------------------------- *)
lemma map_empty (f : 'a -> 'b -> 'c) :
  map f empty = empty.
proof. by apply/fmap_eqP => x; rewrite mapE !emptyE. qed.

(* -------------------------------------------------------------------- *)
lemma map_rem (f:'a -> 'b -> 'c, m, x) :
  map f (rem m x) = rem (map f m) x.
proof.
by apply/fmap_eqP => z; rewrite !(mapE, remE) (fun_if (omap (f z))).
qed.

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
by rewrite !Map.getE Map.offunK -Map.getE /= getE; case: (tomap m).[y].
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

(* -------------------------------------------------------------------- *)
lemma mem_frng ['a 'b] (m : ('a, 'b) fmap) (y : 'b) :
  y \in frng m <=> rng m y.
proof. by rewrite frngE mem_oflist mem_to_seq ?finite_rng. qed.  

(* -------------------------------------------------------------------- *)
lemma frng0 ['a 'b] : frng empty<:'a, 'b> = fset0.
proof. by apply/fsetP=> x; rewrite mem_frng mem_rng_empty in_fset0. qed.

(* -------------------------------------------------------------------- *)
lemma frng_set (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  frng m.[x <- y] = frng (rem m x) `|` fset1 y.
proof.
apply/fsetP => z; rewrite in_fsetU in_fset1 !(mem_frng, rngE) /=.
case: (z = y) => [->>|neq_zy] /=; first by exists x; rewrite get_set_sameE.
apply/exists_eq => /= x'; rewrite remE !get_setE.
by case: (x' = x) => //= ->>; apply/negbTE; rewrite eq_sym.
qed.

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

(* -------------------------------------------------------------------- *)
lemma le_card_frng_fdom ['a 'b] (m : ('a, 'b) fmap) :
  card (frng m) <= card (fdom m).
proof.
elim/fmapW: m=> [| m k v k_notin_m ih].
+ by rewrite frng0 fdom0 !fcards0.
rewrite frng_set fdom_set rem_id -?mem_fdom //.
rewrite fcardU fcardUI_indep; first by rewrite fsetI1 k_notin_m.
by rewrite -addrA ler_add // !fcard1 ler_subl_addr ler_addl fcard_ge0.
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

lemma fdom_join ['a, 'b] (m1 m2 : ('a,'b) fmap):
 fdom (m1 + m2) = fdom m1 `|` fdom m2.
proof.
by apply/fsetP=> x; rewrite mem_fdom mem_join in_fsetU !mem_fdom.
qed.

(* ==================================================================== *)
op ofassoc ['a 'b] (xs : ('a * 'b) list) =
  ofmap (Map.offun (fun k => List.assoc xs k)).

(* -------------------------------------------------------------------- *)
lemma ofassoc_get ['a 'b] (xs : ('a * 'b) list) k :
  (ofassoc xs).[k] = List.assoc xs k.
proof.
rewrite getE ofmapK /= 1:&(finiteP) 2:Map.offunE //.
by exists (map fst xs) => a /=; rewrite Map.offunE &(assocTP).
qed.

(* -------------------------------------------------------------------- *)
lemma mem_ofassoc ['a, 'b] (xs : ('a * 'b) list) k:
 k \in ofassoc xs <=> k \in map fst xs.
proof. by rewrite domE ofassoc_get &(assocTP). qed.

(* -------------------------------------------------------------------- *)
lemma fdom_ofassoc ['a 'b] (xs : ('a * 'b) list) :
  fdom (ofassoc xs) = oflist (map fst xs).
proof.
apply/fsetP=> a; rewrite mem_oflist mem_fdom.
by rewrite /(_ \in _) ofassoc_get &(assocTP).
qed.

(* -------------------------------------------------------------------- *)
(*                             Flagged Maps                             *)
(* -------------------------------------------------------------------- *)
op noflags ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) =
  map (fun _ (p : _ * _) => p.`1) m.

op in_dom_with ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) (x : 'k) (f : 'f) =
 dom m x /\ (oget (m.[x])).`2 = f.

op restr ['k, 'v, 'f] f (m : ('k, 'v * 'f) fmap) = 
  let m = filter (fun _ (p : 'v * 'f) => p.`2 = f) m in
  noflags m.

lemma restrP ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) f x : (restr f m).[x] =
  obind (fun (p : _ * _) => if p.`2 = f then Some p.`1 else None) m.[x].
proof.
rewrite /restr /= mapE filterE /=.
by case (m.[x])=> //= -[x1 f'] /=; case (f' = f).
qed.

lemma dom_restr ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) f x :
  dom (restr f m) x <=> in_dom_with m x f. 
proof. 
rewrite /in_dom_with !domE; case: (m.[x]) (restrP m f x)=> //= -[t f'] /=.
by case (f' = f)=> [_ -> |].
qed.

lemma restr_set ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) f1 f2 x y :
  restr f1 m.[x <- (y, f2)]
    = if f1 = f2 then (restr f1 m).[x <- y] else rem (restr f1 m) x.
proof.
rewrite -fmap_eqP=> k; case: (f1 = f2) => [->|neq_f12].
+ by rewrite !(restrP, get_setE); case: (k = x).
rewrite !(restrP, get_setE); case: (k = x) => [->|ne_kx].
+ by rewrite (@eq_sym f2) neq_f12 /= remE.
by rewrite remE ne_kx /= restrP.
qed.

lemma restr_set_eq ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) f x y :
  restr f m.[x <- (y, f)] = (restr f m).[x <- y].
proof. by rewrite restr_set. qed.

lemma restr0 ['k, 'v, 'f] f : restr f empty<:'k, 'v * 'f> = empty.
proof. by apply fmap_eqP=> x; rewrite restrP !emptyE. qed.

lemma restr_set_neq ['k, 'v, 'f] f2 f1 (m : ('k, 'v * 'f) fmap) x y :
  ! dom m x => f2 <> f1 => restr f1 m.[x <- (y, f2)] = restr f1 m.
proof.
move=> Hm Hneq; rewrite restr_set (eq_sym f1) Hneq rem_id //.
by rewrite dom_restr /in_dom_with Hm.
qed.

lemma restr_rem ['k, 'v, 'f] (m : ('k, 'v * 'f) fmap) (x : 'k) f :
  restr f (rem m x)
    = (if in_dom_with m x f then rem (restr f m) x else restr f m).
proof.
rewrite -fmap_eqP => z; rewrite restrP; case: (in_dom_with m x f);
rewrite !(restrP, remE); rewrite /in_dom_with; case (z = x)=> // ->.
rewrite negb_and => -[Nxm|]; first by rewrite (iffLR _ _ (domNE m x)).
by case: m.[x] => //= x' ->.
qed.
