(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import ExtEq.
require import Int.
require export Option.
require import FSet.

type ('a,'b) map.

(** Our base element is empty *)
op empty: ('a,'b) map.

(** We define equality in terms of get *)
op "_.[_]": ('a,'b) map -> 'a -> 'b option.

axiom get_empty (x:'a):
  empty<:'b='b>.[x] = None.

pred (==) (m1 m2:('a,'b) map) = forall x,
  m1.[x] = m2.[x].

lemma nosmt eq_refl (m:('a,'b) map):
  m == m
by done.

lemma nosmt eq_tran (m2 m1 m3:('a,'b) map):
  m1 == m2 => m2 == m3 => m1 == m3
by (move=> m1_m2 m2_m3 x; rewrite m1_m2 m2_m3).

lemma nosmt eq_symm (m1 m2:('a,'b) map):
  m1 == m2 => m2 == m1
by (move=> m1_m2 x; rewrite eq_sym m1_m2).

axiom map_ext (m1 m2:('a,'b) map):
  m1 == m2 => m1 = m2.

(** Domain *)
op dom: ('a,'b) map -> 'a fset.

axiom mem_dom (m:('a,'b) map) x:
  mem (dom m) x <=> m.[x] <> None.

lemma dom_empty: dom empty<:'a,'b> = fset0.
proof.
  apply fsetP=> x.
  by rewrite mem_dom get_empty in_fset0.
qed.

lemma empty_dom (m:('a,'b) map): dom m = fset0 => m = empty<:'a,'b>.
proof.
  move=> dom_empty; apply map_ext=> x.
  smt.
qed.

(** Range *)
op rng: ('a,'b) map -> 'b fset.

axiom mem_rng (m:('a,'b) map) y:
  mem (rng m) y <=> exists x, m.[x] = Some y.

lemma rng_empty: rng empty<:'a,'b> = fset0.
proof.
  apply fsetP=> y.
  by rewrite mem_rng; smt.
qed.

(** Less defined than *)
pred (<=) (m1 m2:('a,'b) map) = forall x,
  mem (dom m1) x =>
  m1.[x] = m2.[x].

lemma leq_dom (m1 m2:('a,'b) map):
  m1 <= m2 =>
  dom m1 <= dom m2.
proof.
move=> H x x_m1; rewrite mem_dom.
by cut <-:= H x _=> //; rewrite -mem_dom.
qed.

lemma leq_rng (m1 m2:('a,'b) map):
  m1 <= m2 =>
  rng m1 <= rng m2.
proof.
  move=> m1_leq_m2 y.
  rewrite !mem_rng=> -[x m1x_y].
  by exists x; rewrite -m1_leq_m2 // mem_dom m1x_y.
qed.

lemma nosmt leq_refl (m:('a,'b) map):
  m <= m
by done.

lemma nosmt leq_tran (m2 m1 m3:('a,'b) map):
  m1 <= m2 => m2 <= m3 => m1 <= m3.
proof.
move=> m1_m2 m2_m3 x x_m1.
by rewrite m1_m2 2:m2_m3 2:(leq_dom m1 m2 _ x _).
qed.

lemma nosmt leq_asym (m1 m2:('a,'b) map):
  m1 <= m2 => m2 <= m1 => m1 == m2.
proof.
move=> m1_m2 m2_m1 x.
case (m1.[x] <> None)=> /= x_m1.
  by rewrite m1_m2 1:mem_dom.
  case (m2.[x] <> None)=> /= x_m2.
    by rewrite m2_m1 1:mem_dom.
    by rewrite x_m2.
qed.

(** Size definition *)
op size (m:('a,'b) map) = card (dom m).

lemma nosmt size_nneg (m:('a,'b) map): 0 <= size m.
proof. by rewrite /size cardE List.size_ge0. qed.

lemma nosmt size_empty: size empty<:'a,'b> = 0.
proof.
by rewrite /size dom_empty fcards0.
qed.

lemma nosmt size_leq (m1 m2:('a,'b) map):
  m1 <= m2 =>
  size m1 <= size m2
by [].

(* rm *)
op rm: 'a -> ('a,'b) map -> ('a,'b) map.
axiom get_rm x (m:('a,'b) map) x':
  (rm x m).[x'] = if x = x' then None else m.[x'].

lemma nosmt get_rm_eq (m:('a,'b) map) x:
  (rm x m).[x] = None
by (rewrite get_rm).

lemma nosmt get_rm_neq (m:('a,'b) map) x x':
  x <> x' =>
  (rm x m).[x'] = m.[x']
by (rewrite -neqF get_rm=> ->).

lemma dom_rm (m:('a,'b) map) x:
  dom (rm x m) = (dom m) `\` (fset1 x).
proof.
apply fsetP=> x'; rewrite mem_dom get_rm in_fsetD in_fset1;
case (x = x').
  by move=> <-.
  by rewrite eq_sym mem_dom=> ->.
qed.

lemma rng_rm (m:('a,'b) map) x y:
  mem (rng (rm x m)) y = (exists x', x <> x' /\ m.[x'] = Some y).
proof.
  rewrite mem_rng eq_iff; split.
    elim=> x'; rewrite get_rm.
    case (x = x')=> //= x_neq_x' mx'_y.
    by exists x'.
    elim=> x' [x_eq_x' mx'_y].
    by exists x'; rewrite get_rm (_: (x = x') = false); first smt.
qed.

lemma size_rm (m:('a,'b) map) x:
  size (rm x m) = if mem (dom m) x then size m - 1 else size m.
proof.
  by rewrite /size dom_rm (fcardD1 (dom m) x); case (mem (dom m) x); 1:smt.
qed.

lemma nosmt size_rm_in (m:('a,'b) map) x:
  mem (dom m) x =>
  size (rm x m) = size m - 1.
proof. by rewrite size_rm=> ->. qed.

lemma nosmt size_rm_nin (m:('a,'b) map) x:
  !mem (dom m) x =>
  size (rm x m) = size m.
proof. by rewrite size_rm=> ->. qed.

lemma rm_nin_id x (m:('a,'b) map): !mem (dom m) x => rm x m = m.
proof.
  move=> x_notin_m.
  apply map_ext=> x'; rewrite get_rm.
  smt.
qed.

(** We can now define writing operators *)
(* set *)
op "_.[_<-_]": ('a,'b) map -> 'a -> 'b -> ('a,'b) map.

axiom get_set (m:('a,'b) map) x x' y:
  m.[x <- y].[x'] = if x = x' then Some y else m.[x'].

lemma nosmt get_set_eq (m:('a,'b) map) x y:
  m.[x <- y].[x] = Some y
by (rewrite get_set).

lemma nosmt get_set_neq (m:('a,'b) map) x x' y:
  x <> x' =>
  m.[x <- y].[x'] = m.[x']
by (rewrite -neqF get_set=> ->).

lemma set_rm_set (m:('a,'b) map) x y:
  m.[x <- y] = (rm x m).[x <- y].
proof.
  apply map_ext=> x'; case (x = x').
    by move=> ->; rewrite !get_set_eq.
    by move=> x_neq_x'; rewrite !get_set_neq 3:get_rm_neq.
qed.

lemma dom_set (m:('a,'b) map) x y:
  dom (m.[x <- y]) = (dom m) `|` fset1 x.
proof.
apply fsetP=> x'; rewrite in_fsetU in_fset1; case (x = x').
  by move=> <-; rewrite mem_dom get_set.
  by rewrite -neqF=> x_x'; rewrite (eq_sym x') 2!mem_dom get_set_neq ?x_x'.
qed.

lemma nosmt dom_set_in (m:('a,'b) map) x y:
  mem (dom m) x =>
  dom (m.[x <- y]) = dom m.
proof.
  rewrite dom_set fsetP=> x_in_m x'.
  by rewrite in_fsetU in_fset1; move: x_in_m; case (x' = x)=> [<<-|].
qed.

lemma nosmt dom_set_nin (m:('a,'b) map) x y x':
  !mem (dom m) x' =>
  (mem (dom (m.[x <- y])) x' <=> x' = x).
proof. by rewrite dom_set in_fsetU in_fset1=> ->. qed.

lemma mem_dom_set y x (m:('a,'b) map) x':
  mem (dom m.[x <- y]) x' <=> (mem (dom m) x' \/ x' = x).
proof. by rewrite dom_set in_fsetU in_fset1. qed.

lemma dom_set_stable (m:('a,'b) map) x y x':
  mem (dom m) x' => mem (dom m.[x <- y]) x'.
proof. by rewrite mem_dom_set=> H; left. qed.

lemma rng_set (m:('a,'b) map) x y:
  rng (m.[x <- y]) = (rng (rm x m)) `|` fset1 y.
proof.
  apply fsetP=> y'.
  rewrite in_fsetU in_fset1 !mem_rng; split.
    elim=> x'; rewrite get_set; case (x = x').
      by move=> H {H x'}; move=> y_eq_y'; apply someI in y_eq_y'; rewrite eq_sym; right.
      by move=> x_neq_x' mx'_y'; left; exists x'; rewrite get_rm_neq.
    elim=> [[x' mx'_y'] | ->]; last by exists x; rewrite get_set.
    by exists x'; smt.
qed.

lemma size_set (m:('a,'b) map) x y:
  size m.[x <- y] = if mem (dom m) x then size m else size m + 1.
proof.
rewrite /size dom_set; case (mem (dom m) x)=> x_m; smt.
qed.

lemma nosmt size_set_in (m:('a,'b) map) x y:
  mem (dom m) x =>
  size m.[x <- y] = size m.
proof. by rewrite size_set; smt. qed.

lemma nosmt size_set_nin (m:('a,'b) map) x y:
  !mem (dom m) x =>
  size m.[x <- y] = size m + 1.
proof. by rewrite size_set=> ->. qed.

lemma set_set (m:('a,'b) map) x x' y y':
  m.[x <- y].[x' <- y'] = if x = x' then m.[x' <- y']
                                    else m.[x' <- y'].[x <- y].
proof.
apply map_ext=> x0; case (x = x').
  move=> ->; case (x' = x0).
    by move=> ->; rewrite 2!get_set_eq.
    by move=> x'_x0; rewrite 3?get_set_neq.
  move=> x_x'; case (x = x0).
    by move=> <-; rewrite get_set_neq -eq_sym // 2!(get_set_eq _ x).
    move=> x_x0; rewrite (get_set_neq (m.[x' <- y'])) //; case (x' = x0).
      by move=> <-; rewrite 2!get_set_eq.
      by move=> x'_x0; rewrite 3?get_set_neq.
qed.

lemma nosmt set_set_eq (m:('a,'b) map) x y y':
  m.[x <- y].[x <- y'] = m.[x <- y']
by (rewrite set_set).

lemma set_set_neq (m:('a,'b) map) x x' y y':
  x <> x' =>
  m.[x <- y].[x' <- y'] = m.[x' <- y'].[x <- y]
by (rewrite -neqF set_set=> ->).

lemma set_same (x:'a) (m:('a,'b)map):
   mem (dom m) x =>
   m.[x <- oget m.[x]] = m.
proof.
  by move=> Hm; apply map_ext; smt.
qed.

(* all and allb *)
pred all (p:'a -> 'b -> bool) (m:('a,'b) map) = forall x,
  mem (dom m) x =>
  p x (oget m.[x]).

op allb: ('a -> 'b -> bool) -> ('a,'b) map -> bool.

axiom allb_all (p:'a -> 'b -> bool) (m:('a,'b) map):
  allb p m = all p m.

(* exist and existb *)
pred exist (p:'a -> 'b -> bool) (m:('a,'b) map) = exists x,
  mem (dom m) x /\ p x (oget m.[x]).

op existb: ('a -> 'b -> bool) -> ('a,'b) map -> bool.

axiom existb_exist (p:'a -> 'b -> bool) (m:('a,'b) map):
  existb p m = exist p m.

lemma not_exist_all (p:'a -> 'b -> bool) (m:('a,'b) map):
  (!exist p m) = all (fun x y, !(p x y)) m.
proof.
by rewrite eq_iff /exist /Self.all; split; smt.
qed.

lemma not_existb_allb (p:'a -> 'b -> bool) (m:('a,'b) map):
  (!existb p m) = allb (fun x y, !(p x y)) m.
proof.
by rewrite existb_exist allb_all not_exist_all.
qed.

lemma all_set_all_in (p:'a -> 'b -> bool) (m:('a,'b) map) x y:
  all p m =>
  p x y =>
  all p m.[x <- y].
proof.
move=> p_m p_xy a; case (x = a).
  by move=> <- _; rewrite get_set_eq oget_some.
  move=> a_x; rewrite get_set_neq // dom_set in_fsetU in_fset1 (_: (a = x) = false) 1:(eq_sym a) 1:neqF //= => a_m.
  by rewrite p_m.
qed.

(* find *)
op find: ('a -> 'b -> bool) -> ('a,'b) map -> 'a option.

axiom find_nin (p:'a -> 'b -> bool) m:
  all (fun x y, !p x y) m <=> find p m = None.

axiom find_cor (p:'a -> 'b -> bool) m x:
  find p m = Some x =>
  mem (dom m) x /\ p x (oget m.[x]).

lemma find_in (p:'a -> 'b -> bool) (m:('a,'b) map):
  exist p m <=> find p m <> None.
proof.
  case {-1}(find p m) (Logic.eq_refl (find p m))=> //=.
    by rewrite -find_nin; smt. (* de Morgan *)
    by move=> x /find_cor found; exists x.
qed.

lemma find_ext (p':'a -> 'b -> bool) (m:('a,'b) map) p:
  (forall x y, p x y = p' x y) => (* extending both arguments *)
  find p m = find p' m.
proof.
  move=> p_p'.
  cut -> //=: p = p'.
  apply fun_ext=> x /=.
  apply fun_ext=> y /=.
  by rewrite p_p'.
qed.

lemma find_unique x' p (m:('a,'b) map):
  (forall x, p x (oget m.[x]) => x = x') =>
  mem (dom m) x' =>
  p x' (oget m.[x']) =>
  find p m = Some x'.
proof.
  move=> p_unique x'_in_m p_x'.
  case {-1}(find p m) (Logic.eq_refl (find p m))=> //=.
    by rewrite -find_nin; smt. (* de Morgan *)
    by move=> x0 /find_cor [] _ /p_unique.
qed.

(* find1 *)
op find1: ('a -> bool) -> ('a,'b) map -> 'a option.

axiom find1_nin (p:'a -> bool) (m:('a,'b) map):
  all (fun x y, !p x) m <=> find1 p m = None.

axiom find1_cor (p:'a -> bool) (m:('a,'b) map) x:
  find1 p m = Some x =>
  mem (dom m) x /\ p x.

lemma find1_in (p:'a -> bool) (m:('a,'b) map):
  exist (fun x y, p x) m <=> find1 p m <> None.
proof.
  case {-1}(find1 p m) (Logic.eq_refl (find1 p m))=> //=.
    by rewrite -find1_nin; smt. (* de Morgan *)
    by move=> x /find1_cor found; exists x.
qed.

(* filter *)
op filter: ('a -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map.

axiom get_filter f (m:('a,'b) map) x:
  (filter f m).[x] = if f x (oget m.[x]) then m.[x] else None.

lemma filter_empty (f:'a -> 'b -> bool): 
   filter f (empty<:'a,'b>) = empty<:'a,'b>.
proof. by apply map_ext=> x;smt. qed.

lemma nosmt get_filter_nin f (m:('a,'b) map) x:
  !mem (dom m) x =>
  (filter f m).[x] = m.[x].
proof.
by rewrite get_filter mem_dom /= => ->.
qed.

lemma dom_filter f (m:('a,'b) map):
  dom (filter f m) = filter (fun x, f x (oget m.[x])) (dom m).
proof.
by apply fsetP=> x; rewrite mem_dom get_filter in_filter mem_dom /=;
   case (f x (oget m.[x])).
qed.

lemma dom_filter_fst f (m:('a,'b) map):
  dom (filter (fun x y, f x) m) = filter f (dom m).
proof. by apply/(dom_filter (fun x (y : 'b) => f x)). qed.

lemma mem_dom_filter f (m:('a,'b) map) x:
  mem (dom (filter f m)) x =>
  mem (dom m) x /\ f x (oget m.[x])
by (rewrite dom_filter in_filter).

lemma leq_filter f (m:('a,'b) map):
  filter f m <= m.
proof.
by rewrite /Self.(<=)=> x x_in_f; rewrite get_filter;
   cut:= mem_dom_filter f m x _; last move=> [_ ->].
qed.

lemma filter_set_true f (m:('a,'b) map) x y:
  f x y =>
  filter f m.[x <- y] = (filter f m).[x <- y].
proof.
move=> f_xy; apply map_ext=> a.
case (x = a).
  by move=> <-; rewrite get_filter 2!get_set_eq /oget //= f_xy.
  by move=> neq_x_a; rewrite get_filter !get_set_neq // -get_filter.
qed.

lemma filter_set_false f (m:('a,'b) map) x y:
  !f x y =>
  filter f m.[x <- y] = rm x (filter f m).
proof.
rewrite -neqF=> not_f_xy; apply map_ext=> a.
case (x = a).
  by move=> <-; rewrite get_filter get_set_eq /oget //= not_f_xy get_rm.
  by rewrite -neqF=> neq_x_a;
     rewrite get_filter get_set_neq 1:neq_x_a // get_rm neq_x_a //= -get_filter.
qed.

lemma size_filter f (m:('a,'b) map): size (filter<:'a,'b> f m) <= size m.
proof. by apply size_leq; apply leq_filter. qed.

(* eq_except *)
pred eq_except (m1 m2:('a,'b) map) x = forall x',
  x <> x' => m1.[x'] = m2.[x'].

lemma eq_except_refl (m:('a,'b) map) x:
  eq_except m m x
by [].

lemma eq_except_symm (m1 m2:('a,'b) map) x:
  eq_except m1 m2 x = eq_except m2 m1 x
by [].

lemma eq_except_eq (m1 m2:('a,'b) map) x x':
  eq_except m1 m2 x =>
  mem (dom m1) x' <=> !mem (dom m2) x' =>
  x = x'
by [].

lemma eq_except_set1_eq (m1 m2:('a,'b) map) x y:
  eq_except m1 m2 x =>
  eq_except m1.[x <- y] m2 x
by [].

lemma eq_except_in_dom (m1 m2:('a, 'b) map) (x y:'a) :
  eq_except m1 m2 x => x <> y => (mem (dom m1) y <=> mem (dom m2) y)
by [].

lemma eq_except_set2 (m1 m2:('a,'b) map) x x' y1 y2:
  eq_except m1 m2 x =>
  (eq_except m1.[x' <- y1] m2.[x' <- y2] x <=>
   x = x' \/ y1 = y2).
proof.
  move=> m1_eqe_m2_x; split.
    case (x = x')=> //= x_neq_x' eqe_set2.
    by cut:= eqe_set2 x' _=> //; rewrite !get_set_eq.
  move=> [<- | <-] x0 x_neq_x0.
    by rewrite !get_set_neq //; apply m1_eqe_m2_x.
    by rewrite !get_set; case (x' = x0)=> //= _; apply m1_eqe_m2_x.
qed.

(* map *)
op map: ('b -> 'c) -> ('a,'b) map -> ('a,'c) map.

axiom get_map (f:'b -> 'c) (m:('a,'b) map) (x:'a):
  (map f m).[x] = omap f m.[x].

lemma map_empty (f:'b -> 'c) : map f (empty<:'a,'b>) = empty<:'a,'c>.
proof. apply map_ext => x;smt. qed.
  
lemma map_set (f:'b -> 'c) (m:('a,'b) map) (x:'a) y:
  map f (m.[x <- y]) = (map f m).[x <- f y].
proof. by apply map_ext;move=> x';case (x = x');smt. qed.

lemma dom_map (f:'b -> 'c) (m:('a,'b) map):
   dom (map f m) = dom m.
proof. by apply fsetP=> x; rewrite !mem_dom get_map; case (m.[x]). qed.

lemma mem_rng_map (f:'b -> 'c) (m:('a,'b) map) (y:'c):
  mem (rng (map f m)) y = exists x, omap f m.[x] = Some y
by [].

op mapi: ('a -> 'b -> 'c) -> ('a,'b) map -> ('a,'c) map.

axiom get_mapi (f:'a -> 'b -> 'c) (m:('a,'b) map) (x:'a):
  (mapi f m).[x] = omap (f x) m.[x].

(** Lemmas that bind it all together **)
lemma leq_card_rng_dom (m:('a,'b) map):
  card (rng m) <= card (dom m).
proof.
  elim/fset_ind (dom m) {-2}m (Logic.eq_refl (dom m))=> {m} [|x s x_notin_s ih m dom_m].
    by move=> m /empty_dom ->; rewrite rng_empty dom_empty !fcards0.
  cut ->: m = (rm x m).[x <- oget m.[x]].
    by apply map_ext=> x0; rewrite get_set; smt.
  rewrite rng_set.
  cut ->: rm x (rm x m) = (rm x m).
    by apply map_ext=> x0; smt.
  have:= ih (rm x m) _.
    apply/fsetP=> x'; rewrite dom_rm dom_m in_fsetD in_fsetU !in_fset1.
    by case (x' = x).
  smt.
qed.

lemma endo_dom_rng (m:('a,'a) map):
  (exists x, !mem (dom m) x) =>
  exists x, !mem (rng m) x.
proof.
  elim=> x x_notin_m.
  cut: 0 < card (((dom m) `|` fset1 x) `\` (rng m)); last smt.
  rewrite fcardD !fcardU !fcard1.
  have ->: dom m `&` fset1 x = fset0.
    by apply/fsetP=> x'; rewrite in_fsetI in_fset1 in_fset0 /=; case (x' = x).
  rewrite !fcards0 //=.
  smt.
qed.    

(** Miscellaneous higher-order stuff *)
(* lam and lamo: turning maps into lambdas *)
op lam (m:('a,'b) map) = fun x, oget m.[x].
op lamo (m:('a,'b) map) = "_.[_]" m.

lemma lamo_map (f:'b -> 'c) (m:('a,'b) map):
  lamo (map f m) = fun x, (omap f) ((lamo m) x).
proof.
apply ExtEq.fun_ext=> x //=.
by rewrite /lamo /lamo get_map; elim/option_ind m.[x].
qed.
