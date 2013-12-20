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
by (intros=> m1_m2 m2_m3 x; rewrite m1_m2 m2_m3).

lemma nosmt eq_symm (m1 m2:('a,'b) map):
  m1 == m2 => m2 == m1
by (intros=> m1_m2 x; rewrite eq_sym m1_m2).

axiom map_ext (m1 m2:('a,'b) map):
  m1 == m2 => m1 = m2.

(** Domain *)
op dom: ('a,'b) map -> 'a set.

axiom mem_dom (m:('a,'b) map) x:
  mem x (dom m) <=> m.[x] <> None.

lemma dom_empty: dom empty<:'a,'b> = FSet.empty.
proof strict.
apply set_ext=> x.
by rewrite mem_dom get_empty /= mem_empty.
qed.

op in_dom (x:'a) (m:('a,'b) map) = mem x (dom m).

lemma in_dom_empty x: !in_dom x empty<:'a,'b>.
proof strict.
by rewrite /in_dom mem_dom get_empty /=.
qed.

(** Less defined than *)
pred (<=) (m1 m2:('a,'b) map) = forall x,
  mem x (dom m1) =>
  m1.[x] = m2.[x].

lemma leq_dom (m1 m2:('a,'b) map):
  m1 <= m2 =>
  dom m1 <= dom m2.
proof strict.
intros=> H x x_m1; rewrite mem_dom.
by cut <-:= H x _=> //; rewrite -mem_dom.
qed.

lemma leq_in_dom (m1 m2:('a,'b) map) x:
  m1 <= m2 =>
  in_dom x m1 => in_dom x m2.
proof strict.
by rewrite /in_dom=> m1_m2; apply leq_dom.
qed.

lemma nosmt leq_refl (m:('a,'b) map):
  m <= m
by done.

lemma nosmt leq_tran (m2 m1 m3:('a,'b) map):
  m1 <= m2 => m2 <= m3 => m1 <= m3.
proof strict.
intros=> m1_m2 m2_m3 x x_m1.
by rewrite m1_m2 2:m2_m3 2:(leq_dom m1 m2 _ x _).
qed.

lemma nosmt leq_asym (m1 m2:('a,'b) map):
  m1 <= m2 => m2 <= m1 => m1 == m2.
proof strict.
intros=> m1_m2 m2_m1 x.
case (m1.[x] <> None)=> /= x_m1.
  by rewrite m1_m2 1:mem_dom.
  case (m2.[x] <> None)=> /= x_m2.
    by rewrite m2_m1 1:mem_dom.
    by rewrite x_m2.
qed.

(** Size definition *)
op size (m:('a,'b) map) = card (dom m).

lemma nosmt size_nneg (m:('a,'b) map): 0 <= size m.
proof strict.
by rewrite /size card_def List.length_nneg.
qed.

lemma nosmt size_empty: size empty<:'a,'b> = 0.
proof strict.
by rewrite /size dom_empty card_empty.
qed.

(* TODO: make sure we can prove
           lemma size_leq m1 m2: m1 <= m2 => size m1 <= size m2.
         This requires the (currently missing) card_leq lemma,
         which might be provable by a stronger form of induction. *)

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

lemma dom_set (m:('a,'b) map) x y:
  dom (m.[x <- y]) = add x (dom m).
proof strict.
apply set_ext=> x'; rewrite mem_add; case (x = x').
  by intros=> <-; rewrite mem_dom get_set.
  by rewrite -neqF=> x_x'; rewrite (eq_sym x') 2!mem_dom get_set_neq ?x_x'.
qed.

lemma nosmt dom_set_in (m:('a,'b) map) x y:
  mem x (dom m) =>
  dom (m.[x <- y]) = dom m.
proof strict.
by intros=> x_m; rewrite dom_set -add_in_id.
qed.

lemma in_dom_set (m:('a,'b) map) x y x':
  in_dom x' (m.[x <- y]) = (in_dom x' m \/ x' = x).
proof strict.
by rewrite /in_dom -mem_add; congr=> //; apply dom_set.
qed.

lemma nosmt in_dom_set_in (m:('a,'b) map) x y:
  in_dom x m =>
  forall x', in_dom x' (m.[x <- y]) <=> in_dom x' m.
proof strict.
by rewrite /in_dom=> x'_m; rewrite dom_set_in.
qed.

lemma nosmt in_dom_set_nin (m:('a,'b) map) x y x':
  !in_dom x' m =>
  (in_dom x' (m.[x <- y]) <=> x' = x).
proof strict.
by rewrite /in_dom=> x_m;
   rewrite dom_set mem_add (_: mem x' (dom m) = false) 1:neqF.
qed.

lemma size_set (m:('a,'b) map) x y:
  size m.[x <- y] = if in_dom x m then size m else size m + 1.
proof strict.
rewrite /size dom_set; case (in_dom x m)=> x_m.
  by rewrite card_add_in.
  by rewrite card_add_nin.
qed.

lemma nosmt size_set_in (m:('a,'b) map) x y:
  in_dom x m =>
  size m.[x <- y] = size m.
proof strict.
by rewrite /size dom_set=> x_m;
   rewrite card_add_in.
qed.

lemma nosmt size_set_nin (m:('a,'b) map) x y:
  !in_dom x m =>
  size m.[x <- y] = size m + 1.
proof strict.
by rewrite /size dom_set=> x_m;
   rewrite card_add_nin.
qed.

lemma set_set (m:('a,'b) map) x x' y y':
  m.[x <- y].[x' <- y'] = if x = x' then m.[x' <- y']
                                    else m.[x' <- y'].[x <- y].
proof strict.
apply map_ext=> x0; case (x = x').
  intros=> ->; case (x' = x0).
    by intros=> ->; rewrite 2!get_set_eq.
    by intros=> x'_x0; rewrite 3?get_set_neq.
  intros=> x_x'; case (x = x0).
    by intros=> <-; rewrite get_set_neq -eq_sym // 2!(get_set_eq _ x).
    intros=> x_x0; rewrite (get_set_neq (m.[x' <- y'])) //; case (x' = x0).
      by intros=> <-; rewrite 2!get_set_eq.
      by intros=> x'_x0; rewrite 3?get_set_neq.
qed.

lemma nosmt set_set_eq (m:('a,'b) map) x y y':
  m.[x <- y].[x <- y'] = m.[x <- y']
by (rewrite set_set).

lemma set_set_neq (m:('a,'b) map) x x' y y':
  x <> x' =>
  m.[x <- y].[x' <- y'] = m.[x' <- y'].[x <- y]
by (rewrite -neqF set_set=> ->).

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
  dom (rm x m) = rm x (dom m).
proof strict.
apply set_ext=> x'; rewrite mem_dom get_rm mem_rm;
case (x = x').
  by intros=> <-.
  by rewrite eq_sym mem_dom=> ->.
qed.

lemma in_dom_rm (m:('a,'b) map) x x':
  in_dom x (rm x' m) = (in_dom x m /\ x <> x').
proof strict.
by rewrite /in_dom dom_rm mem_rm.
qed.

lemma in_dom_rm_eq (m:('a,'b) map) x:
  !in_dom x (rm x m).
proof strict.
by rewrite /in_dom mem_dom get_rm.
qed.

lemma in_dom_rm_neq (m:('a,'b) map) x x':
  x <> x' =>
  in_dom x (rm x' m) = in_dom x m.
proof strict.
by intros=> x_x'; rewrite in_dom_rm x_x'.
qed.

lemma size_rm (m:('a,'b) map) x:
  size (rm x m) = if in_dom x m then size m - 1 else size m.
proof strict.
rewrite /size dom_rm; case (in_dom x m)=> x_m.
  by rewrite card_rm_in.
  by rewrite card_rm_nin.
qed.

lemma nosmt size_rm_in (m:('a,'b) map) x:
  in_dom x m =>
  size (rm x m) = size m - 1.
proof strict.
by rewrite /size dom_rm=> x_m;
   rewrite card_rm_in.
qed.

lemma nosmt size_rm_nin (m:('a,'b) map) x:
  !in_dom x m =>
  size (rm x m) = size m.
proof strict.
by rewrite /size dom_rm=> x_m;
   rewrite card_rm_nin.
qed.

(* all and allb *)
pred all (p:'a -> 'b -> bool) (m:('a,'b) map) = forall x,
  mem x (dom m) =>
  p x (proj m.[x]).

op allb: ('a -> 'b -> bool) -> ('a,'b) map -> bool.

axiom allb_all (p:'a -> 'b -> bool) (m:('a,'b) map):
  allb p m = all p m.

(* exist and existb *)
pred exist (p:'a -> 'b -> bool) (m:('a,'b) map) = exists x,
  mem x (dom m) /\ p x (proj m.[x]).

op existb: ('a -> 'b -> bool) -> ('a,'b) map -> bool.

axiom existb_exist (p:'a -> 'b -> bool) (m:('a,'b) map):
  existb p m = exist p m.

lemma not_exist_all (p:'a -> 'b -> bool) (m:('a,'b) map):
  (!exist p m) = all (fun x y, !(p x y)) m.
proof strict.
by rewrite eq_iff /exist /Top.all; split; smt.
qed.

lemma not_existb_allb (p:'a -> 'b -> bool) (m:('a,'b) map):
  (!existb p m) = allb (fun x y, !(p x y)) m.
proof strict.
by rewrite existb_exist allb_all not_exist_all.
qed.

lemma all_set_all_in (p:'a -> 'b -> bool) (m:('a,'b) map) x y:
  all p m =>
  p x y =>
  all p m.[x <- y].
proof strict.
intros=> p_m p_xy a; case (x = a).
  by intros=> <- _; rewrite get_set_eq proj_some.
  intros=> a_x; rewrite get_set_neq // dom_set mem_add (_: (a = x) = false) 1:(eq_sym a) 1:neqF //= => a_m.
  by rewrite p_m.
qed.

(* find *) (* Reduce the axiomatization *)
op find: ('a -> 'b -> bool) -> ('a,'b) map -> 'a option.

axiom find_in (p:'a -> 'b -> bool) (m:('a,'b) map):
  exist p m => find p m <> None.

axiom find_nin (p:'a -> 'b -> bool) m:
  all (fun x y, !p x y) m => find p m = None.

axiom find_cor (p:'a -> 'b -> bool) m x:
  find p m = Some x =>
  mem x (dom m) /\ p x (proj m.[x]).

(* filter *)
op filter: ('a -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map.

axiom get_filter f (m:('a,'b) map) x:
  (filter f m).[x] = if f x (proj m.[x]) then m.[x] else None.

lemma nosmt get_filter_nin f (m:('a,'b) map) x:
  !mem x (dom m) =>
  (filter f m).[x] = m.[x].
proof strict.
by rewrite get_filter mem_dom /= => ->.
qed.

lemma dom_filter f (m:('a,'b) map):
  dom (filter f m) = filter (fun x, f x (proj m.[x])) (dom m).
proof strict.
by apply set_ext=> x; rewrite mem_dom get_filter mem_filter mem_dom /=;
   case (f x (proj m.[x])).
qed.

lemma dom_filter_fst f (m:('a,'b) map):
  dom (filter (fun x y, f x) m) = filter f (dom m).
proof strict.
by cut:= dom_filter (fun x (y:'b), f x) m => //= ->;
   congr=> //; apply Fun.fun_ext.
qed.

lemma mem_dom_filter f (m:('a,'b) map) x:
  mem x (dom (filter f m)) =>
  mem x (dom m) /\ f x (proj m.[x])
by (rewrite dom_filter mem_filter).

lemma leq_filter f (m:('a,'b) map):
  filter f m <= m.
proof strict.
by rewrite /Top.(<=)=> x x_in_f; rewrite get_filter;
   cut:= mem_dom_filter f m x _; last intros=> [_ ->].
qed.

(* TODO: Prove
     lemma size_filter f m: size (filter f m) <= size m.
   This is simple once we have size_leq. *)

(* eq_except *)
op eq_except: ('a,'b) map -> ('a,'b) map -> 'a -> bool.

axiom eq_except_def (m1 m2:('a,'b) map) x:
  eq_except m1 m2 x = forall x', x <> x' => m1.[x'] = m2.[x'].

lemma eq_eq_except (m:('a,'b) map) x:
  eq_except m m x
by [].

lemma eq_except_set_eq (m1 m2:('a,'b) map) x y:
  eq_except m1 m2 x =>
  mem x (dom m1) =>
  m2.[x] = Some y =>
  m1.[x <- y] = m2.
proof strict.
rewrite eq_except_def=> eqe x_ndom_m1 m2x.
apply map_ext=> x'; rewrite get_set; case (x = x').
  by intros=> <-; rewrite m2x.
  by apply eqe.
qed.

(* (* This is the way eq_except is most likely to be used: preservation of eq_except in ROMs *)
lemma eq_except_ROM (m1 m2:('a,'b) map) x0 x y0 y:
  let m1' = if !mem x0 (dom m1) then m1.[x0 <- (x0 = x) ? y : y0] else m1 in
  let m2' = if !mem x0 (dom m2) then m2.[x0 <- y0] else m2 in
  (if mem x (dom m1) then m1 = m2 else eq_except m1 m2 x) =>
  m2.[x] = Some y0 =>
  (if mem x (dom m1) then m1' = m2' else eq_except m1' m2' x).
proof strict.
progress.
  smt.
  smt.
  cut:= H; rewrite (_: (mem x (dom m1)) = false) 1:neqF //=.
  rewrite eq_except_def allb_all /Top.all //= => {H} H x'.
    intros=> ->; rewrite H1 /= 1:(_: (!mem x (dom m2)) = false) 1:mem_dom 1:H0 //=.
    by cut:= H; rewrite H1.
    smt.
*)  

(* map *)
op map: ('b -> 'c) -> ('a,'b) map -> ('a,'c) map.

axiom get_map (f:'b -> 'c) (m:('a,'b) map) (x:'a):
  (map f m).[x] = lift f m.[x].

op mapi: ('a -> 'b -> 'c) -> ('a,'b) map -> ('a,'c) map.

axiom get_mapi (f:'a -> 'b -> 'c) (m:('a,'b) map) (x:'a):
  (mapi f m).[x] = lift (f x) m.[x].

(** Miscellaneous higher-order stuff *)
(* lam and lamo: turning maps into lambdas *)
op lam (m:('a,'b) map) = fun x, proj m.[x].
op lamo (m:('a,'b) map) = "_.[_]" m.

lemma lamo_map (f:'b -> 'c) (m:('a,'b) map):
  lamo (map f m) = fun x, (lift f) ((lamo m) x).
proof strict.
apply Fun.fun_ext=> x //=.
by rewrite /lamo /lamo get_map; elim/option_ind m.[x].
qed.
