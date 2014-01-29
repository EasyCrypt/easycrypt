require import Int.
require export Option.
require import FSet.

theory Core.
  type ('a,'b) map.

  (** Our base element is empty *)
  op empty: ('a,'b) map.

  (** We define equality in terms of get *)
  op get: ('a,'b) map -> 'a -> 'b option.

  axiom get_empty (x:'a):
    get empty<:'b='b>  x = None.

  pred (==) (m1 m2:('a,'b) map) = forall x,
    get m1 x = get m2 x.

  lemma nosmt eq_refl (m:('a,'b) map):
    m == m.
  proof strict.
  by intros.
  qed.

  lemma nosmt eq_tran (m2 m1 m3:('a,'b) map):
    m1 == m2 => m2 == m3 => m1 == m3.
  proof strict.
  by rewrite /Core.(==)=> m1_m2 m2_m3 x;
     rewrite m1_m2 m2_m3.
  qed.

  lemma nosmt eq_symm (m1 m2:('a,'b) map):
    m1 == m2 => m2 == m1.
  proof strict.
  by rewrite /Core.(==)=> m1_m2 x;
     rewrite rw_eq_sym m1_m2.
  qed.

  axiom map_ext (m1 m2:('a,'b) map):
    m1 == m2 => m1 = m2.

  (** Domain *)
  op dom: ('a,'b) map -> 'a set.
  op in_dom (x:'a) (m:('a,'b) map) = mem x (dom m).

  axiom mem_dom (m:('a,'b) map) x:
    mem x (dom m) <=> get m x <> None.

  lemma nosmt in_dom_spec (m:('a,'b) map) x:
    in_dom x m <=> get m x <> None.
  proof strict.
  by rewrite /in_dom; apply mem_dom.
  qed.

  lemma dom_empty:
    dom empty<:'a,'b> = empty<:'a>.
  proof strict.
  by apply set_ext=> x; cut:= mem_empty x;
     rewrite -rw_neqF mem_dom get_empty; intros=> ->.
  qed.

  (** Less defined than *)
  pred (<=) (m1 m2:('a,'b) map) =
    forall x, mem x (dom m1) => get m1 x = get m2 x.

  lemma leq_dom (m1 m2:('a,'b) map): m1 <= m2 => dom m1 <= dom m2.
  proof strict.
  by intros=> H x; rewrite (mem_dom m2)=> x_m1;
     rewrite -H // -mem_dom.
  qed.

  lemma nosmt leq_refl (m:('a,'b) map):
    m <= m.
  proof strict.
  by intros.
  qed.

  lemma nosmt leq_tran (m2 m1 m3:('a,'b) map):
    m1 <= m2 => m2 <= m3 => m1 <= m3
  by [].

  lemma nosmt leq_asym (m1 m2:('a,'b) map):
    m1 <= m2 => m2 <= m1 => m1 == m2
  by [].

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
    get m.[x <- y] x' = if x = x' then Some y else get m x'.

  lemma nosmt get_setE (m:('a,'b) map) x y:
    get m.[x <- y] x = Some y.
  proof strict.
  by rewrite get_set.
  qed.

  lemma nosmt get_setN (m:('a,'b) map) x x' y:
    x <> x' =>
    get m.[x <- y] x' = get m x'.
  proof strict.
  by rewrite -rw_neqF get_set=> ->.
  qed.

  lemma dom_set (m:('a,'b) map) x y:
    dom (m.[x <- y]) = add x (dom m).
  proof strict.
  apply set_ext=> x'; rewrite mem_add; case (x = x').
    by intros=> <-; rewrite mem_dom get_set /=; smt. (* Option: disjointness of some and none *)
    by rewrite -rw_neqF=> x_x'; rewrite (rw_eq_sym x') 2!mem_dom get_setN ?x_x'.
  qed.

  lemma size_set (m:('a,'b) map) x y:
    size m.[x <- y] = if mem x (dom m) then size m else size m + 1.
  proof strict.
  rewrite /size dom_set; case (mem x (dom m))=> x_m.
    by rewrite card_add_in.
    by rewrite card_add_nin.
  qed.

  lemma nosmt size_setI (m:('a,'b) map) x y:
    mem x (dom m) =>
    size m.[x <- y] = size m.
  proof strict.
  by rewrite /size dom_set=> x_m;
     rewrite card_add_in.
  qed.

  lemma nosmt size_setN (m:('a,'b) map) x y:
    !mem x (dom m) =>
    size m.[x <- y] = size m + 1.
  proof strict.
  by rewrite /size dom_set=> x_m;
     rewrite card_add_nin.
  qed.

  (* This is nosmt because of the commutativity part... *)
  lemma nosmt set_set (m:('a,'b) map) x x' y y':
    m.[x <- y].[x' <- y'] = if x = x' then m.[x' <- y']
                                      else m.[x' <- y'].[x <- y].
  proof strict.
  apply map_ext=> x0; case (x = x').
    intros=> ->; case (x' = x0).
      by intros=> ->; rewrite 2!get_setE.
      by intros=> x'_x0; rewrite 3?get_setN.
    intros=> x_x'; case (x = x0).
      by intros=> <-; rewrite get_setN -rw_eq_sym // 2!(get_setE _ x).
      intros=> x_x0; rewrite (get_setN (m.[x' <- y'])) //; case (x' = x0).
        by intros=> <-; rewrite 2!get_setE.
        by intros=> x'_x0; rewrite 3?get_setN.
  qed.

  lemma set_setE (m:('a,'b) map) x y y':
    m.[x <- y].[x <- y'] = m.[x <- y'].
  proof strict.
  by rewrite set_set.
  qed.

  (* Again, we don't send commutation lemmas to smt until we can figure things out *)
  lemma nosmt set_setN (m:('a,'b) map) x x' y y':
    x <> x' =>
    m.[x <- y].[x' <- y'] = m.[x' <- y'].[x <- y].
  proof strict.
  by rewrite -rw_neqF set_set; intros=> ->.
  qed.

  (* rm *)
  op rm: 'a -> ('a,'b) map -> ('a,'b) map.
  axiom get_rm x (m:('a,'b) map) x':
    get (rm x m) x' = if x = x' then None else get m x'.

  lemma nosmt get_rmE (m:('a,'b) map) x:
    get (rm x m) x = None.
  proof strict.
  by rewrite get_rm.
  qed.

  lemma nosmt get_rmN (m:('a,'b) map) x x':
    x <> x' =>
    get (rm x m) x' = get m x'.
  proof strict.
  by rewrite get_rm -rw_neqF; intros=> ->.
  qed.

  lemma dom_rm (m:('a,'b) map) x:
    dom (rm x m) = rm x (dom m).
  proof strict.
  apply set_ext=> x'; rewrite mem_dom get_rm mem_rm;
  case (x = x').
    by intros=> <-.
    by rewrite rw_eq_sym mem_dom=> ->.
  qed.

  lemma size_rm (m:('a,'b) map) x:
    size (rm x m) = if in_dom x m then size m - 1 else size m.
  proof strict.
  rewrite /size dom_rm /in_dom; case (mem x (dom m))=> x_m.
    by rewrite card_rm_in.
    by rewrite card_rm_nin.
  qed.

  lemma nosmt size_rmI (m:('a,'b) map) x:
    in_dom x m =>
    size (rm x m) = size m - 1.
  proof strict.
  by rewrite /in_dom /size dom_rm=> x_m;
     rewrite card_rm_in.
  qed.

  lemma nosmt size_rmN (m:('a,'b) map) x:
    !in_dom x m =>
    size (rm x m) = size m.
  proof strict.
  by rewrite /in_dom /size dom_rm=> x_m;
     rewrite card_rm_nin.
  qed.

  (* find *)
  op find: ('a -> 'b -> bool) -> ('a,'b) map -> 'a option.

  axiom find_nin: forall (p:'a -> 'b -> bool) m,
    (forall x, in_dom x m => !(p x (proj (get m x)))) =>
    find p m = None.

  axiom find_in: forall (p:'a -> 'b -> bool) (m:('a,'b) map),
    (exists x, in_dom x m /\ p x (proj (get m x))) =>
    (exists x, find p m = Some x).

  axiom find_cor: forall (p:'a -> 'b -> bool) m x,
    find p m = Some x =>
    in_dom x m /\ p x (proj (get m x)).

  (* filter *)
  op filter: ('a -> 'b -> bool) -> ('a,'b) map -> ('a,'b) map.

  axiom get_filter f (m:('a,'b) map) x:
    get (filter f m) x = if f x (proj (get m x)) then get m x else None.

  lemma get_filterN f (m:('a,'b) map) x:
    !in_dom x m =>
    get (filter f m) x = get m x.
  proof strict.
  by rewrite get_filter /in_dom mem_dom /= => ->.
  qed.

  lemma dom_filter f (m:('a,'b) map):
    dom (filter f m) = filter (lambda x, f x (proj (get m x))) (dom m).
  proof strict.
  by apply set_ext=> x; rewrite mem_dom get_filter mem_filter mem_dom /=;
     case (f x (proj (get m x))).
  qed.

  lemma dom_filter1 f (m:('a,'b) map):
    dom (filter (lambda x y, f x) m) = filter f (dom m).
  proof strict.
  by cut:= dom_filter (lambda x (y:'b), f x) m; beta=> ->;
     congr=> //; apply Fun.fun_ext.
  qed.

  lemma filter_dom f (m:('a,'b) map) x:
    in_dom x (filter f m) =>
    in_dom x m /\ f x (proj (get m x)).
  proof strict.
  by rewrite /in_dom dom_filter mem_filter.
  qed.

  lemma leq_filter f (m:('a,'b) map):
    filter f m <= m.
  proof strict.
  by rewrite /Core.(<=)=> x x_in_f; rewrite get_filter;
     cut:= filter_dom f m x _; last intros=> [_ ->].
  qed.

  lemma filter_set_true p (m:('a,'b) map) x y:
    p x y =>
    filter p m.[x<-y] = (filter p m).[x<-y].
  proof strict.
  intros=> p_xy; apply map_ext=> a; case (x = a).
    by intros <-; rewrite get_filter !get_setE proj_some p_xy.
    by rewrite -rw_neqF=> neq_x_a; rewrite get_filter !get_setN ?neq_x_a // -get_filter.
  qed.

  lemma filter_set_false p (m:('a,'b) map) x y:
    !p x y =>
    filter p m.[x <- y] = filter p (rm x m).
  proof strict.
  rewrite -rw_neqF=> not_p_xy; apply map_ext=> a; case (x = a).
    by intros=> <-; rewrite !get_filter get_setE proj_some not_p_xy get_rm.
    by rewrite -rw_neqF=> neq_x_a; rewrite !get_filter get_rm get_setN ?neq_x_a.
  qed.

  (* TODO: Prove
       lemma size_filter f m: size (filter f m) <= size m.
     This is simple once we have size_leq. *)

  (* eq_except *)
  op eq_except: ('a,'b) map ->  ('a,'b) map -> 'a -> bool.

  axiom eq_except_def (m1 m2:('a,'b) map) x:
    eq_except m1 m2 x <=>
    forall x', x <> x' => get m1 x' = get m2 x'.

  lemma eq_except_eq (m:('a,'b) map) x:
    eq_except m m x
  by [].

  lemma eq_except_setE (m1 m2:('a,'b) map) x y:
    eq_except m1 m2 x =>
    !in_dom x m1 =>
    get m2 x = Some y =>
    m1.[x <- y] = m2.
  proof strict.
  rewrite eq_except_def=> eqe x_ndom_m1 m2x.
  apply map_ext=> x'; rewrite get_set; case (x = x').
    by intros=> <-; rewrite m2x.
    by apply eqe.
  qed.

(*
  lemma eq_except_ROM (m1 m2:('a,'b) map) x0 x y0 y:
    let m1' = if !in_dom x0 m1 then m1.[x0 <- (x0 = x) ? y0 : y] else m1 in
    let m2' = if !in_dom x0 m2 then m2.[x0 <- y0] else m2 in
    (if in_dom x m1 then m1 = m2 else eq_except m1 m2 x) =>
    get m2 x = Some y0 =>
    (if in_dom x m1 then m1' = m2' else eq_except m1' m2' x).
  proof strict.
  intros=> m1' m2' m1_m2 m2x; split=> dom_x_m1 //=.
    rewrite /m1' /m2'; generalize m1_m2; rewrite dom_x_m1 //= => m1_m2; subst; case (x0 = x)=> //.
    case (in_dom x0 m2)=> dom_x0_m1 //=; generalize m1'; rewrite dom_x0_m1 //=.
*)

  op map: ('b -> 'c) -> ('a,'b) map -> ('a,'c) map.
  axiom get_map (f:'b -> 'c) (m:('a,'b) map) (x:'a):
    get (map f m) x =
      if get m x = None
      then None
      else Some (f (proj (get m x))).

  op mapi: ('a -> 'b -> 'c) -> ('a,'b) map -> ('a,'c) map.
  axiom get_mapi (f:'a -> 'b -> 'c) (m:('a,'b) map) (x:'a):
    get (mapi f m) x =
      if get m x = None
      then None
      else  Some (f x (proj (get m x))).

  (** Miscellaneous higher-order stuff *)
  (* lam and lamo: turning maps into lambdas *)
  op lam (m:('a,'b) map) = lambda x, proj (get m x).
  op lamo (m:('a,'b) map) = lambda x, get m x.

  lemma lamo_map (f:'b -> 'c) (m:('a,'b) map):
    lamo (map f m) = lambda x, (lift f) ((lamo m) x).
  proof strict.
  apply Fun.fun_ext=> x //=.
  rewrite /lamo /lamo get_map; elim/option_ind (get m x)=> //= {x}.
  by intros=> x'; rewrite proj_some.
  qed.
end Core.

theory OptionGet.
  export Core.

  op "_.[_]" (m:('a,'b) map) = get m.
end OptionGet.

theory DefaultGet.
  export Core.

  op "_.[_]" (m:('a,'b) map) x = proj (get m x). (* We can use "proj None<:t>" as default element for type t *)
end DefaultGet.
