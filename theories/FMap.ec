require import Int.
require import Option.
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

  (* TODO: Prove
       lemma size_filter f m: size (filter f m) <= size m.
     This is simple once we have size_leq. *)
end Core.

theory OptionGet.
  export Core.

  op "_.[_]" (m:('a,'b) map) = get m.
end OptionGet.

theory DefaultGet.
  export Core.

  op "_.[_]" (m:('a,'b) map) x = proj (get m x). (* We can use "proj None<:t>" as default element for type t *)
end DefaultGet.

