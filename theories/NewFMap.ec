require import Option.
require import Pair.
require import NewFSet.

(*** Finite maps are defined fully extensionally *)
type ('a,'b) map.

op "_.[_]"   : ('a,'b) map -> 'a -> 'b option.

pred (==) (m1 m2:('a,'b) map) = forall x,
  m1.[x] = m2.[x].

lemma eq_refl (m:('a,'b) map): m == m
by [].

lemma eq_trans (m1 m2 m3:('a,'b) map):
  m1 == m2 => m2 == m3 => m1 == m3
by (move=> eq_m1_m2 eq_m2_m3 x; rewrite eq_m1_m2 eq_m2_m3).

lemma eq_symm (m1 m2:('a,'b) map):
  m1 == m2 => m2 == m1
by (move=> eq_m1_m2 x; rewrite eq_m1_m2).

axiom mapP (m1 m2:('a,'b) map):
  m1 = m2 <=> m1 == m2.

(*** "Less-defined-than" partial order *)
pred (<=) (m1 m2:('a,'b) map) = forall x,
  m1.[x] <> None => m1.[x] = m2.[x].

lemma leq_refl (m:('a,'b) map): m <= m
by [].

lemma leq_trans (m1 m2 m3:('a,'b) map):
  m1 <= m2 => m2 <= m3 => m1 <= m3.
proof.
  move=> leq_m1_m2 leq_m2_m3 x; rewrite -neqF=> x_in_m1.
  cut eq_m1_m2:= leq_m1_m2 x _; first by rewrite x_in_m1.
  cut eq_m2_m3:= leq_m2_m3 x _;
    first by apply (absurd true)=> //; rewrite -eq_m1_m2 x_in_m1.
  by rewrite eq_m1_m2 eq_m2_m3.
qed.

lemma leq_asym (m1 m2:('a,'b) map):
  m1 <= m2 => m2 <= m1 => m1 = m2.
proof.
  move=> leq_m1_m2 leq_m2_m1; apply mapP=> x.
  case (m1.[x] <> None)=> [x_nin_m1 | //= x_in_m1].
    by rewrite leq_m1_m2.
    case (m2.[x] <> None)=> [x_nin_m2 | //= -> //].
    by rewrite leq_m2_m1.
qed.

(*** Operators *)
(** map0 *)
op map0:('a,'b) map.

axiom map0E x: map0<:'a,'b>.[x] = None.

(** domain *)
op dom: ('a,'b) map -> 'a fset.

axiom in_dom (m:('a,'b) map) x:
  mem (dom m) x <=> m.[x] <> None.

lemma in_dom_map0 x: mem (dom map0<:'a,'b>) x <=> false.
proof. by rewrite in_dom map0E. qed.

lemma dom_map0: dom map0<:'a,'b> = set0.
proof. by rewrite setP=> x; rewrite in_set0 in_dom_map0. qed.

(** range *)
op rng: ('a,'b) map -> 'b fset.

axiom in_rng (m:('a,'b) map) y:
  mem (rng m) y <=> (exists x, m.[x] = Some y).

lemma in_rng_map0 y: mem (rng map0<:'a,'b>) y <=> false.
proof. by rewrite in_rng; split=> //; case => x; rewrite map0E. qed.

lemma rng_map0: rng map0<:'a,'b> = set0.
proof. by rewrite setP=> x; rewrite in_rng_map0 in_set0. qed.

(** union of maps with disjoint domains *)
op mapU: ('a,'b) map -> ('a,'b) map -> ('a,'b) map.

axiom get_mapU (m1 m2:('a,'b) map) x:
  setI (dom m1) (dom m2) = set0 =>
  (mapU m1 m2).[x] =
    if (mem (dom m1) x) then m1.[x]
                        else m2.[x].

lemma in_dom_mapU (m1 m2:('a,'b) map) x:
  setI (dom m1) (dom m2) = set0 =>
  mem (dom (mapU m1 m2)) x <=> mem (setU (dom m1) (dom m2)) x.
proof.
  intros=> disj_dom; rewrite in_setU !in_dom get_mapU //.
  by case (mem (dom m1) x); rewrite in_dom /= => ->.
qed.

lemma dom_mapU (m1 m2:('a,'b) map):
  setI (dom m1) (dom m2) = set0 =>
  dom (mapU m1 m2) = setU (dom m1) (dom m2).
proof. by intros=> disj_dom; rewrite setP=> x; apply in_dom_mapU. qed.

(** splitting of maps according to a predicate *)
op mapS: ('a,'b) map -> ('a -> 'b -> bool) -> ('a,'b) map * ('a,'b) map.

axiom get_mapSl (m:('a,'b) map) P x:
  (fst (mapS m P)).[x] =
    if omap (P x) m.[x] = Some true then m.[x] else None.

axiom get_mapSr (m:('a,'b) map) P x:
  (snd (mapS m P)).[x] =
    if omap (P x) m.[x] = Some false then m.[x] else None.

lemma get_mapSl_nin (m:('a,'b) map) P x:
  !mem (dom m) x =>
  (fst (mapS m P)).[x] = None.
proof. by rewrite in_dom get_mapSl /= => ->. qed.

lemma get_mapSr_nin (m:('a,'b) map) P x:
  !mem (dom m) x =>
  (snd (mapS m P)).[x] = None.
proof. by rewrite in_dom get_mapSr /= => ->. qed.

lemma get_mapSl_in (m:('a,'b) map) P x:
  mem (dom m) x =>
  (fst (mapS m P)).[x] = if P x (oget m.[x]) = true then m.[x] else None.
proof.
  rewrite in_dom get_mapSl; case (m.[x])=> //= x'; rewrite /oget //=.
  by cut ->: (Some (P x x') = Some true) <=> (P x x' = true) by smt.
qed.

lemma get_mapSr_in (m:('a,'b) map) P x:
  mem (dom m) x =>
  (snd (mapS m P)).[x] = if P x (oget m.[x]) = false then m.[x] else None.
proof.
  rewrite in_dom get_mapSr; case (m.[x])=> //= x'; rewrite /oget //=.
  by cut ->: (Some (P x x') = Some false) <=> (P x x' = false) by smt.
qed.

lemma in_dom_mapSl (m:('a,'b) map) P x:
  mem (dom (fst (mapS m P))) x <=> omap (P x) m.[x] = Some true.
proof. by rewrite in_dom get_mapSl; case (omap (P x) m.[x] = Some true); case (m.[x]). qed.

lemma in_dom_mapSr (m:('a,'b) map) P x:
  mem (dom (snd (mapS m P))) x <=> omap (P x) m.[x] = Some false.
proof. by rewrite in_dom get_mapSr; case (omap (P x) m.[x] = Some false); case (m.[x]). qed.

(* note: we cannot express set-equality versions of these, since P may define an infinite set *)

lemma mapU_mapS (m:('a,'b) map) P:
  mapU (fst (mapS m P)) (snd (mapS m P)) = m.
proof.
  cut disj_dom: setI (dom (fst (mapS m P))) (dom (snd (mapS m P))) = set0
    by (rewrite setP=> x'; rewrite in_setI in_dom_mapSl in_dom_mapSr in_set0;
        case (omap (P x') m.[x'])=> //=; smt).
  rewrite mapP=> x; rewrite get_mapU //.
  rewrite in_dom_mapSl get_mapSl 2:get_mapSr //; case (m.[x])=> //= y.
  by case (P x y)=> //=; cut ->: (Some false = Some true) = false by smt.
qed.

(** set *)
op "_.[_<-_]": ('a,'b) map -> 'a -> 'b -> ('a,'b) map.

axiom get_set (m:('a,'b) map) x y x':
  m.[x <- y].[x'] = if x = x' then Some y else m.[x'].

lemma get_set_eq (m:('a,'b) map) x y:
  m.[x <- y].[x] = Some y
by rewrite get_set.

lemma get_set_neq (m:('a,'b) map) x y x':
  x <> x' =>
  m.[x <- y].[x'] = m.[x']
by rewrite get_set -neqF=> ->.

lemma set_set (m:('a,'b) map) x y x' y':
  m.[x <- y].[x' <- y'] =
    if x = x' then m.[x' <- y']
              else m.[x' <- y'].[x <- y].
proof.
case (x = x')=> [<- | ].
  rewrite mapP=> x0; rewrite (get_set m.[x <- y]) (get_set m x y').
  by case (x = x0)=> //= neq_x_x0; rewrite get_set_neq.
  rewrite -neqF mapP=> neq_x_x' x0; rewrite !get_set.
  by case (x = x0)=> //= <-; rewrite (eq_sym x' x) neq_x_x'.
qed.

lemma set_set_eq y (m:('a,'b) map) x y':
  m.[x <- y].[x <- y'] = m.[x <- y']
by rewrite set_set.

lemma set_set_neq (m:('a,'b) map) x y x' y':
  x <> x' =>
  m.[x <- y].[x' <- y'] = m.[x' <- y'].[x <- y]
by rewrite -neqF set_set=> ->.

lemma in_dom_set (m:('a,'b) map) x y x0:
  mem (dom m.[x <- y]) x0 <=> (x = x0 \/ mem (dom m) x0).
proof. by rewrite !in_dom get_set; case (x = x0). qed.

lemma in_dom_set_eq (m:('a,'b) map) x y: mem (dom m.[x <- y]) x.
proof. by rewrite in_dom_set. qed.

lemma in_dom_set_neq (m:('a,'b) map) x y x0:
  x <> x0 =>
  mem (dom m.[x <- y]) x0 = mem (dom m) x0.
proof. by rewrite -neqF in_dom_set=> ->. qed.

lemma dom_set (m:('a,'b) map) x y: dom m.[x <- y] = setU (set1 x) (dom m).
proof. by rewrite setP=> x0; rewrite in_dom_set in_setU in_set1 (eq_sym x0 x). qed.

lemma rng_set_nin (m:('a,'b) map) x y:
  !mem (dom m) x =>
  rng (m.[x <- y]) = setU (set1 y) (rng m).
proof.
  rewrite in_dom setP /= => x_nin_m y0.
  rewrite in_rng in_setU in_set1 (eq_sym y0 y).
  split=> [[x'] | [y_y0 | ]].
    case (x = x')=> [<- | neq_x_x'].
      by rewrite get_set_eq=> eq_some; left; apply someI.
      by rewrite get_set_neq // in_rng=> mx_y0; right; exists x'.
    by exists x; rewrite get_set_eq y_y0.
    rewrite in_rng=> [x0 mx0_y0]; exists x0.
    rewrite get_set; case (x = x0)=> //=; apply (absurd (x = x0))=> _.
    by rewrite -not_def=> x_x0; generalize x_nin_m; rewrite x_x0 mx0_y0.
qed.

(* todo: interaction of set with splitting and joining *)

(** remove *)
op rm: 'a -> ('a,'b) map -> ('a,'b) map.

axiom get_rm (m:('a,'b) map) x x':
  (rm x m).[x'] = if (x = x') then None else m.[x'].

lemma get_rm_eq (m:('a,'b) map) x:
  (rm x m).[x] = None
by rewrite get_rm.

lemma get_rm_neq (m:('a,'b) map) x x':
  x <> x' =>
  (rm x m).[x'] = m.[x']
by rewrite -neqF get_rm=> ->.

lemma in_dom_rm (m:('a,'b) map) x x':
  mem (dom (rm x m)) x' =
    if (x = x') then false
                else mem (dom m) x'.
proof. by rewrite in_dom get_rm in_dom; case (x = x'). qed.

lemma in_dom_rm_eq (m:('a,'b) map) x:
  mem (dom (rm x m)) x <=> false
by rewrite in_dom_rm.

lemma in_dom_rm_neq (m:('a,'b) map) x x':
  x <> x' =>
  mem (dom (rm x m)) x' = mem (dom m) x'.
proof. by rewrite -neqF in_dom_rm=> ->. qed.

lemma dom_rm (m:('a,'b) map) x:
  dom (rm x m) = setD (dom m) (set1 x).
proof. by rewrite setP=> x0; rewrite in_dom_rm in_setD in_set1 (eq_sym x0 x); case (x = x0). qed.

lemma set_rm (m:('a,'b) map) x y x':
  (rm x' m).[x <- y] =
    if (x = x') then m.[x <- y]
                else rm x' m.[x <- y].
proof.
rewrite mapP=> x0; rewrite fun_if2 !get_set !get_rm; case (x = x').
  by case (x = x0)=> //=; rewrite -neqF=> neq_x_x0 <-; rewrite neq_x_x0.
  case (x = x0)=> //=; rewrite -!neqF (eq_sym x' x0).
    by move=> <- ->; rewrite get_set_eq.
    by rewrite get_set=> ->.
qed.

(* todo: interaction of removal with splitting, joining and setting *)
