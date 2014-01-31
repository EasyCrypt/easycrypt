require import Option.
require import NewFSet.

(* Finite maps are defined fully extensionally *)
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

(* Less-defined than *)
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

(* map0 *)
op map0:('a,'b) map.

axiom map0E x: map0<:'a,'b>.[x] = None.

(* domain *)
op dom: ('a,'b) map -> 'a fset.

axiom in_dom (m:('a,'b) map) x:
  mem (dom m) x <=> m.[x] <> None.

lemma in_dom_map0 x: mem (dom map0<:'a,'b>) x <=> false.
proof. by rewrite in_dom map0E. qed.

lemma dom_map0: dom map0<:'a,'b> = set0.
proof. by rewrite setP=> x; rewrite in_set0 in_dom_map0. qed.

(* range *)
op rng: ('a,'b) map -> 'b fset.

axiom in_rng (m:('a,'b) map) y:
  mem (rng m) y <=> (exists x, m.[x] = Some y).

lemma in_rng_map0 y: mem (rng map0<:'a,'b>) y <=> false.
proof. by rewrite in_rng; split=> //; case => x; rewrite map0E. qed.

lemma rng_map0: rng map0<:'a,'b> = set0.
proof. by rewrite setP=> x; rewrite in_rng_map0 in_set0. qed.

(* set *)
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

(* remove *)
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
