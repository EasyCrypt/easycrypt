require        Map_why.
require import Fun.
require        Option.
require        ISet.

(** Definitions and core lemmas *)
type ('a,'b) map = ('a,'b Option.option) Map_why.map.

op empty:('a,'b) map = Map_why.const_ Option.None.
op get (m:('a,'b) map) (x:'a): 'b Option.option = Map_why."_.[_]" m x.
op "_.[_<-_]" (m:('a,'b) map) (x:'a) (y:'b): ('a,'b) map = Map_why."_.[_<-_]" m x (Option.Some y).

theory OptionGet.
  require export Option.
  op "_.[_]" (m:('a,'b) map): 'a -> 'b option = get m.
end OptionGet.
export OptionGet.

pred (==) (m1 m2:('a,'b) map) =
  forall (x:'a), m1.[x] = m2.[x].

lemma map_ext: forall (m1 m2:('a,'b) map),
  m1 == m2 => m1 = m2
by [].

lemma get_setE: forall (m:('a,'b) map) x v,
  m.[x <- v].[x] = Some v
by [].

lemma get_setNE: forall (x:'a) (v:'b) (m:('a,'b) map) y,
  x <> y => m.[x <- v].[y] = m.[y]
by [].

lemma get_set: forall (m:('a,'b) map) x v y,
  (y <> x => m.[y] = Some v) =>
  m.[x <- v].[y] = Some v
by [].

lemma set_setE: forall (m:('a,'b) map) x v w,
  m.[x <- v].[x <- w] = m.[x <- w]
by [].

lemma set_setNE: forall (m:('a,'b) map) x y v w,
  x <> y => m.[x <- v].[y <- w] = m.[y <- w].[x <- v]
by [].

(** Domain *)
op in_dom (x:'a) (m:('a,'b) map) = m.[x] <> None.

op dom:('a,'b) map -> 'a ISet.set.
axiom dom_def: forall (m:('a,'b) map) x,
  ISet.mem x (dom m) <=> in_dom x m.

(* Lemmas *)
lemma dom_empty: dom empty<:'a,'b> = ISet.empty<:'a>.
proof strict.
by apply ISet.set_ext; smt.
qed.

lemma nosmt in_dom_setE: forall (x:'a) (m:('a,'b) map) v,
  in_dom x m.[x <- v]
by [].

lemma nosmt in_dom_setNE: forall (x:'a) (m:('a,'b) map) y v,
  x <> y =>
  in_dom x m.[y <- v] = in_dom x m
by [].

lemma in_dom_set: forall (x:'a) (m:('a,'b) map) y v,
  in_dom x m.[y <- v] = (in_dom x m \/ x = y) by [].

lemma in_dom_empty: forall x, !(in_dom x empty<:'a,'b>) by [].

lemma dom_set: forall (m:('a,'b) map) x v,
  dom m.[x <- v] = ISet.add x (dom m).
proof strict.
intros=> m x v;
apply ISet.set_ext; delta ISet.(==); beta=> x'.
rewrite ISet.mem_add 2!dom_def.
case (x' = x) => x_x'; last by rewrite in_dom_setNE.
  by subst x'; split => _; [trivial | apply in_dom_setE].
qed.

(** Range *)
op rng: ('a,'b) map -> 'b ISet.set.
axiom rng_def: forall (m:('a,'b) map) v,
  ISet.mem v (rng m) <=> (exists x, m.[x] = Some v).

op in_rng (x:'b) (m:('a,'b) map) = ISet.mem x (rng m).

(* Lemmas *)
lemma in_rng_setE: forall (m:('a,'b) map) x v, in_rng v m.[x <- v] by [].

lemma rng_empty: rng empty<:'a,'b> = ISet.empty.
proof strict.
by apply ISet.set_ext; delta ISet.(==); beta=> v;
   rewrite rng_def; smt.
qed.

lemma in_rng_empty: forall (v:'b), !(in_rng v empty<:'a,'b>) by [].

lemma nin_dom_rng_set: forall (x:'a) m (v:'b),
  !(in_dom x m) =>
  rng (m.[x <- v]) = ISet.add v (rng m).
proof strict.
intros=> x m v x_in_dom_m.
apply ISet.set_ext; delta ISet.(==); beta=> v'.
rewrite ISet.mem_add rng_def; split=> in_rng; first smt.
  elim in_rng; clear in_rng; rewrite 1?rng_def=> in_rng; last smt.
  elim in_rng; clear in_rng => x0 in_rng; exists x0; smt.
qed.

lemma in_rng_setNE_in_rng: forall (v:'b) (m:('a,'b) map) x v',
  v <> v' =>
  in_rng v m.[x <- v'] =>
  in_rng v m.
proof strict.
intros=> v m x v' v_neq_v';
delta in_rng beta; rewrite 2!rng_def=> v_in_rng_set;
elim v_in_rng_set=> {v_in_rng_set} x' get_set;
cut x_neq_x':x' <> x.
  generalize get_set; apply absurd; simplify=> x_x'; subst x'; rewrite get_setE; smt. (* TODO: Injectivity lemma *)
  generalize get_set; rewrite get_setNE; first smt.
    intros=> m_x'_v; exists x'=> //.
qed.

lemma in_rng_setNE: forall (v:'b) (m:('a,'b) map) x v',
  in_rng v m =>
  (!in_dom x m \/ m.[x] <> Some v) =>
  in_rng v m.[x <- v'].
proof strict.
delta in_rng beta=> v m x v';
rewrite 2!rng_def=> v_in_rng_m in_dom_or_neq;
elim v_in_rng_m=> x' m_x'_some; exists x'; rewrite get_setNE //; smt.
qed.

(** General lemmas on rng and dom *)
lemma onto_rng: forall (m:('a,'b) map) v,
  in_rng v m => exists x, in_dom x m /\ m.[x] = Some v
by [].

lemma map_fun: forall (m:('a,'b) map) x,
  in_dom x m => exists v, in_rng v m /\ m.[x] = Some v.
proof strict.
delta in_dom beta;
intros=> m x x_in_m; exists (proj m.[x]); split; last smt.
  delta in_rng beta; rewrite rng_def; exists x; smt.
qed.

(** find *)
op find: ('a -> 'b cpred) -> ('a,'b) map -> 'a option.

axiom find_nin: forall (p:'a -> 'b cpred) m,
  (forall x, in_dom x m => !(p x (proj m.[x]))) =>
  find p m = None.

axiom find_in: forall (p:'a -> 'b cpred) (m:('a,'b) map),
  (exists x, in_dom x m /\ p x (proj m.[x])) =>
  (exists x, find p m = Some x).

axiom find_cor: forall (p:'a -> 'b cpred) m x,
  find p m = Some x =>
  in_dom x m /\ p x (proj m.[x]).

(* Lemmas *)
lemma find_none: forall (p:'a -> 'b cpred) m,
  find p m = None <=>
  (forall x, in_dom x m => !(p x (proj m.[x])))
by [].

lemma find_some: forall (p:'a -> 'b cpred) m,
  (exists x, find p m = Some x) <=>
  (exists x, in_dom x m /\ p x (proj m.[x]))
by [].

lemma find_empty: forall (p:'a -> 'b cpred),
  find p empty = None
by [].

(** rm *)
op rm (x:'a) (m:('a,'b) map) = Map_why."_.[_<-_]" m x None.

(* Lemmas *)
lemma rm_nin_dom: forall (x:'a) (m:('a,'b) map),
  !(in_dom x (rm x m))
by [].

lemma rm_set: forall (x:'a) (m:('a,'b) map),
  !(in_dom x m) => rm x m = m
by [].

lemma dom_rm: forall x (m:('a,'b) map),
  dom (rm x m) = ISet.rm x (dom m).
proof strict.
intros=> x m; apply ISet.set_ext;
delta ISet.(==); beta=> x0; split; last smt.
case (x0 = x)=> x0_x.
  subst x0; apply absurd=> nconcl; rewrite dom_def; apply rm_nin_dom.

  case (ISet.mem x (dom m)); last smt.
    rewrite dom_def ISet.mem_rm_neq //; smt.
qed.

lemma in_dom_rm: forall x y (m:('a,'b) map),
  in_dom x (rm y m) = (in_dom x m /\ !x = y).
intros=> x y m; rewrite -2!dom_def; case (x = y)=> x_y.
  by subst y; simplify; rewrite dom_rm; (cut h: !ISet.mem x (ISet.rm x (dom m));
       first apply ISet.mem_rm_eq);
       smt.
  by simplify; simplify; rewrite dom_rm; rewrite ISet.mem_rm_neq.
qed.

(** eq_except*)
pred eq_except (m1 m2:('a,'b) map) x =
  forall y, x <> y => m1.[y] = m2.[y].

(* Lemmas *)
lemma eqe_refl: forall (m:('a,'b) map) x,
  eq_except m m x
by [].

lemma eqe_symm: forall (m1 m2:('a,'b) map) x,
  eq_except m1 m2 x => eq_except m2 m1 x
by [].

lemma eqe_trans: forall (m1 m2 m3:('a,'b) map) x,
  eq_except m1 m2 x => eq_except m2 m3 x => eq_except m1 m3 x
by [].

lemma eqe_set: forall (m1 m2:('a,'b) map) x x' y,
  eq_except m1 m2 x =>
  eq_except m1.[x' <- y] m2.[x' <- y] x
by [].

lemma eqe_eq: forall (m1 m2:('a,'b) map) x,
  eq_except m1 m2 x =>
  m1.[x] <> None =>
  m1 = m2.[x <- proj m1.[x]].
proof strict.
intros=> m1 m2 x eqe m1_x_nnone;
apply map_ext; delta (==) beta=> x';
cut m1_x_some: exists z, m1.[x] = Some z.
  generalize m1_x_nnone; apply absurd; simplify; smt.
elim m1_x_some=> {m1_x_some} z m1_x_some; rewrite m1_x_some proj_some; smt.
qed.

(** disj *)
pred disj (m1 m2:('a,'b) map) =
  forall x, !in_dom x m1 \/ !in_dom x m2.

lemma disjC: forall (m1 m2:('a,'b) map),
  disj m1 m2 <=> disj m2 m1
by [].

lemma disj0m: forall (m:('a,'b) map),
  disj empty m
by [].

lemma disj_set: forall (m1 m2:('a,'b) map) x v,
  disj m1 m2 =>
  !in_dom x m2 =>
  disj m1.[x <- v] m2
by [].

lemma disj_rm: forall (m1 m2:('a,'b) map) x,
  disj m1 m2 =>
  disj (rm x m1) m2
by [].

(** split *)
pred splitm(m m1 m2:('a,'b) map) =
  disj m1 m2 /\
  (forall x, in_dom x m <=> (in_dom x m1 \/ in_dom x m2)) /\
  (forall x, in_dom x m1 => m.[x] = m1.[x]) /\
  (forall x, in_dom x m2 => m.[x] = m2.[x]).

lemma splitm_empty: forall (m:('a,'b) map),
  splitm m m empty
by [].

lemma splitmC: forall (m m1 m2:('a,'b) map),
  splitm m m1 m2 <=> splitm m m2 m1
by [].

lemma splitm_set: forall (m m1 m2:('a,'b) map) x v,
  splitm m m1 m2 =>
  !in_dom x m2 =>
  splitm m.[x <- v] m1.[x <- v] m2.
proof strict.
by intros=> m m1 m2 x v splitm_m x_nin_m2; delta splitm beta;
   progress; smt.
qed.

lemma splitm_rm: forall (m m1 m2:('a,'b) map) x,
  splitm m m1 m2 =>
  !in_dom x m2 =>
  splitm (rm x m) (rm x m1) m2.
proof strict.
intros=> m m1 m2 x splitm_m x_nin_m2; rewrite /splitm;
progress; first 2 smt.
  by elim splitm_m=> disj {disj} [doms _]; rewrite in_dom_rm doms; smt.
  smt.
  smt.
qed.

(** pre *)
pred pre (p:'a -> bool) (m:('a,'b) map) =
  forall x, in_dom x m => p x.

(** post *)
pred post (p:'b -> bool) (m:('a,'b) map) =
  forall x, in_dom x m => p (proj m.[x]).

lemma post_rng: forall p (m:('a,'b) map),
  post p m <=> forall v, in_rng v m => p v.
proof strict.
intros=> p m; split; smt.
qed.
