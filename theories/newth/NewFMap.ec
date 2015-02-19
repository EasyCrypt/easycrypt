(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Fun Pred Option Pair Int NewList NewFSet.

pragma +implicits.

(** Even more general (to NewList?) **)
lemma uniq_map_uniq (xs : 'a list) (f : 'a -> 'c):
  uniq (map f xs) => uniq xs.
proof.
  elim xs=> //= x xs IH [] x1_notin_fxs /IH -> /=.
  rewrite -not_def=> x_in_xs; move: x1_notin_fxs=> //=. (* This is a weird way of contraposing *)
  by rewrite -has_pred1 has_map hasP; exists x.
qed.

lemma perm_eq_uniq_map (f : 'a -> 'b)  (s1 s2 : 'a list):
  perm_eq s1 s2 => uniq (map f s1) <=> uniq (map f s2).
proof. by move=> /(perm_eq_map f) /perm_eq_uniq ->. qed.

(* TODO: this may be of more general interest and may benefit from a
         move to NewList, or a separate PairList theory. *)
lemma mem_fst_ex_snd (xs : ('a * 'b) list) (x : 'a):
  mem (map fst xs) x <=> (exists y, mem xs (x,y)).
proof.
  rewrite -has_pred1 has_map hasP /preim/fst/pred1; split.
    by move=> [[a b]] /= [x0_in_xs ->>]; exists b.
  by move=> [y] xs_in_xs; exists (x,y).
qed.

lemma mem_snd_ex_fst (xs : ('a * 'b) list) (y : 'b):
  mem (map snd xs) y <=> (exists x, mem xs (x,y)).
proof.
  rewrite -has_pred1 has_map hasP /preim/snd/pred1; split.
    by move=> [[a b]] /= [x0_in_xs ->>]; exists a.
  by move=> [x] xs_in_xs; exists (x,y).
qed.

op reduce_witness (xs : ('a * 'b) list): 'a list * ('a * 'b) list =
  foldl (fun (aout : 'a list * ('a * 'b) list) (kv : 'a * 'b) =>
           if mem aout.`1 kv.`1 then aout else (rcons aout.`1 kv.`1,rcons aout.`2 kv))
        ([],[]) xs.

lemma mem_reduce_witness (xs : ('a * 'b) list):
   mem (reduce_witness xs).`1 = mem (map fst xs).
proof.
  rewrite /reduce_witness -{1}@(revK xs) foldl_rev.
  rewrite -{2}@(cats0 xs).
  cut: [<:'a>] = map fst [<:'a*'b>] by done.
  move: [<:'a>] [<:'a*'b>]; elim xs=> //=.
    by rewrite /rev //= => acc acc'.
  move=> x xs IH a a' H.
  rewrite /rev /= catrevE foldr_cat /= /=.
  case (mem a x.`1).
    rewrite (IH a a' _) // => x1_in_a.
    subst a; apply fun_ext=> x'.
    rewrite in_cons map_cat mem_cat; case (x' = fst x)=> //=.
    by move=> ->; rewrite x1_in_a.
  cut ->:= IH (rcons a x.`1) (rcons a' x) _.
    by rewrite map_rcons -H.
  move=> x1_notin_a; apply fun_ext=> x'.
  rewrite !(in_cons,map_cat,mem_cat,map_rcons,mem_rcons).
  smt. (* Parce que je le vaux bien. *)
qed.

lemma reduce_witness_projs (xs : ('a * 'b) list):
  map fst (reduce_witness xs).`2 = (reduce_witness xs).`1.
proof.
  rewrite /reduce_witness.
  cut: map fst (([<:'a>],[<:'a*'b>]).`2) = ([<:'a>],[<:'a*'b>]).`1 by done.
  elim xs [<:'a>] [<:'a*'b>]=> //= x xs IH a a' a_eq_fa'.
  case (mem a x.`1)=> //=.
    by rewrite (IH a a' a_eq_fa').
  cut -> //:= IH (rcons a x.`1) (rcons a' x) _.
  by rewrite map_rcons a_eq_fa'.
qed.  

op reduce (xs : ('a * 'b) list): ('a * 'b) list =
  (reduce_witness xs).`2.

lemma mem_fst_reduce (xs : ('a * 'b) list):
  mem (map fst (reduce xs)) = mem (map fst xs).
proof.
  rewrite /reduce -@(mem_reduce_witness xs).
  by cut ->:= reduce_witness_projs xs. (* Why not rewrite? BECAUSE IT DOES NOT WORK! :) *)
qed.

lemma uniq_fst_reduce (xs : ('a * 'b) list): uniq (map fst (reduce xs)).
proof.
  admit. (** TODO: Adapt this proof to using reduce **)
qed.

lemma uniq_perm_eq_map (s1 s2 : ('a * 'b) list) (f: 'a * 'b -> 'c):
  uniq (map f s1) =>
  uniq (map f s2) =>
  (forall (x : 'a * 'b), mem s1 x <=> mem s2 x) =>
  perm_eq s1 s2.
proof.
  move=> Us1 Us2 eq12; rewrite /perm_eq allP => x _ /=.
  by rewrite !count_uniq_mem 3:eq12 //; apply @(uniq_map_uniq _ f).
qed.

(* -------------------------------------------------------------------- *)
(* Finite maps are abstractely represented as the quotient by
 * [perm_eq] of lists of pairs without first projection duplicates. *)

type ('a,'b) fmap.

op elems  : ('a,'b) fmap -> ('a * 'b) list.
op oflist : ('a * 'b) list -> ('a,'b) fmap.

axiom elemsK  (m : ('a,'b) fmap): Self.oflist (elems  m) = m.
axiom oflistK (s : ('a * 'b) list): perm_eq (reduce s) (elems (Self.oflist s)).

lemma uniq_keys (m : ('a,'b) fmap): uniq (map fst (elems m)).
proof.
  rewrite -elemsK; move: (elems m) => {m} m.
  apply @(perm_eq_uniq (map fst (reduce m)) _).
    by apply perm_eq_map; apply oflistK.
  by apply uniq_fst_reduce.
qed.

axiom fmap_eq (s1 s2 : ('a,'b) fmap):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)
op map0 ['a,'b] = Self.oflist [<:'a * 'b>]
  axiomatized by map0E.

(* -------------------------------------------------------------------- *)
(* In PairList? *)
op get (xs : ('a * 'b) list) (a : 'a) =
  with xs = "[]"      => None
  with xs = (::) x xs => if a = x.`1
                         then Some x.`2
                         else get xs a.

lemma mem_get_uniq (xs : ('a * 'b) list) (a : 'a) (b : 'b):
  uniq (map fst xs) =>
  mem xs (a,b) <=> get xs a = Some b.
proof.
  (** This feels larger than necessary **)
  elim xs=> //= [[a' b']] xs IH /= [].
  move=> a'_notin_fstxs uniq_xs; split.
    case=> [[-> ->] // | H].
    cut: mem (map fst xs) a
      by rewrite -has_pred1 has_map hasP; exists (a,b).
    move: a'_notin_fstxs; rewrite {2}/fst //=.
    by case (a = a')=> //= [-> -> // | _ _ _]; rewrite -IH.
  case (a = a')=> //= [_ /someI // | ].
  by rewrite -IH.
qed.

lemma get_mem (xs : ('a * 'b) list) (x : 'a):
  get xs x <> None <=> mem xs (x,oget (get xs x)).
proof. by elim xs=> //= [[a b]] xs IH /=; case (x = a). qed.

op "_.[_]" (m : ('a,'b) fmap) (x : 'a) = get (elems m) x
  axiomatized by getE.

lemma mapP (m1 m2 : ('a,'b) fmap):
  (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
  split=> // H; apply fmap_eq; apply uniq_perm_eq;
    first 2 by apply @(uniq_map_uniq _ fst); apply uniq_keys.
  move: H; rewrite getE /= => H [a b].
  by rewrite !mem_get_uniq 1..2:uniq_keys // H.
qed.

(* -------------------------------------------------------------------- *)
op set (xs : ('a * 'b) list) (a : 'a) (b : 'b) =
  with xs = "[]"      => [(a,b)]
  with xs = (::) x xs => if a = x.`1
                         then (a,b)::xs
                         else x::(set xs a b).

op "_.[_<-_]" (m : ('a,'b) fmap) (a : 'a) (b : 'b) =
  Self.oflist (set (elems m) a b)
axiomatized by setE.

(* -------------------------------------------------------------------- *)
op dom (m : ('a,'b) fmap) = NewFSet.oflist (map fst (elems m))
  axiomatized by domE.

lemma in_dom (m: ('a,'b) fmap) (a : 'a):
  mem (dom m) a <=> m.[a] <> None.
proof.
  rewrite domE getE /= mem_oflist.
  split.
    rewrite mem_fst_ex_snd=> [] b.
    by rewrite mem_get_uniq 1:uniq_keys // => ->.
  by rewrite get_mem=> H; rewrite -has_pred1 has_map hasP; exists (a,oget (get (elems m) a)).
qed.

(* -------------------------------------------------------------------- *)
op rng (m : ('a,'b) fmap) = NewFSet.oflist (map snd (elems m))
  axiomatized by rngE.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
  rewrite rngE getE /= mem_oflist.
  split.
    rewrite mem_snd_ex_fst=> [] a.
    by rewrite mem_get_uniq 1:uniq_keys // => a_in_m; exists a.
  by move=> [] a; rewrite -mem_get_uniq 1:uniq_keys // => H; rewrite -has_pred1 has_map hasP; exists (a,b).
qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a,'b) fmap) = card (dom m)
  axiomatized by sizeE.
