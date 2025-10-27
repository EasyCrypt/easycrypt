require import Core Int List StdRing StdOrder FMap FSet StdBigop.
(*---*) import IntOrder.


(* -------------------------------------------------------------------- *)
(* Finite multisets are represented as lists up to permutation          *)

type 'a mset.

op elems  : 'a mset -> 'a list.
op oflist : 'a list -> 'a mset.

axiom elemsK: cancel elems<:'a> oflist.
axiom oflistK (s : 'a list): perm_eq s (elems (oflist s)).

axiom mset_eq (s1 s2 : 'a mset):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)

lemma perm_eq_oflistP (s1 s2 : 'a list) :
  oflist s1 = oflist s2 <=> perm_eq s1 s2.
proof.
split. 
- move=> oflist_eq; rewrite (perm_eq_trans _ _ _ (oflistK s1)) oflist_eq.
  by rewrite perm_eq_sym oflistK.
move=> peq_s1s2; apply/mset_eq.
apply (perm_eq_trans s1 _ _); 1: rewrite perm_eq_sym oflistK.
rewrite (perm_eq_trans s2 _ _ peq_s1s2) oflistK.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] mult ['a]  (x: 'a) (s: 'a mset): int = count (pred1 x) (elems s).

abbrev "_.[_]" (s: 'a mset) (x: 'a) = mult x s.

lemma oflist_mult (s : 'a list):
  forall x, (oflist s).[x] = count (pred1 x) s.
proof. move => x; rewrite/mult; apply/perm_eqP/perm_eq_sym/oflistK. qed.

lemma mult_ge0 s (x: 'a): 0 <= s.[x] by rewrite/mult; apply count_ge0.

hint exact : mult_ge0.

lemma mset_eqP (s1 s2 : 'a mset):
  (forall x, s1.[x] = s2.[x]) => s1 = s2.
proof.
move=> h; apply/mset_eq.
rewrite/mult in h.
by rewrite perm_eqP_pred1.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] mem ['a] (s : 'a mset) (x : 'a) = mem (elems s) x.
lemma memE (s : 's mset) x: mem s x = mem (elems s) x by rewrite /mem.

abbrev (\in)    (z : 'a) (s : 'a mset) =  mem s z.
abbrev (\notin) (z : 'a) (s : 'a mset) = !mem s z.

lemma mult_in_ge1 s (x: 'a): x \in s <=> 1 <= mult x s. 
proof. rewrite /mult; have := mem_count x (elems s); rewrite -memE /#. qed.

lemma mult0 s (x: 'a): x \notin s <=> mult x s = 0 by smt(mult_ge0 mult_in_ge1).

lemma mem_oflist (s : 'a list):
  forall x, x \in (oflist s) <=> x \in s.
proof.
move=> x; rewrite !memE (perm_eq_mem _ s) //.
by rewrite perm_eq_sym oflistK.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] selems (s: 'a mset): 'a fset = oflist (elems s).

lemma mem_selems s (e: 'a): e \in selems s <=> e \in s.
proof. by rewrite /selems mem_oflist memE. qed.

op [opaque] offset (s: 'a fset): 'a mset = oflist (elems s).

lemma offset_mult (s: 'a fset) x: (offset s).[x] = b2i (x \in s).
proof. 
rewrite /mult /offset.
have/perm_eqP_pred1<-:= (oflistK (elems s)).
by rewrite count_uniq_mem ?uniq_elems /mem.
qed.

(* -------------------------------------------------------------------- *)

op [opaque] tofmap (s: 'a mset): ('a, int) fmap = offsetmap (fun e => s.[e]) (selems s).

lemma tofmap_get (s: 'a mset) e: (tofmap s).[e] = if e \in s then Some(s.[e]) else None.
proof.
rewrite /tofmap.
case (e \in s) => e_in.
- by rewrite offsetmapT 1:mem_selems.
by rewrite offsetmapN 1:mem_selems.
qed.

op [opaque] offmap (m: ('a, int) fmap): 'a mset = 
  oflist (flatten (FSet.elems (FMap.frng (FMap.map (fun (a: 'a) (n: int) => nseq n a) m)))).

lemma mem_tofmap (s: 'a mset) e: e \in tofmap s <=> e \in s.
proof. by rewrite /tofmap /= mem_offsetmap mem_selems. qed.

lemma offmap_mult (m: ('a, int) fmap) e: (offmap m).[e] = 
  max 0 (odflt 0 m.[e]).
proof.
rewrite /offmap oflist_mult count_flatten StdBigop.Bigint.sumzE.
rewrite StdBigop.Bigint.BIA.big_mapT /(\o).
pose l:= (frng (map (fun (a : 'a) (n : int) => nseq n a) m)).
have lP: forall il, il \in l <=> exists a, a \in m /\ il = nseq (oget m.[a]) a.
- rewrite /l => il; rewrite mem_frng /rng. 
  apply exists_iff => x /=.
  rewrite mapE /=.
  pose opt_n:= m.[x].
  have: opt_n = m.[x] by done.
  rewrite /dom.
  case (opt_n) => [/= /eq_sym -> //|n <- //=].
move: m l lP; apply fmapW => /= [l lP|m k v k_in IH l lP].
- have ->: l = fset0.
  + apply in_eq_fset0 => il.
    rewrite -negP => /lP [k].
    by rewrite mem_empty.
  rewrite emptyE /= maxrE /= elems_fset0 /=.
  exact StdBigop.Bigint.BIA.big_nil.
rewrite mem_fdom /dom /= in k_in.
case (exists a, a \in m /\ nseq (oget m.[a]) a = nseq v k) => 
  [[x [x_in eq_nseq]]| /negb_exists /= neq_nseq].
- have := IH l => IH'; clear IH.
  have := nseq_eq _ _ _ _ eq_nseq.
  have x_neq : x <> k.
  + rewrite -negP => x_eq; subst x.
    by rewrite /dom k_in in x_in.
  rewrite x_neq /= => [[mx_le0 v_le0]].
  rewrite IH' => [il|]; first last. 
  + case (e = k) => e_eq; 2: by rewrite get_set_neqE.    
    subst e; rewrite get_set_sameE k_in /= lez_maxl // lez_maxl //.
  rewrite lP.
  split => [[a [/mem_set [a_in|->] ->]]|[a [a_in ->]]].
  + exists a; rewrite a_in /= get_set_neqE //.
    by rewrite -negP=> ->>; move: a_in; rewrite domE k_in.
  + by exists x; rewrite x_in /= get_set_sameE eq_nseq.
  have a_neq: a <> k.
  + rewrite -negP => a_eq; subst a.
    by rewrite /dom k_in in a_in.
  by exists a; rewrite get_set_neqE // mem_set a_in.
have nseq_in: nseq v k \in l by rewrite lP; exists k; rewrite get_set_sameE mem_set.
have perm:= FSet.perm_to_rem _ _ nseq_in.
rewrite (StdBigop.Bigint.BIA.eq_big_perm _ _ _ _ perm) StdBigop.Bigint.BIA.big_consT.
rewrite count_nseq {1}/pred1.
case (k = e) => /= e_eq; 1:subst e.
- rewrite get_set_sameE /=.
  rewrite StdBigop.Bigint.BIA.big1_seq; 2:by exact addz0.
  rewrite /predT => il /=.
  rewrite -memE in_fsetD1 => [[/lP [x [/mem_set [x_in|->] ->]]]]; 
    rewrite count_nseq {1}/pred1 /=.
  + by have -> /=: x <> k by rewrite -negP => x_eq; subst x; rewrite /dom k_in in x_in.
  by rewrite get_set_sameE /=.    
rewrite get_set_neqE eq_sym // IH // => il.
rewrite in_fsetD lP exists_andr.
apply exists_iff => x /=.
rewrite mem_set in_fset1.
case (x = k) => [-> /=| /= x_neq].
* by rewrite /dom k_in get_set_sameE /= andbN.
rewrite get_set_neqE //.
split => [->//|[x_in ->]].
rewrite x_in /=.
have := neq_nseq x.
by rewrite x_in.
qed.

lemma tofmapK: cancel tofmap<:'a> offmap.
proof. 
move => s; apply mset_eqP => y.
rewrite offmap_mult tofmap_get.
case (y \in s) => y_in; rewrite lez_maxr //.
by rewrite eq_sym; apply mult0.
qed.

lemma offmapK (x: ('a, int) fmap): 
  (forall e, e \in x => 1 <= oget x.[e]) => tofmap (offmap x) = x.
proof.
move => H; apply fmap_eqP => e.
rewrite tofmap_get mult_in_ge1 offmap_mult.
case (e \in x) => [/H /#|].
rewrite /dom /= => -> /=.
by rewrite lez_maxr.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] mset0 ['a] = oflist [<:'a>].

lemma mset0_mult (e: 'a): mset0.[e] = 0.
proof. by rewrite /mset0 oflist_mult. qed.

op [opaque] mset1 ['a] (z : 'a) = oflist [z].

lemma mset1_mult (x y: 'a): (mset1 x).[y] = b2i (x = y).
proof. by rewrite /mset1 oflist_mult /= /pred1. qed.

op [opaque] add ['a] (s1 s2 : 'a mset) = oflist (elems s1 ++ elems s2).

abbrev (+) ['a] = add<:'a>.

lemma add_mult (s1 s2: 'a mset) e: (s1 + s2).[e] = s1.[e] + s2.[e].
proof. by rewrite /add oflist_mult count_cat /mult. qed.

op [opaque] union ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m \/ is_some n then Some (max (odflt 0 m) (odflt 0 n)) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`|`) ['a] = union<:'a>.

lemma union_mult (s1 s2: 'a mset) e: (s1 `|` s2).[e] = max s1.[e] s2.[e].
proof. rewrite /union offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op [opaque] intersection ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m /\ is_some n then Some (min (odflt 0 m) (odflt 0 n)) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`&`) ['a] = intersection<:'a>.

lemma intersection_mult (s1 s2: 'a mset) e: (s1 `&` s2).[e] = min s1.[e] s2.[e].
proof. rewrite /intersection offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op [opaque] diff ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m then Some (odflt 0 m - odflt 0 n) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`\`) ['a] = diff<:'a>.

lemma diff_mult (s1 s2: 'a mset) e: (s1 `\` s2).[e] = max 0 (s1.[e] - s2.[e]).
proof. rewrite /diff offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op rem ['a] (s : 'a mset) x = s `\` mset1 x.

lemma rem_mult s (x y: 'a): (rem s x).[y] = max 0 (s.[y] - b2i (x = y)).
proof. by rewrite diff_mult mset1_mult. qed.

op insert ['a] x (s : 'a mset) = s + mset1 x.

lemma insert_mult s (x y: 'a): (insert x s).[y] = s.[y] + b2i (x = y).
proof. by rewrite add_mult mset1_mult. qed.

(* -------------------------------------------------------------------- *)

lemma elems_mset0 ['a]: elems mset0 = [<:'a>].
proof. 
rewrite /mset0; apply/perm_eq_small/perm_eq_sym => //=.
rewrite -{1}(undup_id []) // oflistK //.
qed.

lemma elems_eq_mset0 ['a] (A : 'a mset): elems A = [<:'a>] => A = mset0.
proof.
move=> elems_nil; apply/mset_eqP=> x. 
by rewrite mset0_mult -mult0 /mem elems_nil.
qed.

lemma elems_mset1 (x : 'a) : elems (mset1 x) = [x].
proof.
rewrite /mset1; apply/perm_eq_small/perm_eq_sym=> //=.
by rewrite -{1}(undup_id [x]) ?oflistK.
qed.

(* -------------------------------------------------------------------- *)

hint rewrite multE : mset0_mult mset1_mult add_mult union_mult  
  intersection_mult diff_mult.

lemma oflist_cons ['a] (x : 'a) s : oflist (x::s) = insert x (oflist s).
proof. 
apply mset_eqP => z.
rewrite oflist_mult /= !multE /mult {1}/pred1 addzC.
congr; apply perm_eqP_pred1.
exact oflistK.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] pick ['a] (A : 'a mset) = head witness (elems A).

lemma pick0: pick<:'a> mset0 = witness.
proof. by rewrite /pick elems_mset0. qed.

lemma mem_pick (A : 'a mset): A <> mset0 => pick A \in A.
proof.
move=> /(contra _ _ (elems_eq_mset0 A)); rewrite /pick memE.
by move=> /(mem_head_behead witness) <-.
qed.

(* -------------------------------------------------------------------- *)
op (\subset) (s1 s2 : 'a mset) = forall x, s1 .[x] <= s2.[x].
op (\proper) (s1 s2 : 'a mset) = s1 \subset s2 /\ s1 <> s2.

lemma diff_mult_subset (s1 s2 : 'a mset): s2 \subset s1 => 
  forall x, (s1 `\` s2).[x] = s1.[x] - s2.[x].
proof. move => s1_sub_s2 x; rewrite diff_mult => /#. qed.

lemma subset_trans (s1 s2 s3 : 'a mset): 
  s1 \subset s2 => s2 \subset s3 => s1 \subset s3.
proof. move=> le1 le2 x; exact (lez_trans _ _ _ (le1 x) (le2 x)). qed.

lemma properP (s1 s2 : 'a mset) :
  s1 \proper s2 <=> s1 \subset s2 /\ exists x, s1.[x] < s2.[x].
proof.
rewrite /(\proper) &(andb_id2l)=> s1_sub_s2.
have->:(s1<>s2 <=> exists x, s1.[x] <> s2.[x]) by smt(mset_eqP).
apply/eqboolP/exists_eq => x /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma eqEsubset (s1 s2 : 'a mset) : 
  (s1 = s2) <=> (s1 \subset s2) /\ (s2 \subset s1).
proof.
split=> // - [] s1_sub_s2 s2_sub_s1.
by apply: mset_eqP=> /#.
qed.

lemma subset_msetU_id (A B : 'a mset) :
  A \subset B => A `|` B = B.
proof. move=> A_le_B; apply/mset_eqP=> x; rewrite union_mult /#. qed.

lemma subset_msetI_id (A B : 'a mset) :
  B \subset A => A `&` B = B.
proof. move=> A_le_B; apply/mset_eqP=> x; rewrite intersection_mult /#. qed.

lemma subset_mset_add (A B : 'a mset) : A \subset A + B.
proof. rewrite /(\subset) => x; rewrite !multE; smt(mult_ge0). qed.

lemma subset_msetDadd (A B : 'a mset) : A \subset B => (B `\` A) + A = B.
proof. 
move => /diff_mult_subset H; apply mset_eqP => x.
rewrite multE H /#.
qed.

(* -------------------------------------------------------------------- *)
lemma mset_ind (p : 'a mset -> bool):
  p mset0 =>
  (forall x s, p s => p (insert x s)) =>
  (forall s, p s).
proof.
move=> p0 pa s; rewrite -elemsK.
elim (elems s)=> {s} [|x s ih].
- by rewrite -/mset0.
rewrite oflist_cons.
by apply pa.
qed.

(* ------------------------------------------------------------------ *)
lemma addsC (A B : 'a mset) : A + B = B + A.
proof. by apply/mset_eqP => x; rewrite !multE addzC. qed.

lemma add0s (A : 'a mset) : mset0 + A = A.
proof. by apply/mset_eqP => x; rewrite !multE. qed.

lemma adds0 (A : 'a mset) : A + mset0 = A.
proof. by apply/mset_eqP => x; rewrite !multE. qed.

lemma addsA (A B C : 'a mset) : A + (B + C) = A + B + C.
proof. by apply/mset_eqP => x; rewrite !multE addzA. qed.

lemma addsCA (A B C : 'a mset) : A + (B + C) = B + (A + C).
proof. by rewrite !addsA (addsC B). qed.

lemma addsAC (A B C : 'a mset) : A + B + C = A + C + B.
proof. by rewrite -!addsA (addsC B). qed.

lemma addsUACA (A B C D : 'a mset) : (A + B) + (C + D) = (A + C) + (B + D).
proof. by rewrite -!addsA (addsCA B). qed.

(* ------------------------------------------------------------------ *)
lemma msetUC (A B : 'a mset) : A `|` B = B `|` A.
proof. by apply/mset_eqP => x; rewrite !multE maxrC. qed.

lemma mset0U (A : 'a mset) : mset0 `|` A = A.
proof. by apply/mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

lemma msetU0 (A : 'a mset) : A `|` mset0 = A.
proof. by apply/mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

lemma msetUA (A B C : 'a mset) : A `|` (B `|` C) = A `|` B `|` C.
proof. by apply/mset_eqP => x; rewrite !multE maxrA. qed.

lemma msetUCA (A B C : 'a mset) : A `|` (B `|` C) = B `|` (A `|` C).
proof. by rewrite !msetUA (msetUC B). qed.

lemma msetUAC (A B C : 'a mset) : A `|` B `|` C = A `|` C `|` B.
proof. by rewrite -!msetUA (msetUC B). qed.

lemma msetUACA (A B C D : 'a mset) : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
proof. by rewrite -!msetUA (msetUCA B). qed.

lemma msetUid (A : 'a mset) : A `|` A = A.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetUUl (A B C : 'a mset) : A `|` B `|` C = (A `|` C) `|` (B `|` C).
proof. by rewrite msetUA (msetUAC _ C) -(msetUA _ C) msetUid. qed.

lemma msetUUr (A B C : 'a mset) : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
proof. by rewrite !(msetUC A) msetUUl. qed.

(* ------------------------------------------------------------------ *)
lemma msetIC (A B : 'a mset) : A `&` B = B `&` A.
proof. by apply/mset_eqP => x; rewrite !multE minrC. qed.

lemma mset0I (A : 'a mset) : mset0 `&` A = mset0.
proof. by apply/mset_eqP => x; rewrite !multE lez_minl. qed.

lemma msetI0 (A : 'a mset) : A `&` mset0 = mset0.
proof. by rewrite msetIC mset0I. qed.

lemma mset1I (x : 'a) (D : 'a mset):
  mset1 x `&` D = if x \in D then mset1 x else mset0.
proof.
apply/mset_eqP=> y; rewrite (fun_if2 "_.[_]") /= !multE mult_in_ge1.
smt(mult_ge0).
qed.

lemma msetI1 (x : 'a) (D : 'a mset):
  D `&` mset1 x = if x \in D then mset1 x else mset0.
proof. by rewrite msetIC mset1I. qed.

lemma msetIA (A B C : 'a mset) : A `&` (B `&` C) = A `&` B `&` C.
proof. by apply/mset_eqP=> x; rewrite !multE minrA. qed.

lemma msetICA (A B C : 'a mset) : A `&` (B `&` C) = B `&` (A `&` C).
proof. by rewrite !msetIA (msetIC A). qed.

lemma msetIAC (A B C : 'a mset) : A `&` B `&` C = A `&` C `&` B.
proof. by rewrite -!msetIA (msetIC B). qed.

lemma msetIACA (A B C D : 'a mset) : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
proof. by rewrite -!msetIA (msetICA B). qed.

lemma msetIid (A : 'a mset) : A `&` A = A.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetIIl (A B C : 'a mset) : A `&` B `&` C = (A `&` C) `&` (B `&` C).
proof. by rewrite msetIA (msetIAC _ C) -(msetIA _ C) msetIid. qed.

lemma msetIIr (A B C : 'a mset) : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
proof. by rewrite !(msetIC A) msetIIl. qed.

(* ------------------------------------------------------------------ *)
lemma msetIUr (A B C : 'a mset) : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetIUl (A B C : 'a mset) : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUIr (A B C : 'a mset) : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUIl (A B C : 'a mset) : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUK (A B : 'a mset) : (A `|` B) `&` A = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetKU (A B : 'a mset) : A `&` (B `|` A) = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetIK (A B : 'a mset) : (A `&` B) `|` A = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetKI (A B : 'a mset) : A `|` (B `&` A) = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

(* ------------------------------------------------------------------ *)
lemma msetaddUI (A B: 'a mset) : A + B = (A `|` B) + (A `&` B).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

(* ------------------------------------------------------------------ *)
lemma msetD0 (A : 'a mset) : A `\` mset0 = A.
proof. by apply/mset_eqP=> x; rewrite !multE /= ler_maxr. qed.

lemma mset0D (A : 'a mset) : mset0 `\` A = mset0.
proof. apply/mset_eqP=> x; rewrite !multE /=; smt(mult_ge0). qed.

lemma mset1D (x : 'a) (D : 'a mset):
  mset1 x `\` D = if mem D x then mset0 else mset1 x.
proof.
apply/mset_eqP=> y; rewrite (fun_if2 "_.[_]") !multE /= !multE mult_in_ge1.
smt(mult_ge0).
qed.

lemma msetDv (A : 'a mset) : A `\` A = mset0.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetaddD (A B : 'a mset) : (A + B) `\` A = B.
proof. apply mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

lemma msetID (A B : 'a mset) : (A `&` B) + (A `\` B) = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDUl (A B C : 'a mset) : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDUr (A B C : 'a mset) : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDIl (A B C : 'a mset) : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDIr (A B C : 'a mset) : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDDl (A B C : 'a mset) : (A `\` B) `\` C = A `\` (B + C).
proof. apply/mset_eqP=> x; rewrite !multE; smt(mult_ge0). qed.

lemma msetDK (A B : 'a mset) : (A `|` B) `\` B = A `\` B.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDKv (A B : 'a mset) : (A `&` B) `\` B = mset0.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

(* -------------------------------------------------------------------- *)
lemma subsetIl (A B : 'a mset) : (A `&` B) \subset A.
proof. rewrite /(\subset) => x; rewrite multE /#. qed.

lemma subsetIr (A B : 'a mset) : (A `&` B) \subset B.
proof. rewrite /(\subset) => x; rewrite multE /#. qed.

(* -------------------------------------------------------------------- *)
lemma subsetDl (A B : 'a mset) : A `\` B \subset A.
proof. rewrite /(\subset) => x; rewrite multE; smt(mult_ge0). qed.

(* -------------------------------------------------------------------- *)
lemma sub0set (A : 'a mset) : mset0 \subset A.
proof. rewrite /(\subset) => x; rewrite multE mult_ge0. qed.

lemma sub1set x (A : 'a mset) : mset1 x \subset A <=> x \in A.
proof.
rewrite mult_in_ge1 /(\subset) -b2i1 (eq_imp (x = x) true) // -(mset1_mult x).
split => [->//|H y].
case (x = y) => [//|].
by rewrite mset1_mult => ->.
qed.

(* -------------------------------------------------------------------- *)
abbrev disjoint (xs ys : 'a mset) = xs `&` ys = mset0.

lemma disjointC (xs ys : 'a mset): disjoint xs ys => disjoint ys xs.
proof. by rewrite msetIC. qed.

lemma disjointP (xs ys : 'a mset):
  disjoint xs ys <=> forall (x : 'a), x \in xs => ! x \in ys.
proof.
split=> [disj_xs_ys x /mult_in_ge1 x_in_xs | all_xs_not_in_ys].
- suff: ys.[x] = 0 by rewrite mult_in_ge1 => ->.
  have /#:0 = min xs.[x] ys.[x] by rewrite -(mset0_mult x) -disj_xs_ys multE.
apply mset_eqP => x.
have := all_xs_not_in_ys x.
rewrite !multE !mult_in_ge1.
smt(mult_ge0).
qed.

(* -------------------------------------------------------------------- *)
op [opaque] card ['a] (s : 'a mset) = size (elems s). 

lemma card_oflist (l: 'a list): card (oflist l) = size l.
proof. by rewrite /card; have/perm_eq_size->:= oflistK l. qed.

lemma mcards0: card mset0<:'a> = 0.
proof. by rewrite /card elems_mset0. qed.

lemma eq_mcards0 (A : 'a mset): A = mset0 => card A = 0.
proof. by move=> ->; apply/mcards0. qed.

lemma mcards0_eq (A: 'a mset): card A = 0 => A = mset0.
proof. 
rewrite -elemsK; elim (elems A) => [_|x l _]. 
- by rewrite /mset0.
rewrite card_oflist /=; smt(size_ge0).
qed.

lemma mcard_ge0 (A : 'a mset) : 0 <= card A.
proof. by rewrite /card size_ge0. qed.

lemma mcard1 (x : 'a) : card (mset1 x) = 1.
proof. by rewrite /card elems_mset1. qed.

(* -------------------------------------------------------------------- *)
lemma mcard_add (A B : 'a mset): card (A + B) = card A + card B.
proof. by rewrite /add card_oflist size_cat /card. qed.

lemma mcardUI_indep (A B : 'a mset) : disjoint A B =>
  card (A `|` B) = card A + card B.
proof. by move => djab; rewrite -mcard_add msetaddUI djab adds0. qed.

lemma mcardUI (A B : 'a mset) :
  card (A `|` B) + card (A `&` B) = card A + card B.
proof. by rewrite -2!mcard_add -msetaddUI. qed.

(* -------------------------------------------------------------------- *)
lemma mcardU (A B : 'a mset) :
  card (A `|` B) = card A + card B - card (A `&` B).
proof. by rewrite -mcardUI Ring.IntID.addrK. qed.

lemma mcardI (A B : 'a mset) :
  card (A `&` B) = card A + card B - card (A `|` B).
proof. by rewrite -mcardUI addzAC subzz. qed.

(* -------------------------------------------------------------------- *)
lemma mcardID (A B : 'a mset) :
  card (A `&` B) + card (A `\` B) = card A.
proof. by rewrite -mcard_add msetID. qed.

lemma mcardD (A B : 'a mset) :
  card (A `\` B) = card A - card (A `&` B).
proof. by rewrite -(mcardID A B) addzAC subzz. qed.

lemma mcardI_D (A B: 'a mset) :
  card (A `&` B) = card A - card (A `\` B).
proof. rewrite -(mcardID A B) /#. qed.

(* -------------------------------------------------------------------- *)

lemma mcardI1 (A : 'a mset) x : 
  card (A `&` mset1 x) = b2i (x \in A).
proof. by rewrite msetI1; case: (x \in A) => _; rewrite ?mcard1 ?mcards0. qed.

lemma mcardU1 (A : 'a mset) x : 
  card (A `|` mset1 x) = b2i (x \notin A) + card A.
proof. by rewrite mcardU mcard1 mcardI1 /#. qed.

lemma mcardD1 (A : 'a mset) (x : 'a) :
  card A = card (A `\` mset1 x) + (if mem A x then 1 else 0).
proof. by rewrite mcardD mcardI1; ring. qed.

(* -------------------------------------------------------------------- *)
lemma card_iota (n : int) : 0 <= n => card (oflist (iota_ 1 n)) = n.
proof. 
by move=> n_ge0; rewrite card_oflist size_iota /#. 
qed.

(* -------------------------------------------------------------------- *)
lemma subset_leq_mcard (A B : 'a mset) :
  A \subset B => card A <= card B.
proof. move=>/subset_msetI_id<-; rewrite mcardI_D; smt(mcard_ge0). qed.

(* -------------------------------------------------------------------- *)
lemma subset_cardP (A B : 'a mset) :
  card A = card B => (A = B <=> A \subset B).
proof.
move=> eqcAB; split=> [->//| A_leB].
have/eq_sym B_eq:=subset_msetDadd _ _ A_leB.
move: eqcAB; rewrite {1}B_eq mcard_add => H; move: B_eq.
have{H}/mcards0_eq->: card (B `\`A) = 0 by smt().
by rewrite add0s => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma eqEcard (A B : 'a mset) :
  (A = B) <=> (A \subset B) /\ (card B <= card A).
proof.
  split=> [->// |]; case=> le_AB le_cAB; rewrite subset_cardP //.
  by rewrite eqr_le le_cAB /=; apply/subset_leq_mcard.
qed.

(* -------------------------------------------------------------------- *)

lemma mcard_eq1 (A : 'a mset) : (card A = 1) <=> (exists a, A = mset1 a).
proof.
split=> [o_cA|[a ->]]; last apply/mcard1.
exists (pick A); rewrite eq_sym eqEcard o_cA mcard1 /= sub1set mem_pick.
by apply: contraL o_cA => ->; rewrite mcards0.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] fold (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a mset) : 'b =
  foldr f z (elems A).

lemma fold0 (f : 'a -> 'b -> 'b) (z : 'b): fold f z mset0 = z.
proof. by rewrite /fold elems_mset0. qed.

lemma fold1 (f : 'a -> 'b -> 'b) (z : 'b) (a : 'a):
  fold f z (mset1 a) = f a z.
proof. by rewrite /fold elems_mset1. qed.

lemma foldC (a : 'a) (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a mset):
  (forall a a' b, f a (f a' b) = f a' (f a b)) =>
  mem A a =>
  fold f z A = f a (fold f z (rem A a)).
proof.
move=> f_commutative a_in_A; rewrite /fold (foldr_rem a)// 1:-memE//.
congr; apply/foldr_perm=> //.
rewrite perm_eqP_pred1 => x.
rewrite -/(mult _ _) rem_mult /mult.
rewrite (eq_imp (count (pred1 x) (elems A) - b2i (a = x))); 1:smt(count_rem).
smt(mem_count).
qed.
