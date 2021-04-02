(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List.

op is_finite (p : 'a -> bool) =
  exists s, uniq s /\ (forall x, x \in s <=> p x).

(* -------------------------------------------------------------------- *)
op to_seq: ('a -> bool) -> 'a list.

axiom to_seq_finite (P : 'a -> bool):
  is_finite P => uniq (to_seq P) /\ (forall x, x \in to_seq P <=> P x).

(* -------------------------------------------------------------------- *)
lemma mkfinite ['a] (p : 'a -> bool) :
  (exists (s : 'a list), forall x, p x => x \in s) => is_finite p.
proof.
case=> s fin_p; exists (filter p (undup s)); split.
+ by apply/filter_uniq/undup_uniq.
+ by move=> a; rewrite mem_filter mem_undup /#.
qed.

(* -------------------------------------------------------------------- *)
lemma uniq_to_seq (P : 'a -> bool):
  is_finite P => uniq (to_seq P).
proof. by move=>/to_seq_finite [-> _]. qed.

lemma mem_to_seq (P : 'a -> bool) x:
  is_finite P => mem (to_seq P) x <=> P x.
proof. by move=>/to_seq_finite [_ ->]. qed.

(* -------------------------------------------------------------------- *)
lemma finiteP ['a] (p : 'a -> bool) :
  (exists s, forall x, p x => x \in s) <=> is_finite p.
proof. split.
+ case=> s in_sP; exists (undup (filter p s)); split.
  - by apply/undup_uniq.
  - by move=> x; rewrite mem_undup mem_filter andb_idr // &(in_sP).
+ by case=> s [_ in_sP]; exists s => x /in_sP.
qed.

(* -------------------------------------------------------------------- *)
lemma NfiniteP ['a] n (p : 'a -> bool) : 0 <= n =>
  !is_finite p => exists s, (n <= size s /\ uniq s) /\ (mem s) <= p.
proof.
move=> ge0_n; rewrite /is_finite negb_exists /= => h.
elim: n ge0_n => [|n ge0_n [s [[sz uq_s] ih]]]; first by exists [].
suff [x [px x_notin_s]]: exists x, p x /\ !(x \in s).
+ exists (x :: s); rewrite /= x_notin_s uq_s /= addzC.
  by rewrite lez_add2l sz /= => y; rewrite in_cons => -[->//|/ih].
move: (h s); apply/contraR; rewrite negb_exists uq_s /=.
by move=> + x - /(_ x); rewrite negb_and /= /#.
qed.

(* -------------------------------------------------------------------- *)
(* Finite sets can be obtained by union, intersection and difference    *
 * of empty and singleton sets. Finiteness is closed under inclusion.   *)

lemma finite0: is_finite pred0<:'a>.
proof. by exists []. qed.

lemma finite1 (x : 'a): is_finite (pred1 x).
proof. by exists [x]. qed.

lemma finite_leq (B A : 'a -> bool):
  A <= B => is_finite B => is_finite A.
proof.
move=> le_A_B [wB] [uniq_wB wB_univ]; apply/finiteP.
exists (filter A wB) => x Ax; rewrite mem_filter Ax /=.
by rewrite wB_univ le_A_B.
qed.

lemma finiteU (A B : 'a -> bool):
  is_finite A => is_finite B => is_finite (predU A B).
proof.
move=> [wA] [uniq_wA wA_univ] [wB] [uniq_wB wB_univ].
apply/finiteP; exists (wA ++ wB) => x ABx.
by rewrite mem_cat wA_univ wB_univ.
qed.

lemma finiteIl (A B : 'a -> bool):
  is_finite A => is_finite (predI A B).
proof.
by move=> fin_A; apply/(finite_leq A)=> //=; exact/predIsubpredl.
qed.

lemma finiteIr (A B : 'a -> bool):
  is_finite B => is_finite (predI A B).
proof.
by move=> fin_B; apply/(finite_leq B)=> //=; exact/predIsubpredr.
qed.

lemma finiteD (A B : 'a -> bool):
  is_finite A => is_finite (predD A B).
proof. by move=> fin_A; apply/(finite_leq A)=> //= x @/predD. qed.

(* -------------------------------------------------------------------- *)
lemma is_finite_surj ['a 'b] (f : 'a -> 'b) pa pb :
      (forall b, pb b => exists a, pa a /\ b = f a)
   => is_finite pa
   => is_finite pb.
proof. 
move=> surj_f /finiteP [s hs]; apply/finiteP.
exists (map f s) => b /surj_f [a [pa_a ->]].
by apply/mapP; exists a => /=; apply/hs.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_unit (p : unit -> bool): is_finite p.
proof.
exists (filter p [tt]); split; first by apply/filter_uniq.
by move=> x; rewrite mem_filter; apply/andb_idr; case: x.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_bool (p : bool -> bool): is_finite p.
proof.
exists (filter p [true; false]); split; first by apply/filter_uniq.
by move=> x; rewrite mem_filter; apply/andb_idr; case: x.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_pair ['a 'b] pa pb :
  is_finite<:'a> pa => is_finite<:'b> pb
    => is_finite (fun x : _ * _ => pa x.`1 /\ pb x.`2).
proof.
move=> /finiteP[sa ha] /finiteP[sb hb]; apply/finiteP.
exists (allpairs (fun x y => (x, y)) sa sb) => /= p [hpa hpb].
by apply/allpairsP; exists p; rewrite !(ha, hb) //=; case: (p).
qed.

(* -------------------------------------------------------------------- *)
op fingraph ['a 'b] (sa : 'a list) (sb : 'b list) : ('a * 'b) list list =
  foldr (fun (a : 'a) (g : ('a * 'b) list list) =>
    flatten (map (fun g1 => map (fun b => (a, b) :: g1) sb) g)
  ) [[]] sa.

lemma fingraph_nil ['a 'b] (sb : 'b list) : fingraph<:'a, 'b> [] sb = [[]].
proof. by []. qed.

lemma fingraph_cons ['a 'b] (a : 'a) (sa : 'a list) (sb : 'b list) :
  fingraph<:'a, 'b> (a :: sa) sb =
    flatten (map (fun g1 => map (fun b => (a, b) :: g1) sb) (fingraph sa sb)).
proof. by []. qed.

lemma finite_fun ['a 'b] :
     is_finite<:'a> predT
  => is_finite<:'b> predT
  => is_finite<: 'a -> 'b> predT.
proof.
case=> [sa [uqa @/predT /= ha]] [sb [uqb @/predT /= hb]]; apply/finiteP.
pose F (s : ('a * 'b) list) (a : 'a) := odflt witness (assoc s a).
exists (map F (fingraph sa sb)) => /= f.
apply/mapP; pose s := map (fun a => (a, f a)) sa.
exists s; split=> [@/s|]; last first.
- apply/fun_ext=> a @/F; have: (a, f a) \in s.
  - by apply/mapP; exists a => /=; apply/ha.
  rewrite mem_assoc_uniq => [|->//]; apply/map_inj_in_uniq.
  - case=> [/= a1 b1] [/= a2 b2] /mapP[/= ? [# _ ->> ->>]].
    by case/mapP=> /= ? [# _ ->> ->> ->].
  - by apply/map_inj_in_uniq.
elim: {s ha} sa uqa => //= a sa ih [a_notin_sa /ih {ih}ih].
rewrite fingraph_cons; apply/flatten_mapP.
exists (map (fun a => (a, f a)) sa); rewrite ih /=.
by apply/mapP; exists (f a); rewrite hb.
qed.

(* -------------------------------------------------------------------- *)
op finite_type = is_finite predT<:'a>.

lemma finite_typeP ['a] :
  (exists (s:'a list), forall x, x \in s) <=> finite_type <:'a>.
proof. by rewrite /finite_type -finiteP /predT. qed.
  
lemma finite_type_surj ['a 'b] (f : 'a -> 'b):
  surjective f => finite_type <:'a> => finite_type <:'b>.
proof. by move=> surj_f h; apply: (is_finite_surj f predT predT). qed.
 
(* -------------------------------------------------------------------- *)
lemma finite_type_unit : finite_type <:unit>.
proof. by apply: finite_unit. qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_bool : finite_type <:bool>.
proof. by apply: finite_bool. qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_pair ['a 'b] : 
  finite_type <:'a> => finite_type <:'b> => finite_type <:'a * 'b>.
proof. by apply: finite_pair. qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_tuple3 ['a 'b 'c] : 
     finite_type <:'a>
  => finite_type <:'b>
  => finite_type <:'c>
  => finite_type <:'a * 'b * 'c>.
proof. 
move=> ha hb hc; pose f (p : 'a * ('b * 'c)) := (p.`1, p.`2.`1, p.`2.`2).
apply: (finite_type_surj f); 1: by case=> t1 t2 t3; exists (t1, (t2, t3)).
by apply/finite_type_pair/finite_type_pair.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_tuple4 ['a 'b 'c 'd] : 
     finite_type <:'a>
  => finite_type <:'b>
  => finite_type <:'c>
  => finite_type <:'d>
  => finite_type <:'a * 'b * 'c * 'd>.
proof. 
move=> ha hb hc hd; pose f (p: 'a * ('b * 'c * 'd)) :=
  (p.`1, p.`2.`1, p.`2.`2, p.`2.`3); apply: (finite_type_surj f).
- by case=> t1 t2 t3 t4; exists (t1, (t2, t3, t4)).
- by apply/finite_type_pair/finite_type_tuple3.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_tuple5 ['a 'b 'c 'd 'e] : 
     finite_type <:'a>
  => finite_type <:'b>
  => finite_type <:'c>
  => finite_type <:'d>
  => finite_type <:'e>
  => finite_type <:'a * 'b * 'c * 'd * 'e>.
proof. 
move=> ha hb hc hd he; pose f (p: 'a * ('b * 'c * 'd * 'e)) :=
  (p.`1, p.`2.`1, p.`2.`2, p.`2.`3, p.`2.`4); apply: (finite_type_surj f).
- by case=> t1 t2 t3 t4 t5; exists (t1, (t2, t3, t4, t5)).
- by apply/finite_type_pair/finite_type_tuple4.
qed.

(* -------------------------------------------------------------------- *)
lemma finite_type_fun ['a 'b] :
     finite_type <:'a>
  => finite_type <:'b>
  => finite_type <: 'a -> 'b>.
proof. by apply: finite_fun. qed.
