(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv Binomial Ring StdOrder.
(*---*) import IntID IntOrder.

(* -------------------------------------------------------------------- *)
op allperms_r (n : unit list) (s : 'a list) : 'a list list.

axiom allperms_r0 (s : 'a list) :
  allperms_r [] s = [[]].

axiom allperms_rS (x : unit) (n : unit list) (s : 'a list) :
  allperms_r (x :: n) s = flatten (
    map (fun x => map ((::) x) (allperms_r n (rem x s))) (undup s)).

op allperms (s : 'a list) = allperms_r (nseq (size s) tt) s.

hint rewrite ap_r : allperms_r0 allperms_rS.

(* -------------------------------------------------------------------- *)
lemma nosmt allperms_rP n (s t : 'a list) : size s = size n =>
  (mem (allperms_r n s) t) <=> (perm_eq s t).
proof.
elim: n s t => [s t /size_eq0 ->|? n ih s t] //=; rewrite ?ap_r /=.
  split => [->|]; first by apply/perm_eq_refl.
  by move/perm_eq_sym; apply/perm_eq_small.
case: s=> [|x s]; first by rewrite addz_neq0 ?size_ge0.
(pose s' := undup _)=> /=; move/addrI=> eq_sz; split.
  move/flatten_mapP=> [y] [s'y] /= /mapP [t'] [+ ->>].
  case: (x = y)=> [<<-|]; first by rewrite ih // perm_cons.
  move=> ne_xy; have sy: mem s y.
    by have @/s' := s'y; rewrite mem_undup /= eq_sym ne_xy.
  rewrite ih /= ?size_rem // 1?addrCA //.
  move/(perm_cons y); rewrite perm_consCA => /perm_eqrE <-.
  by apply/perm_cons/perm_to_rem.
move=> ^eq_st /perm_eq_mem/(_ x) /= tx; apply/flatten_mapP=> /=.
have nz_t: t <> [] by case: (t) tx. exists (head x t) => /=.
have/perm_eq_mem/(_ (head x t)) := eq_st; rewrite /s' mem_undup.
move=> ->; rewrite -(mem_head_behead x) //=; apply/mapP.
case: (x = head x t)=> /= [xE|nex].
  exists (behead t); rewrite head_behead //= ih //.
  by rewrite -(perm_cons x) {2}xE head_behead.
have shx: mem s (head x t).
  move/perm_eq_mem/(_ (head x t)): eq_st => /=; rewrite eq_sym.
  by rewrite nex /= => ->; rewrite -(mem_head_behead x).
exists (behead t); rewrite head_behead //= ih /=.
  by rewrite size_rem // addrCA.
rewrite -(perm_cons (head x t)) head_behead // perm_consCA.
by have/perm_eqrE <- := eq_st; apply/perm_cons/perm_eq_sym/perm_to_rem.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt uniq_allperms_r n (s : 'a list) : uniq (allperms_r n s).
proof.
elim: n s => [|? n ih] s; rewrite ?ap_r  //.
apply/uniq_flatten_map/undup_uniq.
  by move=> x /=; apply/map_inj_in_uniq/ih => a b _ _ [].
move=> x y; rewrite !mem_undup => sx sy /= /hasP[t].
by case=> /mapP[t1] [st1 ->] /mapP[t2] [st2 [->]].
qed.

(* -------------------------------------------------------------------- *)
lemma allpermsP (s t : 'a list) : mem (allperms s) t <=> perm_eq s t.
proof. by apply/allperms_rP; rewrite size_nseq ler_maxr ?size_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma uniq_allperms (s : 'a list) : uniq (allperms s).
proof. by apply/uniq_allperms_r. qed.

(* -------------------------------------------------------------------- *)
lemma allperms_spec (s t : 'a list) :
  count (pred1 t) (allperms s) = b2i (perm_eq s t).
proof. by rewrite count_uniq_mem 1:uniq_allperms // allpermsP. qed.

(* -------------------------------------------------------------------- *)
require import StdBigop.
(*---*) import Bigint Bigint.BIM Bigint.BIA.

(* -------------------------------------------------------------------- *)
lemma size_allperms_uniq_r n (s : 'a list) : size s = size n => uniq s =>
  size (allperms_r n s) = fact (size s).
proof.
elim: n s => /= [|? n ih] s; rewrite ?ap_r /=.
  by move/size_eq0=> -> /=; rewrite fact0.
case: s=> [|x s]; first by rewrite addz_neq0 ?size_ge0.
(pose s' := undup _)=> /=; move/addrI=> eq_sz [Nsz uqs].
rewrite (addrC 1) factS ?size_ge0 // -ih //.
rewrite size_flatten sumzE -map_comp; pose F := _ \o _.
rewrite /s' undup_id //= big_consT /= {1}/F /(\o) /=.
rewrite size_map /= mulrDl /= addrC; congr.
have: forall y, mem s y => F y = size (allperms_r n s).
  move=> y sy @/F @/(\o); rewrite size_map; case: (x = y)=> //.
  move=> ne_xy; rewrite !ih //= ?size_rem //.
    by rewrite rem_uniq //=; apply/negP=> /mem_rem.
move/eq_in_map=> ->; rewrite big_map predT_comp /(\o) /=.
by rewrite sumr_const intmulz count_predT mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma size_allperms_uniq (s : 'a list) :
  uniq s => size (allperms s) = fact (size s).
proof. by apply/size_allperms_uniq_r; rewrite size_nseq ler_maxr ?size_ge0. qed.

(* -------------------------------------------------------------------- *)
(*TODO: why is \subset not in List?*)
(*require import FSet.*)
(*TODO: also where does this 'a comes from?*)

op subset (s t : 'a list) = forall x , x \in s => x \in t.

lemma subsetA (s t u : 'a list) : subset s t => subset t u => subset s u.
proof. by move => subset_s_t subset_t_u x mem_x_s; apply/subset_t_u/subset_s_t. qed.

(* -------------------------------------------------------------------- *)
(*Represents the permutation: k -> p[k]*)
pred is_perm (n : int) (p : int list) =
  perm_eq p (range 0 n).

lemma size_is_perm n p :
  0 <= n =>
  is_perm n p =>
  size p = n.
proof. by rewrite /is_perm => le0n /perm_eq_size; rewrite size_range ler_maxr. qed.

op id_perm n = range 0 n.

lemma is_perm_id n : is_perm n (id_perm n).
proof. by rewrite /is_perm /id_perm perm_eq_refl. qed.

op cc_perm n = if 0 < n then rcons (range 1 n) 0 else [].

lemma is_perm_cc n : is_perm n (cc_perm n).
proof.
rewrite /is_perm /cc_perm -cats1; case (0 < n) => [lt0n|/lerNgt len0].
+ by rewrite (range_ltn 0) // -(cat1s _ (range _ _)) perm_catC.
by rewrite range_geq.
qed.

(* -------------------------------------------------------------------- *)
op permute (dflt : 'a) (p : int list) (s : 'a list) =
  mkseq (fun n => nth dflt s (nth (-1) p n)) (size s).

lemma permute_is_perm dflt n (p : int list) :
  is_perm n p =>
  permute dflt p (range 0 n) = p.
proof.
  rewrite /is_perm /permute => perm_eq_p; apply/(eq_from_nth (-1)).
  + by rewrite size_mkseq ler_maxr ?size_ge0 // eq_sym; apply/perm_eq_size.
  move => k; rewrite size_mkseq ler_maxr ?size_ge0 // => mem_k.
  rewrite nth_mkseq //= nth_range //= -mem_range.
  move: (all_nthP (fun i => i \in range 0 n) p (-1)) => [_ /= imp].
  apply/imp => {imp}; [by apply/allP => x mem_x; rewrite -(perm_eq_mem _ _ perm_eq_p)|].
  by rewrite (perm_eq_size _ _ perm_eq_p).
qed.

lemma permuteP (dflt : 'a) (p : int list) (s : 'a list) :
  is_perm (size s) p =>
  perm_eq s (permute dflt p s).
proof.
  rewrite /permute => is_perm_p; move: (is_perm_p); rewrite /is_perm => /perm_eqP eq_count.
  apply/perm_eqP1 => x; rewrite /mkseq count_map /preim /=.
  rewrite range_iota /=; rewrite -{1}(map_nth_range dflt s) count_map /preim /=.
  rewrite -eq_count -(permute_is_perm (-1) (size s)) //.
  rewrite /permute /mkseq count_map /preim /= range_iota /= size_range /= ler_maxr ?size_ge0 //.
  apply/eq_in_count => n mem_n /=; rewrite (nth_map (-1)) /=.
  + by rewrite -mem_range size_range /= ler_maxr ?size_ge0.
  by rewrite (nth_range n (size s) 0 (-1)) //= -mem_range.
qed.

(* -------------------------------------------------------------------- *)
op perm_of_lists (dflt : 'a) (s t : 'a list) =
  mkseq (fun n => index (nth dflt t n) s) (size s).

lemma permute_perm_of_lists (dflt : 'a) (s t : 'a list) :
  uniq s =>
  perm_eq s t =>
  permute dflt (perm_of_lists dflt s t) s = t.
proof.
  admit.
qed.

lemma perm_of_lists_permute (dflt : 'a) (p : int list) (s : 'a list) :
  is_perm (size s) p =>
  uniq s =>
  perm_of_lists dflt s (permute dflt p s) = p.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op (\c) = permute (-1).

lemma compA n p1 p2 p3 :
  is_perm n p1 =>
  is_perm n p2 =>
  is_perm n p3 =>
  p1 \c p2 \c p3 = p1 \c (p2 \c p3).
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op inv (n : int) (p : int list) : int list.

lemma invK n p :
  is_perm n p =>
  (inv n p) \c p = id_perm n.
proof.
  admit.
qed.

lemma invrK n p :
  is_perm n p =>
  p \c (inv n p) = id_perm n.
proof.
  admit.
qed.

lemma invC n p q :
  is_perm n p =>
  is_perm n q =>
  inv n (p \c q) = inv n q \c inv n p.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op conj n u p = u \c p \c (inv n u).

lemma conjA n u v p :
  is_perm n u =>
  is_perm n v =>
  is_perm n p =>
  conj n u (conj n v p) = conj n (u \c v) p.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op is_cycle n p y = subset (zip y (rot 1 y)) (zip (range 0 n) p).

op cycles (n : int) (p : int list) : int list list.

lemma cyclesP n p :
  is_perm n p =>
  perm_eq (range 0 n) (flatten (cycles n p)) /\
  all (is_cycle n p) (cycles n p).
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op shape (n : int) (p : int list) = mkseq (fun n => count (fun c => size c = n + 1) (cycles n p)) (size p).

lemma shape_eq n p q :
  is_perm n p =>
  is_perm n q =>
  shape n p = shape n q <=> (exists u , conj n u p = q).
proof.
  admit.
qed.

lemma nth_shape_ge0 x k n p :
  k \in range 0 (size p) =>
  0 <= nth x (shape n p) k.
proof. by move=> mem_k; rewrite /shape nth_mkseq -?mem_range //= count_ge0. qed.

(* -------------------------------------------------------------------- *)
pred is_shape (n : int) (s : int list) = true. (*TODO*)

lemma is_shapeP n s :
  is_shape n s <=> (exists p , is_perm n p /\ shape n p = s).
proof.
  admit.
qed.

lemma is_shape_sum n s :
  0 <= n =>
  is_shape n s =>
  BIA.bigi predT (fun i => i * nth 0 s (i - 1)) 1 (n + 1) = n.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op allperms_shape (n : int) (s : int list) : int list list.

lemma allperms_shapeP n s :
  is_shape n s =>
  perm_eq (allperms_shape n s) (filter (fun p => shape n p = s) (allperms (range 0 n))).
proof.
  admit.
qed.

lemma size_allperms_shape n s :
  is_shape n s =>
  size (allperms_shape n s) = 0. (*TODO*)
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op allshapes (n : int) : int list list.

lemma allshapesP n s :
  is_shape n s <=> s \in allshapes n.
proof.
  admit.
qed.

lemma allshapes_uniq n :
  uniq (allshapes n).
proof.
  admit.
qed.

lemma size_allshapes n :
  size (allshapes n) = 0. (*TODO*)
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
(*TODO: need a big clone to bring everything together.*)
