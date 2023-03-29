(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv Binomial Ring StdOrder IntMin IntDiv.
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
  0 < n /\ perm_eq p (range 0 n).

lemma is_perm_lt0 n p :
  is_perm n p =>
  0 < n.
proof. by case. qed.

lemma size_is_perm n p :
  is_perm n p =>
  size p = n.
proof. by case=> /ltzW le0n /perm_eq_size; rewrite size_range ler_maxr. qed.

op id_perm n = range 0 n.

lemma is_perm_id n : 0 < n => is_perm n (id_perm n).
proof. by rewrite /is_perm /id_perm perm_eq_refl. qed.

op cc_perm c = mkseq (fun i => nth (-1) c ((index i c + 1) %% (size c))) (size c).

lemma is_perm_cc n c :
  0 < n =>
  perm_eq c (range 0 n) =>
  is_perm n (cc_perm c).
proof.
move=> lt0n eq_; move/perm_eq_size: (eq_); rewrite size_range ler_maxr ?ltzW //= => <<-.
split=> //; apply/uniq_perm_eq; [|by apply/range_uniq|].
+ rewrite map_inj_in_uniq range_iota ?range_uniq //=.
  move=> i j memi memj eq_nth; move: (uniq_nth_inj_in _ _ _ _ _ _ _ _ eq_nth).
  - by rewrite (perm_eq_uniq _ _ eq_) range_uniq.
  - apply/mem_range; move: (mem_range_mod (index i c + 1) (size c)).
    by rewrite gtr_eqF // gtr0_norm.
  - apply/mem_range; move: (mem_range_mod (index j c + 1) (size c)).
    by rewrite gtr_eqF // gtr0_norm.
  rewrite -eq_mod opprD !addrA (addrAC _ _ (-1)) /= eq_mod !modz_small.
  - by rewrite index_ge0 gtr0_norm // index_mem /= (perm_eq_mem _ _ eq_).
  - by rewrite index_ge0 gtr0_norm // index_mem /= (perm_eq_mem _ _ eq_).
  apply/uniq_index_inj_in.
  - by rewrite (perm_eq_uniq _ _ eq_) range_uniq.
  - by rewrite (perm_eq_mem _ _ eq_).
  by rewrite (perm_eq_mem _ _ eq_).
move=> i; rewrite mkseqP; split=> [[j] [] /mem_range memj /= ->>|memi /=].
+ rewrite -(perm_eq_mem _ _ eq_); apply/mem_nth/mem_range.
  move: (mem_range_mod (index j c + 1) (size c)).
  by rewrite gtr_eqF // gtr0_norm.
exists (nth witness c ((index i c - 1) %% size c)).
rewrite -mem_range -(perm_eq_mem _ _ eq_) mem_nth /=.
+ rewrite -mem_range; move: (mem_range_mod (index i c - 1) (size c)).
  by rewrite gtr_eqF // gtr0_norm.
rewrite index_uniq //.
+ rewrite -mem_range; move: (mem_range_mod (index i c - 1) (size c)).
  by rewrite gtr_eqF // gtr0_norm.
+ by rewrite (perm_eq_uniq _ _ eq_) range_uniq.
rewrite modzDml /= modz_small.
+ by rewrite index_ge0 gtr0_norm // index_mem /= (perm_eq_mem _ _ eq_).
by rewrite nth_index // (perm_eq_mem _ _ eq_).
qed.

(* -------------------------------------------------------------------- *)
op permute (dflt : 'a) (p : int list) (s : 'a list) =
  map (fun n => nth dflt s n) p.

lemma permute_is_perm dflt n (p : int list) :
  is_perm n p =>
  permute dflt p (id_perm n) = p.
proof.
  rewrite /di_perm /is_perm /permute => -[] lt0n perm_eq_p; apply/(eq_from_nth (-1)).
  + by rewrite size_map.
  move => k; rewrite size_map => mem_k.
  rewrite (nth_map (-1)) //= nth_range //= -mem_range.
  move: (all_nthP (fun i => i \in range 0 n) p (-1)) => [_ /= imp].
  by apply/imp => {imp} //; apply/allP => x mem_x; rewrite -(perm_eq_mem _ _ perm_eq_p).
qed.

lemma permuteP (dflt : 'a) (p : int list) (s : 'a list) :
  is_perm (size s) p =>
  perm_eq s (permute dflt p s).
proof.
  rewrite /permute => -[] lt0n is_perm_p; move: (is_perm_p).
  rewrite /is_perm => /perm_eqP eq_count.
  apply/perm_eqP1 => x; rewrite count_map /preim /= eq_count.
  by rewrite -{1}(map_nth_range dflt s) count_map /preim.
qed.

(* -------------------------------------------------------------------- *)
op perm_of_lists (dflt : 'a) (s t : 'a list) =
  map (fun x => index x t) s.

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

lemma compr1 n p :
  is_perm n p =>
  p \c (id_perm n) = p.
proof.
  admit.
qed.

lemma comp1r n p :
  is_perm n p =>
  (id_perm n) \c p = p.
proof.
  admit.
qed.

lemma compA n p1 p2 p3 :
  is_perm n p1 =>
  is_perm n p2 =>
  is_perm n p3 =>
  p1 \c p2 \c p3 = p1 \c (p2 \c p3).
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op inv (p : int list) =
  mkseq (fun i => index i p) (size p).

lemma invK n p :
  is_perm n p =>
  (inv p) \c p = id_perm n.
proof.
  admit.
qed.

lemma invrK n p :
  is_perm n p =>
  p \c (inv p) = id_perm n.
proof.
  admit.
qed.

lemma invC n p q :
  is_perm n p =>
  is_perm n q =>
  inv (p \c q) = inv q \c inv p.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op exp p n =
  if n < 0
  then iterop (-n) (\c) (inv p) (id_perm (size p))
  else iterop n (\c) p (id_perm (size p)).

(* -------------------------------------------------------------------- *)
op conj u p = u \c p \c (inv u).

lemma conjA n u v p :
  is_perm n u =>
  is_perm n v =>
  is_perm n p =>
  conj u (conj v p) = conj (u \c v) p.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op is_fixed p i =
  forall dflt , nth dflt p i = i.

(* -------------------------------------------------------------------- *)
op order p i = argmin idfun (fun n => 0 < n /\ is_fixed (exp p n) i).

lemma dvd_order n p i :
  is_perm n p =>
  order p i %| n.
proof.
  admit.
qed.

lemma order_id_perm n p :
  is_perm n p =>
  (forall i , i \in range 0 n => order p i = 1) <=>
  (p = id_perm n).
proof.
  admit.
qed.

lemma order_cc_perm n p :
  is_perm n p =>
  (forall i , i \in range 0 n => order p i = n) <=>
  (exists c , perm_eq c (range 0 n) /\ p = cc_perm c).
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op is_cycle p c = c <> [] /\ subset (zip c (rot 1 c)) (zip (range 0 (size p)) p).

lemma is_cycle_size n p c i :
  is_perm n p =>
  is_cycle p c =>
  i \in c =>
  size c = order p i.
proof.
  admit.
qed.

lemma is_cycle_dvd_size n p c :
  is_perm n p =>
  is_cycle p c =>
  size c %| n.
proof.
  move=> is_p_p is_c_c.
  rewrite (is_cycle_size _ _ _ (head (-1) c) is_p_p is_c_c).
  + by case: is_c_c => + _; case: c.
  by apply/dvd_order.
qed.

lemma is_cycle_rot n p c k :
  is_perm n p =>
  is_cycle p c =>
  is_cycle p (rot k c).
proof.
  admit.
qed.

lemma is_cycle_mem_rot_inj n p c1 c2 i :
  is_perm n p =>
  is_cycle p c1 =>
  is_cycle p c2 =>
  i \in c1 =>
  i \in c2 =>
  exists k , c1 = rot k c2.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op cycles (p : int list) =
  undup_eqv
    (fun c1 c2 => exists k , c1 = rot k c2)
    (mkseq
      (fun i =>
        take
          (order p i)
          (mkseq
            (fun j => nth (-1) (exp p j) i)
            (size p)))
      (size p)).

lemma is_cycle_cycles n p :
  is_perm n p =>
  all (is_cycle p) (cycles p).
proof.
  admit.
qed.

lemma cyclesP n p c :
  is_perm n p =>
  is_cycle p c <=>
  (exists k, rot k c \in cycles p).
proof.
  admit.
qed.

lemma cycles_perm_eq n p :
  is_perm n p =>
  perm_eq (flatten (cycles p)) (range 0 n).
proof.
  admit.
qed.

lemma cycles_sum n p :
  is_perm n p =>
  BIA.big predT size (cycles p) = n.
proof.
  move=> is_p_p; move/is_perm_lt0: is_p_p (is_p_p) => lt0n.
  move/cycles_perm_eq/perm_eq_size.
  by rewrite size_flatten sumzE BIA.big_mapT size_range ler_maxr // ltzW.
qed.

(* -------------------------------------------------------------------- *)
op shape (p : int list) =
  mkseq (fun n => count (fun c => size c = n + 1) (cycles p)) (size p).

lemma size_shape p :
  size (shape p) = size p.
proof. by rewrite /shape size_mkseq ler_maxr // size_ge0. qed.

lemma shape_eq n p q :
  is_perm n p =>
  is_perm n q =>
  shape p = shape q <=> (exists u , conj u p = q).
proof.
  admit.
qed.

lemma shape_ge0 p :
  all ((<=) 0) (shape p).
proof.
  by apply/allP => ? /mapP [] i [] _ ->>; apply/count_ge0.
qed.

lemma shape_sum dflt n p :
  is_perm n p =>
  BIA.bigi predT (fun i => i * nth dflt (shape p) (i - 1)) 1 (n + 1) = n.
proof.
  move=> is_p_p; rewrite -{2}(cycles_sum n p) // /shape.
  rewrite eq_sym (big_mcount _ _ 1 (size p + 1)).
  + move=> ? /mapP [] c [] mem_ ->>.
    move/allP/(_ _ mem_): (is_cycle_cycles _ _ is_p_p) => is_c_c.
    move: (is_cycle_dvd_size _ _ _ is_p_p is_c_c) => dvd_.
    move: (dvdz_le _ _ _ dvd_); [by apply/gtr_eqF; case: is_p_p|].
    rewrite ger0_norm ?size_ge0 // gtr0_norm; [by case: is_p_p|].
    rewrite mem_range ltzS => le_; split=> [|_].
    - case/ler_eqVlt: (size_ge0 c) => [/eq_sym/size_eq0 ->>|/ltzE //].
      by move/dvd0z: dvd_ => ->>; case: is_p_p.
    apply/(ler_trans _ _ _ le_); case: is_p_p => lt0n.
    by move/perm_eq_size => ->; rewrite size_range; apply/maxrr.
  case: (is_p_p) => lt0n /perm_eq_size; rewrite size_range ler_maxr ?ltzW //= => ->.
  apply/BIA.eq_big_seq => i memi /=; rewrite nth_mkseq /=.
  + by rewrite -mem_range mem_range_subr.
  by rewrite count_map /preim /pred1.
qed.

lemma id_shapeP n :
  0 < n =>
  shape (id_perm n) = n :: nseq (n - 1) 0.
proof.
  admit.
qed.

lemma cc_shapeP n c :
  0 < n =>
  perm_eq c (range 0 n) =>
  shape (cc_perm c) = rcons (nseq (n - 1) 0) 1.
proof.
  admit.
qed.

lemma cc_shapeW dflt n p :
  is_perm n p =>
  0 < nth dflt (shape p) (n - 1) <=>
  (exists c , perm_eq c (range 0 n) /\ p = cc_perm c).
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op is_shape (n : int) (s : int list) : bool =
  size s = n /\
  all ((<=) 0) s /\
  forall dflt , BIA.bigi predT (fun i => i * nth dflt s (i - 1)) 1 (n + 1) = n.

lemma is_shape_size n s :
  is_shape n s =>
  size s = n.
proof. by case. qed.

lemma is_shape_ge0 n s :
  is_shape n s =>
  all ((<=) 0) s.
proof. by case=> _ []. qed.

lemma is_shape_sum dflt n s :
  is_shape n s =>
  BIA.bigi predT (fun i => i * nth dflt s (i - 1)) 1 (n + 1) = n.
proof. by case=> _ [] _ => ->. qed.

lemma is_shapeW n s :
  size s = n =>
  all ((<=) 0) s =>
  (forall dflt , BIA.bigi predT (fun i => i * nth dflt s (i - 1)) 1 (n + 1) = n) =>
  is_shape n s.
proof. by move=> ? ? ?; split. qed.

lemma is_shapeP n s :
  is_shape n s <=> (exists p , is_perm n p /\ shape p = s).
proof.
  admit.
qed.

lemma cc_is_shapeW dflt n s :
  is_shape n s =>
  0 < nth dflt s (n - 1) <=>
  s = rcons (nseq (n - 1) 0) 1.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
op allperms_shape (s : int list) =
  filter (fun p => shape p = s) (allperms (range 0 (size s))).

lemma allperms_shapeP n s :
  is_shape n s =>
  perm_eq (allperms_shape s) (filter (fun p => shape p = s) (allperms (range 0 n))).
proof.
  case/is_shapeP => p [] [] lt0n /perm_eq_size.
  rewrite size_range ler_maxr ?ltzW //= => <<- <<-.
  by rewrite /allperms_shape size_shape perm_eq_refl.
qed.

lemma size_allperms_shape n s :
  is_shape n s =>
  size (allperms_shape s) = 0. (*TODO*)
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
