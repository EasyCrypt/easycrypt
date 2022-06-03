require import AllCore List Distr DList StdOrder Ring IntDiv RealSeries.
require FinType.

(* We assume that a have a finite type (with p elements) and 
   this type is a field. This implies that p is of the form q^n with q a prime *)
clone import MFinite as FT.
import Support.
op p = card.

clone import Field as F
  with type t <- FT.t.

lemma gt0_p : 0 < p.
proof.
rewrite /p /card; have /= /#:= uniq_leq_size [zeror] enum _ _ => //.
by move=> x _; apply enumP.
qed.

clone import Bigalg.BigComRing as Big with
  type CR.t <- t,
  pred CR.unit (x : t)  <- x <> zeror,
    op CR.zeror  <- zeror,
    op CR.oner   <- oner,
    op CR.( + )  <- F.( + ),
    op CR.([-])  <- F.([-]),
    op CR.( * )  <- F.( * ),
    op CR.invr   <- F.invr,
    op CR.intmul <- F.intmul,
    op CR.ofint  <- F.ofint,
    op CR.exp    <- F.exp,
    op CR.lreg   <- F.lreg.

import BAdd.

lemma duni_zmod_shift (d : t distr) (c : t) :
  is_funiform d => is_lossless d => dmap d (fun z => z + c) = d.
proof.
move=> funi_d ll_d; apply: (@dmap_bij _ _ _ (fun z => z - c)) => /=.
- by move=> v _; apply: funi_ll_full.
- by move=> v _; apply: funi_d.
- by move=> v _; rewrite addrK.
- by move=> v _; rewrite subrK.
qed.

op uhash_list (s:t list) (vs : t list) = 
 let k = size s in
 map (fun (i : int) =>
       BAdd.bigi predT
         (fun (j : int) => exp (nth zeror s i) j * nth zeror vs j)
           0 k) (range 0 k).

op uhash_list_inv : t list -> t list -> t list.

axiom uhash_list_bij s vs :
  uniq s => size s = size vs =>
  uhash_list_inv s (uhash_list s vs) = vs /\
  uhash_list s (uhash_list_inv s vs) = vs.

axiom uhash_list_inv s vs : 
  uniq s => size s = size vs => 
  size (uhash_list_inv s vs) = size s.

lemma vdmV s :
    uniq s => 
    dmap (dlist dunifin (size s)) (uhash_list s) = dlist dunifin (size s).
proof.
  move=> hu.
  have h0s: 0 <= size s by apply size_ge0.
  have hsize : forall l, size s = size (uhash_list s l).
  + move=> l; rewrite /uhash_list /= size_map size_range /#.
  apply (dmap_bij _ _ _ (uhash_list_inv s)) => /=.
  + move=> l /(supp_dlist dunifin (size s) l h0s) [] heq _; rewrite (hsize l).
    by apply dlist_fu => x _; apply dunifin_fu.
  + move=> l /(supp_dlist dunifin (size s) l h0s) [] heq _.
    apply dlist_uni => //; 1: by apply dunifin_uni.
    by rewrite -heq; apply dlist_fu => ??; apply dunifin_fu.
  + have <- := uhash_list_inv s l hu _; 1: by rewrite heq.
    by apply dlist_fu => ??; apply dunifin_fu.
  + move=> l  /(supp_dlist dunifin (size s) l h0s) [] heq _.
    by case : (uhash_list_bij s l hu _); 1: by rewrite heq.
  move=> l  /(supp_dlist dunifin (size s) l h0s) [] heq _.
  by case : (uhash_list_bij s l hu _); 1: by rewrite heq.
qed.

(*

op n : { int | 0 < n <= p } as gt0_n.
op k : { int | 0 < k <= n } as rg_k.

op s, t : t list.

axiom size_s : size s = k.
axiom size_t : k + size t = n.
axiom uniq_s : uniq s.
axiom sub_ts : forall x, x \in t => x \in s.
x

*)


op dv = dlist dunifin p.

op dout r =
  dmap dv (fun v => map (fun i => nth zeror v (index i enum)) r).

op dsim n k r =
  dmap (dlist dunifin n) (fun seed => map
    (fun i =>
      BAdd.bigi predT (fun j => exp (nth zeror r i) j * nth zeror seed j) 0 n)
    (range 0 k)).

lemma dletC ['a 'b] (da : 'a distr) (db : 'b distr) :
  is_lossless da => dlet da (fun _ => db) = db.
proof.
move=> ll; apply: eq_distr=> b; rewrite dlet1E /=.
rewrite RealSeries.sumZr -(RealSeries.eq_sum (mu1 da)) //.
by rewrite -weightE ll.
qed.

lemma mask0s ['a] (s : 'a list) : mask [] s = [].
proof. by case: s. qed.

lemma take_range0 (i j : int) : i <= j => take i (range 0 j) = range 0 i.
proof. by move=> le_ij; rewrite /range take_iota /#. qed.

lemma drop_range0 (i j : int) : 0 <= i => drop i (range 0 j) = range i j.
proof. by move=> le_ij; rewrite /range drop_iota. qed.

lemma dlist_djoin ['a] (d : 'a distr) n :
  dlist d n = djoin (nseq n d).
proof.
elim/natind: n.
- by move=> n le0_n; rewrite dlist0 // nseq0_le // djoin_nil.
- by move=> n ge0_n ih; rewrite dlistS // nseqS // djoin_cons ih.
qed.

lemma dmap_select ['a 'b 'c] z0 (d : 'a distr)
  p (r : 'c list) (idx : 'c -> int) (f : 'a list -> 'b)
:
  0 <= p => uniq r =>
  (forall i j, i \in r => j \in r => i <> j => idx i <> idx j) =>
  (forall i, i \in r => 0 <= idx i < p) =>
  is_lossless d =>
      dmap (dlist d p) (fun xs => f (map (nth z0 xs \o idx) r))
    = dmap (dlist d (size r)) f.
proof.
move=> ge0_p + + + ll_d; elim: p ge0_p r idx f
  => [|p ge0_p ih] r idx f uq_r inj_idx rg_idx.
- by rewrite (_ : r = []) 1:/# /= dlist0 // !dmap_dunit.
rewrite dlistS //= !dmap_comp.
case: (forall i, i \in r => idx i <> 0) => [h|].
- pose g xs := f (map (nth z0 xs \o (fun i => idx i - 1)) r).
  rewrite -(eq_dmap _ (fun xs : _ * _ => g xs.`2)) /=.
  - case=> y ys /= @/(\o) /=; pose s := map _ _.
    have ->//: s = map (fun i => nth z0 ys (idx i - 1)) r. 
    - by apply/eq_in_map => k k_r /=; rewrite (h k).
    by rewrite dmap_dprodE /= dletC //; apply: ih => //#.
rewrite negb_forall; case=> c0 /= /negb_imply /= [c0_r idx_c0].
pose i0 := index c0 r; pose idx' c := idx c - 1.
have ge0_i0: 0 <= i0 by apply/index_ge0.
have mem_remc0: forall c, c \in rem c0 r => c <> c0.
- move/perm_to_rem: c0_r => /perm_eq_uniq; rewrite uq_r /=.
  by move=> + c h - [+ _]; apply/contra => ->>.
have [us vs] [# rE ?? size_us]: exists us vs,
  r = us ++ c0 :: vs /\ !(c0 \in us) /\ !(c0 \in vs) /\ size us = i0.
- have := cat_take_drop i0 r; rewrite (drop_nth witness).
  - by rewrite ge0_i0 index_mem.
  rewrite nth_index // => /eq_sym ^rE ->.
  exists (take i0 r) (drop (i0+1) r) => /=.
  move: uq_r; rewrite {1}rE -cat1s catA uniq_catCA /=.
  case=> + _; rewrite mem_cat negb_or size_take //.
  by case=> -> -> /=; rewrite index_mem c0_r.
have remE: rem c0 r = (us ++ vs).
+ rewrite rem_filter // rE filter_cat /= {2}/predC1 /=.
  rewrite -!rem_filter ?rem_id //; move: uq_r;
    by rewrite rE cat_uniq /=.
have take_remc0: take i0 (rem c0 r) = take i0 r.
- rewrite remE take_cat size_us /= take0 cats0.
  by rewrite rE take_cat size_us /= cats0.
have drop_remc0: drop i0 (rem c0 r) = drop (i0+1) r.
- rewrite remE drop_cat size_us /= drop0 rE drop_cat.
  rewrite size_us /= (_ : (i0 + 1 < i0) = false) 1:/# /=.
  by rewrite (addzC _ 1) addrK /= drop0.
have drop_i0: drop i0 r = c0 :: drop (i0+1) r.
- rewrite rE !drop_cat size_us /= (_ : (i0 + 1 < i0) = false) 1:/# /=.
  by rewrite (addzC _ 1) addrK /= drop0.
pose F (x : 'a) (xs : 'a list) :=
  let s = map (nth z0 xs \o idx') (rem c0 r) in
  take i0 s ++ x :: drop i0 s.
pose G (x_xs : _ * _) := f (F x_xs.`1 x_xs.`2); rewrite -(eq_dmap _ G).
- case=> x xs @/G @/F @/(\o) /=; congr; apply/eq_sym.
  rewrite -(cat_take_drop i0 (map _ _)); congr.
  - rewrite -!map_take take_remc0; apply/eq_in_map.
    move=> c' /= c'_in; suff: idx c' <> 0 by smt().
    move: c'_in; rewrite -take_remc0 => /mem_take.
    by move=> ^/mem_rem ? /mem_remc0 /#.
  - rewrite -!map_drop drop_remc0 drop_i0 /= idx_c0 /=.
    apply/eq_in_map=> /= c ^/mem_drop c_r; rewrite drop_add //.
    rewrite rE drop_cat size_us /= drop0 => c_vs.
    by suff ->//: idx c <> 0; smt().
have ->: dmap (dlist d (size r)) f =
  dmap (d `*` (dlist d (size r - 1)))
    (fun xy : _ * _ => f (take i0 xy.`2 ++ xy.`1 :: drop i0 xy.`2)).
- pose n := size r; have ge0_r: 0 <= n by apply: size_ge0.
  have rg_i0: 0 <= i0 < n by rewrite index_ge0 index_mem.
  rewrite dlist_djoin {1}(_ : n = i0 + (1 + (n - 1 - i0))) 1:#ring.
  rewrite -cat_nseq 1,2:/# (addzC 1) nseqS 1:/#.
  rewrite djoin_perm_s1s /= dmap_dlet (dprodC d) dmap_comp; apply/eq_sym.
  rewrite dmap_dprodE {1}(_ : n - 1 = i0 + (n - 1 - i0)) 1:#ring.
  rewrite dlist_add 1,2:/# /= dlet_dmap -!dlist_djoin.
  apply: in_eq_dlet; case=> xs ys /supp_dprod => /=.
  case=> xs_in ys_in; have sz_xs: size xs = i0.
  - by apply: (supp_dlist_size _ _ _ _ xs_in) => /#.
  have sz_ys: size ys = n - 1 - i0.
  - by apply: (supp_dlist_size _ _ _ _ ys_in) => /#.
  rewrite dmap_comp; apply/eq_dmap => a @/(\o); congr=> /=.
  by rewrite take_cat sz_xs /= drop_cat sz_xs /= take0 drop0 cats0.
rewrite !dmap_dprodE &(eq_dlet) //= => a.
pose g xs := f (take i0 xs ++ a :: drop i0 xs).
have ->: size r - 1 = size (rem c0 r) by rewrite size_rem.
rewrite -(ih (rem c0 r) idx' g).
- by apply: rem_uniq.
- by move=> c1 c2 /mem_rem hc1 /mem_rem hc2 /#.
- by move=> c @/idx' ^/mem_rem c_r /mem_remc0 ne_c_c0 /#.
by apply: eq_dmap_in=> xs xs_in /#.
qed.

lemma dsim_dout (s t : t list) :
  uniq s => 
  (forall x, x \in t => x \in s) => 
  let n = size s + size t in
  dsim n n (s ++ t) = dout (s ++ t).
proof.
move=> uniq_s sub_ts n.
have ->: dout (s ++ t) =
  dmap (dout s) (fun s' => s' ++ map (fun i => nth zeror s' (index i s)) t).
- apply/eq_sym; apply/(@dmap_bij _ _ _ (take (size s))) => /=.
  - move=> xs /supp_dmap[vs [vs_dv ->>]] /=; apply/supp_dmap.
    exists vs; split=> //=; rewrite map_cat; congr=> //.
    apply: eq_in_map=> z z_in_t /=; rewrite (nth_map zeror) /=.
    - by rewrite index_ge0 /= index_mem sub_ts.
    by rewrite nth_index // sub_ts.
  - move=> xs /supp_dmap[vs [vs_dv ->>]]; rewrite !dmap1E.
    rewrite /(\o) /=; apply: mu_eq_support.
    move=> ws ws_dv @/pred1 /=; rewrite !map_cat take_cat.
    rewrite size_map /= take0 cats0; apply: eq_iff.
    split=> [|^eq <-]; first by rewrite eqseq_cat ?size_map.
    congr; apply/eq_in_map=> v /sub_ts v_in_s /=.
    move/(congr1 (nth zeror)): eq => /fun_ext /(_ (index v s)).
    by rewrite !(nth_map zeror) ?index_ge0 ?index_mem //= nth_index.
  - move=> vs /supp_dmap[ws [_ ->>]] /=; rewrite take_cat.
    by rewrite size_map /= take0 cats0.
  - move=> vs /supp_dmap[ws [_ ->>]]; rewrite map_cat take_cat.
    rewrite size_map /= take0 cats0; congr.
    apply: eq_in_map=> v /sub_ts v_in_s /=.
    by rewrite (nth_map zeror) ?index_ge0 ?index_mem //= nth_index.
pose k := size s.
have ->: dsim n n (s ++ t) =
  dmap (dsim n k (s ++ t)) (fun s' => s' ++ map (fun i => nth zeror s' (index i s)) t).
- apply/eq_sym; apply/(@dmap_bij _ _ _ (take k)) => /=.
  - move=> xs /supp_dmap[vs [vs_dv ->>]] /=; apply/supp_dmap.
    exists vs; split=> //=; rewrite {4}(range_cat k 0 n); 1,2: smt(size_ge0).
    rewrite map_cat; congr=> //.
    pose f := fun z : t =>
      BAdd.bigi predT (fun (j : int) => exp z j * nth zeror vs j) 0 n.
    apply/eq_sym; rewrite (map_comp f (fun i => nth zeror (s ++ t) i)).
    pose w := map _ (range k n); have ->: w = t.
    - rewrite /w (_ : n = n - k + k) 1:#ring range_addr /=.
      rewrite -map_comp /(\o) -{2}(map_nth_range zeror t).
      rewrite (_ : size t = n - k); 1: smt(). 
      apply: eq_in_map => i /mem_range rg_i /=.
      rewrite nth_cat /#.
    apply: eq_in_map=> x x_t @/f /=; rewrite (nth_map 0) /=.
    - rewrite index_ge0 /= size_range /=.
      rewrite IntOrder.ler_maxr; 1: smt(size_ge0).
      by rewrite index_mem sub_ts.
    apply: BAdd.eq_bigr=> i _ /=; do 2! congr.
    rewrite nth_range /=; first by
      rewrite index_ge0 index_mem sub_ts.
    by rewrite nth_cat index_mem sub_ts //= nth_index ?sub_ts.
  - move=> xs /supp_dmap[vs [vs_dv ->>]]; rewrite !dmap1E.
    rewrite /(\o) /=; apply: mu_eq_support.
    move=> ws ws_dv @/pred1 /=;
      rewrite {2 4 7}(range_cat k 0 n); 1,2: smt(size_ge0).
    rewrite !map_cat take_cat size_map size_range /=.
    rewrite IntOrder.ler_maxr /=; 1: smt(size_ge0).
    rewrite take0 cats0; apply: eq_iff.
    split=> [|^eq <-]; first by rewrite eqseq_cat ?size_map.
    congr; apply/eq_in_map=> v /= /mem_range rg_v /=.
    pose i0 := index (nth zeror (s ++ t) v) s.
    have rg_i0: 0 <= i0 < k.
    - rewrite index_ge0 /= /i0 nth_cat.
      rewrite (_ : !(v < size s)) 1:/# /=.
      by rewrite index_mem sub_ts mem_nth /= /#.
    move/(congr1 (nth zeror)): eq => /fun_ext /(_ i0).
    rewrite !(nth_map 0) ?index_ge0 ?index_mem //=;
      1,2: by rewrite size_range /= IntOrder.ler_maxr; smt(size_ge0).
    suff ->//: nth zeror (s ++ t) (nth 0 (range 0 k) i0)
      = nth zeror (s ++ t) v.
    rewrite nth_range //= nth_cat.
    rewrite (_ : (i0 < k)) 1:/# /= /i0 nth_index //.
    rewrite nth_cat (_ : !(v < k)) 1:/# /=.
    by apply/sub_ts; rewrite mem_nth; smt().
  - move=> vs /supp_dmap[ws [_ ->>]] /=; rewrite take_cat.
    rewrite size_map size_range IntOrder.ler_maxr /=; 1: smt(size_ge0).
    by rewrite take0 cats0.
  - move=> vs /supp_dmap[ws [_ ->>]].
    rewrite -map_take take_range0; 1: smt(size_ge0).
    rewrite {4}(range_cat k 0 n); 1,2: smt(size_ge0).
    rewrite map_cat; congr.
    pose f := fun z : t =>
      BAdd.bigi predT (fun (j : int) => exp z j * nth zeror ws j) 0 n.
    apply/eq_sym; rewrite (map_comp f (fun i => nth zeror (s ++ t) i)).
    pose w := map _ (range k n); have ->: w = t.
    - rewrite /w (_ : n = n - k + k) 1:#ring range_addr /=.
      rewrite -map_comp /(\o) -{2}(map_nth_range zeror t).
      rewrite (_ : size t = n - k); 1: smt().
      apply: eq_in_map => i /mem_range rg_i /=.
      rewrite nth_cat /#.
    apply: eq_in_map=> x x_t @/f /=; rewrite (nth_map 0) /=.
    - rewrite index_ge0 /= size_range /=.
      rewrite IntOrder.ler_maxr; 1: smt(size_ge0).
      by rewrite index_mem sub_ts.
    apply: BAdd.eq_bigr=> i _ /=; do 2! congr.
    rewrite nth_range /=; first by
      rewrite index_ge0 index_mem sub_ts.
    by rewrite nth_cat index_mem sub_ts //= nth_index ?sub_ts.
pose F x := map (fun i =>
  BAdd.bigi predT (fun j =>
    exp (nth zeror s i) j * nth zeror x j
  ) 0 k) (range 0 k).
congr; have ->: dout s = dmap (dlist dunifin k) F.
- rewrite vdmV // /dout /dv 
     (dmap_select zeror dunifin p s (fun x => index x enum) idfun).
  - smt(gt0_p). 
  - by apply: uniq_s.  
  + (* FIXME this should be a lemma *)
    move=> /= i j hi hj; apply contra => /(congr1 (nth witness enum)).
    by rewrite !nth_index // enumP.
  - smt (index_ge0 index_mem enumP).
  - by apply/dunifin_ll.
  by rewrite dmap_id.
rewrite /dsim {1}(_ : n = k + (n - k)) 1:#ring.
rewrite dlist_add /= 1,2:#smt:(size_ge0) dmap_comp dmap_dprodE_swap /(\o) /=.
pose G y c :=
  map (fun i => nth zeror c i +
    BAdd.bigi predT (fun j => exp (nth zeror (s ++ t) i) j * nth zeror y (j - k)
  ) k n) (range 0 k).
pose D y := dmap (dlist dunifin k) (fun x => G y (F x)).
rewrite -(eq_dlet D _ (dlist dunifin (n - k))) //.
- move=> vs @/D; apply/eq_dmap_in => ws ws_in /= @/G @/F /=.
  apply: eq_in_map => i /mem_range rg_i /=.
  rewrite (nth_map 0) /= ?size_range 1:/# nth_range 1:/# /=.
  pose H r d j := exp (nth zeror (s ++ t) i) j * nth zeror r (j - d).
  rewrite -(BAdd.eq_big_int _ _ (H (ws ++ vs) 0)).
  - move=> l rg_l @/H /=; congr; rewrite nth_cat.
    - by rewrite (_ : i < k) 1:/#.
    rewrite (supp_dlist_size _ _ _ _ ws_in); 1: smt(size_ge0).
    by rewrite (_ : l < k) 1:/#.
  rewrite addrC -(BAdd.eq_big_int _ _ (H (ws ++ vs) 0)).
  - move=> l rg_l @/H /=; congr; rewrite nth_cat.
    by rewrite (supp_dlist_size _ _ _ _ ws_in); smt(size_ge0).
  by rewrite addrC -BAdd.big_cat_int; 1,2: smt(size_ge0).
move=> @/D => {D}; pose D y := dmap (dmap (dlist dunifin k) F) (G y).
rewrite -(eq_dlet D _ (dlist dunifin (n - k))) //.
- by move=> vs @/D; rewrite dmap_comp.
move=> @/D => {D}.
have ->: dmap (dlist dunifin k) F = dlist dunifin k.
- by apply: vdmV.
pose d := dlist dunifin k.
rewrite -(eq_dlet (fun _ => d) _ (dlist dunifin (n - k))) //.
pose Gi y c :=
  map (fun i => nth zeror c i -
    BAdd.bigi predT (fun j => exp (nth zeror (s ++ t) i) j * nth zeror y (j - k)
  ) k n) (range 0 (size c)).
move=> vs; apply/eq_sym/(dmap_bij _ _ _ (Gi vs)).
- move=> ws _; apply/supp_dlist; 1: smt(size_ge0).
  rewrite size_map size_range; split; 1: smt(size_ge0).
  by apply/allP=> z _; apply: dunifin_fu.
- move=> ws _; case: (ws \in d).
  - move=> ws_d; apply: dlist_uni; 1: by apply/dunifin_uni.
    - apply/supp_dlist; 1: smt(size_ge0); split.
      - by apply: (supp_dlist_size _ _ _ _ ws_d); smt(size_ge0).
      - by apply/allP => ? _; apply/dunifin_fu.
    - apply/supp_dlist; 1: smt(size_ge0); split.
      rewrite size_map size_range /= IntOrder.ler_maxr ?size_ge0.
      have /supp_dlist_size<:t>: 0 <= k by smt(size_ge0).
      by move/(_ dunifin _ ws_d).
    - by apply/allP => ? _; apply/dunifin_fu.
  - move=> ^ws_d /supportPn => ->; apply/eq_sym/supportPn.
    apply: contra ws_d => vs_d; apply/supp_dlist; 1: smt(size_ge0); split.
    - have /supp_dlist_size<:t>: 0 <= k by smt(size_ge0).
      move/(_ dunifin _ vs_d); rewrite size_map.
      by rewrite size_range /= IntOrder.ler_maxr ?size_ge0.
    - by apply/allP=> ? _; apply/dunifin_fu.
- move=> ws ws_d @/Gi @/G; apply: (eq_from_nth zeror).
  - rewrite size_map size_range /= IntOrder.ler_maxr ?size_ge0.
    rewrite size_map size_range /= IntOrder.ler_maxr; 1: smt(size_ge0).
    apply/eq_sym/(supp_dlist_size _ _ _ _ ws_d); smt(size_ge0).
  rewrite !size_map !size_range /= IntOrder.ler_maxr; 1: smt(size_ge0). 
  move=> i rgi; rewrite (nth_map 0) ?size_range /=; 1: smt(size_ge0).
  rewrite nth_range //= (nth_map 0) ?size_range /=; 1: smt(size_ge0).
  by rewrite nth_range /=; 1: smt(size_ge0); rewrite addrK.
- move=> ws ws_d @/Gi @/G; apply: (eq_from_nth zeror).
  - rewrite size_map size_range /= (_ : max 0 k = k); 1: smt(size_ge0).
    apply/eq_sym/(supp_dlist_size _ _ _ _ ws_d); smt(size_ge0).
  rewrite size_map size_range /= (_ : max 0 k = k); 1: smt(size_ge0).
  move=> i rgi; rewrite (nth_map 0) ?size_range /=; 1: smt(size_ge0).
  rewrite nth_range //= (nth_map 0) ?size_range /=.
  - rewrite IntOrder.ler_maxr ?size_ge0.
    split=> [/#|_]; suff: size ws = k by smt().
    by apply/(supp_dlist_size _ _ _ _ ws_d); smt(size_ge0).
  rewrite nth_range //=; first suff: size ws = k by smt().
  - by apply/(supp_dlist_size _ _ _ _ ws_d); smt(size_ge0).
  by rewrite subrK.
by rewrite dletC // dlist_ll dunifin_ll.
qed.
