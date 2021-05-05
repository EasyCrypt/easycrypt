require import AllCore List Distr DList StdOrder IntDiv ZModP.
require (*--*) Matrix.

op p : { int | prime p } as prime_p.
op n : { int | 0 < n <= p } as gt0_n.
op k : { int | 0 < k <= n } as rg_k.

clone import ZModField
  with op p <- p proof prime_p by exact/prime_p.

import ZModpField.

clone Matrix as ZModMx_n with 
  type R         <- zmod,
    op size      <- n,

  pred ZR.unit   <- ZModField .unit,
    op ZR.zeror  <- ZModField .zero,
    op ZR.oner   <- ZModField .one,
    op ZR.( + )  <- ZModField .( + ),
    op ZR.([-])  <- ZModField .([-]),
    op ZR.( * )  <- ZModField .( * ),
    op ZR.invr   <- ZModField .inv,
    op ZR.intmul <- ZModpField.intmul,
    op ZR.ofint  <- ZModpField.ofint,
    op ZR.exp    <- ZModpField.exp,
    op ZR.lreg   <- ZModpField.lreg.

clone Matrix as ZModMx_k with 
  type R         <- zmod,
    op size      <- k,

  pred ZR.unit   <- ZModField .unit,
    op ZR.zeror  <- ZModField .zero,
    op ZR.oner   <- ZModField .one,
    op ZR.( + )  <- ZModField .( + ),
    op ZR.([-])  <- ZModField .([-]),
    op ZR.( * )  <- ZModField .( * ),
    op ZR.invr   <- ZModField .inv,
    op ZR.intmul <- ZModpField.intmul,
    op ZR.ofint  <- ZModpField.ofint,
    op ZR.exp    <- ZModpField.exp,
    op ZR.lreg   <- ZModpField.lreg.

import ZModMx_k.Big.

lemma duni_zmod_shift (d : zmod distr) (c : zmod) :
  is_funiform d => is_lossless d => dmap d (fun z => z + c) = d.
proof.
move=> funi_d ll_d; apply: (@dmap_bij _ _ _ (fun z => z - c)) => /=.
- by move=> v _; apply: funi_ll_full.
- by move=> v _; apply: funi_d.
- by move=> v _; rewrite addrK.
- by move=> v _; rewrite subrK.
qed.

op s, t : zmod list.

axiom size_s : size s = k.
axiom size_t : k + size t = n.
axiom uniq_s : uniq s.
axiom sub_ts : forall x, x \in t => x \in s.

axiom vdmV :
    dmap (dlist DZmodP.dunifin k)
      (fun vs => map (fun (i : int) =>
          (BAdd.bigi predT
            (fun (j : int) => exp (nth zero s i) j * nth zero vs j)
            0 k)) (range 0 k))
  = dlist DZmodP.dunifin k.

op dv =
  dlist DZmodP.dunifin p.

op dout r =
  dmap dv (fun v => map (fun i => nth zero v (asint i)) r).

op dsim k r =
  dmap (dlist DZmodP.dunifin n) (fun seed => map
    (fun i =>
      BAdd.bigi predT (fun j => exp (nth zero r i) j * nth zero seed j) 0 n)
    (range 0 k)).

lemma dletC ['a 'b] (da : 'a distr) (db : 'b distr) :
  is_lossless da => dlet da (fun _ => db) = db.
proof.
move=> ll; apply: eq_distr=> b; rewrite dlet1E /=.
rewrite RealSeries.sumZr -(RealSeries.eq_sum (mass da)).
- by move=> a; rewrite massE.
- by rewrite -weightE ll.
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

lemma dsim_dout : dsim n (s ++ t) = dout (s ++ t).
proof.
have ->: dout (s ++ t) =
  dmap (dout s) (fun s' => s' ++ map (fun i => nth zero s' (index i s)) t).
- apply/eq_sym; apply/(@dmap_bij _ _ _ (take k)) => /=.
  - move=> xs /supp_dmap[vs [vs_dv ->>]] /=; apply/supp_dmap.
    exists vs; split=> //=; rewrite map_cat; congr=> //.
    apply: eq_in_map=> z z_in_t /=; rewrite (nth_map zero) /=.
    - by rewrite index_ge0 /= index_mem sub_ts.
    by rewrite nth_index // sub_ts.
  - move=> xs /supp_dmap[vs [vs_dv ->>]]; rewrite !dmap1E.
    rewrite /(\o) /=; apply: mu_eq_support.
    move=> ws ws_dv @/pred1 /=; rewrite !map_cat take_cat.
    rewrite size_map size_s /= take0 cats0; apply: eq_iff.
    split=> [|^eq <-]; first by rewrite eqseq_cat ?size_map.
    congr; apply/eq_in_map=> v /sub_ts v_in_s /=.
    move/(congr1 (nth zero)): eq => /fun_ext /(_ (index v s)).
    by rewrite !(nth_map zero) ?index_ge0 ?index_mem //= nth_index.
  - move=> vs /supp_dmap[ws [_ ->>]] /=; rewrite take_cat.
    by rewrite size_map size_s /= take0 cats0.
  - move=> vs /supp_dmap[ws [_ ->>]]; rewrite map_cat take_cat.
    rewrite size_map size_s /= take0 cats0; congr.
    apply: eq_in_map=> v /sub_ts v_in_s /=.
    by rewrite (nth_map zero) ?index_ge0 ?index_mem //= nth_index.
have ->: dsim n (s ++ t) =
  dmap (dsim k (s ++ t)) (fun s' => s' ++ map (fun i => nth zero s' (index i s)) t).
- apply/eq_sym; apply/(@dmap_bij _ _ _ (take k)) => /=.
  - move=> xs /supp_dmap[vs [vs_dv ->>]] /=; apply/supp_dmap.
    exists vs; split=> //=; rewrite {4}(range_cat k 0 n); 1,2: smt(rg_k).
    rewrite map_cat; congr=> //.
    pose f := fun z : zmod =>
      BAdd.bigi predT (fun (j : int) => exp z j * nth zero vs j) 0 n.
    apply/eq_sym; rewrite (map_comp f (fun i => nth zero (s ++ t) i)).
    pose w := map _ (range k n); have ->: w = t.
    - rewrite /w (_ : n = n - k + k) 1:#ring range_addr /=.
      rewrite -map_comp /(\o) -{2}(map_nth_range zero t).
      rewrite (_ : size t = n - k); 1: smt(size_t).
      apply: eq_in_map => i /mem_range rg_i /=.
      rewrite nth_cat size_s /#.
    apply: eq_in_map=> x x_t @/f /=; rewrite (nth_map 0) /=.
    - rewrite index_ge0 /= size_range /=.
      rewrite IntOrder.ler_maxr; 1: smt(rg_k).
      by rewrite -size_s index_mem sub_ts.
    apply: BAdd.eq_bigr=> i _ /=; do 2! congr.
    rewrite nth_range /=; first by
      rewrite index_ge0 -size_s index_mem sub_ts.
    by rewrite nth_cat index_mem sub_ts //= nth_index ?sub_ts.
  - move=> xs /supp_dmap[vs [vs_dv ->>]]; rewrite !dmap1E.
    rewrite /(\o) /=; apply: mu_eq_support.
    move=> ws ws_dv @/pred1 /=;
      rewrite {2 4 7}(range_cat k 0 n); 1,2: smt(rg_k).
    rewrite !map_cat take_cat size_map size_range /=.
    rewrite IntOrder.ler_maxr /=; 1: smt(rg_k).
    rewrite take0 cats0; apply: eq_iff.
    split=> [|^eq <-]; first by rewrite eqseq_cat ?size_map.
    congr; apply/eq_in_map=> v /= /mem_range rg_v /=.
    pose i0 := index (nth zero (s ++ t) v) s.
    have rg_i0: 0 <= i0 < k.
    - rewrite index_ge0 /= -size_s /i0 nth_cat.
      rewrite {1}size_s (_ : !(v < k)) 1:/# /=.
      by rewrite index_mem sub_ts mem_nth /= size_s; smt(size_t).
    move/(congr1 (nth zero)): eq => /fun_ext /(_ i0).
    rewrite !(nth_map 0) ?index_ge0 ?index_mem //=;
      1,2: by rewrite size_range /= IntOrder.ler_maxr; smt(rg_k).
    suff ->//: nth zero (s ++ t) (nth 0 (range 0 k) i0)
      = nth zero (s ++ t) v.
    rewrite nth_range //= nth_cat size_s.
    rewrite (_ : (i0 < k)) 1:/# /= /i0 nth_index //.
    rewrite nth_cat size_s (_ : !(v < k)) 1:/# /=.
    by apply/sub_ts; rewrite mem_nth; smt(size_t).
  - move=> vs /supp_dmap[ws [_ ->>]] /=; rewrite take_cat.
    rewrite size_map size_range IntOrder.ler_maxr /=; 1: smt(rg_k).
    by rewrite take0 cats0.
  - move=> vs /supp_dmap[ws [_ ->>]].
    rewrite -map_take take_range0; 1: smt(rg_k).
    rewrite {4}(range_cat k 0 n); 1,2: smt(rg_k).
    rewrite map_cat; congr.
    pose f := fun z : zmod =>
      BAdd.bigi predT (fun (j : int) => exp z j * nth zero ws j) 0 n.
    apply/eq_sym; rewrite (map_comp f (fun i => nth zero (s ++ t) i)).
    pose w := map _ (range k n); have ->: w = t.
    - rewrite /w (_ : n = n - k + k) 1:#ring range_addr /=.
      rewrite -map_comp /(\o) -{2}(map_nth_range zero t).
      rewrite (_ : size t = n - k); 1: smt(size_t).
      apply: eq_in_map => i /mem_range rg_i /=.
      rewrite nth_cat size_s /#.
    apply: eq_in_map=> x x_t @/f /=; rewrite (nth_map 0) /=.
    - rewrite index_ge0 /= size_range /=.
      rewrite IntOrder.ler_maxr; 1: smt(rg_k).
      by rewrite -size_s index_mem sub_ts.
    apply: BAdd.eq_bigr=> i _ /=; do 2! congr.
    rewrite nth_range /=; first by
      rewrite index_ge0 -size_s index_mem sub_ts.
    by rewrite nth_cat index_mem sub_ts //= nth_index ?sub_ts.
pose F x := map (fun i =>
  BAdd.bigi predT (fun j =>
    exp (nth zero s i) j * nth zero x j
  ) 0 k) (range 0 k).
congr; have ->: dout s = dmap (dlist DZmodP.dunifin k) F.
- rewrite vdmV /dout /dv (dmap_select zero DZmodP.dunifin p s asint idfun).
  - smt(gt0_prime prime_p).
  - by apply: uniq_s.  
  - smt(asint_inj).
  - smt(gtp_asint ge0_asint).
  - by apply/DZmodP.dunifin_ll.
  by rewrite size_s dmap_id.
rewrite /dsim {1}(_ : n = k + (n - k)) 1:#ring.
rewrite dlist_add /= 1,2:[smt(rg_k)] dmap_comp dmap_dprodE_swap /(\o) /=.
pose G y c :=
  map (fun i => nth zero c i +
    BAdd.bigi predT (fun j => exp (nth zero (s ++ t) i) j * nth zero y (j - k)
  ) k n) (range 0 k).
pose D y := dmap (dlist DZmodP.dunifin k) (fun x => G y (F x)).
rewrite -(eq_dlet D _ (dlist DZmodP.dunifin (n - k))) //.
- move=> vs @/D; apply/eq_dmap_in => ws ws_in /= @/G @/F /=.
  apply: eq_in_map => i /mem_range rg_i /=.
  rewrite (nth_map 0) /= ?size_range 1:/# nth_range 1:/# /=.
  pose H r d j := exp (nth zero (s ++ t) i) j * nth zero r (j - d).
  rewrite -(BAdd.eq_big_int _ _ (H (ws ++ vs) 0)).
  - move=> l rg_l @/H /=; congr; rewrite nth_cat.
    - by rewrite size_s (_ : i < k) 1:/#.
    rewrite (supp_dlist_size _ _ _ _ ws_in); 1: smt(rg_k).
    by rewrite (_ : l < k) 1:/#.
  rewrite addrC -(BAdd.eq_big_int _ _ (H (ws ++ vs) 0)).
  - move=> l rg_l @/H /=; congr; rewrite nth_cat.
    by rewrite (supp_dlist_size _ _ _ _ ws_in); smt(rg_k).
  by rewrite addrC -BAdd.big_cat_int; 1,2: smt(rg_k).
move=> @/D => {D}; pose D y := dmap (dmap (dlist DZmodP.dunifin k) F) (G y).
rewrite -(eq_dlet D _ (dlist DZmodP.dunifin (n - k))) //.
- by move=> vs @/D; rewrite dmap_comp.
move=> @/D => {D}.
have ->: dmap (dlist DZmodP.dunifin k) F = dlist DZmodP.dunifin k.
- by apply: vdmV.
pose d := dlist DZmodP.dunifin k.
rewrite -(eq_dlet (fun _ => d) _ (dlist DZmodP.dunifin (n - k))) //.
pose Gi y c :=
  map (fun i => nth zero c i -
    BAdd.bigi predT (fun j => exp (nth zero (s ++ t) i) j * nth zero y (j - k)
  ) k n) (range 0 (size c)).
move=> vs; apply/eq_sym/(dmap_bij _ _ _ (Gi vs)).
- move=> ws _; apply/supp_dlist; 1: smt(rg_k).
  rewrite size_map size_range; split; 1: smt(rg_k).
  by apply/allP=> z _; apply: DZmodP.dunifin_fu.
- move=> ws _; case: (ws \in d).
  - move=> ws_d; apply: dlist_uni; 1: by apply/DZmodP.dunifin_uni.
    - apply/supp_dlist; 1: smt(rg_k); split.
      - by apply: (supp_dlist_size _ _ _ _ ws_d); smt(rg_k).
      - by apply/allP => ? _; apply/DZmodP.dunifin_fu.
    - apply/supp_dlist; 1: smt(rg_k); split.
      rewrite size_map size_range /= IntOrder.ler_maxr ?size_ge0.
      have /supp_dlist_size<:zmod>: 0 <= k by smt(rg_k).
      by move/(_ DZmodP.dunifin _ ws_d).
    - by apply/allP => ? _; apply/DZmodP.dunifin_fu.
  - move=> ^ws_d /supportPn => ->; apply/eq_sym/supportPn.
    apply: contra ws_d => vs_d; apply/supp_dlist; 1: smt(rg_k); split.
    - have /supp_dlist_size<:zmod>: 0 <= k by smt(rg_k).
      move/(_ DZmodP.dunifin _ vs_d); rewrite size_map.
      by rewrite size_range /= IntOrder.ler_maxr ?size_ge0.
    - by apply/allP=> ? _; apply/DZmodP.dunifin_fu.
- move=> ws ws_d @/Gi @/G; apply: (eq_from_nth zero).
  - rewrite size_map size_range /= IntOrder.ler_maxr ?size_ge0.
    rewrite size_map size_range /= IntOrder.ler_maxr; 1: smt(rg_k).
    apply/eq_sym/(supp_dlist_size _ _ _ _ ws_d); smt(rg_k).
  rewrite !size_map !size_range /= IntOrder.ler_maxr; 1: smt(rg_k). 
  move=> i rgi; rewrite (nth_map 0) ?size_range /=; 1: smt(rg_k).
  rewrite nth_range //= (nth_map 0) ?size_range /=; 1: smt(rg_k).
  by rewrite nth_range /=; 1: smt(rg_k); rewrite addrK.
- move=> ws ws_d @/Gi @/G; apply: (eq_from_nth zero).
  - rewrite size_map size_range /= (_ : max 0 k = k); 1: smt(rg_k).
    apply/eq_sym/(supp_dlist_size _ _ _ _ ws_d); smt(rg_k).
  rewrite size_map size_range /= (_ : max 0 k = k); 1: smt(rg_k).
  move=> i rgi; rewrite (nth_map 0) ?size_range /=; 1: smt(rg_k).
  rewrite nth_range //= (nth_map 0) ?size_range /=.
  - rewrite IntOrder.ler_maxr ?size_ge0.
    split=> [/#|_]; suff: size ws = k by smt().
    by apply/(supp_dlist_size _ _ _ _ ws_d); smt(rg_k).
  rewrite nth_range //=; first suff: size ws = k by smt().
  - by apply/(supp_dlist_size _ _ _ _ ws_d); smt(rg_k).
  by rewrite subrK.
by rewrite dletC // dlist_ll DZmodP.dunifin_ll.
qed.
