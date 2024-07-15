(* -------------------------------------------------------------------- *)
require import AllCore List Distr DList Number StdOrder StdBigop.
require import RealSeries.
require (*--*) DynMatrix.
(*---*) import IntOrder RealOrder RField Bigint Bigreal.

(* -------------------------------------------------------------------- *)
clone import DynMatrix as DM.
(*-*) import DM.ZR.

(* -------------------------------------------------------------------- *)
abbrev "_.[_]" ['a] (xs : 'a list) (i : int) = nth<:'a> witness xs i.

(* -------------------------------------------------------------------- *)
lemma compE ['a 'b 'c] (f : 'a -> 'b) (g : 'b -> 'c) (x : 'a) :
  (g \o f) x = g (f x).
proof. done. qed.

hint simplify compE.

(* -------------------------------------------------------------------- *)
lemma dlist_ubound (n : int) (d : R distr) (E : R -> bool) : 0 <= n =>
  mu
    (dlist d n)
    (fun xs => exists i, 0 <= i < n /\ E xs.[i])
  <= n%r * mu d E.
proof.
elim: n => /= [|n ge0_n ih]; first by rewrite dlist0 // dunitE //#.
rewrite dlistS //= dmapE /(\o) /=.
pose P1 (x : R) := E x.
pose P2 (xs : R list) := exists i, (0 <= i < n /\ E xs.[i]).
pose P (x_xs : R * R list) := P1 x_xs.`1 \/ P2 x_xs.`2.
rewrite (mu_eq_support _ _ P).
- case=> [x xs] /supp_dprod /= [_].
  case/(supp_dlist _ _ _ ge0_n) => [sz_xs _].
  rewrite /P /=; apply/eq_iff; split; first smt().
  case=> [Ex|]; first exists 0; smt().
  by case=> i rg_i; exists (i+1) => //#.
apply: (ler_trans _ _ _ (le_dprod_or _ _ _ _)).
rewrite fromintD mulrDl /= addrC ler_add.
- by apply: (ler_trans _ _ _ (ler_pimulr _ _ _ _)).
- by apply: (ler_trans _ _ _ (ler_pimulr _ _ _ _)).
qed.

(* -------------------------------------------------------------------- *)
op dadd (d1 d2 : R distr) =
  dmap (d1 `*` d2) (fun xy :  R * R => xy.`1 + xy.`2).

(* -------------------------------------------------------------------- *)
lemma dlistD (n : int) (d1 d2 : R distr) : 0 <= n =>
    dlet (dlist d1 n) (fun (xs : R list) =>
    dmap (dlist d2 n) (fun (ys : R list) =>
      mkseq (fun i => xs.[i] + ys.[i]) n))
  = dlist (dadd d1 d2) n.
proof.
pose S n (xs ys : R list) := mkseq (fun i => xs.[i] + ys.[i]) n.
pose T n (xs : R list * R list) := S n xs.`1 xs.`2.
move=> ge0_n; rewrite -(dmap_dprodE _ _ (T n)). (* SLOW *)
elim: n ge0_n => /= [|n ge0_n ih]; last rewrite !dlistS //.
- by rewrite !dlist0 // dprod_dunit dmap_dunit /T /S /= mkseq0.
pose C (x_xs : R * R list) := x_xs.`1 :: x_xs.`2.
pose F (x : R * R) (xs : R list * R list) :=
  S (n+1) (x.`1 :: xs.`1) (x.`2 :: xs.`2).
pose G (xs ys : R list) := S (n+1) xs ys. 
rewrite dmap_dprodE; have -> := dprod_dmap_cross
  d1 (dlist d1 n) d2 (dlist d2 n) C C G idfun idfun F _; first by done.
rewrite !dmap_id /= dmap_dprodE {1}/dadd dlet_dmap.
apply/eq_dlet => // -[x y] /=; rewrite -ih.
rewrite dmap_comp &(eq_dmap) => -[xs ys] /=.
by rewrite /F /S /C /T /= mkseqSr //= &(eq_in_mkseq) //#.
qed.

(* -------------------------------------------------------------------- *)
lemma dmatrix_dlist (r c : int) (d : R distr) :
  0 <= r => 0 <= c => dmatrix d r c =
    dmap
      (dlist d (r * c))
      (fun vs => offunm ((fun i j => vs.[j * r + i]), r, c)).
proof.
move=> ge0_r ge0_c @/dmatrix @/dvector.
rewrite dlist_dmap dmap_comp !lez_maxr //.
rewrite -dlist_dlist // dmap_comp &(eq_dmap_in) => xss /=.
case/(supp_dlist _ _ _ ge0_c) => size_xss /allP xssE.
have {xssE} xssE: forall xs, xs \in xss => size xs = r.
- by move=> xs /xssE /(supp_dlist _ _ _ ge0_r).
apply/eq_matrixP=> @/ofcols /= i j [].
rewrite !lez_maxr // => rgi rgj.
rewrite !get_offunm /= ?lez_maxr //.
rewrite (nth_map witness) 1:/#.
rewrite (get_oflist witness) 1:#smt:(mem_nth).
rewrite -nth_flatten ~-1:#smt:(mem_nth); do 2! congr.
rewrite sumzE BIA.big_map predT_comp /(\o) /=.
pose D := BIA.big predT (fun _ => r) (take j xss).
apply: (eq_trans _ D) => @/D.
- rewrite !BIA.big_seq &(BIA.eq_bigr) //=.
  by move=> xs /mem_take /xssE.
by rewrite big_constz count_predT size_take //#.
qed.

(* -------------------------------------------------------------------- *)
lemma dmatrixD (r c : int) (d1 d2 : R distr) : 0 <= r => 0 <= c =>
    dlet (dmatrix d1 r c) (fun (m1 : matrix) =>
    dmap (dmatrix d2 r c) (fun (m2 : matrix) => m1 + m2))
  = dmatrix (dadd d1 d2) r c.
proof.
move=> ge0_r ge0_c; rewrite 2?dmatrix_dlist //=.
pose F vs := offunm (fun i j => vs.[j * r + i], r, c).
rewrite dlet_dmap /= dlet_swap dlet_dmap /= dlet_swap /=.
rewrite dmatrix_dlist // -/F -dlistD ~-1:/#.
rewrite dmap_dlet &(eq_dlet) // => xs /=.
rewrite dlet_dunit dmap_comp &(eq_dmap) => ys /=.
apply/eq_matrixP; split.
- by rewrite /F size_addm !size_offunm.
move=> i j []; rewrite rows_addm cols_addm /=.
rewrite !rows_offunm !cols_offunm !maxzz => rgi rgj.
by rewrite get_addm !get_offunm //= nth_mkseq //#.
qed.

(* -------------------------------------------------------------------- *)
op dmul (n : int) (d1 d2 : R distr) =
  dmap
    (dlist d1 n `*` dlist d2 n)
    (fun vs : R list * R list =>
       DM.Big.BAdd.big predT
         (fun xy : R * R => xy.`1 * xy.`2)
         (zip vs.`1 vs.`2)).

(* -------------------------------------------------------------------- *)
lemma dmatrix_cols (d : R distr) (r c : int) : 0 <= c => 0 <= r =>
  dmatrix d r c = dmap (dlist (dvector d r) c) (ofcols r c).
proof. by move=> ge0_c ge0_r @/dmatrix; rewrite lez_maxr. qed.

(* -------------------------------------------------------------------- *)
lemma dmatrix_rows (d : R distr) (r c : int) : 0 <= c => 0 <= r =>
  dmatrix d r c = dmap (dlist (dvector d c) r) (trmx \o ofcols c r).
proof.
move=> ge0_r ge0_c; rewrite -dmap_comp -dmatrix_cols //.
apply/eq_distr => /= m; rewrite (dmap1E _ trmx).
have ->: pred1 m \o trmx = pred1 (trmx m) by smt(trmxK).
case: (size m = (r, c)); last first.
- by move=> ne_size; rewrite !dmatrix0E //#.
case=> <<- <<-; rewrite -{2}rows_tr -{2}cols_tr !dmatrix1E /=.
by rewrite BRM.exchange_big.
qed.

(* -------------------------------------------------------------------- *)
hint simplify drop0, take0, cats0, cat0s.

(* -------------------------------------------------------------------- *)
lemma dmatrix_cols_i (i : int) (d : R distr) (r c : int) :
  0 <= c => 0 <= r => 0 <= i < c =>
    dmatrix d r c =
      dmap
        (dvector d r `*` dlist (dvector d r) (c-1))
        (fun c_cs : _ * _ => ofcols r c (insert c_cs.`1 c_cs.`2 i)).
proof.
move=> ge0_c ge0_r rgi; rewrite dmatrix_cols //.
rewrite {1}(_ : c = (c - 1) + 1) // (dlist_insert witness i) ~-1://# /=.
by rewrite dmap_comp &(eq_dmap) => -[v vs].
qed.

(* -------------------------------------------------------------------- *)
lemma dmatrix_rows_i (j : int) (d : R distr) (r c : int) :
  0 <= c => 0 <= r => 0 <= j < r =>
    dmatrix d r c =
      dmap
        (dvector d c `*` dlist (dvector d c) (r-1))
        (fun r_rs : _ * _ => trmx (ofcols c r (insert r_rs.`1 r_rs.`2 j))).
proof.
move=> ge0_c ge0_r rgj; rewrite dmatrix_rows //.
rewrite {1}(_ : r = (r - 1) + 1) // (dlist_insert witness j) ~-1://# /=.
by rewrite dmap_comp &(eq_dmap) => -[v vs].
qed.

(* -------------------------------------------------------------------- *)
lemma col_ofcols (i r c : int) (vs : vector list) :
     0 <= r => 0 <= c => 0 <= i < c
  => size vs = c
  => all (fun v : vector => size v = r) vs
  => col (ofcols r c vs) i = vs.[i].
proof.
move=> ge0_r ge0_c rgi sz_vs /allP => sz_in_vs.
have sz_rows: rows (ofcols r c vs) = r.
- by rewrite rows_offunm lez_maxr // sz_in_vs.
apply/eq_vectorP; split=> /=.
- by rewrite sz_rows sz_in_vs // &(mem_nth) sz_vs.
by move=> j; rewrite sz_rows => rgj; rewrite get_offunm //#.
qed.

(* -------------------------------------------------------------------- *)
lemma dmatrixM (m n p : int) (d1 d2 : R distr) :
  0 <= m => 0 <= n => 0 <= p =>

  let d =
    dlet (dmatrix d1 m n) (fun (m1 : matrix) =>
    dmap (dmatrix d2 n p) (fun (m2 : matrix) => m1 * m2)) in

  forall i j, 0 <= i < m => 0 <= j < p =>
    dmap d (fun m => m.[i, j]) =
      ((weight d1) ^ (n * (m-1)) * (weight d2) ^ (n * (p-1))) \cdot dmul n d1 d2.
proof.
move=> ge0_m ge0_n ge0_p d i j rg_i rg_j.
have [gt0_m gt0_p]: (0 <= m-1) /\ (0 <= p-1) by smt().
rewrite /d (dmatrix_rows_i i) //= (dmatrix_cols_i j) //=.
pose D1 := dvector d1 n `*` _; pose D2 := dvector d2 n `*` _.
pose F1 := fun (r_rs : _ * _) => trmx (ofcols n m (insert r_rs.`1 r_rs.`2 i)).
pose F2 := fun (c_cs : _ * _) => ofcols n p (insert c_cs.`1 c_cs.`2 j).
pose F r rs c cs := (trmx (ofcols n m (insert r rs i)) * ofcols n p (insert c cs j)).[i, j].
pose D := dlet D1 (fun c : _ * _ => dmap D2 (fun r : _ * _ => F c.`1 c.`2 r.`1 r.`2)).
apply: (eq_trans _ D) => @/D => {D}.
- rewrite dmap_dlet dlet_dmap /= &(eq_dlet) // => ? /=.
  by rewrite 2!dmap_comp &(eq_dmap).
pose G (x_xs : (_ * _) * (_ * _)) := F x_xs.`1.`1 x_xs.`2.`1 x_xs.`1.`2 x_xs.`2.`2.
rewrite dprod_cross /= => {D1 D2}; pose D1 := _ `*` _; pose D2 := _ `*` _.
have @/G /= <- := dmap_dprodE D1 D2 G => {G}.
pose G (vs : vector * vector) := dotp vs.`1 vs.`2.
apply: (eq_trans _ (dmap (D1 `*` D2) (fun x : _ * _ => G x.`1))).
- apply: eq_dmap_in=> -[[c r] [cs rs]] @/G @/F /=.
  case/supp_dprod=> /= /supp_dprod[/=].
  case/(supp_dvector _ _ _ ge0_n) => sz_c _.
  case/(supp_dvector _ _ _ ge0_n) => sz_r _.
  move/supp_dprod=> [/=].
  case/(supp_dlist _ _ _ gt0_m) => [sz_cs /allP sz_in_cs].
  case/(supp_dlist _ _ _ gt0_p) => [sz_rs /allP sz_in_rs].
  rewrite get_mulmx row_trmx /= !col_ofcols //.
  - by rewrite size_insert ?sz_cs //#.
  - apply/allP=> v /mem_insert [->>|] //=.
    by move/sz_in_cs => /(supp_dvector _ _ _ ge0_n).
  - by rewrite size_insert ?sz_rs //#.
  - apply/allP=> v /mem_insert [->>|] //=.
    by move/sz_in_rs => /(supp_dvector _ _ _ ge0_n).
  by rewrite !nth_insert // (sz_cs, sz_rs) //#.
rewrite dprod_marginalL /D2 weight_dprod !weight_dlist // !weight_dmap.
rewrite !weight_dlist ?lez_maxr // -!exprM.
congr=> @/D1 @/G => {D1 D2 G} @/dmul.
rewrite !dmap_dprodE /= dlet_dmap lez_maxr //.
apply/in_eq_dlet => //= xs /(supp_dlist _ _ _ ge0_n)[sz_xs _].
rewrite dmap_comp lez_maxr //; apply/eq_dmap_in => /= ys.
case/(supp_dlist _ _ _ ge0_n)=> sz_ys _ @/dotp.
rewrite !size_oflist sz_xs sz_ys lez_maxr //.
apply/eq_sym; rewrite (Big.BAdd.big_nth witness) predT_comp.
rewrite size_zip sz_xs sz_ys lez_minr //.
rewrite !Big.BAdd.big_seq /= &(Big.BAdd.eq_bigr) /=.
move=> k /mem_range rg_k; rewrite !(get_oflist witness) ~-1://#.
have := nth_zip witness witness xs ys k _; first by smt().
by rewrite (nth_change_dfl witness) => [|->//]; rewrite size_zip /#.
qed.

(* -------------------------------------------------------------------- *)
lemma dmatrixM_ll (m n p : int) (d1 d2 : R distr) :
  0 <= m => 0 <= n => 0 <= p =>

  is_lossless d1 => is_lossless d2 =>

  let d =
    dlet (dmatrix d1 m n) (fun (m1 : matrix) =>
    dmap (dmatrix d2 n p) (fun (m2 : matrix) => m1 * m2)) in

  forall i j, 0 <= i < m => 0 <= j < p =>
    dmap d (fun m => m.[i, j]) = dmul n d1 d2.
proof.
move=> *; rewrite dmatrixM //; pose c := (_ * _)%Real.
rewrite (_ : c = 1%r) -1:dscalar1 // /c.
by do 2! rewrite (_ : weight _ = 1%r) // expr1z.
qed.
