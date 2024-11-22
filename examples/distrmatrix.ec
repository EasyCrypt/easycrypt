(* -------------------------------------------------------------------- *)
require import AllCore List Distr DList Number StdOrder StdBigop.
require import IntDiv ZModP RealSeries.
require (*--*) DynMatrix.
(*---*) import IntOrder RealOrder RField Bigint Bigreal.

(* -------------------------------------------------------------------- *)
clone ZModRing as Zq.
clone import DynMatrix as DM with theory ZR = Zq.ZModpRing.
(*-*) import ZR.

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
op dadd (d1 d2 : R distr) : R distr =
  dmap (d1 `*` d2) (fun xy :  R * R => xy.`1 + xy.`2).

(* -------------------------------------------------------------------- *)
lemma dadd_sym (d1 d2 : R distr) : dadd d1 d2 = dadd d2 d1.
proof.
rewrite /dadd dmap_dprodE dmap_dprodE_swap /=.
rewrite &(eq_dlet) // => x /=; rewrite &(eq_dlet) // => y /=.
by rewrite addrC.
qed.

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
rewrite get_addm !get_offunm //= nth_mkseq //.
move: rgi rgj; rewrite !ler_maxr 1,2:// => rgi rgj.
split=> [|_]; first smt().
by apply: (IntOrder.ltr_le_trans ((c - 1) * r + r)) => //#.
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

(* -------------------------------------------------------------------- *)
op dmul1 (d1 d2 : R distr) : R distr =
  dmap (d1 `*` d2) (fun xy : R * R => xy.`1 * xy.`2).

(* -------------------------------------------------------------------- *)
lemma dmul0E (d1 d2 : R distr): dmul 0 d1 d2 = dunit zeror.
proof.
apply/eq_distr=> x; rewrite dunit1E.
rewrite dmap1E //= !dlist0 // dprod_dunit dunitE /=.
by rewrite Big.BAdd.big_nil.
qed.

(* -------------------------------------------------------------------- *)
lemma dmulE (n : int) (d1 d2 : R distr) : 0 <= n =>
  dmul n d1 d2 = iter n (fun d => dadd d (dmul1 d1 d2)) (dunit zeror).
proof.
elim: n => [| n ge0_n ih]; first by rewrite iter0 // dmul0E.
rewrite iterS //= -ih {1}/dmul !dlistS //=.
pose S (xs ys : R list) :=
  Big.BAdd.big predT (fun (xy : R * R) => xy.`1 * xy.`2) (zip xs ys).
pose C (x_xs : R * R list) := x_xs.`1 :: x_xs.`2.
pose F (x : R * R) (xs : R list * R list) := S (x.`1 :: xs.`1) (x.`2 :: xs.`2).
rewrite dmap_dprodE /=; have -> := dprod_dmap_cross
  d1 (dlist d1 n) d2 (dlist d2 n) C C S idfun idfun F _; first by done.
rewrite !dmap_id dadd_sym /dadd dmap_dprodE /dmul1 dlet_dmap /=.
rewrite &(eq_dlet) // => -[x y] /=; rewrite /dmul dmap_comp &(eq_dmap).
by case=> [/= xs ys] @/F @/S /=; rewrite Big.BAdd.big_consT.
qed.

(* -------------------------------------------------------------------- *)
import MRat.

lemma drat0 ['a] : drat<:'a> [] = dnull.
proof. by apply/eq_distr=> x; rewrite dratE dnull1E /=. qed.

lemma weight_drat ['a] (xs : 'a list) :
  weight (drat xs) = if xs = [] then 0%r else 1%r.
proof.
case: (xs = []) => [->>|nz_xs].
- by rewrite drat0 weight_dnull.
- by rewrite drat_ll.
qed.

lemma daddC ['a] (d1 d2 : 'a distr):
  weight d1 + weight d2 <= 1%r => d1 + d2 = d2 + d1.
proof. by move=> lew; apply/eq_distr=> c; rewrite !daddE // addrC. qed.

lemma dadd0d ['a] (d : 'a distr) : dnull + d = d.
proof.
apply/eq_distr => x; rewrite daddE.
- by rewrite weight_dnull /= &(le1_mu).
- by rewrite dnullE /=.
qed.

lemma daddd0 ['a] (d : 'a distr) : d + dnull = d.
proof. by rewrite daddC 1:weight_dnull /= 1:le1_mu // dadd0d. qed.

lemma dscalar0 ['a] (d : 'a distr) : 0%r \cdot d = dnull.
proof.
apply/eq_distr=> x; rewrite dscalar1E /= ?dnullE //.
- by rewrite invr_ge0 ge0_mu.
qed.

lemma drat_cat ['a] (xs ys : 'a list) :
  let c  = size xs + size ys in
  let cx = (size xs)%r / c%r in
  let cy = (size ys)%r / c%r in
  drat (xs ++ ys) = (cx \cdot (drat xs)) + (cy \cdot (drat ys)).
proof.
move=> c cx cy; case: (xs = []) => [->>| nz_xs] /=.
- rewrite drat0 dscalar0r dadd0d /cy /c /=.
  case: (ys = []) => [->>|nz_ys] /=; first by rewrite dscalar0 drat0.
  by rewrite divff ?dscalar1 // eq_fromint size_eq0.
case: (ys = []) => [->>|nz_ys] /=.
- rewrite drat0 dscalar0r daddd0 /cx /c /=.
  by rewrite divff ?dscalar1 // eq_fromint size_eq0.
apply: eq_distr=> z; rewrite daddE.
- by rewrite !weight_dscalar; smt(List.size_ge0 weight_drat).
rewrite !dscalar1E; 1,2: smt(List.size_ge0 weight_drat).
rewrite !dratE [cx * _]mulrCA [cy * _]mulrCA.
have ->: cx / (size xs)%r = inv (size (xs ++ ys))%r.
- by rewrite size_cat /cx /c mulrAC divff // eq_fromint size_eq0.
have ->: cy / (size ys)%r = inv (size (xs ++ ys))%r.
- by rewrite size_cat /cy /c mulrAC divff // eq_fromint size_eq0.
by rewrite -mulrDl -fromintD -count_cat.
qed.

lemma dratS ['a] (x : 'a) (xs : 'a list) :
  let c1 = 1%r / (1 + size xs)%r in
  let cs = (size xs)%r / (1 + size xs)%r in
  drat (x :: xs) = (c1 \cdot dunit x) + (cs \cdot (drat xs)).
proof. by move=> c1 cS; rewrite -cat1s; have /= -> := drat_cat [x] xs. qed.

lemma dprod0d ['a 'b] (d : 'b distr) : dnull<:'a> `*` d = dnull.
proof. by rewrite dprod_dlet dlet_dnull. qed.

lemma dprodd0 ['a 'b] (d : 'b distr) : d `*` dnull<:'a> = dnull.
proof. by rewrite dprod_dlet dlet_swap /= dlet_dnull. qed.

lemma dprodD ['a 'b] (da1 da2 : 'a distr) (db : 'b distr) :
  weight da1 + weight da2 <= 1%r =>
    (da1 + da2) `*` db = da1 `*` db + da2 `*` db.
proof.
move=> le1_w; apply/eq_distr => -[a b].
rewrite !(dprod1E, dadd1E) // -1:mulrDl //.
by rewrite !weight_dprod #smt:(ge0_mu le1_mu).
qed.

lemma dnullP ['a] (d : 'a distr) :
  (forall x, mu1 d x = 0%r) <=> (d = dnull).
proof.
split=> [|->>]; last by move=> x; rewrite dnull1E.
by move=> eq0; apply/eq_distr=> x; rewrite eq0 dnull1E.
qed.

lemma scalardA ['a 'b] (c : real) (d1 : 'a distr) (d2 : 'b distr) :
  0%r <= c <= 1%r / weight d1 => (c \cdot d1) `*` d2 = c \cdot (d1 `*` d2).
proof.
move=> /= rgc; case: (d1 = dnull) => [->>|nz_d1].
- by rewrite !(dscalar0r, dprod0d).
case: (d2 = dnull) => [->>|nz_d2].
- by rewrite !(dscalar0r, dprodd0).
have nz_wd1: weight d1 <> 0%r.
- by apply: contra nz_d1 => /weight_eq0 /dnullP.
have nz_wd2: weight d2 <> 0%r.
- by apply: contra nz_d2 => /weight_eq0 /dnullP.
apply/eq_distr=> -[a b]; rewrite !(dprod1E, dscalar1E) /= -1:mulrA //.
by rewrite weight_dprod; smt(ge0_mu le1_mu).
qed.

lemma dmap_drat ['a 'b] (f : 'a -> 'b) (xs : 'a list) :
  dmap (drat xs) f = drat (map f xs).
proof.
apply: eq_distr=> y; rewrite dratE dmap1E /(\o) /=.
rewrite size_map muE /= (sumE_fin _ (undup xs)) /=.
- by apply: undup_uniq.
- move=> x @/pred1; case: (f x = y) => // _.
  by move/supportP/supp_drat; rewrite mem_undup.
pose F (x : 'a) := (count (pred1 x) xs)%r / (size xs)%r.
rewrite -BRA.big_mkcond /= -(BRA.eq_bigr _ F) /F /= => {F}.
- by move=> x _; rewrite dratE.
rewrite -BRA.mulr_suml -Bigreal.sumr_ofint; do 2! congr.
by rewrite count_map big_count size_filter.
qed.

lemma dprod_drat ['a] (xs ys : 'a list) :
  drat xs `*` drat ys = drat (allpairs (fun x y => (x, y)) xs ys).
proof.
case: (ys = []) => [->>|nz_ys].
- by rewrite allpairs0r !drat0 dprodd0.
elim: xs => [|x xs ih]; first by rewrite drat0 dprod0d allpairs0l drat0.
have /= -> := dratS x xs; pose m := inv _; rewrite allpairs_consl.
pose s1 := map _ _; pose s2 := allpairs _ _ _.
have /= -> := drat_cat s1 s2; rewrite -ih.
rewrite !size_map !size_allpairs.
have ->: size ys + size xs * size ys = (1 + size xs) * (size ys) by ring.
rewrite !(fromintM, fromintD) !invfM mulrACA divff /= 1:#smt:(size_eq0).
rewrite invfM mulrCA divff /= 1:#smt:(size_eq0).
rewrite dprodD ?scalardA.
- rewrite !weight_dscalar.
  - smt(List.size_ge0).
  - by rewrite dunit_ll /= #smt:(List.size_ge0).
  - smt(List.size_ge0).
  - case: (xs = []) => [->>|nz_xs] /=.
    - by rewrite drat0 weight_dnull.
    - by rewrite drat_ll //= #smt:(List.size_ge0).
  rewrite dunit_ll /=; case: (xs = []) => [->>|nz_xs] /=.
  - smt(List.size_ge0 le1_mu).
  - by rewrite drat_ll //= #smt:(List.size_ge0).
- by rewrite dunit_ll /= #smt:(List.size_ge0).
- case: (xs = []) => [->>|nz_xs] /=.
  - by rewrite drat0 weight_dnull.
  - by rewrite drat_ll //= #smt:(List.size_ge0).
congr; last by congr => @/m; rewrite fromintD.
apply/eq_distr=> -[x1 x2]; rewrite !dscalar1E.
- by rewrite weight_dprod dunit_ll /= drat_ll //= #smt:(List.size_ge0).
- by rewrite -dmap_drat weight_dmap drat_ll //= #smt:(List.size_ge0).
rewrite dprod1E dunit1E /m fromintD; congr.
rewrite !dratE size_map  !mulrA; congr.
case: (x = x1) => [<<-|neq_x_x1] /=; last first.
- by rewrite count_pred0_eq_in // => -[a1 a2] /mapP[/=] /#.
by congr; rewrite count_map &(eq_count) /#.
qed.

lemma map_allpairs ['a 'b 'c 'd]
  (f : 'c -> 'd) (g : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list)
:
  map f (allpairs g xs ys) = allpairs (fun x y => f (g x y)) xs ys.
proof.
elim: xs => [|x xs ih] //=; rewrite !allpairs_consl map_cat /= ih.
by congr; rewrite -map_comp.
qed.

lemma dmul1_drat (xs ys : R list) :
  dmul1 (drat xs) (drat ys) = drat (allpairs (fun (x y : R) => x * y) xs ys).
proof.
rewrite /dmul1 dprod_drat dmap_drat /= &(perm_eq_drat).
by rewrite map_allpairs perm_eq_refl.
qed.

op dfreq ['a] (s : (int * 'a) list) =
  drat (flatten (map (fun xi : _ * _ => nseq xi.`1 xi.`2) s)).

op isfreq ['a] (s : (int * 'a) list) =
  forall (x : int * 'a), x \in s => 0 <= x.`1.

lemma allpairs_cat ['a 'b 'c] (f : 'a -> 'b -> 'c) (xs1 xs2 : 'a list) (ys : 'b list) :
  allpairs f (xs1 ++ xs2) ys = allpairs f xs1 ys ++ allpairs f xs2 ys.
proof.
elim: xs1 => [|x1 xs1 ih] /=; first by rewrite allpairs0l.
by rewrite !allpairs_consl ih catA.
qed.

lemma perm_cat ['a] (xs1 xs2 ys1 ys2 : 'a list) :
  perm_eq xs1 ys1 => perm_eq xs2 ys2 => perm_eq (xs1 ++ xs2) (ys1 ++ ys2).
proof.
move=> eqx eqy; apply: (perm_eq_trans (xs1 ++ ys2)).
- by apply/perm_cat2l. - by apply/perm_cat2r.
qed.

lemma flatten_nseq_nil ['a] (i : int) : flatten (nseq i []) = [<:'a>].
proof.
by elim/natind: i => [i le0_i|i ge0_i ih]; [rewrite nseq0_le | rewrite nseqS].
qed.

lemma map_constant ['a 'b] (s : 'a list) (b : 'b) :
  map (fun _ : 'a => b) s = nseq (size s) b.
proof.
elim: s => [|x s ih] /=; first by rewrite nseq0.
by rewrite [1+_]addzC nseqS.
qed.

lemma map_nseq ['a 'b] (f : 'a -> 'b) (n : int) (a : 'a) :
  map f (nseq n a) = nseq n (f a).
proof.
by elim/natind: n => [n le0_n|n ge0_n ih]; [rewrite !nseq0_le | rewrite !nseqS].
qed.

lemma dmul1_dfreq (xs ys : (int * R) list) : isfreq xs => isfreq ys =>
  dmul1 (dfreq xs) (dfreq ys)
    = dfreq (allpairs (fun (x y : int * R) => (x.`1 * y.`1, x.`2 * y.`2)) xs ys).
proof.
move=> okxs okys; rewrite /dfreq dmul1_drat &(perm_eq_drat).
elim: xs okxs => [|[i x] xs ih okxs] /=.
- by rewrite !(flatten_nil, allpairs0l) perm_eq_refl.
rewrite flatten_cons /= allpairs_cat allpairs_consl map_cat flatten_cat.
rewrite &(perm_cat) /=; last by apply/ih=> /#.
have {okxs ih}: 0 <= i by smt().
rewrite -map_comp /(\o) /=; elim: i => [|i ge0_i ih] /=.
- rewrite nseq0 allpairs0l perm_eq_refl_eq &(eq_sym).
  rewrite [map _ ys](_ : _ = map (fun _ => []) ys).
  - by apply: eq_map => /= *; rewrite nseq0.
  by rewrite map_constant flatten_nseq_nil.
rewrite nseqS // allpairs_consl; pose s := map _ _.
move: ih; rewrite -(perm_cat2l s) => /perm_eq_trans; apply.
move=> @/s => {s}; rewrite map_flatten /=.
elim: ys okys => [|y ys ih] okys /=; first by rewrite flatten_nil.
rewrite mulrDl /= -cat_nseq 1,2:/# !flatten_cons map_nseq.
rewrite perm_eq_sym perm_catCA -!catA perm_cat2l.
rewrite perm_eq_sym !catA perm_catCA -!catA perm_cat2l.
by apply: ih => /#.
qed.

op inject (ix : int * int) = (ix.`1, Zq.inzmod ix.`2).

lemma allpairs_map ['a 'a2 'b 'b2 'c]
  (f : 'a2 -> 'b2 -> 'c) (fa : 'a -> 'a2) (fb : 'b -> 'b2)
  (xs : 'a list) (ys : 'b list)
:
    allpairs f (map fa xs) (map fb ys)
  = allpairs (fun a b => f (fa a) (fb b)) xs ys.
proof.
elim: xs => [|x xs ih] //=.
by rewrite !allpairs_consl /= -ih -map_comp.
qed.

lemma dmul1_dfreq_int (xs ys : (int * int) list) : isfreq xs => isfreq ys =>
  dmul1 (dfreq (map inject xs)) (dfreq (map inject ys))
    = dfreq (map inject
        (allpairs (fun (x y : int * int) => (x.`1 * y.`1, (x.`2 * y.`2) %% Zq.p)) xs ys)).
proof.
move=> okxs okys; rewrite dmul1_dfreq.
- by case=> [i x] /mapP[/=] [j k] [?] [/= ->> _] /#.
- by case=> [i y] /mapP[/=] [j k] [?] [/= ->> _] /#.
congr; rewrite map_allpairs allpairs_map /=.
congr; apply/fun_ext2 => -[i zi] -[j zj] /=.
by rewrite /inject /= Zq.inzmodM_mod.
qed.

op frodo640 =
  let s = [8720; 7216; 5264; 3384; 1918; 958; 422; 164; 56; 17; 4; 1] in
  let s = mapi (fun (i v : int) => [(v, i); (v, -i)]) s in
  (9288, 0) :: flatten s.

op dfrodo640 : R distr = dfreq (map inject frodo640).

lemma isfreq_frodo640 : isfreq frodo640.
proof. by apply/allP. qed.

op zmod_cross (x y : int * int) / = (x.`1 * y.`1, (x.`2 * y.`2) %% Zq.p).

op zmod_add (x y : int * int) / = (x.`1 * y.`1, (x.`2 + y.`2) %% Zq.p).

op rinsert ['a] (i : int) (x : 'a) (xs : (int * 'a) list) =
  with xs = "[]" => [(i, x)]
  with xs = jx :: xs =>
    if   x = jx.`2
    then (i + jx.`1, x) :: xs
    else jx :: rinsert i x xs.

op reduce_r ['a] (acc : (int * 'a) list) (xs : (int * 'a) list) =
  with xs = "[]" => acc
  with xs = ix :: xs => reduce_r (rinsert ix.`1 ix.`2 acc) xs.

op reduce ['a] (xs : (int * 'a) list) / = reduce_r [] xs.

lemma dfreq_reduce ['a] (xs : (int * 'a) list) : dfreq (reduce xs) = dfreq xs.
proof. admitted.

lemma mapiE ['a 'b] f xs : mapi<:'a, 'b> f xs = mapi_rec<:'a, 'b> f xs 0.
proof. done. qed.

lemma iterS_minus ['a] (n : int) (f : 'a -> 'a) (x0 : 'a) :
  0 < n => iter n f x0 = iter (n-1) f (f x0).
proof. admitted.

hint simplify mapiE.
hint simplify flatten_nil, flatten_cons.
hint simplify allpairs0l, allpairs_consl.
hint simplify iter0, iterS_minus.

(*
lemma foo s : s =
  let dm = allpairs zmod_cross frodo640 frodo640 in
  let d  = [(1, 0)] in
  let d  = reduce (allpairs zmod_add d dm) in
  let d  = reduce (allpairs zmod_add d dm) in
  size d.
proof.
have pE: Zq.p = 32768 by admit.
rewrite /zmod_cross /zmod_add pE /frodo640.
pragma silent.
time cbv.
abort.
*)
