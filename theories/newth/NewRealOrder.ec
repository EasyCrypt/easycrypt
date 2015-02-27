(* -------------------------------------------------------------------- *)
require import NewIntCore NewRealCore.

(* -------------------------------------------------------------------- *)
lemma nosmt ler_norm_add (x y : real):
  `|x + y| <= `|x| + `|y|
by smt.

lemma nosmt addr_gt0 (x y : real):
  0%r < x => 0%r < y => 0%r < x + y
by smt.

lemma nosmt normr0_eq0 (x : real):
  `|x| = 0%r => x = 0%r
by smt.

lemma nosmt ger_leVge (x y : real):
  0%r <= x => 0%r <= y => (x <= y) \/ (y <= x)
by smt.

lemma nosmt normrM (x y : real):
  `|x * y| = `|x| * `|y|
by smt.

lemma nosmt ler_def (x y : real):
  (x <= y) <=> (`|y - x| = y - x)
by smt.

lemma nosmt ltr_def (x y : real):
  (x < y) <=> (y <> x) /\ (x <= y)
by smt.

lemma nosmt lerr (x : real):
  x <= x
by smt.

lemma nosmt ltrr (x : real):
  !(x < x)
by smt.

lemma nosmt ltrW (x y : real):
  x < y => x <= y
by smt.

lemma nosmt ltr_neqAle (x y : real):
  (x < y) <=> (x <> y) /\ (x <= y)
by smt.

lemma nosmt ler_eqVlt (x y : real):
  (x <= y) <=> (x = y) \/ (x < y)
by smt.

lemma nosmt lt0r (x : real):
  (0%r < x) <=> (x <> 0%r) /\ (0%r <= x)
by smt.

lemma nosmt le0r (x : real):
  (0%r <= x) <=> (x = 0%r) \/ (0%r < x)
by smt.

lemma nosmt lt0r_neq0 (x : real):
  0%r < x => (x <> 0%r)
by smt.

lemma nosmt ltr0_neq0 (x : real):
  0%r < x => (x <> 0%r)
by smt.

lemma nosmt gtr_eqF (x y : real):
  y < x => (x <> y)
by smt.

lemma nosmt ltr_eqF (x y : real):
  x < y => (x <> y)
by smt.

lemma nosmt pmulr_rgt0 (x y : real):
  0%r < x => (0%r < x * y) <=> (0%r < y)
by smt.

lemma nosmt pmulr_rge0 (x y : real):
  0%r < x => (0%r <= x * y) <=> (0%r <= y)
by smt.

lemma nosmt ler01:
  0%r <= 1%r 
by smt.

lemma nosmt ltr01:
  0%r < 1%r 
by smt.

lemma nosmt normr_idP (x : real):
  (`|x| = x) <=> (0%r <= x)
by smt.

lemma nosmt ger0_norm (x : real):
  0%r <= x => `|x| = x
by smt.

lemma nosmt normr0:
  `|0%r| = 0%r
by smt.

lemma nosmt normr1:
  `|1%r| = 1%r
by smt.

lemma nosmt normr0P (x : real):
  (`|x| = 0%r) <=> (x = 0%r)
by smt.

lemma nosmt normrN1:
  `|-1%r| = 1%r
by smt.

lemma nosmt normrN (x : real):
  `|- x| = `|x|
by smt.

lemma nosmt distrC (x y : real):
  `|x - y| = `|y - x|
by smt.

lemma nosmt ler0_def (x : real):
  (x <= 0%r) <=> (`|x| = - x)
by smt.

lemma nosmt normr_id (x : real):
  `| `|x| | = `|x|
by smt.

lemma nosmt normr_ge0 (x : real):
  0%r <= `|x|
by smt.

lemma nosmt ler0_norm (x : real):
  x <= 0%r => `|x| = - x
by smt.

lemma nosmt gtr0_norm (x : real):
  0%r < x => `|x| = x
by smt.

lemma nosmt ltr0_norm (x : real):
  x < 0%r => `|x| = - x
by smt.

lemma nosmt subr_ge0 (x y : real):
  (0%r <= y - x) = (x <= y)
by smt.

lemma nosmt subr_gt0 (x y : real):
  (0%r < y - x) <=> (x < y)
by smt.

lemma nosmt subr_le0 (x y : real):
  (y - x <= 0%r) <=> (y <= x)
by smt.

lemma nosmt subr_lt0 (x y : real):
  (y - x < 0%r) <=> (y < x)
by smt.

lemma nosmt ler_asym (x y : real):
  x <= y <= x => x = y
by smt.

lemma nosmt eqr_le (x y : real):
  (x = y) <=> (x <= y <= x)
by smt.

lemma nosmt ltr_trans (y x z : real):
  x < y => y < z => x < z
by smt.

lemma nosmt ler_lt_trans (y x z : real):
  x <= y => y < z => x < z
by smt.

lemma nosmt ltr_le_trans (y x z : real):
  x < y => y <= z => x < z
by smt.

lemma nosmt ler_trans (y x z : real):
  x <= y => y <= z => x <= z
by smt.

lemma nosmt addr_ge0 (x y : real):
  0%r <= x => 0%r <= y => 0%r <= x + y
by smt.

lemma nosmt ltr_asym (x y : real):
  ! (x < y < x)
by smt.

lemma nosmt ltr_le_asym (x y : real):
  ! (x < y <= x)
by smt.

lemma nosmt ler_lt_asym (x y : real):
  ! (x <= y < x)
by smt.

lemma nosmt ltr_geF (x y : real):
  x < y => ! (y <= x)
by smt.

lemma nosmt ler_gtF (x y : real):
  x <= y => ! (y < x)
by smt.

lemma nosmt ltr_gtF (x y : real):
  x < y => ! (y < x)
by smt.

lemma nosmt normr_le0 (x : real):
  (`|x| <= 0%r) <=> (x = 0%r)
by smt.

lemma nosmt normr_lt0 (x : real):
  ! (`|x| < 0%r)
by smt.

lemma nosmt normr_gt0 (x : real):
  (0%r < `|x|) <=> (x <> 0%r)
by smt.

lemma nosmt ler_oppr (x y : real):
  (x <= - y) <=> (y <= - x)
by smt.

lemma nosmt ltr_oppr (x y : real):
  (x < - y) <=> (y < - x)
by smt.

lemma nosmt ler_oppl (x y : real):
  (- x <= y) <=> (- y <= x)
by smt.

lemma nosmt ltr_oppl (x y : real):
  (- x < y) <=> (- y < x)
by smt.

lemma nosmt oppr_ge0 (x : real):
  (0%r <= - x) <=> (x <= 0%r)
by smt.

lemma nosmt oppr_gt0 (x : real):
  (0%r < - x) <=> (x < 0%r)
by smt.

lemma nosmt oppr_le0 (x : real):
  (- x <= 0%r) <=> (0%r <= x)
by smt.

lemma nosmt oppr_lt0 (x : real):
  (- x < 0%r) <=> (0%r < x)
by smt.

lemma nosmt ler_leVge (x y : real):
  x <= 0%r => y <= 0%r => (x <= y) \/ (y <= x)
by smt.

lemma nosmt ltr_add2r (z x y : real):
  (x + z < y + z) <=> (x < y)
by smt.

lemma nosmt ltr_add2l (z x y : real):
  (z + x < z + y) <=> (x < y)
by smt.

lemma nosmt ler_add (x y z t : real):
  x <= y => z <= t => x + z <= y + t
by smt.

lemma nosmt ler_lt_add (x y z t : real):
  x <= y => z < t => x + z < y + t
by smt.

lemma nosmt ltr_le_add (x y z t : real):
  x < y => z <= t => x + z < y + t
by smt.

lemma nosmt ltr_add (x y z t : real):
  x < y => z < t => x + z < y + t
by smt.

lemma nosmt ler_sub (x y z t : real):
  x <= y => t <= z => x - z <= y - t
by smt.

lemma nosmt ler_lt_sub (x y z t : real):
  x <= y => t < z => x - z < y - t
by smt.

lemma nosmt ltr_le_sub (x y z t : real):
  x < y => t <= z => x - z < y - t
by smt.

lemma nosmt ltr_sub (x y z t : real):
  x < y => t < z => x - z < y - t
by smt.

lemma nosmt ler_subl_addr (x y z : real):
  (x - y <= z) <=> (x <= z + y)
by smt.

lemma nosmt ltr_subl_addr (x y z : real):
  (x - y < z) <=> (x < z + y)
by smt.

lemma nosmt ler_subr_addr (x y z : real):
  (x <= y - z) <=> (x + z <= y)
by smt.

lemma nosmt ltr_subr_addr (x y z : real):
  (x < y - z) <=> (x + z < y)
by smt.

lemma nosmt ler_subl_addl (x y z : real):
  (x - y <= z) <=> (x <= y + z)
by smt.

lemma nosmt ltr_subl_addl (x y z : real):
  (x - y < z) <=> (x < y + z)
by smt.

lemma nosmt ler_subr_addl (x y z : real):
  (x <= y - z) <=> (z + x <= y)
by smt.

lemma nosmt ltr_subr_addl (x y z : real):
  (x < y - z) <=> (z + x < y)
by smt.

lemma nosmt ler_addl (x y : real):
  (x <= x + y) <=> (0%r <= y)
by smt.

lemma nosmt ltr_addl (x y : real):
  (x < x + y) <=> (0%r < y)
by smt.

lemma nosmt ler_addr (x y : real):
  (x <= y + x) <=> (0%r <= y)
by smt.

lemma nosmt ltr_addr (x y : real):
  (x < y + x) <=> (0%r < y)
by smt.

lemma nosmt ger_addl (x y : real):
  (x + y <= x) <=> (y <= 0%r)
by smt.

lemma nosmt gtr_addl (x y : real):
  (x + y < x) <=> (y < 0%r)
by smt.

lemma nosmt ger_addr (x y : real):
  (y + x <= x) <=> (y <= 0%r)
by smt.

lemma nosmt gtr_addr (x y : real):
  (y + x < x) <=> (y < 0%r)
by smt.

lemma nosmt ler_paddl (y x z : real):
  0%r <= x => y <= z => y <= x + z
by smt.

lemma nosmt ltr_paddl (y x z : real):
  0%r <= x => y < z => y < x + z
by smt.

lemma nosmt ltr_spaddl (y x z : real):
  0%r < x => y <= z => y < x + z
by smt.

lemma nosmt ltr_spsaddl (y x z : real):
  0%r < x => y < z => y < x + z
by smt.

lemma nosmt ler_naddl (y x z : real):
  x <= 0%r => y <= z => x + y <= z
by smt.

lemma nosmt ltr_naddl (y x z : real):
  x <= 0%r => y < z => x + y < z
by smt.

lemma nosmt ltr_snaddl (y x z : real):
  x < 0%r => y <= z => x + y < z
by smt.

lemma nosmt ltr_snsaddl (y x z : real):
  x < 0%r => y < z => x + y < z
by smt.

lemma nosmt ler_paddr (y x z : real):
  0%r <= x => y <= z => y <= z + x
by smt.

lemma nosmt ltr_paddr (y x z : real):
  0%r <= x => y < z => y < z + x
by smt.

lemma nosmt ltr_spaddr (y x z : real):
  0%r < x => y <= z => y < z + x
by smt.

lemma nosmt ltr_spsaddr (y x z : real):
  0%r < x => y < z => y < z + x
by smt.

lemma nosmt ler_naddr (y x z : real):
  x <= 0%r => y <= z => y + x <= z
by smt.

lemma nosmt ltr_naddr (y x z : real):
  x <= 0%r => y < z => y + x < z
by smt.

lemma nosmt ltr_snaddr (y x z : real):
  x < 0%r => y <= z => y + x < z
by smt.

lemma nosmt ltr_snsaddr (y x z : real):
  x < 0%r => y < z => y + x < z
by smt.

lemma nosmt paddr_eq0 (x y : real):
  0%r <= x => 0%r <= y => (x + y = 0%r) <=> (x = 0%r) /\ (y = 0%r)
by smt.

lemma nosmt naddr_eq0 (x y : real):
  x <= 0%r => y <= 0%r => (x + y = 0%r) <=> (x = 0%r) /\ (y = 0%r)
by smt.

lemma nosmt addr_ss_eq0 (x y : real):
        (0%r <= x  ) /\ (0%r <= y  )
     \/ (x   <= 0%r) /\ (y   <= 0%r)
  => (x + y = 0%r) <=> (x = 0%r) /\ (y = 0%r)
by smt.

lemma nosmt ler_pmul (x1 y1 x2 y2 : real):
  0%r <= x1 => 0%r <= x2 => x1 <= y1 => x2 <= y2 => x1 * x2 <= y1 * y2
by smt.

lemma nosmt ltr_pmul (x1 y1 x2 y2 : real):
  0%r <= x1 => 0%r <= x2 => x1 < y1 => x2 < y2 => x1 * x2 < y1 * y2
by smt.

lemma nosmt ltrN10:
  -1%r < 0%r 
by smt.

lemma nosmt lerN10:
  -1%r <= 0%r 
by smt.

lemma nosmt ltr0N1:
  !(0%r < -1%r)
by smt.

lemma nosmt ler0N1:
  !(0%r <= -1%r)
by smt.

lemma nosmt pmulr_rlt0 (x y : real):
  0%r < x => (x * y < 0%r) <=> (y < 0%r)
by smt.

lemma nosmt pmulr_rle0 (x y : real):
  0%r < x => (x * y <= 0%r) <=> (y <= 0%r)
by smt.

lemma nosmt pmulr_lgt0 (x y : real):
  0%r < x => (0%r < y * x) <=> (0%r < y)
by smt.

lemma nosmt pmulr_lge0 (x y : real):
  0%r < x => (0%r <= y * x) <=> (0%r <= y)
by smt.

lemma nosmt pmulr_llt0 (x y : real):
  0%r < x => (y * x < 0%r) <=> (y < 0%r)
by smt.

lemma nosmt pmulr_lle0 (x y : real):
  0%r < x => (y * x <= 0%r) <=> (y <= 0%r)
by smt.

lemma nosmt nmulr_rgt0 (x y : real):
  x < 0%r => (0%r < x * y) <=> (y < 0%r)
by smt.

lemma nosmt nmulr_rge0 (x y : real):
  x < 0%r => (0%r <= x * y) <=> (y <= 0%r)
by smt.

lemma nosmt nmulr_rlt0 (x y : real):
  x < 0%r => (x * y < 0%r) <=> (0%r < y)
by smt.

lemma nosmt nmulr_rle0 (x y : real):
  x < 0%r => (x * y <= 0%r) <=> (0%r <= y)
by smt.

lemma nosmt nmulr_lgt0 (x y : real):
  x < 0%r => (0%r < y * x) <=> (y < 0%r)
by smt.

lemma nosmt nmulr_lge0 (x y : real):
  x < 0%r => (0%r <= y * x) <=> (y <= 0%r)
by smt.

lemma nosmt nmulr_llt0 (x y : real):
  x < 0%r => (y * x < 0%r) <=> (0%r < y)
by smt.

lemma nosmt nmulr_lle0 (x y : real):
  x < 0%r => (y * x <= 0%r) <=> (0%r <= y)
by smt.

lemma nosmt mulr_ge0 (x y : real):
  0%r <= x => 0%r <= y => 0%r <= x * y
by smt.

lemma nosmt mulr_le0 (x y : real):
  x <= 0%r => y <= 0%r => 0%r <= x * y
by smt.

lemma nosmt mulr_ge0_le0 (x y : real):
  0%r <= x => y <= 0%r => x * y <= 0%r
by smt.

lemma nosmt mulr_le0_ge0 (x y : real):
  x <= 0%r => 0%r <= y => x * y <= 0%r
by smt.

lemma nosmt mulr_gt0 (x y : real):
  0%r < x => 0%r < y => 0%r < x * y
by smt.

lemma nosmt ger_pmull (x y : real):
  0%r < y => (x * y <= y) <=> (x <= 1%r)
by smt.

lemma nosmt gtr_pmull (x y : real):
  0%r < y => (x * y < y) <=> (x < 1%r)
by smt.

lemma nosmt ger_pmulr (x y : real):
  0%r < y => (y * x <= y) <=> (x <= 1%r)
by smt.

lemma nosmt gtr_pmulr (x y : real):
  0%r < y => (y * x < y) <=> (x < 1%r)
by smt.

lemma nosmt ler_nmull (x y : real):
  y < 0%r => (y <= x * y) <=> (x <= 1%r)
by smt.

lemma nosmt ltr_nmull (x y : real):
  y < 0%r => (y < x * y) <=> (x < 1%r)
by smt.

lemma nosmt ler_nmulr (x y : real):
  y < 0%r => (y <= y * x) <=> (x <= 1%r)
by smt.

lemma nosmt ltr_nmulr (x y : real):
  y < 0%r => (y < y * x) <=> (x < 1%r)
by smt.

lemma nosmt ler_pimull (x y : real):
  0%r <= y => x <= 1%r => x * y <= y
by smt.

lemma nosmt ler_nimull (x y : real):
  y <= 0%r => x <= 1%r => y <= x * y
by smt.

lemma nosmt ler_pimulr (x y : real):
  0%r <= y => x <= 1%r => y * x <= y
by smt.

lemma nosmt ler_nimulr (x y : real):
  y <= 0%r => x <= 1%r => y <= y * x
by smt.

lemma nosmt mulr_ile1 (x y : real):
  0%r <= x => 0%r <= y => x <= 1%r => y <= 1%r => x * y <= 1%r
by smt.

lemma nosmt mulr_ilt1 (x y : real):
  0%r <= x => 0%r <= y => x < 1%r => y < 1%r => x * y < 1%r
by smt.

lemma nosmt invr_gt0 (x : real):
  (0%r < inv x) <=> (0%r < x)
by smt.

lemma nosmt invr_ge0 (x : real):
  (0%r <= inv x) <=> (0%r <= x)
by smt.

lemma nosmt invr_lt0 (x : real):
  (inv x < 0%r) <=> (x < 0%r)
by smt.

lemma nosmt invr_le0 (x : real):
  (inv x <= 0%r) <=> (x <= 0%r)
by smt.

lemma nosmt divr_ge0 (x y : real):
  0%r <= x => 0%r <= y => 0%r <= x / y
by smt.

lemma nosmt divr_gt0 (x y : real):
  0%r < x => 0%r < y => 0%r < x / y
by smt.

lemma nosmt ler_norm_sub (x y : real):
  `|x - y| <= `|x| + `|y|
by smt.

lemma nosmt ler_dist_add (z x y : real):
  `|x - y| <= `|x - z| + `|z - y|
by smt.

lemma nosmt ler_sub_norm_add (x y : real):
  `|x| - `|y| <= `|x + y|
by smt.

lemma nosmt ler_sub_dist (x y : real):
  `|x| - `|y| <= `|x - y|
by smt.

lemma nosmt ler_dist_dist (x y : real):
  `| `|x| - `|y| | <= `|x - y|
by smt.

lemma nosmt ler_dist_norm_add (x y : real):
  `| `|x| - `|y| | <= `|x + y|
by smt.

lemma nosmt ler_nnorml (x y : real):
  y < 0%r => ! (`|x| <= y)
by smt.

lemma nosmt ltr_nnorml (x y : real):
  y <= 0%r => ! (`|x| < y)
by smt.

lemma nosmt eqr_norm_id (x : real):
  (`|x| = x) <=> (0%r <= x)
by smt.

lemma nosmt eqr_normN (x : real):
  (`|x| = - x) <=> (x <= 0%r)
by smt.
