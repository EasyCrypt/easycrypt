require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.

require Partition.

clone import Partition as Partition0.



lemma sumidE_rm (m n : int) : m <= n =>
   2 * sumid m n = (n-m) * (n + m - 1).
proof.
  move=> h.
  rewrite -{1}(add0r m) BIA.big_addn /= BIA.big_split /predT.
  have hnm : 0 <= n - m by smt().
  rewrite !Num.Domain.mulrDr sumidE_r 1://.
  rewrite bigi_constz 1://; ring.
qed.

(* cost less-th-an *)
op clt = 1.

lemma clt_ge0 : 0 <= clt.
proof. done. qed.

module QS = {
  var c : int

  proc swap_(t : elem array, i j : int) : elem array = {
    var aux;
    aux <- t.[i];
    t.[i] <- t.[j];
    t.[j] <- aux;
    return t;
  }

  proc partition(t : elem array, lo hi : int ) : elem array * int = {
    var pv, i, j;
    pv <- t.[hi];
    i <- lo - 1;
    j <- lo;
    while (j < hi) { 
      if (t.[j] < pv) {
        i <- i + 1;
        t <@ swap_(t, i, j);
      }
      c <- c + clt;
      j <- j + 1;
    }
    i <- i + 1;
    t <@ swap_(t, i, hi);
    return (t, i);
  }
  
  proc p_partition(t : elem array, lo hi : int) : elem array * int = {
    var p;
    p <$ [lo .. hi];
    t <@ swap_(t, p, hi);
    (t, p) <@ partition(t, lo, hi);
    return (t,p);
  }

  proc qselect(t : elem array, pos: int) : elem = {
    var lo, hi, p : int;
    c <- 0;
    lo <- 0;
    hi <- size t - 1;
    p <- 0;
    while (lo < hi) {
      (t, p) <@ p_partition(t, lo, hi);
      if (p = pos) { lo <- p; hi <- p; }
      else { if (p < pos) lo <- p + 1; else hi <- p - 1; }
    }
    return t.[pos];
  }

  proc p_partition_abs(lo hi : int) : int = {
    var p;
    p <$ [lo .. hi];
    c <- c + (hi - lo) * clt;
    return p;
  }

  proc qselect_abs(t : elem array, pos: int) = {
    var lo, hi, p : int;
    c <- 0;
    lo <- 0;
    hi <- size t - 1;
    p <- 0;
    while (lo < hi) {
      p <@ p_partition_abs(lo, hi);
      if (p = pos) { lo <- p; hi <- p; }
      else { if (p < pos) lo <- p + 1; else hi <- p - 1; }
    }
  }

}.

import var QS.

hoare h_swap t_ i_ j_ c_ : QS.swap_ : 
     t = t_ /\ i = i_ /\ j = j_ /\ c = c_ /\ 0 <= i < size t /\ 0 <= j < size t 
     ==>
     c = c_ /\ swapP t_ res i_ j_.
proof. by proc; auto => />; smt (get_set size_set). qed.

phoare h_swap_ll t_ i_ j_ c_ : [QS.swap_ : 
     t = t_ /\ i = i_ /\ j = j_ /\ c = c_ /\ 0 <= i < size t /\ 0 <= j < size t 
     ==>
     c = c_ /\ swapP t_ res i_ j_] = 1%r.
proof. by conseq (_: true ==> true) (h_swap t_ i_ j_ c_) => //; islossless. qed.

hoare h_partition (t_ : elem array) (c_ lo_ hi_ : int) : QS.partition :
    c = c_ /\ t = t_ /\ lo = lo_ /\ hi = hi_ /\ 0 <= lo <= hi < size t
    ==>
    let (t,p) = (res.`1, res.`2) in 
    perm_eq_on t_ t lo_ hi_ /\ partition_on t lo_ p hi_ /\ t.[p] = t_.[hi_] /\ lo_ <= p <= hi_ /\
    (* This is needed for for function correctness of qselect, only equality on size is needed for complexity *)
    eq_except t_ t lo_ hi_ /\  
    (* Only needed for complexity *)
    c = c_ + (hi_ - lo_) * clt.
proof.
  proc; ecall (h_swap t i hi c). wp.
  while ((forall k, 0 <= k < size t_ => 
         if lo <= k < j then 
           if k <= i then t.[k] < pv
           else pv <= t.[k]
         else t.[k] = t_.[k]) /\ 
         0 <= lo /\ i < j /\ lo <= i + 1 /\    
         lo <= j <= hi < size t /\ eq_except t_ t lo hi /\ 
         perm_eq_on t_ t lo hi /\ t.[hi] = pv /\
         c = c_ + (j - lo) * clt).
  + wp; if; last by skip => />; smt(clt_ge0 lt_nle).
    ecall (h_swap t i j c); wp; skip => |>.
    move=> &hr 8? hpe *; split; 1: smt().
    move=> 4? t' *; rewrite 4!andbA; split; 1: smt().
    split; 2: smt().
    apply: (perm_eq_on_trans _ _ _ _ _ hpe).
    by apply (swapP_perm_eq_on t{hr} t' lo{hr} hi{hr} (i{hr} + 1) j{hr}) => /#.
  wp; skip => |> &hr *; split; 1: smt(perm_eq_refl).
  move=> c0 i0 j0 t0 7? hpe *; split; 1: smt().
  move=> 3? t' hp; split; 2: smt().
  apply: (perm_eq_on_trans _ _ _ _ _ hpe).
  by apply: swapP_perm_eq_on hp => /#.
qed.

phoare h_partition_ll t_ c_ lo_ hi_: [ QS.partition :
    c = c_ /\ t = t_ /\ lo = lo_ /\ hi = hi_ /\ uniq_on t lo hi /\ 0 <= lo <= hi < size t
    ==>
    let (t,p) = (res.`1, res.`2) in 
    perm_eq_on t_ t lo_ hi_ /\ partition_on t lo_ p hi_ /\ t.[p] = t_.[hi_] /\ lo_ <= p <= hi_ /\
    eq_except t_ t lo_ hi_ /\
    c = c_ + (hi_ - lo_) * clt ] = 1%r.
proof.
  conseq (_: true ==> true) (h_partition t_ c_ lo_ hi_) => //.
  proc; inline QS.swap_; wp.
  by while true (hi - j); auto => /#.
qed.

equiv p_partitionE t_ lo_ hi_ : QS.p_partition ~ QS.p_partition_abs : 
  ={lo,hi,c} /\ lo{1} = lo_ /\ hi{1} = hi_ /\ t{1} = t_ /\ 0 <= lo_ <= hi_ < size t{1} /\ (uniq_on t lo hi){1} 
  ==> 
  ={c} /\ uniq_on res.`1{1} lo_ hi_ /\ res.`2{1} = res{2} /\ lo_ <= res.`2{1} <= hi_ /\ size res.`1{1} = size t_.
proof.
  proc.
  seq 1 1 : (#pre /\ p{2} = sindex Partition0.(<=) t{1} lo{1} hi{1} p{1} /\ (lo <= p <= hi){1} ).
  + rnd (sindex Partition0.(<=) t{1} lo{1} hi{1}) (sindex_inv Partition0.(<=) t{1} lo{1} hi{1}); skip => />.
    move=> hlo hlohi hhi hu; split.
    + by move=> p /supp_dinter hp; rewrite sindex_sindex_inv.
    move=> _; split.
    + move=> p /supp_dinter hp.
      by rewrite !dinter1E hp /=; smt(sindex_inv_in).
    move=> _ p /supp_dinter hp; split. 
    + by apply/supp_dinter; smt(sindex_in).
    by move=> _; rewrite sindex_inv_sindex //; smt(sindex_in).
  wp.
  ecall{1} (h_partition_ll t{1} c{1} lo{1} hi{1}).
  ecall{1} (h_swap_ll t{1} p{1} hi{1} c{1}); skip => |>.
  move=> &1 &2 hu *.
  split; 1: smt().
  move=> 3? t' hsw.
  have hp := swapP_perm_eq_on _ _ lo_ hi_ _ _ _ _ hsw => //.
  rewrite -(perm_uniq_on _ _ _ _ hp); split; 1: smt().
  move=> ?? [t'' p''] /= hp' hpart *.
  have hp2 := perm_eq_on_trans _ _ _ _ _ hp hp'.
  split; 1: by have /perm_uniq_on <- := hp2.
  have -> := perm_sindex t_ t'' lo_ hi_ p{1} p'' _ _ _ hp2 => //; 1:smt().
  rewrite sindex_countP //;  1: by rewrite -(perm_uniq_on _ _ _ _ hp2).
  rewrite (partition_on_sindex _ _ _ _ _ hpart) // /#. 
qed.

ehoare eh_p_partition f t_ lo_ hi_: QS.p_partition :
  (lo = lo_ /\ hi = hi_ /\ t = t_ /\ uniq_on t lo hi /\  0 <= lo_ <= hi_ < size t) `|` 
Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt)) ==> 
   (lo_ <= res.`2 <= hi_ /\ uniq_on res.`1 lo_ hi_ /\ size res.`1 = size t_) `|` f res.`2 c.
proof.
  conseq (p_partitionE t_ lo_ hi_) 
    (_:  Ep [lo .. hi] (fun p => f p (c + (hi - lo)*clt)) ==> 
         f res c) => />.
  + by move=> &1; exists c{1} (lo, hi){1}; apply trans_help => />.
  proc; auto.
qed.

ehoare eh_qselect : QS.qselect : (0 <= pos < size t /\ uniq_on t 0 (size t - 1)) `|` (4 * (size t - 1))%xr ==> c%xr.
proof.
  proc.
  while ((0 <= lo <= pos <= hi < size t /\ lo <= pos <= hi /\ uniq_on t lo hi /\ 0 <= c) `|` 
          c%xr + (4 * (hi - lo))%xr).
  + by move=> &hr /=; apply xle_cxr_r => /> * /#.
  + wp; exlim t, lo, hi, pos => t_ lo_ hi_ pos_.
    call /(fun x => (lo = lo_ /\ hi = hi_ /\ pos = pos_ /\ 0 <= lo <= pos <= hi < size t_ ) `|` x) 
      (eh_p_partition (fun p c => (0 <= c) `|`
        if p = pos_ then c%xr
        else if p < pos_ then c%xr + (4 * (hi_ - (p+1)))%xr
        else  c%xr + (4 * ((p-1) - lo_))%xr)
       t_ lo_ hi_).
    + by move=> &hr /=; apply xle_cxr_r => /> *; smt(uniq_on_sub).
    skip => &hr /=; apply xle_cxr => />.
    move: (pos{hr}) (lo{hr}) (hi{hr}) (t{hr}) (c{hr}) => {&hr lo_ hi_ pos_} pos lo hi t c *.
    split; 1: smt().
    rewrite Ep_cxr; apply xle_cxr_l; 1: by move=> x /supp_dinter /= /#.
    rewrite -(eq_Ep _ (
         (fun (p0 : int) =>
            if p0 = pos then 0%xr
            else if p0 < pos then (4 * (hi - (p0 + 1)))%xr
                 else (4 * (p0 - 1 - lo))%xr)
          + (fun (_:int) => (c + (hi - lo))%xr))).
    + by move=> p /supp_dinter hp /=; case: (p = pos) => //#.
    rewrite EpD EpC dinter_ll 1:/# /=.
    have -> : (c%rp + (4 * (hi - lo))%rp)%xr = (3 * (hi - lo))%xr + (c + (hi - lo))%xr.
    + by rewrite /= -!of_realD /#.
    apply xler_addr.
    rewrite Ep_dinterval (: lo <= hi) 1:/# /=.
    rewrite (BXA.big_cat_int pos) 1:// 1:/#.
    rewrite (BXA.eq_big_int lo pos _ (fun p => (4 * ((hi - 1) - p))%xr)) 1:/#.
    rewrite bigiXI 1:/# BXA.big_ltn 1:/#.
    rewrite (BXA.eq_big_int (pos + 1) (hi + 1) _ (fun p => (4 * (p - (1 + lo)))%xr)) 1:/#.
    rewrite bigiXI 1:/# /=.
    rewrite -!BIA.mulr_sumr BIA.big_split bigi_constz 1://.
    rewrite BIA.big_split bigi_constz 1:/#.
    have /= <- := BIA.sumrN<:int> predT (fun x => x).
    rewrite Num.Domain.mulrDr mulrN. 
    have -> : 4 * sumid lo pos = 2 * (2 * sumid lo pos) by ring.
    rewrite sumidE_rm 1://.
    have -> : 4 * ((hi - 1) * (pos - lo)) - 2 * ((pos - lo) * (pos + lo - 1)) = 
             (pos - lo) * (4 * (hi - 1) - 2 * (pos + lo - 1)) by ring.
    rewrite (Num.Domain.mulrDr 4 (sumid _ _)).
    have -> : 4 * sumid (pos + 1)(hi + 1) = 2 * (2 * sumid (pos + 1)(hi + 1)) by ring.
    rewrite sumidE_rm 1:/#.
    apply RealOrder.ler_pdivr_mulr; 1: smt().
    rewrite !to_pos_pos 1,3,4:/#.
    + rewrite le_fromint.
      pose h1 := hi + 1; pose p1 := pos + 1. pose lo1 := 1+ lo.
      have -> : 2 * ((h1 - p1) * (h1 + p1 - 1)) + 4 * ((- lo1) * (h1 - p1)) = 
                (h1 - p1) * (2 * (h1 + p1 - 1) - 4 * lo1) by ring. 
      by apply IntOrder.mulr_ge0 => /#.
    rewrite -!fromintD -!fromintM le_fromint -subz_ge0 /=.
    pose i := pos - lo; pose j := hi - pos; pose k := (_ - _)%Int.
    have -> : k = (i - j) ^ 2 + 5 * i + 5 * j by rewrite /k /i /j; ring.
    by have /# := IntOrder.ge0_sqr (i - j).
  by wp; skip => &hr /=; apply xle_cxr => /#. 
qed.
