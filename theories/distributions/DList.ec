(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Option Pair Int List Distr Real.
require (*--*) Bigop.

op dlist (d : 'a distr) (n : int): 'a list distr =
  Int.fold (fun d' => Dapply.dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (Dprod.( * ) d d')) (Dunit.dunit []) n
  axiomatized by dlistE.

lemma dlist0 (d : 'a distr) n: n <= 0 => dlist d n = Dunit.dunit [].
proof. by move=> ge0_n; rewrite dlistE Int.foldle0. qed.

lemma dlistS (d : 'a distr) n:
  0 <= n =>
  dlist d (n + 1)
  = Dapply.dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (Dprod.( * ) d (dlist d n)).
proof.
  elim n=> [|n le0_n ih].
    by rewrite !dlistE /= -foldpos // fold0.
  rewrite dlistE -foldpos 1:smt -dlistE /=.
  by have <-: n + 1 = n + 1 + 1 - 1 by smt.
qed.

lemma dlist0_ll (d : 'a distr) n:
  n <= 0 =>
  is_lossless (dlist d n).
proof. by move=> /(dlist0 d) ->; smt. qed.

lemma dlist_ll (d : 'a distr) n:
  is_lossless d =>
  is_lossless (dlist d n).
proof.
  move=> d_ll; case (0 <= n); first last.
    by move=> lt0_n; rewrite dlist0 smt.
  elim n=> [|n le0_n ih].
    by rewrite dlist0 // smt.
  rewrite dlistS // /is_lossless -/(weight _) Dapply.lossless Dprod.lossless !/weight -!/(is_lossless _) //.
qed.

lemma dlist_support0 (d : 'a distr) n xs:
  n <= 0 =>
  support (dlist d n) xs <=> xs = []
by [].

lemma dlist_support_ge0 (d : 'a distr) n xs:
  0 <= n =>
  support (dlist d n) xs <=> size xs = n /\ all (support d) xs.
proof.
  move=> le0_n; move: le0_n xs.
  elim n =>[|n le0_n ih xs]; 1:smt.
  rewrite dlistS // /support Dapply.supp_def; split.
    move=> [[x xs'] /= [->]]; rewrite Dprod.supp_def /fst /snd /=.
    rewrite -!/(support _ xs') ih; smt.
    case xs=> [|x xs /= [len_n [x_in_d all_in_d]]]; 1:smt.
    by exists (x,xs)=> //=; rewrite Dprod.supp_def /fst/ snd /= smt.
qed.

lemma mux_dlist0 (d : 'a distr) n x:
  n <= 0 =>
  mu (dlist d n) (pred1 x) = if x = [] then 1%r else 0%r
by [].

lemma mux_dlistS (d : 'a distr) x xs:
  mu (dlist d (size (x::xs))) (pred1 (x::xs)) =
    mu d (pred1 x) * mu (dlist d (size xs)) (pred1 xs).
proof.
  rewrite /= addzC dlistS 1:smt.
  rewrite -/(mu_x _ _) Dapply.mu_x_def /preim /pred1 /=.
  by rewrite (Dprod.mu_def (fun x0 => x0 = x) (fun x0 => x0 = xs)).
qed.

clone import Bigop as Prod with
  type t <- real,
  op   Support.idm <- 1%r,
  op   Support.(+) <- Real.( * )
proof * by smt.

lemma mux_dlist (d : 'a distr) n xs:
  0 <= n =>
  mu (dlist d n) (pred1 xs)
  = if   n = size xs
    then big predT (fun x => mu d (pred1 x)) xs
    else 0%r.
proof.
  move=> le0_n; case (n = size xs)=> [->|].
    elim xs=> [|x xs ih].
      by rewrite mux_dlist0.
    by rewrite mux_dlistS /= big_cons ih.
  smt.
qed.

lemma mux_dlist_perm_eq (d : 'a distr) s1 s2:
  perm_eq s1 s2 =>
  mu (dlist d (size s1)) (pred1 s1) = mu (dlist d (size s2)) (pred1 s2).
proof.
  rewrite !mux_dlist //= 1,2:smt.
  exact/eq_big_perm.
qed.

abstract theory Program.
  type t.
  op d: t distr.

  module Sample = {
    proc sample(n:int): t list = {
      var r;

      r <$ dlist d n;
      return r;
    }
  }.

  module SampleCons = {
    proc sample(n:int): t list = {
      var r, rs;

      rs <$ dlist d (n - 1);
      r  <$ d;
      return r::rs;
    }
  }.

  module Loop = {
    proc sample(n:int): t list = {
      var i, r, l;

      i <- 0;
      l <- [];
      while (i < n) {
        r <$ d;
        l <- r :: l;
        i <- i + 1;
      }
      return l;
    }
  }.

  module LoopSnoc = {
    proc sample(n:int): t list = {
      var i, r, l;

      i <- 0;
      l <- [];
      while (i < n) {
        r <$ d;
        l <- l ++ [r];
        i <- i + 1;
      }
      return l;
    }
  }.

  lemma pr_Sample _n &m xs: Pr[Sample.sample(_n) @ &m: xs = res] = mu (dlist d _n) (pred1 xs).
  proof. by byphoare (_: n = _n ==> xs = res)=> //=; proc; rnd (pred1 xs); auto; smt. qed.

  equiv Sample_SampleCons_eq: Sample.sample ~ SampleCons.sample: 0 < n{1} /\ ={n} ==> ={res}.
  proof.
    bypr (res{1}) (res{2})=> //= &1 &2 xs [lt0_n] <-.
    rewrite (pr_Sample n{1} &1 xs); case (size xs = n{1})=> [<<-|].
      case xs lt0_n=> [|x xs lt0_n]; 1:smt.
      rewrite mux_dlistS.
      byphoare (_: n = size xs + 1 ==> x::xs = res)=> //=; 2:smt.
      proc; seq  1: (rs = xs) (mu (dlist d (size xs)) (pred1 xs)) (mu d (pred1 x)) _ 0%r.
        done.
        by rnd (pred1 xs); skip; smt.
        by rnd (pred1 x); skip; smt.
        by hoare; auto; smt.
        smt.
    move=> len_xs; rewrite mux_dlist 1:smt (_: n{1} <> size xs) /= 1:smt.
    byphoare (_: n = n{1} ==> xs = res)=> //=; hoare.
    by proc; auto; smt.
  qed.

  equiv Sample_Loop_eq: Sample.sample ~ Loop.sample: ={n} ==> ={res}.
  proof. 
    proc*; exists* n{1}; elim* => _n.
    move: (eq_refl _n); case (_n <= 0)=> //= h.
      by inline *; rcondf{2} 4; auto; smt.
    have {h} h: 0 <= _n by smt.
    call (_: _n = n{1} /\ ={n} ==> ={res})=> //=.
    elim _n h=> //= [|_n le0_n ih].
      by proc; rcondf{2} 3; auto; smt.
    case (_n = 0)=> h.
      proc.
      rcondt{2} 3; 1:by auto; smt.
      rcondf{2} 6; 1:by auto; smt.
      wp; rnd (fun x => head witness x) (fun x => [x]).
      auto; progress; subst _n=> /=.
      + rewrite (dlistS _ 0) // dlist0 // Dapply.mu_x_def /preim /pred1 /=.
        rewrite (Dprod.mu_def (pred1 rR) (pred1 []) d (Dunit.dunit [])).
        by rewrite Dunit.mu_x_def.
      + move: H0; rewrite (dlistS _ 0) // dlist0 // Dapply.supp_def /preim /pred1 /=.
        move=> [[x xs]] /= [->] /=.
        by rewrite Dprod.supp_def.
      + move: H0; rewrite (dlistS _ 0) // dlist0 // Dapply.supp_def /preim /pred1 /=.
        move=> [[x xs]] /= [->] /=.
        by rewrite Dprod.supp_def /fst /snd /= Dunit.supp_def.
    transitivity SampleCons.sample
                 (={n} /\ 0 < n{1} ==> ={res})
                 (_n + 1 = n{1} /\ ={n} /\ 0 < n{1} ==> ={res})=> //=; 1:smt.
      by conseq Sample_SampleCons_eq.
    proc; splitwhile{2} 3: (i < n - 1).
    rcondt{2} 4; 1:by auto; while (i < n); auto; smt.
    rcondf{2} 7; 1:by auto; while (i < n); auto; smt.
    wp; rnd.
    transitivity{1} { rs <@ Sample.sample(n - 1); }
                    (={n} /\ 0 < n{1} ==> ={rs})
                    (_n + 1 = n{1} /\ ={n} /\ 0 < n{1} ==> rs{1} = l{2})=> //=; 1:smt.
      by inline *; auto.
    transitivity{1} { rs <@ Loop.sample(n - 1); }
                    (_n + 1 = n{1} /\ ={n} /\ 0 < n{1} ==> ={rs})
                    (={n} /\ 0 < n{1} ==> rs{1} = l{2})=> //=; 1:smt.
      by call ih; auto; smt.
    by inline *; wp; while (={i, n, l} /\ n0{1} = n{1} - 1 /\ 0 < n{1}); auto; smt.
  qed.

  equiv Sample_LoopSnoc_eq: Sample.sample ~ LoopSnoc.sample: ={n} ==> ={res}.
  proof.
    proc*. transitivity{1} { r <@ Sample.sample(n);
                             r <- rev r;            }
                           (={n} ==> ={r})
                           (={n} ==> ={r})=> //=; 1:smt.
      inline *; wp; rnd rev; auto.
      move=> &1 &2 ->>; split=> /= [|t {t}]; 1:smt.
      split.
        move=> r; rewrite -/(support _ _); case (0 <= n{2})=> sign_n; 2:smt.
          rewrite /mu_x dlist_support_ge0 // => -[<<- all_in_d].
          rewrite -{2}(size_rev r); apply/mux_dlist_perm_eq.
          by rewrite perm_eqP=> p; rewrite count_rev.
      smt.
    transitivity{1} { r <@ Loop.sample(n);
                      r <- rev r;          }
                    (={n} ==> ={r})
                    (={n} ==> ={r})=> //=; 1:smt.
      by wp; call Sample_Loop_eq.
    by inline *; wp; while (={i, n0} /\ rev l{1} = l{2}); auto; smt.
  qed.
end Program.
