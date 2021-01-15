(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Distr DProd StdBigop.
(*---*) import Bigreal.BRM MUnit.

op dlist (d : 'a distr) (n : int): 'a list distr =
  fold (fun d' => dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` d')) (dunit []) n
  axiomatized by dlist_def.

lemma dlist0 (d : 'a distr) n: n <= 0 => dlist d n = dunit [].
proof. by move=> ge0_n; rewrite dlist_def foldle0. qed.

lemma dlistS (d : 'a distr) n:
  0 <= n =>
  dlist d (n + 1)
  = dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` (dlist d n)).
proof.
elim n=> [|n le0_n ih].
+ by rewrite !dlist_def /= -foldpos // fold0.
by rewrite dlist_def -foldpos 1:/# -dlist_def /=.
qed.

lemma dlist01E (d : 'a distr) n x:
  n <= 0 => mu1 (dlist d n) x = b2r (x = []).
proof. by move=> /(dlist0 d) ->;rewrite dunit1E (eq_sym x). qed.

lemma dlistS1E (d : 'a distr) x xs:
  mu1 (dlist d (size (x::xs))) (x::xs) =
    mu1 d x * mu1 (dlist d (size xs)) xs.
proof.
rewrite /= addzC dlistS 1:size_ge0 /= dmap1E -dprod1E &(mu_eq) => z /#.
qed.

lemma dlist0_ll (d : 'a distr) n:
  n <= 0 =>
  is_lossless (dlist d n).
proof. by move=> /(dlist0 d) ->;apply dunit_ll. qed.

lemma dlist_ll (d : 'a distr) n:
  is_lossless d =>
  is_lossless (dlist d n).
proof.
move=> d_ll; case (0 <= n); first last.
+ move=> lt0_n; rewrite dlist0 1:/#;apply dunit_ll.
elim n=> [|n le0_n ih];first by rewrite dlist0 //;apply dunit_ll.
by rewrite dlistS //;apply/dmap_ll/dprod_ll.
qed.

hint exact random : dlist_ll.

lemma supp_dlist0 (d : 'a distr) n xs:
  n <= 0 =>
  xs \in dlist d n <=> xs = [].
proof. by move=> le0; rewrite dlist0 // supp_dunit. qed.

lemma supp_dlist (d : 'a distr) n xs:
  0 <= n =>
  xs \in dlist d n <=> size xs = n /\ all (support d) xs.
proof.
move=> le0_n;elim: n le0_n xs => [xs | i le0 Hrec xs].
+ by smt (supp_dlist0 size_eq0).
rewrite dlistS // supp_dmap /=;split => [[p]|].
+ rewrite supp_dprod => [# Hp /Hrec [<- Ha] ->] /=.
  by rewrite Hp Ha addzC. 
case xs => //= [/# | x xs [# Hs Hin Ha]];exists (x,xs);smt (supp_dprod).
qed.

lemma supp_dlist_size (d : 'a distr) n xs:
  0 <= n => xs \in dlist d n => size xs = n.
proof. by move=> ge0_n; case/(supp_dlist d n xs ge0_n). qed.

lemma dlist1E (d : 'a distr) n xs:
  0 <= n =>
  mu1 (dlist d n) xs
  = if   n = size xs
    then big predT (fun x => mu1 d x) xs
    else 0%r.
proof.
move=> le0_n; case (n = size xs)=> [->|].
+ elim xs=> [|x xs ih];first by rewrite dlist01E.
  by rewrite dlistS1E /= big_cons ih.
smt w=(supp_dlist mu_bounded).
qed.

lemma dlist0E n (d : 'a distr) P : n <= 0 => mu (dlist d n) P = b2r (P []).
proof. by move=> le0;rewrite dlist0 // dunitE. qed.

lemma dlistSE (a:'a) (d: 'a distr) n P1 P2 :
  0 <= n =>
  mu (dlist d (n+1)) (fun (xs:'a list) => P1 (head a xs) /\ P2 (behead xs)) =
  mu d P1 * mu (dlist d n) P2.
proof. by move=> Hle;rewrite dlistS // /= dmapE -dprodE. qed.

lemma dlist_perm_eq (d : 'a distr) s1 s2:
  perm_eq s1 s2 =>
  mu1 (dlist d (size s1)) s1 = mu1 (dlist d (size s2)) s2.
proof.
rewrite !dlist1E //= 1,2:size_ge0;apply eq_big_perm.
qed.

lemma weight_dlist0 n (d:'a distr):
  n <= 0 => weight (dlist d n) = 1%r.
proof. by move=> le0;rewrite dlist0E. qed.

lemma weight_dlistS n (d:'a distr):
  0 <= n => weight (dlist d (n + 1)) = weight d * weight (dlist d n).
proof. by move=> ge0;rewrite -(dlistSE witness) //. qed.

lemma dlist_fu (d: 'a distr) (xs:'a list): 
  (forall x, x \in xs => x \in d) =>
  xs \in dlist d (size xs).
proof. 
move=> fu; rewrite /support dlist1E 1:size_ge0 /=.
by apply Bigreal.prodr_gt0_seq => /= a Hin _;apply fu.
qed.

lemma dlist_uni (d:'a distr) n : 
  is_uniform d => is_uniform (dlist d n).
proof.
  case (n < 0)=> [Hlt0 Hu xs ys| /lezNgt Hge0 Hu xs ys].
  + rewrite !supp_dlist0 ?ltzW //. 
  rewrite !supp_dlist // => -[eqxs Hxs] [eqys Hys].
  rewrite !dlist1E // eqxs eqys /=;move: eqys;rewrite -eqxs => {eqxs}.
  elim: xs ys Hxs Hys => [ | x xs Hrec] [ | y ys] //=; 1,2:smt (size_ge0).
  rewrite !big_consT /#.
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

  lemma pr_Sample _n &m xs: Pr[Sample.sample(_n) @ &m: res = xs] = mu (dlist d _n) (pred1 xs).
  proof. by byphoare (_: n = _n ==> res = xs)=> //=; proc; rnd. qed.

  equiv Sample_SampleCons_eq: Sample.sample ~ SampleCons.sample: 0 < n{1} /\ ={n} ==> ={res}.
  proof.
    bypr (res{1}) (res{2})=> //= &1 &2 xs [lt0_n] <-.
    rewrite (pr_Sample n{1} &1 xs); case (size xs = n{1})=> [<<-|].
      case xs lt0_n=> [|x xs lt0_n]; 1:smt.
      rewrite dlistS1E.
      byphoare (_: n = size xs + 1 ==> x::xs = res)=> //=; 2:smt.
      proc; seq  1: (rs = xs) (mu (dlist d (size xs)) (pred1 xs)) (mu d (pred1 x)) _ 0%r.
        done.
        by rnd (pred1 xs); skip; smt.
        by rnd (pred1 x); skip; smt.
        by hoare; auto; smt.
        smt.
    move=> len_xs; rewrite dlist1E 1:smt (_: n{1} <> size xs) /= 1:smt.
    byphoare (_: n = n{1} ==> xs = res)=> //=; hoare.
    by proc; auto; smt.
  qed.

  equiv Sample_Loop_eq: Sample.sample ~ Loop.sample: ={n} ==> ={res}.
  proof.
    proc*; exists* n{1}; elim* => _n.
    move: (eq_refl _n); case (_n <= 0)=> //= h.
    + inline *;rcondf{2} 4;auto;smt (supp_dlist0 weight_dlist0).
    have {h} h: 0 <= _n by smt ().
    call (_: _n = n{1} /\ ={n} ==> ={res})=> //=.
    elim _n h=> //= [|_n le0_n ih].
      by proc; rcondf{2} 3; auto; smt.
    case (_n = 0)=> [-> | h].
      proc; rcondt{2} 3; 1:(by auto); rcondf{2} 6; 1:by auto.
      wp; rnd (fun x => head witness x) (fun x => [x]).
      auto => />;split => [ rR ? | _ rL ].
      + by rewrite dlist1E //= big_consT big_nil.
      rewrite supp_dlist //;case rL => //=; smt (size_eq0).
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
          rewrite !dlist1E // (size_rev r)=> ?;congr;apply eq_big_perm.
          by apply perm_eqP=> ?;rewrite count_rev.
      smt.
    transitivity{1} { r <@ Loop.sample(n);
                      r <- rev r;          }
                    (={n} ==> ={r})
                    (={n} ==> ={r})=> //=; 1:smt.
      by wp; call Sample_Loop_eq.
    by inline *; wp; while (={i, n0} /\ rev l{1} = l{2}); auto; smt.
  qed.
end Program.
