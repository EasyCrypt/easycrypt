(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List FSet Distr DProd StdBigop.
(*---*) import Bigreal Bigreal.BRM MUnit.

op dlist (d : 'a distr) (n : int): 'a list distr =
  fold (fun d' => dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` d')) (dunit []) n
  axiomatized by dlist_def.

lemma dlist0 (d : 'a distr) n: n <= 0 => dlist d n = dunit [].
proof. by move=> ge0_n; rewrite dlist_def foldle0. qed.

lemma dlist1 (d : 'a distr) : dlist d 1 = dmap d (fun x => [x]).
proof.
rewrite /dlist -foldpos //= fold0 /= dmap_dprodE /dmap /(\o).
by apply eq_dlet => // x; rewrite dlet_unit.
qed.

lemma dlist01E (d : 'a distr) n x:
  n <= 0 => mu1 (dlist d n) x = b2r (x = []).
proof. by move=> /(dlist0 d) ->; rewrite dunit1E (eq_sym x). qed.

lemma dlistS (d : 'a distr) n:
  0 <= n =>
  dlist d (n + 1)
  = dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` dlist d n).
proof. by move=> hn; rewrite !dlist_def foldS. qed.

lemma dlist_djoin (d : 'a distr) n: 0 <= n => dlist d n = djoin (nseq n d).
proof.
elim: n => [|n Hn IHn]; first by rewrite dlist0 // /nseq iter0 // djoin_nil.
by rewrite dlistS // nseqS // djoin_cons IHn.
qed.

lemma dapply_dmap ['a 'b] (d:'a distr) (F:'a -> 'b): dapply F d = dmap d F by done.

lemma dlist_add (d:'a distr) n1 n2:
  0 <= n1 => 0 <= n2 =>
  dlist d (n1 + n2) =
    dmap (dlist d n1 `*` dlist d n2) (fun (p:'a list * 'a list) => p.`1 ++ p.`2).
proof.
elim: n1 => [hn2|n1 hn1 IHn1 hn2].
  by rewrite (dlist0 d 0) //= /(\o) dmap_dprodE dlet_unit /= dmap_id_eq_in.
rewrite addzAC !dlistS 1:/# //= IHn1 //.
rewrite !dmap_dprodE /= dlet_dlet; apply eq_dlet => //= x.
rewrite dmap_dlet dlet_dmap; apply eq_dlet => //= x1.
rewrite /dmap dlet_dlet /(\o); apply eq_dlet => //= x2.
by rewrite dlet_dunit dmap_dunit.
qed.

lemma dlistSr (d : 'a distr) (n : int) : 0 <= n =>
  dlist d (n + 1) = dapply (fun (xy : 'a list * 'a) => rcons xy.`1 xy.`2) (dlist d n `*` d).
proof.
move => hn; rewrite dlist_add // dlist1 /= !dmap_dprodE.
apply eq_dlet => // xs; rewrite dmap_comp.
by apply eq_dmap => x //=; rewrite /(\o) cats1.
qed.

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

lemma dlistS1E (d : 'a distr) x xs:
  mu1 (dlist d (size (x::xs))) (x::xs) =
    mu1 d x * mu1 (dlist d (size xs)) xs.
proof.
rewrite /= addzC dlistS 1:size_ge0 /= dmap1E -dprod1E &(mu_eq) => z /#.
qed.

lemma dlistE x0 (d : 'a distr) (p : int -> 'a -> bool) n :
    mu (dlist d n) (fun xs : 'a list =>
                    forall i, (0 <= i) && (i < n) => (p i (nth x0 xs i)))
  = bigi predT (fun i => mu d (p i)) 0 n.
proof.
elim/natind : n p => [n n_le0|n n_ge0 IHn] p.
- rewrite dlist0 // dunitE range_geq //= big_nil; smt().
rewrite rangeSr // -cats1 big_cat big_seq1.
rewrite dlistSr //= dmapE.
pose P1 xs := forall i, 0 <= i && i < n => p i (nth x0 xs i).
pose P2 x := p n x.
pose P (a : 'a list * 'a) := P1 a.`1 /\ P2 a.`2.
rewrite (mu_eq_support _ _ P); 2: by rewrite dprodE IHn.
case => xs x /=. rewrite supp_dprod /= supp_dlist // => -[[? ?] ?].
rewrite /(\o) /P /P1 /P2 /= eq_iff; subst n; split; 2: smt(nth_rcons).
move => H; split => [i|];[have := (H i)|have := H (size xs)]; smt(nth_rcons).
qed.

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
by move=> ?; rewrite -supportPn supp_dlist /#.
qed.

lemma dlist1E_add (d : 'a distr) n1 n2 l : 
  0 <= n1 => 0 <= n2 =>
  mu1 (dlist d (n1 + n2)) l = mu1 (dlist d n1) (take n1 l) * mu1 (dlist d n2) (drop n1 l).
proof.
  move=> h1 h2.
  case (size l < n1) => hs. 
  + rewrite dlist1E 1:/# dlist1E 1://; smt(size_take).
  rewrite dlist_add //= dmap1E -dprod1E.
  apply mu_eq_support => -[l1 l2] /= /supp_dprod [] /=.
  move=> /(supp_dlist_size _ _ _ h1) <<- _.
  rewrite /(\o) /pred1 /= -{1}(cat_take_drop (size l1) l); smt(eqseq_cat size_take).
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
by rewrite !dlist1E ?size_ge0 /=;apply eq_big_perm.
qed.

lemma weight_dlist0 n (d:'a distr):
  n <= 0 => weight (dlist d n) = 1%r.
proof. by move=> le0;rewrite dlist0E. qed.

lemma weight_dlistS n (d:'a distr):
  0 <= n => weight (dlist d (n + 1)) = weight d * weight (dlist d n).
proof. by move=> ge0;rewrite -(dlistSE witness) //. qed.

lemma weight_dlist (d : 'a distr) n : 
 0 <= n => weight (dlist d n) = (weight d)^n.
proof.
elim: n => [|n ? IHn]; 1: by rewrite weight_dlist0 // RField.expr0.
by rewrite weight_dlistS // IHn RField.exprS.
qed.


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

lemma dlist_dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) n :
  dlist (dmap d f) n = dmap (dlist d n) (map f).
proof.
elim/natind: n => [n le0_n| n ge0_n ih].
- by rewrite !dlist0 // dmap_dunit.
- by rewrite !dlistS //= ih -dmap_dprod_comp dmap_comp.
qed.

(* 0 <= n could be removed, but applying the lemma is pointless in that case *)
lemma dlist_set2E x0 (d : 'a distr) (p : 'a -> bool) n (I J : int fset) :
  is_lossless d => 0 <= n =>
  (forall i, i \in I => 0 <= i && i < n) =>
  (forall j, j \in J => 0 <= j && j < n) =>
  (forall k, !(k \in I /\ k \in J)) =>
  mu (dlist d n)
     (fun xs => (forall i, i \in I => p (nth x0 xs i)) /\
                (forall j, j \in J => !p (nth x0 xs j)))
  = (mu d p)^(card I) * (mu d (predC p))^(card J).
proof.
move => d_ll n_ge0 I_range J_range disjIJ.
pose q i x := (i \in I => p x) /\ (i \in J => !p x).
rewrite (mu_eq_support _ _
  (fun xs => forall i, (0 <= i) && (i < n) => q i (nth x0 xs i))); 1: smt(supp_dlist).
rewrite dlistE (bigEM (mem (I `|` J))).
rewrite (big1 (predC (mem (I `|` J)))) ?mulr1.
  move => i; rewrite /predC in_fsetU negb_or /= /q => -[iNI iNJ].
  rewrite (mu_eq _ _ predT) 1:/# //.
rewrite -big_filter (eq_big_perm _ _ _ (elems I ++ elems J)) ?big_cat.
- apply uniq_perm_eq => [| |x].
  + by rewrite filter_uniq range_uniq.
  + rewrite cat_uniq !uniq_elems => />; apply/hasPn; smt().
  + by rewrite mem_filter mem_range mem_cat -!memE in_fsetU /#.
rewrite big_seq_cond (eq_bigr _ _ (fun _ => mu d p)) -?big_seq_cond.
  move => i; rewrite /= /q -memE => -[iI _]; apply mu_eq => /#.
rewrite mulr_const big_seq_cond (eq_bigr _ _ (fun _ => mu d (predC p))) -?big_seq_cond.
  move => i; rewrite /= /q -memE => -[iI _]; apply mu_eq => /#.
by rewrite mulr_const /card.
qed.

lemma dlist_setE x0 (d : 'a distr) (p : 'a -> bool) n (I : int fset) :
  is_lossless d => 0 <= n => (forall i, i \in I => 0 <= i && i < n) =>
  mu (dlist d n) (fun xs => forall i, i \in I => p (nth x0 xs i)) = (mu d p)^(card I).
proof.
move => d_ll n_ge0 hI.
have := dlist_set2E x0 d p n I fset0 d_ll n_ge0 hI _ _; 1,2 : smt(in_fset0).
rewrite fcards0 RField.expr0 RField.mulr1 => <-.
apply: mu_eq_support => xs; rewrite supp_dlist //= => -[? ?]; smt(in_fset0).
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
    proc sample2(n1:int, n2:int) : t list * t * t list = {
      var rs1,r,rs2;
      rs1 <$ dlist d n1;
      r   <$ d;
      rs2 <$ dlist d n2;
      return (rs1, r, rs2);
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
    move=> len_xs; rewrite dlist1E 1:#smt (_: n{1} <> size xs) /= 1:#smt.
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

  equiv Sample_Sample2 n1_ n2_ : Sample.sample ~ Sample.sample2 : 
     n{1} = n1{2} + 1 + n2{2} /\ 0 <= n1{2} /\ 0 <= n2{2} /\ n1{2} = n1_ /\ n2{2} = n2_ ==>
     res{1} = res{2}.`1 ++ res{2}.`2 :: res{2}.`3 /\
     size res{2}.`1 = n1_ /\ size res{2}.`3 = n2_.
  proof.
    conseq (: _ ==> res{1} = res{2}.`1 ++ res{2}.`2 :: res{2}.`3) _ 
      (: 0 <= n1 /\ 0 <= n2 /\ n1 = n1_ /\ n2 = n2_ ==> size res.`1 = n1_ /\ size res.`3 = n2_) => //.
    + by proc; auto; smt(supp_dlist_size).
    bypr (res{1}) (res{2}.`1 ++ res{2}.`2 :: res{2}.`3) => />.
    move=> &1 &2 l {n1_ n2_}; move: (arg{1}) (n1{2}) (n2{2}) => /> n1_ n2_ hn1 hn2.
    have -> : Pr[Sample.sample2(n1_, n2_) @ &2 : res.`1 ++ res.`2 :: res.`3 = l] =
              mu1 (dlist d (n1_ + 1 + n2_)) l; last first.
    + by byphoare (: n = n1_ + 1 + n2_ ==> _) => //; proc; rnd (pred1 l); skip.
    byphoare (: n1 = n1_ /\ n2 = n2_ ==> _) => //; proc.
    case @[ambient] (size l = n1_ + 1 + n2_) => hs; last first.
    + conseq (:_ : 0%r); 1: smt(dlist1E).
      by hoare; auto; smt (supp_dlist size_cat).
    conseq (: rs1 = take n1_ l /\ r = nth witness l n1_ /\ rs2 = drop (n1_ + 1) l : 
      = (mu1 (dlist d n1_) (take n1_ l) * 
          (mu1 d (nth witness l n1_) * mu1 (dlist d n2_) (drop (n1_ + 1) l)))) (: _ ==> size rs1 = n1_ ) => //.
    + move=> _ _ r rs1 rs2.
      rewrite -{1 3}(cat_take_drop n1_ l) -(cat_take_drop 1 (drop n1_ l)) -drop_add //. 
      case: (drop n1_ l) (size_drop n1_ l hn1) => /=; 1: smt().
      move=> x *; rewrite take0 /= nth_cat size_takel /=; smt (eqseq_cat size_takel).
    + move=> *; rewrite -addrA (dlist1E_add d _ _ l) // 1:/# dlist1E_add // -drop_add //.
      do 2!congr; rewrite -{1}(cat_take_drop n1_ l) nth_cat size_takel 1:/# /=.
      case: (drop n1_ l) (size_drop n1_ l hn1) => /=; 1: smt().
      by move=> x *; rewrite take0 (dlistS1E d x []) dlist01E.
    + by auto => /> ? /(supp_dlist_size _ _ _ hn1).
    seq 1 : (rs1 = take n1_ l) 
      (mu1 (dlist d n1_) (take n1_ l)) 
      (mu1 d (nth witness l n1_) * mu1 (dlist d n2_) (drop (n1_ + 1) l))
      _ 0%r (n2 = n2_) => //.
    + by conseq />.
    + by rnd (pred1 (take n1_ l)); skip => />.
    + conseq />; seq 1 : (r = nth witness l n1_) 
            (mu1 d (nth witness l n1_)) (mu1 (dlist d n2_) (drop (n1_ + 1) l))
            _ 0%r (n2 = n2_) => //.
      + by conseq />.
      + by rnd (pred1 (nth witness l n1_)).      
      + by conseq />; rnd (pred1 (drop (n1_ + 1) l)).
      by conseq (:false) => /> //.
    by conseq (:false) => /> //.
  qed. 

end Program.
