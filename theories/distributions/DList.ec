(* -------------------------------------------------------------------- *)
require import AllCore List FSet Distr DProd StdOrder StdBigop.
(*---*) import Bigreal Bigreal.BRM MUnit.

op [opaque] dlist (d : 'a distr) (n : int): 'a list distr =
  fold (fun d' => dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` d')) (dunit []) n.
lemma dlist_def (d : 'a distr) n: dlist d n = fold 
  (fun d' => dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` d')) 
  (dunit []) n by rewrite/dlist.

lemma dlist0 (d : 'a distr) n: n <= 0 => dlist d n = dunit [].
proof. by move=> ge0_n; rewrite dlist_def foldle0. qed.

lemma dlist1 (d : 'a distr) : dlist d 1 = dmap d (fun x => [x]).
proof.
rewrite /dlist -foldpos //= fold0 /= dmap_dprodE /dmap /(\o).
by apply eq_dlet => // x; rewrite dlet_unit.
qed.

lemma dlistS (d : 'a distr) n:
  0 <= n =>
  dlist d (n + 1)
  = dapply (fun (xy : 'a * 'a list) => xy.`1 :: xy.`2) (d `*` (dlist d n)).
proof.
elim n=> [|n le0_n ih].
+ by rewrite !dlist_def /= -foldpos // fold0.
by rewrite dlist_def -foldpos 1:/# -dlist_def /=.
qed.

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
  by rewrite (dlist0 d 0) //= dmap_dprodE dlet_unit /= dmap_id_eq_in.
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
rewrite !big_consT.
move=> /= /> x_in_d all_in_d_xs y_in_d all_in_d_ys /addzI eq_size.
rewrite (Hrec ys) //.
by congr=> //; exact: Hu.
qed.

lemma dlist_dmap ['a 'b] (d : 'a distr) (f : 'a -> 'b) n :
  dlist (dmap d f) n = dmap (dlist d n) (map f).
proof.
elim/natind: n => [n le0_n| n ge0_n ih].
- by rewrite !dlist0 // dmap_dunit.
- by rewrite !dlistS //= ih -dmap_dprod_comp dmap_comp.
qed.

lemma dlist_rev (d:'a distr) n s:
  mu1 (dlist d n) (rev s) =  mu1 (dlist d n) s.
proof.
case (n <= 0) => [?|?].
+ rewrite !dlist0E // /pred1 /= -{1}rev_nil.
  by congr; rewrite eq_iff; split=> />; exact: rev_inj.
case (size s = n) => [<-|?]; 2: smt(dlist1E supp_dlist_size size_rev).
by rewrite -{1}size_rev &(dlist_perm_eq) perm_eq_sym perm_eq_rev.
qed.

lemma dlist_dlist ['a] (d : 'a distr) (m n : int) :
  0 <= m => 0 <= n =>
    dmap (dlist (dlist d m) n) flatten = dlist d (m * n).
proof.
move=> ge0_m; elim: n => /= [|n ge0_n ih].
- by rewrite !dlist0 // dmap_dunit.
rewrite mulrDr /= [dlist d (m * n + m)]dlist_add //.
- by apply: IntOrder.mulr_ge0.
rewrite dlistSr //= dmap_comp !dmap_dprodE /=.
rewrite -ih dlet_dmap /= &(eq_dlet) // => xss /=.
by rewrite &(eq_dmap) /(\o) /= => xs; rewrite flatten_rcons.
qed.

lemma dlist_insert ['a] (x0 : 'a) (i n : int) (d : 'a distr) :
  0 <= n => 0 <= i <= n => dlist d (n+1) =
    dmap (d `*` dlist d n) (fun x_xs : 'a * 'a list => insert x_xs.`1 x_xs.`2 i).
proof.
move=> ge0_n [ge0_i lti]; apply/eq_sym.
pose f (x_xs : _ * _) := insert x_xs.`1 x_xs.`2 i.
pose g (xs : 'a list) := (nth x0 xs i, take i xs ++ drop (i+1) xs).
have ge0_Sn: 0 <= n + 1 by smt(). apply: (dmap_bij _ _ f g).
- case=> [x xs] /supp_dprod[/=] x_in_d.
  case/(supp_dlist _ _ _ ge0_n)=> sz_xs /allP xs_in_d.
  move=> @/f /=; apply/supp_dlist; first smt().
  rewrite size_insert ?sz_xs //=; apply/allP.
  by move=> y /mem_insert[->>//|/xs_in_d].
- move=> xs /(supp_dlist _ _ _ ge0_Sn)[sz_xs /allP xs_in_d] @/g.
  rewrite dprod1E !dlist1E ~-1://# sz_xs /=.
  rewrite size_cat size_take // size_drop 1:/#.
  rewrite iftrue 1:/# -(BRM.big_consT (mu1 d)) &(BRM.eq_big_perm).
  by rewrite -cat_cons perm_eq_sym  &(perm_eq_nth_take_drop) //#.
- case=> x xs /supp_dprod[/=] _ /(supp_dlist _ _ _ ge0_n)[sz_xs _].
  rewrite /g /f /= nth_insert ?sz_xs //= take_insert_le 1:/#.
  by rewrite drop_insert_gt 1:/# /= cat_take_drop.
- move=> xs /(supp_dlist _ _ _ ge0_Sn)[/=] sz_xs _ @/f @/g /=.
  have sz_take: size (take i xs) = i by rewrite size_take //#.
  by apply/insert_nth_take_drop => //#.
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
      case xs lt0_n=> [|x xs lt0_n]; 1: smt().
      rewrite dlistS1E.
      byphoare (_: n = size xs + 1 ==> x::xs = res)=> //=; 2: by rewrite addrC. 
      proc; seq 1: (rs = xs) (mu (dlist d (size xs)) (pred1 xs)) (mu d (pred1 x)) _ 0%r => //.
        by rnd (pred1 xs); skip; smt().
        by rnd (pred1 x); skip; smt().
        by hoare; auto; smt().
        smt().
    move=> len_xs; rewrite dlist1E 1:/# ifF 1:/#.
    byphoare (_: n = n{1} ==> xs = res)=> //=; hoare.
    proc; auto=> />; smt(supp_dlist_size).
  qed.

  equiv Sample_Loop_eq: Sample.sample ~ Loop.sample: ={n} ==> ={res}.
  proof.
    proc*; exists* n{1}; elim* => _n.
    move: (eq_refl _n); case (_n <= 0)=> //= h.
    + inline *;rcondf{2} 4;auto;smt (supp_dlist0 weight_dlist0).
    have {h} h: 0 <= _n by smt ().
    call (_: _n = n{1} /\ ={n} ==> ={res})=> //=.
    elim _n h=> //= [|_n le0_n ih].
      proc; rcondf{2} 3; auto=> />. smt(supp_dlist0 weight_dlist0).
    case (_n = 0)=> [-> | h].
      proc; rcondt{2} 3; 1:(by auto); rcondf{2} 6; 1:by auto.
      wp; rnd (fun x => head witness x) (fun x => [x]).
      auto => />;split => [ rR ? | _ rL ].
      + by rewrite dlist1E //= big_consT big_nil.
      rewrite supp_dlist //;case rL => //=; smt (size_eq0).
    transitivity SampleCons.sample
                 (={n} /\ 0 < n{1} ==> ={res})
                 (_n + 1 = n{1} /\ ={n} /\ 0 < n{1} ==> ={res})=> //=; 1:smt().
      by conseq Sample_SampleCons_eq.
    proc; splitwhile{2} 3: (i < n - 1).
    rcondt{2} 4; 1:by auto; while (i < n); auto; smt().
    rcondf{2} 7; 1:by auto; while (i < n); auto; smt().
    wp; rnd.
    outline {1} 1 ~ Sample.sample.
    rewrite equiv[{1} 1 ih].
    inline.
    by wp; while (={i} /\ ={l} /\ n0{1} = n{2} - 1); auto; smt().
  qed.

  equiv Sample_LoopSnoc_eq: Sample.sample ~ LoopSnoc.sample: ={n} ==> ={res}.
  proof.
    proc*. 
    replace* {1} { x } by { x; r <- rev r; }.
      inline *; wp; rnd rev; auto.
      smt(revK dlist_rev).
    rewrite equiv[{1} 1 Sample_Loop_eq].
    inline *; wp; while (={i, n0} /\ rev l{1} = l{2}); auto => />.
    smt(rev_cons cats1).
  qed.
end Program.
