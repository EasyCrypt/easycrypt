require import AllCore Distr Bool DBool DInterval List.

require BitWord Bigop.

clone import BitWord as BS.
clone import Bigop as BBS with
   type t <- BS.word,
   op Support.idm <- BS.zerow,
   op Support.( + ) <- BS.(+^)
   proof * by smt(xorwA xorwC xorw0).

op N:int.

pred sxor (s s':int list) (i:int) =
  exists s1 s2, s = s1 ++ s2 /\ s' = s1 ++ i :: s2.

pred sxor2 (s s':int list) (i:int) =
  sxor s s' i \/ sxor s' s i.

lemma sxor_cons s i : sxor s (i :: s) i.
proof. by exists [] s. qed.

lemma sxor2_cons (s s':int list) (i j:int):
  sxor2 s s' i => sxor2 (j::s) (j::s') i.
proof. smt (). qed.

(* The database *)
op a : int -> word.

module PIR = {

  proc query (s:int list) = {
    return (big predT a s);
  } 

  var s, s' : int list

  proc main (i:int) = {
    var r, r' : word;
    var j <- 0;

    var b;

    (s, s') <- ([], []);
    while (j < N) {
      b <$ {0,1};
      if (j = i) {
        if (b) s <- j :: s; else s' <- j :: s';
      } else {
        if (b) { s <- j :: s; s' <- j :: s'; }
      }
      j <- j + 1;
    }

    r <@ query(s);
    r' <@ query(s');

    return r +^ r';
  }
   
}.

lemma PIR_correct &m i0 : 0 <= i0 < N => Pr [PIR.main(i0) @ &m : res = a i0] = 1%r.
proof.
  move=> bound.
  (* TODO: allows to do directly "byhoare (_: i = i0 ==> res = a i0)" *)
  byphoare (_: i = i0 ==> res = a i0) => // {&m}.
  conseq (: _ ==> true) (: _ ==> res = a i0)=> //.
  + proc;inline *;wp.
    conseq (_: _ ==> sxor2 PIR.s PIR.s' i) => //.
    + by move=> &m -> s s' [] [s1 s2 [-> ->]];rewrite !big_cat big_consT;ring.
    while (j <= N /\ if j <= i then PIR.s = PIR.s' else sxor2 PIR.s PIR.s' i).
    + wp;rnd;skip => /= &m [[_]] + HjN. 
      have -> /= : j{m} + 1 <= N by smt ().
      case: (j{m} <= i{m}) => Hji;2: by smt ().
      move=> -> b _;case: (j{m} = i{m}) => [->> | /#].
      by rewrite (_ : !(i{m}+1 <= i{m})) 1:/# /=; smt (sxor_cons).
    by auto => /#.
  proc;inline *;wp.
  while (true) (N-j).
  + move=> z;wp;rnd predT;skip => &hr />;smt (dbool_ll).
  by auto=> /#. 
qed.

equiv PIR_secure1: PIR.main ~ PIR.main : true ==> ={PIR.s}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s});auto.
qed.

hint exact : dbool_funi.
hint exact : dbool_fu.

equiv PIR_secure2: PIR.main ~ PIR.main : true ==> ={PIR.s'}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s'});2: by auto.
  wp; case: ((j = i){1} = (j = i){2}).
  + auto;smt (dbool_funi dbool_fu).
  rnd (fun x => !x);skip;smt (dbool_funi dbool_fu).
qed.

lemma PIR_secuity_s_byequiv i1 i2 &m1 &m2 x: 
   Pr[PIR.main(i1) @ &m1 : PIR.s = x] = Pr[PIR.main(i2) @ &m2 : PIR.s = x].
proof. by byequiv PIR_secure1. qed.

lemma PIR_secuity_s'_byequiv i1 i2 &m1 &m2 x: 
   Pr[PIR.main(i1) @ &m1 : PIR.s' = x] = Pr[PIR.main(i2) @ &m2 : PIR.s' = x].
proof. by byequiv PIR_secure2. qed.

(* ************************************************************************** *)
(* Alternative proof:                                                         *)
(*   We show that the distribution of PIR.s and PIR.s' is uniform             *)
(* First version we use phoare                                                *)

require import List FSet.

op restr (s : int fset) n = 
 s `&` oflist (iota_ 0 n).

op is_restr (s : int fset) n = 
  s = restr s n.

lemma restrS s j : 0 <= j => 
  restr  s (j + 1) = 
  (if (j \in s) then fset1 j else fset0) `|` restr s j.
proof.
  move=> H0j;rewrite /restr iotaSr //= -cats1 oflist_cat.
  by rewrite fsetUC fsetIUr -set1E fsetI1.
qed.

lemma nin_is_restr n s : is_restr s n => !n \in s.
proof.
  by move=> ->;rewrite /restr in_fsetI mem_oflist mem_iota.
qed.

(* TODO: rename mem_oflist in in_oflist *)
lemma is_restr_diff n s1 s2 : is_restr s2 n => fset1 n `|` s1 <> s2.
proof.
  move => /nin_is_restr Hs2;apply contraT => Heq.
  rewrite /= in Heq;subst s2.
  by apply Hs2;rewrite in_fsetU in_fset1.
qed.

lemma is_restr_Ueq n s1 s2 : 
  is_restr s1 n => is_restr s2 n => 
  (fset1 n `|` s1 =  fset1 n `|` s2) = (s1 = s2).
proof.
  move=> Hs1 Hs2;rewrite eq_iff;split => [ | -> //].
  rewrite !fsetP => H x; have := H x.
  rewrite !in_fsetU in_fset1;case: (x = n) => /= [-> | //].
  by rewrite !nin_is_restr.
qed.

lemma is_restr_addS n s : 
  0 <= n =>
  is_restr s n => is_restr (fset1 n `|` s) (n + 1).
proof.
  move=> Hn Hs;apply fsetP => x.
  rewrite /restr !inE Hs !(in_fsetI, mem_oflist, mem_iota) /#.
qed.

lemma is_restrS n s :
  0 <= n =>
  is_restr s n => is_restr s (n + 1).
proof.
  by move=> Hn Hs;rewrite /is_restr restrS // (nin_is_restr _ _ Hs) /= fset0U.
qed.

lemma is_restr_restr n s : is_restr (restr s n) n.
proof.
  apply fsetP => x;rewrite /restr !in_fsetI !mem_oflist /#.
qed.

lemma is_restr_fset0 n : is_restr fset0 n.
proof. by apply fsetP => x;rewrite /restr in_fsetI in_fset0. qed.

lemma restr_0 s : restr s 0 = fset0.
proof. 
  apply fsetP => x;rewrite /restr in_fsetI in_fset0 mem_oflist mem_iota /#.
qed.

axiom N_pos : 0 <= N.

import RField StdOrder.RealOrder.

lemma Pr_PIR_s i0 &m x :
  Pr[PIR.main(i0) @ &m : oflist PIR.s = x] = 
    if is_restr x N then 1%r/2%r^N else 0%r.
proof.
  byphoare=> // {i0};proc;inline *;wp.
  case: (is_restr x N);first last.
  + conseq (_ : _ ==> _ : = 0%r) => [ _ -> // | ].
    hoare;conseq (_ : _ ==> is_restr (oflist PIR.s) N); 1:by smt().
    while (0<= j <= N /\ is_restr (oflist PIR.s) j).
    + by auto => &m1 />;rewrite oflist_cons;smt (is_restrS is_restr_addS).
    auto=> ?;rewrite -set0E;smt (is_restr_fset0 N_pos).
  sp; conseq (_ : _ ==> _ : = (if (oflist PIR.s) = restr x j then 1%r/2%r^(N-j) else 0%r)).
  + move=> {&m} &m />;rewrite -set0E. 
    have -> // : fset0 = restr x 0.
    + by apply fsetP=> z;rewrite /restr !inE mem_oflist mem_iota /#.
  conseq (_ : _ ==> oflist PIR.s = restr x j) (_: _ ==> j = N) => //;1:smt().
  + while(0 <= j <= N);auto;smt (N_pos).
  while (0 <= j <= N /\ is_restr (oflist PIR.s) j) (N-j) N 1%r;2,3:smt(N_pos).
  + by move=> &hr /> _;rewrite -set0E N_pos /=; apply is_restr_fset0.
  + move=> H.
    case (oflist PIR.s = restr x j);first last.
    + seq 3 : true _ 0%r 0%r _ (0 <= j <= N /\ is_restr (oflist PIR.s) j /\ oflist PIR.s <> restr x j).
      + auto => /> &hr H0j ???? b ?.    
        rewrite restrS //= oflist_cons. 
        smt (is_restr_addS is_restrS is_restr_Ueq  is_restr_diff fset0U is_restr_restr).
        by conseq H => /#.
      + by hoare;auto.
      smt().      
    conseq (_ : _ : = (1%r / 2%r ^ (N - j))) => [/#|].
    exists * j, PIR.s;elim * => j0 s0.    
    seq 3: (b = j0 \in x) (1%r/2%r) (1%r / 2%r ^ (N - (j0+1))) _ 0%r 
        (1 <= j <= N /\ j = j0 + 1 /\ (PIR.s = if b then j0 :: s0 else s0) /\ 
         is_restr (oflist s0) j0 /\ oflist s0 = restr x j0).
    + by auto => /> /#.
    + by wp => /=;rnd (pred1 (j0 \in x));skip => /> &hr;rewrite dbool1E.
    + conseq H => />.
      + case: (j0 \in x) => Hjx ?? His Hof.
        + by rewrite oflist_cons restrS 1:/# Hjx Hof.
        by rewrite restrS 1:/# Hjx Hof /= fset0U.
      smt (is_restrS is_restr_addS oflist_cons).
    + conseq H => />.
      + move=> &hr ?? His Hof Hb.
        rewrite restrS 1:/# (negbRL _ _ Hb).    
        case (j0 \in x) => /= Hj0x.
        + by rewrite (eq_sym (oflist s0)) (is_restr_diff j0 (restr x j0) _ His). 
        by rewrite fset0U oflist_cons -Hof (is_restr_diff j0 (oflist s0) _ His).
      smt (is_restrS is_restr_addS oflist_cons).
    move=> &hr /> ?????; rewrite -exprS 1:/#; congr;congr;ring.
  + wp;rnd predT;skip => /> &hr.
    smt (dbool_ll oflist_cons is_restrS is_restr_addS).
  move=> z;auto=> />;smt (dbool_ll).
qed.

lemma Pr_PIR_s' i0 &m x :
  Pr[PIR.main(i0) @ &m : oflist PIR.s' = x] = 
    if is_restr x N then 1%r/2%r^N else 0%r.
proof.
  byphoare=> // {i0};proc;inline *;wp.
  case: (is_restr x N);first last.
  + conseq (_ : _ ==> _ : = 0%r) => [ _ -> // | ].
    hoare;conseq (_ : _ ==> is_restr (oflist PIR.s') N); 1:by smt().
    while (0<= j <= N /\ is_restr (oflist PIR.s') j).
    + auto;smt (oflist_cons is_restrS is_restr_addS).
    auto=> ?;rewrite -set0E;smt (is_restr_fset0 N_pos).
  sp; conseq (_ : _ ==> _ : = (if (oflist PIR.s') = restr x j then 1%r/2%r^(N-j) else 0%r)).
  + move=> {&m} &m />;rewrite -set0E. 
    have -> // : fset0 = restr x 0.
    + by apply fsetP=> z;rewrite /restr !inE mem_oflist mem_iota /#.
  conseq (_ : _ ==> oflist PIR.s' = restr x j) (_: _ ==> j = N) => //;1:smt().
  + while(0 <= j <= N);auto;smt (N_pos).
  while (0 <= j <= N /\ is_restr (oflist PIR.s') j) (N-j) N 1%r;2,3:smt(N_pos).
  + by move=> &hr /> _;rewrite -set0E N_pos /=; apply is_restr_fset0.
  + move=> H.
    case (oflist PIR.s' = restr x j);first last.
    + seq 3 : true _ 0%r 0%r _ (0 <= j <= N /\ is_restr (oflist PIR.s') j /\ oflist PIR.s' <> restr x j).
      + auto => &hr [#] ????? b _;case: (j{hr}=i{hr}) => />;rewrite restrS //= oflist_cons;
          smt (is_restr_addS is_restrS is_restr_Ueq  is_restr_diff fset0U is_restr_restr).
        by conseq H => /#.
      + by hoare;auto.
      smt().      
    conseq (_ : _ : = (1%r / 2%r ^ (N - j))) => [/#|].
    exists * j, PIR.s';elim * => j0 s0.    
    seq 3: (b = ((j0 = i) ^^ (j0 \in x))) (1%r/2%r) (1%r / 2%r ^ (N - (j0+1))) _ 0%r 
        (1 <= j <= N /\ j = j0 + 1 /\ (PIR.s' = if (j0=i) then (if b then s0 else j0::s0) else if b then j0 :: s0 else s0) /\ 
         is_restr (oflist s0) j0 /\ oflist s0 = restr x j0).
    + by auto => /#.
    + by wp => /=;rnd (pred1 ((j0 = i) ^^ (j0 \in x)));skip => /> &hr;rewrite dbool1E.
    + conseq H => />.
      + move=> &hr ?? His Hof;case: (j0 = i{hr}) => /=. 
        + rewrite xorC xor_true => <<-.
          case: (j0 \in x) => Hjx.
          + by rewrite restrS 1:/# Hjx /= oflist_cons Hof.
          by rewrite /= restrS 1:/# Hjx /= fset0U Hof.
        rewrite xorC xor_false => ?.
        case: (j0 \in x) => Hjx.
        + by rewrite oflist_cons restrS 1:/# Hjx Hof.
        by rewrite restrS 1:/# Hjx Hof /= fset0U.
      smt (is_restrS is_restr_addS oflist_cons).
    + conseq H => />.
      + move=> &hr ?? His Hof Hb.
        rewrite restrS 1:/# (negbRL _ _ Hb);case: (j0 = i{hr}) => /= [<<- | ?].  
        + rewrite xorC xor_true /=.
          case (j0 \in x) => /= Hj0x /=.
          + by rewrite (eq_sym (oflist s0)) (is_restr_diff j0 (restr x j0) _ His). 
          by rewrite fset0U oflist_cons -Hof (is_restr_diff j0 (oflist s0) _ His).
        rewrite xorC xor_false.
        case (j0 \in x) => /= Hj0x /=.
        + by rewrite (eq_sym (oflist s0)) (is_restr_diff j0 (restr x j0) _ His). 
        by rewrite fset0U oflist_cons -Hof (is_restr_diff j0 (oflist s0) _ His).
      smt (is_restrS is_restr_addS oflist_cons).
    by move=> &hr /> ?????;rewrite -exprS 1:/#;congr;congr;ring.
  + wp;rnd predT;skip => &hr.
    smt (dbool_ll oflist_cons is_restrS is_restr_addS).
  move=> z;auto=> />;smt (dbool_ll).
qed.

lemma PIR_secuity_s_bypr i1 i2 &m1 &m2 x: 
   Pr[PIR.main(i1) @ &m1 : oflist PIR.s = x] = Pr[PIR.main(i2) @ &m2 : oflist PIR.s = x].
proof. by rewrite (Pr_PIR_s i1 &m1 x) (Pr_PIR_s i2 &m2 x). qed.

lemma PIR_secuity_s'_bypr i1 i2 &m1 &m2 x: 
   Pr[PIR.main(i1) @ &m1 : oflist PIR.s' = x] = Pr[PIR.main(i2) @ &m2 : oflist PIR.s' = x].
proof. by rewrite (Pr_PIR_s' i1 &m1 x) (Pr_PIR_s' i2 &m2 x). qed.


(* Other version without explicite computation of the probability,
   we first show that the probability is uniform,
   unfortunatly this does not allows to conclude in easycrypt.
   We need to be able to do the projection of memories. 
   So we need functions on memory
*)
 
lemma PIR_s_uniform (x1 x2 : int fset):
  0 <= N =>
  is_restr x1 N => 
  is_restr x2 N =>
  equiv [PIR.main ~ PIR.main : ={i} ==> (oflist PIR.s{1} = x1) = (oflist PIR.s{2} = x2)].
proof.
  move=> HN B1 B2;proc;inline *;wp.
  while (={i,j} /\ 0 <= j{1} <= N /\ 
         is_restr (oflist PIR.s{1}) j{1} /\ is_restr (oflist PIR.s{2}) j{1} /\
         ((oflist PIR.s{1} = restr x1 j{1}) = (oflist PIR.s{2} = restr x2 j{1}))).
  + wp.
    rnd (fun b => b ^^ (j{1} \in x1) ^^ (j{1} \in x2)). 
    skip => &m1 &m2 /> H0j HjN Hrs1 Hrs2 Hs Hj; split.
    + by move=> b _;ring.
    move=> _ b _;split;1: by ring.
    move=> _; rewrite !oflist_cons !restrS //. 
    smt (is_restr_addS is_restrS is_restr_diff is_restr_Ueq is_restr_restr  fset0U).
  auto; move => &m1 &m2 />.
  rewrite !restr_0 -set0E /=;smt (is_restr_fset0).
qed.

lemma PIR_s'_uniform (x1 x2 : int fset):
  0 <= N =>
  is_restr x1 N => 
  is_restr x2 N =>
  equiv [PIR.main ~ PIR.main : ={i} ==> (oflist PIR.s'{1} = x1) = (oflist PIR.s'{2} = x2)].
proof.
  move=> HN B1 B2;proc;inline *;wp.
  while (={i,j} /\ 0 <= j{1} <= N /\ 
         is_restr (oflist PIR.s'{1}) j{1} /\ is_restr (oflist PIR.s'{2}) j{1} /\
         ((oflist PIR.s'{1} = restr x1 j{1}) = (oflist PIR.s'{2} = restr x2 j{1}))).
  + wp.
    rnd (fun b => b ^^ (j{1} \in x1) ^^ (j{1} \in x2)). 
    skip => &m1 &m2 [#] 2!->> H0j HjN Hrs1 Hrs2 Hs Hj _; split.
    + move=> b _;ring.
    move=> _ b _; split;1: by ring.
    move=> _; rewrite /= !oflist_cons !restrS //. 
    smt (is_restr_addS is_restrS is_restr_diff is_restr_Ueq is_restr_restr fset0U).
  auto => &m1 &m2 />.
  rewrite !restr_0 -set0E /=;smt (is_restr_fset0).
qed.

