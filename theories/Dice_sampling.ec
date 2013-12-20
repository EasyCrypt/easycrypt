require import Distr.
require import Int.
require import Real.
require import FSet.

theory GenDice.

  type t.
  type input.
  op d : input -> t distr.

  op test : input -> t -> bool.
  op sub_supp : input -> t set.
  axiom dU : forall i, isuniform (d i).

  axiom test_in_supp : forall i x, 
     test i x => in_supp x (d i).

  axiom test_sub_supp : forall i x, 
      mem x (sub_supp i) <=> test i x.
  
  module RsampleW = {
    proc sample (i:input, r:t) : t = {
      while (!test i r) {
         r = $(d i);
      }
      return r;
    }
  }.

  lemma prRsampleW : forall i dfl k &m, 
      ! test i dfl =>
      weight (d i) = 1%r =>
      Pr[RsampleW.sample(i,dfl) @ &m : res = k] = 
         if test i k then 1%r/(card(sub_supp i))%r else 0%r.
  proof -strict.
    intros i0 dfl0 k.
    pose bdt := (card(sub_supp i0))%r.
    cut bdt_pos: 0 <= card (sub_supp i0) by smt.
    cut bdt_posr: 0%r <= (card (sub_supp i0))%r by smt.
    case (test i0 k) => Htk &m Hdfl Hweight;
      byphoare (_: !test i r /\ i0 = i ==> k = res) => //;proc.
      (* case : test i k *)
      pose bd := mu_x (d i0) k.
      cut d_uni : forall x, in_supp x (d i0) => mu_x (d i0) x = bd.
         by intros x Hx;rewrite /bd; apply dU => //; apply test_in_supp.
      cut Hdiff: bdt <> (Real.zero)%Real by smt.
      conseq (_:i=i0 ==> k = r : = (if test i r then charfun ((=) k) r else 1%r / bdt)) => //;
        first by smt.
      while (i0=i) (if test i r then 0 else 1) 1 (bdt * bd) => //; first 2 smt.
        intros Hw; alias 2 r0 = r.
        cut Htk' := Htk;generalize Htk';rewrite -test_sub_supp => Hmemk.
        phoare split bd ((1%r - bdt*bd) * (1%r/bdt)) : (k=r0).
          by intros &hr [H1 H2]; rewrite (_: test i{hr} r{hr} = false) 1:neqF //=; fieldeq=> //.
          (* bounding pr : k = r0 /\ k = r *)
          seq 2 : (k = r0) bd 1%r 1%r 0%r (r0 = r /\ i = i0) => //.
            by wp;rnd => //.
            wp;rnd;skip;progress => //. 
            rewrite /bd /mu_x;apply mu_eq => w' //.
            by conseq * Hw;progress => //; rewrite Htk.
          by conseq * (_: _ ==> false) => //.
        (* bounding pr : ! k = r0 /\ k = r *)
       seq 2 : (test i r0) _ 0%r (1%r - bdt*bd) (1%r/bdt) 
                           (i0 = i /\ test i k /\ r0 = r) => //.
         by wp;rnd.
         case (k = r0);first by conseq * (_ : _ ==> false) => //.
         conseq * Hw;progress => //.
         by rewrite H0 //= /charfun (_: (k = r{hr}) = false) 1:neqF //.
         phoare split ! 1%r (bdt*bd);wp;rnd => //.
          skip;progress => //.
          rewrite -(mu_eq (d i{hr}) (cpMem (sub_supp i{hr}))).
            by intros x ; rewrite /= -test_sub_supp.
          apply (mu_cpMem (sub_supp i{hr}) (d i{hr}) bd _) => x Hx.
          by apply d_uni; apply test_in_supp; rewrite -test_sub_supp.
        by conseq * Hw => //; smt.         
        by conseq * (_ : _ ==> true) => //;rnd;skip;progress=> //; smt.
      split; first smt.
      intros z;conseq * (_ : _ ==>  mem r (sub_supp i)); first smt.
      rnd;skip;progress => //.
      rewrite -(mu_eq (d i{hr}) (cpMem (sub_supp i{hr}))) => //.
      rewrite (mu_cpMem (sub_supp i{hr}) (d i{hr}) bd) => // x Hx.
      by apply d_uni; apply test_in_supp; rewrite -test_sub_supp.  
    (* case ! test i0 k *)
    hoare; while (!test i k); first rnd => //.
    by skip;smt.
  qed.

  type t'.
  op d' : input -> t' distr.

  module Sample = {  
    proc sample (i:input) : t' = {
      var r : t';
      r = $(d' i);
      return r;
    }
  }.

  axiom d'_uni : forall i x, in_supp x (d' i) => mu_x (d' i) x = 1%r/(card(sub_supp i))%r.
  
  lemma prSample : forall i k &m, Pr[Sample.sample(i) @ &m : res = k] = mu_x (d' i) k.
  proof -strict.
    intros i0 k &m; byphoare (_: i0 = i ==> k = res) => //;proc.
    rnd;skip;progress.
    by apply (mu_eq (d' i{hr}) (fun (x:t'), k = x) ((=) k)).
  qed.

  equiv Sample_RsampleW (f : t' -> t) (finv : t -> t') : 
     Sample.sample ~ RsampleW.sample : 
       ={i} /\  !test i{2} r{2} /\ weight (d i{2}) = 1%r /\
       (forall rL, in_supp rL (d' i{1}) <=> test i{1} (f rL)) /\
       (forall rR, test i{2} rR => f (finv rR) = rR) /\
       (forall rL, in_supp rL (d' i{1}) => finv (f rL) = rL) ==>
       res{1} = finv res{2}.
  proof -strict.
    bypr (res{1}) (finv res{2}) => //.      
    intros &m1 &m2 k [Heqi [Ht [Hw [Htin [Hffi Hfif]]]]].
    rewrite (_:Pr[RsampleW.sample(i{m2}, r{m2}) @ &m2 : k = finv res] = 
               Pr[RsampleW.sample(i{m2}, r{m2}) @ &m2 : res = f k]).
      byequiv (_: ={i,r} /\ i{2} = i{m2} ==> 
                        ={res} /\ test i{m2} res{2}) => //.
        by proc;while (={i,r});[rnd | ];trivial.
      progress => //. 
        by rewrite Hffi.
      by rewrite Hfif // Htin Heqi.
    rewrite (_:Pr[Sample.sample(i{m1}) @ &m1 : k = res] = 
               Pr[Sample.sample(i{m1}) @ &m1 : res = k]). 
      by rewrite Pr[mu_eq].
    rewrite (prSample i{m1} k &m1) (prRsampleW i{m2} r{m2} (f k) &m2) => //.   
    case (test i{m2} (f k)).
      by rewrite -Heqi -Htin; apply d'_uni.
    rewrite -Heqi -Htin /in_supp;smt.
 qed.

end GenDice.
