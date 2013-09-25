require import Distr.
require import Int.
require import Real.
require import FSet.

  (* TODO : provide the good lemma in FSet *)
  axiom mu_cpMem (s:'a set): forall (d:'a distr) (bd:real),
    (forall (x : 'a), mem x s => mu_x d x = bd) => 
    mu d (cpMem s) = (card s)%r * bd.

theory GenDice.

  type t.
  type input.
  op d : input -> t distr.

  op test : input -> t -> bool.
  op sub_supp : input -> t set.
  op bd : real.
  axiom d_uni : forall i x, in_supp x (d i) => mu_x (d i) x = bd.

  axiom test_in_supp : forall i x, 
     test i x => in_supp x (d i).

  axiom test_sub_supp : forall i x, 
      mem x (sub_supp i) <=> test i x.

  
  module RsampleW = {
    fun sample (i:input, r:t) : t = {
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
  proof.
    intros i0 dfl0 k.
    pose bdt := (card(sub_supp i0))%r.
    case (test i0 k) => Htk &m Hdfl Hweight;
      bdhoare_deno (_: !test i r /\ i0 = i ==> k = res) => //;fun.
      (* case : test i k *)
      cut Hdiff : ! bdt = (Real.zero)%Real by smt.
      while (i0=i) (if test i r then 0 else 1) 1 (bdt * bd) => //; first 2 smt.
        intros Hw; alias 2 r0 = r.
        cut Htk' := Htk;generalize Htk';rewrite -test_sub_supp => Hmemk.
        bd_hoare split bd ((1%r - bdt*bd) * (1%r/bdt)) : (k=r0).
          by intros _ _; fieldeq => //.
          (* bounding pr : k = r0 /\ k = r *)
          seq 2 : (k = r0) bd 1%r 1%r 0%r (r0 = r /\ i = i0) => //.
            by wp;rnd => //.
            wp;rnd;skip;progress => //. 
            by rewrite -(d_uni i{hr} k) /mu_x; [ smt | apply mu_eq].
            by rcondf 1 => //.
          by conseq * (_: _ ==> false) => //.
          (* bounding pr : ! k = r0 /\ k = r *)
        bd_hoare split 0%r ((1%r - bdt*bd) * (1%r/bdt)) : (test i r0).
          by intros &m1 [ _ H]; fieldeq => //.
          (* bounding pr :  test i r0 /\ ! k = r0 /\ k = r *) 
          seq 2 : (test i r0) 1%r 0%r 1%r 0%r (i0 = i /\ test i k /\ r0 = r) => //.
            by wp;rnd => //.
            by rcondf 1 => //;hoare;skip;smt.
          by conseq * (_ : _ ==> false) => //.
          (* bounding pr :  !test i r0 /\ ! k = r0 /\ k = r *) 
        seq 2 : (test i r0) 1%r 0%r (1%r - bdt*bd) (1%r/bdt) 
                           (i0 = i /\ test i k /\ r0 = r) => //.
          by wp;rnd => //.
          by rcondf 1 => //;hoare;skip;smt.
          bd_hoare split ! 1%r (bdt*bd);wp;rnd => //.
          skip;progress => //.
          rewrite -(mu_eq (d i{hr}) (cpMem (sub_supp i{hr}))).
            by intros x ; rewrite /= -test_sub_supp.
          apply (mu_cpMem (sub_supp i{hr}) (d i{hr}) bd _) => x Hx.
          by apply d_uni; apply test_in_supp; rewrite -test_sub_supp.
        conseq * Hw => //; by smt.
      by conseq * (_ : _ ==> true) => //;rnd;skip;progress=> //; smt.
      intros z;conseq * (_ : _ ==>  mem r (sub_supp i)); first smt.
      rnd;skip;progress => //.
      rewrite -(mu_eq (d i{hr}) (cpMem (sub_supp i{hr}))) => //.
      rewrite (mu_cpMem (sub_supp i{hr}) (d i{hr}) bd) => // x Hx.
      by apply d_uni; apply test_in_supp; rewrite -test_sub_supp.
    (* case ! test i0 k *)
    hoare; while (!test i k); first rnd => //.
    by skip;smt.
  save.

  type t'.
  op d' : input -> t' distr.

  module Sample = {  
    fun sample (i:input) : t' = {
      var r : t';
      r = $(d' i);
      return r;
    }
  }.

  axiom d'_uni : forall i x, in_supp x (d' i) => mu_x (d' i) x = 1%r/(card(sub_supp i))%r.
  
  lemma prSample : forall i k &m, Pr[Sample.sample(i) @ &m : res = k] = mu_x (d' i) k.
  proof.
    intros i0 k &m; bdhoare_deno (_: i0 = i ==> k = res) => //;fun.
    rnd;skip;progress.
    by apply (mu_eq (d' i{hr}) (lambda (x:t'), k = x) ((=) k)).
  save.

  equiv Sample_RsampleW (f : t' -> t) (finv : t -> t') : 
     Sample.sample ~ RsampleW.sample : 
       ={i} /\  !test i{2} r{2} /\ weight (d i{2}) = 1%r /\
       (forall rR, test i{2} rR <=> in_supp (finv rR) (d' i{1})) /\
       (forall rR, test i{2} rR => f (finv rR) = rR) /\
       (forall rL, in_supp rL (d' i{1}) => finv (f rL) = rL) ==>
       f res{1} = res{2}.
  proof.
    bypr (f res{1}) (res{2}) => //.      
    intros &m1 &m2 k [Heqi [Ht [Hw [Htf [Hffi Hfif]]]]].
    rewrite (_:Pr[Sample.sample(i{m1}) @ &m1 : k = f res] = 
             Pr[Sample.sample(i{m1}) @ &m1 : res = finv k]). 
      equiv_deno (_: ={i} /\ i{1} = i{m1} ==> in_supp res{1} (d' i{m1}) /\ ={res}) => //.
        by fun;rnd => //.
      progress. smt. smt.
    rewrite (_:Pr[RsampleW.sample(i{m2}, r{m2}) @ &m2 : k = res] = 
               Pr[RsampleW.sample(i{m2}, r{m2}) @ &m2 : res = k]).
      by equiv_deno (_: ={i,r} ==> ={res}) => //;fun;eqobs_in.
    rewrite (prSample i{m1} (finv k) &m1) (prRsampleW i{m2} r{m2} k &m2) => //.
    case (test i{m2} k) => Htest.
      rewrite d'_uni;[ by rewrite -Htf | by rewrite Heqi].
    generalize Htest;rewrite Htf /in_supp;smt.
 save.

end GenDice.


