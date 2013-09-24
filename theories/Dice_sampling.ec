require import Distr.
require import Int.
require import Real.
require import FSet.

require import AlgTactic.

print theory Real.
instance ring with real
  op rzero = Real.zero
  op rone  = Real.one
  op add   = Real.( + )
  op opp   = Real.([-])
  op mul   = Real.( * )
  op expr  = Real.PowerInt.( ^ )
  op sub   = Real.(-)
  op ofint = FromInt.from_int

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

instance field with real
  op rzero = Real.zero
  op rone  = Real.one
  op add   = Real.( + )
  op opp   = Real.([-])
  op mul   = Real.( * )
  op expr  = Real.PowerInt.( ^ )
  op sub   = Real.(-)
  op ofint = FromInt.from_int
  op inv   = Real.inv
  op div   = Real.(/)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by admit
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

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
        conseq (_: _ ==> (k = r0 /\ k = r) \/ (k <> r0 /\ k = r)); first by smt.
        cut Htk' := Htk;generalize Htk';rewrite -test_sub_supp => Hmemk.
        bd_hoare split bd ((1%r - bdt*bd) * (1%r/bdt)).
          by intros _ _; fieldeq => //.
          (* bounding pr : k = r0 /\ k = r *)
          seq 2 : (k = r0) bd 1%r 1%r 0%r (r0 = r /\ i = i0) => //.
            by wp;rnd => //.
            wp;rnd;skip;progress => //. 
            rewrite -(d_uni i{hr} k) /mu_x; first smt.
            by apply mu_eq => //.
            rcondf 1 => //.
            conseq * (_: _ ==> false) => //.
          (* bounding pr : ! k = r0 /\ k = r *)
          conseq * (_: _ ==> (test i r0 /\ !k=r0 /\ k = r) \/ (!test i r0 /\ !k = r0 /\ k = r));
            first by smt.
          bd_hoare split 0%r ((1%r - bdt*bd) * (1%r/bdt)).
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
          (* the events are disjoint *)        
          by conseq * ( _ : _ ==> false) => //.
        (* The events are disjoint *)
        by conseq * (_ : _ ==> false) => //.
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

theory Dice4_6.

 op d6 (i:unit) = [1..6].
 op test4 (i:unit) x = 1 <= x <= 4.
 op sub_supp (i:unit) = Interval.interval 1 4.
 op bd6 = 1%r/6%r.
 op d4 (i:unit) = [1..4].

 lemma d6_uni: forall (i : unit) (x : int), in_supp x (d6 i) => mu_x (d6 i) x = bd6.
 proof.
   intros i x; apply (Distr.Dinter.mu_x_def_in 1 6 x).
 save.

 lemma test_in_supp: forall (i : unit) (x : int), test4 i x => in_supp x (d6 i).
 proof.
   intros i x;rewrite /test4 /d6 Dinter.supp_def;smt.
 save.

 lemma test_sub_supp: forall (i : unit) (x : int), mem x (sub_supp i) <=> test4 i x.
 proof. 
  (*PY: Bug ? *)
(*  intros i x; apply (Interval.mem_interval 1 4). *)
  intros i x;rewrite /sub_supp /test4;apply Interval.mem_interval.
 save.

 lemma d'_uni: forall (i : unit) (x : int),
           in_supp x (d4 i) => mu_x (d4 i) x = 1%r / (card (sub_supp i))%r.
 proof.
   intros i x;rewrite /d4 /sub_supp Interval.card_interval_max /max /=.
   apply (Distr.Dinter.mu_x_def_in 1 4 x).
 save.
 
 clone GenDice as D4_6 with 
   type t <- int,
   type input <- unit,
   op d <- d6,
   op test <- test4,
   op sub_supp <- sub_supp,
   op bd <- bd6,
   type t' <- int,
   op d' <- d4
   proof * by smt.

  module D4 = {
    fun sample () : int = { 
      var r : int;
      r = $[1..4];
      return r;
    }
  }.

  lemma prD4 : forall k &m, Pr[D4.sample() @ &m : res = k] = 
     if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
  proof.
    intros k &m;bdhoare_deno (_: true ==> k = res) => //.
    fun;rnd;skip;progress => //.
    rewrite (_:mu [1..4] (lambda (x : int), k = x) = mu_x [1..4] k).
      rewrite /mu_x;apply mu_eq => //.
    case (1 <= k && k <= 4) => Hk; 
     [rewrite Dinter.mu_x_def_in // | rewrite Dinter.mu_x_def_notin //];
    rewrite Dinter.supp_def => //. 
  save.

  module D6 = {
    fun sample () : int = {
      var r : int;
      r = 5;
      while (5 <= r) r = $[1..6];
      return r;
    }
  }.

  equiv D4_Sample : D4.sample ~ D4_6.Sample.sample : true ==> ={res}.
  proof. fun;rnd => //. save.

  equiv D6_RsampleW : D6.sample ~ D4_6.RsampleW.sample : r{2} = 5 ==> ={res}.
  proof. 
    fun;while (={r}).
      rnd;skip;progress => //; smt.
    wp => //.
  save.

  lemma D4_D6 (f finv : int -> int) :
      (forall i, 1 <= i <= 4 <=> 1 <= finv i <= 4) =>
      (forall i, 1 <= i <= 4 => f (finv i) = i /\ finv (f i) = i) =>
      equiv [D4.sample ~ D6.sample : true ==> f res{1} = res{2}].
  proof.
    intros Hbound Hbij.
    transitivity D4_6.Sample.sample (true ==> ={res}) (true ==> f res{1} = res{2}) => //.
      by apply D4_Sample.
    transitivity D4_6.RsampleW.sample (r{2} = 5 ==> f res{1} = res{2})
      (r{1} = 5 ==> res{2} = res{1}) => //.
      by intros _ _ _;exists 5 => //.
      conseq (D4_6.Sample_RsampleW f finv) => //.
      rewrite /d6 /test4 /d4 => &m1 &m2 -> /=;split; first by smt.
      split; first by rewrite Dinter.weight_def.
      split; first by intros x;rewrite Dinter.supp_def;apply Hbound.
      split; first by intros x Hx;elim (Hbij x _).
      by intros x; rewrite Dinter.supp_def => Hx;elim (Hbij x _).
    by symmetry;apply D6_RsampleW.
  save.

  lemma prD6 : forall k &m, Pr[D6.sample() @ &m : res = k] = 
      if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
  proof.
    intros k &m. 
    rewrite -(_:Pr[D4.sample() @ &m : res = k] = Pr[D6.sample() @ &m : res = k]).
      by equiv_deno (D4_D6 (lambda x, x) (lambda x, x) _ _).
    by apply (prD4 k &m). 
  save.

end Dice4_6.

