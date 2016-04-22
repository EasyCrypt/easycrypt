require import NewLogic Option Real List NewDistr.
require import RealExtra StdBigop StdRing StdOrder.
(*---*) import Bigreal BRA RField IntOrder RealOrder.

pragma -oldip. pragma +implicits.

type input, output.

module type T = {
  proc f(_: input): output
}.

abstract theory Partitioning.
  type partition.

  section.
  declare module M : T.

  lemma probability_partitioning
          &m i (E : input -> (glob M) -> output -> bool)
          (phi : input -> (glob M) -> output -> partition) P:
    uniq P =>
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a =>
                   Pr[M.f(i) @ &m: E i (glob M) res /\ phi i (glob M) res = a]) P
      + Pr[M.f(i) @ &m: E i (glob M) res /\ !mem P (phi i (glob M) res)].
  proof.
  move=> uniq_P. rewrite Pr[mu_split (mem P (phi i (glob M) res))]; congr.
  elim: P uniq_P=> /=; first by rewrite big_nil Pr[mu_false].
  move=> x xs ih [] x_notin_xs uniq_xs /=.
  rewrite {1}andb_orr Pr[mu_or] andbCA !andbA andbb.
  have ->: Pr[M.f(i) @ &m: (   E i (glob M) res
                            /\ phi i (glob M) res = x)
                           /\ mem xs (phi i (glob M) res)]
           = Pr[M.f(i) @ &m: false].
  + by rewrite Pr[mu_eq] // => &hr /#.
  by rewrite Pr[mu_false] //= big_cons {1}/predT /=; congr; exact/ih.
  qed.
  end section.
end Partitioning.

theory TotalResultPartitioning.
  section.
  declare module M : T.

  local clone import Partitioning with type partition <- output.

  lemma Pr_support_split &m i X (E : input -> (glob M) -> output -> bool):
    (forall i, hoare [M.f: arg = i ==> mem (X i) res]) =>
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a => Pr[M.f(i) @ &m: E i (glob M) res /\ res = a]) (undup (X i)).
  proof.
  move=> support_M.
  rewrite (@probability_partitioning M &m i E (fun _ _ x => x) (undup (X i))) 1:undup_uniq.
  have ->: Pr[M.f(i) @ &m: E i (glob M) res /\ !mem (undup (X i)) res]
           = Pr[M.f(i) @ &m: false].
    rewrite Pr[mu_false]; byphoare (_: arg = i ==> _)=> //=.
    by hoare; conseq (support_M i)=> /> &hr r gm; rewrite mem_undup=> />.
  by rewrite Pr[mu_false].
  qed.
  end section.
end TotalResultPartitioning.

theory TotalSubuniformPartitioning.
  section.
  declare module M : T.

  axiom M_subuniform a b X &m i:
       mem (X i) a
    => mem (X i) b
    => Pr[M.f(i) @ &m: res = a] = Pr[M.f(i) @ &m: res = b].

  lemma Pr_subuniform_split &m i X a:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => mem (X i) a
    => Pr[M.f(i) @ &m: true] = (size (undup (X i)))%r * Pr[M.f(i) @ &m: res = a].
  proof.
  move=> support_M a_in_X.
  rewrite
    (@TotalResultPartitioning.Pr_support_split M &m i X (fun _ _=> predT)) //
    big_seq (@eq_bigr _ _ (fun b=> Pr[M.f(i) @ &m: res = a])).
  + by move=> b /=; rewrite mem_undup=> b_in_X; apply/(@M_subuniform b a X &m i).
  rewrite -big_seq big_const count_predT -AddMonoid.iteropE -intmulpE 1:size_ge0.
  by rewrite intmulr mulrC.
  qed.
  end section.
end TotalSubuniformPartitioning.

theory ScaledUniformByResult.
  (*---*) import MUniform DScalar.

  (* "fun i=> Pr[M.f(i) @ &m: true]" is not well-defined because of &m *)
  op k : { input -> real | forall i, 0%r < k i <= 1%r } as k_in_unit.

  lemma gt0_k i: 0%r < k i  by move: (k_in_unit i).
  lemma le1_k i: k i <= 1%r by move: (k_in_unit i).

  (* The first few Sections are more general than this: generalize them and push them out? *)
  section.
  declare module M : T.

  axiom M_subuniform a b X &m i:
       mem (X i) a
    => mem (X i) b
    => Pr[M.f(i) @ &m: res = a] = Pr[M.f(i) @ &m: res = b].

  axiom weight_M: phoare [M.f: true ==> true] =(k arg).

  lemma Pr_a_notin_X &m i X a:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => !mem (X i) a
    => Pr[M.f(i) @ &m: res = a] = 0%r.
  proof.
  move=> support_M a_notin_X.
  byphoare (_: arg = i ==> _)=> //=; hoare; conseq (support_M i)=> &hr /> r.
  by apply/(@contra (r = a) (!mem (X arg{hr}) r))=> ->.
  qed.

  lemma Pr_uniform &m i X a:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => mem (X i) a
    => Pr[M.f(i) @ &m: res = a] = (k i)/(size (undup (X i)))%r.
  proof.
  move=> support_M a_in_X; have <-: Pr[M.f(i) @ &m: true] = (k i).
  + by byphoare (_: arg = i ==> true)=> //=; conseq weight_M.
  rewrite (@TotalSubuniformPartitioning.Pr_subuniform_split M M_subuniform &m i X a support_M a_in_X) mulrAC divff //.
  rewrite eq_fromint size_eq0 undup_nilp -implybF=> h.
  by move: a_in_X; rewrite h.
  qed.

  module Reference = {
    proc f(i: input, xs : input -> output list): output = {
      var r;

      r <$ (k i) \cdot (duniform (xs i));
      return r;
    }
  }.

  lemma M_uniform &m X:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => (forall i, X i <> [])
    => equiv [M.f ~ Reference.f: arg{1} = i{2} /\ xs{2} = X ==> ={res}].
  proof.
  move=> support_M Xi_neq0.
  bypr (res{1}) (res{2})=> //= &1 &2 a [] i_def xs.
  rewrite !(@eq_sym a); case: (mem (X arg{1}) a); last first.
  + move=> ^a_notin_X /(@Pr_a_notin_X &1 arg{1} X a support_M) ->.
    byphoare (_: arg = (i,xs){2} ==> _)=> //=; hoare; proc; auto=> /> r.
    rewrite -/(support _ _) support_dscalar_gt0 1:gt0_k.
    + by rewrite duniform_ll 1:xs 1:Xi_neq0 // le1_k.
    by case: (r = a)=> [->|]; first by rewrite xs -i_def duniform_fu.
  move=> a_in_X. rewrite (@Pr_uniform &1 arg{1} X a support_M a_in_X).
  byphoare (_: arg = (i,xs){2} ==> _)=> //=; proc; rnd (pred1 a); auto=> />.
  rewrite -i_def xs dscalar1E 1:ltrW 1:gt0_k.
  + by rewrite duniform_ll 1:Xi_neq0 //= le1_k.
  by rewrite duniform1E a_in_X.
  qed.
  end section.
end ScaledUniformByResult.
