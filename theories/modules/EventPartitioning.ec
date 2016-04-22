require import NewLogic Option Real List NewDistr.
require import RealExtra StdBigop StdRing StdOrder.
(*---*) import Bigreal BRA RField IntOrder RealOrder.

pragma -oldip. pragma +implicits.

type input, output.

module type T = {
  proc f(_: input): output
}.

abstract theory ListPartitioning.
  type partition.

  section.
  declare module M : T.

  lemma list_partitioning
          (i : input)
          (E : input -> (glob M) -> output -> bool)
          (phi : input -> (glob M) -> output -> partition)
          (P : partition list) &m:
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
end ListPartitioning.

abstract theory FSetPartitioning.
  require import FSet.

  type partition.

  section.
  declare module M : T.

  local clone import ListPartitioning with
    type partition <- partition.

  lemma fset_partitioning
          (i : input)
          (E : input -> (glob M) -> output -> bool)
          (phi : input -> (glob M) -> output -> partition)
          (P : partition fset) &m:
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a =>
                   Pr[M.f(i) @ &m: E i (glob M) res /\ phi i (glob M) res = a]) (elems P)
      + Pr[M.f(i) @ &m: E i (glob M) res /\ !mem P (phi i (glob M) res)].
  proof.
  by rewrite memE; exact/(@list_partitioning M i E phi (elems P) &m _)/uniq_elems.
  qed.
  end section.
end FSetPartitioning.

abstract theory FPredPartitioning.
  require import Finite.

  type partition.

  section.
  declare module M : T.

  local clone import ListPartitioning with
    type partition <- partition.

  lemma fpred_partitioning
          (i : input)
          (E : input -> (glob M) -> output -> bool)
          (phi : input -> (glob M) -> output -> partition)
          (P : partition -> bool) &m:
    is_finite P =>
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a =>
                   Pr[M.f(i) @ &m: E i (glob M) res /\ phi i (glob M) res = a]) (to_seq P)
      + Pr[M.f(i) @ &m: E i (glob M) res /\ !P (phi i (glob M) res)].
  proof.
  move=> ^/mem_to_seq <- /uniq_to_seq.
  exact/(@list_partitioning M i E phi (to_seq P) &m).
  qed.
  end section.
end FPredPartitioning.

theory ResultPartitioning.
  section.
  declare module M : T.

  local clone import ListPartitioning with
    type partition <- output.

  lemma result_partitioning
          (i : input)
          (E : input -> (glob M) -> output -> bool)
          (X : input -> output list)
          &m:
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a=> Pr[M.f(i) @ &m: E i (glob M) res /\ res = a]) (undup (X i))
      + Pr[M.f(i) @ &m: E i (glob M) res /\ !mem (X i) res].
  proof.
  rewrite -mem_undup.
  exact/(@list_partitioning M i E (fun _ _ x=> x) (undup (X i)) &m)/undup_uniq.
  qed.
  end section.
end ResultPartitioning.

theory TotalResultPartitioning.
  (*---*) import ResultPartitioning.

  section.
  declare module M : T.

  lemma total_result_partitioning
          (i : input)
          (E : input -> (glob M) -> output -> bool)
          (X : input -> output list)
          &m:
    (forall i, hoare [M.f: arg = i ==> mem (X i) res]) =>
    Pr[M.f(i) @ &m: E i (glob M) res]
    = big predT (fun a => Pr[M.f(i) @ &m: E i (glob M) res /\ res = a]) (undup (X i)).
  proof.
  move=> support_M.
  rewrite (@result_partitioning M i E X &m).
  have ->: Pr[M.f(i) @ &m: E i (glob M) res /\ !mem (X i) res]
           = Pr[M.f(i) @ &m: false].
    rewrite Pr[mu_false]; byphoare (_: arg = i ==> _)=> //=.
    by hoare; conseq (support_M i)=> />.
  by rewrite Pr[mu_false].
  qed.
  end section.
end TotalResultPartitioning.

theory TotalSubuniformResultOnly.
  import TotalResultPartitioning.

  section.
  declare module M : T.

  axiom M_suf a b i X &m:
       mem (X i) a
    => mem (X i) b
    => Pr[M.f(i) @ &m: res = a] = Pr[M.f(i) @ &m: res = b].

  lemma subuniform_result i X a &m:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => mem (X i) a
    => Pr[M.f(i) @ &m: true] = (size (undup (X i)))%r * Pr[M.f(i) @ &m: res = a].
  proof.
  move=> support_M a_in_X.
  rewrite
    (@total_result_partitioning M i (fun _ _=> predT) X &m) //
    big_seq (@eq_bigr _ _ (fun b=> Pr[M.f(i) @ &m: res = a])).
  + by move=> b /=; rewrite mem_undup=> b_in_X; exact/(@M_suf b a i X &m).
  rewrite -big_seq big_const count_predT -AddMonoid.iteropE -intmulpE 1:size_ge0.
  by rewrite intmulr mulrC.
  qed.
  end section.
end TotalSubuniformResultOnly.

theory SubuniformReference.
  import TotalSubuniformResultOnly.
  (*---*) import MUniform DScalar.

  (* "fun i=> Pr[M.f(i) @ &m: true]" is not well-defined because of &m *)
  op k : { input -> real | forall i, 0%r < k i <= 1%r } as k_in_unit.

  lemma gt0_k i: 0%r < k i  by move: (k_in_unit i).
  lemma le1_k i: k i <= 1%r by move: (k_in_unit i).

  module Ref = {
    proc f(i : input, xs : output list): output = {
      var r;

      r <$ (k i) \cdot (duniform xs);
      return r;
    }
  }.

  section.
  declare module M : T.

  axiom M_suf a b i X &m:
       mem (X i) a
    => mem (X i) b
    => Pr[M.f(i) @ &m: res = a] = Pr[M.f(i) @ &m: res = b].

  axiom weight_M: phoare [M.f: true ==> true] =(k arg).

  lemma pr_res_notin_X a i X &m:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => !mem (X i) a
    => Pr[M.f(i) @ &m: res = a] = 0%r.
  proof.
  move=> support_M a_notin_X.
  byphoare (_: arg = i ==> _)=> //=; hoare; conseq (support_M i)=> &hr /> r.
  by apply/(@contra (r = a) (!mem (X arg{hr}) r))=> ->.
  qed.

  lemma is_subuniform i X a &m:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => mem (X i) a
    => Pr[M.f(i) @ &m: res = a] = (k i)/(size (undup (X i)))%r.
  proof.
  move=> support_M a_in_X; have <-: Pr[M.f(i) @ &m: true] = (k i).
  + by byphoare (_: arg = i ==> true)=> //=; conseq weight_M.
  rewrite (@subuniform_result M M_suf i X a &m support_M a_in_X) mulrAC divff //.
  rewrite eq_fromint size_eq0 undup_nilp -implybF=> h.
  by move: a_in_X; rewrite h.
  qed.

  lemma eq_M_Ref &m X:
       (forall i, hoare [M.f: arg = i ==> mem (X i) res])
    => (forall i, X i <> [])
    => equiv [M.f ~ Ref.f: (i,xs){2} = (arg,X arg){1} ==> ={res}].
  proof.
  move=> support_M Xi_neq0.
  bypr (res{1}) (res{2})=> //= &1 &2 a [] i_def xs_def.
  rewrite !(@eq_sym a); case: (mem (X arg{1}) a); last first.
  + move=> ^a_notin_X /(@pr_res_notin_X a arg{1} X &1 support_M) ->.
    byphoare (_: (i,xs) = (arg,X arg){1} ==> _)=> //=.
    hoare; proc; auto=> /> r.
    rewrite -/(support _ _) support_dscalar_gt0 1:gt0_k.
    + by rewrite duniform_ll 1:Xi_neq0 // le1_k.
    by case: (r = a)=> [->|]; first by rewrite duniform_fu.
  move=> a_in_X. rewrite (@is_subuniform arg{1} X a &1 support_M a_in_X).
  byphoare (_: (i,xs) = (i,xs){2} ==> _)=> //=; proc; rnd (pred1 a); auto=> />.
  rewrite dscalar1E 1:ltrW 1:gt0_k.
  + by rewrite duniform_ll 1:xs_def 1:Xi_neq0 //= le1_k.
  by rewrite duniform1E i_def xs_def a_in_X.
  qed.
  end section.
end SubuniformReference.
