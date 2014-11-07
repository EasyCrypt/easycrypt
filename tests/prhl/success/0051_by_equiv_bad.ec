require import Real.

module type Adv = {
  proc a():bool
}.

module M(A:Adv) = {
  var x:int
  var bad : bool
  proc main() : bool = {
    var b : bool;
    x = 1;
    b = A.a();
    return b;
  }
}.

module M'(A:Adv) = {
  var x:int
  var bad:bool
  proc main() : bool = {
    var b : bool;
    x = 1;
    b = A.a();
    return b;
  }
}.

axiom upto1 (A<:Adv{M,M'}) :
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> !M'.bad{2} => res{1} => res{2}]. 

lemma bad1_demo &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  apply (real_le_trans _ (Pr[ M'(A).main() @ &m : res /\ !M'.bad \/ M'.bad])).
    byequiv (_ : ={glob A} ==> !M'.bad{2} => res{1} => res{2}). 
      by apply (upto1 A).
      by [].
    move=> _ _; apply upto_bad_or.
  rewrite Pr [mu_disjoint].
    move=> _; apply upto_bad_false.
  apply addleM.    
    rewrite Pr [mu_sub].
      by move => _;apply upto_bad_sub.
    by [].
  by [].
qed.

lemma bad1_demo1 &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv.
    by apply (upto1 A).
  by [].
qed.

lemma bad1_demo1_app &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto1 A).
  by [].
qed.

lemma bad1_demo1_app' &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res /\ !M'.bad] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto1 A).
  by [].
  smt.
qed.

axiom upto1_eq (A<:Adv{M,M'}) :
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> !M'.bad{2} => res{1} = res{2}]. 

lemma bad1_demo1_eq &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (_ : _ ==> !M'.bad{2} => res{1} = res{2}).
    by apply (upto1_eq A).
  by [].
  smt.
qed.

lemma bad1_demo1_eq_app &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto1_eq A).
  by [].
  smt.
qed.

pred p.
axiom p_ok : p.

axiom upto1_eq' (A<:Adv{M,M'}) : p => 
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> !M'.bad{2} => res{1} = res{2}]. 

lemma bad1_demo1_eq_app_p &m  (A<:Adv{M,M'}) : 
   Pr[ M(A).main() @ &m : res] <=
   Pr[ M'(A).main() @ &m : res] + 
   Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto1_eq' A _).
  apply p_ok.
  by [].
  smt.
qed.

axiom upto2 (A<:Adv{M,M'}) :
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> 
      (M.bad{1} <=> M'.bad{2}) /\ (!M'.bad{2} => (res{1} <=> res{2}))].

lemma bad2_abs_demo &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  apply (real_le_trans _
          `| (Pr[M(A).main() @ &m : res /\ M.bad] + 
               Pr[M(A).main() @ &m : res /\ !M.bad]) -
             (Pr[M'(A).main() @ &m : res /\ M'.bad] + 
               Pr[M'(A).main() @ &m : res /\ !M'.bad])|).
    apply Real.eq_le;congr;congr.
      by rewrite Pr [mu_split (M.bad)].
    by rewrite Pr [mu_split (M'.bad)].
  apply upto2_abs.
  + apply (real_le_trans _ Pr[M(A).main() @ &m : false]).
      by rewrite Pr [mu_false].
    by rewrite Pr [mu_sub].
  + apply (real_le_trans _ Pr[M'(A).main() @ &m : false]).
      by rewrite Pr [mu_false].
    by rewrite Pr [mu_sub].
  + byequiv (upto2 A).
      by trivial. 
    by move=> _ _; apply upto2_imp_bad.
  + by rewrite Pr [mu_sub].
  + byequiv (upto2 A).
      by trivial.
  by move=> _ _; apply upto2_notbad.
qed.

lemma bad1_abs &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (: _ ==> _) : (M.bad).
    by apply (upto2 A).
  by trivial.
qed.

lemma bad1_abs' &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto2 A) : (M.bad).
  by trivial.
qed.

axiom upto2_if (A<:Adv{M,M'}) :
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> 
           if M'.bad{2} then M.bad{1} else !M.bad{1} /\ res{1} = res{2} ].

lemma bad1_abs_sub &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (: _ ==> if M'.bad{2} then M.bad{1} else 
                    !M.bad{1} /\ res{1} = res{2}) : (M.bad).
    by apply (upto2_if A).
  by trivial.
  smt.
qed.

lemma bad1_abs_sub' &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto2_if A) : (M.bad).
  by trivial.
  smt.
qed.

axiom upto2_if_p (A<:Adv{M,M'}) : p =>
  equiv [M(A).main ~ M'(A).main : ={glob A} ==> 
           if M'.bad{2} then M.bad{1} else !M.bad{1} /\ res{1} = res{2} ].

lemma bad1_abs_sub_app &m  (A<:Adv{M, M'}) : 
   `| Pr[ M(A).main() @ &m : res] - Pr[ M'(A).main() @ &m : res] | <=
       Pr[ M'(A).main() @ &m : M'.bad].
proof.
  byequiv (upto2_if_p A _) : (M.bad).
  by apply p_ok.
  by trivial.
  smt.
qed.
