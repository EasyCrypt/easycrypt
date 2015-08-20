require import Real.
module type Adv = {
  proc a():bool
}.

module M(A:Adv) = {
  var x:int
  proc main() : bool = {
    var b : bool;
    x = 1;
    b = A.a();
    return b;
  }
}.

lemma test_eq &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] = Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv (_: ={glob A} ==> _ ) => //.
  proc;call (_: true);auto.
qed.

lemma test_eq' &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] = Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv (_: ) => //.
  proc;call (_: true);auto.
qed.

lemma test_eq_opt &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] = Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv [eq] (_: ) => //.
  proc;call (_: true);auto.
qed.

lemma test_eq_opt_no &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] = Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv [-eq] (_: ) => //.
  proc;call (_: true);auto.
qed.

require import Int.

module M'(A:Adv) = {
  var x:int
  proc main(i:int) : bool = {
    var b : bool;
    x = 1 + i;
    b = A.a();
    return b;
  }
}.

lemma test_eqMM' &m (A<:Adv{M,M'}) : 
    Pr[M'(A).main(0) @ &m : res] = Pr[M(A).main() @ &m : res]. 
proof.
  byequiv (_: ) => //. 
  proc;call (_: true);auto.
qed.


lemma test_eqM'M' &m (A<:Adv{M,M'}) : 
    Pr[M'(A).main(0) @ &m : res /\ M'.x = 1] = 
    Pr[M'(A).main(0) @ &m : res /\ M'.x = 1]. 
proof.
  byequiv => //. 
  proc;call (_: true);auto.
qed.

lemma test_le &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] <= 
       Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv (_: ={glob A} ) => //. 
  proc;call (_: true);auto.
qed.

lemma test_ge &m (A<:Adv{M}) : 
    Pr[M(A).main() @ &m : res /\ M.x = 1] >= 
       Pr[M(A).main() @ &m : res /\ M.x = 1]. 
proof.
  byequiv (: ={glob A} ) => //. 
  proc;call (_: true);auto.
qed.
