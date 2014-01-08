require import Int.
require import Real.
require import FSet.


(** Minimalist group theory with only needed components *)
theory Group.

  type group.

  const q : int.

  const g : group.

  axiom q_pos  : 0 < q.

  op ( * ) : group -> group -> group.

  op ( ^ ) : group -> int -> group.

  axiom pow_mult (x y:int) : (g ^ x) ^ y = g ^ (x * y).
 
  axiom pow_plus (x y:int) : (g ^ x) * (g ^ y) = g ^ (x + y).

end Group.


(** Computational Diffie-Hellman problem *)
theory CDH.

  import Group.

  module type Adversary = {
    fun solve(gx gy:group) : group {*}
  }.

  module CDH (A:Adversary) = {
    fun main() : bool = {
      var x, y : int;
      var r : group;

      x = $[0..q-1];
      y = $[0..q-1];
      r = A.solve(g ^ x, g ^ y);
      return (r = g ^ (x * y));
    }
  }.

end CDH.


(** Set version of the Computational Diffie-Hellman problem *)
theory Set_CDH.

  import Group.

  const n : int.

  module type Adversary = {
    fun solve(gx:group, gy:group) : group set {*}
  }.

  module SCDH (B:Adversary) = {
    fun main() : bool = {
      var x, y : int;
      var s : group set;

      x = $[0..q-1];
      y = $[0..q-1];
      s = B.solve(g ^ x, g ^ y);
      return (mem (g ^ (x * y)) s /\ card s <= n);
    }
  }.

  module CDH_from_SCDH (A:Adversary) : CDH.Adversary = {
    fun solve(gx:group, gy:group) : group = {
      var s : group set;
      var x : group;

      s = A.solve(gx, gy);
      x = $Duni.duni s;
      return x;
    }
  }.


  (** Naive reduction to CDH *)

  (* Useful lemmas on reals, maybe move to Real.ec *)
  lemma nosmt le_compat_r (w x y: real) : 0%r < w => x * w <= y * w => x <= y 
  by [].

  lemma nosmt inv_le (x y:real) : 0%r < x => 0%r < y => y <= x => inv x <= inv y.
  proof.
    intros _ _ _.
    apply (le_compat_r x); first trivial.
    apply (le_compat_r y); first trivial.
    cut H : ((x * inv x) * y <= (y * inv y) * x); last smt.
    rewrite (Inverse y _); first smt.
    by rewrite (Inverse x _); smt.
  qed.

  lemma div_le (x y:real) : 
    0%r < x => 0%r < y => y <= x => 1%r / x <= 1%r / y .
  proof.
    by progress; cut X := inv_le x y; smt.
  qed.

  lemma mu_duni_mem (s:'a set) (x:'a) :
    mem x s => 1%r / (card s)%r <= mu (Duni.duni s) ((=) x).
  proof.
    by intros _; rewrite Duni.mu_def; smt.
  qed.

  module SCDH' (A:Adversary) = {
    var x, y : int

    fun aux() : group set = {
      var s : group set;
      x = $[0..q-1];
      y = $[0..q-1];
      s = A.solve(g ^ x, g ^ y);
      return s;
    }

    fun main() : bool = {
      var z : group;
      var s : group set;
      s = aux();
      z = $Duni.duni s;
      return z = g ^ (x * y);
    }
  }.

  lemma Reduction (A <: Adversary {SCDH'}) &m :
    0 < n =>
    exists (B <: CDH.Adversary), 
      1%r / n%r * Pr[SCDH(A).main() @ &m : res] <=
      Pr[CDH.CDH(B).main() @ &m : res]. 
  proof.
   intros n_pos; exists (CDH_from_SCDH(A)).
   apply (Trans _ Pr[SCDH'(A).main() @ &m : res]); first last.
     equiv_deno (_ : true ==> ={res}) => //.
     fun; inline CDH_from_SCDH(A).solve SCDH'(A).aux.
     by wp; rnd; wp; call (_:true); wp; do rnd.
   
     bdhoare_deno (_ : true ==> _) => //.
     fun. 
     seq 1 : (mem (g ^ (SCDH'.x * SCDH'.y)) s /\ card s <= n)
             Pr[SCDH(A).main() @ &m: res]
             (1%r / n%r)
             (1%r - Pr[SCDH(A).main() @ &m: res])
             0%r => //. 
       conseq (_ : _ : = (Pr[SCDH(A).main() @ &m : res])).
       call (_ : true ==> mem (g ^ (SCDH'.x * SCDH'.y)) res /\ card res <= n) => //.
       bypr; progress.
       equiv_deno (_: 
         true ==> 
         (mem (g ^ (SCDH'.x * SCDH'.y)) res /\ card res <= n){1} = res{2}) => //.
       fun *; inline SCDH(A).main SCDH'(A).aux; wp.
       by call (_:true); do rnd; skip; smt.
       
       rnd ((=) (g ^ (SCDH'.x * SCDH'.y))).
       by skip => &m1 H1; split => //; rewrite Duni.mu_def; smt.
  qed.  

  (** Shoup's reduction to CDH -- would be nice to prove a bound *)

  module CDH_from_SCDH_Shoup (A:Adversary, B:Adversary) : CDH.Adversary = {
    fun solve(gx:group, gy:group) : group = {
      var a, b : int;
      var s1, s2 : group set;
      var r : group;

      s1 = A.solve(gx, gy);
      a = $[0..q-1];
      b = $[0..q-1];
      s2 = B.solve(gx ^ a * g ^ b, g ^ b);    
      r = pick (filter (lambda (z:group), mem (z ^ a * gy ^ b) s2) s1);
      return r;
    }
  }.

end Set_CDH.
