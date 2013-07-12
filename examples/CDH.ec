require import Int.
require import Real.
require import Set_Why.


(** Minimalist group theory with only needed components *)
theory Group.

  type group.

  const q : int.

  const g : group.

  axiom q_pos  : 0 < q.

  op ( * ) : group -> group -> group.

  op ( ^ ) : group -> int -> group.

  axiom pow_mult (x, y:int) : (g ^ x) ^ y = g ^ (x * y).
 
  axiom pow_plus (x, y:int) : (g ^ x) * (g ^ y) = g ^ (x + y).

end Group.


(** Computational Diffie-Hellman problem *)
theory CDH.

  import Group.

  module type Adversary = {
    fun solve(gx:group, gy:group) : group
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
  import Fset.
  import FsetNth.

  const n : int.

  module type Adversary = {
    fun solve(gx:group, gy:group) : group set
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
      var i : int;

      s = A.solve(gx, gy);
      i = $[0.. card s - 1];
      return (nth i s);
    }
  }.

  (** Naive reduction to CDH *)

  (* Useful lemmas on reals, maybe move to Real.ec *)
  lemma nosmt le_compat_r (w x y: real) : 0%r < w => x * w <= y * w => x <= y 
  by [].

  lemma inv_le (x y:real) : 0%r < x => 0%r < y => y <= x => inv x <= inv y.
  proof.
    intros _ _ _.
    apply (le_compat_r x); first trivial.
    apply (le_compat_r y); first trivial.
    cut H : ((x * inv x) * y <= (y * inv y) * x); last smt.
    rewrite (Inverse y _); first smt.
    rewrite (Inverse x _); smt.
  qed.

  lemma nosmt div_le (x y:real) : 
    0%r < x => 0%r < y => y <= x => 1%r / x <= 1%r / y 
  by [].

  lemma mult_inv_le_r (x y z:real) : 
    0%r < x => (1%r / x) * y <= z => y <= x * z
  by admit. (*[]*)

  lemma Reduction (A <: Adversary) &m :
    0 < n =>
    exists (B <: CDH.Adversary), 
      1%r / n%r * Pr[SCDH(A).main() @ &m : res] <=
      Pr[CDH.CDH(B).main() @ &m : res]. 
  proof.
    intros n_pos.
    exists (CDH_from_SCDH(A)).
    bdhoare_deno (_ : true ==> _); [ | trivial | trivial ].
    fun; inline CDH_from_SCDH(A).solve.
    seq 6 : (nth i s = g ^ (x * y)) (1%r / n%r) 1%r (1%r -(1%r / n%r))  0%r.
    by rnd; call (_ : true); wp; do rnd; skip; smt.
    rnd (lambda i, nth i s = g ^ (x * y)) => /=.
    seq 5: (mem (g ^ (x * y)) s /\ card s <= n) 1%r 1%r 0%r 0%r.
    by call (_ : true); wp; do rnd; skip; smt.
    (* This is exactly the SCDH(A) game in the bound *)
    admit.
    skip; intros &m1 H.
    apply (Trans _ (1%r / (card s{m1})%r)).
    apply div_le; smt.
    apply (mu_choose_mem s{m1} (g ^ (x{m1} * y{m1})) _); first smt. 
    (* This is exactly the SCDH(A) game in the bound *)
    admit.
    by smt.
    by wp; skip; trivial.
    by hoare;wp;skip;smt.
    progress.
    cut _: (Pr[SCDH(A).main() @ &m : res] <= 1%r); first by smt.
    cut lem : forall (x y z : real), x <= y => 0%r < z => x / z <= y / z;
    first by admit (*smt*).
    by apply lem; smt.
  qed.  


  (** Shoup's reduction to CDH -- would be nice to prove a bound *)

  import MapFilter.

  module CDH_from_SCDH_Shoup (A:Adversary, B:Adversary) : CDH.Adversary = {
    fun solve(gx:group, gy:group) : group = {
      var a, b : int;
      var s1, s2 : group set;
      var r : group;

      s1 = A.solve(gx, gy);
      a = $[0..q-1];
      b = $[0..q-1];
      s2 = B.solve(gx ^ a * g ^ b, g ^ b);    
      r = choose (filter (lambda (z:group), mem (z ^ a * gy ^ b) s2) s1);
      return r;
    }
  }.

end Set_CDH.
