require import Int.
require import Real.
require import FSet.


(** Minimalist group theory with only needed components *)
theory Group.
  type group.

  const q: int.
  const g: group.
  axiom q_pos: 0 < q.

  op ( * ): group -> group -> group.
  op ( ^ ): group -> int -> group.

  axiom pow_mult (x y:int): (g ^ x) ^ y = g ^ (x * y). 
  axiom pow_plus (x y:int): (g ^ x) * (g ^ y) = g ^ (x + y).
end Group.

(** Computational Diffie-Hellman problem *)
theory CDH.
  import Group.

  module type Adversary = {
    proc solve(gx gy:group): group
  }.

  module CDH (A:Adversary) = {
    proc main(): bool = {
      var x, y, r;

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

  const n: int.

  module type Adversary = {
    proc solve(gx:group, gy:group): group set
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x = $[0..q-1];
      y = $[0..q-1];
      s = B.solve(g ^ x, g ^ y);
      return (mem (g ^ (x * y)) s /\ card s <= n);
    }
  }.

  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s = A.solve(gx, gy);
      x = $Duni.duni s;
      return x;
    }
  }.

  (** Naive reduction to CDH *)
  (* Useful lemmas on reals, maybe move to Real.ec *)
  lemma nosmt le_compat_r (w x y:real): 0%r < w => x * w <= y * w => x <= y 
  by [].

  lemma nosmt inv_le (x y:real): 0%r < x => 0%r < y => y <= x => inv x <= inv y.
  proof.
    move=> _ _ _.
    apply (le_compat_r x); first trivial.
    apply (le_compat_r y); first trivial.
    cut H: ((x * inv x) * y <= (y * inv y) * x); last smt.
    rewrite (Inverse y _); first smt.
    by rewrite (Inverse x _); smt.
  qed.

  lemma div_le (x y:real): 
    0%r < x => 0%r < y => y <= x => 1%r / x <= 1%r / y .
  proof. by progress; cut X:= inv_le x y; smt. qed.

  lemma mu_duni_mem (s:'a set) (x:'a):
    mem x s => 1%r / (card s)%r <= mu (Duni.duni s) ((=) x).
  proof. by intros _; rewrite Duni.mu_def; smt. qed.

  section.
    declare module A: Adversary.

    local module SCDH' = {
      var x, y: int

      proc aux(): group set = {
        var s;

        x = $[0..q-1];
        y = $[0..q-1];
        s = A.solve(g ^ x, g ^ y);
        return s;
      }

      proc main(): bool = {
        var z, s;

        s = aux();
        z = $Duni.duni s;
        return z = g ^ (x * y);
      }
    }.

    lemma Reduction &m:
      0 < n =>
      1%r / n%r * Pr[SCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res].
    proof.
      move=> n_pos.
      apply (Trans _ Pr[SCDH'.main() @ &m: res]); first last.
        byequiv (_: ={glob A} ==> ={res})=> //.
        proc; inline CDH_from_SCDH(A).solve SCDH'.aux.
        by wp; rnd; wp; call (_: true); wp; do rnd.
      byphoare (_: (glob A) = (glob A){m} ==> _)=> //.
      pose d:= 1%r/n%r * Pr[SCDH(A).main() @ &m: res]; conseq (_: _: >= d). (* bug *)
      pose d':= Pr[SCDH(A).main() @ &m: res].
      proc.
      seq  1: (mem (g ^ (SCDH'.x * SCDH'.y)) s /\ card s <= n)
              d' (1%r / n%r) _ 0%r => //. 
        conseq (_ : (glob A) = (glob A){m} : = d').
        call (_: (glob A) = (glob A){m} ==> mem (g ^ (SCDH'.x * SCDH'.y)) res /\ card res <= n) => //.
        bypr; progress; rewrite /d'.
        byequiv (_: ={glob A} ==>
                    (mem (g ^ (SCDH'.x * SCDH'.y)) res /\
                     card res <= n){1} = res{2}) => //.
        proc*; inline SCDH(A).main SCDH'.aux; wp.
        by call (_: true); do rnd.
      rnd ((=) (g ^ (SCDH'.x * SCDH'.y))).
      skip; progress; rewrite Duni.mu_def; first smt.
      cut ->: card (filter ((=) (g ^ (SCDH'.x * SCDH'.y))) s){hr} = 1 by smt.
      by apply div_le; expect 3 smt.
    qed.  
  end section.

(*
  (** Shoup's reduction to CDH -- would be nice to prove a bound *)
  module CDH_from_SCDH_Shoup (A:Adversary, B:Adversary) : CDH.Adversary = {
    proc solve(gx:group, gy:group) : group = {
      var a, b, s1, s2, r;

      s1 = A.solve(gx, gy);
      a = $[0..q-1];
      b = $[0..q-1];
      s2 = B.solve(gx ^ a * g ^ b, g ^ b);    
      r = pick (filter (fun (z:group), mem (z ^ a * gy ^ b) s2) s1);
      return r;
    }
  }.
*)
end Set_CDH.
