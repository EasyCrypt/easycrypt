(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require import Int.
require import Real.
require import FSet.

require (*  *) CyclicGroup.

clone export CyclicGroup as G.

theory DDH.
   
  module type Adversary = {
    proc guess(gx gy gz:G.group): bool
  }.

  module DDH0 (A:Adversary) = {
    proc main() : bool = {
      var b, x, y;
      x = $FDistr.dt;
      y = $FDistr.dt;
      b = A.guess(g ^ x, g ^ y, g ^ (x*y));
      return b;
    }
  }.

  module DDH1 (A:Adversary) = {
    proc main() : bool = {
      var b, x, y, z;
        
      x = $FDistr.dt;
      y = $FDistr.dt;
      z = $FDistr.dt;
      b = A.guess(g ^ x, g ^ y, g ^ z);
      return b;
    }
  }.

end DDH.
  


(** Computational Diffie-Hellman problem **)
theory CDH.

  module type Adversary = {
    proc solve(gx gy:group): group
  }.

  module CDH (A:Adversary) = {
    proc main(): bool = {
      var x, y, r;

      x = $FDistr.dt;
      y = $FDistr.dt;
      r = A.solve(g ^ x, g ^ y);
      return (r = g ^ (x * y));
    }
  }.
end CDH.

(** Set version of the Computational Diffie-Hellman problem **)
theory Set_CDH.

  const n: int.

  module type Adversary = {
    proc solve(gx:group, gy:group): group set
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x = $FDistr.dt;
      y = $FDistr.dt;
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

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    local module SCDH' = {
      var x, y: F.t

      proc aux(): group set = {
        var s;

        x = $FDistr.dt;
        y = $FDistr.dt;
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
      (* Move "0 < n" into the context *)
      move=> n_pos.
      (* We prove the inequality by transitivity:
           1%r/n%r * Pr[SCDH(A).main() @ &m: res]
           <= Pr[SCDH'.main() @ &m: res]
           <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res]. *)
      (* "first last" allows us to first focus on the second inequality, which is easier. *)
      apply (real_le_trans _ Pr[SCDH'.main() @ &m: res]); first last.
        (* Pr[SCDH'.main() @ &m: res] <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res] *)
        (* This is in fact an equality, which we prove by program equivalence *)
        byequiv (_: _ ==> ={res})=> //=.
        by proc; inline *; auto; call (_: true); auto.
      (* 1%r/n%r * Pr[SCDH(A).main() @ &m: res] <= Pr[SCDH'.main() @ &m: res] *)
      (* We do this one using a combination of phoare (to deal with the final sampling of z)
         and equiv (to show that SCDH'.aux and CDH.CDH are equivalent in context). *)
      byphoare (_: (glob A) = (glob A){m} ==> _)=> //.
      (* This line is due to a bug in proc *) pose d:= 1%r/n%r * Pr[SCDH(A).main() @ &m: res].
      pose p:= Pr[SCDH(A).main() @ &m: res]. (* notation for ease of writing below *)
      proc.
      (* We split the probability computation into:
           - the probability that s contains g^(x*y) and that |s| <= n is Pr[SCDH(A).main() @ &m: res], and
           - when s contains g^(x*y), the probability of sampling that one element uniformly in s is bounded
             by 1/n. *)
      seq  1: (mem (g ^ (SCDH'.x * SCDH'.y)) s /\ card s <= n) p (1%r/n%r) _ 0%r => //. 
        (* The first part is dealt with by equivalence with SCDH. *)
        conseq (_: _: =p). (* strengthening >= into = for simplicity*)
          call (_: (glob A) = (glob A){m}  ==> mem (g^(SCDH'.x * SCDH'.y)) res /\ card res <= n)=> //.
            bypr; progress; rewrite /p.
            byequiv (_: )=> //.
            by proc *; inline *; wp; call (_: true); auto.
      (* The second part is just arithmetic, but smt needs some help. *)
      rnd ((=) (g^(SCDH'.x * SCDH'.y))).
      skip; progress.
      rewrite Duni.mu_def; first smt.
      cut ->: card (filter ((=) (g^(SCDH'.x * SCDH'.y))) s){hr} = 1 by smt.
      cut H1: 0 < card s{hr} by smt.
      by rewrite -!Real.inv_def inv_le; smt.
    qed.  
  end section.

end Set_CDH.
