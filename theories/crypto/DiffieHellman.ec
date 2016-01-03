(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import FSet Int Real.
require (*  *) Duni.
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
    proc solve(gx:group, gy:group): group fset
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x = $FDistr.dt;
      y = $FDistr.dt;
      s = B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ card s <= n);
    }
  }.

  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s = A.solve(gx, gy);
      x = $Duni.dU s;
      return x;
    }
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    local module SCDH' = {
      var x, y: F.t

      proc aux(): group fset = {
        var s;

        x = $FDistr.dt;
        y = $FDistr.dt;
        s = A.solve(g ^ x, g ^ y);
        return s;
      }

      proc main(): bool = {
        var z, s;

        s = aux();
        z = $Duni.dU s;
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
      seq  1: (mem s (g ^ (SCDH'.x * SCDH'.y)) /\ card s <= n) p (1%r/n%r) _ 0%r => //. 
        (* The first part is dealt with by equivalence with SCDH. *)
        conseq (_: _: =p). (* strengthening >= into = for simplicity*)
          call (_: (glob A) = (glob A){m}  ==> mem res (g^(SCDH'.x * SCDH'.y)) /\ card res <= n)=> //.
            bypr; progress; rewrite /p.
            byequiv (_: )=> //.
            by proc *; inline *; wp; call (_: true); auto.
      (* The second part is just arithmetic, but smt needs some help. *)
      rnd (Pred.pred1 (g^(SCDH'.x * SCDH'.y))).
      skip; progress.
        rewrite Duni.mu_dU filter_pred1 H /= fcard1.
        cut H1: 0 < card s{hr} by smt.
        by rewrite -!Real.inv_def inv_le; smt.
        smt.
    qed.  
  end section.

end Set_CDH.
