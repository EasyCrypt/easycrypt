(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore StdRing StdOrder Distr List FSet.
(*---*) import RField RealOrder.
require (*  *) CyclicGroup.

clone export CyclicGroup as G.

theory DDH.

  module type Adversary = {
    proc guess(gx gy gz:G.group): bool
  }.

  module DDH0 (A:Adversary) = {
    proc main() : bool = {
      var b, x, y;
      x <$ FDistr.dt;
      y <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ (x*y));
      return b;
    }
  }.

  module DDH1 (A:Adversary) = {
    proc main() : bool = {
      var b, x, y, z;

      x <$ FDistr.dt;
      y <$ FDistr.dt;
      z <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ z);
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

      x <$ FDistr.dt;
      y <$ FDistr.dt;
      r <@ A.solve(g ^ x, g ^ y);
      return (r = g ^ (x * y));
    }
  }.
end CDH.

theory List_CDH.

  const n: int.

  module type Adversary = {
    proc solve(gx:group, gy:group): group list
  }.

  module LCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x <$ FDistr.dt;
      y <$ FDistr.dt;
      s <@ B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ size s <= n);
    }
  }.

  module CDH_from_LCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s <@ A.solve(gx, gy);
      x <$ MUniform.duniform s;
      return x;
    }
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    local module LCDH' = {
      var x, y: F.t

      proc aux(): group list = {
        var s;

        x <$ FDistr.dt;
        y <$ FDistr.dt;
        s <@ A.solve(g ^ x, g ^ y);
        return s;
      }

      proc main(): bool = {
        var z, s;

        s <@ aux();
        z <$ MUniform.duniform s;
        return z = g ^ (x * y);
      }
    }.

    lemma Reduction &m:
      0 < n =>
      1%r / n%r * Pr[LCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_LCDH(A)).main() @ &m: res].
    proof.
      (* Move "0 < n" into the context *)
      move=> n_pos.
      (* We prove the inequality by transitivity:
           1%r/n%r * Pr[LCDH(A).main() @ &m: res]
           <= Pr[LCDH'.main() @ &m: res]
           <= Pr[CDH.CDH(CDH_from_LCDH(A)).main() @ &m: res]. *)
      (* "first last" allows us to first focus on the second inequality, which is easier. *)
      apply (ler_trans Pr[LCDH'.main() @ &m: res]); first last.
        (* Pr[LCDH'.main() @ &m: res] <= Pr[CDH.CDH(CDH_from_LCDH(A)).main() @ &m: res] *)
        (* This is in fact an equality, which we prove by program equivalence *)
        byequiv (_: _ ==> ={res})=> //=.
        by proc; inline *; auto; call (_: true); auto.
      (* 1%r/n%r * Pr[LCDH(A).main() @ &m: res] <= Pr[LCDH'.main() @ &m: res] *)
      (* We do this one using a combination of phoare (to deal with the final sampling of z)
         and equiv (to show that LCDH'.aux and CDH.CDH are equivalent in context). *)
      byphoare (_: (glob A) = (glob A){m} ==> _)=> //.
      (* This line is due to a bug in proc *) pose d:= 1%r/n%r * Pr[LCDH(A).main() @ &m: res].
      pose p:= Pr[LCDH(A).main() @ &m: res]. (* notation for ease of writing below *)
      proc.
      (* We split the probability computation into:
           - the probability that s contains g^(x*y) and that |s| <= n is Pr[LCDH(A).main() @ &m: res], and
           - when s contains g^(x*y), the probability of sampling that one element uniformly in s is bounded
             by 1/n. *)
      seq  1: (mem s (g ^ (LCDH'.x * LCDH'.y)) /\ size s <= n) p (1%r/n%r) _ 0%r => //.
        (* The first part is dealt with by equivalence with LCDH. *)
        conseq (_: _: =p). (* strengthening >= into = for simplicity*)
        call (_: (glob A) = (glob A){m}  ==> 
                   mem res (g^(LCDH'.x * LCDH'.y)) /\ size res <= n)=> //.
        bypr; progress; rewrite /p.
        byequiv (_: )=> //.
        by proc *; inline *; wp; call (_: true); auto.
      (* The second part is just arithmetic, but smt needs some help. *)
      rnd (pred1 (g^(LCDH'.x * LCDH'.y))).
      skip=> /> ? Hin Hle.
      rewrite /pred1 MUniform.duniform1E Hin /= lef_pinv 2:/#.
      + by move: Hin;rewrite -mem_undup -index_mem;smt (index_ge0).
      smt (size_undup).
    qed.
  end section.

end List_CDH.

(** Set version of the Computational Diffie-Hellman problem **)
theory Set_CDH.

  const n: int.

  module type Adversary = {
    proc solve(gx:group, gy:group): group fset
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x <$ FDistr.dt;
      y <$ FDistr.dt;
      s <@ B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ card s <= n);
    }
  }.

  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s <@ A.solve(gx, gy);
      x <$ MUniform.duniform (elems s);
      return x;
    }
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    local module AL = {
      proc solve(gx:group, gy:group) = {
        var s;
        s <@ A.solve(gx, gy);
        return elems s;
      }
    }.

    local clone List_CDH as LCDH with op n <- n.

    lemma Reduction &m:
      0 < n =>
      1%r / n%r * Pr[SCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res].
    proof.
      move=> Hn.
      have := LCDH.Reduction AL &m Hn.
      have -> : Pr[LCDH.LCDH(AL).main() @ &m : res] = Pr[SCDH(A).main() @ &m : res].
      + by byequiv=> //;proc;inline *;wp;call (_:true);auto => /> ?????;rewrite memE cardE.
      have -> //: Pr[CDH.CDH(LCDH.CDH_from_LCDH(AL)).main() @ &m : res] =
                Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m : res].
      by byequiv=> //;proc;inline *;auto=> /=;call (_:true);auto.
    qed.
  
  end section.

end Set_CDH.
