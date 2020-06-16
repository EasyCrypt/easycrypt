(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int Real RealExtra StdRing StdOrder Distr List FSet.
(*---*) import RField RealOrder.
require (*  *) CyclicGroup CHoareTactic.

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
  axiom gt0_n :  0 < n.

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

  op build_list (s: group list) = 
    if s = [] || n < size s then [g] else s 
  axiomatized by build_listE.

  schema cost_build_list `{P} {s:group list} : 
     cost [P:build_list s] = cost [P:s] + n.
  hint simplify cost_build_list.
   
  module CDH_from_LCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s <@ A.solve(gx, gy);
      x <$ MUniform.duniform (build_list s);
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
        z <$ MUniform.duniform (build_list s);
        return z = g ^ (x * y);
      }
    }.

    lemma Reduction &m:
      1%r / n%r * Pr[LCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_LCDH(A)).main() @ &m: res].
    proof.
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
      wp; skip=> /> ?; rewrite build_listE => Hin ^ Hle /lezNgt -> /=.
      rewrite /pred1 MUniform.duniform1E. 
      have -> /=: s{hr} <> [] by case: (s{hr}) Hin.
      rewrite Hin /= lef_pinv 2:[smt (gt0_n)].
      + by move: Hin;rewrite -mem_undup -index_mem;smt (index_ge0).
      smt (size_undup).
    qed.
  end section.

  abstract theory C.

    op cduniform_n : { int | 0 <= cduniform_n } as ge0_cduniform_n.

    schema cost_duniform `{P} {s : group list} : 
       cost [P : duniform (build_list s)] = cost [P : s] + cduniform_n.
    hint simplify cost_duniform.
(*
FIXME: 
    lemma ex_reduction cs (A<:Adversary [solve : `{cs}]) &m :
  (*    0 <= cs =>  *)
      (* FIXME : pas de verification que les couts sont positifs *)
      exists (B <:CDH.Adversary [solve : `{cduniform_n + cs} ] {+A}),
      Pr[LCDH(A).main() @ &m: res] <= n%r * Pr[CDH.CDH(B).main() @ &m: res]. *)
    lemma ex_reduction (cs:int) (A<:Adversary [solve : `{cs}]) &m :
      (* FIXME : pas de verification que les couts sont positifs *)
      exists (B <:CDH.Adversary [solve : `{cduniform_n + cs} ] {+A}),
      Pr[LCDH(A).main() @ &m: res] <= n%r * Pr[CDH.CDH(B).main() @ &m: res]. 
    proof.
      exists (CDH_from_LCDH(A));split; last first.
      + have /= h1 := Reduction A &m.  
        rewrite -ler_pdivr_mull; smt(lt_fromint gt0_n).
      proc.
      rnd; call (:true; time []); skip => />; split.
      + move=> ?; apply duniform_ll; rewrite build_listE /#.
      smt().
    qed.

  end C.

end List_CDH.

(** Set version of the Computational Diffie-Hellman problem **)
theory Set_CDH.

  const n: int.
  axiom gt0_n :  0 < n.

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

  clone List_CDH as LCDH with 
    op n <- n
    proof gt0_n by apply gt0_n.

  op choose_n (s:group fset) = 
    take n (elems s) axiomatized by choose_nE.
  
  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    module AL = {
      proc solve(gx:group, gy:group): group list = {
        var s;
        s <@ A.solve(gx, gy);
        return (choose_n s);
      }
    }
    proc solve = LCDH.CDH_from_LCDH(AL).solve
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    (* FIXME: schemas cannot be declared in sections *)
    (* local clone List_CDH as LCDH with op n <- n. *)

    lemma Reduction &m:
      1%r / n%r * Pr[SCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res].
    proof.
      have h0 := LCDH.Reduction (<:CDH_from_SCDH(A).AL) &m.
      have h1 : Pr[SCDH(A).main() @ &m : res] <= 
                Pr[LCDH.LCDH(CDH_from_SCDH(A).AL).main() @ &m : res].
      + byequiv=> //;proc;inline *;wp;call (_:true);auto => /> ?????. 
        by rewrite memE cardE choose_nE => hin hc; rewrite take_oversize.
      have -> : Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m : res] =
                Pr[CDH.CDH(LCDH.CDH_from_LCDH(CDH_from_SCDH(A).AL)).main() @ &m : res].
      + by byequiv=> //;proc;inline *;auto=> /=;call (_:true);auto.
      apply: ler_trans h0 => /=.
      by apply ler_wpmul2r => //; rewrite invr_ge0 le_fromint [smt(gt0_n)].
    qed.
  
  end section.

  abstract theory C.

    clone include LCDH.C.

    schema cost_choose_n `{P} {s:group fset} :
       cost[P: choose_n s] = n.
    hint simplify cost_choose_n.

    lemma ex_reduction_s (cs:int) (A<:Adversary [solve : `{cs}]) &m :
      
      exists (B <:CDH.Adversary [solve : `{cduniform_n + n + cs} ] {+A}),
      Pr[SCDH(A).main() @ &m: res] <= n%r * Pr[CDH.CDH(B).main() @ &m: res].
    proof.
      have := ex_reduction (n + cs) (<:CDH_from_SCDH(A).AL) _ &m.
      + proc; call (:true; time []); skip => /> /#.
      move=> [B hB]; exists B;split.
      + proc true : time [] => // /#.
      have /# : Pr[SCDH(A).main() @ &m : res] <= 
                Pr[LCDH.LCDH(CDH_from_SCDH(A).AL).main() @ &m : res].
      byequiv=> //;proc;inline *;wp;call (_:true);auto => /> ?????. 
      by rewrite memE cardE choose_nE => hin hc; rewrite take_oversize.
    qed.

  end C.

end Set_CDH.
