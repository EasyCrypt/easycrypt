require import AllCore StdRing StdOrder Distr List FSet CHoareTactic Group.
(*---*) import RField RealOrder.

clone CyclicGroup as G.
axiom prime_p : IntDiv.prime G.order.

clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

clone GP.FDistr as FD.

import G GP FD GP.ZModE.

theory DDH.

  module type Adversary = {
    proc guess(gx gy gz : group) : bool
  }.

(* no matching operator, named `*', for the following parameters' type:
  [1]: exp
  [2]: exp
when writing
      b <@ A.guess(g ^ x, g ^ y, g ^ (x * y));
so it is replaced with
      b <@ A.guess(g ^ x, g ^ y, g ^ (P.ZModE.( * ) x y));
*)

  module DDH0 (A : Adversary) = {
    proc main() : bool = {
      var b, x, y;
      (*
      x <$ dZp;
      y <$ dZp;
      *)
      (*
      x <$ FD.dt;
      y <$ FD.dt;
      *)
      x <$ dt;
      y <$ dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ (x * y));
      return b;
    }
  }.

  module DDH1 (A : Adversary) = {
    proc main() : bool = {
      var b, x, y, z;

      x <$ dt;
      y <$ dt;
      z <$ dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ z);
      return b;
    }
  }.

end DDH.

(** Computational Diffie-Hellman problem **)
theory CDH.

  module type Adversary = {
    proc solve(gx gy : group) : group
  }.

  module CDH (A : Adversary) = {
    proc main(): bool = {
      var x, y, r;

      x <$ dt;
      y <$ dt;
      r <@ A.solve(g ^ x, g ^ y);
      return (r = g ^ (x * y));
    }
  }.

end CDH.

theory List_CDH.

  const n: int.
  axiom gt0_n :  0 < n.

  module type Adversary = {
    proc solve(gx : group, gy : group): group list
  }.

  module LCDH (B : Adversary) = {
    proc main() : bool = {
      var x, y, s;

      x <$ dt;
      y <$ dt;
      s <@ B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ size s <= n);
    }
  }.

  module CDH_from_LCDH (A : Adversary): CDH.Adversary = {
    proc solve(gx : group, gy : group) : group = {
      var s, x;

      s <@ A.solve(gx, gy);
      x <$ MUniform.duniform s;
      return x;
    }
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A <: Adversary.

    local module LCDH' = {
      var x, y: exp

      proc aux(): group list = {
        var s;

        x <$ dt;
        y <$ dt;
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
                   mem res (g ^ (LCDH'.x * LCDH'.y)) /\ size res <= n)=> //.
        bypr; progress; rewrite /p.
        byequiv (_: )=> //.
        by proc *; inline *; wp; call (_: true); auto.
      (* The second part is just arithmetic, but smt needs some help. *)
      rnd (pred1 (g ^ (LCDH'.x * LCDH'.y))).
      wp; skip=> /> ? Hin Hle /=.
      rewrite /pred1 MUniform.duniform1E Hin /= lef_pinv; [2:smt (gt0_n)].
      + by move: Hin;rewrite -mem_undup -index_mem;smt (index_ge0).
      smt (size_undup).
    qed.
  end section.

  abstract theory Cost.

    op cduniform_n : { int | 0 <= cduniform_n } as ge0_cduniform_n.

    schema cost_duniform `{P} {s : group list} :
       cost [P /\ size s <= n : duniform s] <= cost [P : s] + N cduniform_n.

    lemma ex_reduction (cs:int) (A<:Adversary) &m :
      choare[A.solve : true ==> 0 < size res <= n] time [N cs] =>
      exists (B <:CDH.Adversary [solve : `{N(cduniform_n + cs)} ] {+A}),
      Pr[LCDH(A).main() @ &m: res] <= n%r * Pr[CDH.CDH(B).main() @ &m: res].
    proof.
      move=> hcA;exists (CDH_from_LCDH(A));split; last first.
      + have /= h1 := Reduction A &m.
        rewrite -ler_pdivr_mull; smt(lt_fromint gt0_n).
      proc => //.
      instantiate /= h := (cost_duniform {gx, gy, x : group, s : group list}
                        `(true) s).
      rnd (size s <= n).
      + by apply: (is_int_le _ _ h).
      call hcA; skip => />; split.
      + move=> *; apply duniform_ll;rewrite -size_eq0 /#.
      move: h; pose t :=
        cost(&hr: {gx, gy, x : group, s : group list})[size s <= n : duniform s].
      by case: t => // ? /#.
    qed.

  end Cost.

end List_CDH.

(** Set version of the Computational Diffie-Hellman problem **)
theory Set_CDH.

  const n: int.
  axiom gt0_n :  0 < n.

  module type Adversary = {
    proc solve(gx : group, gy : group): group fset
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x <$ dt;
      y <$ FD.dt;
      s <@ B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ card s <= n);
    }
  }.

  clone List_CDH as LCDH with
    op n <- n
    proof gt0_n by apply gt0_n.

  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    module AL = {
      proc solve(gx : group, gy:group): group list = {
        var s;
        s <@ A.solve(gx, gy);
        return elems s;
      }
    }
    proc solve = LCDH.CDH_from_LCDH(AL).solve
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A <: Adversary.

    (* FIXME: schemas cannot be declared in sections *)
    (* local clone List_CDH as LCDH with op n <- n. *)

    lemma Reduction &m:
      1%r / n%r * Pr[SCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res].
    proof.
      have h0 := LCDH.Reduction (<:CDH_from_SCDH(A).AL) &m.
      have h1 : Pr[SCDH(A).main() @ &m : res] <=
                Pr[LCDH.LCDH(CDH_from_SCDH(A).AL).main() @ &m : res].
      + byequiv=> //;proc;inline *;wp;call (_:true);auto => /> 5?.
        by rewrite memE cardE.
      have -> : Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m : res] =
                Pr[CDH.CDH(LCDH.CDH_from_LCDH(CDH_from_SCDH(A).AL)).main() @ &m : res].
      + by byequiv=> //;proc;inline *;auto=> /=;call (_:true);auto.
      apply: ler_trans h0 => /=.
      by apply ler_wpmul2r => //; rewrite invr_ge0 le_fromint; smt(gt0_n).
    qed.

  end section.

end Set_CDH.
