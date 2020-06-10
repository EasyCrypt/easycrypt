(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Finite List FSet SmtMap Distr.
require import StdRing StdBigop StdOrder FelTactic.
(*---*) import RealOrder.

(* -------------------------------------------------------------------- *)
theory Types.
  type from.
  type to.

  (* Distribution to use on the target type; it can be parameterized by the input *)
  op dsample: from -> to distr.

  (* A signature for random oracles from "from" to "to". *)
  module type Oracle =
  {
    proc init():unit
    proc o (x:from):to
  }.

  module type ARO = {
    proc o(x:from):to
  }.

  module type Dist (H:ARO) = {
    proc distinguish(): bool
  }.

  module IND(H:Oracle,D:Dist) = {
    module D = D(H)

    proc main(): bool = {
      var b:bool;

      H.init();
      b <@ D.distinguish();
      return b;
    }
  }.
end Types.

(* -------------------------------------------------------------------- *)
theory Lazy.
  type from.
  type to.

  op dsample: from -> to distr.

  clone export Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO:Oracle = {
    var m:(from, to) fmap

    proc init():unit = {
      m <- empty;
    }

    proc o(x:from):to = {
      var y:to;
      y <$ dsample x;
      if (x \notin m) m.[x] <- y;
      return oget (m.[x]);
    }
  }.

  lemma RO_init_ll: islossless RO.init.
  proof. by proc; wp. qed.

  lemma RO_o_ll:
    (forall x, mu (dsample x) predT = 1%r) =>
    islossless RO.o.
  proof. by move=> dsampleL; proc; auto=> /#. qed.

  equiv RO_init_eq: RO.init ~ RO.init: true ==> ={glob RO}.
  proof. by sim. qed.

  equiv RO_o_eq: RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}.
  proof. by sim. qed.

  hoare dom_RO_o d x':
    RO.o: x = x' /\ dom RO.m = d ==>
          dom RO.m = predU d (pred1 x').
  proof.
  proc; auto=> /> &m y _; split.
  + by move=> x_notin_m; apply/fun_ext=> x0; rewrite mem_set.
  move=> x_in_m; apply/fun_ext=> x0 @/predU @/pred1.
  by case: (x0 = x{m})=> // ->>; rewrite x_in_m.
  qed.

end Lazy.

(* -------------------------------------------------------------------- *)
theory Eager.
  type from.
  type to.

  op dsample: from -> to distr.

  clone export Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO: Oracle = {
    var m:(from,to) fmap

    proc init(): unit = {
      var y:to;
      var work:from fset;
      var f:from;

      m    <- empty;
      work <- FSet.oflist (to_seq predT);
      while (work <> fset0)
      {
        f     <- pick work;
        y     <$ dsample f;
        m.[f] <- y;
        work  <- work `\` fset1 f;
      }
    }

    proc o(x:from): to = {
      return oget m.[x];
    }
  }.

  lemma RO_init_full:
    is_finite predT<:from> =>
    hoare [RO.init: true ==> forall x, x \in RO.m].
  proof.
  move=> fType; proc.
  while (forall x, FSet.mem work x \/ x \in RO.m).
  + auto=> /> &m w_m_part w_non_empty y _ x.
    case: (x = pick work{m}).
    + by rewrite mem_set.
    + by rewrite mem_set in_fsetD in_fset1=> -> /=; exact/w_m_part.
  auto=> />; split=> [x|m h x].
  + by rewrite mem_oflist mem_to_seq.
  by have:= h x; rewrite in_fset0.
  qed.

  lemma RO_init_ll:
    is_finite predT<:from> =>
    (forall x, mu (dsample x) predT = 1%r) =>
    islossless RO.init.
  proof.
  move=> fType dsampleL; proc.
  while (true) (card work); auto => />.
  + move=> &hr Hw;rewrite dsampleL /= => ??. 
    rewrite (fcardD1 work{hr} (pick work{hr})) mem_pick //= /#.   
  smt(fcard_ge0 fcard_eq0).
  qed.

  lemma RO_o_ll: islossless RO.o.
  proof. by proc; wp. qed.

  lemma RO_init_eq:
    is_finite predT<:from> =>
    equiv [RO.init ~ RO.init: true ==> ={glob RO}].
  proof. by move=> fType; proc; while (={glob RO, work}); auto. qed.

  equiv RO_o_eq: RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}.
  proof. by sim. qed.

  lemma dom_RO_init x:
    is_finite predT<:from> =>
    hoare [RO.init: true ==> x \in RO.m].
  proof.
  move=> fType; proc; while (forall x, !FSet.mem work x => x \in RO.m).
  + auto=> /> &m w_m_part w_non_empty y _ x'.
    case: (x' = pick work{m}).
    + by rewrite mem_set.
    + by rewrite mem_set in_fsetD in_fset1=> -> /=; exact/w_m_part.
  auto=> />; split=> [x'|m h].
  + by rewrite mem_oflist mem_to_seq // /predT.
  by have:= h x; rewrite in_fset0.
  qed.
end Eager.

(* -------------------------------------------------------------------- *)
theory LazyEager.
  type from.
  type to.

  op dsample: from -> to distr.

  clone Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  clone export Lazy with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  clone export Eager with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  section.
    declare module D:Dist {Lazy.RO,Eager.RO}.

    local module IND_Lazy = {
      module H:Oracle = {
        var m : (from, to) fmap

        proc init():unit = {
          m <- empty;
        }

        proc o(x:from):to = {
          var y:to;
          y <$ dsample x;
          if (x \notin m) m.[x] <- y;
          return oget (m.[x]);
        }
      }

      proc resample(): unit = {
        var work : from fset;
        var f : from;
        var y, y0 : to;

        work <- FSet.oflist (to_seq predT);
        while (work <> fset0)
        {
          f <- pick work;
          y <$ dsample f;
          if (f \notin H.m) H.m.[f] <- y;
          work <- work `\` fset1 f;
        }
      }

      module D = D(H)

      proc main(): bool = {
        var b:bool;

        H.init();
        b <@ D.distinguish();
        resample();

        return b;
      }
    }.

    local lemma IND_Lazy:
         is_finite predT<:from>
      => (forall x, mu (dsample x) predT = 1%r)
      => equiv [IND(Lazy.RO,D).main ~ IND_Lazy.main: ={glob D} ==> ={res}].
    proof.
    move=> fromF dsampleL; proc; seq 2 2: (={b}).
    + call (_: Lazy.RO.m{1} = IND_Lazy.H.m{2}); first by sim.
      by call (_: ={glob D} ==> Lazy.RO.m{1} = IND_Lazy.H.m{2})=> //; proc; wp.
    inline IND_Lazy.resample; while{2} (true) (card work{2}).
    + auto=> /> &hr Hw;rewrite dsampleL /= => ??.
      by rewrite (fcardD1 work{hr} (pick work{hr})) mem_pick //= /#.
    by auto=> />; smt(fcard_ge0 fcard_eq0).
    qed.

    local module IND_Eager = {
      module H = {
        var m:(from,to) fmap

        proc o(x:from): to = {
          return oget (m.[x]);
        }
      }

      proc resample(): unit = {
        var work:from fset;
        var f:from;
        var y,y0:to;

        work <- FSet.oflist (to_seq predT);
        while (work <> fset0)
        {
          f <- pick work;
          y <$ dsample f;
          if (f \notin H.m) H.m.[f] <- y;
          work <- work `\` fset1 f;
        }
      }

      module D = D(H)

      proc main(): bool = {
        var b:bool;

        H.m <- empty;
        resample();
        b <@ D.distinguish();

        return b;
      }
    }.

    local lemma eager_query:
      is_finite predT<:from> =>
      (forall x, mu (dsample x) predT = 1%r) =>
      eager [IND_Eager.resample(); ,
                 IND_Eager.H.o ~ IND_Lazy.H.o,
             IND_Lazy.resample();:
        ={x} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2} ==>
        ={res} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}].
    proof.
    move=> fromF dsampleL; eager proc.
    inline IND_Eager.resample IND_Lazy.resample; swap{2} 4 -3.
    seq 1 1: (={x,work} /\
              IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
              mem work{1} x{1}).
    + by auto=> /> &2; rewrite mem_oflist mem_to_seq.
    case (x{2} \notin IND_Lazy.H.m{2});
      [rcondt{2} 2; first by auto | rcondf{2} 2; first by auto].
    + transitivity{1} {
        y0 <$ dsample x;
        while (work <> fset0) {
          f <- pick work;
          y <$ dsample f;
          if (f \notin IND_Eager.H.m)
            IND_Eager.H.m.[f] <- if f = x then y0 else y;
          work <- work `\` fset1 f;
        }
        result <- oget IND_Eager.H.m.[x];
      }
      (={x, work, IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
      ((={x,work} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\  mem work{1} x{1})
        /\ x{2} \notin IND_Lazy.H.m{2} ==>
          ={result} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}) => //.
      + by move=> &1 &2 H; exists IND_Lazy.H.m{2} work{2} x{2}; move: H.
      + transitivity{1} {
          while (work <> fset0) {
            f <- pick work;
            y <$ dsample f;
            if (f \notin IND_Eager.H.m)
              IND_Eager.H.m.[f] <- y;
              work <- work `\` fset1 f;
            }
            y0 <$ dsample x;
            result <- oget IND_Eager.H.m.[x];
          }
          (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
          (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})=> //.
        + by move=> &1 &2 H; exists IND_Eager.H.m{2} work{2} x{2}; move: H.
        + by sim; rnd{2}; sim: (={x,IND_Eager.H.m})=> /> ?;apply dsampleL.
        wp; symmetry; eager
          while (H:y0 <$ dsample x; ~ y0 <$ dsample x; : ={x} ==> ={y0})=> //;
          first by rnd.
        + swap{2} 5 -4; swap [2..3] -1; case ((x = pick work){1}).
          + by wp; rnd{2}; rnd; rnd{1}; wp; skip=> /#.
          by auto=> /> &1 _; rewrite eq_sym=> ->.
        by sim.
      wp; while (={x, work} /\
                 (!mem work x => x \in IND_Eager.H.m){1} /\
                 IND_Lazy.H.m.[x]{2} = Some y0{1} /\
                 if (x \in IND_Eager.H.m){1}
                 then IND_Eager.H.m{1} = IND_Lazy.H.m{2}
                 else eq_except (pred1 x{1}) IND_Eager.H.m{1} IND_Lazy.H.m{2}).
      + auto=> /> &1 &2 Hpart m_x upd_cond work_neq_nil y _.
        case: (mem work{2} x{2})=> [|^x_in_work /Hpart x_in_Em]; last first.
        + move: upd_cond=> /= <*>; rewrite x_in_Em => /= <*>.
          case: (pick work{2} = x{2})=> //= ^pkwork_neq_x.
          rewrite in_fsetD1 eq_sym mem_set !get_setE=> -> /=.
          rewrite eq_exceptP /pred1 /=.
          by split=> ^ + -> //=.
        case: (pick work{2} = x{2})=> [<<*> _ {Hpart}|].
        + rewrite in_fsetD1 mem_set !get_setE //= domE.
          have -> /= := m_x.
          move: upd_cond; rewrite domE.
          case: (IND_Eager.H.m{1}.[pick work{2}] <> None)=> //= m'_x /eq_exceptP @/pred1 eqe_m_m'.
          rewrite -fmap_eqP => x; rewrite get_setE; case: (x = pick work{2})=> [->|^ + /eqe_m_m' ->] //.
          by rewrite m_x.
        rewrite mem_set !get_setE !inE=> //= ^ pw_neq_x; rewrite eq_sym=> -> -> //=.
        rewrite m_x !eq_exceptP /=.
        move: upd_cond; case: (x{2} \in IND_Eager.H.m{1})=> [_ ->|/=] //.
        rewrite eq_exceptP=> _ h; split.
        + move=> pw_notin_Lm; split.
          + by move=> pw_notin_Em x0 /h; rewrite !get_setE=> ->.
          by move: pw_neq_x pw_notin_Lm=> /h; rewrite !domE=> ->.
        by move: pw_neq_x=> /h; rewrite !domE=> ->.
      auto=> /> &2 x_in_w x_notin_m y _.
      rewrite get_set_eqE //= eq_except_sym; first exact/eq_except_setl.
      move=> /= mL mR.
      by rewrite in_fset0=> /= -> /= + -> - ->.
    wp; while (={x,work} /\
               IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
               x{2} \in IND_Lazy.H.m{2} /\
               oget IND_Eager.H.m.[x]{1} = result{2}).
    + auto => /> &m2 Hin ????. 
      by rewrite domE get_set_neqE /#.
    by auto=> /#.
    qed.

    local lemma eager_aux:
      is_finite predT<:from> =>
      (forall x, mu (dsample x) predT = 1%r) =>
      equiv [IND_Lazy.main ~ IND_Eager.main: ={glob D} ==> ={res}].
    proof.
    move=> fromF dsampleL; proc; inline IND_Lazy.H.init.
    seq 1 1: (={glob D} /\ IND_Lazy.H.m{1} = IND_Eager.H.m{2}); first by wp.
    symmetry.
    eager (H: IND_Eager.resample(); ~ IND_Lazy.resample();:
                IND_Eager.H.m{1} = IND_Lazy.H.m{2} ==> IND_Eager.H.m{1} = IND_Lazy.H.m{2}):
          (={glob D} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}) => //;
      first by sim.
    eager proc H (IND_Eager.H.m{1} = IND_Lazy.H.m{2})=> //;
      first by apply eager_query.
    by sim.
    qed.

    local lemma IND_Eager:
      is_finite predT<:from> =>
      (forall x, mu (dsample x) predT = 1%r) =>
      equiv [IND_Eager.main ~ IND(Eager.RO,D).main: ={glob D} ==> ={res}].
    proof.
    move=> fromF dsampleL; proc.
    call (_: (forall x, x \in IND_Eager.H.m{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
    + by proc; skip; smt(@SmtMap).
    inline RO.init IND_Eager.resample.
    while (={work} /\
           (forall x, x \notin IND_Eager.H.m{1} <=>
                      mem work{1} x) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
    + auto=> /> &2 in_mVw.
      move=> notempty_w y _; split.
      + by move=> pw_notin_m x; rewrite mem_set in_fsetD in_fset1 negb_or in_mVw.
      by move: notempty_w=> /mem_pick /in_mVw.
    auto => />; split=> [x| m].
    + by rewrite mem_empty mem_oflist mem_to_seq.
    by move=> h x; have:= h x; rewrite in_fset0.
    qed.

    lemma eagerRO:
      is_finite predT<:from> =>
      (forall x, mu (dsample x) predT = 1%r) =>
      equiv [IND(Lazy.RO,D).main ~ IND(Eager.RO,D).main: ={glob D} ==> ={res}].
    proof.
    move=> fromF dsampleL; bypr (res{1}) (res{2})=> // &1 &2 a eq_D.
    apply (@eq_trans _ Pr[IND_Lazy.main() @ &1: a = res]);
      first by byequiv (IND_Lazy _ _).
    apply (@eq_trans _ Pr[IND_Eager.main() @ &1: a = res]);
      first by byequiv (eager_aux _ _).
    by byequiv (IND_Eager _ _).
    qed.
  end section.
end LazyEager.

(* -------------------------------------------------------------------- *)
theory BoundedCall.
  type from.
  type to.

  op dsample: from -> to distr.

  op qH:int.

  clone export Lazy with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module Bound (O:Oracle) = {
    var c:int

    proc init(): unit = {
      O.init();
      c <- 0;
    }

    proc o(x:from): to = {
      var r <- witness;

      if (c < qH) {
        r <- O.o(x);
        c <- c + 1;
      }
      return r;
    }
  }.

  lemma Bound_init_ll (O <: Oracle): islossless O.init => islossless Bound(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Bound_o_ll (O <: Oracle): islossless O.o => islossless Bound(O).o.
  proof. by move=> O_o_ll; proc; sp; if=> //; wp; call O_o_ll. qed.
end BoundedCall.

(* -------------------------------------------------------------------- *)
theory ListLog.
  type from.
  type to.

  op dsample: from -> to distr.

  op qH:int.

  clone export Lazy with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module Log (O:Oracle) = {
    var qs:from list

    proc init(): unit = {
      O.init();
      qs <- [];
    }

    proc o(x:from): to = {
      var r:to;

      qs <- x::qs;
      r  <@ O.o(x);
      return r;
    }
  }.

  lemma Log_init_ll (O <: Oracle): islossless O.init => islossless Log(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Log_o_ll (O <: Oracle): islossless O.o => islossless Log(O).o.
  proof. by move=> O_oL; proc; call O_oL; wp. qed.

  lemma Log_o_stable (O <: Oracle {Log}) q:
    islossless O.o => phoare[Log(O).o: mem Log.qs q ==> mem Log.qs q] = 1%r.
  proof. by move=> O_o_ll; proc; call O_o_ll; auto; progress; right. qed.

  module Bound(O:Oracle) = {
    module LO = Log(O)

    proc init(): unit = {
      Log(O).init();
    }

    proc o(x:from): to = {
      var r <- witness;

      if (size Log.qs < qH) {
        r <@ O.o(x);
      }
      return r;
    }
  }.
end ListLog.

(* -------------------------------------------------------------------- *)
theory SetLog.
  type from.
  type to.

  op dsample: from -> to distr.

  op qH:int.

  clone export Lazy with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module Log(O:Oracle) = {
    var qs:from fset

    proc init(): unit = {
      O.init();
      qs <- fset0;
    }

    proc o(x:from): to = {
      var r;

      r  <@ O.o(x);
      qs <- qs `|` fset1 x;
      return r;
    }
  }.

  lemma Log_init_ll (O <: Oracle): islossless O.init => islossless Log(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Log_o_ll (O <: Oracle): islossless O.o => islossless Log(O).o.
  proof. by move=> O_o_ll; proc; wp; call O_o_ll; wp. qed.

  hoare Log_o_stable (O <: Oracle {Log}) x: Log(O).o: mem Log.qs x ==> mem Log.qs x.
  proof. by proc; wp; call (_: true); skip=> &m; rewrite in_fsetU in_fset1=> ->. qed.

  hoare Log_o_Dom: Log(RO).o:
    (forall x, x \in Log.qs = x \in RO.m) ==>
    (forall x, x \in Log.qs = x \in RO.m).
  proof.
  proc; inline*; auto=> &m eq_qs_m y _ /=; split=> /=.
  + by move=> x_notin_m x0; rewrite in_fsetU in_fset1 mem_set eq_qs_m.
  move=> x_in_m x0; rewrite in_fsetU in_fset1 eq_qs_m.
  by case: (x0 = x{m})=> //= ->; rewrite x_in_m.
  qed.

  module Bound(O:Oracle) = {
    module LO = Log(O)

    proc init = Log(O).init

    proc o(x:from): to = {
      var r <- witness;

      if (card Log.qs < qH) {
        r <@ LO.o(x);
      }
      return r;
    }
  }.

  lemma Bound_init_ll (O <: Oracle): islossless O.init => islossless Bound(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Bound_o_ll (O <: Oracle {Log}): islossless O.o => islossless Bound(O).o.
  proof. by move=> O_o_ll; proc; sp; if=> //; wp; call (Log_o_ll O _). qed.

  hoare Bound_o_stable (O <: Oracle {Log}) x: Bound(O).o: mem Log.qs x ==> mem Log.qs x.
  proof. by proc; sp; if=> //; wp; call (Log_o_stable O x). qed.

  equiv Log_Bound (O <: Oracle {Log}) (D <: Dist {O,Log}):
    IND(Bound(O),D).main ~ IND(Log(Bound(O)),D).main: ={glob O, glob D} ==> ={res}.
  proof.
  proc.
  call (_: ={glob O} /\ card Log.qs{1} <= card Log.qs{2} /\ (card Log.qs{1} < qH => ={glob Log})).
    proc *; inline Log(Bound(O)).o Bound(O).o Bound(O).LO.o.
    sp; if=> />; first by smt().
    + wp; call (: true); auto=> /> &1 &2.
      move=> le_c1_c2 h ^ + /h <<-.
      have /#: Log.qs{1} `|` fset1 x{2} `|` fset1 x{2} = Log.qs{1} `|` fset1 x{2}.
      by rewrite fsetP=> x; rewrite !(in_fsetU, in_fset1)=> /#.
    auto=> /> &1 &2; rewrite fcardU fcard1; case: (x{2} \in Log.qs{2})=> [x_in_qs|x_notin_qs].
    + have ->: Log.qs{2} `&` fset1 x{2} = fset1 x{2}.
      + by rewrite fsetP=> x'; rewrite in_fsetI in_fset1 /#.
      by rewrite fcard1 addzK.
    have ->: Log.qs{2} `&` fset1 x{2} = fset0.
    + rewrite fsetP=> x'; rewrite in_fsetI in_fset1.
      case: (x' = x{2})=> [->>|].
      + by rewrite x_notin_qs in_fset0.
      by rewrite in_fset0.
    by rewrite fcards0 /#.
  by inline *; wp; call (: true).
  qed.
end SetLog.

(* -------------------------------------------------------------------- *)
theory ROM_BadCall.
  (** A generic argument allowing us to replace a single random
      oracle query with freshly sampled randomness. We then bound
      the probability of distinguishing the two modules by the
      probability of a third module that simply returns whether
      the replaced query has been guessed by the adversary.       *)
  (** We want to be able to:
        1) express the result on Log(O);
        2) and use it on Bound(O)...
      HOW? *)

  type from.
  type to.

  op dsample: from -> to distr.
  axiom dsampleL x: mu (dsample x) predT = 1%r.

  op qH:int.

  clone export SetLog with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample,
    op qH      <- qH.

  module type Dist(H:ARO) = {
    proc a1(): from
    proc a2(x:to): bool
  }.

  theory OnLog.
    module G0(D:Dist, H:Oracle) = {
      module D = D(Log(H))

      proc main(): bool = {
        var x, y, b;

        Log(H).init();
        x <@ D.a1();
        y <@ H.o(x);
        b <@ D.a2(y);
        return b;
      }
    }.

    module G1(D:Dist, H:Oracle) = {
      module D = D(Log(H))

      proc main(): bool = {
        var x, y, b;

        Log(H).init();
        x <@ D.a1();
        y <$ dsample x;
        b <@ D.a2(y);
        return b;
      }
    }.

    module G2(D:Dist, H:Oracle) = {
      module D = D(Log(H))

      proc main(): bool = {
        var x, y, b;

        Log(H).init();
        x <@ D.a1();
        y <$ dsample x;
        b <@ D.a2(y);
        return mem Log.qs x;
      }
    }.

    section.
      declare module D : Dist {Log, RO}.
      axiom Da1L (H <: Types.ARO {D}): islossless H.o => islossless D(H).a1.
      axiom Da2L (H <: Types.ARO {D}): islossless H.o => islossless D(H).a2.

      local module G1'(D:Dist, H:Oracle) = {
        module D = D(Log(H))

        var x:from

        proc main(): bool = {
          var y, b;

          Log(H).init();
          x <@ D.a1();
          y <$ dsample x;
          b <@ D.a2(y);
          return b;
        }
      }.

      lemma ROM_BadCall &m:
        Pr[G0(D,RO).main() @ &m: res] <= Pr[G1(D,RO).main() @ &m: res] + Pr[G2(D,RO).main() @ &m: res].
      proof.
      cut ->: Pr[G2(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: mem Log.qs G1'.x].
      + byequiv (_: ={glob D} ==> res{1} = (mem Log.qs G1'.x){2})=> //.
        proc.
        call (_: ={glob Log, glob RO}); first by sim.
        rnd; call (_: ={glob Log, glob RO}); first by sim.
        by inline *; wp.
      cut ->: Pr[G1(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: res].
      + by byequiv (_: ={glob D} ==> ={res}); first by sim.
      cut: Pr[G0(D,RO).main() @ &m: res] <= Pr[G1'(D,RO).main() @ &m: res \/ mem Log.qs G1'.x].
      byequiv (_: ={glob D} ==> !mem Log.qs{2} G1'.x{2} => ={res})=> //; last smt().
      proc.
      call (_: mem Log.qs G1'.x,
               ={glob Log} /\
               (forall x, x \in Log.qs{2} = x \in RO.m{2}) /\
               eq_except (pred1 G1'.x{2}) RO.m{1} RO.m{2}).
      + by apply Da2L.
      + proc; inline RO.o; auto=> /> //= &1 &2 x2_notin_qs eq_qs_m eqe y _.
        rewrite !inE !get_setE x2_notin_qs /= eq_except_set_eq //= eq_sym.
        split.
        + move=> x_notin_m2; split.
          + by move=> x_notin_m1 + x1; rewrite in_fsetU in_fset1 mem_set eq_qs_m.
          move: eqe; rewrite eq_exceptP /pred1=> /(_ x{2}) h + /h eq_mx.
          by rewrite domE eq_mx -domE.
        move=> x_in_m2; split.
        + move: eqe; rewrite eq_exceptP /pred1=> /(_ x{2}) h + /h eq_mx.
          by rewrite domE eq_mx -domE.
        move=> x_in_m1 x2_neq_G1'x. move: eqe; rewrite eq_exceptP=> -> //= x1.
        by rewrite in_fsetU in_fset1 eq_qs_m; case: (x1 = x{2})=> [->|] //=; rewrite x_in_m2.
      + by progress; apply (Log_o_ll RO); apply (RO_o_ll _); smt(dsampleL).
      + progress; exists* G1'.x; elim* => x; conseq (Log_o_ll RO _) (Log_o_stable RO x)=> //.
        by apply (RO_o_ll _); smt(dsampleL).
      + inline RO.o; auto.
        call (_: ={glob Log, glob RO} /\ (forall x, x \in Log.qs{2} = x \in RO.m{2})).
        + proc; inline RO.o; auto=> /> &2 eq_qs_m y _; split.
          + by move=> x_notin_m x1; rewrite in_fsetU in_fset1 mem_set eq_qs_m.
          move=> x_in_m x1; rewrite in_fsetU in_fset1 eq_qs_m; case: (x1 = x{2})=> //=.
          by move=> ->; rewrite x_in_m.          
        inline Log(RO).init RO.init; auto=> />; split=> [x1|_ r qs m eq_qs_m y _].
        + by rewrite in_fset0 mem_empty.
        by rewrite get_set_eqE //= eq_except_setl /= eq_qs_m /#.
      by rewrite Pr [mu_or]; smt(mu_bounded).
      qed.
    end section.
  end OnLog.

  theory OnBound.
    module G0(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x <@ D.a1();
        y <@ H.o(x);
        b <@ D.a2(y);
        return b;
      }
    }.

    module G1(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x <@ D.a1();
        y <$ dsample x;
        b <@ D.a2(y);
        return b;
      }
    }.

    module G2(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x <@ D.a1();
        y <$ dsample x;
        b <@ D.a2(y);
        return mem Log.qs x;
      }
    }.

    section.
      declare module D : Dist {Log, RO}.
      axiom Da1L (H <: Types.ARO {D}): islossless H.o => islossless D(H).a1.
      axiom Da2L (H <: Types.ARO {D}): islossless H.o => islossless D(H).a2.

      local module G1'(D:Dist, H:Oracle) = {
        module D = D(Bound(H))

        var x:from

        proc main(): bool = {
          var y, b;

          Log(H).init();
          x <@ D.a1();
          y <$ dsample x;
          b <@ D.a2(y);
          return b;
        }
      }.

      lemma ROM_BadCall &m:
        Pr[G0(D,RO).main() @ &m: res] <= Pr[G1(D,RO).main() @ &m: res] + Pr[G2(D,RO).main() @ &m: res].
      proof.
      cut ->: Pr[G2(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: mem Log.qs G1'.x].
      + byequiv (_: ={glob D} ==> res{1} = (mem Log.qs G1'.x){2})=> //.
        proc.
        call (_: ={glob Log, glob RO}); first by sim.
        rnd; call (_: ={glob Log, glob RO}); first by sim.
        by inline *; wp.
      cut ->: Pr[G1(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: res].
        by byequiv (_: ={glob D} ==> ={res}); first by sim.
      cut: Pr[G0(D,RO).main() @ &m: res] <= Pr[G1'(D,RO).main() @ &m: res \/ mem Log.qs G1'.x].
        byequiv (_: ={glob D} ==> !mem Log.qs{2} G1'.x{2} => ={res})=> //; last by smt().
        proc.
        call (_: mem Log.qs G1'.x,
                 ={glob Log} /\
                 (forall x, x \in Log.qs{2} = x \in RO.m{2}) /\
                 eq_except (pred1 G1'.x{2}) RO.m{1} RO.m{2}).
        + by apply Da2L.
        + proc; inline *; sp; if=> //=; auto=> /> //= &1 &2 x2_notin_qs eq_qs_m eqe _ y _.
          rewrite !inE !get_setE x2_notin_qs /= eq_except_set_eq //= eq_sym.
          split.
          + move=> x_notin_m2; split.
            + by move=> x_notin_m1 + x1; rewrite in_fsetU in_fset1 mem_set eq_qs_m.
            move: eqe; rewrite eq_exceptP /pred1=> /(_ x{2}) h + /h eq_mx.
            by rewrite domE eq_mx -domE.
          move=> x_in_m2; split.
          + move: eqe; rewrite eq_exceptP /pred1=> /(_ x{2}) h + /h eq_mx.
            by rewrite domE eq_mx -domE.
          move=> x_in_m1 x2_neq_G1'x. move: eqe; rewrite eq_exceptP=> -> //= x1.
          by rewrite in_fsetU in_fset1 eq_qs_m; case: (x1 = x{2})=> [->|] //=; rewrite x_in_m2.
        + by progress; apply (Bound_o_ll RO); apply (RO_o_ll _); smt(dsampleL).
        + progress; exists* G1'.x; elim* => x; conseq (Bound_o_ll RO _) (Bound_o_stable RO x)=> //.
          by apply (RO_o_ll _); smt(dsampleL).
        + inline RO.o; auto.
          call (_: ={glob Log, glob RO} /\ (forall x, x \in Log.qs{2} = x \in RO.m{2})).
          + proc; inline Bound(RO).LO.o RO.o; sp; if=> //; auto=> /> &2 eq_qs_m _ y _; split.
            + by move=> x_notin_m x1; rewrite in_fsetU in_fset1 mem_set eq_qs_m.
            move=> x_in_m x1; rewrite in_fsetU in_fset1 eq_qs_m; case: (x1 = x{2})=> //=.
            by move=> ->; rewrite x_in_m.          
          inline Log(RO).init RO.init; auto=> />; split=> [x1|_ r qs m eq_qs_m y _].
          + by rewrite in_fset0 mem_empty.
        by rewrite get_set_eqE //= eq_except_setl /= eq_qs_m /#.
      by rewrite Pr [mu_or]; smt(mu_bounded).
      qed.
    end section.
  end OnBound.
end ROM_BadCall.

theory ROM_Bad.
  (** This theory (and its final result FEL_ROM) abstracts away from the
      Failure Event Lemma for Random Oracles, allowing it to be used at
      a high-level of abstraction, without worrying about fel internals. *)
  type from.
  type to.

  op dsample: from -> to distr.
  axiom dsampleL x: mu (dsample x) predT = 1%r.

  op qH:int.
  axiom qH_pos: 0 < qH.

  clone export BoundedCall with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample,
    op qH      <- qH.

  module type Dist(H:Oracle) = {
    proc distinguish(): bool {H.o}
  }.

  module Experiment(H:Oracle,D:Dist) = {
    module D = D(Bound(H))

    proc main(): bool = {
      var b;

      Bound(H).init();
      b <@ D.distinguish();
      return b;
    }
  }.

  section.
    (** Note that the proof does not depend at all on the fact that O1 and O2
        are random oracles. This argument could (and should) be generalized to
        any two oracles whose probability of behaving differently on a single
        query is bounded. *)
    declare module O1 : Oracle {Bound}.
    axiom O1_o_ll: islossless O1.o.

    declare module O2 : Oracle {O1,Bound}.
    axiom O2_o_ll: islossless O2.o.

    declare module D : Dist {O1,O2,Bound}.
    axiom D_distinguish_ll (O <: Oracle {D}): islossless O.o => islossless D(O).distinguish.

    lemma FEL_ROM (bad: (glob O2) -> bool)
                  (Phi: (glob O1) -> (glob O2) -> bool) eps &m:
      0%r <= eps => (* should be derivable from phoare but isn't *)
      hoare [O2.init: true ==> !bad (glob O2)] =>
      equiv [O1.init ~ O2.init: true ==> Phi (glob O1){1} (glob O2){2}] =>
      hoare [O2.o: bad (glob O2) ==> bad (glob O2)] =>
      phoare [O2.o: !bad (glob O2) ==> bad (glob O2)] <= eps =>
      equiv [O1.o ~ O2.o: !bad (glob O2){2} /\ ={x} /\ Phi (glob O1){1} (glob O2){2} ==>
                          !bad (glob O2){2} => ={res} /\ Phi (glob O1){1} (glob O2){2}] =>
      Pr[Experiment(O1,D).main() @ &m: res] <= Pr[Experiment(O2,D).main() @ &m: res] + qH%r * eps.
    proof.
    move=> eps_pos badinit eq_init bad_preserved bad1 eq_upto.
    apply (ler_trans (Pr[Experiment(O2,D).main() @ &m: res] + Pr[Experiment(O2,D).main() @ &m: bad (glob O2)])).
      cut: Pr[Experiment(O1,D).main() @ &m: res] <= Pr[Experiment(O2,D).main() @ &m: res \/ bad (glob O2)].
        byequiv (_: ={glob D} ==> !bad (glob O2){2} => ={res})=> //; last smt().
        proc.
        call (_: bad (glob O2),
                 ={glob Bound} /\
                 Phi (glob O1){1} (glob O2){2}).
          by apply D_distinguish_ll.
          by proc; sp; if=> //; wp; call eq_upto.
          by progress; proc; sp; if=> //; wp; call O1_o_ll.
          by progress; proc; sp; if=> //; wp;
             call (_: bad (glob O2) ==> bad (glob O2));
               first by conseq O2_o_ll bad_preserved.
        call (_: true ==> ={glob Bound} /\ Phi (glob O1){1} (glob O2){2} /\ !bad (glob O2){2}).
          proc; inline Bound(O1).init Bound(O2).init; wp.
          by call (_: true ==> Phi (glob O1){1} (glob O2){2} /\ !bad (glob O2){2});
               first conseq eq_init _ badinit=> //.
        by skip=> /#.
      by rewrite Pr [mu_or]; smt(mu_bounded).
    cut: Pr[Experiment(O2,D).main() @ &m: bad (glob O2)] <= qH%r * eps.
      cut ->: Pr[Experiment(O2,D).main() @ &m: bad (glob O2)]
              = Pr[Experiment(O2,D).main() @ &m: bad (glob O2) /\ Bound.c <= qH].
        byequiv (_: ={glob D, glob O2} ==> bad (glob O2){1} <=> bad (glob O2){2} /\ Bound.c{2} <= qH)=> //.
        proc.
        call (_: ={glob O2, glob Bound} /\ Bound.c{2} <= qH)=> //.
          by proc; sp; if=> //; wp; call (_: true); skip=> /#.
        call (_: ={glob O2} ==> ={glob O2, glob Bound} /\ Bound.c{2} <= qH).
          by proc*; inline Bound(O2).init; wp; call (_: true); skip; smt(qH_pos).
        done.
      fel 1 Bound.c (fun x, eps) qH (bad (glob O2)) [Bound(O2).o: (Bound.c < qH)]=> //.
        rewrite Bigreal.sumr_const count_predT size_range /=.
        by move: qH_pos=> /#.
        by call (_: true ==> !bad (glob O2) /\ Bound.c = 0);
          first proc; wp; call badinit.
        proc; sp;rcondt 1 => //.
        by wp; call (_: !bad (glob O2) ==> bad (glob O2)).
        by progress; proc; sp; if=> //; wp; call (_: true); skip; smt(dsampleL).
        by progress; proc; rcondf 2; auto; smt(dsampleL).
    smt(mu_bounded).
    qed.
  end section.
end ROM_Bad.
