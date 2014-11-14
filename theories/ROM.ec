(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

require import FMap.
require import Distr.

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
      b = D.distinguish();
      return b;
    }
  }.
end Types.

theory Lazy.
  require import FSet.

  type from.
  type to.

  op dsample: from -> to distr.

  clone export Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO:Oracle = {
    var m:(from, to) map

    proc init():unit = {
      m = FMap.empty;
    }
  
    proc o(x:from):to = {
      var y:to;
      y = $dsample x;
      if (!mem x (dom m)) m.[x] = y;
      return oget (m.[x]);
    }
  }.

  lemma RO_init_ll: islossless RO.init.
  proof. by proc; wp. qed.

  lemma RO_o_ll:
    (forall x, mu (dsample x) True = 1%r) =>
    islossless RO.o.
  proof. by intros=> dsampleL; proc; auto; smt. qed.

  equiv RO_init_eq: RO.init ~ RO.init: true ==> ={glob RO}
  by sim.

  equiv RO_o_eq: RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}
  by sim.

  hoare dom_RO_o d x': RO.o: x = x' /\ dom RO.m = d ==> dom RO.m = add x' d.
  proof. by proc; auto; smt. qed.
end Lazy.

theory Eager.
  require import ISet.
  (*---*) import Finite.
  require import FSet.

  type from.
  type to.

  op dsample: from -> to distr.

  clone export Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO: Oracle = {
    var m:(from,to) map

    proc init(): unit = {
      var y:to;
      var work:from set;
      var f:from;

      m = FMap.empty;
      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        y = $dsample f;
        m.[f] = y;
        work = rm f work;
      }
    }

    proc o(x:from): to = {
      return oget m.[x];
    }
  }.

  lemma RO_init_full:
    finite univ<:from> =>
    hoare [RO.init: true ==> forall x, mem x (dom RO.m)].
  proof.
    move=> fType; proc.
    while (forall x, mem x work \/ mem x (dom RO.m)).
      by auto; smt.
    by auto; smt.
  qed.

  lemma RO_init_ll:
    finite univ<:from> =>
    (forall x, mu (dsample x) True = 1%r) =>
    islossless RO.init.
  proof.
    move=> fType dsampleL; proc.
    while (true) (card work);
    by auto; smt.
  qed.

  lemma RO_o_ll: islossless RO.o.
  proof. by proc; wp. qed.

  lemma RO_init_eq:
    finite univ<:from> =>
    equiv [RO.init ~ RO.init: true ==> ={glob RO}].
  proof. by move=> fType; proc; while (={glob RO, work}); auto. qed.

  equiv RO_o_eq: RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}
  by sim.

  lemma dom_RO_init x:
    finite univ<:from> =>
    hoare [RO.init: true ==> mem x (dom RO.m)].
  proof. by move=> fType; proc; while (forall x, !mem x work => mem x (dom RO.m)); auto; smt. qed.
end Eager.

theory LazyEager.
  require import ISet.
  (*---*) import Finite.
  require import FSet.

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
        var m:(from, to) map

        proc init():unit = {
          m = FMap.empty;
        }

        proc o(x:from):to = {
          var y:to;
          y = $dsample x;
          if (!mem x (dom m)) m.[x] = y;
          return oget (m.[x]);
        }
      }

      proc resample(): unit = {
        var work:from set;
        var f:from;
        var y,y0:to;

        work = toFSet univ;
        while (work <> FSet.empty)
        {
          f = pick work;
          y = $dsample f;
          if (!mem f (dom H.m)) H.m.[f] = y;
          work = rm f work;
        }
      }

      module D = D(H)

      proc main(): bool = {
        var b:bool;

        H.init();
        b = D.distinguish();
        resample();

        return b;
      }
    }.

    local lemma IND_Lazy:
      finite univ<:from> =>
      (forall x, mu (dsample x) True = 1%r) =>
      equiv [IND(Lazy.RO,D).main ~ IND_Lazy.main: ={glob D} ==> ={res}].
    proof.
      move=> fromF dsampleL; proc; seq 2 2: (={b}).
        call (_: Lazy.RO.m{1} = IND_Lazy.H.m{2}); first by sim.
        by call (_: ={glob D} ==> Lazy.RO.m{1} = IND_Lazy.H.m{2});
          first by proc; wp.
      inline IND_Lazy.resample;
      while{2} (true) (card work{2});
        first by auto; smt.
      by auto; smt.
    qed.

    local module IND_Eager = {
      module H = {
        var m:(from,to) map

        proc o(x:from): to = {
          return oget (m.[x]);
        }
      }

      proc resample(): unit = {
        var work:from set;
        var f:from;
        var y,y0:to;

        work = toFSet univ;
        while (work <> FSet.empty)
        {
          f = pick work;
          y = $dsample f;
          if (!mem f (dom H.m)) H.m.[f] = y;
          work = rm f work;
        }
      }

      module D = D(H)

      proc main(): bool = {
        var b:bool;

        H.m = FMap.empty;
        resample();
        b = D.distinguish();

        return b;
      }
    }.

    local lemma eager_query:
      finite univ<:from> =>
      (forall x, mu (dsample x) True = 1%r) =>
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
                mem x{1} work{1});
        first by auto; smt.
      case (!mem x{2} (dom IND_Lazy.H.m{2})); [rcondt{2} 2; first by auto |
                                            rcondf{2} 2; first by auto].
        transitivity{1} {y0 = $dsample x;
                         while (work <> FSet.empty) {
                           f = pick work;
                           y = $dsample f;
                           if (!mem f (dom IND_Eager.H.m))
                             IND_Eager.H.m.[f] = if f = x then y0 else y;
                           work = rm f work;
                         }
                         result = oget IND_Eager.H.m.[x]; }
                         (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
                         ((={x,work} /\
                          IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
                          mem x{1} work{1}) /\
                          !mem x{2} (dom IND_Lazy.H.m{2}) ==>
                          ={result} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}) => //.
          by move=> &1 &2 H; exists IND_Lazy.H.m{2}, x{2}, work{2}; generalize H.
        transitivity{1} {while (work <> FSet.empty) {
                           f = pick work;
                           y = $dsample f;
                           if (!mem f (dom IND_Eager.H.m))
                             IND_Eager.H.m.[f] = y;
                           work = rm f work;
                         }
                         y0 = $dsample x;
                         result = oget IND_Eager.H.m.[x]; }
                         (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
                         (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})=> //.
          by move=> &1 &2 H; exists IND_Eager.H.m{2}, x{2}, work{2}; generalize H.
        by sim; rnd{2}; sim : (={x,IND_Eager.H.m}); smt.

        wp; symmetry.
        eager while (H:y0 = $dsample x; ~ y0 = $dsample x; : ={x} ==> ={y0})=> //; first by rnd.
          swap{2} 5 -4; swap [2..3] -1; case ((x = pick work){1}).
            by wp; rnd{2}; rnd; rnd{1}; wp; skip; smt.
            by auto; smt.
          by sim.

        wp; while (={x, work} /\
                   (!mem x work => mem x (dom IND_Eager.H.m)){1} /\
                   IND_Lazy.H.m.[x]{2} = Some y0{1} /\
                   if (mem x (dom IND_Eager.H.m)){1}
                   then IND_Eager.H.m{1} = IND_Lazy.H.m{2}
                   else eq_except IND_Eager.H.m{1} IND_Lazy.H.m{2} x{1}).
          (* "expect 12 (move)" is used for catching changes in tactic behaviour early *)
          auto; (progress; expect 12 move); last 2 first; first 11 smt.
          case ((pick work = x){2})=> pick_x; last smt.
          subst x{2}; generalize H7 H1; rewrite -neqF /eq_except=> -> /= eq_exc.
          by apply map_ext=> x0; case (pick work{2} = x0); smt.
        by auto; smt.

      wp; while (={x,work} /\
                 IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
                 mem x{2} (dom IND_Lazy.H.m{2}) /\
                 oget IND_Eager.H.m.[x]{1} = result{2}).
         by auto; smt.
      by auto; smt.
    qed.

    local lemma eager_aux:
      finite univ<:from> =>
      (forall x, mu (dsample x) True = 1%r) =>
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
      finite univ<:from> =>
      (forall x, mu (dsample x) True = 1%r) =>
      equiv [IND_Eager.main ~ IND(Eager.RO,D).main: ={glob D} ==> ={res}].
    proof.
      move=> fromF dsampleL; proc.
      call (_: (forall x, mem x (dom IND_Eager.H.m{1})) /\ IND_Eager.H.m{1} = Eager.RO.m{2});
        first by proc; skip; smt.
      inline RO.init IND_Eager.resample.
      while (={work} /\
             (forall x, !mem x (dom IND_Eager.H.m{1}) <=>
                        mem x work{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
        by auto; progress; smt.
      by auto; smt.
    qed.

    lemma eagerRO:
      finite univ<:from> =>
      (forall x, mu (dsample x) True = 1%r) =>
      equiv [IND(Lazy.RO,D).main ~ IND(Eager.RO,D).main: ={glob D} ==> ={res}].
    proof.
      move=> fromF dsampleL; bypr (res{1}) (res{2})=> // &1 &2 a eq_D.
      apply (eq_trans _ Pr[IND_Lazy.main() @ &1: a = res]);
        first by byequiv (IND_Lazy _ _).
      apply (eq_trans _ Pr[IND_Eager.main() @ &1: a = res]);
        first by byequiv (eager_aux _ _).
      by byequiv (IND_Eager _ _).
    qed.
  end section.
end LazyEager.

theory BoundedCall.
  require import Int.

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
      c = 0;
    }

    proc o(x:from): to = {
      var r = witness;

      if (c < qH) {
        r = O.o(x);
        c = c + 1;
      }
      return r;
    }
  }.

  lemma Bound_init_ll (O <: Oracle): islossless O.init => islossless Bound(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Bound_o_ll (O <: Oracle): islossless O.o => islossless Bound(O).o.
  proof. by move=> O_o_ll; proc; sp; if=> //; wp; call O_o_ll. qed.
end BoundedCall.

theory ListLog.
  require import Int.
  require import List.

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
      qs = [];
    }

    proc o(x:from): to = {
      var r:to;

      qs = x::qs;
      r = O.o(x);
      return r;
    }
  }.

  lemma Log_init_ll (O <: Oracle): islossless O.init => islossless Log(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Log_o_ll (O <: Oracle): islossless O.o => islossless Log(O).o.
  proof. by move=> O_oL; proc; call O_oL; wp. qed.

  lemma Log_o_stable (O <: Oracle {Log}) q:
    islossless O.o => phoare[Log(O).o: mem q Log.qs ==> mem q Log.qs] = 1%r.
  proof. by move=> O_o_ll; proc; call O_o_ll; auto; progress; right. qed.

  module Bound(O:Oracle) = {
    module LO = Log(O)

    proc init(): unit = {
      Log(O).init();
    }

    proc o(x:from): to = {
      var r = witness;

      if (length Log.qs < qH) {
        r = O.o(x);
      }
      return r;
    }
  }.
end ListLog.

theory SetLog.
  require import Int.
  require import FSet.

  type from.
  type to.

  op dsample: from -> to distr.

  op qH:int.

  clone export Lazy with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module Log(O:Oracle) = {
    var qs:from set

    proc init(): unit = {
      O.init();
      qs = FSet.empty;
    }

    proc o(x:from): to = {
      var r;

      r  = O.o(x);
      qs = add x qs;
      return r;
    }
  }.

  lemma Log_init_ll (O <: Oracle): islossless O.init => islossless Log(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Log_o_ll (O <: Oracle): islossless O.o => islossless Log(O).o.
  proof. by move=> O_o_ll; proc; wp; call O_o_ll; wp. qed.

  hoare Log_o_stable (O <: Oracle {Log}) x: Log(O).o: mem x Log.qs ==> mem x Log.qs.
  proof. by proc; wp; call (_: true); skip; smt. qed.

  module Bound(O:Oracle) = {
    module LO = Log(O)

    proc init = Log(O).init

    proc o(x:from): to = {
      var r = witness;

      if (card Log.qs < qH) {
        r = LO.o(x);
      }
      return r;
    }
  }.

  lemma Bound_init_ll (O <: Oracle): islossless O.init => islossless Bound(O).init.
  proof. by move=> O_init_ll; proc; wp; call O_init_ll. qed.

  lemma Bound_o_ll (O <: Oracle {Log}): islossless O.o => islossless Bound(O).o.
  proof. by move=> O_o_ll; proc; sp; if=> //; wp; call (Log_o_ll O _). qed.

  hoare Bound_o_stable (O <: Oracle {Log}) x: Bound(O).o: mem x Log.qs ==> mem x Log.qs.
  proof. by proc; sp; if=> //; wp; call (Log_o_stable O x). qed.

  equiv Log_Bound (O <: Oracle {Log}) (D <: Dist {O,Log}):
    IND(Bound(O),D).main ~ IND(Log(Bound(O)),D).main: ={glob O, glob D} ==> ={res}.
  proof.
    proc.
    call (_: ={glob O} /\ card Log.qs{1} <= card Log.qs{2} /\ (card Log.qs{1} < qH => ={glob Log})).
      proc*; inline Log(Bound(O)).o Bound(O).o Bound(O).LO.o.
      sp; if; first smt.
        by wp; call (_: true); auto; smt.
        by auto; smt.
    by inline *; wp; call (_: true).
  qed.
end SetLog.

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
  require import Int.
  require import Real.
  require import FSet.

  type from.
  type to.

  op dsample: from -> to distr.
  axiom dsampleL x: mu (dsample x) True = 1%r.

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
        x = D.a1();
        y = H.o(x);
        b = D.a2(y);
        return b;
      }
    }.

    module G1(D:Dist, H:Oracle) = {
      module D = D(Log(H))

      proc main(): bool = {
        var x, y, b;

        Log(H).init();
        x = D.a1();
        y = $dsample x;
        b = D.a2(y);
        return b;
      }
    }.

    module G2(D:Dist, H:Oracle) = {
      module D = D(Log(H))

      proc main(): bool = {
        var x, y, b;

        Log(H).init();
        x = D.a1();
        y = $dsample x;
        b = D.a2(y);
        return mem x Log.qs;
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
          x = D.a1();
          y = $dsample x;
          b = D.a2(y);
          return b;
        }
      }.

      lemma ROM_BadCall &m:
        Pr[G0(D,RO).main() @ &m: res] <= Pr[G1(D,RO).main() @ &m: res] + Pr[G2(D,RO).main() @ &m: res].
      proof.
        cut ->: Pr[G2(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: mem G1'.x Log.qs].
          byequiv (_: ={glob D} ==> res{1} = (mem G1'.x Log.qs){2})=> //.
          proc.
          call (_: ={glob Log, glob RO}); first by sim.
          rnd; call (_: ={glob Log, glob RO}); first by sim.
          by inline *; wp.
        cut ->: Pr[G1(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: res].
          by byequiv (_: ={glob D} ==> ={res}); first by sim.
        cut: Pr[G0(D,RO).main() @ &m: res] <= Pr[G1'(D,RO).main() @ &m: res \/ mem G1'.x Log.qs].
          byequiv (_: ={glob D} ==> !mem G1'.x{2} Log.qs{2} => ={res})=> //; last smt.
          proc.
          call (_: mem G1'.x Log.qs,
                   ={glob Log} /\
                   Log.qs{2} = dom RO.m{2} /\
                   eq_except RO.m{1} RO.m{2} G1'.x{2}).
            by apply Da2L.
            by proc; inline RO.o; auto; smt.
            by progress; apply (Log_o_ll RO); apply (RO_o_ll _); smt.
            move=> &1; proc; wp; call (RO_o_ll _); first smt.
            by skip; rewrite mem_add=> //= &hr ->.
          inline RO.o; auto.
          call (_: ={glob Log, glob RO} /\ Log.qs{2} = dom RO.m{2}).
            by proc; inline RO.o; auto; smt.
          by inline Log(RO).init RO.init; auto; smt.
        by rewrite Pr [mu_or]; smt.
      qed.
    end section.
  end OnLog.

  theory OnBound.
    module G0(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x = D.a1();
        y = H.o(x);
        b = D.a2(y);
        return b;
      }
    }.

    module G1(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x = D.a1();
        y = $dsample x;
        b = D.a2(y);
        return b;
      }
    }.

    module G2(D:Dist, H:Oracle) = {
      module D = D(Bound(H))

      proc main(): bool = {
        var x, y, b;

        Bound(H).init();
        x = D.a1();
        y = $dsample x;
        b = D.a2(y);
        return mem x Log.qs;
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
          x = D.a1();
          y = $dsample x;
          b = D.a2(y);
          return b;
        }
      }.

      lemma ROM_BadCall &m:
        Pr[G0(D,RO).main() @ &m: res] <= Pr[G1(D,RO).main() @ &m: res] + Pr[G2(D,RO).main() @ &m: res].
      proof.
        cut ->: Pr[G2(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: mem G1'.x Log.qs].
          byequiv (_: ={glob D} ==> res{1} = (mem G1'.x Log.qs){2})=> //.
          proc.
          call (_: ={glob Log, glob RO}); first by sim.
          rnd; call (_: ={glob Log, glob RO}); first by sim.
          by inline *; wp.
        cut ->: Pr[G1(D,RO).main() @ &m: res] = Pr[G1'(D,RO).main() @ &m: res].
          by byequiv (_: ={glob D} ==> ={res}); first by sim.
        cut: Pr[G0(D,RO).main() @ &m: res] <= Pr[G1'(D,RO).main() @ &m: res \/ mem G1'.x Log.qs].
          byequiv (_: ={glob D} ==> !mem G1'.x{2} Log.qs{2} => ={res})=> //; last smt.
          proc.
          call (_: mem G1'.x Log.qs,
                   ={glob Log} /\
                   Log.qs{2} = dom RO.m{2} /\
                   eq_except RO.m{1} RO.m{2} G1'.x{2}).
            by apply Da2L.
            by proc; inline Bound(RO).LO.o RO.o; sp; if=> //; auto; smt.
            by progress; apply (Bound_o_ll RO); apply (RO_o_ll _); smt.
            move=> &1; proc; sp; if=> //=.
            inline Bound(RO).LO.o; wp; call (RO_o_ll _); first smt.
            by auto; rewrite mem_add=> //= &hr [*] _ ->.
          inline RO.o; auto.
          call (_: ={glob Log, glob RO} /\ Log.qs{2} = dom RO.m{2}).
            by proc; inline Bound(RO).LO.o RO.o; sp; if=> //; auto; smt.
          by inline Bound(RO).init Log(RO).init RO.init; auto; smt.
        by rewrite Pr [mu_or]; smt.
      qed.
    end section.
  end OnBound.    
end ROM_BadCall.

theory ROM_Bad.
  (** This theory (and its final result FEL_ROM) abstracts away from the
      Failure Event Lemma for Random Oracles, allowing it to be used at
      a high-level of abstraction, without worrying about fel internals. *)
  require import Int.
  require import Real.
  require import Sum. (* for the FEL tactic *)

  type from.
  type to.

  op dsample: from -> to distr.
  axiom dsampleL x: mu (dsample x) True = 1%r.

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
      b = D.distinguish();
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
      apply (Trans _ (Pr[Experiment(O2,D).main() @ &m: res] + Pr[Experiment(O2,D).main() @ &m: bad (glob O2)])).
        cut: Pr[Experiment(O1,D).main() @ &m: res] <= Pr[Experiment(O2,D).main() @ &m: res \/ bad (glob O2)].
          byequiv (_: ={glob D} ==> !bad (glob O2){2} => ={res})=> //; last smt.
          proc.
          call (_: bad (glob O2),
                   ={glob Bound} /\
                   Phi (glob O1){1} (glob O2){2}).
            by apply D_distinguish_ll.
            by proc; sp; if=> //; wp; call eq_upto.
            by progress; proc; sp; if=> //; wp; call O1_o_ll.
            by progress; proc; sp; if=> //; wp;
               call (_: bad (glob O2) ==> bad (glob O2));
                 first by conseq* O2_o_ll bad_preserved.
          call (_: true ==> ={glob Bound} /\ Phi (glob O1){1} (glob O2){2} /\ !bad (glob O2){2}).
            proc; inline Bound(O1).init Bound(O2).init; wp.
            by call (_: true ==> Phi (glob O1){1} (glob O2){2} /\ !bad (glob O2){2});
                 first conseq* eq_init _ badinit=> //.
          by skip; smt.
        by rewrite Pr [mu_or]; smt.
      cut: Pr[Experiment(O2,D).main() @ &m: bad (glob O2)] <= qH%r * eps.
        cut ->: Pr[Experiment(O2,D).main() @ &m: bad (glob O2)]
                = Pr[Experiment(O2,D).main() @ &m: bad (glob O2) /\ Bound.c <= qH].
          byequiv (_: ={glob D, glob O2} ==> bad (glob O2){1} <=> bad (glob O2){2} /\ Bound.c{2} <= qH)=> //.
          proc.
          call (_: ={glob O2, glob Bound} /\ Bound.c{2} <= qH)=> //.
            by proc; sp; if=> //; wp; call (_: true); skip; smt.
          call (_: ={glob O2} ==> ={glob O2, glob Bound} /\ Bound.c{2} <= qH).
            by proc*; inline Bound(O2).init; wp; call (_: true); skip; smt.
          done.
        fel 1 Bound.c (fun x, eps) qH (bad (glob O2)) [Bound(O2).o: (Bound.c < qH)]=> //.
          smt.
          by call (_: true ==> !bad (glob O2) /\ Bound.c = 0);
            first proc; wp; call badinit.
          proc; sp; if=> //; last by hoare.
          by wp; call (_: !bad (glob O2) ==> bad (glob O2)).
          by progress; proc; sp; if=> //; wp; call (_: true); skip; smt.
          by progress; proc; rcondf 2; auto; smt.
      smt.
    qed.
  end section.
end ROM_Bad.

(*
theory Wrappers.
  clone import Types.
  clone Lazy with
    type from = from,
    type to = to,
    op dsample = dsample.

  module type WRO = {
    proc init(qO:int): unit {}
    proc o(x:from): to
  }.

  module IND_b(H:WRO,D:Dist) = {
    module D = D(H)

    proc main(qO:int): bool = {
      var b:bool;
      H.init(qO);
      b = D.distinguish();
      return b;
    }
  }.

  (** Budget-cutting wrapper *)
  require import Int.
  module Count(H:Oracle) = {
    var qO:int
    var qs:int

    proc init(qO:int): unit = {
      H.init();
      Count.qO = qO;
      qs = 0;
    }

    proc o(x:from): to = {
      var r:to;
      if (qs < qO)
      {
        qs = qs + 1;
        r = H.o(x);
      }
      return r;
    }
  }.

  import FSet.
  import ISet.Finite.
  lemma bound qO' (D <: Dist {Lazy.RO,Count}):
    0 < qO' =>
    (forall x, mu (dsample x) cpTrue = 1%r) =>
    (forall (H <: ARO {D}), islossless H.o => islossless D(H).distinguish) =>
    equiv [ IND(Lazy.RO,D).main ~ IND_b(Count(Lazy.RO),D).main:
              qO{2} = qO' ==>
              (Count.qs{2} < qO' =>
                 ={res} /\
                 size Lazy.RO.m{1} <= Count.qs{2}) ].
  proof strict.
  intros=> lt0_qO dsampleL DL; proc.
  call (_: Count.qO <= Count.qs,
           ={glob Lazy.RO} /\
           Count.qO{2} = qO' /\
           size Lazy.RO.m{1} <= Count.qs{2}).
    (* H *)
    proc; rcondt{2} 1; first intros=> &m; skip; progress=> //; smt.
      inline Lazy.RO.o; wp; rnd; wp; skip; progress=> //; last smt.
        by rewrite /size dom_set card_add_nin -/(in_dom _ _); last smt.
    by intros=> _ _; apply Lazy.lossless_o.
    by intros=> _; proc; if=> //; inline Lazy.RO.o; wp; rnd; wp; skip; smt.
  inline Count(Lazy.RO).init; wp; call (_: true ==> ={glob Lazy.RO} /\ dom Lazy.RO.m{1} = FSet.empty)=> //;
    first by proc; wp; skip; progress=> //; smt.
  wp; skip; cut H1: ISet.empty<:from> == FSet.empty by smt; progress=> //.
    by rewrite /size H card_empty.
    by cut [eq_res _]:= H2 _; first smt.
    by cut [_ [_ [fdom _]]]:= H2 _; first smt.
  qed.

(*
  (** Query-tracking wrapper *)
  require import Int.
  module Index(H:Oracle) = {
    var qs:(int,from) map
    var qc:int

    fun init(): unit = {
      H.init();
      qs = FMap.Core.empty;
      qc = 0;
    }

    fun o(x:from): to = {
      var r:to;
      if (!in_rng x qs)
      {
        qs.[qc] = x;
        qc = qc + 1;
      }
      r = H.o(x);
      return r;
    }
  }.
*)
  (** Query-numbering wrapper *)
  module Number(H:Oracle) = {
    var qs:(from,int) map
    var qc:int

    proc init(): unit = {
      H.init();
      qs = FMap.empty;
      qc = 0;
    }

    proc o(x:from): to = {
      var r:to;
      if (!in_dom x qs)
      {
        qs.[x] = qc;
        qc = qc + 1;
      }
      r = H.o(x);
      return r;
    }
  }.
end Wrappers.
*)

