require import FMap. import OptionGet.
require import Distr.

theory Types.
  type from.
  type to.

  op dsample: from -> to distr. (* Distribution to use on the target type; it can be parameterized by the input *)

  (* A signature for random oracles from "from" to "to". *)
  module type Oracle =
  {
    fun init():unit {*}
    fun o(x:from):to
  }.

  module type ARO = { fun o(x:from):to }.

  module type Dist (H:ARO) = {
    fun distinguish(): bool {* H.o}
  }.

  module IND(H:Oracle,D:Dist) = {
    module D = D(H)

    fun main(): bool = {
      var b:bool;

      H.init();
      b = D.distinguish();
      return b;
    }
  }.
end Types.

theory Lazy.
  type from.
  type to.

  op dsample: from -> to distr.

  clone import Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.
  require import FSet.

  module RO:Oracle = {
    var m:(from, to) map

    fun init():unit = {
      m = FMap.Core.empty;
    }
  
    fun o(x:from):to = {
      var y:to;
      y = $dsample x;
      if (!in_dom x m) m.[x] = y;
      return proj (m.[x]);
    }
  }.

  lemma lossless_init: islossless RO.init.
  proof strict.
  by fun; wp.
  qed.

  lemma lossless_o:
    (forall x, mu (dsample x) cpTrue = 1%r) =>
    islossless RO.o.
  proof strict.
  by intros=> dsampleL; fun; wp; rnd; skip; smt.
  qed.

  equiv abstract_init:
    RO.init ~ RO.init: true ==> ={glob RO}
  by (fun; wp).

  equiv abstract_o:
    RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}
  by (fun; eqobs_in).
end Lazy.

theory Eager.
  require import ISet.
    import Finite.
  require import FSet.

  type from.
  type to.

  op dsample: from -> to distr.

  clone import Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO: Oracle = {
    var m:(from,to) map

    fun init(): unit = {
      var y:to;
      var work:from set;
      var f:from;

      m = FMap.Core.empty;
      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        y = $dsample f;
        m.[f] = y;
        work = rm f work;
      }
    }

    fun o(x:from): to = {
      return proj m.[x];
    }
  }.

  lemma lossless_init:
    finite univ<:from> =>
    (forall x, mu (dsample x) cpTrue = 1%r) =>
    islossless RO.init.
  proof strict.
  intros=> fType dsampleL; fun.
  while (true) (card work).
    by intros=> z; wp; rnd cpTrue; wp;
       skip; smt.
  by wp; skip; smt.
  qed.

  lemma lossless_o: islossless RO.o.
  proof strict.
  by fun; wp.
  qed.

  lemma abstract_init:
    finite univ<:from> =>
    equiv [RO.init ~ RO.init: true ==> ={glob RO} /\ forall x, in_dom x RO.m{1}].
  proof strict.
  intros=> fType; fun;
  while (={glob RO, work} /\ forall x, !mem x work{1} => in_dom x RO.m{1}).
    by wp; rnd; wp; skip; progress=> //; smt.
  by wp; skip; smt.
  qed.

  equiv abstract_o: RO.o ~ RO.o: ={glob RO, x} ==> ={glob RO, res}
  by (fun; wp).
end Eager.

theory LazyEager.
  require import ISet.
    import Finite.
  require import FSet.

  type from.
  axiom finite: finite univ<:from>.

  type to.

  op dsample: from -> to distr.

  clone import Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  clone import Lazy with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  clone import Eager with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  section.
  (* Proof note: We may be missing losslessness assumptions on D *)
  declare module D:Dist {Lazy.RO,Eager.RO}.

  local module IND_Lazy = {
    module H:Oracle = {
      var m:(from, to) map

      fun init():unit = {
        m = FMap.Core.empty;
      }
  
      fun o(x:from):to = {
        var y:to;
        y = $dsample x;
        if (!in_dom x m) m.[x] = y;
        return proj (m.[x]);
      }
    }

    fun resample(): unit = {
      var work:from set;
      var f:from;
      var y,y0:to;

      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        y = $dsample f;
        if (!in_dom f H.m) H.m.[f] = y;
        work = rm f work;
      }
    }

    module D = D(H)

    fun main(): bool = {
      var b:bool;

      H.init();
      b = D.distinguish();
      resample();

      return b;
    }
  }.

  local lemma IND_Lazy: (forall x, mu (dsample x) cpTrue = 1%r) =>
    equiv [IND(Lazy.RO,D).main ~ IND_Lazy.main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; fun; seq 2 2: (={b}).
    call (_: Lazy.RO.m{1} = IND_Lazy.H.m{2}); first by fun; eqobs_in.
    by call (_: true ==> Lazy.RO.m{1} = IND_Lazy.H.m{2})=> //;
      first by fun; wp.
    inline IND_Lazy.resample;
    while{2} (true) (card work{2}).
      intros=> &m z; wp; rnd; wp; skip; progress=> //; last smt.
        by rewrite card_rm_in ?mem_pick //; smt. (* This should definitely be a lemma in FSet. *)
    by wp; skip; progress=> //; smt.
  qed.

  local module IND_Eager = {
    module H = {
      var m:(from,to) map

      fun o(x:from): to = {
        return proj (m.[x]);
      }
    }

    fun resample(): unit = {
      var work:from set;
      var f:from;
      var y,y0:to;

      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        y = $dsample f;
        if (!in_dom f H.m) H.m.[f] = y;
        work = rm f work;
      }
    }

    module D = D(H)

    fun main(): bool = {
      var b:bool;

      H.m = FMap.Core.empty;
      resample();
      b = D.distinguish();

      return b;
    }
  }.

  local lemma eager_query: (forall x, mu (dsample x) cpTrue = 1%r) =>
    eager [IND_Eager.resample(); ,
               IND_Eager.H.o ~ IND_Lazy.H.o,
           IND_Lazy.resample();:
      ={x} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2} ==>
      ={res} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}].
  proof strict.
  intros=> dsampleL; eager fun.
  inline IND_Eager.resample IND_Lazy.resample; swap{2} 4 -3.
  seq 1 1: (={x,work} /\
            IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
            mem x{1} work{1});
     first by wp; skip; smt.
  case (!in_dom x IND_Lazy.H.m){2}; [rcondt{2} 2; first by intros=> &m; rnd |
                                     rcondf{2} 2; first by intros=> &m; rnd].
    transitivity{1} {y0 = $dsample x;
                     while (work <> FSet.empty) {
                       f = pick work;
                       y = $dsample f;
                       if (!in_dom f IND_Eager.H.m)
                         IND_Eager.H.m.[f] = if f = x then y0 else y;
                       work = rm f work;
                     }
                     result = proj IND_Eager.H.m.[x]; }
                     (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
                     ((={x,work} /\
                      IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
                      mem x{1} work{1}) /\
                      !in_dom x{2} IND_Lazy.H.m{2} ==>
                      ={result} /\ IND_Eager.H.m{1} = IND_Lazy.H.m{2}) => //.
      by intros=> &1 &2 H; exists IND_Lazy.H.m{2}, x{2}, work{2}; generalize H.
    transitivity{1} {while (work <> FSet.empty) {
                       f = pick work;
                       y = $dsample f;
                       if (!in_dom f IND_Eager.H.m)
                         IND_Eager.H.m.[f] = y;
                       work = rm f work;
                     }
                     y0 = $dsample x;
                     result = proj IND_Eager.H.m.[x]; }
                     (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})
                     (={x,work,IND_Eager.H.m} ==> ={result,IND_Eager.H.m})=> //.
      by intros &1 &2 H; exists IND_Eager.H.m{2}, x{2}, work{2}; generalize H.
    by eqobs_in; rnd{2}; eqobs_in true true: (={x,IND_Eager.H.m}); smt.

    wp; symmetry.
    eager while (H:y0 = $dsample x; ~ y0 = $dsample x; : ={x} ==> ={y0})=> //; first by rnd.
      swap{2} 5 -4; swap [2..3] -1; case (x = pick work){1}.
        by wp; rnd{2}; rnd; rnd{1}; wp; skip; smt.
        by wp; do 2!rnd; wp; skip; smt.
      by eqobs_in.

    wp; while (={x, work} /\
               (!mem x work => in_dom x IND_Eager.H.m){1} /\
               IND_Lazy.H.m.[x]{2} = Some y0{1} /\
               if (in_dom x IND_Eager.H.m){1}
                 then IND_Eager.H.m{1} = IND_Lazy.H.m{2}
                 else eq_except IND_Eager.H.m{1} IND_Lazy.H.m{2} x{1}).
      by wp; rnd; wp; skip; progress=> //; try case (pick work = x){2}; smt.
    by wp; rnd; skip; progress=> //; smt.

  wp; while (={x,work} /\
             IND_Eager.H.m{1} = IND_Lazy.H.m{2} /\
             in_dom x{2} IND_Lazy.H.m{2} /\ 
             proj IND_Eager.H.m.[x]{1} = result{2}).
     by wp; rnd; wp; skip; smt.
  by wp; rnd{2}; skip; smt.
  qed.

  local lemma eager_aux: (forall x, mu (dsample x) cpTrue = 1%r) =>
    equiv [IND_Lazy.main ~ IND_Eager.main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; fun; inline IND_Lazy.H.init.
  seq 1 1: (IND_Lazy.H.m{1} = IND_Eager.H.m{2}); first by wp.
  symmetry;
  eager (H: IND_Eager.resample(); ~ IND_Lazy.resample();:
              IND_Eager.H.m{1} = IND_Lazy.H.m{2} ==> IND_Eager.H.m{1} = IND_Lazy.H.m{2}): 
        (IND_Eager.H.m{1} = IND_Lazy.H.m{2})=> //;
    first by eqobs_in.
  eager fun H (IND_Eager.H.m{1} = IND_Lazy.H.m{2})=> //;
    first by apply eager_query=> //.
  by fun; eqobs_in.
  qed.

  local lemma IND_Eager: (forall x, mu (dsample x) cpTrue = 1%r) =>
    equiv [IND_Eager.main ~ IND(Eager.RO,D).main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; fun.
  call (_: (forall x, in_dom x IND_Eager.H.m{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
    by fun; skip; smt.
  inline RO.init IND_Eager.resample.
    while (={work} /\ (forall x, !in_dom x IND_Eager.H.m{1} <=> mem x work{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
      wp; rnd; wp; skip; progress=> //; smt.
    by wp; skip; smt.
  qed.

  lemma eagerRO: (forall x, mu (dsample x) cpTrue = 1%r) =>
    equiv [IND(Lazy.RO,D).main ~ IND(Eager.RO,D).main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; bypr (res{1}) (res{2})=> //; intros=> &1 &2 a.
  apply (eq_trans _ Pr[IND_Lazy.main() @ &1: a = res]);
    first by equiv_deno (IND_Lazy _).
  apply (eq_trans _ Pr[IND_Eager.main() @ &1: a = res]);
    first by equiv_deno (eager_aux _).
  by equiv_deno (IND_Eager _).
  qed.
  end section.
end LazyEager.

theory Wrappers.
  clone import Types.
  clone Lazy with
    type from = from,
    type to = to,
    op dsample = dsample.

  module type WRO = {
    fun init(qO:int): unit {*}
    fun o(x:from): to
  }.

  module IND_b(H:WRO,D:Dist) = {
    module D = D(H)

    fun main(qO:int): bool = {
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

    fun init(qO:int): unit = {
      H.init();
      Count.qO = qO;
      qs = 0;
    }

    fun o(x:from): to = {
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
  intros=> lt0_qO dsampleL DL; fun.
  call (_: Count.qO <= Count.qs,
           ={glob Lazy.RO} /\
           Count.qO{2} = qO' /\
           size Lazy.RO.m{1} <= Count.qs{2}).
    (* H *)
    fun; rcondt{2} 1; first intros=> &m; skip; progress=> //; smt.
      inline Lazy.RO.o; wp; rnd; wp; skip; progress=> //; last smt.
        by rewrite /size dom_set card_add_nin -/(in_dom _ _); last smt.
    by intros=> _ _; apply Lazy.lossless_o.
    by intros=> _; fun; if=> //; inline Lazy.RO.o; wp; rnd; wp; skip; smt.
  inline Count(Lazy.RO).init; wp; call (_: true ==> ={glob Lazy.RO} /\ dom Lazy.RO.m{1} = FSet.empty)=> //;
    first by fun; wp; skip; progress=> //; smt.
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

    fun init(): unit = {
      H.init();
      qs = FMap.Core.empty;
      qc = 0;
    }

    fun o(x:from): to = {
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