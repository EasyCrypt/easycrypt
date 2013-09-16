require import Map.
require import Distr.

theory Types.
  type from.
  type to.

  op dsample: to distr. (* Distribution to use on the target type *)

  (* A signature for random oracles from "from" to "to". *)
  module type Oracle =
  {
    fun init():unit {*}
    fun o(x:from):to
  }.

  module type ARO = { fun o(x:from):to }.
end Types.

theory Lazy.
  type from.
  type to.

  op dsample: to distr.

  clone import Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.
  require import FSet.

  module RO:Oracle = {
    var m:(from, to) map

    fun init():unit = {
      m = Map.empty;
    }
  
    fun o(x:from):to = {
      var y : to;
      y = $dsample;
      if (!in_dom x m) m.[x] = y;
      return proj (m.[x]);
    }
  }.

  lemma lossless_init: islossless RO.init.
  proof strict.
  by fun; wp.
  qed.

  lemma termination_o r:
    mu dsample cpTrue = r =>
    bd_hoare [RO.o: true ==> true] = r.
  proof strict.
  by intros=> r_def; fun; wp; rnd (cpTrue); wp.
  qed.

  lemma lossless_o:
    mu dsample cpTrue = 1%r => islossless RO.o.
  proof strict.
  by intros=> Hd; apply (termination_o 1%r).
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

  op dsample: to distr.

  clone import Types with
    type from <- from,
    type to <- to,
    op dsample <- dsample.

  module RO: Oracle = {
    var m:(from,to) map

    fun init(): unit = {
      var work:from set;
      var f:from;
      var t:to;

      m = Map.empty;
      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        t = $dsample;
        m.[f] = t;
        work = rm f work;
      }
    }

    fun o(x:from): to = {
      return proj m.[x];
    }
  }.

  lemma lossless_init:
    finite univ<:from> =>
    mu dsample cpTrue = 1%r =>
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

  op dsample: to distr.

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

  section.
  (* Proof note: We may be missing losslessness assumptions on D *)
  declare module D:Dist {Lazy.RO,Eager.RO}.

  local module IND_Lazy = {
    module H:Oracle = {
      var m:(from, to) map

      fun init():unit = {
        m = Map.empty;
      }
  
      fun o(x:from):to = {
        var y : to;
        y = $dsample;
        if (!in_dom x m) m.[x] = y;
        return proj (m.[x]);
      }
    }

    module D = D(H)

    fun main(): bool = {
      var b:bool;
      var work:from set;
      var f:from;
      var t:to;

      H.init();
      b = D.distinguish();

      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        t = $dsample;
        H.m.[f] = t;
        work = rm f work;
      }

      return b;
    }
  }.

  local lemma IND_Lazy: mu dsample cpTrue = 1%r =>
    equiv [IND(Lazy.RO,D).main ~ IND_Lazy.main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; fun; seq 2 2: (={b}).
    call (_: Lazy.RO.m{1} = IND_Lazy.H.m{2}); first by fun; eqobs_in.
    by call (_: true ==> Lazy.RO.m{1} = IND_Lazy.H.m{2})=> //;
      first by fun; wp.
    while{2} (true) (card work{2}).
      intros=> &m z; wp; rnd; wp; skip; progress=> //.
        by rewrite card_rm_in ?mem_pick //; smt. (* This should definitely be a lemma in FSet. *)
    by wp; skip; progress=> //; smt.
  qed.

  local module IND_Eager = {
    module H = {
      var m:(from,to) map

      fun o(x:from): to = {
        var y : to;
        y = $dsample;
        if (!in_dom x m) m.[x] = y;
        return proj (m.[x]);
      }
    }

    module D = D(H)

    fun main(): bool = {
      var b:bool;
      var work:from set;
      var f:from;
      var t:to;

      H.m = Map.empty;
      work = toFSet univ;
      while (work <> FSet.empty)
      {
        f = pick work;
        t = $dsample;
        H.m.[f] = t;
        work = rm f work;
      }

      b = D.distinguish();

      return b;
    }
  }.

  local lemma eager_aux: mu dsample cpTrue = 1%r =>
    equiv [IND_Lazy.main ~ IND_Eager.main: true ==> ={res}].
  proof strict.
  (* by eager *)
  admit.
  qed.

  local lemma IND_Eager: mu dsample cpTrue = 1%r =>
    equiv [IND_Eager.main ~ IND(Eager.RO,D).main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; fun.
  call (_: (forall x, in_dom x IND_Eager.H.m{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
    fun; rcondf{1} 2; first by intros=> _; rnd; skip; smt.
         by rnd{1}; skip; smt.
  inline RO.init.
    while (={work} /\ (forall x, !in_dom x IND_Eager.H.m{1} => mem x work{1}) /\ IND_Eager.H.m{1} = Eager.RO.m{2}).
      wp; rnd; wp; skip; progress=> //.
        rewrite mem_rm andC (_: forall a b, a /\ b <=> a && b) //; split.
          by generalize H5; apply absurd=> //= ->; rewrite in_dom_set; right.
          by intros=> x_neq_pick; apply H; generalize H5; apply absurd=> //= x_in_m; rewrite in_dom_set; left.
    wp; skip; smt.
  qed.

  lemma eagerRO: mu dsample cpTrue = 1%r =>
    equiv [IND(Lazy.RO,D).main ~ IND(Eager.RO,D).main: true ==> ={res}].
  proof strict.
  intros=> dsampleL; bypr (res{1}) (res{2})=> //; intros=> a &1 &2 _.
  apply (eq_trans _ Pr[IND_Lazy.main() @ &1: a = res]);
    first by equiv_deno (IND_Lazy _).
  apply (eq_trans _ Pr[IND_Eager.main() @ &1: a = res]);
    first by equiv_deno (eager_aux _).
  by equiv_deno (IND_Eager _).
  qed.
  end section.
end LazyEager.

theory Wrappers.
          import Types.
  (** Budget-tracking wrapper *)
  require import FSet.
  module Count(H:Oracle) = {
    var qs:from set

    fun init(): unit = {
      H.init();
      qs = FSet.empty;
    }

    fun o(x:from): to = {
      var r:to;
      qs = add x qs;
      r = H.o(x);
      return r;
    }

    fun queries(): int = {
      return card qs;
    }
  }.

  (** Query-tracking wrapper *)
  require import Int.
  module Index(H:Oracle) = {
    var qs:(int,from) map
    var qc:int

    fun init(): unit = {
      H.init();
      qs = Map.empty;
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

  (** Query-numbering wrapper *)
  module Number(H:Oracle) = {
    var qs:(from,int) map
    var qc:int

    fun init(): unit = {
      H.init();
      qs = Map.empty;
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
