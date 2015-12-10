(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int.
require import Real.
require import FSet.
require import Finite.
require import Pair.
require import Distr.
require import OldMonoid.
require Means.

type input.
type output.
type inleaks.
type outleaks.
type outputA.

(* -------------------------------------------------------------------- *)
(* Wrappers for counting *)

module Count = { 
  var c : int
  proc init () : unit = {
    c <- 0;
  }
  proc incr () : unit = {
    c <- c + 1;
  }
}.

module type Adv = {
  proc main() : outputA
}.

module AdvCount (A : Adv) = {
  proc main() : outputA = {
    var r : outputA;
    Count.init();
    r <@ A.main();
    return r;
  }
}.

module type Orcl = { 
  proc orcl(m : input) : output
}.

module OrclCount (O : Orcl) = {
  proc orcl(m : input) : output = {
    var r : output;
    r <@ O.orcl(m);
    Count.incr();
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
(* Hybrid oracles and games *)

op q : { int | 0 < q } as q_pos.

module type AdvOrcl (O : Orcl) = {
  proc main () : outputA 
}.

module type Orclb = {
  proc leaks (il : inleaks) : outleaks  
  proc orclL (m : input) : output
  proc orclR (m : input) : output
}.

module L (Ob : Orclb) : Orcl = {
  proc orcl = Ob.orclL
}.

module R (Ob : Orclb) : Orcl = {
  proc orcl = Ob.orclR
}.

module type AdvOrclb (Ob : Orclb, O : Orcl) = {
  proc main () : outputA
}.

module Orcln (A : AdvOrcl, O : Orcl) = AdvCount(A(OrclCount(O))). 

module Ln(Ob : Orclb, A : AdvOrclb) = Orcln(A(Ob), L(Ob)).

module Rn(Ob : Orclb, A : AdvOrclb) = Orcln(A(Ob), R(Ob)).

(* Hybrid oracle:
   Use left oracle for queries < l0,
   oracle O for queries = l0, and
   right oracle for queries > l0. *)
module HybOrcl (Ob : Orclb, O : Orcl) = {
  var l, l0 : int  
  proc orcl(m:input):output = {
    var r : output;
    if   (l0 < l) r <@ Ob.orclL(m);
    elif (l0 = l) r <@ O.orcl(m);
    else          r <@ Ob.orclR(m);
    l <- l + 1;
    return r;
  }
}.

(* Hybrid game: Adversary has access to
   leaks, left, right, and hybrid oracle *)
module HybGame(A:AdvOrclb, Ob:Orclb, O:Orcl) = {
  module LR = HybOrcl(Ob,O)
  module A = A(Ob,LR)
  proc main() : outputA = {
    var r : outputA;
    HybOrcl.l0 <$ [0..q-1];
    HybOrcl.l  <- 0;
    r <@ A.main();
    return r;
  }
}.

clone import Means as M with
  type input <- int,
  type output <- outputA,
  op d <- [0..q-1].

(* -------------------------------------------------------------------- *)
(* Prove that it is equivalent to consider n or 1 calls to the oracle *)
section.

  declare module Ob : Orclb    {Count,HybOrcl}.
  declare module A  : AdvOrclb {Count,HybOrcl,Ob}.

  (* Hybrid game where index is fixed, not sampled *)
  local module HybGameFixed (O : Orcl) = {
    module LR = HybOrcl(Ob,O)
    module A = A(Ob,LR)
    proc work(x : int) : outputA = {
      var r : outputA;
      HybOrcl.l <- 0; HybOrcl.l0 <- x;
      r <@ A.main();
      return r;
    }
  }.

  local equiv Obleaks : Ob.leaks ~ Ob.leaks : ={il,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local equiv Oborcl1 : Ob.orclL ~ Ob.orclL : ={m,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local equiv Oborcl2 : Ob.orclR ~ Ob.orclR : ={m,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local lemma GLB_WL &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    Pr[Ln(Ob,HybGame(A)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1] = 
    Pr[Rand(HybGameFixed(L(Ob))).main() @ &m : p (glob A) (glob Ob) HybOrcl.l (snd res)].
  proof.
    byequiv (_ : ={glob A, glob Ob} ==> 
                    ={glob A, glob Ob,glob HybOrcl} /\ res{1} = snd res{2} /\ 
                    Count.c{1} <= 1) => //;proc. 
    inline{1} HybGame(A, Ob, OrclCount(L(Ob))).main; inline{2} HybGameFixed(L(Ob)).work;wp.
    call (_: ={glob Ob, glob HybOrcl} /\ Count.c{1} = (HybOrcl.l0{1} < HybOrcl.l{1}) ? 1 : 0).
      proc;wp.
      if => //;first by call Oborcl1;skip;progress => //; smt.
      if => //.
        inline{1} OrclCount(L(Ob)).orcl Count.incr.
        by wp;call Oborcl1;wp;skip;progress => //;smt.
      by call Oborcl2;skip;progress => //; smt.
      by conseq Obleaks.
      by conseq Oborcl1.
      by conseq Oborcl2.
    swap{1} 1 2;inline{1} Count.init.
    by wp;rnd;wp;skip;progress => //;smt.
  qed.

  local lemma GRB_WR &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    Pr[Rn(Ob,HybGame(A)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1] =
    Pr[Rand(HybGameFixed(R(Ob))).main() @ &m : p (glob A) (glob Ob) HybOrcl.l (snd res)].
  proof.
    byequiv (_ : ={glob A, glob Ob} ==> 
                    ={glob A, glob Ob, glob HybOrcl} /\ res{1} = snd res{2} /\ 
                    Count.c{1} <= 1) => //;proc.
    inline{1} HybGame(A, Ob, OrclCount(R(Ob))).main; inline{2} HybGameFixed(R(Ob)).work;wp.
    call (_: ={glob Ob, glob HybGame} /\ Count.c{1} = (HybOrcl.l0{1} < HybOrcl.l{1}) ? 1 : 0).
      proc;wp.
      if => //;first by call Oborcl1;skip;progress => //; smt.
      if => //.
        inline{1} OrclCount(R(Ob)).orcl Count.incr.
        by wp;call Oborcl2;wp;skip;progress => //;smt.
      by call Oborcl2;skip;progress => //; smt.
      by conseq Obleaks.
      by conseq Oborcl1.
      by conseq Oborcl2.
    swap{1} 1 2;inline{1} Count.init.
    by wp;rnd;wp;skip;progress => //;smt.
  qed.

  axiom losslessL: islossless Ob.leaks.
  axiom losslessOb1: islossless Ob.orclL.
  axiom losslessOb2: islossless Ob.orclR.
  axiom losslessA (Ob0 <: Orclb{A}) (LR <: Orcl{A}):
    islossless LR.orcl => 
    islossless Ob0.leaks => islossless Ob0.orclL => islossless Ob0.orclR =>
    islossless A(Ob0, LR).main.

  local lemma WL0_GLA &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
    Pr[HybGameFixed(L(Ob)).work(0) @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q] = 
    Pr[Ln(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res /\ Count.c <= q ].
  proof.
    byequiv (_ : ={glob A, glob Ob} /\ x{1}=0 ==> 
                    (HybOrcl.l{1} <= q) = (Count.c{2} <= q) /\
                    (Count.c{2} <= q =>
                      ={glob A, glob Ob,res} /\ HybOrcl.l{1} = Count.c{2})) => //;
     [proc | smt].
    call (_: q < Count.c,
             ={glob Ob} /\ HybOrcl.l0{1} = 0 /\ HybOrcl.l{1} = Count.c{2} /\ 0 <= HybOrcl.l{1},
             HybOrcl.l0{1} = 0 /\ q < HybOrcl.l{1}).
      by apply losslessA.
      proc;inline{2} Count.incr;wp.
      if{1};first by call Oborcl1;wp;skip;progress => //;smt.
      rcondt{1} 1; first by move=> &m0;skip;smt.
      by wp;call Oborcl1;wp;skip;progress => //;smt.
      move=> &m2 _;proc.
      rcondt 1; first by skip;smt.
      by wp;call losslessOb1;skip;smt.
      by move=> &m1;proc;inline Count.incr;wp;call losslessOb1;wp;skip;smt.
      by conseq Obleaks.
      move=> &m2 _;conseq losslessL.
      move=> &m1; conseq losslessL.

      by conseq Oborcl1.
      move=> &m2 _;conseq losslessOb1.
      move=> &m1; conseq losslessOb1.

      by conseq Oborcl2.
      move=> &m2 _;conseq losslessOb2.
      move=> &m1; conseq losslessOb2.

    by inline{2} Count.init;wp;skip;smt.
  qed.

  local lemma WRq_GRA &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
    Pr[HybGameFixed(R(Ob)).work((q-1)) @ &m :  p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q] = 
    Pr[Rn(Ob,A).main() @ &m :  p (glob A) (glob Ob) Count.c res /\ Count.c <= q ].
  proof.
    byequiv (_ : ={glob A, glob Ob} /\ x{1}=q-1 ==> 
                    (HybOrcl.l{1} <= q) = (Count.c{2} <= q) /\
                    (Count.c{2} <= q =>
                      ={glob A, glob Ob, res} /\ HybOrcl.l{1} = Count.c{2})) => //;
    [proc | smt].
    call (_: q < Count.c,
             ={glob Ob} /\ HybOrcl.l0{1} = q-1 /\ HybOrcl.l{1} = Count.c{2} /\ 0 <= HybOrcl.l{1},
             HybOrcl.l0{1} = q-1 /\ q < HybOrcl.l{1}).
      by apply losslessA.

      proc;inline{2} Count.incr;wp.
      if{1};first by call{1} losslessOb1;call{2} losslessOb2;wp;skip; smt.
      if{1};
        first by wp;call Oborcl2;wp;skip;progress => //;smt.
      by call Oborcl2;wp;skip;progress => //;smt.
      move=> &m2 _;proc.
      rcondt 1; first by skip;smt.
      by wp;call losslessOb1;skip; smt.
      move=> &m1;proc;inline Count.incr;wp;call losslessOb2;wp;skip;smt.

      by conseq Obleaks.
      move=> &m2 _;conseq losslessL.
      move=> &m1; conseq losslessL.

      by conseq Oborcl1.
      move=> &m2 _;conseq losslessOb1.
      move=> &m1; conseq losslessOb1.

      by conseq Oborcl2.
      move=> &m2 _;conseq losslessOb2.
      move=> &m1; conseq losslessOb2.

    by inline{2} Count.init;wp;skip;smt.
  qed.

  local lemma WLR_shift &m v (p:glob A -> glob Ob -> int -> outputA -> bool): 
    1 <= v <= q-1 => 
    Pr[HybGameFixed(L(Ob)).work(v) @ &m: p (glob A) (glob Ob) HybOrcl.l res] = 
    Pr[HybGameFixed(R(Ob)).work((v-1)) @ &m : p (glob A) (glob Ob) HybOrcl.l res].
  proof.
    move=> Hv;byequiv (_: ={glob A,glob Ob} /\ x{1} = v /\ x{2} = v-1 ==> 
                             ={glob A,glob Ob, HybOrcl.l, res}) => //.
    proc.
    call (_: ={glob Ob, HybOrcl.l} /\ HybOrcl.l0{1} = v /\ HybOrcl.l0{2} = v-1).
      proc.
      if{1}; first by rcondt{2} 1;[move=> &m0;skip;smt | wp;call Oborcl1].
      if{1};first by rcondt{2} 1;
       [move=> &m0;skip;smt | wp;call Oborcl1;wp].
      rcondf{2} 1;first by move=> &m0;skip;smt.
      by if{2};wp;call Oborcl2;wp.
      by conseq Obleaks.
      by conseq Oborcl1.
      by conseq Oborcl2.
    by wp.
  qed.

  (* TODO : move this *)
  lemma Mrplus_inter_shift (i j k:int) f: 
      Mrplus.sum f (oflist (List.Iota.iota_ i (j - i + 1))) = 
      Mrplus.sum (fun l, f (l + k)) (oflist (List.Iota.iota_ (i-k) (j - i + 1))).
  proof strict.
    rewrite (Mrplus.sum_chind f (fun l, l - k) (fun l, l + k)) /=;first smt.
    congr => //.   
    apply FSet.fsetP => x.
    rewrite imageP !mem_oflist !List.Iota.mem_iota; split.
      move=> [y];rewrite !mem_oflist !List.Iota.mem_iota;smt.
    move=> Hx;exists (x+k);rewrite !mem_oflist !List.Iota.mem_iota;smt.
  qed.

  lemma Hybrid &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    let p' = fun ga ge l r, p ga ge l r /\ l <= q in
    Pr[Ln(Ob,HybGame(A)).main() @ &m : p' (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1] - 
      Pr[Rn(Ob,HybGame(A)).main() @ &m : p' (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1] =
    1%r/q%r * (
      Pr[Ln(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res] - 
        Pr[Rn(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res]).
  proof.
    move=> p';rewrite (GLB_WL &m p') (GRB_WR &m p').
    simplify p'; rewrite -(WL0_GLA &m p) -(WRq_GRA &m p).
    cut Hint : forall x, support [0..q - 1] x <=> mem (oflist (List.Iota.iota_ 0 q)) x.
      by move=> x; rewrite !mem_oflist !List.Iota.mem_iota /support Dinter.supp_def; smt.
    cut Hfin: is_finite (support [0..q - 1]).
      by exists (List.Iota.iota_ 0 q); smt.
    cut Huni : forall (x : int), in_supp x [0..q - 1] => mu_x [0..q - 1] x = 1%r / q%r.
      by move=> x Hx;rewrite Dinter.mu_x_def_in //;smt.
    pose ev := 
      fun (_j:int) (g:glob HybGameFixed(L(Ob))) (r:outputA),
        let (l,l0,ga,ge) = g in p ga ge l r /\ l <= q.
    cut := M.Mean_uni (HybGameFixed(L(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
    cut := M.Mean_uni (HybGameFixed(R(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
    cut -> : oflist (to_seq (support [0..q - 1])) = oflist (List.Iota.iota_ 0 q).
      by apply FSet.fsetP => x; rewrite !mem_oflist mem_to_seq// smt.
    (* BUG type are not normalized in ev => assert failure in ecWhy *)      
    clear ev.
    cut {1}->: oflist (List.Iota.iota_ 0 q) = oflist (List.Iota.iota_ 1 (q - 1)) `|` fset1 0.
      by apply/fsetP=> x; rewrite !inE !mem_oflist !List.Iota.mem_iota; smt.
    cut ->: oflist (List.Iota.iota_ 0 q) = oflist (List.Iota.iota_ 0 (q - 1)) `|` fset1 (q - 1).
      by apply/fsetP=> x; rewrite !inE !mem_oflist !List.Iota.mem_iota; smt.
    rewrite Mrplus.sum_add /=.
      by rewrite mem_oflist List.Iota.mem_iota.
    rewrite Mrplus.sum_add /=.
      by rewrite mem_oflist List.Iota.mem_iota.
    cut Hq : q%r <> 0%r by smt.
    fieldeq => //.
    cut ->: q - 1 = q - 1 - 1 - 0 + 1 by smt.
    rewrite (Mrplus_inter_shift 0 (q - 1 - 1) (-1)) /=.
    have ->: q - 1 - 1 + 1 = q - 1 by smt.
    rewrite -(Mrplus.sum_comp (( * ) (-q%r))) 1..2:smt.
    rewrite -(Mrplus.sum_comp (( * ) (q%r))) 1..2:smt.
    rewrite Mrplus.sum_add2 /=.
    rewrite (Mrplus.NatMul.sum_const 0%r) /Mrplus.NatMul.( * ) //=.
    move=> x; rewrite mem_oflist List.Iota.mem_iota=> Hx.
    cut:= WLR_shift &m x p' _; 1:smt. simplify p'=> ->.
    by smt.
  qed.

end section.

(* -------------------------------------------------------------------- *)
(* Simplified variant: Assume that A calls the oracle at most q times. *)
section.
  declare module Ob : Orclb    {Count,HybOrcl}.
  declare module A  : AdvOrclb {Count,HybOrcl,Ob}.

  axiom A_call : forall (O<:Orcl{Count,A}), hoare [ Orcln(A(Ob), O).main : true ==> Count.c <= q ].

  local module Al = Orcln(A(Ob),HybOrcl(Ob,L(Ob))).

  local module Bl = {
    proc main() : outputA = {
      var r : outputA;
      HybOrcl.l0 <$ [0..q-1];
      HybOrcl.l  <- 0;
      r <@ Al.main();
      return r;
    }
  }.

  local module Ar = Orcln(A(Ob),HybOrcl(Ob,R(Ob))).

  local module Br = {
    proc main() : outputA = {
      var r : outputA;
      HybOrcl.l0 <$ [0..q-1];
      HybOrcl.l  <- 0;
      r <@ Ar.main();
      return r;
    }
  }.

  local equiv B_Bl : HybGame(A,Ob,L(Ob)).main ~ Bl.main :
     ={glob A, glob Ob} ==>
     ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} = HybOrcl.l{2} /\ Count.c{2} <= q.
  proof.
    conseq [-frame] (_:  ={glob A, glob Ob} ==>  ={glob A, glob Ob, glob HybOrcl, res}) _ 
           (_:true ==> Count.c = HybOrcl.l /\ Count.c <= q).
     conseq [-frame] (_:true ==> Count.c = HybOrcl.l) (_: true ==> Count.c <= q).
       proc; call (A_call (<:HybOrcl(Ob,L(Ob)))) => //.
     proc;inline *;wp;call (_ : Count.c = HybOrcl.l).
     proc;inline *;wp; by conseq (_: _ ==> true) => //.
     conseq (_: _ ==> true) => //. conseq (_: _ ==> true) => //. conseq (_: _ ==> true) => //. 
     by wp.
    proc;inline Al.main;wp. call (_: ={glob Ob, glob HybOrcl}).
    proc;inline *;wp. sp;if => //. call (_:true) => //.
      if => //. wp;call (_:true) => //. wp=> //. call (_:true) => //.
    proc (={glob HybOrcl}) => //. proc (={glob HybOrcl}) => //. proc (={glob HybOrcl}) => //.
    inline *;wp;rnd => //.
  qed.

  local equiv B_Br : HybGame(A,Ob,R(Ob)).main ~ Br.main :
     ={glob A, glob Ob} ==>
     ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} = HybOrcl.l{2} /\ Count.c{2} <= q.
  proof.
    conseq [-frame] (_:  ={glob A, glob Ob} ==>  ={glob A, glob Ob, glob HybOrcl, res}) _ 
           (_:true ==> Count.c = HybOrcl.l /\ Count.c <= q).
     conseq [-frame] (_:true ==> Count.c = HybOrcl.l) (_: true ==> Count.c <= q).
       proc; call (A_call (<:HybOrcl(Ob,R(Ob)))) => //.
     proc;inline *;wp;call (_ : Count.c = HybOrcl.l).
     proc;inline *;wp; by conseq (_: _ ==> true) => //.
     conseq (_: _ ==> true) => //. conseq (_: _ ==> true) => //. conseq (_: _ ==> true) => //. 
     by wp.
    proc;inline Ar.main;wp. call (_: ={glob Ob, glob HybOrcl}).
    proc;inline *;wp. sp;if => //. call (_:true) => //.
      if => //. wp;call (_:true) => //. wp=> //. call (_:true) => //.
    proc (={glob HybOrcl}) => //. proc (={glob HybOrcl}) => //. proc (={glob HybOrcl}) => //.
    inline *;wp;rnd => //.
  qed.

  local lemma Pr_Bl &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
     Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] =
     Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  proof.
    cut -> : 
       Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] =
       Pr[Bl.main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
      byequiv B_Bl => //.
    apply eq_sym.  byequiv B_Bl => //.   
  qed.

  local lemma Pr_Br &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
     Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] =
     Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  proof.
    cut -> : 
       Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] =
       Pr[Br.main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
      byequiv B_Br => //.
    apply eq_sym.  byequiv B_Br => //.   
  qed.

  axiom losslessL: islossless Ob.leaks.
  axiom losslessOb1: islossless Ob.orclL. 
  axiom losslessOb2: islossless Ob.orclR.
  axiom losslessA (Ob0 <: Orclb{A}) (LR <: Orcl{A}):
    islossless LR.orcl => 
    islossless Ob0.leaks => islossless Ob0.orclL => islossless Ob0.orclR =>
    islossless A(Ob0, LR).main.

  lemma Hybrid_restr &m (p:glob A -> glob Ob -> int -> outputA -> bool):
      Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] -
      Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res] =
      1%r/q%r * (
         Pr[Ln(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res] - 
         Pr[Rn(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res]).
   proof.
     pose p' := fun ga ge l r, p ga ge l r /\ l <= q.
     cut -> : Pr[Ln(Ob,A).main() @ &m : p  (glob A) (glob Ob) Count.c res] =
              Pr[Ln(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res].
       byequiv (_ : ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res} /\ Count.c{1} <= q) => //;
         last by rewrite /p'.
       conseq [-frame] (_:  ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res}) (_ : true ==> Count.c <= q);
         last by sim;  proc (={Count.c}).
       apply (A_call (<:L(Ob))).
     cut -> : Pr[Rn(Ob,A).main() @ &m : p  (glob A) (glob Ob) Count.c res] =
              Pr[Rn(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res].
       byequiv (_ : ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res} /\ Count.c{1} <= q) => //;
         last by rewrite /p'.
       conseq [-frame] (_:  ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res}) (_ : true ==> Count.c <= q);
         last by sim;  proc (={Count.c}).
       apply (A_call (<:R(Ob))).
     rewrite (Pr_Bl &m p) (Pr_Br &m p).
     cut := Hybrid Ob A _ _ _ _ &m p. 
      apply losslessL. apply losslessOb1. apply losslessOb2. apply losslessA.
     move=> /= H. rewrite /p' -H.
     congr; last congr.
     byequiv (_ : ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} <= 1) => //.
       proc;inline *;wp.
       call (_ : ={glob Ob, glob HybOrcl} /\ (if HybOrcl.l <= HybOrcl.l0 then Count.c = 0 else Count.c =1){2}). 
        proc. inline *;wp. 
        if => //. call (_: ={glob HybOrcl});auto; smt.
        if => //. wp;call (_: ={glob HybOrcl});auto; smt. call (_: ={glob HybOrcl});auto; smt.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       auto;progress;smt.
     byequiv (_ : ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} <= 1) => //.
       proc;inline *;wp.
       call (_ : ={glob Ob, glob HybOrcl} /\ (if HybOrcl.l <= HybOrcl.l0 then Count.c = 0 else Count.c =1){2}). 
        proc. inline *;wp. 
        if => //. call (_: ={glob HybOrcl});auto; smt.
        if => //. wp;call (_: ={glob HybOrcl});auto; smt. call (_: ={glob HybOrcl});auto; smt.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       conseq (_: _ ==> ={res,glob Ob}) => //. sim.
       auto;progress;smt.
    qed.

end section.
