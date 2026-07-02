(* GlobalHybridExamp2.ec *)

(* We use theories/crypto/GlobalHybrid.ec for an example involving the
   Decisional Diffie-Hellman (DDH) assumption, expressing security
   as an equality. *)

require import AllCore Real Distr DBool StdOrder StdBigop.
require import FMap PROM.
import RealOrder Bigreal BRA.
require GlobalHybrid TotalProb.

theory DDH.

type input.  (* additional input *)

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)
op kid  : key.                (* identity *)
op kinv : key -> key.         (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).
axiom kid_l (x : key)     : kid ^^ x = x.
axiom kid_r (x : key)     : x ^^ kid = x.
axiom kinv_l (x : key)    : kinv x ^^ x = kid.
axiom kinv_r (x : key)    : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e     : exp.  (* some exponent *)
op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp)   : q * r = r * q.
axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op [full uniform lossless] dexp : exp distr.

op g   : key.  (* generator *)
op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* DDH Adversary *)

module type DDH_ADV = {
  proc main(i : input, k1 k2 k3 : key) : bool
}.

(* the real DDH game *)

module DDH1 (Adv : DDH_ADV) = {
  proc main(i : input) : bool = {
    var b : bool; var q1, q2 : exp;
    q1 <$ dexp; q2 <$ dexp;
    b <@ Adv.main(i, g ^ q1, g ^ q2, g ^ (q1 * q2));
    return b;
  }
}.

(* the ideal DDH game *)

module DDH2 (Adv : DDH_ADV) = {
  proc main(i : input) : bool = {
    var b : bool; var q1, q2, q3 : exp;
    q1 <$ dexp; q2 <$ dexp; q3 <$ dexp;
    b <@ Adv.main(i, g ^ q1, g ^ q2 , g ^ q3);
    return b;
  }
}.

end DDH.

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)
op kid  : key.                (* identity *)
op kinv : key -> key.         (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).
axiom kid_l (x : key)     : kid ^^ x = x.
axiom kid_r (x : key)     : x ^^ kid = x.
axiom kinv_l (x : key)    : kinv x ^^ x = kid.
axiom kinv_r (x : key)    : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e     : exp.  (* some exponent *)
op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp)   : q * r = r * q.
axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op [full uniform lossless] dexp : exp distr.

op g   : key.  (* generator *)
op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

clone import DDH as DDH' with
  type input <- unit * int,  (* note *)
  type key   <- key,
  type exp   <- exp,
  op (^^)    <- (^^),
  op kid     <- kid,
  op kinv    <- kinv,
  op e       <- e,
  op ( * )   <- ( * ),
  op dexp    <- dexp,
  op g       <- g,
  op (^)     <- (^)
proof *.
realize kmulA. apply kmulA. qed.
realize kid_l. apply kid_l. qed.
realize kid_r. apply kid_r. qed.
realize kinv_l. apply kinv_l. qed.
realize kinv_r. apply kinv_r. qed.
realize mulC. apply mulC. qed.
realize mulA. apply mulA. qed.
realize dexp_ll. apply dexp_ll. qed.
realize dexp_uni. apply dexp_uni. qed.
realize dexp_fu. apply dexp_fu. qed.
realize double_exp_gen. apply double_exp_gen. qed.

(* the real and ideal games let an adversary call an oracle
   m times before the returned results return a default value *)

op m : { int | 1 <= m } as ge1_m.

module type OR = {
  proc init() : unit
  proc get()  : key * key * key
}.

(* the real oracle *)

module OrReal : OR = {
  var ctr : int
  var x, y : exp

  proc init() : unit = { ctr <- 1; }

  proc get() : key * key * key = {
    var r : key * key * key;
    if (ctr <= m) {
      x <$ dexp; y <$ dexp;
      r <- (g ^ x, g ^ y, g ^ (x * y));
      ctr <- ctr + 1;
    }
    else { r <- witness; }
    return r;
  }
}.

(* the ideal oracle *)

module OrIdeal : OR = {
  var ctr : int

  proc init() : unit = { ctr <- 1; }

  proc get() : key * key * key = {
    var r : key * key * key;
    var x, y, z : exp;
    if (ctr <= m) {
      x <$ dexp; y <$ dexp; z <$ dexp;
      r <- (g ^ x, g ^ y, g ^ z);
      ctr <- ctr + 1;
    }
    else { r <- witness; }
    return r;
  }
}.

(* an adversary can only call the oracle's get procedure *)

module type ADV(Or : OR) = {
  proc disting() : bool {Or.get}
}.

(* the real game *)

module GReal(Adv : ADV) = {
  proc main() : bool = {
    var b : bool;
    OrReal.init();
    b <@ Adv(OrReal).disting();
    return b;
  }
}.

(* the ideal game *)

module GIdeal(Adv : ADV) = {
  proc main() : bool = {
    var b : bool;
    OrIdeal.init();
    b <@ Adv(OrIdeal).disting();
    return b;
  }
}.

(* our reduction to DDH *)

module Reduct(Adv : ADV) : DDH_ADV = {
  var i : int
  var u, v, w : key

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr <= m) {
        if (ctr < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr = i) { r <- (u, v, w); }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else { r <- witness; }
      return r;
    }
  }

  proc main(i' : unit * int, u' : key, v' : key, w' : key) : bool = {
    var b : bool; var x : unit;
    Or.ctr <- 1;
    i <- i'.`2; u <- u'; v <- v'; w <- w';
    b <@ Adv(Or).disting();
    return b;
  }
}.

clone TotalProb.TotalRange as TR with
  type input <- unit
proof *.

(* We will prove security with an exact upper bound:

lemma GReal_GIdeal1 (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  m%r *
  `|Pr[TR.Rand(DDH1(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res] -
    Pr[TR.Rand(DDH2(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res]|.
proof. by apply (GReal_GIdeal1_sect Adv). qed.

   or equivalently

lemma GReal_GIdeal2 (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  `|bigi predT
    (fun (i : int) =>
       Pr[DDH1(Reduct(Adv)).main((), i) @ &m : res] -
       Pr[DDH2(Reduct(Adv)).main((), i) @ &m : res])
    1 (m + 1)|.
*)

section.

local clone GlobalHybrid as GH with
  type input <- unit
proof *.

local clone GH.Param as GHP with
  type or_input  <- unit,
  type or_output <- key * key * key
proof *.

declare module Adv <: ADV{-OrReal, -OrIdeal, -Reduct}.

local module DDHOr1 : GHP.OR = {  (* real *)
  proc init() : unit = { }

  proc f() : key * key * key = {
    var x, y : exp;
    x <$ dexp; y <$ dexp;
    return (g ^ x, g ^ y, g ^ (x * y));
  }
}.

local module DDHOr2 : GHP.OR = {  (* ideal *)
  proc init() : unit = { }

  proc f() : key * key * key = {
    var x, y, z : exp;
    x <$ dexp; y <$ dexp; z <$ dexp;
    return (g ^ x, g ^ y, g ^ z);
  }
}.

local module (Hybrid : GHP.HYBRID_PARAM) (GHOr : GHP.OR) = {
  var i : int

  module Or = {
    var ctr : int

    proc init() : unit = { }

    (* get shifts from ideal to real based on the value of i *)

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr <= m) {
        if (ctr < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;  (* ideal *)
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr = i) { r <@ GHOr.f(); }
        else {
          x <$ dexp; y <$ dexp;  (* real *)
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else { r <- witness; }
      return r;
    }
  }

  (* i' should be between 1 and m + 1 *)

  proc main(x : unit, i' : int) : bool = {
    var b : bool;
    i <- i'; Or.ctr <- 1;
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma GReal_Hybrid &m :
  Pr[GReal(Adv).main() @ &m : res] =
  Pr[GHP.Exper(Hybrid, DDHOr1).main((), 1) @ &m : res].
proof.
byequiv => //; proc; inline; wp.
seq 1 4 :
  (={glob Adv} /\ OrReal.ctr{1} = Hybrid.Or.ctr{2} /\
   OrReal.ctr{1} = 1 /\ Hybrid.i{2} = 1); first auto.
call
  (:
   OrReal.ctr{1} = Hybrid.Or.ctr{2} /\
   1 <= OrReal.ctr{1} <= m + 1 /\ Hybrid.i{2} = 1);
  last auto; smt(ge1_m).
proc; if => //; last auto; smt(ge1_m).
rcondf{2} 1; first auto; smt().
by if{2}; [inline{2} 1; auto; smt() | auto; smt()].
qed.

local lemma Hybrid_GIdeal &m :
  Pr[GHP.Exper(Hybrid, DDHOr1).main((), m + 1) @ &m : res] =
  Pr[GIdeal(Adv).main() @ &m : res].
proof.
byequiv => //; proc; inline; wp.
seq 4 1 :
  (={glob Adv} /\ Hybrid.Or.ctr{1} = OrIdeal.ctr{2} /\
   OrIdeal.ctr{2} = 1 /\ Hybrid.i{1} = m + 1); first auto.
call
  (:
   Hybrid.Or.ctr{1} = OrIdeal.ctr{2} /\
   0 <= OrIdeal.ctr{2} <= m + 1 /\ Hybrid.i{1} = m + 1);
  last auto; smt(ge1_m).
proc; if => //; last auto.
rcondt{1} 1; first auto; smt().
by auto; smt().
qed.

local lemma Hybrid_step (j : int) &m :
  1 <= j <= m =>
  Pr[GHP.Exper(Hybrid, DDHOr2).main((), j) @ &m : res] =
  Pr[GHP.Exper(Hybrid, DDHOr1).main((), j + 1) @ &m : res].
proof.
move => j_rng; byequiv => //; proc; inline; wp.
seq 4 4 :
  (Hybrid.i{1} = j /\ Hybrid.i{2} = j + 1 /\
   Hybrid.Or.ctr{1} = 1 /\ ={glob Adv, Hybrid.Or.ctr});
  first auto.
call
  (:
   ={Hybrid.Or.ctr} /\ Hybrid.i{1} = j /\
   Hybrid.i{2} = j + 1 /\ 1 <= Hybrid.Or.ctr{1} <= m + 1);
  last auto; smt().
proc.
if => //; last auto.
if{1}.
+ rcondt{2} 1; first auto; smt().
  by auto; smt().
if{1}.
+ rcondt{2} 1; first auto; smt().
  by inline{1} 1; auto; smt().
rcondf{2} 1; first auto; smt().
by if{2}; [inline{2} 1; auto; smt() | auto; smt()].
qed.

(* in our sequences of games, we need to shift from lazy to eager
   sampling for two or three exponents, and so we use PROM *)

local type ro_in_t = [A | B | C].  (* three names of exponents *)

local clone FullRO with
  type in_t    <- ro_in_t,
  type out_t   <- exp,
  op dout      <- fun _ => dexp,
  type d_in_t  <- int,
  type d_out_t <- bool
proof *.

(* first, the sequence of games proving:

   1 <= i < m + 1 =>
   Pr[GHP.Exper(Hybrid, DDHOr1).main((), i) @ &m : res] =
   Pr[DDH1(Reduct(Adv)).main((), i) @ &m : res]. *)

local module (RO_Disting1 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  var i : int

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr <= m) {
        if (ctr < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr = i) {
          x <@ RO.get(A); y <@ RO.get(B);
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else { r <- witness; }
      return r;
    }
  }

  proc distinguish(i' : int) : bool = {
    var b : bool;
    i <- i'; Or.ctr <- 1;
    RO.sample(A); RO.sample(B);
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma Hybrid_DDHOr1_MainD_RO_Disting1_RO (i' : int) :
  1 <= i' < m + 1 =>
  equiv
  [GHP.Exper(Hybrid, DDHOr1).main ~
   FullRO.MainD(RO_Disting1, FullRO.RO).distinguish :
   ={glob Adv} /\ i{1} = i' /\ x{2} = i' ==>
   ={res}].
proof.
move => [ge1_i' le_i'_m]; rewrite ltzS in le_i'_m.
transitivity
  FullRO.MainD(RO_Disting1, FullRO.LRO).distinguish
  (={glob Adv} /\ i{1} = i' /\ x{2} = i' ==> ={res})
  (={glob RO_Disting1, x} ==> ={res}) => //; first smt().
+ proc; inline*; wp.
  seq 4 6 :
    (={glob Adv} /\ Hybrid.i{1} = i' /\ RO_Disting1.i{2} = i' /\
     Hybrid.Or.ctr{1} = 1 /\ RO_Disting1.Or.ctr{2} = 1 /\
     FullRO.RO.m{2} = empty); first auto.
  call
    (:
     Hybrid.Or.ctr{1} = RO_Disting1.Or.ctr{2} /\
     1 <= Hybrid.Or.ctr{1} <= m + 1 /\
     Hybrid.i{1} = i' /\ RO_Disting1.i{2} = i' /\
     (Hybrid.Or.ctr{1} <= i' => FullRO.RO.m{2} = empty));
    last auto; smt().
  proc.
  if => //; last auto.
  if => //; first auto; smt().
  if => //; last auto; smt().
  inline*; swap{2} 2 -1; swap{2} 6 -4.
  seq 2 3 :
    (#pre /\ x0{1} = r0{2} /\ y0{1} = r1{2} /\
     x0{2} = A); first auto.
  rcondt{2} 1; first auto; smt(mem_empty).
  sp 0 3.
  rcondt{2} 1; first auto; smt(mem_set mem_empty).
  by auto; smt(get_set_sameE).
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting1 _) => //.
by move => _; apply dexp_ll.
qed.

local lemma MainD_RO_Disting1_RO_DDH1_Reduct (i' : int) :
  1 <= i' < m + 1 =>
  equiv
  [FullRO.MainD(RO_Disting1, FullRO.RO).distinguish ~
   DDH1(Reduct(Adv)).main :
   ={glob Adv} /\ x{1} = i' /\ i{2}.`2 = i' ==>
   ={res}].
proof.
move => [ge1_i' le_i'_m]; rewrite ltzS in le_i'_m.
proc; inline*; wp; swap{1} 7 -6; swap{1} 11 -9.
seq 2 2 : (#pre /\ r0{1} = q1{2} /\ r1{1} = q2{2});
  first auto.
seq 10 9 :
  (={glob Adv} /\
   RO_Disting1.i{1} = i' /\ Reduct.i{2} = i' /\
   RO_Disting1.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1{2} /\
   FullRO.RO.m{1}.[B] = Some q2{2} /\
   Reduct.u{2} = g ^ q1{2} /\
   Reduct.v{2} = g ^ q2{2} /\
   Reduct.w{2} = g ^ (q1{2} * q2{2})).
+ by auto; smt(get_setE mem_set mem_empty).
exlim q1{2}, q2{2} => q1_R q2_R.
call
  (:
   RO_Disting1.i{1} = i' /\
   Reduct.i{2} = i' /\
   RO_Disting1.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1_R /\
   FullRO.RO.m{1}.[B] = Some q2_R /\
   Reduct.u{2} = g ^ q1_R /\
   Reduct.v{2} = g ^ q2_R /\
   Reduct.w{2} = g ^ (q1_R * q2_R)); last auto.
proc.
if => //; last auto.
if => //; first auto; smt().
if => //; last auto.
inline*.
rcondf{1} 3; first auto; smt().
rcondf{1} 6; first auto; smt().
by auto; smt().
qed.

local lemma reduct1 (i' : int) &m :
  1 <= i' < m + 1 =>
  Pr[GHP.Exper(Hybrid, DDHOr1).main((), i') @ &m : res] =
  Pr[DDH1(Reduct(Adv)).main((), i') @ &m : res].
proof.
move => i'_rng.
byequiv
  (: ={glob Adv} /\ i{1} = i' /\ i{2}.`2 = i' ==> _) => //.
transitivity
  FullRO.MainD(RO_Disting1, FullRO.RO).distinguish
  (={glob Adv} /\ i{1} = i' /\ x{2} = i' ==> ={res})
  (={glob Adv} /\ x{1} = i' /\ i{2}.`2 = i' ==> ={res}) => //.
by smt().
by apply Hybrid_DDHOr1_MainD_RO_Disting1_RO.
by apply MainD_RO_Disting1_RO_DDH1_Reduct.
qed.

local module (RO_Disting2 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  var i : int

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr <= m) {
        if (ctr < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr = i) {
          x <@ RO.get(A); y <@ RO.get(B); z <@ RO.get(C);
          r <- (g ^ x, g ^ y, g ^ z);
        }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else { r <- witness; }
      return r;
    }
  }

  proc distinguish(i' : int) : bool = {
    var b : bool;
    i <- i'; Or.ctr <- 1;
    RO.sample(A); RO.sample(B); RO.sample(C);
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma Hybrid_DDHOr2_MainD_RO_Disting2_RO (i' : int) :
  1 <= i' < m + 1 =>
  equiv
  [GHP.Exper(Hybrid, DDHOr2).main ~
   FullRO.MainD(RO_Disting2, FullRO.RO).distinguish :
   ={glob Adv} /\ i{1} = i' /\ x{2} = i' ==>
   ={res}].
proof.
move => [ge1_i' le_i'_m]; rewrite ltzS in le_i'_m.
transitivity
  FullRO.MainD(RO_Disting2, FullRO.LRO).distinguish
  (={glob Adv} /\ i{1} = i' /\ x{2} = i' ==> ={res})
  (={glob RO_Disting2, x} ==> ={res}) => //; first smt().
+ proc; inline*; wp.
  seq 4 7 :
    (={glob Adv} /\ Hybrid.i{1} = i' /\ RO_Disting2.i{2} = i' /\
     Hybrid.Or.ctr{1} = 1 /\ RO_Disting2.Or.ctr{2} = 1 /\
     FullRO.RO.m{2} = empty); first auto.
  call
    (:
     Hybrid.Or.ctr{1} = RO_Disting2.Or.ctr{2} /\
     1 <= Hybrid.Or.ctr{1} <= m + 1 /\
     Hybrid.i{1} = i' /\ RO_Disting2.i{2} = i' /\
     (Hybrid.Or.ctr{1} <= i' => FullRO.RO.m{2} = empty));
    last auto; smt().
  proc.
  if => //; last auto.
  if => //; first auto; smt().
  if => //; last auto; smt().
  inline*; swap{2} 2 -1; swap{2} 6 -4; swap{2} 10 -7.
  seq 3 4 :
    (#pre /\ x0{1} = r0{2} /\ y0{1} = r1{2} /\
     z0{1} = r2{2} /\ x0{2} = A); first auto.
  rcondt{2} 1; first auto; smt(mem_empty).
  sp 0 3.
  rcondt{2} 1; first auto; smt(mem_set mem_empty).
  sp 0 3.
  rcondt{2} 1; first auto; smt(mem_set mem_empty).
  auto; smt(get_set_sameE).
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting2 _) => //.
by move => _; apply dexp_ll.
qed.

local lemma MainD_RO_Disting2_RO_DDH2_Reduct (i' : int) :
  1 <= i' < m + 1 =>
  equiv
  [FullRO.MainD(RO_Disting2, FullRO.RO).distinguish ~
   DDH2(Reduct(Adv)).main :
   ={glob Adv} /\ x{1} = i' /\ i{2}.`2 = i' ==>
   ={res}].
proof.
move => [ge1_i' le_i'_m]; rewrite ltzS in le_i'_m.
proc; inline*; wp; swap{1} 7 -6; swap{1} 11 -9; swap{1} 15 -12.
seq 3 3 :
  (#pre /\ r0{1} = q1{2} /\ r1{1} = q2{2} /\
   r2{1} = q3{2}); first auto.
seq 13 9 :
  (={glob Adv} /\
   RO_Disting2.i{1} = i' /\ Reduct.i{2} = i' /\
   RO_Disting2.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1{2} /\
   FullRO.RO.m{1}.[B] = Some q2{2} /\
   FullRO.RO.m{1}.[C] = Some q3{2} /\
   Reduct.u{2} = g ^ q1{2} /\
   Reduct.v{2} = g ^ q2{2} /\
   Reduct.w{2} = g ^ q3{2}).
+ auto; smt(get_setE mem_set mem_empty).
exlim q1{2}, q2{2}, q3{2} => q1_R q2_R q3_R.
call
  (:
   RO_Disting2.i{1} = i' /\
   Reduct.i{2} = i' /\
   RO_Disting2.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1_R /\
   FullRO.RO.m{1}.[B] = Some q2_R /\
   FullRO.RO.m{1}.[C] = Some q3_R /\
   Reduct.u{2} = g ^ q1_R /\
   Reduct.v{2} = g ^ q2_R /\
   Reduct.w{2} = g ^ q3_R); last auto.
proc.
if => //; last auto.
if => //; first auto; smt().
if => //; last auto.
inline*.
rcondf{1} 3; first auto; smt().
rcondf{1} 6; first auto; smt().
rcondf{1} 9; first auto; smt().
by auto; smt().
qed.

local lemma reduct2 (i' : int) &m :
  1 <= i' < m + 1 =>
  Pr[GHP.Exper(Hybrid, DDHOr2).main((), i') @ &m : res] =
  Pr[DDH2(Reduct(Adv)).main((), i') @ &m : res].
proof.
move => i'_rng.
byequiv
  (: ={glob Adv} /\ i{1} = i' /\ i{2}.`2 = i' ==> _) => //.
transitivity
  FullRO.MainD(RO_Disting2, FullRO.RO).distinguish
  (={glob Adv} /\ i{1} = i' /\ x{2} = i' ==> ={res})
  (={glob Adv} /\ x{1} = i' /\ i{2}.`2 = i' ==> ={res}) => //.
by smt().
by apply Hybrid_DDHOr2_MainD_RO_Disting2_RO.
by apply MainD_RO_Disting2_RO_DDH2_Reduct.
qed.

lemma GReal_GIdeal1_sect &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  m%r *
  `|Pr[TR.Rand(DDH1(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res] -
    Pr[TR.Rand(DDH2(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res]|.
proof.
rewrite GReal_Hybrid -Hybrid_GIdeal.
rewrite (GHP.hybrid_param () (m + 1) DDHOr1 DDHOr2 Hybrid) /=.
+ smt(ge1_m).
+ move => i i_rng; rewrite Hybrid_step /#.
rewrite (GHP.TR.total_prob_drange (GHP.Exper(Hybrid, DDHOr1))).
+ smt(ge1_m).
rewrite (GHP.TR.total_prob_drange (GHP.Exper(Hybrid, DDHOr2))) /=.
+ smt(ge1_m).
rewrite
  (eq_big_int _ _
   (fun (j : int) =>
      Pr[GHP.Exper(Hybrid, DDHOr1).main((), j) @ &m : res] / m%r)
   (fun (i : int) =>
      Pr[DDH1(Reduct(Adv)).main((), i) @ &m : res] / m%r)).
+ by move => i i_rng /=; rewrite reduct1.
rewrite
  (eq_big_int _ _
   (fun (j : int) =>
      Pr[GHP.Exper(Hybrid, DDHOr2).main(tt, j) @ &m : res] / m%r)
   (fun (i : int) =>
      Pr[DDH2(Reduct(Adv)).main((), i) @ &m : res] / m%r)).
+ by move => i i_rng /=; rewrite reduct2.
rewrite (TR.total_prob_drange(DDH1(Reduct(Adv)))).
+ smt(ge1_m).
rewrite (TR.total_prob_drange(DDH2(Reduct(Adv)))).
+ smt(ge1_m).
done.
qed.

lemma GReal_GIdeal2_sect &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  `|bigi predT
    (fun (i : int) =>
       Pr[DDH1(Reduct(Adv)).main((), i) @ &m : res] -
       Pr[DDH2(Reduct(Adv)).main((), i) @ &m : res])
    1 (m + 1)|.
proof.
rewrite GReal_GIdeal1_sect
        -(GHP.hybrid_param_result _ _
           (DDH1(Reduct(Adv))) (DDH2(Reduct(Adv)))) /=.
+ smt(ge1_m).
have -> :
  Pr[TR.Rand(DDH1(Reduct(Adv))).f(drange 1 (m + 1), tt) @ &m : res] =
  Pr[GHP.TR.Rand(DDH1(Reduct(Adv))).f(drange 1 (m + 1), tt) @ &m : res].
+ by byequiv => //; sim.
have -> :
  Pr[TR.Rand(DDH2(Reduct(Adv))).f(drange 1 (m + 1), tt) @ &m : res] =
  Pr[GHP.TR.Rand(DDH2(Reduct(Adv))).f(drange 1 (m + 1), tt) @ &m : res].
+ by byequiv => //; sim.
done.
qed.

end section.

(* two ways of expressing the security result *)

lemma GReal_GIdeal1 (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  m%r *
  `|Pr[TR.Rand(DDH1(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res] -
    Pr[TR.Rand(DDH2(Reduct(Adv))).f(drange 1 (m + 1), ()) @ &m : res]|.
proof. by apply (GReal_GIdeal1_sect Adv). qed.

lemma GReal_GIdeal2 (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| =
  `|bigi predT
    (fun (i : int) =>
       Pr[DDH1(Reduct(Adv)).main((), i) @ &m : res] -
       Pr[DDH2(Reduct(Adv)).main((), i) @ &m : res])
    1 (m + 1)|.
proof. by apply (GReal_GIdeal2_sect Adv). qed.
