(* GlobalHybridExamp2.ec *)

(* We use theories/crypto/GlobalHybrid.ec for an example where the
   cost of each hybrid step is an instance of the Decisional
   Diffie-Hellman (DDH) assumption. *)

require import AllCore Real Distr DBool StdOrder StdBigop GlobalHybrid.
require import FMap PROM.
import RealOrder Bigreal BRA.

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)

op kid : key.  (* identity *)

op kinv : key -> key.  (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom kid_l (x : key) : kid ^^ x = x.

axiom kid_r (x : key) : x ^^ kid = x.

axiom kinv_l (x : key) : kinv x ^^ x = kid.

axiom kinv_r (x : key) : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op [full uniform lossless] dexp : exp distr.

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* DDH Adversary *)

module type DDH_ADV = {
  proc main(k1 k2 k3 : key) : bool
}.

(* the real DDH game *)

module DDH1 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var q1, q2 : exp;
    q1 <$ dexp; q2 <$ dexp;
    b <@ Adv.main(g ^ q1, g ^ q2, g ^ (q1 * q2));
    return b;
  }
}.
  
(* the ideal DDH game *)

module DDH2 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var q1, q2, q3 : exp;
    q1 <$ dexp; q2 <$ dexp; q3 <$ dexp;
    b <@ Adv.main(g ^ q1, g ^ q2 , g ^ q3);
    return b;
  }
}.

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

  proc init() : unit = {
    ctr <- 0;
  }

  proc get() : key * key * key = {
    var r : key * key * key;
    if (ctr < m) {
      x <$ dexp; y <$ dexp;
      r <- (g ^ x, g ^ y, g ^ (x * y));
      ctr <- ctr + 1;
    }
    else {
      r <- witness;
    }
    return r;
  }
}.

(* the ideal oracle *)

module OrIdeal : OR = {
  var ctr : int

  proc init() : unit = {
    ctr <- 0;
  }

  proc get() : key * key * key = {
    var r : key * key * key;
    var x, y, z : exp;
    if (ctr < m) {
      x <$ dexp; y <$ dexp; z <$ dexp;
      r <- (g ^ x, g ^ y, g ^ z);
      ctr <- ctr + 1;
    }
    else {
      r <- witness;
    }
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
  var i : int  (* needs to be a global to support game hoping *)
  var u, v, w : key

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr < m) {
        if (ctr + 1 < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr + 1 = i) {
          r <- (u, v, w);
        }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else {
        r <- witness;
      }
      return r;
    }
  }

  proc main(u' : key, v' : key, w' : key) : bool = {
    var b : bool;
    Or.ctr <- 0;
    u <- u'; v <- v'; w <- w';
    b <@ Adv(Or).disting();
    return b;
  }
}.

(* the reduction composed with DDH1 *)

module DDH1Reduct(Adv : ADV) = {
  proc main(i : int) : bool = {
    var b : bool;
    Reduct.i <- i;  (* so value of Reduct.i in memory irrelevant *)
    b <@ DDH1(Reduct(Adv)).main();
    return b;
  }
}.
    
(* the reduction composed with DDH2 *)

module DDH2Reduct(Adv : ADV) = {
  proc main(i : int) : bool = {
    var b : bool;
    Reduct.i <- i;  (* so value of Reduct.i in memory irrelevant *)
    b <@ DDH2(Reduct(Adv)).main();
    return b;
  }
}.

(* our goal is to prove:

lemma GReal_GIdeal (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| <=
  bigi predT
  (fun i =>
   `|Pr[DDH1Reduct(Adv).main(i) @ &m : res] -
     Pr[DDH2Reduct(Adv).main(i) @ &m : res]|)
  1 (m + 1).
*)

section.

declare module Adv <: ADV{-OrReal, -OrIdeal, -Reduct}.

local module Hybrid : HYBRID = {
  var i : int

  module Or = {
    var ctr : int

    proc init() : unit = { }

    (* get shifts from ideal to real based on the value of i *)

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr < m) {
        if (ctr + 1 < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;  (* ideal *)
          r <- (g ^ x, g ^ y, g ^ z);
        }
        else {
          x <$ dexp; y <$ dexp;  (* real *)
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else {
        r <- witness;
      }
      return r;
    }
  }

  (* i' should be between 1 and m + 1 *)

  proc main(i' : int) : bool = {
    var b : bool;
    i <- i'; Or.ctr <- 0;
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma GReal_Hybrid &m :
  Pr[GReal(Adv).main() @ &m : res] = Pr[Hybrid.main(1) @ &m : res].
proof.
byequiv => //; proc; inline.
seq 1 2 :
  (={glob Adv} /\ OrReal.ctr{1} = Hybrid.Or.ctr{2} /\
   OrReal.ctr{1} = 0 /\ Hybrid.i{2} = 1); first auto.
call
  (_ :
   OrReal.ctr{1} = Hybrid.Or.ctr{2} /\
   0 <= OrReal.ctr{1} <= m /\ Hybrid.i{2} = 1).
proc; if => //.
rcondf{2} 1; first auto; smt().
auto; smt().
auto.
auto; smt(ge1_m).
qed.

local lemma Hybrid_GIdeal &m :
  Pr[Hybrid.main(m + 1) @ &m : res] = Pr[GIdeal(Adv).main() @ &m : res].
proof.
byequiv => //; proc; inline.
seq 2 1 :
  (={glob Adv} /\ Hybrid.Or.ctr{1} = OrIdeal.ctr{2} /\
   OrIdeal.ctr{2} = 0 /\ Hybrid.i{1} = m + 1); first auto.
call
  (_ :
   Hybrid.Or.ctr{1} = OrIdeal.ctr{2} /\
   0 <= OrIdeal.ctr{2} <= m /\ Hybrid.i{1} = m + 1).
proc; if => //.
rcondt{1} 1; first auto; smt().
auto; smt().
auto.
auto; smt(ge1_m).
qed.

(* in our sequences of games, we need to shift from lazy to eager
   sampling for two or three exponents, and so we use PROM *)

type ro_in_t = [A | B | C].  (* three names of exponents *)

local clone FullRO with
  type in_t    <- ro_in_t,
  type out_t   <- exp,
  op dout      <- fun _ => dexp,
  type d_in_t  <- unit,
  type d_out_t <- bool
proof *.

(* first, the sequence of games proving:

   1 <= i < m + 1 => Reduct.i{m} = i =>
   Pr[Hybrid.main(i) @ &m : res] =
   Pr[DDH1(Reduct(Adv)).main() @ &m : res] *)

local module (RO_Disting1 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  var i : int
  var u, v, w : key

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr < m) {
        if (ctr + 1 < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr + 1 = i) {
          x <@ RO.get(A); y <@ RO.get(B);
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else {
        r <- witness;
      }
      return r;
    }
  }

  proc distinguish() : bool = {
    var b : bool;
    Or.ctr <- 0;
    RO.sample(A); RO.sample(B); RO.sample(C);
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma Hybrid_MainD_RO_Disting1_RO (i : int) :
  1 <= i < m + 1 =>
  equiv
  [Hybrid.main ~
   FullRO.MainD(RO_Disting1, FullRO.RO).distinguish :
   ={glob Adv} /\ i'{1} = i /\ RO_Disting1.i{2} = i ==>
   ={res}].
proof.
move => [ge1_i le_i_m]; rewrite ltzS in le_i_m.
transitivity
  FullRO.MainD(RO_Disting1, FullRO.LRO).distinguish 
  (={glob Adv} /\ i'{1} = i /\ RO_Disting1.i{2} = i ==> ={res})
  (={glob Adv} /\ ={glob RO_Disting1} ==> ={res}) => //.
progress.
by exists (glob Adv){2} arg{1} RO_Disting1.u{2} RO_Disting1.v{2}
          RO_Disting1.w{2} RO_Disting1.Or.ctr{2}.
proc; inline*; wp.
seq 2 6 :
  (={glob Adv} /\ Hybrid.i{1} = i /\ RO_Disting1.i{2} = i /\
   Hybrid.Or.ctr{1} = 0 /\ RO_Disting1.Or.ctr{2} = 0 /\
   FullRO.RO.m{2} = empty); first auto.
call
  (_ :
   Hybrid.Or.ctr{1} = RO_Disting1.Or.ctr{2} /\
   0 <= Hybrid.Or.ctr{1} <= m /\
   Hybrid.i{1} = i /\ RO_Disting1.i{2} = i /\
   (Hybrid.Or.ctr{1} + 1 <= i => FullRO.RO.m{2} = empty)).
proc; if => //.
case (Hybrid.Or.ctr{1} + 1 = Hybrid.i{1}).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto.
wp; inline*.
swap{2} 2 -1; swap{2} 6 -4; swap{2} 10 -7.
seq 2 3 :
  (#pre /\ x{1} = r0{2} /\ y{1} = r1{2} /\
   x0{2} = A); first auto.
rcondt{2} 1; first auto; smt(mem_empty).
sp 0 3.
rcondt{2} 1; first auto; smt(mem_set mem_empty).
auto; smt(get_set_sameE).
if => //; first auto; smt().
rcondf{2} 1; first auto.
auto; smt().
auto.
auto.
smt(ge1_m).
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting1 _) => //.
move => _; apply dexp_ll.
qed.

local lemma MainD_RO_Disting1_RO_DDH1_Reduct :
  equiv
  [FullRO.MainD(RO_Disting1, FullRO.RO).distinguish ~
   DDH1(Reduct(Adv)).main :
   ={glob Adv} /\ RO_Disting1.i{1} = Reduct.i{2} ==>
   ={res}].
proof.
proc; inline*; wp.
swap{1} 6 -5; swap{1} 10 -8; swap{1} 14 -11.
seq 15 9 :
  (={glob Adv} /\ RO_Disting1.i{1} = Reduct.i{2} /\
   RO_Disting1.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1{2} /\
   FullRO.RO.m{1}.[B] = Some q2{2} /\
   Reduct.u{2} = g ^ q1{2} /\
   Reduct.v{2} = g ^ q2{2} /\
   Reduct.w{2} = g ^ (q1{2} * q2{2})).
wp => /=; rnd{1}; rnd; rnd.
auto; smt(get_setE mem_set mem_empty).
exlim q1{2}, q2{2} => q1_R q2_R.
call
  (_ :
   RO_Disting1.i{1} = Reduct.i{2} /\
   RO_Disting1.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1_R /\
   FullRO.RO.m{1}.[B] = Some q2_R /\
   Reduct.u{2} = g ^ q1_R /\
   Reduct.v{2} = g ^ q2_R /\
   Reduct.w{2} = g ^ (q1_R * q2_R)).
proc; if => //.
if => //; first auto.
if => //.
wp; inline*; auto; smt(get_setE).
auto.
auto.
auto.
qed.

local lemma Hybrid_DDH1_Reduct (i : int) &m :
  1 <= i < m + 1 => Reduct.i{m} = i =>
  Pr[Hybrid.main(i) @ &m : res] =
  Pr[DDH1(Reduct(Adv)).main() @ &m : res].
proof.
move => i_bnd Reduct_i_eq_i.
byequiv (_ : ={glob Adv} /\ i'{1} = i /\ Reduct.i{2} = i ==> _) => //.
transitivity
  FullRO.MainD(RO_Disting1, FullRO.RO).distinguish
  (={glob Adv} /\ i'{1} = i /\ RO_Disting1.i{2} = i ==> ={res})
  (={glob Adv} /\ RO_Disting1.i{1} = Reduct.i{2} ==> ={res}) => //.
progress; by exists (glob Adv){2} arg{1}.
by apply Hybrid_MainD_RO_Disting1_RO.
by apply MainD_RO_Disting1_RO_DDH1_Reduct.
qed.

(* next the sequence of games proving:
   1 <= i < m + 1 => Reduct.i{m} = i =>
   Pr[Hybrid.main(i + 1) @ &m : res] =
   Pr[DDH2(Reduct(Adv)).main() @ &m : res] *)

local module (RO_Disting2 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  var i : int
  var u, v, w : key

  module Or = {
    var ctr : int

    proc init() : unit = { }

    proc get() : key * key * key = {
      var r : key * key * key;
      var x, y, z : exp;
      if (ctr < m) {
        if (ctr + 1 < i) {
          x <$ dexp; y <$ dexp; z <$ dexp;
          r <- (g ^ x, g ^ y, g ^ z);
        }
        elif (ctr + 1 = i) {
          x <@ RO.get(A); y <@ RO.get(B); z <@ RO.get(C);
          r <- (g ^ x, g ^ y, g ^ z);
        }
        else {
          x <$ dexp; y <$ dexp;
          r <- (g ^ x, g ^ y, g ^ (x * y));
        }
        ctr <- ctr + 1;
      }
      else {
        r <- witness;
      }
      return r;
    }
  }

  proc distinguish() : bool = {
    var b : bool;
    Or.ctr <- 0;
    RO.sample(A); RO.sample(B); RO.sample(C);
    b <@ Adv(Or).disting();
    return b;
  }
}.

local lemma Hybrid_MainD_RO_Disting2_RO (i : int) :
  1 <= i < m + 1 =>
  equiv
  [Hybrid.main ~
   FullRO.MainD(RO_Disting2, FullRO.RO).distinguish :
   ={glob Adv} /\ i'{1} = i + 1 /\ RO_Disting2.i{2} = i ==>
   ={res}].
proof.
move => [ge1_i le_i_m]; rewrite ltzS in le_i_m.
transitivity
  FullRO.MainD(RO_Disting2, FullRO.LRO).distinguish 
  (={glob Adv} /\ i'{1} = i + 1 /\ RO_Disting2.i{2} = i ==> ={res})
  (={glob Adv} /\ ={glob RO_Disting2} ==> ={res}) => //.
progress.
by exists (glob Adv){2} RO_Disting2.i{2} RO_Disting2.u{2} RO_Disting2.v{2}
          RO_Disting2.w{2} RO_Disting2.Or.ctr{2}.
proc; inline*; wp.
seq 2 6 :
  (={glob Adv} /\ Hybrid.i{1} = i + 1 /\ RO_Disting2.i{2} = i /\
   Hybrid.Or.ctr{1} = 0 /\ RO_Disting2.Or.ctr{2} = 0 /\
   FullRO.RO.m{2} = empty); first auto.
call
  (_ :
   Hybrid.Or.ctr{1} = RO_Disting2.Or.ctr{2} /\
   0 <= Hybrid.Or.ctr{1} <= m /\
   Hybrid.i{1} = i + 1 /\ RO_Disting2.i{2} = i /\
   (Hybrid.Or.ctr{1} + 1 <= i => FullRO.RO.m{2} = empty)).
proc; if => //.
if{1}.
if{2}; first auto; smt().
rcondt{2} 1; first auto; smt().
wp; inline*; swap{2} 2 -1; swap{2} 6 -4; swap{2} 10 -7.
seq 3 4 :
  (#pre /\ x{1} = r0{2} /\ y{1} = r1{2} /\ z{1} = r2{2} /\
   x0{2} = A); first auto.
rcondt{2} 1; first auto; smt(mem_empty).
sp 0 3.
rcondt{2} 1; first auto; smt(mem_set mem_empty).
sp 0 3.
rcondt{2} 1; first auto; smt(mem_set mem_empty).
auto; smt(get_set_sameE).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
auto; smt().
auto.
auto; smt(ge1_m).
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting2 _) => //.
move => _; apply dexp_ll.
qed.

local lemma MainD_RO_Disting2_RO_DDH2_Reduct :
  equiv
  [FullRO.MainD(RO_Disting2, FullRO.RO).distinguish ~
   DDH2(Reduct(Adv)).main :
   ={glob Adv} /\ RO_Disting2.i{1} = Reduct.i{2} ==>
   ={res}].
proof.
proc; inline*; wp.
swap{1} 6 -5; swap{1} 10 -8; swap{1} 14 -11.
seq 15 10 :
  (={glob Adv} /\ RO_Disting2.i{1} = Reduct.i{2} /\
   RO_Disting2.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1{2} /\
   FullRO.RO.m{1}.[B] = Some q2{2} /\
   FullRO.RO.m{1}.[C] = Some q3{2} /\
   Reduct.u{2} = g ^ q1{2} /\
   Reduct.v{2} = g ^ q2{2} /\
   Reduct.w{2} = g ^ q3{2}).
wp => /=; rnd; rnd; rnd.
auto; smt(get_setE mem_set mem_empty).
exlim q1{2}, q2{2}, q3{2} => q1_R q2_R q3_R.
call
  (_ :
   RO_Disting2.i{1} = Reduct.i{2} /\
   RO_Disting2.Or.ctr{1} = Reduct.Or.ctr{2} /\
   FullRO.RO.m{1}.[A] = Some q1_R /\
   FullRO.RO.m{1}.[B] = Some q2_R /\
   FullRO.RO.m{1}.[C] = Some q3_R /\
   Reduct.u{2} = g ^ q1_R /\
   Reduct.v{2} = g ^ q2_R /\
   Reduct.w{2} = g ^ q3_R).
proc; if => //.
if => //; first auto.
if => //; first wp; inline*; auto; smt(get_setE).
auto.
auto.
auto.
qed.

local lemma Hybrid_DDH2_Reduct (i : int) &m :
  1 <= i < m + 1 => Reduct.i{m} = i =>
  Pr[Hybrid.main(i + 1) @ &m : res] =
  Pr[DDH2(Reduct(Adv)).main() @ &m : res].
proof.
move => i_bnd H.
byequiv (_ : ={glob Adv} /\ i'{1} = i + 1 /\ Reduct.i{2} = i ==> _) => //.
transitivity
  FullRO.MainD(RO_Disting2, FullRO.RO).distinguish
  (={glob Adv} /\ i'{1} = i + 1 /\ RO_Disting2.i{2} = i ==> ={res})
  (={glob Adv} /\ RO_Disting2.i{1} = Reduct.i{2} ==> ={res}) => //.
progress; by exists (glob Adv){2} Reduct.i{2}.
by apply (Hybrid_MainD_RO_Disting2_RO i).
by apply MainD_RO_Disting2_RO_DDH2_Reduct.
qed.

local lemma Hybrid_DDH1Reduct (i' : int) &m :
  1 <= i' < m + 1 =>
  Pr[Hybrid.main(i') @ &m : res] =
  Pr[DDH1Reduct(Adv).main(i') @ &m : res].
proof.
move => ge1_i'_lt_m_plus1.
rewrite eq_sym.
byphoare (_ : i = i' /\ glob Adv = (glob Adv){m} ==> _) => //.
proc; sp.
call (_ : Reduct.i = i' /\ (glob Adv) = (glob Adv){m} ==> res).
bypr => &n [] Reduct_i_n_eq_i' eq_glob_n_m.
rewrite -(Hybrid_DDH1_Reduct i' &n) => //.
byequiv => //; sim.
auto.
qed.

local lemma Hybrid_DDH2Reduct (i' : int) &m :
  1 <= i' < m + 1 =>
  Pr[Hybrid.main(i' + 1) @ &m : res] =
  Pr[DDH2Reduct(Adv).main(i') @ &m : res].
proof.
move => ge1_i'_lt_m_plus1.
rewrite eq_sym.
byphoare (_ : i = i' /\ glob Adv = (glob Adv){m} ==> _) => //.
proc; sp.
call (_ : Reduct.i = i' /\ (glob Adv) = (glob Adv){m} ==> res).
bypr => &n [] Reduct_i_n_eq_i' eq_glob_n_m.
rewrite -(Hybrid_DDH2_Reduct i' &n) => //.
byequiv => //; sim.
auto.
qed.

lemma GReal_GIdeal_sect &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| <=
  bigi predT
  (fun i =>
   `|Pr[DDH1Reduct(Adv).main(i) @ &m : res] -
     Pr[DDH2Reduct(Adv).main(i) @ &m : res]|)
  1 (m + 1).
proof.
rewrite GReal_Hybrid -Hybrid_GIdeal (hybrid_gen _ _ Hybrid _ _ _).
smt(ge1_m).
move => i bnd_i /=.
by rewrite Hybrid_DDH1Reduct // Hybrid_DDH2Reduct.
qed.

end section.

lemma GReal_GIdeal (Adv <: ADV{-OrReal, -OrIdeal, -Reduct}) &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv).main() @ &m : res]| <=
  bigi predT
  (fun i =>
   `|Pr[DDH1Reduct(Adv).main(i) @ &m : res] -
     Pr[DDH2Reduct(Adv).main(i) @ &m : res]|)
  1 (m + 1).
proof.
apply (GReal_GIdeal_sect Adv).
qed.
