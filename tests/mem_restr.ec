theory TEST_proc_abs_inv.
type t1, t2, t3, t4, t5, t6.

module type M = {
  proc f(_: t1) : t2
}.

module type F (O : M) = {
  proc g(_: t3) : t4
}.

module Mem = {
  var v1 : t5
  var v2 : t6
  proc _init() = {
    v1 <- witness;
    v2 <- witness;
  }
}.

module (H1 : F) (O : M) = {
  proc g(x: t3) : t4 = {
    return witness;
  }
}.

module (H5 : F) (O : M) = {
  var v : t1

  proc g(x: t3) : t4 = {
    v <- witness;
    return witness;
  }
}.

module (H2 : F) (O : M) = {
  proc g(x: t3) : t4 = {
    Mem.v1 <- witness;
    return witness;
  }
}.

module (H3 : F) (O : M) = {
  proc g(x: t3) : t4 = {
    O.f(witness);
    return witness;
  }
}.

module (H4 : F) (O : M) = {
  proc g(x: t3) : t4 = {
    O.f(witness);
    Mem.v1 <- witness;
    return witness;
  }
}.

module N : M = {
  proc f(x: t1) : t2 = {
    Mem.v2 <- witness;
    return witness;
  }
}.

module O : M = {
  proc f(x: t1) : t2 = {
    Mem.v1 <- witness;
    Mem.v2 <- witness;
    return witness;
  }
}.

lemma t: forall (G <: F{-Mem}), true.
proof. trivial. qed.

lemma f: false.
proof.
have := t H1.
have := t H2.


section.
declare module N1 <: M. 
declare module N2 <: M {-Mem.v1}. 
declare module G1 <: F {0}.
declare module N3 <: M {-G1}.

phoare hr_proc_inv: [G1(N3).g: true ==> true] = 1.0.
proof.
print glob G1(N1).
proc (true).
fail proc (Mem.v1 = witness).
(* fail proc (glob N1 = witness). *)
(* fail proc (glob N1.f = witness). *)
proc (true).
abort.

hoare hr_proc_inv: G1(N1).g: true ==> true.
proof.
fail proc (Mem.v1 = witness).
fail proc (glob N1 = witness).
fail proc (glob N1.f = witness).
proc (true); expect 3.
abort.



theory U.
module type AT = {
  proc p():unit
}.

module A : AT = {
  var x : int
  proc p() = { x <- 1; }
}.

print glob A.
(* glob A = A.x : int *)

module type BT(Al:AT) = {
  proc p():unit
}.

module B(A:AT) = {
  proc p() = {}
}.

print glob B.
(* glob B(A) = {} : unit, no matter what A is because B does not invoke A *)

(* Auxiliary lemma, nothing fishy here *)
lemma singleton_unit: (forall (x y:unit), x=y) <=> true.
  rewrite /singleton.
  progress.
qed.
    
(* Auxiliary lemma, nothing fishy here *)
lemma singleton_int: (forall (x y:int), x=y) <=> false.
  rewrite /singleton.
  simplify.
  rewrite negb_forall.
  exists 0.
  simplify.
  rewrite negb_forall.
  exists 1.
  trivial.
qed.

(* Auxiliary lemma, nothing fishy here *)
lemma singleton_pair ['a 'b]: (forall (x y:'a*'b), x=y) <=> ((forall (x y:'a), x=y) /\ (forall (x y:'b), x=y)).
  rewrite /singleton.
  apply iffI.
  move => H.  
  split.
  (* Goal 1 *)
  move => x y.  
  have H1 := H (x,witness) (y,witness).
  smt.
  (* Goal 2 *)
  move => x y.  
  have H1 := H (witness,x) (witness,y).
  smt.
  (* Goal 2 *)
  move => [H1 H2] x y.
  have H1' := H1 x.`1 y.`1.
  have H2' := H2 x.`2 y.`2.
  smt.
qed.

(* The trouble starts here *)
lemma contradiction: false.
  have H1: exists (B0<:BT) (A0 <: AT), (forall (x y:glob B0(A0)), x=y) /\ ! (forall (x y:glob A0), x=y).
    exists B A. 
    by rewrite singleton_unit singleton_int.
  elim H1 => B0 A0 [H2 H3].
  have H4: !(forall (x y:glob B0(A0)), x=y).
    (* This no longer applies since glob for abstract modules is not eagerly normalized *)
    admit.
  (* H2,H4 are a contradiction *)
  done.  
qed.
end U.

theory C.
(* Auxiliary lemmas, nothing fishy here *)
lemma singleton_int: (forall (x y:int), x=y) <=> false.
proof. smt(). qed.

module type AT = {
  proc p():unit
}.

module A : AT = {
  var x : int
  proc p() = { }
}.

module A' : AT = {
  var x : int
  proc p() = { x <- 1; }
}.

module Bx(A0:AT) = { 
 proc p() = { A0.p() ; }
}.

print glob A.     (* A.x - even though A.p doesn't actually access A.x *)
print glob Bx(A). (* unit, presumably because A.p does not access A.x *)

lemma contradiction : false.
proof.
(* for abstact A0, glob Bx(A0) is acutally glob A0 ... *)
have X : forall (A' <: AT), 
  (forall (x y: glob Bx(A')), x = y) <=> (forall (x y: glob A'), x = y).
- done.

(* Consistent handling of globs makes this lemma useless *)
move: (X A). 
move: (X A'). 
admit.
qed.
end C.

theory X.
require import AllCore.

module type T = { proc p(): unit }.

module M = { var x : int proc p(): unit = {x <- 1;} }.

module N(A:T) = {
  proc p():unit = { A.p(); }
}.

section.


(* vars(N(A)) overapproximated as vars(A)
   So C is assumed disjoint from vars(A).
   But if we later instantiate A := M,
   vars(N(M)) will be {}, so the lemma test below is proven
   for C disjoint from vars(A), but can be used for C disjoint
   from {}, i.e. for any C. *)

lemma test (A <: T) (C <: T {-N(A)}) x: hoare [ C.p : glob A = x  ==>  glob A = x ].
proc (M.x = 1).
qed.

end section.


(* Instantiating test2 with A := N, this looks harmless
but now C{-N(M)} doesn't restrict C much. *)
lemma test2 (C <: T{-N(M)}) x:
hoare [ C.p : glob M = x ==> glob M = x ].
exact (test M C x).
qed.

module D = {
  proc p() = { M.x <- 1; }
}.

(* We instantiate C := D. This can be done because D is disjoint
   from vars(N(M)) = {}. *)
lemma test3:
hoare [ D.p : M.x = 0 ==> M.x = 0 ].
move: (test2 D).
qed.

(* At this point, we have a clearly false statement (since D.p 
   sets M.x <- 1). Below we just do a bit of uninteresting extra
   work to get an explicit false.  *)

module E = {
  proc p() = { M.x <- 0; D.p(); }
}.

lemma false: false.
    have false_m: forall &m, false.
    + move => &m.
      have Pr1: Pr[ E.p() @ &m : M.x = 1 ] = 1%r.
      - byphoare => //.
        proc.
        inline *.
        auto.
      have Pr0: Pr[ E.p() @ &m : M.x = 1 ] = 0%r.
      - byphoare => //.
        hoare.
        proc.
        call test3.
        auto.
      have H01: 0%r = 1%r.
      - rewrite -Pr0 -Pr1. trivial.
    trivial.
  trivial.
qed.
end X.


theory D.
require import AllCore.

module type T = { proc p():bool }.
module type T1(M:T) = { proc p():bool }.
module type T2(M:T1) = { proc p():bool }.

module A:T = { var x : bool proc p():bool = { return A.x; } }.
module B(A:T) = { proc p():bool = { var r : bool; r <@ A.p(); return r; } }.
module C(B:T1) = { proc p():bool = { var r : bool; r <@ B(A).p(); return r; } }.
print glob A.
print glob B.
print glob C.

(* Nothing fishy here. *)
lemma correct (A<:T) &m &n: (glob A){m} = (glob A){n} => Pr[A.p() @ &m : res] = Pr[A.p() @ &n : res].
    move => H.
    byequiv.
    proc*.
    call (_: true).
    auto.
    smt.
    smt.
qed.

(* Hoping for some unsoundness because "glob B(A)" might be rewritten to something undesirable.
   Instead, EasyCrypt crashes (more precisely: an anomaly is raised that gets ProofGeneral out of sync) *)    
lemma test (B<:T1) &m &n : (glob B){m} = (glob B){n} => Pr[B(A).p() @ &m : res] = Pr[B(A).p() @ &n : res].  
  have H := correct (B(A)).
end D.
(* Lemma looks suspicious: C(B).p might read variables of C, so ={glob C} should not be a sufficient precondition.
   Reason for this: glob C(B) seems to rewrite to glob C. *)
lemma suspicious (C<:T2) (B<:T1): equiv [ C(B).p ~ C(B).p : true ==> ={res} ].
  proc*.
  call (_: true).
  progress.    
qed.

(* Intuitively, lemma suspicious should give a contradiction when instantiating it with the concrete C and B from above.
   I didn't manage to do so because I get an error I don't understand.
   Maybe that's accidental, maybe this is intentional to make the glob-reasoning sound.
   In any case, it is a confusing error. *)  
lemma false_try: true.
(*

  (* invalid argument (incompatible module type):
  procedure `p' is not compatible: the function is not allowed to use B(A).p *)
  have H := suspicious C B.

  *)
  trivial.
qed.  
