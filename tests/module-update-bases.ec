(* ------------------------------------------------------------------------
   Fine-grained module definitions (`module M' = M with {...}`) on bases
   beyond a plain top-level module:

     - applied functors:                     F(A0)   with {...}
     - re-parameterized functors:    (B:T) = F(B)    with {...}
     - sub-modules:                          P.O     with {...}
     - sub-modules of applied functors:      F(A0).O with {...}

   Semantics under test: the update copies the base's ITEMS (variables,
   procedures, nested sub-modules), re-rooting exactly the references to
   those copied items.  References to anything else -- an enclosing
   module's state, sibling sub-modules, other modules -- denote state that
   is NOT copied and stays SHARED with the base.  Functor applications
   are baked into the copy.

   Regressions covered:
     - functor bases whose bodies contain self-calls used to crash the
       elaborator (the self-reference is unsuspended at the application's
       arguments, which the re-rooting failed to absorb);
     - sub-module bases used to re-root references to the enclosing
       module's state -- and even to the sub-module's own state -- onto
       paths of the new module that do not exist (dangling globals).
   ------------------------------------------------------------------------ *)
require import AllCore.

module type T = { proc run() : int }.

module A0 : T = { proc run() : int = { return 7; } }.

(* ======================================================================
   Functor bases with a self-call (`f` calls its sibling `h`).
   ====================================================================== *)
module F (B : T) = {
  var g : int
  proc h() : int = { var r; r <@ B.run(); g <- g + r; return g; }
  proc f() : int = { var r; r <@ h(); return r; }
}.

(* -- applied at a concrete module: the application is baked in --------- *)
module QC = F(A0) with { proc f [ 1 + ^ { g <- 1; } ] }.

(* QC.g is a fresh copy of F.g; the self-call resolves to QC.h; F's own
   state is not touched by running the copy. *)
lemma QC_f : hoare[ QC.f : QC.g = 0 /\ F.g = 5
                       ==> QC.g = 8 /\ F.g = 5 /\ res = 8 ].
proof. by proc; inline *; auto. qed.

(* -- re-parameterized: same, at a functor parameter -------------------- *)
module QP (B : T) = F(B) with { proc f [ 1 + ^ { g <- 1; } ] }.

lemma QP_f : hoare[ QP(A0).f : QP.g = 0 ==> QP.g = 8 /\ res = 8 ].
proof. by proc; inline *; auto. qed.

(* ======================================================================
   Sub-module bases.
   ====================================================================== *)

(* -- the enclosing module's state is shared, not copied ---------------- *)
module P = {
  var g : int
  module O = {
    proc f() : int = { g <- g + 1; return g; }
  }
}.

(* Inside the patch, the enclosing module's variables are written
   qualified (`P.g`): the patch is typed in the new module's scope. *)
module QO = P.O with { proc f [ 1 + { P.g <- P.g + 2; } ] }.

lemma QO_f : hoare[ QO.f : P.g = 0 ==> P.g = 3 /\ res = 3 ].
proof. by proc; auto. qed.

(* the base is unchanged *)
lemma PO_f : hoare[ P.O.f : P.g = 0 ==> P.g = 1 /\ res = 1 ].
proof. by proc; auto. qed.

(* -- the sub-module's own state is copied ------------------------------ *)
module P2 = {
  module O = {
    var x : int
    proc f() : int = { x <- x + 1; return x; }
  }
}.

module QX = P2.O with { proc f [ 1 + { x <- x + 2; } ] }.

lemma QX_f : hoare[ QX.f : QX.x = 0 /\ P2.O.x = 5
                      ==> QX.x = 3 /\ P2.O.x = 5 /\ res = 3 ].
proof. by proc; auto. qed.

(* -- self-calls inside the sub-module re-root to the copy -------------- *)
module P3 = {
  module O = {
    var n : int
    proc get() : int = { n <- n + 1; return n; }
    proc sample() : unit = { var d; d <@ get(); }
  }
}.

module QS = P3.O with { proc sample [ var e : int  1 + { e <@ get(); } ] }.

lemma QS_sample : hoare[ QS.sample : QS.n = 0 /\ P3.O.n = 5
                            ==> QS.n = 2 /\ P3.O.n = 5 ].
proof. by proc; inline *; auto. qed.

(* -- nested sub-modules are copied along ------------------------------- *)
module P4 = {
  module O = {
    module M = {
      var y : int
      proc bump() : unit = { y <- y + 1; }
    }
    proc f() : int = { M.bump(); return M.y; }
  }
}.

module QN = P4.O with { proc f [ 1 + ^ { M.y <- 5; } ] }.

lemma QN_f : hoare[ QN.f : P4.O.M.y = 0
                      ==> QN.M.y = 6 /\ P4.O.M.y = 0 /\ res = 6 ].
proof. by proc; inline *; auto. qed.

(* ======================================================================
   Sub-module of an applied functor: the functor's enclosing state is
   shared (it is application-independent), the sub-module's state is
   copied, and the application is baked in.
   ====================================================================== *)
module G (B : T) = {
  var g : int
  module O = {
    var x : int
    proc f() : int = { var r; r <@ B.run(); g <- g + r; x <- x + 1; return x; }
  }
}.

module QD = G(A0).O with { proc f [ 1 + ^ { x <- x + 2; } ] }.

lemma QD_f : hoare[ QD.f : QD.x = 0 /\ G.g = 0 /\ G.O.x = 5
                      ==> QD.x = 3 /\ G.g = 7 /\ G.O.x = 5 /\ res = 3 ].
proof. by proc; inline *; auto. qed.

(* -- and the re-parameterized variant of the same ----------------------- *)
module QE (B : T) = G(B).O with { proc f [ 1 + ^ { x <- x + 2; } ] }.

lemma QE_f : hoare[ QE(A0).f : QE.x = 0 /\ G.g = 0
                       ==> QE.x = 3 /\ G.g = 7 /\ res = 3 ].
proof. by proc; inline *; auto. qed.

(* ======================================================================
   Multi-parameter functors: the argument prefix has length > 1.
   ====================================================================== *)
module A1 : T = { proc run() : int = { return 11; } }.

module H (B1 : T) (B2 : T) = {
  var g : int
  proc h() : int = {
    var r1, r2;
    r1 <@ B1.run();
    r2 <@ B2.run();
    g <- g + r1 + r2;
    return g;
  }
  proc f() : int = { var r; r <@ h(); return r; }
}.

module QM = H(A0, A1) with { proc f [ 1 + ^ { g <- 1; } ] }.

lemma QM_f : hoare[ QM.f : QM.g = 0 /\ H.g = 5
                      ==> QM.g = 19 /\ H.g = 5 /\ res = 19 ].
proof. by proc; inline *; auto. qed.

(* ======================================================================
   Abstract bases are rejected with a proper error (not an anomaly).
   ====================================================================== *)
section.

declare module X <: T.

expect fail "cannot update an abstract module"
local module QA = X with { proc run [ 1 - ] }.

end section.
