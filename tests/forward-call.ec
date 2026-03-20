require import AllCore.

(* -------------------------------------------------------------------- *)
(* Base module and contracts for tests *)

module M = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc g(x : int, y : int) : int = {
    x <@ f(x);
    x <- x + 1;
    return 2*x;
  }
}.

lemma fP : hoare[M.f : 0 <= x ==> 1 <= res].
proof. by proc; auto=> /#. qed.

lemma fPx (x_ : int) : hoare[M.f : 0 <= x_ /\ x = x_ ==> res = x_ + 1].
proof. by proc; auto. qed.

pred p : int.
pred q : int.

(* ================================================================== *)
(* Forward ecall with a parameterized contract: the contract's         *)
(* universally-quantified parameter is instantiated with a program     *)
(* variable. The first subgoal checks the contract precondition,       *)
(* the second is the continuation using the precise postcondition      *)
(* together with framed conjuncts.                                     *)
(* ================================================================== *)

lemma gP_param (y_ : int) :
  hoare[M.g : 0 < x /\ y = y_ /\ p y ==> p y_].
proof.
proc=> /=.
ecall ->> (fPx x).
- by move=> |> * /#.
- by auto=> |> * /#.
qed.

(* ================================================================== *)
(*             Test 1: No lvalue (call result discarded)               *)
(* ================================================================== *)

module N1 = {
  var g : int

  proc incr() : int = {
    g <- g + 1;
    return g;
  }

  proc h(x : int) : int = {
    incr();
    return x;
  }
}.

lemma n1_incrP : hoare[N1.incr : 0 <= N1.g ==> 0 < N1.g].
proof. by proc; auto => /#. qed.

(* Forward ecall with no lvalue: postcondition conjuncts mentioning
   res are filtered out. The conjunct 0 < x is framed since x is
   not in the write set of incr. *)
lemma n1_hP : hoare[N1.h : 0 <= N1.g /\ 0 < x ==> 0 < N1.g /\ 0 < res].
proof.
proc=> /=.
ecall ->> (n1_incrP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*       Test 2: Multiple conjuncts with mixed framing                 *)
(* ================================================================== *)

(* p x depends on writes (x is modified by the call to f), but
   q y and y = y_ do not. The framer should keep q y /\ y = y_
   and drop p x. *)
lemma gP_mixed (y_ : int) :
  hoare[M.g : 0 < x /\ p x /\ q y /\ y = y_ ==> 0 < res /\ q y_].
proof.
proc=> /=.
ecall ->> (fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*           Test 3: No frameable conjuncts                            *)
(* ================================================================== *)

(* The entire precondition depends on x (which is written by the call).
   The framed part should be true. *)
lemma gP_noframe : hoare[M.g : 0 < x ==> 0 < res].
proof.
proc=> /=.
ecall ->> (fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*          Test 4: Backward ecall regression                          *)
(* ================================================================== *)

(* Backward ecall requires the call to be the last instruction
   (after proc absorbs `return`). *)
module B4 = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc g(x : int) : int = {
    x <@ f(x);
    return x;
  }
}.

lemma b4_fP : hoare[B4.f : 0 <= x ==> 1 <= res].
proof. by proc; auto=> /#. qed.

lemma b4_fPx (x_ : int) : hoare[B4.f : 0 <= x_ /\ x = x_ ==> res = x_ + 1].
proof. by proc; auto. qed.

(* Backward ecall (the existing behavior, no ->>) should still work
   after the refactoring. *)
lemma b4_gP : hoare[B4.g : 0 <= x ==> 1 <= res].
proof.
proc=> /=.
ecall (b4_fP).
by auto=> &hr |> /#.
qed.

(* Backward ecall with a parameterized contract. *)
lemma b4_gPx : hoare[B4.g : 0 <= x ==> 1 <= res].
proof.
proc=> /=.
ecall (b4_fPx x).
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*     Test 5: Forward ecall on equiv goals (negative test)            *)
(* ================================================================== *)

equiv gE : M.g ~ M.g : ={x, y} ==> ={res}.
proof.
proc.
fail ecall ->> (fP).
abort.

(* ================================================================== *)
(*         Test 6: Multiple forward ecalls in sequence                 *)
(* ================================================================== *)

module M6 = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc h(x : int, y : int) : int = {
    x <@ f(x);
    y <@ f(y);
    return x + y;
  }
}.

lemma m6_fP : hoare[M6.f : 0 <= x ==> 1 <= res].
proof. by proc; auto => /#. qed.

(* Two forward ecalls in sequence: the first consumes x <@ f(x),
   the second consumes y <@ f(y). *)
lemma m6_hP : hoare[M6.h : 0 <= x /\ 0 <= y ==> 2 <= res].
proof.
proc=> /=.
ecall ->> (m6_fP); first by move=> &hr |> /#.
ecall ->> (m6_fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*              Test 7: Tuple lvalue                                    *)
(* ================================================================== *)

module M7 = {
  proc f(x : int) : int * int = {
    return (x, x + 1);
  }

  proc g(x : int) : int = {
    var y : int;
    (x, y) <@ f(x);
    return x + y;
  }
}.

lemma m7_fP : hoare[M7.f : 0 <= x ==> 0 <= fst res /\ fst res < snd res].
proof. by proc; auto => /#. qed.

(* Forward ecall with a tuple lvalue: res is substituted by (x, y).
   The postcondition 0 <= fst res /\ fst res < snd res becomes
   0 <= x /\ x < y after substitution. *)
lemma m7_gP : hoare[M7.g : 0 <= x ==> 0 < res].
proof.
proc=> /=.
ecall ->> (m7_fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*           Test 8: Global variable framing                           *)
(* ================================================================== *)

module M8 = {
  var g : int

  proc f(x : int) : int = {
    return x + 1;
  }

  proc h(x : int) : int = {
    x <@ f(x);
    return x + g;
  }
}.

lemma m8_fP : hoare[M8.f : 0 <= x ==> 1 <= res].
proof. by proc; auto => /#. qed.

(* M8.g is not in the write set of f (f has no side effects on globals),
   so the conjunct 0 < M8.g is automatically framed. *)
lemma m8_hP : hoare[M8.h : 0 <= x /\ 0 < M8.g ==> 1 < res].
proof.
proc=> /=.
ecall ->> (m8_fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.

(* ================================================================== *)
(*  Test 9: Exception postcondition in forward mode (negative test)    *)
(* ================================================================== *)

exception exn.

module M9 = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc g(x : int) : int = {
    x <@ f(x);
    return x;
  }
}.

(* A contract with a non-trivial exception postcondition *)
lemma m9_fP_exn (x_ : int) :
  hoare[M9.f : x = x_ ==> res = x_ + 1 | exn => x_ = 0].
proof. by proc; auto. qed.

(* Forward ecall requires an empty exception postcondition.
   Using a contract with exceptions should fail. *)
lemma m9_gP : hoare[M9.g : 0 <= x ==> 0 < res].
proof.
proc=> /=.
fail ecall ->> (m9_fP_exn x).
abort.

(* ================================================================== *)
(*   Test 10: Contract for wrong procedure (negative test)             *)
(* ================================================================== *)

module M10 = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc h(x : int) : int = {
    return x + 2;
  }

  proc g(x : int) : int = {
    x <@ h(x);
    return x;
  }
}.

lemma m10_fP : hoare[M10.f : 0 <= x ==> 1 <= res].
proof. by proc; auto => /#. qed.

(* The contract is for M10.f but the call targets M10.h.
   check_contract_type should reject this. *)
lemma m10_gP : hoare[M10.g : 0 <= x ==> 0 < res].
proof.
proc=> /=.
fail ecall ->> (m10_fP).
abort.
