require import AllCore Distr DBool.

(* ================================================================== *)
(* Backward ecall on bdHoare/phoare goals.                            *)
(*                                                                    *)
(* Only lossless [= 1%r] goals with a lossless [= 1%r] contract are   *)
(* supported: the construction routes the suffix call through a       *)
(* trivial probability split that is sound only at bound 1%r.         *)
(* ================================================================== *)

module M = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc g(x : int) : int = {
    var y, r : int;
    y <- x + 1;
    r <@ f(y);
    return r;
  }

  proc h(x : int) : int = {
    var b : bool;
    b <$ dbool;
    return b ? 1 : 0;
  }

  proc gh(x : int) : int = {
    var r : int;
    r <@ h(x);
    return r;
  }
}.

(* ================================================================== *)
(*           Test 1: Backward ecall, lossless contract                *)
(* ================================================================== *)
lemma f_spec : phoare[ M.f : x = 1 ==> res = 2 ] = 1%r.
proof. by proc; auto. qed.

(* The call is the last instruction, with a non-empty deterministic
   prefix.  ecall consumes the call and leaves the (lossless) prefix. *)
lemma g_spec : phoare[ M.g : x = 0 ==> res = 2 ] = 1%r.
proof.
proc.
ecall (f_spec).
auto.
qed.

(* ================================================================== *)
(*        Test 2: Forward ecall on phoare (negative test)             *)
(* ================================================================== *)
lemma g_fwd : phoare[ M.g : x = 0 ==> res = 2 ] = 1%r.
proof.
proc.
fail ecall ->> (f_spec).
abort.

(* ================================================================== *)
(*       Test 3: side annotation on phoare (negative test)            *)
(* ================================================================== *)
lemma g_side : phoare[ M.g : x = 0 ==> res = 2 ] = 1%r.
proof.
proc.
fail ecall{1} (f_spec).
abort.

(* ================================================================== *)
(*   Test 4: non-[= 1%r] goal is rejected up-front (negative test)    *)
(* ================================================================== *)
lemma h_le : phoare[ M.h : true ==> res = 1 ] <= (1%r / 2%r).
proof. admit. qed.

(* The goal bound is [<= 1/2], not [= 1%r]: the goal guard fires
   before the construction reaches t_call. *)
lemma gh_le : phoare[ M.gh : true ==> res = 1 ] <= (1%r / 2%r).
proof.
proc.
fail ecall (h_le).
abort.

(* ================================================================== *)
(*   Test 5: non-[= 1%r] contract is rejected up-front (neg. test)    *)
(* ================================================================== *)

(* The goal is lossless [= 1%r] but the contract is [<= 1/2]: the
   contract guard fires rather than failing opaquely inside apply. *)
lemma gh_eq : phoare[ M.gh : true ==> res = 1 ] = 1%r.
proof.
proc.
fail ecall (h_le).
abort.
