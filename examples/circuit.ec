(* ==================================================================== *)
(* Examples for the [circuit] tactic family.                            *)
(*                                                                       *)
(* The [circuit] tactics discharge (or simplify) goals over finite      *)
(* types by translating them into boolean circuits. They rely on the    *)
(* [bind] commands to know how types and operators map to their         *)
(* bit-level counterparts; see doc/tactics/{circuit,bindings}.rst.      *)
(*                                                                       *)
(* To keep the focus on the tactic itself, this file works over an      *)
(* abstract 8-bit word [W8]: the [bind] side conditions (the [realize]  *)
(* lines) are admitted. The tactic invocations below are real and run.  *)
(* ==================================================================== *)
require import AllCore List QFABV IntDiv.

(* -------------------------------------------------------------------- *)
(* An abstract bound word. [bind bitstring] connects the type [W8] to   *)
(* its 8-bit representation; the [realize]s discharge the laws relating *)
(* the conversion operators (admitted here).                            *)
type W8.

op to_bits   : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int    : int -> W8.
op to_uint   : W8 -> int.
op to_sint   : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.

realize gt0_size    by admit.
realize tolistP     by admit.
realize oflistP     by admit.
realize touintP     by admit.
realize tosintP     by admit.
realize ofintP      by admit.
realize size_tolist by admit.

op zero : W8 = of_int 0.

(* Bit-level operators, bound to their circuit gates by name. *)
op (+^) : W8 -> W8 -> W8.   (* xor *)
bind op W8 (+^) "xor".
realize bvxorP by admit.

op (&&&) : W8 -> W8 -> W8.  (* and *)
bind op W8 (&&&) "and".
realize bvandP by admit.

(* An operator with no circuit binding, used to illustrate a failure. *)
op opaque : W8 -> W8.

(* ==================================================================== *)
(* Variant: [circuit] (FOL)                                             *)
(*                                                                       *)
(* On a first-order goal, [circuit] translates the proposition into a   *)
(* circuit and checks that it is identically true.                      *)
(* ==================================================================== *)

(* xor is commutative. *)
lemma xor_comm (a b : W8) : a +^ b = b +^ a.
proof. circuit. qed.

(* xor is associative. *)
lemma xor_assoc (a b c : W8) : (a +^ b) +^ c = a +^ (b +^ c).
proof. circuit. qed.

(* xor with itself is zero. *)
lemma xor_self (a : W8) : a +^ a = zero.
proof. circuit. qed.

(* and distributes over... itself trivially; a small mixed-gate goal. *)
lemma and_comm (a b : W8) : a &&& b = b &&& a.
proof. circuit. qed.

(* ==================================================================== *)
(* Variant: [circuit] (HL)                                              *)
(*                                                                       *)
(* On a Hoare triple, [circuit] translates the precondition, the        *)
(* (assignment-only) program, and the postcondition, then checks the    *)
(* postcondition holds on every input satisfying the precondition.      *)
(* ==================================================================== *)

module M = {
  proc xor (a b : W8) : W8 = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

lemma hl_xor (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc; circuit. qed.

(* The precondition can also constrain the inputs: with [a = b], the
   result [a +^ b] is forced to [zero]. *)
lemma hl_xor_eq : hoare[M.xor : a = b ==> res = zero].
proof. proc; circuit. qed.

(* ==================================================================== *)
(* Variant: [circuit] (rHL)                                             *)
(*                                                                       *)
(* On an equivalence, [circuit] builds an input-to-output map for each  *)
(* program and checks the relational postcondition on every joint       *)
(* initial state satisfying the precondition.                           *)
(* ==================================================================== *)

module N = {
  proc f1 (a b : W8) : W8 = {
    var c : W8;
    c <- a +^ b;
    return c;
  }

  proc f2 (a b : W8) : W8 = {
    var c : W8;
    c <- b +^ a;
    return c;
  }
}.

lemma rhl_xor_comm : equiv[N.f1 ~ N.f2 : ={arg} ==> ={res}].
proof. proc; circuit. qed.

(* ==================================================================== *)
(* Variant: [circuit simplify]                                          *)
(*                                                                       *)
(* Same translation as [circuit] (HL), but instead of closing the goal  *)
(* it rewrites the postcondition with the bit-level equalities and      *)
(* leaves a residual goal for ordinary tactics.                         *)
(* ==================================================================== *)

lemma hl_simplify (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc; circuit simplify; trivial. qed.

(* ==================================================================== *)
(* [proc change circuit]                                                *)
(*                                                                       *)
(* Rewrite a run of statements into an equivalent block, discharging    *)
(* the equivalence with the circuit checker. Only variables live after  *)
(* the region need agree.                                               *)
(* ==================================================================== *)

lemma pcc_swap (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  (* replace [c <- a +^ b] by the commuted [c <- b +^ a] *)
  proc change circuit 1 + 1 { c <- b +^ a; }.
  circuit.
qed.

(* The optional [bindings] introduce fresh locals visible only inside   *)
(* the replacement block. *)
lemma pcc_fresh_local (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof.
  proc.
  proc change circuit [d : W8] 1 + 1 { d <- a; c <- d +^ b; }.
  circuit.
qed.

(* ==================================================================== *)
(* Failure modes                                                        *)
(* ==================================================================== *)

(* A genuinely false postcondition: the circuit is not a tautology. *)
lemma fail_false (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ zero].
proof.
  proc.
  fail circuit.
abort.

(* An operator with no circuit binding: translation raises an error. *)
lemma fail_translate (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = opaque (a_ +^ b_)].
proof.
  proc.
  fail circuit.
abort.
