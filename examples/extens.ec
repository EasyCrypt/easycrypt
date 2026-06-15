(* ==================================================================== *)
(* The [extens] tactical.                                               *)
(*                                                                       *)
(* [extens] performs an extensionality-style case split, enumerating a  *)
(* finite quantity and running an inner tactic on each case. Two shapes: *)
(*                                                                       *)
(*   - [all P (iota_ start len)]   (no binder): one subgoal [P i] per    *)
(*     integer i in [start, start+len);                                  *)
(*   - [hoare[M.f : pre ==> post]] with a binder [v] naming a bound      *)
(*     bitstring program variable: 2^n subgoals, one per concrete value  *)
(*     of v.                                                             *)
(*                                                                       *)
(* The usual use is [extens [v] : circuit] — replacing one input by a    *)
(* concrete constant per case lets circuit translation succeed where a   *)
(* whole-input translation might not. See doc/tactics/extens.rst.        *)
(*                                                                       *)
(* As elsewhere, the [bind] side conditions are admitted where they      *)
(* would need real proofs; the tactic invocations are real and run.      *)
(* ==================================================================== *)
require import AllCore List QFABV IntDiv.

(* -------------------------------------------------------------------- *)
(* An abstract 8-bit word with xor. *)
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

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

(* -------------------------------------------------------------------- *)
(* [bool] as a size-1 bitstring: the per-bit output type that the array- *)
(* style bit-access operator [get] returns. *)
op bool2bits (b : bool) : bool list = [b].
op bits2bool (b : bool list) : bool = List.nth false b 0.
op i2b : int -> bool.
op b2si (b : bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize gt0_size    by done.
realize size_tolist by auto.
realize tolistP     by auto.
realize oflistP     by rewrite /bool2bits /bits2bool; smt(size_eq1).
realize touintP     by admit.
realize tosintP     by done.
realize ofintP      by admit.

(* The bit-access operator: [a.[i]] is bit i of [a]. [extens] over an
   [iota_] range needs this to express the per-bit subgoals. *)
op "_.[_]" : W8 -> int -> bool.
bind op [W8 & bool] "_.[_]" "get".
realize le_size  by auto.
realize eq1_size by auto.
realize bvgetP   by admit.

(* ==================================================================== *)
(* Variant: list enumeration over [iota_]                               *)
(*                                                                       *)
(* [all (fun i => P i) (iota_ 0 8)] splits into the 8 subgoals [P 0],    *)
(* ..., [P 7], each discharged by the inner tactic.                      *)
(* ==================================================================== *)

(* Trivial per-bit reflexivity (the canonical first example). *)
lemma ext_refl (a : W8) : all (fun i => a.[i] = a.[i]) (iota_ 0 8).
proof. extens : circuit. qed.

(* A real per-bit fact: xor is bitwise-commutative at every index. *)
lemma ext_xor_comm (a b : W8) :
  all (fun i => (a +^ b).[i] = (b +^ a).[i]) (iota_ 0 8).
proof. extens : circuit. qed.

(* ==================================================================== *)
(* Variant: Hoare-triple enumeration over a bitstring variable          *)
(*                                                                       *)
(* The binder [a] picks the program variable to enumerate; since         *)
(* [a : W8] is 8 bits, this produces 2^8 = 256 subgoals in which [a] is   *)
(* replaced by each concrete [of_int i]. The inner tactic closes each.   *)
(* ==================================================================== *)

module M = {
  proc xor (a b : W8) : W8 = {
    var c : W8;
    c <- a +^ b;
    return c;
  }
}.

(* Inner tactic = circuit: each per-constant case is a circuit goal. *)
lemma ext_hoare_circuit (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. by proc; extens [a] : circuit. qed.

(* Inner tactic = circuit simplify then trivial. *)
lemma ext_hoare_simplify (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc; extens [a] : by circuit simplify; trivial. qed.

(* Inner tactic need not be circuit at all: any tactic closing each
   per-constant case works (here a plain weakest-precondition pass). *)
lemma ext_hoare_wp (a_ b_ : W8) :
  hoare[M.xor : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc; extens [a] : (wp; skip; smt()). qed.
