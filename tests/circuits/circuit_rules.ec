(* The [circuit], [circuit simplify] and [extens] rules: every form and
   the error paths. *)

require import AllCore List QFABV.

type W8.

op to_bits : W8 -> bool list.
op from_bits : bool list -> W8.
op of_int : int -> W8.
op to_uint : W8 -> int.
op to_sint : W8 -> int.

bind bitstring to_bits from_bits to_uint to_sint of_int W8 8.
realize gt0_size by admit.
realize tolistP by admit.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.
realize size_tolist by admit.

op (+^) : W8 -> W8 -> W8.
bind op W8 (+^) "xor".
realize bvxorP by admit.

op "_.[_]" : W8 -> int -> bool.

exception oops.

module M = {
  proc test (a : W8, b : W8) = {
    var c : W8;
    c <- a +^ b;
    return c;
  }

  proc swp (a : W8, b : W8) = {
    var c : W8;
    c <- b +^ a;
    return c;
  }

  proc cnt (a : W8, n : int) = {
    var c : W8;
    c <- a;
    n <- n + 1;
    return c;
  }

  proc rse (a : W8) = {
    if (a = of_int 0) { raise oops; }
    return a;
  }
}.

(* -------------------------------------------------------------------- *)
(* [circuit]: hoare, equiv and formulas. *)
lemma hoare_circuit (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. by proc; circuit. qed.

lemma equiv_circuit : equiv[M.test ~ M.swp : ={a, b} ==> ={res}].
proof. by proc; circuit. qed.

lemma fol_circuit (w1 w2 : W8) : w1 +^ w2 = w2 +^ w1.
proof. by circuit. qed.

(* The decision fails. *)
lemma hoare_circuit_invalid (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_].
proof. proc. fail circuit. abort.

lemma equiv_circuit_invalid : equiv[M.test ~ M.swp : ={a} ==> ={res}].
proof. proc. fail circuit. abort.

lemma fol_circuit_invalid (w1 w2 : W8) : w1 +^ w2 = w1.
proof. fail circuit. abort.

(* The translation fails ([int] is not bound). *)
lemma hoare_circuit_untranslatable (a_ : W8) :
  hoare[M.cnt : a_ = a ==> res = a_].
proof. proc. fail circuit. abort.

lemma fol_circuit_untranslatable (w : W8) : w.[0] = w.[1].
proof. fail circuit. abort.

(* Exceptional postconditions are not supported. *)
lemma hoare_circuit_exn (a_ : W8) :
  hoare[M.test : a_ = a ==> true | oops => true].
proof. proc. fail circuit. abort.

(* -------------------------------------------------------------------- *)
(* [circuit simplify]. *)
lemma hoare_circuit_simplify (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_ /\ (res = a_ \/ true)].
proof. by proc; circuit simplify. qed.

lemma hoare_circuit_simplify_exn (a_ : W8) :
  hoare[M.test : a_ = a ==> true | oops => true].
proof. proc. fail circuit simplify. abort.

lemma hoare_circuit_simplify_untranslatable (a_ : W8) :
  hoare[M.cnt : a_ = a ==> res = a_].
proof. proc. fail circuit simplify. abort.

(* -------------------------------------------------------------------- *)
(* [extens]: hoare (enumeration of a program variable) and formulas
   ([all p (iota_ s n)]). *)
lemma hoare_extens (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. by proc; extens [a] : circuit. qed.

lemma fol_extens : all (fun i => 0 <= i) (iota_ 3 5).
proof. by extens : trivial. qed.

lemma fol_extens_empty : all (fun (i : int) => false) (iota_ 3 0).
proof. by extens : trivial. qed.

(* Wrong goal shapes. *)
lemma hoare_extens_novar (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc. fail extens : circuit. abort.

lemma fol_extens_var : all (fun i => 0 <= i) (iota_ 3 5).
proof. fail extens [a] : trivial. abort.

lemma fol_extens_notint : all (fun (b : bool) => b \/ !b) [true; false].
proof. fail extens : trivial. abort.

lemma fol_extens_list : all (fun i => 0 <= i) [1; 2].
proof. fail extens : trivial. abort.

lemma fol_extens_start (s : int) : all (fun i => 0 <= i - s) (iota_ s 5).
proof. fail extens : trivial. abort.

lemma fol_extens_len (n : int) : all (fun i => 0 <= i) (iota_ 0 n).
proof. fail extens : trivial. abort.

(* The variable is not in the memory, or its type is not bound. *)
lemma hoare_extens_unknown (a_ b_ : W8) :
  hoare[M.test : a_ = a /\ b_ = b ==> res = a_ +^ b_].
proof. proc. fail extens [z] : circuit. abort.

lemma hoare_extens_unbound (a_ : W8) :
  hoare[M.cnt : a_ = a ==> res = a_].
proof. proc. fail extens [n] : circuit. abort.

lemma hoare_extens_exn (a_ : W8) :
  hoare[M.test : a_ = a ==> true | oops => true].
proof. proc. fail extens [a] : circuit. abort.

(* The tactic fails on, or does not close, an instance. *)
lemma fol_extens_fails : all (fun i => i <> 5) (iota_ 3 5).
proof. fail extens : (move=> /=; done). abort.

lemma fol_extens_open : all (fun i => i <> 5) (iota_ 3 5).
proof. fail extens : idtac. abort.
