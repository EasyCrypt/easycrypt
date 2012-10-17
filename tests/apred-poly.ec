pred P : 'a list.

axiom P_nil : P([]).
axiom P_cons_0 : forall (l : int list), P(l) => P(0 :: l).
axiom P_cons_false : forall (l : bool list), P(l) => P(false :: l).

lemma L_int  : P([0; 0]).
lemma L_bool : P([false; false]).

unset L_int, L_bool.

lemma L_int_bool : P([0; 0]) && P([false; false]).
