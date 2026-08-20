(* Overriding indexed types and operators in cloning (#1065, comment 5):

     clone U with type {n} 'a foo = 'a vec<:n>,
                  op   f {n} ['a] (x : 'a) (xs : 'a vec<:n>) = cons[:n] x xs.
*)

type {n} 'a vec.

op cons {n} ['a] (x : 'a) (xs : 'a vec<:n>) : 'a vec<:n+1>.

theory U.
  type {n} 'a foo.

  op f {n} ['a] : 'a -> 'a foo<:n> -> 'a foo<:n+1>.

  axiom fP {n} ['a] (x : 'a) (xs : 'a foo<:n>) : f x xs = f x xs.

  pred p {n} ['a] : 'a foo<:n>.
end U.

(* type override only *)
clone U as U1 with
  type {n} 'a foo = 'a vec<:n>.

(* type + op + pred overrides, alias mode *)
pred nonempty {n} ['a] (xs : 'a vec<:n>) = ! (n = 0).

clone U as U2 with
  type {n} 'a foo = 'a vec<:n>,
  op f {n} ['a] (x : 'a) (xs : 'a vec<:n>) = cons[:n] x xs,
  pred p {n} ['a] (xs : 'a vec<:n>) = nonempty xs.

(* the overridden operator unfolds to its definition *)
lemma f_is_cons {n} ['a] (x : 'a) (xs : 'a vec<:n>) :
  U2.f x xs = cons x xs.
proof. trivial. qed.

expect "* In [operators, predicates or exceptions]:

pred p {n} ['a] (xs : 'a vec<:n>) = nonempty xs." by print U2.p.

(* inline mode *)
clone U as U3 with
  type {n} 'a foo <- 'a vec<:n>,
  op f {n} ['a] (x : 'a) (xs : 'a vec<:n>) <- cons[:n] x xs.

(* the inlined operator is substituted in the clone's axioms *)
expect "* In [lemmas or axioms]:

(* U3.fP *)
axiom fP {n} ['a]: forall (x : 'a) (xs : 'a vec<:n>), cons x xs = cons x xs." by print U3.fP.

(* index-arity mismatch in an override is rejected *)
theory V.
  type {n m} 'a bar.
  op g {n m} ['a] : 'a bar<:n, m> -> 'a bar<:n, m>.
end V.

fail clone V as V1 with
  type {n} 'a bar = 'a vec<:n>.
