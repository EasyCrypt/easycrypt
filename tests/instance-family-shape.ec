(* Every instance records ONE shared instantiation (indices and
   types), and typed selection checks each operator resolves to
   exactly it.  Mixing shapes inside one instance is rejected with a
   located diagnostic naming both operators; a UNIFORM non-trivial
   shape (all operators over the carrier's predecessor) is fine. *)

require import AllCore Ring.

type {n} t.
op zer  {n} : t<:n>.
op one  {n} : t<:n>.
op add  {n} (x y : t<:n>) : t<:n>.
op mul  {n} (x y : t<:n>) : t<:n>.
op opp  {n} (x : t<:n>) : t<:n>.

(* predecessor-shaped zero *)
op zp {n} : t<:n+1>.

(* MIXED shapes: [zp] resolves at [k], [add] at [k+1] -- rejected.
   (message: "operators `add' (Top.add) and `rzero' (Top.zp) resolve
   to different instantiations at the carrier: all instance operators
   must share one" -- asserted manually, hierror embeds locations) *)
fail instance ring [shpbad] with {k} t<:k+1>
  op rzero = zp
  op rone  = one
  op add   = add
  op mul   = mul
  op opp   = opp.

(* UNIFORMLY predecessor-shaped: every operator over t<:j+1>, all
   resolving at [k] -- accepted, and the tactic fires. *)
op onep {n} : t<:n+1>.
op addp {n} (x y : t<:n+1>) : t<:n+1>.
op mulp {n} (x y : t<:n+1>) : t<:n+1>.
op oppp {n} (x : t<:n+1>) : t<:n+1>.

axiom A_addr0 {n} (x : t<:n+1>) : addp x zp = x.
axiom A_addrA {n} (x y z : t<:n+1>) : addp x (addp y z) = addp (addp x y) z.
axiom A_addrC {n} (x y : t<:n+1>) : addp x y = addp y x.
axiom A_addrN {n} (x : t<:n+1>) : addp x (oppp x) = zp.
axiom A_mulr1 {n} (x : t<:n+1>) : mulp x onep = x.
axiom A_mulrA {n} (x y z : t<:n+1>) : mulp x (mulp y z) = mulp (mulp x y) z.
axiom A_mulrC {n} (x y : t<:n+1>) : mulp x y = mulp y x.
axiom A_mulrDl {n} (x y z : t<:n+1>) :
  mulp (addp x y) z = addp (mulp x z) (mulp y z).

instance ring [shp] with {k} t<:k+1>
  op rzero = zp
  op rone  = onep
  op add   = addp
  op mul   = mulp
  op opp   = oppp

  proof addr0     by exact (A_addr0[:k])
  proof addrA     by exact (A_addrA[:k])
  proof addrC     by exact (A_addrC[:k])
  proof addrN     by exact (A_addrN[:k])
  proof mulr1     by exact (A_mulr1[:k])
  proof mulrA     by exact (A_mulrA[:k])
  proof mulrC     by exact (A_mulrC[:k])
  proof mulrDl    by exact (A_mulrDl[:k]).

lemma shp_test {k} (x y : t<:k+1>) :
  addp x (addp y (oppp x)) = y.
proof. by ring [shp]. qed.

lemma shp_concrete (x : t<:8>) : addp x zp = x.
proof. by ring [shp]. qed.

(* ------------------------------------------------------------------ *)
(* Arity mismatches are subsumed by the same gates:
   - an op whose extra index is UNCONSTRAINED by the required type
     fails the closed-check ("cannot infer the instantiation of
     operator ... from the carrier type");
   - an op whose indices all resolve but to a DIFFERENT-LENGTH
     instantiation fails the uniformity check. *)
op add2 {a b} (x : t<:a>) (y : t<:b>) : t<:a>.

fail instance ring [arbad1] with {k} t<:k>
  op rzero = zer  op rone = one  op add = add2  op mul = mul  op opp = opp.

op addu {a b} (x : t<:a>) (y : t<:a>) : t<:a>.

fail instance ring [arbad2] with {k} t<:k>
  op rzero = zer  op rone = one  op add = addu  op mul = mul  op opp = opp.
