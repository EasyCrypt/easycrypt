(* Declaration builders that FRESHEN parameters must rename idxvars in
   BOTH namespaces (tindex positions and int-typed formula-local
   occurrences), and generated op applications must carry indices:
   axiomatized-by axioms, refinement axioms, and clone-freshened
   indexed lemmas were all born with dangling idents. *)

require import AllCore.

type {n} 'a vec.
op vsize {n} ['a] (v : 'a vec<:n>) : int = n.

(* axiomatized_op: the generated axiom must keep both namespaces linked *)
op double {n} (x : int) : int = x + n axiomatized by doubleE.

expect "* In [lemmas or axioms]:

axiom doubleE {n}: forall (x : int), double[:n] x = x + n." by print doubleE.

lemma use_doubleE {k} (x : int) : double[:k] x = x + k.
proof. by smt(doubleE). qed.

lemma vszE {k} ['a] (v : 'a vec<:k>) : vsize v = k.
proof. by rewrite /vsize. qed.

lemma rw_control (v : int vec<:3>) : vsize v = 3.
proof. by rewrite vszE. qed.

(* clone-freshening: an indexed lemma using its index as a term *)
theory U.
  type {n} t.
  op sz {n} (x : t<:n>) : int.
  axiom szE {n} (x : t<:n>) : sz x = n.
end U.

clone U as U2.

lemma use_szE {k} (x : U2.t<:k>) : U2.sz x = k.
proof. by rewrite U2.szE. qed.
