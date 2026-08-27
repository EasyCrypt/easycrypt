(* Module overriding in clones is sound exactly for *stateless* modules: a
   module that declares no program variable (transitively through its
   sub-modules) has an empty own-glob, so once its components are AST-equal to
   the target's it is indiscernible from it. Calling external stateful modules
   and taking module parameters is fine; owning a variable never is. *)

require import AllCore.

(* ==================================================================== *)
(*                              positive                                *)
(* ==================================================================== *)

(* -- P1: plain stateless module, the three override modes -------------- *)
abstract theory P1.
  module M = {
    proc f (x : int) : int = { return x + 1; }
  }.

  lemma f_h (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.

  lemma f_ph (n : int) : phoare [M.f : x = n ==> res = n + 1] = 1%r.
  proof. by proc; skip. qed.
end P1.

module P1N = { proc f (x : int) : int = { return x + 1; } }.

clone P1 as P1Clear with module M <- P1N.
clone P1 as P1Keep  with module M <= P1N.
clone P1 as P1Alias with module M  = P1N.

lemma p1_clear (n : int) : hoare [P1N.f : x = n ==> res = n + 1].
proof. by apply (P1Clear.f_h n). qed.

lemma p1_keep (n : int) : phoare [P1Keep.M.f : x = n ==> res = n + 1] = 1%r.
proof. by apply (P1Keep.f_ph n). qed.

lemma p1_alias (n : int) : hoare [P1Alias.M.f : x = n ==> res = n + 1].
proof. by apply (P1Alias.f_h n). qed.

(* -- P2: stateless module writing an *external* stateful module -------- *)
module S = { var x : int }.

abstract theory P2.
  module M = { proc f (n : int) : unit = { S.x <- n; } }.

  lemma f_spec : hoare [M.f : n = 3 ==> S.x = 3].
  proof. by proc; auto. qed.
end P2.

module P2N = { proc f (n : int) : unit = { S.x <- n; } }.

clone P2 as P2C with module M <- P2N.

lemma p2_use : hoare [P2N.f : n = 3 ==> S.x = 3].
proof. by apply P2C.f_spec. qed.

(* -- P3: stateless functor, lemma quantifying over a restricted adversary *)
module type Adv = { proc a (x : int) : int }.

abstract theory P3.
  module G (A : Adv) = {
    proc f (x : int) : int = { var r; r <@ A.a(x); return r; }
  }.

  lemma g_spec (A <: Adv{-S}) : hoare [G(A).f : S.x = 0 ==> true].
  proof. by proc; call (: true). qed.
end P3.

module P3H (A : Adv) = {
  proc f (x : int) : int = { var r; r <@ A.a(x); return r; }
}.

clone P3 as P3C with module G <- P3H.

lemma p3_use (A <: Adv{-S}) : hoare [P3H(A).f : S.x = 0 ==> true].
proof. by apply (P3C.g_spec A). qed.

(* -- P3': the functor parameter may be alpha-renamed in the target ----- *)
module P3H' (B : Adv) = {
  proc f (x : int) : int = { var r; r <@ B.a(x); return r; }
}.

clone P3 as P3C' with module G <- P3H'.

lemma p3'_use (A <: Adv{-S}) : hoare [P3H'(A).f : S.x = 0 ==> true].
proof. by apply (P3C'.g_spec A). qed.

(* -- P4: nested stateless sub-module ----------------------------------- *)
abstract theory P4.
  module M = {
    module Sub = { proc g (x : int) : int = { return x + 1; } }

    proc f (x : int) : int = { var r; r <@ Sub.g(x); return r; }
  }.

  lemma f_spec (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; inline *; auto. qed.
end P4.

module P4N = {
  module Sub = { proc g (x : int) : int = { return x + 1; } }

  proc f (x : int) : int = { var r; r <@ Sub.g(x); return r; }
}.

clone P4 as P4C with module M <- P4N.

lemma p4_use (n : int) : hoare [P4N.f : x = n ==> res = n + 1].
proof. by apply (P4C.f_spec n). qed.

(* -- P5: theory override, the theory holding only stateless modules ---- *)
theory P5Src.
  module type I = { proc g (x : int) : int }.
  module K = { proc f (x : int) : int = { return x + 1; } }.
end P5Src.

abstract theory P5.
  theory Sub.
    module type I = { proc g (x : int) : int }.
    module K = { proc f (x : int) : int = { return x + 1; } }.
  end Sub.

  lemma k_spec (n : int) : hoare [Sub.K.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P5.

clone P5 as P5C with theory Sub <- P5Src.

lemma p5_use (n : int) : hoare [P5Src.K.f : x = n ==> res = n + 1].
proof. by apply (P5C.k_spec n). qed.

(* -- P6: the target is itself a module alias (checked with ~body:false) - *)
module P6Z = { proc f (x : int) : int = { return x + 1; } }.
module P6Y = P6Z.

abstract theory P6.
  module M = { proc f (x : int) : int = { return x + 1; } }.

  lemma f_spec (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P6.

clone P6 as P6C with module M <- P6Y.

lemma p6_use (n : int) : hoare [P6Y.f : x = n ==> res = n + 1].
proof. by apply (P6C.f_spec n). qed.

(* -- P6': the target is an alias of a functor application -------------- *)
module type P6I = { proc a () : unit }.
module P6A = { proc a () : unit = { } }.
module P6F (X : P6I) = { proc f () : unit = { X.a(); } }.
module P6R = P6F(P6A).

abstract theory P6'.
  module M = { proc f () : unit = { P6A.a(); } }.

  lemma f_spec : hoare [M.f : true ==> true].
  proof. by proc; inline *; auto. qed.
end P6'.

clone P6' as P6C' with module M <- P6R.

lemma p6'_use : hoare [P6R.f : true ==> true].
proof. by apply P6C'.f_spec. qed.

(* -- P7: the module lives deep in a sub-theory path -------------------- *)
abstract theory P7.
  theory A. theory B.
    module M = { proc f (x : int) : int = { return x + 1; } }.
  end B. end A.

  lemma f_spec (n : int) : hoare [A.B.M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P7.

module P7N = { proc f (x : int) : int = { return x + 1; } }.

clone P7 as P7C with module A.B.M <- P7N.

lemma p7_use (n : int) : hoare [P7N.f : x = n ==> res = n + 1].
proof. by apply (P7C.f_spec n). qed.

(* -- P8: the module comes from an abstract sub-theory of the clonee ---- *)
abstract theory P8Inner.
  module M = { proc f (x : int) : int = { return x + 1; } }.

  lemma f_spec (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P8Inner.

abstract theory P8.
  clone import P8Inner as I.
end P8.

module P8N = { proc f (x : int) : int = { return x + 1; } }.

clone P8 as P8C with module I.M <- P8N.

lemma p8_use (n : int) : hoare [P8N.f : x = n ==> res = n + 1].
proof. by apply (P8C.I.f_spec n). qed.

(* -- P9: an alias and a caller inside the clonee follow the override --- *)
abstract theory P9.
  module M = { proc f (x : int) : int = { return x + 1; } }.
  module P = M.
  module Q = { proc h (x : int) : int = { var r; r <@ M.f(x); return r; } }.

  lemma p_spec (n : int) : hoare [P.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.

  lemma q_spec (n : int) : hoare [Q.h : x = n ==> res = n + 1].
  proof. by proc; inline *; auto. qed.
end P9.

module P9N = { proc f (x : int) : int = { return x + 1; } }.

clone P9 as P9C with module M <- P9N.

lemma p9_use1 (n : int) : hoare [P9C.P.f : x = n ==> res = n + 1].
proof. by apply (P9C.p_spec n). qed.

lemma p9_use2 (n : int) : hoare [P9C.Q.h : x = n ==> res = n + 1].
proof. by apply (P9C.q_spec n). qed.

(* -- P10: the overridden module is itself an alias inside the clonee --- *)
abstract theory P10.
  module Base = { proc f (x : int) : int = { return x + 1; } }.
  module M    = Base.

  lemma f_spec (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P10.

module P10N = { proc f (x : int) : int = { return x + 1; } }.

clone P10 as P10C with module M <- P10N.

lemma p10_use (n : int) : hoare [P10N.f : x = n ==> res = n + 1].
proof. by apply (P10C.f_spec n). qed.

(* -- P11: `glob` of a stateless module survives the override ----------- *)
abstract theory P11.
  module M = { proc f (x : int) : int = { return x + 1; } }.

  lemma f_spec (g : glob M) (n : int) :
    hoare [M.f : x = n /\ (glob M) = g ==> res = n + 1 /\ (glob M) = g].
  proof. by proc; skip. qed.
end P11.

module P11N = { proc f (x : int) : int = { return x + 1; } }.

clone P11 as P11C with module M <- P11N.

lemma p11_use (g : glob P11N) (n : int) :
  hoare [P11N.f : x = n /\ (glob P11N) = g ==> res = n + 1 /\ (glob P11N) = g].
proof. by apply (P11C.f_spec g n). qed.

(* -- P12: two stateless modules may be identified with the same target - *)
abstract theory P12.
  module M1 = { proc f (x : int) : int = { return x + 1; } }.
  module M2 = { proc f (x : int) : int = { return x + 1; } }.

  lemma eq_spec : equiv [M1.f ~ M2.f : ={x} ==> ={res}].
  proof. by proc; skip. qed.
end P12.

module P12N = { proc f (x : int) : int = { return x + 1; } }.

clone P12 as P12C with module M1 <- P12N, module M2 <- P12N.

lemma p12_use : equiv [P12N.f ~ P12N.f : ={x} ==> ={res}].
proof. by apply P12C.eq_spec. qed.

(* -- P13: a module override combines with `rename` and a modtype override *)
module type P13I = { proc a () : unit }.

abstract theory P13.
  module type J = { proc a () : unit }.
  module M = { proc f (x : int) : int = { return x + 1; } }.

  lemma foo (n : int) : hoare [M.f : x = n ==> res = n + 1].
  proof. by proc; skip. qed.
end P13.

module P13N = { proc f (x : int) : int = { return x + 1; } }.

clone P13 as P13C with
  module type J <- P13I,
  module M       = P13N
  rename [module] "M" as "MM" "foo" as "bar".

lemma p13_use (n : int) : hoare [P13C.MM.f : x = n ==> res = n + 1].
proof. by apply (P13C.bar n). qed.

(* -- P14: a module kept by `clone include ... <=` stays overridable ---- *)
module P14N = { proc f (x : int) : int = { return x + 1; } }.
module P14P = { proc f (x : int) : int = { return x + 1; } }.

theory P14Mid.
  clone include P1 with module M <= P14N.
end P14Mid.

lemma p14_use (n : int) : hoare [P14N.f : x = n ==> res = n + 1].
proof. by apply (P14Mid.f_h n). qed.

clone P14Mid as P14C with module M <- P14P.

(* -- P15: theory override carrying a stateless functor ----------------- *)
theory P15Src.
  module G (A : Adv) = {
    proc f (x : int) : int = { var r; r <@ A.a(x); return r; }
  }.
end P15Src.

abstract theory P15.
  theory Sub.
    module G (A : Adv) = {
      proc f (x : int) : int = { var r; r <@ A.a(x); return r; }
    }.
  end Sub.

  lemma g_spec (A <: Adv) : hoare [Sub.G(A).f : true ==> true].
  proof. by proc; call (: true). qed.
end P15.

clone P15 as P15C with theory Sub <- P15Src.

lemma p15_use (A <: Adv) : hoare [P15Src.G(A).f : true ==> true].
proof. by apply (P15C.g_spec A). qed.

(* ==================================================================== *)
(*                              negative                                *)
(* ==================================================================== *)

(* -- N1: the #380 unsoundness (oskgo's `module A2.M <- A1.M`) ---------- *)
abstract theory N1A.
  module M = {
    var x : int

    proc f () : unit = { x <- 1; }
  }.
end N1A.

theory N1B.
  clone N1A as A1.
  clone N1A as A2.

  (* A1.M and A2.M own *distinct* variables; identifying them proves False. *)
  lemma sep : hoare [A1.M.f : A2.M.x = 0 ==> A2.M.x = 0].
  proof. by proc; auto. qed.
end N1B.

expect fail "module `A2.M' declares state and cannot be overridden"
clone N1B as N1B1 with module A2.M <- A1.M.

(* -- N1': the same unsoundness through Unruh's `theory A2 <- A1` ------- *)
expect fail "Cannot override theory `A2': contains stateful module `A2.M'"
clone N1B as N1B2 with theory A2 <- A1.

(* -- N2: stateless source, stateful target ----------------------------- *)
abstract theory N2.
  module M = { proc f () : unit = { } }.
end N2.

module N2N = { var x : int  proc f () : unit = { } }.

expect fail "module `N2N' declares state and cannot be overridden"
clone N2 as N2C with module M <- N2N.

(* -- N3: state hidden in a nested sub-module --------------------------- *)
abstract theory N3.
  module M = {
    module Sub = { var x : int  proc g () : unit = { } }

    proc f () : unit = { Sub.g(); }
  }.
end N3.

module N3N = {
  module Sub = { var x : int  proc g () : unit = { } }

  proc f () : unit = { Sub.g(); }
}.

expect fail "module `M.Sub' declares state and cannot be overridden"
clone N3 as N3C with module M <- N3N.

(* -- N3': state three sub-modules deep --------------------------------- *)
abstract theory N3'.
  module M = {
    module A = { module B = { var x : int  proc g () : unit = { } } }

    proc f () : unit = { }
  }.
end N3'.

module N3'N = {
  module A = { module B = { var x : int  proc g () : unit = { } } }

  proc f () : unit = { }
}.

expect fail "module `M.A.B' declares state and cannot be overridden"
clone N3' as N3'C with module M <- N3'N.

(* -- N3'': state reached through a sub-module aliasing a stateful module  *)
module N3''S = { var x : int  proc g () : unit = { x <- 1; } }.

abstract theory N3''.
  module M = { module Sub = N3''S  proc f () : unit = { Sub.g(); } }.
end N3''.

module N3''N = { module Sub = N3''S  proc f () : unit = { Sub.g(); } }.

expect fail "module `M.Sub' declares state and cannot be overridden"
clone N3'' as N3''C with module M <- N3''N.

(* -- N3''': state behind a restricting signature is still state -------- *)
abstract theory N3'''.
  module M : P13I = { var x : int  proc a () : unit = { x <- 1; } }.
end N3'''.

module N3'''N : P13I = { var x : int  proc a () : unit = { x <- 1; } }.

expect fail "module `M' declares state and cannot be overridden"
clone N3''' as N3'''C with module M <- N3'''N.

(* -- N3'''': a top-level alias of a stateful module is stateful -------- *)
module N3AliasS = { var x : int  proc f () : unit = { x <- 1; } }.
module N3AliasY = N3AliasS.

abstract theory N3Alias.
  module M = { proc f () : unit = { } }.
end N3Alias.

expect fail "module `N3AliasY' declares state and cannot be overridden"
clone N3Alias as N3AliasC with module M <- N3AliasY.

(* -- N4: same signature, different body -------------------------------- *)
abstract theory N4.
  module M = { proc f (x : int) : int = { return x + 1; } }.
end N4.

module N4N = { proc f (x : int) : int = { return x + 2; } }.

expect fail "module `M` is incompatible"
clone N4 as N4C with module M <- N4N.

(* -- N4': same names, different number of procedures ------------------- *)
abstract theory N4'.
  module M = { proc f () : unit = { }  proc g () : unit = { } }.
end N4'.

module N4'N = { proc f () : unit = { } }.

expect fail "module `M` is incompatible"
clone N4' as N4'C with module M <- N4'N.

(* -- N4'': parameter arity mismatch (non-functor vs functor) ----------- *)
abstract theory N4''.
  module M = { proc f () : unit = { } }.
end N4''.

module N4''N (A : Adv) = { proc f () : unit = { } }.

expect fail "module `M` is incompatible"
clone N4'' as N4''C with module M <- N4''N.

(* -- N4''': same arity, different parameter module type ---------------- *)
module type N4'''J = { proc b () : unit }.

abstract theory N4'''.
  module M (A : Adv) = { proc f () : unit = { } }.
  lemma foo (A <: Adv) : hoare [M(A).f : true ==> true] by proc.
end N4'''.

module N4'''N (A : N4'''J) = { proc f () : unit = { } }.

expect fail "module `M` is incompatible"
clone N4''' as N4'''C with module M <- N4'''N.

expect fail "module `M` is incompatible"
clone N4''' as N4'''D with module M <- N4'N.

(* -- N5: the target is a `declare module` ------------------------------ *)
abstract theory N5.
  module M = { proc a () : unit = { } }.
end N5.

section.
declare module N5D <: P13I.

expect fail "module `N5D' is not a concrete top-level module"
clone N5 as N5C with module M <- N5D.

end section.

(* -- N6: theory override with a stateful module inside ----------------- *)
theory N6Src.
  module K = { var y : int  proc f () : unit = { } }.
end N6Src.

abstract theory N6.
  theory Sub.
    module K = { var y : int  proc f () : unit = { } }.
  end Sub.
end N6.

expect fail "Cannot override theory `Sub': contains stateful module `Sub.K'"
clone N6 as N6C with theory Sub <- N6Src.

(* -- N6': theory override whose *target* module is the stateful one ---- *)
theory N6'Src.
  module K = { var y : int  proc f () : unit = { } }.
end N6'Src.

abstract theory N6'.
  theory Sub.
    module K = { proc f () : unit = { } }.
  end Sub.
end N6'.

expect fail "module `Top.N6'Src.K' declares state and cannot be overridden"
clone N6' as N6'C with theory Sub <- N6'Src.

(* -- N7: the same module overridden twice ------------------------------ *)
abstract theory N7.
  module M = { proc f () : unit = { } }.
end N7.

module N7N = { proc f () : unit = { } }.
module N7P = { proc f () : unit = { } }.

expect fail "the module `M' is instantiate twice"
clone N7 as N7C with module M <- N7N, module M <- N7P.

(* -- N8: unknown source, unknown target -------------------------------- *)
abstract theory N8.
  module M = { proc f () : unit = { } }.
end N8.

module N8N = { proc f () : unit = { } }.

expect fail "unknown module `NoSuchModule'"
clone N8 as N8C1 with module NoSuchModule <- N8N.

expect fail "unknown module `NoSuchModule'"
clone N8 as N8C2 with module M <- NoSuchModule.

(* -- N9: a module cleared by `<-` is gone from the clone --------------- *)
clone N8 as N9C with module M <- N8N.

expect fail "unknown module `M'"
clone N9C as N9D with module M <- N8N.

(* -- N10: a functor owning a variable is stateful ---------------------- *)
abstract theory N10.
  module G (A : Adv) = { var x : int  proc f () : unit = { x <- 1; } }.
end N10.

module N10H (A : Adv) = { var x : int  proc f () : unit = { x <- 1; } }.

expect fail "module `G' declares state and cannot be overridden"
clone N10 as N10C with module G <- N10H.

(* -- N11: a section-local target may not leak into a global lemma ------ *)
section.
local module N11N = { proc f (x : int) : int = { return x + 1; } }.

expect fail "lemma/axiom f_h cannot depend on local module N11N"
clone P1 as N11C with module M <- N11N.

end section.
