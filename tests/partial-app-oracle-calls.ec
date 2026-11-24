(* Regression for #1175: partially applying a functor must keep the
   calls to its remaining parameters, including calls to an applied
   parameter such as `S(M).kg`. Dropping them let `B (D : T) (S : Sch)`
   be cast to (or instantiate) an adversary type forbidding those calls. *)
require import AllCore.

module type T   = { }.
module type Sch (X : T) = { proc kg() : unit }.
module type Adv (S : Sch) = { proc run() : unit }.

module M : T = { }.

module St (X : T) = {
  var c : int
  proc kg() : unit = { c <- c + 1; }
}.

(* Without a leading parameter: rejected. *)
fail module (B' : Adv) (S : Sch) = {
  proc run() : unit = { S(M).kg(); }
}.

(* With a leading parameter: must be rejected as well. *)
fail module (B (D : T) : Adv) (S : Sch) = {
  proc run() : unit = { S(M).kg(); }
}.

(* A leading parameter alone does not make the cast fail. *)
module (C (D : T) : Adv) (S : Sch) = {
  proc run() : unit = { }
}.

(* Without the cast, `B(M)` must not instantiate an `Adv`. *)
module B (D : T) (S : Sch) = {
  proc run() : unit = { S(M).kg(); }
}.

lemma frame (A <: Adv {-St}) n :
  hoare [A(St).run : St.c = n ==> St.c = n].
proof. by proc (St.c = n). qed.

lemma ok : hoare [C(M, St).run : St.c = 0 ==> St.c = 0].
proof. exact (frame (C(M)) 0). qed.

lemma bad : hoare [B(M, St).run : St.c = 0 ==> St.c = 0].
proof. fail exact (frame (B(M)) 0). abort.
