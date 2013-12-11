
require import Int.

module type ADV = {
proc main() : unit {*}
}.

module type O = {
proc init() : unit
proc get() : int
}.

module O1 : O = {
var x : int
proc init() : unit = {
x = 0;
}
proc get() : int = {
return x;
}
}.

module O2 : O = {
var x : int
proc init() : unit = {
x = 0;
}
proc get() : int = {
return x;
}
}.

module G(Adv : ADV, O : O) = {
proc main() : bool = {
var y : int;
O.init();
Adv.main();
y = O.get();
return y = 0;
}
}.

lemma G_main :
forall (Adv <: ADV{O1, O2}),
equiv[G(Adv, O1).main ~ G(Adv, O2).main : true ==> ={res}].
proof.
intros Adv.
proc.
call (_ : O1.x{1} = O2.x{2}).
call (_ : O1.x{1} = O2.x{2}).
inline O1.init O2.init; wp; skip; trivial.
qed.

(* if Adv can write O1.x or O2.x, this shouldn't hold: *)

lemma G :
forall (Adv <: ADV) &m,
Pr[G(Adv, O1).main() @ &m : res] = Pr[G(Adv, O2).main() @ &m : res].
proof.
intros Adv &m.
(* the following shouldn't succeed, as Adv <: ADV, whereas
G_main needs Adv <: ADV{O1, O2} *)
equiv_deno (G_main Adv).
trivial. trivial.
qed.