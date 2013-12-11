module type T = {
proc f() : bool
}.

module M1(A:T) = {
proc f() : bool = {
var c : bool;
var r : bool;
c = true;
r  = A.f();
return c = r;
}
}.

module M2(A:T) = {
proc f() : bool = {
var c : bool;
var r : bool;
r  = A.f();
c = true;
return c = r;
}
}.

lemma test :
forall (A<:T),
equiv [M1(A).f ~ M2(A).f : true ==> res{1} = res{2}].
proof.
intros A.
proc.
swap{1} 1 1.
admit.
save.