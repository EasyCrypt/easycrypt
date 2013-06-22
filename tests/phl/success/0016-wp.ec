module type Orcl = {
  fun o (x:int) : int
}.

module type Adv (O:Orcl) = {
  fun a (x:int) : int { O.o }
}.

module A (O:Orcl) = {
  var x : int
  fun a (w:int) : int = {
    var r : int;
    r = O.o(w);
    return r;
  }
}.

module X : Orcl = {
  fun o (x:int) : int = { return x; }
}.

module Y : Orcl = {
  fun o (x:int) : int = { return x; }
}.

module B = A(X).
module C = A(Y).

module M =  { 
  fun f (w:int) : unit = {
    B.x = 1;
    C.x = 2;
  }
}.

lemma foo : hoare [M.f : true ==> B.x = 2 /\ C.x = 2].
 fun.
 wp.
 skip.
 simplify.
 trivial.
save.