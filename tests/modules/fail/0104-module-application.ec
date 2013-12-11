module type Adv = {
  proc a (x:int) : int {} 
}.

module Test (A:Adv) = { 
  proc main(x:int) : int = { 
    var r : int;
    r  = A.a(x);
    return r;
  }
}.

module A = {
  proc b (x:int) : int = { return x; }
}.

module M = Test(A).
