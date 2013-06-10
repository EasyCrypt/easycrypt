module type Adv = {
  fun a (x:int) : int {} 
}.

module Test (A:Adv) = { 
  fun main(x:int) : int = { 
    var r : int;
    r  = A.a(x);
    return r;
  }
}.

module A = {
  var z : int
  fun b () : unit = { }
  fun a (x:int) : int = { return x; }
}.

module M = Test(A).
