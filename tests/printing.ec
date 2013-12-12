require import Int.
require import List.
theory T.
module type I = {
  proc g (x:int) : int
}.

module M(U:I) = { 
  proc f (x y : int) : int = { 
    var b : bool;
    b = if x = 0 then true else false;
    b = if x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0 then true else false;
    b = if x = 0 then x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0 else x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0;
    if (b) b = false;
    else b = true;
    return 0;
  }
}.
end T.
 print theory T. 

cnst c : int -> int -> int = (+).
print op c.
op p (x x:int) : int = x + x.
print op p.

lemma foo : let x = 1 + 1 in x = x.
proof -strict.
 intros x.

op p1 : (int, int) -> int.
print op p1.

theory T1.
 type t = int.
end T1.

theory T2.
type t = T1.t.
end T2.
import T1.
print type T2.t.
type t = T2.t.
print type T2.t.


module M1 = {

  proc f (x:int) : int = {
    var b : bool;
    var y : int;
    y = let w = 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +0 + 0 + 0  in x + w;
    return y;
  }

}.

op p20 : int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int.

lemma toto1 : 
  p (p20 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1) 
    (p20 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1) = 1.
proof -strict.

lemma toto : forall x, p (x + x + x + x + x + x + x + x + x + x + x + x ) (x + x + x + x+ x) = x.
proof -strict.
(*
Require Import ZArith.
Open Scope Z_scope.
Parameter p : Z -> Z -> Z -> Z.
Lemma foo : forall (b:bool) x, 
 p 
  (if b then x + x + x + x + x + x + x + x + x + x + x + x + x 
   else x + x + x + x + x + x + x + x + x + x + x + x + x) 
 ( x + x + x + x+ x + x+ x+ x+x + x + x + x+ x + x+ x+ x+x + x + x + 
   x+ x + x+ x+ x+x + x + x + x+ x + x+ x+ x+ x) x = 
  x + x + x + x + x + x + x + x + x + x + x + x.
*)

lemma foo1 : forall x, (x+x) + x = x + (x + x).
proof -strict.

lemma foo2 : (true => true => true) => true => true => true => true=> true => true => true => true => true => true.
proof -strict.

lemma foo : hoare [M1.f : true ==> true /\ true  /\ true  /\ true  /\ true  /\ true  /\ true  /\ true].
proof -strict.
  proc. 

type t1 = int * int.
print type t1.
type ('a,'b,'c,'d) t2 = ('a * int * int * int * int * int * int * int * int * int * int * int * int * int * int * ('b * int) * 'c *'d) list.
print type t2.
type t3 = (int * int, int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int,int * int, int * int ) t2.
print type t3.
type t4 = int -> int -> (int * int, int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int,int * int, int * int ) t2.
print type t4.
lemma foo : hoare [M.f : true ==> true].
proof -strict.
  proc. 
print type int.

theory T.
  type t1.
  type t2 = int.
  type 'a u.

  theory U.
    type k.
    type k'.
  end U.

  cnst myop0 : int.
  op   myop1 : int -> int.
  op   myop2 : int * int -> int.

  op eqxx : int -> bool.

  op foo : 'a -> 'a.

  op myrop1 (x : int) : int * int =
    (let y = x in if eqxx(y) then y else y, 0).

  pred p0 : ().
  pred p1 : bool.
  pred p2 : (int * int).        

  export U.

  module type A = {
  }.

  module type I(A : A) = {
  }.

  module M = {
    var x : int
    var y : int

    proc g(x : int) : unit = {
    }

    proc f(x : int) : int = {
      var b  : bool;
      var l1 : int;
      var l2 : int;
      var l3 : int;

      assert (true);

      g(3);

      l2 = (l1 + l1) + l1;
      l2 = l1 + (l1 + l1);
      l2 = l1 * (l1 + l1);
      l2 = (l1 * l1) + l1;
      l2 = l1 + (l1 * l1);
      l2 = (l1 + l1) * l1;

      b = (l1 <= l2) || b;
      b = l1 + l2 <= l2 + l1;

      l1 = (l1 + (if b then l1 else l1)) * l2;

      l2 = if b then l1 else (l1 + l2);
      l2 = (if b then l1 else l1) + l2;

      l2 = l1 + (if b then l1 else l2);

      l1 = b ? (b ? l1 : l1) : (b ? l1 : l1);

      l1 = b ? l1 : (l1 + l2);
      l1 = (b ? l1 : l1) + l2;

      if (true)
        l1 = 1;
      else
        l2 = 2;

      while (true) {}

      return x;
    }
  }.

  module M' = M.
end T.

print theory T.
