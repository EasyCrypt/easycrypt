require import Int.
require import List.
module M = { 
  fun f (x:int) : int = { 
    var b : bool;
    b = if x = 0 then true else false;
    b = if x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0 then true else false;
    b = if x = 0 then x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0 else x + x + x + x + x + x + x = 0 + 0 + 0 + 0 + 0;
    if (b) b = false;
    else b = true;
    return 0;
  }
}.

module M1 = {
  fun f (x:int) : int = {
    var b : bool;
    var y : int;
    y = let w = 0 in x + w;
    return y;
}

type t1 = int * int.
print type t1.
type ('a,'b,'c,'d) t2 = ('a * int * int * int * int * int * int * int * int * int * int * int * int * int * int * ('b * int) * 'c *'d) list.
print type t2.
type t3 = (int * int, int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int,int * int, int * int ) t2.
print type t3.
type t4 = int -> int -> (int * int, int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int,int * int, int * int ) t2.
print type t4.
lemma foo : hoare [M.f : true ==> true]
proof.
  fun. 
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

    fun g(x : int) : unit = {
    }

    fun f(x : int) : int = {
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
