require int.
import  int.

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
