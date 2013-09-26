require import Int.

theory T.
  op myop : int -> int -> int.

  op dup = myop.

  axiom A :  forall x y, myop x y = myop y x.
end T.

clone T as U with op myop(x, y) = x + y.

clone T as V with op myop(x, y) <- x + y.

clone T as W with op myop <- lambda (x, y), x + y.

print axiom W.A.
