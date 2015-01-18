(* -------------------------------------------------------------------- *)
require import Int.

theory T.
  type t.
end T.

clone T as U with type t <- int.

op myop : int = 0.

(* -------------------------------------------------------------------- *)
theory V.
  type 'a t.

  op x : 'a t.
end V.

clone V as W with type 'b t <- 'b * 'b.

op myop2 : int * int = W.x.

(* -------------------------------------------------------------------- *)
theory OP.
  op myop : int -> int.

  axiom L (x : int): myop x = x.
end OP.

clone OP as OP' with
  op myop <- fun (x : int), x
  proof L by (move=> x; reflexivity).

(* -------------------------------------------------------------------- *)
theory PR.
  pred mypr : int.

  axiom L (x : int): mypr x => (x = 2).
end PR.

clone PR as PR' with
  pred mypr <- fun (x : int), x = 2
  proof L by done.
