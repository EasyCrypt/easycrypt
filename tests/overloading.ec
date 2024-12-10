require import AllCore List.

theory T.
  op o : int.
  op a : int -> int -> int.
end T.

theory U.
  op o : bool.
  op a : bool -> bool -> bool.
end U.

import T U.

op foo : int -> unit.

op bar = foo o.

op plop1 = foldr a false [].

op plop2 = foldr (fun x => a x) false [].

op plop3 = foldr (fun x y => a x y) false [].

