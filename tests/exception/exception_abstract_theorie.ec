require import AllCore.

abstract theory Et.
  type t.

  op test : t -> bool.

  op truc : t -> exn.

  exception et of t.
  exception et2 of t * t.

  print et2.

  module Truc = {
    proc f (x:t):t = {
     if (test x) {raise (et x);}
    return x;
    }
  }.

  axiom hf :  forall (_x :t), hoare [Truc.f : _x = x ==> res = _x | et x => test x = false].
end Et.

require import List.

exception et1 of int.

clone Et as H with
type t <- int.

print H.
print H.truc.
print H.et.
print H.et2.

fail clone Et as H' with
type t <- int,
op et <- et1.

clone Et as H' rename [exception] "et" as "ett".

print H'.

clone Et as H'' rename [op] "t" as "ett".

print H''.
