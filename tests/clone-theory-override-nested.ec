(* A theory override of a nested theory, `theory B.A <- T`, concerns
   `B.A` only. It used to be recorded under its last component `A`: an
   unrelated top-level theory `A` lost its import, and a second override
   `theory A <- T'` was rejected by an assertion failure. *)

require import AllCore.

theory Arr.
  type 'a t.
  op get : 'a t -> int -> 'a.
end Arr.

theory Arr2.
  type u.
end Arr2.

abstract theory Base.
  theory A.
    type 'a t.
    op get : 'a t -> int -> 'a.
  end A.
end Base.

abstract theory Leaf.
  clone import Base as B.

  theory A.
    type u.
  end A.

  op h : A.u -> int B.A.t.
end Leaf.

(* The top-level `A` is still imported. *)
clone Leaf as L1 with theory B.A <- Arr.

expect "
theory L1.
  (* import *) theory B.
                 (* no import *) theory A = Arr.
               end B.
  
  (* import *) theory A.
                 (* import *) type u.
               end A.
  
  (* import *) op h : A.u -> int Arr.t.
end L1.
" by print theory L1.

(* `B.A` and `A` are overridden independently. *)
clone Leaf as L2 with theory B.A <- Arr, theory A <- Arr2.

expect "
(* L2.h *)
op h : Arr2.u -> int Arr.t.
" by print op L2.h.

(* The cleared theories are replaced with aliases to their targets. *)
op w1 : L2.A.u -> Arr2.u = fun x => x.
op w2 : int L2.B.A.t -> int Arr.t = fun x => x.

(* Overriding the same theory twice is an error. *)
expect fail "the theory `B.A' is instantiate twice"
clone Leaf as L3 with theory B.A <- Arr, theory B.A <- Arr.
