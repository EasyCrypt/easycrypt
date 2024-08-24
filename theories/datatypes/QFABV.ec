require import AllCore List Int IntDiv BitEncoding.
(* - *) import BS2Int. 

abstract theory BV.
  op size : int.

  axiom ge0_size : 0 < size.

  type bv.

  op tolist : bv -> bool list.
  op oflist : bool list -> bv.

  op get (b: bv) (n: int) : bool = 
	List.nth false (tolist b) n.

  op toint (b: bv) : int = 
    bs2int (tolist b).

  axiom size_tolist (bv : bv): List.size (tolist bv) = size.

  axiom tolistK (bv : bv) : oflist (tolist bv) = bv.
  axiom oflistK (xs : bool list) : size xs = size => tolist (oflist xs) = xs.

  abstract theory BVAdd.
    op bvadd : bv -> bv -> bv.

    axiom bvaddP (bv1 bv2 : bv) :
     toint (bvadd bv1 bv2) = (toint bv1 + toint bv2) %% 2^size.
  end BVAdd.

  abstract theory BVSub.
    op bvsub : bv -> bv -> bv.

    axiom bvsubP (bv1 bv2 : bv) :
     toint (bvsub bv1 bv2) = (toint bv1 - toint bv2) %% 2^size.
  end BVSub.
end BV.


(* type w16. *)

(* clone import BV as BV_W16 *)
(*   with op size <= 16, type bv <- w16 proof * by admit. *)

(* op add16 : w16 -> w16 -> w16. *)

(* clone BV_W16.BVAdd as BV_W16_BVAdd *)
(*   with op bvadd <= add16 proof * by admit. *)

