(* -------------------------------------------------------------------- *)
require import AllCore List Int IntDiv BitEncoding.
(* - *) import BS2Int. 

(* ==================================================================== *)
abstract theory BV.
  op size : int.

  axiom [bydone] gt0_size : 0 < size.

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
end BV.

(* ==================================================================== *)
theory BVOperators.
  (* ------------------------------------------------------------------ *)
  abstract theory BVAdd.
    clone import BV.
  
    op bvadd : bv -> bv -> bv.
  
    axiom bvaddP (bv1 bv2 : bv) :
      toint (bvadd bv1 bv2) = (toint bv1 + toint bv2) %% 2^BV.size.
  end BVAdd.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSub.
    clone import BV.
  
    op bvsub : bv -> bv -> bv.
  
    axiom bvsubP (bv1 bv2 : bv) :
      toint (bvsub bv1 bv2) = (toint bv1 - toint bv2) %% 2^BV.size.
  end BVSub.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVMul.
    clone import BV.
  
    op bvmul : bv -> bv -> bv.
  
    axiom bvmulP (bv1 bv2 : bv) :
      toint (bvmul bv1 bv2) = (toint bv1 * toint bv2) %% 2^BV.size.
  end BVMul.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVUDiv.
    clone import BV.
  
    op bvudiv : bv -> bv -> bv.
  
    axiom bvudivP (bv1 bv2 : bv) : toint bv2 <> 0 =>
      toint (bvudiv bv1 bv2) = toint bv1 %/ toint bv2.
  end BVUDiv.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVURem.
    clone import BV.
  
    op bvurem : bv -> bv -> bv.
  
    axiom bvuremP (bv1 bv2 : bv) :
      toint (bvurem bv1 bv2) = toint bv1 %% toint bv2.
  end BVURem.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSHL.
    clone import BV.
  
    op bvshl : bv -> bv -> bv.
  
    axiom bvshlP (bv1 bv2 : bv) : toint (bvshl bv1 bv2) =
      toint bv1 * 2 ^ (toint bv2).
  end BVSHL.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSHR.
    clone import BV.
  
    op bvshr : bv -> bv -> bv.
  
    axiom bvshrP (bv1 bv2 : bv) : toint (bvshr bv1 bv2) =
      toint bv1 %/ 2 ^ (toint bv2).
  end BVSHR.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVAnd.
    clone import BV.
  
    op bvand : bv -> bv -> bv.
  
    axiom bvandP (bv1 bv2 : bv) : tolist (bvand bv1 bv2) =
      map (fun (b : _ * _) => b.`1 /\ b.`2) (zip (tolist bv1) (tolist bv2)).
  end BVAnd.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVOr.
    clone import BV.
  
    op bvor : bv -> bv -> bv.
  
    axiom bvorP (bv1 bv2 : bv) : tolist (bvor bv1 bv2) =
      map (fun (b : _ * _) => b.`1 \/ b.`2) (zip (tolist bv1) (tolist bv2)).
  end BVOr.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVNot.
    clone import BV.
  
    op bvnot : bv -> bv.
  
    axiom bvnotP (bv : bv) : tolist (bvnot bv) =
      map (fun b => !b) (tolist bv).
  end BVNot.

  (* ------------------------------------------------------------------ *)
  abstract theory BVZExtend.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] le_size : BV1.size <= BV2.size.

    op bvzextend : BV1.bv -> BV2.bv.

    axiom bvzextendP (bv : BV1.bv) :
      BV1.toint bv = BV2.toint (bvzextend bv).
  end BVZExtend.

  (* ------------------------------------------------------------------ *)
  abstract theory BVTruncate.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] le_size : BV2.size <= BV1.size.

    op bvtruncate : BV1.bv -> BV2.bv.

    axiom bvtruncateP (bv : BV1.bv) :
      take BV2.size (BV1.tolist bv) = BV2.tolist (bvtruncate bv).
  end BVTruncate.
end BVOperators.

(* ==================================================================== *)
theory A.
  op size : int.

  axiom gt0_size : 0 < size.

  type 'a t.

  op get ['a] : 'a t -> int -> 'a.

  op set ['a] : 'a t -> int -> 'a -> 'a t.

  op to_list ['a] : 'a t -> 'a list.

  axiom tolistP ['a] (a : 'a t) :
    to_list a = mkseq (fun i => get a i) size.

  axiom eqP ['a] (a1 a2 : 'a t) :
        (forall i, 0 <= i < size => get a1 i = get a2 i)
    <=> (a1 = a2).

  axiom get_setP ['a] (a : 'a t) (i j : int) (v : 'a) :
       0 <= i < size
    => 0 <= j < size
    => get (set a j v) i = if i = j then v else get a i.

  axiom get_out ['a] (a1 a2 : 'a t) (i : int) :
    !(0 <= i < size) => get a1 i = get a2 i.
end A.
