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

  op toint : bv -> int.
  op ofint : int -> bv.

  op get (b: bv) (n: int) : bool = 
    List.nth false (tolist b) n.

  axiom size_tolist (bv : bv): List.size (tolist bv) = size.

  axiom tolistP (bv : bv) : oflist (tolist bv) = bv.
  axiom oflistP (xs : bool list) : size xs = size => tolist (oflist xs) = xs.

  axiom tointP (bv : bv) :
    toint bv = bs2int (tolist bv).

  axiom ofintP (i : int) :
    ofint i = oflist (int2bs size i).
end BV.

(* ==================================================================== *)
theory A.
  op size : int.

  axiom [bydone] gt0_size : 0 < size.

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
  abstract theory BVULt.
    clone import BV as BV1 with op size <= 1.
    clone import BV as BV2.
  
    op ult : BV2.bv -> BV2.bv -> BV1.bv.
  
    axiom bvultP (bv1 bv2 : BV2.bv) :
      BV1.toint (ult bv1 bv2) <> 0 <=> (BV2.toint bv1 < BV2.toint bv2).
  end BVULt.

  (* ------------------------------------------------------------------ *)
  abstract theory BVULe.
    clone import BV as BV1 with op size <= 1.
    clone import BV as BV2.
  
    op ule : BV2.bv -> BV2.bv -> BV1.bv.
  
    axiom bvuleP (bv1 bv2 : BV2.bv) :
      BV1.toint (ule bv1 bv2) <> 0 <=> (BV2.toint bv1 <= BV2.toint bv2).
  end BVULe.

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

  (* ------------------------------------------------------------------ *)
  abstract theory BVA2B.
    clone BV as BV1.
    clone BV as BV2.
    clone A.

    axiom [bydone] size_ok : A.size * BV2.size = BV1.size.

    op a2b : BV2.bv A.t -> BV1.bv.

    axiom a2bP (bva : BV2.bv A.t) :
      flatten (map BV2.tolist (A.to_list bva)) = BV1.tolist (a2b bva).
  end BVA2B.

  (* ------------------------------------------------------------------ *)
  abstract theory BVB2A.
    clone BV as BV1.
    clone BV as BV2.
    clone A.

    axiom [bydone] size_ok : A.size * BV2.size = BV1.size.

    op b2a : BV1.bv -> BV2.bv A.t.

    axiom b2aP (bva : BV1.bv) :
      BV1.tolist bva = flatten (map BV2.tolist (A.to_list (b2a bva))).
  end BVB2A.

  (* ------------------------------------------------------------------ *)
  abstract theory A2B2A.        (* choubidoubidou *)
    clone BV as BV1.
    clone BV as BV2.
    clone import A.

    axiom [bydone] size_ok : A.size * BV2.size = BV1.size.

    clone import BVA2B with
      theory BV1 <- BV1,
      theory BV2 <- BV2,
      theory A   <- A
      proof size_ok by exact/size_ok.

    clone import BVB2A with
      theory BV1 <- BV1,
      theory BV2 <- BV2,
      theory A   <- A
      proof size_ok by exact/size_ok.

    lemma a2bK : cancel a2b b2a.
    proof. admitted.

    lemma b2aK : cancel a2b b2a.
    proof. admitted.
  end A2B2A.
end BVOperators.
