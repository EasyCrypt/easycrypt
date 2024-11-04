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

  op touint : bv -> int.
  op tosint : bv -> int.
  op ofint : int -> bv.

  op get (b: bv) (n: int) : bool = 
    List.nth false (tolist b) n.

  op msb (b: bv) : bool = 
    List.nth false (tolist b) (size - 1).

  axiom size_tolist (bv : bv): List.size (tolist bv) = size.

  axiom tolistP (bv : bv) : oflist (tolist bv) = bv.
  axiom oflistP (xs : bool list) : size xs = size => tolist (oflist xs) = xs.

  axiom touintP (bv : bv) :
    touint bv = bs2int (tolist bv).

  axiom tosintP (bv : bv) :
    (size = 1) \/
    let v = bs2int (tolist bv) in
    if (msb bv) then
      tosint bv = v - 2^size
    else 
      tosint bv = v.

  axiom ofintP (i : int) :
    ofint i = oflist (int2bs size i).
end BV.

(* ==================================================================== *)
abstract theory A.
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
      touint (bvadd bv1 bv2) = (touint bv1 + touint bv2) %% 2^BV.size.
  end BVAdd.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSub.
    clone import BV.
  
    op bvsub : bv -> bv -> bv.
  
    axiom bvsubP (bv1 bv2 : bv) :
      touint (bvsub bv1 bv2) = (touint bv1 - touint bv2) %% 2^BV.size.
  end BVSub.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVMul.
    clone import BV.
  
    op bvmul : bv -> bv -> bv.
  
    axiom bvmulP (bv1 bv2 : bv) :
      touint (bvmul bv1 bv2) = (touint bv1 * touint bv2) %% 2^BV.size.
  end BVMul.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVUDiv.
    clone import BV.
  
    op bvudiv : bv -> bv -> bv.
  
    axiom bvudivP (bv1 bv2 : bv) : touint bv2 <> 0 =>
      touint (bvudiv bv1 bv2) = touint bv1 %/ touint bv2.
  end BVUDiv.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVURem.
    clone import BV.
  
    op bvurem : bv -> bv -> bv.
  
    axiom bvuremP (bv1 bv2 : bv) :
      touint (bvurem bv1 bv2) = touint bv1 %% touint bv2.
  end BVURem.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSHL.
    clone import BV.
  
    op bvshl : bv -> bv -> bv.
  
    axiom bvshlP (bv1 bv2 : bv) : touint (bvshl bv1 bv2) =
      (touint bv1 * 2 ^ (touint bv2)) %% (2 ^ BV.size).
  end BVSHL.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVSHR.
    clone import BV.
  
    op bvshr : bv -> bv -> bv.
  
    axiom bvshrP (bv1 bv2 : bv) : touint (bvshr bv1 bv2) =
      touint bv1 %/ 2 ^ (touint bv2).
  end BVSHR.
  
  (* ------------------------------------------------------------------ *)
  abstract theory BVASHR.
    clone import BV.
  
    op bvashr : bv -> bv -> bv.
  
    axiom bvashrP (bv1 bv2 : bv) : tosint (bvashr bv1 bv2) =
      tosint bv1 %/ 2 ^ (touint bv2).
  end BVASHR.

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
      BV1.touint (ult bv1 bv2) <> 0 <=> (BV2.touint bv1 < BV2.touint bv2).
  end BVULt.

(* ------------------------------------------------------------------ *)
  abstract theory BVSLt.
    clone import BV as BV1 with op size <= 1.
    clone import BV as BV2.
  
    op slt : BV2.bv -> BV2.bv -> BV1.bv.
  
    axiom bvsltP (bv1 bv2 : BV2.bv) :
      BV1.touint (slt bv1 bv2) <> 0 <=> (BV2.tosint bv1 < BV2.tosint bv2).
  end BVSLt.


  (* ------------------------------------------------------------------ *)
  abstract theory BVULe.
    clone import BV as BV1 with op size <= 1.
    clone import BV as BV2.
  
    op ule : BV2.bv -> BV2.bv -> BV1.bv.
  
    axiom bvuleP (bv1 bv2 : BV2.bv) :
      BV1.touint (ule bv1 bv2) <> 0 <=> (BV2.touint bv1 <= BV2.touint bv2).
  end BVULe.

(* ------------------------------------------------------------------ *)
  abstract theory BVSLe.
    clone import BV as BV1 with op size <= 1.
    clone import BV as BV2.
  
    op sle : BV2.bv -> BV2.bv -> BV1.bv.
  
    axiom bvsleP (bv1 bv2 : BV2.bv) :
      BV1.touint (sle bv1 bv2) <> 0 <=> (BV2.tosint bv1 <= BV2.tosint bv2).
  end BVSLe.


  (* ------------------------------------------------------------------ *)
  abstract theory BVZExtend.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] le_size : BV1.size <= BV2.size.

    op bvzextend : BV1.bv -> BV2.bv.

    axiom bvzextendP (bv : BV1.bv) :
      BV1.touint bv = BV2.touint (bvzextend bv).
  end BVZExtend.

(* ------------------------------------------------------------------ *)
  abstract theory BVSExtend.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] le_size : BV1.size <= BV2.size.

    op bvsextend : BV1.bv -> BV2.bv.

    axiom bvsextendP (bv : BV1.bv) :
      BV1.tosint bv = BV2.tosint (bvsextend bv).
  end BVSExtend.

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
  abstract theory BVExtract.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] le_size : BV2.size <= BV1.size.

    op bvextract : BV1.bv -> int -> BV2.bv.

    axiom bvextractP (bv : BV1.bv) (base : int) : base + BV2.size <= BV1.size =>
      take BV2.size (drop base (BV1.tolist bv)) = BV2.tolist (bvextract bv base).
  end BVExtract.

  (* ------------------------------------------------------------------ *)
  abstract theory BVASliceGet.
    clone BV as BV1.
    clone BV as BV2.
    clone A.

    axiom [bydone] le_size : BV2.size <= BV1.size * A.size.

    op bvasliceget : (BV1.bv A.t) -> int -> BV2.bv.

    (* We need the definition of target semantic to allow
       a rewrite without conditions, but the binding just
       needs to be correct for valid offsets *)
    axiom bvaslicegetP (arr : BV1.bv A.t) (offset : int) :
    0 <= offset <= BV1.size * A.size - BV2.size =>
    let base = List.flatten (List.map BV1.tolist (A.to_list arr)) in
    let ret = bvasliceget arr offset in
       forall i, 0 <= i < BV2.size =>
       nth false (BV2.tolist ret) i = nth false (take BV2.size (List.drop offset base)) i.
  end BVASliceGet.

  (* ------------------------------------------------------------------ *)
  abstract theory BVASliceSet.
    clone BV as BV1.
    clone BV as BV2.
    clone A.

    axiom [bydone] le_size : BV2.size <= BV1.size * A.size.

    op bvasliceset : (BV1.bv A.t) -> int -> (BV2.bv) -> BV1.bv A.t.

    (* We need the definition of target semantic to allow
       a rewrite without conditions, but the binding just
       needs to be correct for valid offsets *)
    axiom bvaslicesetP (arr : BV1.bv A.t) (offset : int) (bv: BV2.bv): 
       0 <= offset <= BV1.size * A.size - BV2.size  =>
      let input_arr = List.flatten (List.map (BV1.tolist) (A.to_list arr)) in
      let input_bv = BV2.tolist bv in
      let output_arr = List.flatten (List.map BV1.tolist (A.to_list (bvasliceset arr offset bv))) in
      forall i, 0 <= i < BV1.size * A.size =>
      List.nth false output_arr i = 
      if offset <= i < offset + BV2.size then
        List.nth false input_bv (i - offset)
      else
        List.nth false input_arr i.
  end BVASliceSet.

  (* ------------------------------------------------------------------ *)
  abstract theory BVConcat.
    clone BV as BV1.
    clone BV as BV2.
    clone BV as BV3.

    axiom [bydone] eq_size : BV1.size + BV2.size = BV3.size.

    op bvconcat : BV1.bv -> BV2.bv -> BV3.bv.

    axiom bvconcatP (bv1 : BV1.bv) (bv2 : BV2.bv) :
      BV3.tolist (bvconcat bv1 bv2) = BV1.tolist bv1 ++ BV2.tolist bv2.
  end BVConcat.

  (* ------------------------------------------------------------------ *)
  abstract theory BVInit.
    clone BV as BV1.
    clone BV as BV2.

    axiom [bydone] size_1 : BV1.size = 1.

    op bvinit : (int -> BV1.bv) -> BV2.bv.

    axiom bvinitP (f : int -> BV1.bv) : 
      BV2.tolist (bvinit f) = List.flatten (List.mkseq (fun i => BV1.tolist (f i)) BV2.size).
  end BVInit.

  (* ------------------------------------------------------------------ *)
  abstract theory BVAInit.
    clone BV.
    clone A.

    op bvainit : (int -> BV.bv) -> BV.bv A.t.

    axiom bvainitP (f : int -> BV.bv) : 
      A.to_list (bvainit f) = List.mkseq (fun i => (f i)) A.size.
  end BVAInit.

  (* ------------------------------------------------------------------ *)
  abstract theory BVMap.
    clone BV as BV1.
    clone BV as BV2.
    clone A.

    op map (f: BV1.bv -> BV2.bv) (abv: BV1.bv A.t) : BV2.bv A.t.
    
    print List.map.

    axiom mapP (f: BV1.bv -> BV2.bv) (abv: BV1.bv A.t) : 
      A.to_list (map f abv) = List.map f (A.to_list abv).
  end BVMap.

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

