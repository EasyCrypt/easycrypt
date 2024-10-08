(* -------------------------------------------------------------------- *)
require import AllCore List Int IntDiv BitEncoding.
(* - *) import BS2Int. 

(* -------------------------------------------------------------------- *)
abstract theory BV.
  op size : int.

  axiom gt0_size : 0 < size.

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

(* -------------------------------------------------------------------- *)
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
