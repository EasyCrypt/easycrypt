(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdOrder StdBigop.
require (*--*) Bigop.
(*---*) import IntID IntOrder Bigint.

(* This lemma ensure the correctness of our rules for seq, wp ... *)
lemma subrK (x y : xint) : is_inf x \/ is_int y => (x - y) + y = x.
proof. case y => //; case x => //= *; ring. qed.

(* -------------------------------------------------------------------- *)
lemma add0x : left_id '0 xadd.
proof. by case. qed.

lemma addx0 : right_id '0 xadd.
proof. by case. qed.

hint simplify [reduce] add0x, addx0.

lemma addxA : associative xadd.
proof. by case=> [x|] [y|] [z|] => //=; rewrite addrA. qed.

lemma addxC : commutative xadd.
proof. by case=> [x|] [y|] => //=; rewrite addrC. qed.

(* -------------------------------------------------------------------- *)
lemma mul1x : left_id '1 xmul.
proof. by case. qed.

lemma mulx1 : right_id '1 xmul.
proof. by case. qed.

lemma mulxA : associative xmul.
proof. by case=> [x|] [y|] [z|] => //=; rewrite mulrA. qed.

lemma mulxC : commutative xmul.
proof. by case=> [x|] [y|] => //=; rewrite mulrC. qed.

(* -------------------------------------------------------------------- *)

lemma xaddInfx (x:xint) : Inf + x = Inf.
proof. by case: x. qed.

lemma xaddxInf (x:xint) : x + Inf = Inf.
proof. by case: x. qed.

lemma xmulInfx (x:xint) : Inf * x = Inf.
proof. by case: x. qed.

lemma xmulxInf (x:xint) : x * Inf = Inf.
proof. by case: x. qed.

hint simplify xaddInfx, xaddxInf, xmulInfx, xmulxInf.

(* -------------------------------------------------------------------- *)
op xle (x y : xint) =
  with x = N x, y = N y => (x <= y)
  with x = N x, y = Inf => true
  with x = Inf, y = N y => false
  with x = Inf, y = Inf => true.

abbrev (<=) = xle.

lemma lexx : reflexive (<=).
proof. by case. qed.

lemma lexx_rw (x y : xint) : x = y => x <= y.
proof. by move=> ->; apply lexx. qed.

hint simplify lexx_rw.

lemma lex_anti (x y : xint) : x <= y <= x => x = y.
proof. by case: x y => [x|] [y|] //=; apply: ler_anti. qed.

lemma lex_trans : transitive (<=).
proof. by case=> [x|] [y|] [z|] //=; apply: ler_trans. qed.

lemma lex_inf (x : xint) : x <= Inf.
proof. by case: x. qed.

lemma lex_add2r (x1 x2 y : xint) :
  x1 <= x2 => x1 + y <= x2 + y.
proof.
by case: x1 x2 y => [x1|] [x2|] [y|] //=; apply: ler_add2r.
qed.

lemma is_int_le x y : x <= y => is_int y => is_int x.
proof. by case: x => //; case: y. qed.

lemma lex_add2l (x1 x2 y : xint) :
  x1 <= x2 => y + x1 <= y + x2.
proof. by rewrite !(@addxC y) &(lex_add2r). qed.

op xmax (x y : xint) = 
  with x = N x, y = N y => N (max x y)
  with x = N _, y = Inf => Inf
  with x = Inf, y = N _ => Inf
  with x = Inf, y = Inf => Inf.

lemma sub_completness (t1 t2 t:xint) : 
   t1 + t2 <= t <=>
   t1 <= t - t2 /\ (is_int t2 \/ is_inf t).
proof.
  case: t t1 t2 => [i | ] [i1 | ] [i2 | ] //=; smt().
qed.

(* -------------------------------------------------------------------- *)
theory Bigxint.
clone include Bigop
  with type t <- xint,
         op Support.idm <- ('0),
         op Support.(+) <- xadd
  proof *.

realize Support.Axioms.addmA by exact/addxA.
realize Support.Axioms.addmC by exact/addxC.
realize Support.Axioms.add0m by exact/add0x.

lemma nosmt big_morph_N (P : 'a -> bool) (f : 'a -> int) s:
  big P (fun i => N (f i)) s = N (BIA.big P (fun i => f i) s).
proof.
elim: s => [|x s ih] //=.
by rewrite !(big_cons, BIA.big_cons) ih /=; case: (P x).
qed.

lemma nosmt big_const_Nx (P : 'a -> bool) x s:
  big P (fun _ => N x) s = (count P s) ** N x.
proof. by rewrite big_morph_N /= big_constz mulrC. qed.

lemma nosmt big_constx (P : 'a -> bool) x s: x <> Inf =>
  big P (fun _ => x) s = (count P s) ** x.
proof. by case: x => //= x; apply: big_const_Nx. qed.

lemma big_constNz x (s: 'a list) :
  big predT (fun _ => N x) s = N (size s * x).
proof. by rewrite big_const_Nx count_predT. qed.

lemma bigi_constz x (n m:int) : 
   n <= m =>
   bigi predT (fun _ => N x) n m = N ((m - n) * x).
proof. by move=> hnm;rewrite big_constNz size_range /#. qed.

end Bigxint.
export Bigxint.

(* ------------------------------------------------------------------------------ *)
lemma is_int_xopp (x:xint) : is_int x => is_int (-x).
proof. by case: x. qed.

lemma is_int_xadd (x y: xint) : 
  is_int x => is_int y => is_int (x + y).
proof. by case: x; case y. qed.

lemma is_int_xmul (x y: xint) : 
  is_int x => is_int y => is_int (x * y).
proof. by case: x; case y. qed.

hint simplify is_int_xopp, is_int_xadd, is_int_xmul.

lemma is_int_big (P: 'a -> bool) (f:'a -> xint) (s:'a list) : 
    (forall x, is_int (f x)) =>
    is_int (big P f s).
proof.
  move=> h; elim: s. 
  + by rewrite big_nil.
  move=> x l hl; rewrite big_cons; case: (P x) => ? //.
  by apply is_int_xadd => //; apply h.
qed.

hint simplify is_int_big.

(* -------------------------------------------------------------------- *)
lemma N_D (x y : int) : N (x + y) = N x + N y.
proof. by []. qed.

lemma N_N (x : int) : N (-x) = -N x.
proof. by []. qed.

lemma N_B (x y : int) : N (x-y) = N x - N y.
proof. by []. qed.

lemma mono_N_le (x y : int): x <= y <=> N x <= N y.
proof. by []. qed.
