(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Option Int.

(* -------------------------------------------------------------------- *)
lemma lt0n n : (0 <= n) => (0 < n <=> n <> 0).
proof. by rewrite ltz_def => ->. qed.

lemma eqn0Ngt n : (0 <= n) => (n = 0) <=> !(0 < n).
proof. by rewrite eq_sym lez_eqVlt -ora_or => [<-|?->]. qed.

lemma ltzS m n : (m < n+1) = (m <= n).
proof. by rewrite -lez_add1r addzC lez_add2r. qed.

(* -------------------------------------------------------------------- *)
op b2i (b : bool) = b ? 1 : 0.

lemma b2i0 : b2i false = 0. proof. by []. qed.
lemma b2i1 : b2i true  = 1. proof. by []. qed.

lemma b2i_or b1 b2: b2i (b1 \/ b2) = b2i b1 + b2i b2 - b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|] //=; rewrite oppz0. qed.

lemma b2i_and b1 b2: b2i (b1 /\ b2) = b2i b1 * b2i b2.
proof. by rewrite /b2i; case: b1 b2 => [|] [|]. qed.

lemma le_b2i b1 b2: (b1 => b2) <=> (b2i b1 <= b2i b2).
proof. by case: b1 b2 => [|] [|]. qed.

lemma b2i_ge0 b: 0 <= b2i b.
proof. by case: b. qed.

lemma b2i_le1 b: b2i b <= 1.
proof. by case: b. qed.

lemma b2i_eq1 b : b2i b = 1 <=> b.
proof. by case: b. qed.

lemma b2i_eq0 b : b2i b = 0 <=> !b.
proof. by case: b. qed.

(* -------------------------------------------------------------------- *)
theory IterOp.
  op iteri ['a] : int -> (int -> 'a -> 'a) -> 'a -> 'a.

  axiom iteri0 ['a] n opr (x : 'a):
    n <= 0 => iteri n opr x  = x.

  axiom iteriS ['a] n opr (x : 'a):
    0 <= n => iteri (n+1) opr x = opr n (iteri n opr x).

  lemma eq_iteri (f1 f2 : int -> 'a -> 'a) k a:
       (forall i a, 0 <= i < k => f1 i a = f2 i a)
    => iteri k f1 a = iteri k f2 a.
  proof.
  elim/natind: k=> [n le0_n|n ge0_n ih] h; first by rewrite !iteri0.
  rewrite !iteriS // h 1:ltz_addl ?ih // => i b [ge0_i lt_in].
  by apply/h; rewrite ge0_i (ltz_trans n) // ltz_addl.
  qed.

  op iter ['a] n f x0 = iteri<:'a> n (fun i => f) x0.

  lemma iter0 ['a] n opr (x : 'a): n <= 0 => iter n opr x = x.
  proof. by move/iteri0<:'a>=> @/iter ->. qed.

  lemma iterS ['a] n opr (x : 'a): 0 <= n =>
    iter (n+1) opr x = opr (iter n opr x).
  proof. by move/iteriS<:'a>=> @/iter ->. qed.

  lemma iter1 ['a] opr (x : 'a): iter 1 opr x = opr x.
  proof. by rewrite (@iterS 0) // iter0. qed.

  lemma iter2 ['a] opr (x : 'a): iter 2 opr x = opr (opr x).
  proof. by rewrite (@iterS 1) // iter1. qed.

  lemma iterSr n opr (x : 'a):
    0 <= n => iter (n + 1) opr x = iter n opr (opr x).
  proof.
    elim: n=> /=; first by rewrite (iterS 0) ?iter0.
    by move=> n geo0 ih; rewrite iterS 2:ih ?iterS // addz_ge0.
  qed.

  op iterop ['a] (n : int) opr (x z : 'a) : 'a =
    let f = fun i y, if i <= 0 then x else opr x y in
    iteri n f z.

  lemma iterop0 ['a] (n : int) opr (x z : 'a): n <= 0 =>
    iterop n opr x z = z.
  proof. by move=> le0_n; rewrite /iterop /= iteri0. qed.

  lemma iterop1 ['a] opr (x z : 'a): iterop 1 opr x z = x.
  proof. by rewrite /iterop /= (iteriS 0). qed.

  lemma iteropS ['a] (n : int) opr (x z : 'a): 0 <= n =>
    iterop (n+1) opr x z = iter n (opr x) x.
  proof.
    rewrite /iterop; elim: n=> /=; first by rewrite iter0 ?(iteriS 0).
    move=> n ge0_n /= ih; rewrite iteriS 1:addz_ge0 //= ih.
    by rewrite {1}addzC lez_add1r ltzNge ge0_n /= iterS.
  qed.
end IterOp.

export IterOp.

(* -------------------------------------------------------------------- *)
op odd (z : int) = iter z [!] false.

lemma odd0 : !odd 0. proof. by rewrite iter0. qed.
lemma odd1 :  odd 1. proof. by rewrite iter1. qed.
lemma odd2 : !odd 2. proof. by rewrite iter2. qed.

lemma oddS z : 0 <= z => odd (z + 1) = !(odd z).
proof. by move/iterS<:bool>=> ->. qed.

(* -------------------------------------------------------------------- *)
(* FIXME: should be supersed by IntDiv                                  *)
lemma nosmt mod_mul_mod n p i: n <> 0 => 0 < p => (i %% (n*p)) %% p = i %% p.
proof.
(*
  move=> Hn Hp;rewrite {2}(Div_mod i (n*p));1:smt ml=0. 
  rewrite mulzC mulzA Mod_mult //.
*)
admitted.

lemma nosmt mod_mod i p: 0 < p => (i%%p) %% p = i%%p.
proof. (* by move=> Hp;apply (mod_mul_mod 1 p i). *) admitted.

lemma nosmt mod_pow2_mod n p i: 0 <= n <= p => i %% 2^p %% 2^n = i %% 2^n.
proof.
(*
  move=> Hb;rewrite (_:p = (p - n) + n);1:ring.
  by rewrite -pow_add 1,2:[smt ml=0] mod_mul_mod //;1:apply gtr_eqF;apply powPos.
*)
admitted.

lemma nosmt mod_pow2_split i n p : 0 <= p <= n =>
   i = (i/%2^n)*2^n + ((i%%2^n)/%2^p)*2^p + i%%2^p.
proof.
(*
  cut Hn := gtr_eqF _ _ (powPos 2 n _) => //. 
  cut Hp := gtr_eqF _ _ (powPos 2 p _) => //.
  move=> Hb;rewrite {1}(Div_mod i (2^n))// {1}(Div_mod (i%%2^n) (2^p))//.
  rewrite mod_pow2_mod //;ring.
*)
admitted.

lemma nosmt div_Mle x y p: 0 <= x <= y => 0 < p => x/%p <= y/%p.
proof.
(*
  move=> [H0x Hxy]; cut : 0 <= y - x by smt ml=0.
  cut {2}->: y = x + (y - x) by ring.
  move:(y-x)=> {Hxy y} y Hy Hp. cut Hneq:= gtr_eqF _ _ Hp.
  rewrite {2}(Div_mod x p) // (Div_mod y p) // .
  cut ->: p * (x /% p) + x %% p + (p * (y /% p) + y %% p) =
          p * (x/%p + y/%p) + (x%%p + y%%p) by ring.
  rewrite Div_mult //; move: Mod_bound Div_bound;smt ml=0.
*)
admitted.
  
lemma nosmt mod_pow2_div i n p:
  0 <= i => 0 <= p <= n => (i %% 2^n) /% 2^p = (i /% 2^p) %% 2^(n-p).
proof.
(*
  move=> Hi ^Hb [H0p Hpn]. cut Hn := powPos 2 n _ => //; cut Hp:= powPos 2 p _ => //.
  rewrite {2}(mod_pow2_split _ _ _ Hb).
  cut -> : i /% 2 ^ n * 2 ^ n + i %% 2 ^ n /% 2 ^ p * 2 ^ p =
           2^p * ( 2 ^ (n-p) * (i /% 2 ^ n)  + i %% 2 ^ n /% 2 ^ p).
  + rewrite {2}(_:n = (n-p)+p) 2:-pow_add;1,4:(by ring);smt ml= 0.
  rewrite Div_mult // (Div_inf (i%%2^p)) /Int.zero /=.
  + rewrite -{3}(ger0_norm (2^p));1:by apply ltzW.
    by apply /Mod_bound/gtr_eqF.
  rewrite Mod_mult 1:powPos // (mod_small (i %% 2 ^ n /% 2 ^ p)) //.
  split;1:by move:Mod_bound Div_bound;smt ml=0.
  move=> _;cut := div_Mle (i %% 2 ^ n) (2^n) (2^p) _ _ => //.
  + move:Mod_bound;smt ml=0.
  cut {2}->: n = p+(n-p) by ring.
  rewrite -pow_add // 1:[smt ml=0] (Div_mult _ (2^(n - p)) 0 Hp).
  rewrite (Div_inf 0) /Int.zero //= ler_eqVlt=> [Heq | //] .
  cut Hp0 := gtr_eqF _ _ Hp.
  move:(Div_mod (i%%2^n) (2^p) Hp0). 
  move:(Mod_bound i (2^n) _). by apply gtr_eqF.
  move:(Mod_bound  (i %% 2^n) (2^p) Hp0). 
  rewrite Heq pow_add //;smt ml=0.
*)
admitted.
