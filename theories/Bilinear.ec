require Int.

theory Prime_field. 
  (* prime fields GF(q) for q prime *)
  theory Base.

    (* the order of field is a prime q *)
    op q: int.
    axiom q_pos:  Int.(<) 0 q.
    (* TODO: Add an axiom asserting primality of q. *)

    (* Type of elements of the field *)
    type t.
    op zero : t. (* zero *)
    op one  : t. (* one *)
    op ( * ): t -> t -> t.  (* multiplication modulo q *)
    op ( + ): t -> t -> t.  (* addition modulo q *)
    op [ - ]: t -> t.       (* the additive inverse *)
    op inv: t -> t.         (* the multiplicative inverse *)
  
    op (-) : t -> t -> t.   (* subtraction modulo q *)
    op (/) : t -> t -> t.   (* division modulo q for y <> 0 *)
    op (^) : t -> int -> t. (* exponentiation *)

    axiom non_trivial: zero <> one.

    (* Addition/Subtraction *)
    axiom addC (x y:t): x + y = y + x.
    axiom addA (x y z:t) : x + (y + z) = (x + y) + z.
    axiom addf0 (x:t): x + zero = x.
    axiom addfN (x:t): x + -x = zero.
    axiom sub_def (x y:t) : x - y = x + -y.   

    (* Multiplication *)
    axiom mulC (x y:t): x * y = y * x.
    axiom mulA (x y z:t): x * (y * z) = (x * y) * z.
    axiom mulf1 (x:t): x * one = x.
    axiom mulfV (x:t): x <> zero => (x * (inv x)) = one.
    axiom mulfDl (x y z:t): x * y + x * z = x * (y + z).
    axiom div_def (x y:t): x / y = x * (inv y). 

    (* Exponentiation *)
    axiom pow0 (x:t): x ^ 0 = one.
    axiom powS (x:t) (n:int): Int.(<=) 0 n => x ^ (Int.(+) n 1) = x * x ^ n.
    axiom powN (x:t) (n:int): Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).

    (** conversion between int and gf_q *)
    op ofint : int -> t.
    op toint : t -> int.

    axiom ofint0: ofint 0 = zero.
    axiom ofintS (n:int): Int.(<=) 0 n => ofint (Int.(+) n 1) = (ofint n) + one.
    axiom ofintN (n:int): ofint (Int.([-]) n) = -(ofint n).

    import Int.
    axiom toint_bounded (x:t): 0 <= toint x < q.
    axiom oftoint (x:t): ofint (toint x) = x.
    axiom toofint_mod (x:int): toint (ofint x) = Int.EuclDiv.(%%) x q. 

  end Base.
  export Base.

  (** Lemmas *)
  lemma subff (x:t): (x - x) = zero
  by [].

  lemma add0f (x:t): zero + x = x
  by [].

  lemma mulf0 (x:t): x * zero = zero
  by [].

  lemma mulNf (x y:t): (-x) * y = - (x * y)
  by [].

  lemma mulfN (x y:t): y * (-x)= - (y * x)
  by [].  

  lemma nosmt oppK (x:t): -(-x) = x
  by [].

  lemma mulfNl (x y z:t): x * y - x * z = x * (y - z)
  by [].

  lemma mulN1f (x:t): (-one) * x = -x
  by [].

  lemma oppfD (x y:t): (-x) + (-y) = -(x + y)
  by [].

  import Int.
  lemma toint_pos (x:t): 0 <= toint x
  by [].

  lemma toint_lt (x:t): toint x < q
  by [].

  lemma toint_le (x:t): toint x <= q - 1
  by [].

  lemma toofint (x:int): 0 <= x => x < q => toint (ofint x) = x.
  proof.
    intros Hp Hlt;rewrite toofint_mod.
    by cut H:= ediv_unique x q 0 x _; smt.
  qed.

  lemma ofint1_: ofint 1 = Base.one (* bug : if ofint1 is used then can not declare the ring and field instance *)
  by [].

  (* Declaring the ring and field structure *)
  require AlgTactic.

  instance ring with t
    op rzero = Base.zero
    op rone  = Base.one
    op add   = Base.( + )
    op opp   = Base.([-])
    op mul   = Base.( * )
    op expr  = Base.( ^ ) 
    op sub   = Base.(-)
    op ofint = ofint

    proof oner_neq0 by smt
    proof addr0     by smt
    proof addrA     by smt
    proof addrC     by smt
    proof addrN     by smt
    proof mulr1     by smt
    proof mulrA     by smt
    proof mulrC     by smt
    proof mulrDl    by smt
    proof expr0     by smt
    proof exprS     by smt
    proof subrE     by smt
    proof ofint0    by smt
    proof ofint1    by smt
    proof ofintS    by smt
    proof ofintN    by smt.

  instance field with t
    op rzero = Base.zero
    op rone  = Base.one
    op add   = Base.( + )
    op opp   = Base.([-])
    op mul   = Base.( * )
    op expr  = Base.( ^ )
    op sub   = Base.(-)
    op ofint = ofint
    op inv   = inv
    op div   = Base.(/)

    proof oner_neq0 by smt
    proof addr0     by smt
    proof addrA     by smt
    proof addrC     by smt
    proof addrN     by smt
    proof mulr1     by smt
    proof mulrA     by smt
    proof mulrC     by smt
    proof mulrDl    by smt
    proof mulrV     by smt
    proof expr0     by smt
    proof exprS     by smt
    proof exprN     by smt
    proof subrE     by smt
    proof divrE     by smt
    proof ofint0    by smt
    proof ofint1    by smt
    proof ofintS    by smt
    proof ofintN    by smt.

  theory Distr.

    require import Distr.
    require import Real.
    (* distrinution *)
    op dt: t distr.

    axiom supp_def: forall (s:t),
      in_supp s dt.

    axiom mu_x_def_in: forall (s:t),
      mu_x dt s = (1%r/q%r)%Real.

    axiom lossless: weight dt = 1%r.

  end Distr.

end Prime_field.

theory Cyclic.
  clone export Prime_field.Base as F. 
  type group.
  const g:group. (* the generator *)

  op ( * ): group -> group -> group.   (* multiplication of group elements *)
  op ( / ): group -> group -> group.   (* division *)
  op ( ^ ): group -> t -> group.    (* exponentiation *)
  op log:group -> t.                (* discrete logarithm *)

  op g1 = g ^ zero.

  axiom div_def (a b:group): g^(log a - log b) = a / b.

  axiom mul_pow g (x y:t):
    g ^ x * g ^ y = g ^ (x + y).

  axiom pow_pow g (x y:t):
    (g ^ x) ^ y = g ^ (x * y).

  axiom pow_log (a:group):
    g ^ (log a) = a.

  axiom log_pow (x:t):
    log (g ^ x) = x.

  lemma mulC (x y: group) : x * y = y * x.
  proof. 
    by rewrite -(pow_log x) -(pow_log y) mul_pow;smt. 
  qed.

  lemma mulA (x y z: group) : x * (y * z) = x * y * z.
  proof. 
    by rewrite -(pow_log x) -(pow_log y) -(pow_log z) !mul_pow;smt. 
  qed.

  lemma mul1 x : g1 * x = x.
  proof.
    by rewrite /g1 -(pow_log x) mul_pow;smt.
  qed.

  lemma divK (a:group) : a / a = g ^ zero.
  proof strict.
    by rewrite -div_def sub_def addfN.
  qed.

end Cyclic.

theory Bilinear.
  import Prime_field.
(*  clone export Prime_field as Fq. *)
  clone import Cyclic as G1
   (* with theory F = F.Base. (* Bug <- do not work *) *)
    with type F.t    <- Base.t,
         op F.q      <- Base.q,
         op F.zero   <- Base.zero,
         op F.one    <- Base.one,
         op F.( * )  <- Base.( * ),
         op F.( + )  <- Base.( + ),
         op F.( - )  <- Base.( - ),
         op F.([-])  <- Base.([-]),  (* Strange syntax ... *)
         op F.inv    <- Base.inv,
         op F.( / )  <- Base.( / ),
         op F.( ^ )  <- Base.( ^ ),
         op F.ofint  <- Base.ofint, 
         op F.toint  <- Base.toint
        (* axiom F.q_pos <- Base.q_pos. : can not be done ? *)
     proof F.* by smt.
     (* How can we do to not duplicate axiom ??? *)
  clone import Cyclic as G2
    with type F.t    <- Base.t,
         op F.q      <- Base.q,
         op F.zero   <- Base.zero,
         op F.one    <- Base.one,
         op F.( * )  <- Base.( * ),
         op F.( + )  <- Base.( + ),
         op F.( - )  <- Base.( - ),
         op F.([-])  <- Base.([-]),  (* Strange syntax ... *)
         op F.inv    <- Base.inv,
         op F.( / )  <- Base.( / ),
         op F.( ^ )  <- Base.( ^ ),
         op F.ofint  <- Base.ofint, 
         op F.toint  <- Base.toint
        (* axiom F.q_pos <- Base.q_pos. : can not be done ? *)
    proof F.* by smt.

  clone import Cyclic as GT
    with type F.t    <- Base.t,
         op F.q      <- Base.q,
         op F.zero   <- Base.zero,
         op F.one    <- Base.one,
         op F.( * )  <- Base.( * ),
         op F.( + )  <- Base.( + ),
         op F.( - )  <- Base.( - ),
         op F.([-])  <- Base.([-]),  (* Strange syntax ... *)
         op F.inv    <- Base.inv,
         op F.( / )  <- Base.( / ),
         op F.( ^ )  <- Base.( ^ ),
         op F.ofint  <- Base.ofint, 
         op F.toint  <- Base.toint
        (* axiom F.q_pos <- Base.q_pos. : can not be done ? *)
    proof F.* by smt.

  op e : G1.group -> G2.group -> GT.group.

  axiom eND : e G1.g G2.g <> GT.g1.

  axiom e_pow1 (g:G1.group) (x:t) f: e (g^x) f = (e g f)^x.
  axiom e_pow2 (f:G2.group) x g: e g (f^x) = (e g f)^x.

  lemma e_pow (g:G1.group) (f:G2.group) (x y:t) : e (g^x) (f^y) =  (e g f)^(x*y).
  proof.
    by rewrite e_pow2 e_pow1 pow_pow.
  qed.

  op ge = e G1.g G2.g.

  lemma log_ge : log ge <> zero
  by smt.
(*
  proof.
    case (log ge = zero) => //.
    rewrite /ge => H /=; cut := eND; by rewrite - GT.pow_log /GT.g1 H.
  qed.
*)

  op loge (h:GT.group) = GT.log h / log ge.

  lemma pow_loge (a:GT.group): ge ^ (loge a) = a.
  proof. 
    by rewrite /loge -{1}(GT.pow_log ge) pow_pow; smt.
  qed.

  lemma loge_pow (x:t): loge (ge ^ x) = x.    
  proof.
    by rewrite /loge -{1}(pow_log ge) pow_pow log_pow; smt.
  qed.  

  lemma loge_log g f : e g f = ge ^ (log g * log f).
  proof.
    by rewrite -{1}G1.pow_log -{1}G2.pow_log e_pow.
  qed.
(*
instance field with t
    op rzero = Base.zero
    op rone  = Base.one
    op add   = Base.( + )
    op opp   = Base.([-])
    op mul   = Base.( * )
    op expr  = Base.( ^ )
    op sub   = Base.(-)
    op ofint = ofint
    op inv   = inv
    op div   = Base.(/)

    proof oner_neq0 by smt
    proof addr0     by smt
    proof addrA     by smt
    proof addrC     by smt
    proof addrN     by smt
    proof mulr1     by smt
    proof mulrA     by smt
    proof mulrC     by smt
    proof mulrDl    by smt
    proof mulrV     by smt
    proof expr0     by smt
    proof exprS     by smt
    proof exprN     by smt
    proof subrE     by smt
    proof divrE     by smt
    proof ofint0    by smt
    proof ofint1    by smt
    proof ofintS    by smt
    proof ofintN    by smt.
*)
  lemma test g f : e g f = ge ^ (log f * log g).
  proof.
    rewrite loge_log;congr; last by trivial.
    by fieldeq .
  qed.

(*    fieldeq. (* bug, need to redeclare the field *) *)

end Bilinear.




