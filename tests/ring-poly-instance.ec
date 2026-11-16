(* Type-polymorphic ring instances (per-slot recorded instantiations:
   the instance's tyvars rebind at the matched carrier, like indices). *)

require import AllCore Ring.

(* type-polymorphic carrier: the pointwise-integer function ring *)
op fzero ['a] : 'a -> int = fun _ => 0.
op fone  ['a] : 'a -> int = fun _ => 1.
op fadd  ['a] (f g : 'a -> int) : 'a -> int = fun x => f x + g x.
op fmul  ['a] (f g : 'a -> int) : 'a -> int = fun x => f x * g x.
op fopp  ['a] (f : 'a -> int)   : 'a -> int = fun x => - f x.

lemma L_oner_neq0 ['a] : fone<:'a> <> fzero.
proof. by apply/negP=> /fun_ext /(_ witness). qed.

lemma L_addr0 ['a] (f : 'a -> int) : fadd f fzero = f.
proof. by apply/fun_ext=> x; rewrite /fadd /fzero. qed.

lemma L_addrA ['a] (f g h : 'a -> int) :
  fadd f (fadd g h) = fadd (fadd f g) h.
proof. by apply/fun_ext=> x; rewrite /fadd /#. qed.

lemma L_addrC ['a] (f g : 'a -> int) : fadd f g = fadd g f.
proof. by apply/fun_ext=> x; rewrite /fadd /#. qed.

lemma L_addrN ['a] (f : 'a -> int) : fadd f (fopp f) = fzero.
proof. by apply/fun_ext=> x; rewrite /fadd /fopp /fzero /#. qed.

lemma L_mulr1 ['a] (f : 'a -> int) : fmul f fone = f.
proof. by apply/fun_ext=> x; rewrite /fmul /fone /#. qed.

lemma L_mulrA ['a] (f g h : 'a -> int) :
  fmul f (fmul g h) = fmul (fmul f g) h.
proof. by apply/fun_ext=> x; rewrite /fmul /#. qed.

lemma L_mulrC ['a] (f g : 'a -> int) : fmul f g = fmul g f.
proof. by apply/fun_ext=> x; rewrite /fmul /#. qed.

lemma L_mulrDl ['a] (f g h : 'a -> int) :
  fmul (fadd f g) h = fadd (fmul f h) (fmul g h).
proof. by apply/fun_ext=> x; rewrite /fadd /fmul /#. qed.

instance ring [pfun] with ['a] ('a -> int)
  op rzero = fzero
  op rone  = fone
  op add   = fadd
  op mul   = fmul
  op opp   = fopp

  proof addr0     by exact L_addr0
  proof addrA     by exact L_addrA
  proof addrC     by exact L_addrC
  proof addrN     by exact L_addrN
  proof mulr1     by exact L_mulr1
  proof mulrA     by exact L_mulrA
  proof mulrC     by exact L_mulrC
  proof mulrDl    by exact L_mulrDl.

lemma pf_test ['a] (f g : 'a -> int) :
  fadd f (fadd g (fopp f)) = g.
proof. by ring [pfun]. qed.

lemma pf_bool (f g : bool -> int) :
  fmul f g = fmul g f.
proof. by ring [pfun]. qed.
