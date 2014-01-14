(* -------------------------------------------------------------------- *)
require import Int.

op pred1 ['a] (c : 'a) = fun (x : 'a), c = x.
op predT ['a] = fun (x : 'a), true.
op pred0 ['a] = fun (x : 'a), false.
op predC ['a] (P : 'a -> bool) = fun (x : 'a), ! (P x).
op predC1 ['a] (c : 'a) = fun (x : 'a), c <> x.

op int_of_bool (b : bool) = if b then 1 else 0.

(* -------------------------------------------------------------------- *)
(*theory Ring.
  type ring.

  op zeror : ring.
  op oner  : ring.

  op ( + ) : ring -> ring -> ring.
  op [ - ] : ring -> ring.
  op ( * ) : ring -> ring -> ring.

  op ( - ) (x y : ring) = x + -x.

  axiom nosmt oner_neq0 : oner <> zeror.

  axiom nosmt addrA (x y z : ring): x + (y + z) = (x + y) + z.
  axiom nosmt addrC (x y   : ring): x + y = y + x.
  axiom nosmt add0r (x     : ring): zeror + x = x.
  axiom nosmt addNr (x     : ring): (-x) + x = zeror.

  axiom nosmt mulrA  (x y z : ring): x * (y * z) = (x * y) * z.
  axiom nosmt mulrC  (x y   : ring): x * y = y * x.
  axiom nosmt mul1r  (x     : ring): oner * x = x.
  axiom nosmt mulrDl (x y z : ring): (x + y) * z = x * z + y * z.

  lemma nosmt addr0 (x : ring): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN (x : ring): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma nosmt subrr (x : ring): x - x = zeror by apply addrN.

  lemma nosmt mulr1 (x : ring): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr (x y z : ring): x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.

  lemma oppr0: -zeror = zeror.
  proof. by rewrite -(add0r (-zeror)) addrN. qed.
end Ring.
*)
(* -------------------------------------------------------------------- *)
theory Seq.
  type 'a list = [
    | "[]"
    | (::) of  'a & 'a list
  ].

  op size (xs : 'a list) =
    with xs = "[]"      => 0
    with xs = (::) y ys => 1 + (size ys).

  lemma size_ge0 (s : 'a list): 0 <= size s.
  proof. by elim s=> //= x s; smt. qed.

  op (++) (s1 s2 : 'a list) =
    with s1 = "[]"      => s2
    with s1 = (::) x s1 => x :: (s1 ++ s2).

  op rcons (s : 'a list) (z : 'a) =
    with s = "[]"      => [z]
    with s = (::) x s' => x :: (rcons s' z).

  op last_ (x : 'a) s =
    with s = "[]"      => x
    with s = (::) y ys => last_ y ys.

  lemma cat0s (s : 'a list): [] ++ s = s.
  proof. by []. qed.

  lemma cats0 (s : 'a list): s ++ [] = s.
  proof. by elim s=> //= x s ->. qed.

  lemma cat1s (x : 'a) (s : 'a list): [x] ++ s = x::s.
  proof. by []. qed.

  lemma cats1 (s : 'a list) (z : 'a): s ++ [z] = rcons s z.
  proof. by elim s => //= x s ->. qed.

  lemma cat_cons (x : 'a) s1 s2: (x :: s1) ++ s2 = x :: (s1 ++ s2).
  proof. by []. qed.

  lemma catA (s1 s2 s3 : 'a list): s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
  proof. by elim s1=> //= x s1 ->. qed.

  lemma size_cat (s1 s2 : 'a list): size (s1 ++ s2) = size s1 + size s2.
  proof. by elim s1=> // x s1 /= ->; smt. qed.

  lemma last_cons (x y : 'a) (s : 'a list): last_ x (y :: s) = last_ y s.
  proof. by []. qed.

  lemma cat_rcons (x : 'a) s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
  proof. by rewrite -cats1 -catA. qed.

  lemma rcons_cat (x : 'a) s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
  proof. by rewrite -!cats1 catA. qed.

  op nth x (xs : 'a list) n : 'a =
    with xs = "[]"      => x
    with xs = (::) y ys => if n = 0 then y else (nth x ys (n-1)).

  lemma nth_default (z : 'a) s n: size s <= n => nth z s n = z.
  proof.
    elim s n => //= x s IHs n; case (n = 0).
      by intros=> ->; smt.
      by intros=> _ _; rewrite IHs; smt.
  qed.

  op mem (s : 'a list) (z : 'a) =
    with s = "[]"      => false
    with s = (::) x s' => (z = x) \/ mem s' z.

  lemma in_nil (x : 'a): mem [] x = false.
  proof. by []. qed.

  lemma in_cons y s (x : 'a): mem (y :: s) x <=> (x = y) \/ (mem s x).
  proof. by []. qed.

  lemma mem_head (x : 'a) s: mem (x :: s) x.
  proof. by []. qed.

  lemma mem_seq1 (x y : 'a): mem [y] x <=> (x = y).
  proof. by []. qed.

  lemma mem_seq2 (x y1 y2 : 'a):
    mem [y1; y2] x <=> (x = y1 \/ x = y2).
  proof. by []. qed.

  lemma mem_seq3 (x y1 y2 y3 : 'a):
    mem [y1; y2; y3] x <=> (x = y1 \/ x = y2 \/ x = y3).
  proof. by []. qed.

  lemma mem_seq4 (x y1 y2 y3 y4 : 'a):
    mem [y1; y2; y3; y4] x <=> (x = y1 \/ x = y2 \/ x = y3 \/ x = y4).
  proof. by []. qed.

  op uniq (s : 'a list) =
    with s = "[]"      => true
    with s = (::) x s' => !(mem s' x) /\ uniq s'.

  op drop n (xs : 'a list) =
    with xs = "[]"      => []
    with xs = (::) y ys =>
      if n <= 0 then xs else drop (n-1) ys.

  op map (f : 'a -> 'b) xs =
    with xs = "[]"      => []
    with xs = (::) y ys => (f y) :: (map f ys).

  op filter (p : 'a -> bool) xs =
    with xs = "[]"      => []
    with xs = (::) y ys => if p y then y :: filter p ys else filter p ys.

  lemma filter_pred0 (s : 'a list): filter pred0 s = [].
  proof. by elim s. qed.

  lemma filter_predT (s : 'a list): filter predT s = s.
  proof. by elim s => //= x s ->. qed.

  op count ['a] (p : 'a -> bool) xs =
    with xs = "[]"      => 0
    with xs = (::) y ys => (int_of_bool (p y)) + (count p ys).

  lemma count_ge0 (p : 'a -> bool) s: 0 <= count p s.
  proof. by elim s=> //= x s; smt. qed.

  lemma count_size p (s : 'a list): count p s <= size s.
  proof. by elim s => //= x s; smt. qed.

  op has (p : 'a -> bool) xs =
    with xs = "[]"      => false
    with xs = (::) y ys => (p y) \/ (has p ys).

  op all (p : 'a -> bool) xs =
    with xs = "[]"      => true
    with xs = (::) y ys => (p y) /\ (all p ys).

  lemma hasP p (s : 'a list): has p s <=> (exists x, mem s x /\ p x).
  proof.
    elim s => //= y s IHs; case (p y) => py.
      by rewrite orTb /=; exists y; smt.
    by rewrite orFb IHs; split; elim=> x []; smt.
  qed.

  lemma allP p (s : 'a list):
    all p s <=> (forall x, mem s x => p x).
  proof.
    elim s=> //= x s [IH1 IH2]; split.
      by elim=> _ h y []; [intros=> -> // | apply IH1].
    intros=> h; split; [by apply h | apply IH2].
    by intros=> y y_in_s; apply h; right.
  qed.

  lemma count_filter p (s : 'a list): count p s = size (filter p s).
  proof. by elim s => //= x s ->; case (p x). qed.

  lemma count_pred0 (s : 'a list): count pred0 s = 0.
  proof. by rewrite count_filter filter_pred0. qed.

  lemma count_predT (s : 'a list): count predT s = size s.
  proof. by rewrite count_filter filter_predT. qed.

  lemma has_count p (s : 'a list): has p s <=> (0 < count p s).
  proof. by elim s => //= x s -> /=; case (p x); smt. qed.

  lemma has_pred0 (s : 'a list): has pred0 s <=> false.
  proof. by rewrite has_count count_pred0. qed.

  lemma has_predT (s : 'a list): has predT s <=> (0 < size s).
  proof. by rewrite has_count count_predT. qed.

  lemma all_count p (s : 'a list): all p s <=> (count p s = size s).
  proof. by elim s => //= x s; case (p x) => _ /=; smt. qed.

  lemma all_pred0 (s : 'a list): all pred0 s <=> (size s = 0).
  proof. by rewrite all_count count_pred0 eq_sym. qed.

  lemma all_predT (s : 'a list): all predT s.
  proof. by rewrite all_count count_predT. qed.

  lemma eq_filter p1 p2 (s : 'a list): p1 = p2 => filter p1 s = filter p2 s.
  proof. by intros=> h; elim s=> //= x l; rewrite h => ->. qed.

  lemma eq_count p1 p2 (s : 'a list): p1 = p2 => count p1 s = count p2 s.
  proof. by intros=> h; rewrite !count_filter (eq_filter _ p2). qed.

  lemma eq_has p1 p2 (s : 'a list): p1 = p2 => has p1 s <=> has p2 s.
  proof. by intros=> h; rewrite !has_count (eq_count _ p2). qed.

  lemma eq_all p1 p2 (s : 'a list): p1 = p2 => has p1 s <=> has p2 s.
  proof. by intros=> h; rewrite !has_count (eq_count _ p2). qed.

  lemma has_sym (s1 s2 : 'a list): has (mem s1) s2 <=> has (mem s2) s1.
  proof. smt. qed.

  lemma has_pred1 (z : 'a) s: has (pred1 z) s <=> mem s z.
  proof. smt. qed.

  lemma filter_all p (s : 'a list): all p (filter p s).
  proof. by elim s => //= x s IHs; case (p x). qed.

  lemma all_filterP p (s : 'a list): all p s <=> filter p s = s.
  proof.
    split; last by intros=> <-; apply filter_all.
    by elim s => //= x s IHs [-> Hs]; rewrite IHs.
  qed.

  lemma filter_id p (s : 'a list): filter p (filter p s) = filter p s.
  proof. by apply all_filterP; apply filter_all. qed.

  lemma filter_cat p (s1 s2 : 'a list): filter p (s1 ++ s2) = filter p s1 ++ filter p s2.
  proof. by elim s1 => //= x s1 ->; case (p x). qed.

  lemma count_cat p (s1 s2 : 'a list): count p (s1 ++ s2) = count p s1 + count p s2.
  proof. by rewrite !count_filter filter_cat size_cat. qed.

  lemma has_cat p (s1 s2 : 'a list): has p (s1 ++ s2) <=> has p s1 \/ has p s2.
  proof. by elim s1 => //= x s1 IHs; rewrite IHs; smt. qed.

  lemma all_cat p (s1 s2 : 'a list): all p (s1 ++ s2) <=> all p s1 /\ all p s2.
  proof. by elim s1 => //= x s1 IHs; rewrite IHs. qed.

  op perm_eq ['a] (s1 s2 : 'a list) =
    all (fun x, count (pred1 x) s1 = count (pred1 x) s2) (s1 ++ s2).

  lemma perm_eqP (s1 s2 : 'a list):
    perm_eq s1 s2 <=> (forall p, count p s1 = count p s2).
  proof. admit. qed.

  lemma perm_eq_refl (s : 'a list): perm_eq s s.
  proof. by apply perm_eqP. qed.

  lemma perm_eq_sym (s1 s2 : 'a list): perm_eq s1 s2 <=> perm_eq s2 s1.
  proof. by rewrite !perm_eqP; smt. qed.

  lemma perm_eq_trans (s2 s1 s3 : 'a list):
    perm_eq s1 s2 => perm_eq s2 s3 => perm_eq s1 s3.
  proof. by rewrite !perm_eqP => h1 h2 p; rewrite h1 h2. qed.

  lemma perm_eqlP (s1 s2 : 'a list):
    perm_eq s1 s2 <=> (forall s, perm_eq s1 s <=> perm_eq s2 s).
  proof.
    split; last by intros=> ->; rewrite perm_eq_refl.
    intros=> h s; split; last by apply perm_eq_trans.
    by apply perm_eq_trans; apply perm_eq_sym.
  qed.

  lemma perm_catC (s1 s2 : 'a list): perm_eq (s1 ++ s2) (s2 ++ s1).
  proof. by rewrite !perm_eqP => p; rewrite !count_cat; smt. qed.

  lemma perm_catCl (s1 s2 : 'a list):
    forall s, perm_eq (s1 ++ s2) s <=> perm_eq (s2 ++ s1) s.
  proof. by rewrite -perm_eqlP perm_catC. qed.

  lemma perm_cat2l (s1 s2 s3 : 'a list):
    perm_eq (s1 ++ s2) (s1 ++ s3) <=> perm_eq s2 s3.
  proof.
    rewrite !perm_eqP; split=> h p; cut := h p;
      by rewrite !count_cat; smt.
  qed.

  lemma perm_cat2r (s1 s2 s3 : 'a list):
    perm_eq (s2 ++ s1) (s3 ++ s1) <=> perm_eq s2 s3.
  proof. by do 2! rewrite perm_eq_sym perm_catCl; apply perm_cat2l. qed.

  lemma perm_catCAl (s1 s2 s3 : 'a list):
    forall s, perm_eq (s1 ++ s2 ++ s3) s <=> perm_eq (s2 ++ s1 ++ s3) s.
  proof. by rewrite -!perm_eqlP perm_cat2r perm_catC. qed.

  lemma perm_cons (x : 'a) s1 s2:
    perm_eq (x :: s1) (x :: s2) <=> perm_eq s1 s2.
  proof. by generalize (perm_cat2l [x]) => /= h; apply h. qed.

  lemma perm_eq_mem (s1 s2 : 'a list):
    perm_eq s1 s2 => forall x, mem s1 x <=> mem s2 x.
  proof. by rewrite perm_eqP => h x; rewrite -!has_pred1 !has_count h. qed.

  lemma perm_eq_size (s1 s2 : 'a list):
    perm_eq s1 s2 => size s1 = size s2.
  proof. by rewrite perm_eqP=> h; rewrite -!count_predT h. qed.

  op rem (z : 'a) s =
    with s = "[]"      => []
    with s = (::) x s' => if x = z then s' else x :: (rem z s').

  lemma rem_id (z : 'a) s: ! mem s z => rem z s = s.
  proof.
    elim s => //= y s IHs; rewrite -nor; elim.
    intros=> neq_yz s_notin_z; rewrite IHs // (eq_sym y).
    by cut ->: (z = y) <=> false.
  qed.

  lemma perm_to_rem (z : 'a) s : mem s z => perm_eq s (z :: rem z s).
  proof.
    elim s => //= y s IHs; rewrite eq_sym perm_eq_sym.
    rewrite -ora_or; elim; first by intros=> -> /=; rewrite perm_eq_refl.
    rewrite -neqF => -> /= z_in_s; rewrite -(cat1s z) -(cat1s y) catA.
    by rewrite perm_catCAl /= perm_cons perm_eq_sym IHs.
  qed.

  lemma size_rem (x : 'a) s: mem s x => size (rem x s) = (size s) - 1.
  proof.
    intros=> h; apply perm_to_rem in h; apply perm_eq_size in h.
    by rewrite h; smt.
  qed.

  op foldr (f : 'a -> 'b -> 'b) z0 xs =
    with xs = "[]"      => z0
    with xs = (::) y ys => f y (foldr f z0 ys).

  op flatten ['a] = foldr (++) [<:'a>].

  op path (e : 'a -> 'a -> bool) (x : 'a) (p : 'a list) : bool =
    with p = "[]"      => true
    with p = (::) y p' => e x y /\ path e y p'.

  op sorted (e : 'a -> 'a -> bool) (xs : 'a list) =
    with xs = "[]"      => true
    with xs = (::) y ys => false. (* BUG: path e y ys. *) 

  op sort : ('a -> 'a -> bool) -> 'a list -> 'a list.

  axiom sort_sorted (e : 'a -> 'a -> bool) (xs : 'a list):
       (forall x y, e x y || e y x)
    => sorted e (sort e xs).

  axiom perm_sort (e : 'a -> 'a -> bool) (xs : 'a list):
       (forall x y, e x y || e y x)
    => perm_eq (sort e xs) xs.

  op lex (e : 'a -> 'a -> bool) s1 s2 =
    with s1 = "[]"      , s2 = "[]"       => false
    with s1 = "[]"      , s2 = (::) y2 s2 => true
    with s1 = (::) y1 s1, s2 = "[]"       => false
    with s1 = (::) y1 s1, s2 = (::) y2 s2 =>
      if e y1 y2 then true else false.
end Seq.

(* -------------------------------------------------------------------- *)
theory Bigop.
  import Seq.

  op bigop ['a 'b] (id : 'a) (op_ : 'a -> 'a -> 'a) (s : 'b list) P F =
    foldr op_ id (map F (filter P s)).
end Bigop.

(* -------------------------------------------------------------------- *)

theory BigSum.
  (*-*) import Seq.
  clone import Top.Ring.Ring.

  op sum (s : 'a list) P F = Bigop.bigop Ring.zeror Ring.(+) s P F.
end BigSum.

(* -------------------------------------------------------------------- *)
theory FreeGroup.
  require import Pair.
  (*---*) import Seq.

  type Z.                       (* type of coefficients  *)
  type K.                       (* type of formal points *)

  op lez : K -> K -> bool.

  clone import Top.Ring.Ring   with type ring <- Z.
  clone import BigSum with type Ring.ring <- Z.

  type freeg.
  type repr = (Z * K) list.

  op repr : repr  -> freeg.
  op pi   : freeg -> repr .

  pred normalized (s : repr) =
       all  (fun (zk : Z * K), zk.`1 <> zeror) s
    /\ uniq (map snd s)
    /\ sorted lez (map snd s).

  axiom pi_normed (s : freeg): normalized (pi s).
end FreeGroup.

(* -------------------------------------------------------------------- *)
theory Poly.
  require import Pair.
  (*---*) import Iota.
  (*---*) import Seq.
  (*---*) import Bigop.
  clone   import Top.Ring.Ring.

  (* Polynomials with a countable set of indeterminates *)
  type poly.

  (* Monomial coefficients *)
  type monomial = ring * int list.

  op normal1 (cs : monomial) =
       cs.`1 <> zeror
    /\ all (fun x, x >= 0) cs.`2
    /\ last_ 1 cs.`2 <> 0.

  op normal (cs : monomial list) =
       all normal1 cs
    /\ sorted (lex Int.(<)) (map snd cs).

  op coeffs : poly -> monomial list.

  axiom coeffs_normal (p : poly): normal (coeffs p).

  pred valid_monom (s : int -> int) =
       (forall j, j < 0 => s j = 0)
    /\ (forall j, s j >= 0)
    /\ (forall j, exists d, s j <> 0 <=> has ((=) j) d).

  op coeff : poly -> (int -> int) -> ring.

  axiom coeff_neq0 p s: coeff p s <> zeror => valid_monom s.

  lemma coeff_eq0 p s: ! valid_monom s => coeff p s = zeror.
  proof. by apply absurd; rewrite nnot; apply coeff_neq0. qed.

  lemma valid_monomP s:
    valid_monom s <=>
      exists d, all (fun j, j >= 0) d /\ forall j, nth 0 d j = s j.
  proof. admit. qed.

  (* Hilbert-ε for valid_monomP *)
  op seq_of_monom: (int -> int) -> int list.

  axiom seq_of_monomP s:
    valid_monom s =>
         all (fun j, j >= 0) (seq_of_monom s)
      /\ forall j, nth 0 (seq_of_monom s) j = s j.

  (* Equality is the equality of all the monomial coeffs. *)
  axiom poly_eqP (p q : poly):
    (forall s, coeff p s = coeff q s) <=> (p = q).

  (* Group structure *)
  op zerop : poly.
  op ( + ) : poly -> poly -> poly.
  op [ - ] : poly -> poly.

  axiom coeff0: forall s, coeff zerop s = zeror.

  axiom coeffD_r (p q : poly) s: valid_monom s => coeff (p + q) s = (coeff p s) + (coeff q s).
  axiom coeffN_r (p   : poly) s: valid_monom s => coeff (-p) s = - (coeff p s).

  lemma coeffD (p q : poly) s: coeff (p + q) s = (coeff p s) + (coeff q s).
  proof.
    case (valid_monom s) => h; first by rewrite coeffD_r.
    by rewrite !coeff_eq0 // addr0.
  qed.

  lemma coeffN (p : poly) s: coeff (-p) s = - (coeff p s).
  proof.
    case (valid_monom s) => h; first by rewrite coeffN_r.
    by rewrite !coeff_eq0 // oppr0.
  qed.

  lemma nosmt addpA (p q r : poly): p + (q + r) = (p + q) + r.
  proof. by apply poly_eqP=> s; rewrite !coeffD addrA. qed.

  lemma nosmt addrC (p q : poly): p + q = q + p.
  proof. by apply poly_eqP=> s; rewrite !coeffD addrC. qed.

  lemma nosmt add0r (p : poly): zerop + p = p.
  proof. by apply poly_eqP=> s; rewrite coeffD coeff0 add0r. qed.

  lemma nosmt addNr (p : poly): (-p) + p = zerop.
  proof. by apply poly_eqP=> s; rewrite coeffD coeffN coeff0 addNr. qed.

  (* Ring structure *)
  op oner  : poly.
  op ( * ) : poly -> poly -> poly.

  op decomp_monoms (d : int list) : (int * int) list list =
    with d = "[]"     => [[]]
    with d = (::) x d =>
      let idx = iota_ 0 (x+1) in
      let idx = map (fun i, (i, x-i)) idx in
        flatten
          (map
            (fun idx2, map (fun idx1, idx1 :: idx2) idx)
            (decomp_monoms d)).

  axiom nosmt coeffM_r (p q : poly) s: valid_monom s =>
    coeff (p * q) s =
      bigop zeror Ring.(+) (decomp_monoms (seq_of_monom s)) predT
        (fun d, coeff p (nth 0 (map fst d)) * coeff q (nth 0 (map snd d))).
end Poly.
