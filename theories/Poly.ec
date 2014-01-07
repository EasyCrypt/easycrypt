(* SANDBOX FOR MULTIVARIATE POLYNOMIALS *)

(* -------------------------------------------------------------------- *)
require import Int.

pred predT ['a] (x : 'a) = true.

(* -------------------------------------------------------------------- *)
theory Ring.
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

(* -------------------------------------------------------------------- *)
theory Seq.
  type 'a list = [
    | "[]"
    | (::) of  'a & 'a list
  ].

  op size (xs : 'a list) =
    with xs = "[]"      => 0
    with xs = (::) y ys => 1 + (size ys).

  op cat (s1 s2 : 'a list) =
    with s1 = "[]"      => s2
    with s1 = (::) x s1 => x :: (cat s1 s2).

  op nth x (xs : 'a list) n : 'a =
    with xs = "[]"      => x
    with xs = (::) y ys => if n = 0 then y else (nth x ys (n-1)).

  op has (p : 'a -> bool) xs =
    with xs = "[]"      => false
    with xs = (::) y ys => (p y) || (has p ys).

  op all (p : 'a -> bool) xs =
    with xs = "[]"      => true
    with xs = (::) y ys => (p y) && (all p ys).

  op drop n (xs : 'a list) =
    with xs = "[]"      => []
    with xs = (::) y ys =>
      if n <= 0 then xs else drop (n-1) ys.

  op map (f : 'a -> 'b) xs =
    with xs = "[]"      => []
    with xs = (::) y ys => (f y) :: (map f ys).

  op filter (P : 'a -> bool) xs =
    with xs = "[]"      => []
    with xs = (::) y ys => if P y then y :: filter P ys else filter P ys.

  op foldr (f : 'a -> 'b -> 'b) z0 xs =
    with xs = "[]"      => z0
    with xs = (::) y ys => f y (foldr f z0 ys).

  op flatten ['a] = foldr cat [<:'a>].
end Seq.

(* -------------------------------------------------------------------- *)
theory Iota.
  import Seq.

  op iota_ : int -> int -> int list.

  axiom size_iota i j: size (iota_ i j) = max 0 j.

  axiom nth_iota i j n: n < max 0 j => nth 0 (iota_ i j) n = i + n.
end Iota.

(* -------------------------------------------------------------------- *)
theory Bigop.
  import Seq.

  op bigop ['a 'b] (id : 'a) (op_ : 'a -> 'a -> 'a) (s : 'b list) P F =
    foldr op_ id (map F (filter P s)).
end Bigop.

(* -------------------------------------------------------------------- *)
theory Poly.
  require import Pair.
  (*-*)   import Iota.
  (*-*)   import Seq.
  (*-*)   import Bigop.
  clone   import Ring.

  (* Polynomials with a countable set of indeterminates *)
  type poly.

  (* Monomial coefficients *)
  op coeff : poly -> (int -> int) -> ring.

  pred valid_monom (s : int -> int) =
       (forall j, j < 0 => s j = 0)
    /\ (forall j, s j >= 0)
    /\ (forall j, exists d, s j <> 0 <=> has ((=) j) d).

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
