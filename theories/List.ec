require import Int.
require import Fun.

type 'a list = [
  | "[]"
  | (::) of 'a & 'a list ].

(*** Recursor and Derived Induction Principles *)
(** Recursor *)
op list_rect (v:'b) (f:'a -> 'a list -> 'b -> 'b) (xs:'a list) =
  with xs = "[]"      => v
  with xs = (::) x xs => f x xs (list_rect v f xs).

(** Induction principles. *)
lemma list_case_eq (P:'a list -> bool) (xs:'a list):
  (xs = [] => P xs) => 
  ((exists x' xs', xs = x'::xs') => P xs) =>
  P xs.
proof strict.
elim/list_case xs=> //= x xs -> //.
by exists x; exists xs.
qed.

lemma list_ind_eq (P:'a list -> bool):
  (forall xs, xs = [] => P xs) =>
  (forall xs x' xs', xs = x'::xs' => P xs' => P xs) =>
  (forall xs, P xs).
proof strict.
intros=> P_nil P_cons; elim.
  by apply P_nil.
  by intros=> x' xs' P_xs'; apply (P_cons (x'::xs') x' xs').
qed.

(*** Destructors (partially specified) *)
(** Head *)
op hd: 'a list -> 'a.
axiom hd_cons (x:'a) xs: hd (x::xs) = x.

(** Tail *)
op tl: 'a list -> 'a list.
axiom tl_cons (x:'a) xs: tl (x::xs) = xs.

(** Lemma *)
lemma cons_hd_tl (xs:'a list):
  xs <> [] => xs = (hd xs)::(tl xs).
proof strict.
elim/list_case xs=> //= x xs.
by rewrite hd_cons tl_cons.
qed.

(*** Operators *)
(** foldr *)
op foldr (f:'a -> 'b -> 'b) (v:'b) (xs:'a list) =
  with xs = "[]"      => v
  with xs = (::) x xs => f x (foldr f v xs).

(** foldl *)
op foldl (f:'a -> 'b -> 'b) (v:'b) (xs:'a list) =
  with xs = "[]"      => v
  with xs = (::) x xs => foldl f (f x v) xs.

(** mem *)
op mem (e:'a) (xs:'a list) =
  with xs = "[]"      => false
  with xs = (::) x xs => x = e \/ mem e xs.

(* alternate definitions: short-circuiting and foldr *)
op memsc (e:'a) (xs:'a list) =
  with xs = "[]"      => false
  with xs = (::) x xs => x = e || memsc e xs.

lemma memsc_mem (e:'a) xs:
  memsc e xs = mem e xs.
proof strict.
by elim xs=> //= x xs ->; rewrite ora_or.
qed.

lemma mem_foldr (e:'a) xs:
  foldr (fun x b, x = e || b) false xs = mem e xs.
proof strict.
by elim xs=> //= x xs ->; rewrite ora_or.
qed.

(* Lemmas *)
lemma mem_cons_eq (x:'a) xs: mem x (x::xs) by [].
lemma mem_cons_neq (x y:'a) xs: x <> y => mem y (x::xs) = mem y xs by [].

lemma cons_mem (x y:'a) xs: mem y xs => mem y (x::xs) by [].

lemma mem_hd (xs:'a list): mem (hd xs) xs <=> xs <> []
by (split; smt).

lemma nmem_nil (xs:'a list): (forall x, !mem x xs) <=> xs = [] by [].

(** length *)
op length (xs:'a list) =
  with xs = "[]"      => 0
  with xs = (::) x xs => 1 + length xs.

(* Notation *)
op "`|_|":'a list -> int  = length.

(* Lemmas *)
lemma length_nneg (xs:'a list): 0 <= length xs
by (elim xs=> //=; smt).

lemma length_cons_pos (x:'a) xs: 0 < length (x::xs)
by (elim xs=> //=; smt).

lemma length0_nil (xs:'a list): length xs = 0 <=> xs = []
by (elim xs=> //=; smt).

(** append *)
op (++) (xs ys:'a list) =
  with xs = "[]"      => ys
  with xs = (::) x xs => x::(xs ++ ys).

(* Lemmas *)
lemma app_consC (x:'a) xs ys: (x::xs) ++ ys = x::(xs ++ ys)
by elim xs.

lemma appl_nil (xs:'a list): xs ++ [] = xs
by (elim xs=> //= x xs ->).

lemma appA (xs ys zs:'a list):
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
by (elim xs=> //= x xs->).

lemma length_app (xs ys:'a list):
  length (xs ++ ys) = length xs + length ys
by (elim xs=> //= xs ->; smt).

lemma mem_app (y:'a) xs ys:
  mem y (xs ++ ys) = (mem y xs \/ mem y ys)
by (elim xs=> //= x xs ->; rewrite orA).

(** rev *)
op rev (xs:'a list) =
  with xs = "[]"      => []
  with xs = (::) x xs => rev xs ++ [x].

op revacc (acc:'a list) (xs:'a list) =
  with xs = "[]"      => acc
  with xs = (::) x xs => revacc (x::acc) xs.

lemma revacc_rev (xs:'a list):
  revacc [] xs = rev xs.
proof strict.
rewrite -(appl_nil (rev xs)); generalize [].
by elim xs=> //= x xs IH acc; rewrite IH -appA.
qed.

(* Lemmas *)  
lemma rev_app (xs ys:'a list):
  rev (xs ++ ys) = (rev ys) ++ (rev xs).
proof strict.
elim xs=> //=.
  by rewrite appl_nil.
  by intros=> x xs ->; rewrite appA.
qed.

lemma rev_rev (xs:'a list):
  rev (rev xs) = xs.
proof strict.
by elim xs=> //= x xs; rewrite rev_app //= => ->.
qed.

lemma mem_rev (e:'a) xs:
  mem e (rev xs) <=> mem e xs.
proof strict.
by elim xs=> //= x xs; rewrite mem_app orC=> ->.
qed.

lemma eq_rev (xs ys:'a list):
  rev xs = rev ys <=> xs = ys
by [].

(** all *)
pred all (p:'a -> bool) xs = forall x, mem x xs => p x.

(* Direct inductive definition *)
lemma all_nil (p:'a -> bool): all p [] by [].
lemma all_cons (p:'a -> bool) x xs: all p (x::xs) = (p x /\ all p xs) by [].

(* Lemmas *)
lemma all_app (p:'a -> bool) xs ys: all p (xs ++ ys) = (all p xs /\ all p ys) by [].

(** allb *)
op allb (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => true
  with xs = (::) x xs => p x /\ allb p xs.

op allbsc (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => true
  with xs = (::) x xs => p x && allbsc p xs.

(* Lemmas *)
lemma allbsc_allb (p:'a -> bool) (xs:'a list):
  allbsc p xs <=> allb p xs
by (elim xs=> //= x xs ->; rewrite anda_and).

lemma allb_all (p:'a -> bool) xs:
  allb p xs <=> all p xs
by (elim xs=> //= x xs ->; rewrite all_cons).

(** any *)
pred any (p:'a -> bool) xs = exists x, mem x xs /\ p x.

(* Direct inductive definition *)
lemma any_nil (p:'a -> bool): !(any p []) by [].
lemma any_cons (p:'a -> bool) x xs: any p (x::xs) = (p x \/ any p xs) by [].

(* Lemmas *)
lemma any_app (p:('a -> bool)) xs ys: any p (xs ++ ys) = (any p xs \/ any p ys) by [].

(** anyb *)
op anyb (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => false
  with xs = (::) x xs => p x \/ anyb p xs.

op anybsc (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => false
  with xs = (::) x xs => p x || anybsc p xs.

(* Lemmas *)
lemma anybsc_anyb (p:'a -> bool) xs:
  anybsc p xs <=> anyb p xs
by (elim xs=> //= x xs ->; rewrite ora_or).

lemma anyb_any (p:'a -> bool) xs: anyb p xs <=> any p xs
by (elim xs=> //= x xs ->; rewrite any_cons).

(** filter *)
op filter (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => []
  with xs = (::) x xs => let rest = filter p xs in
                         if p x then x::rest else rest.

op revfilter (acc:'a list) (p:'a -> bool) (xs:'a list) =
  with xs = "[]"      => acc
  with xs = (::) x xs => if p x then revfilter (x::acc) p xs
                                else revfilter acc p xs.

(* Lemmas *)
lemma revfilter_filter (p:'a -> bool) xs:
  rev (revfilter [] p xs) = filter p xs.
proof strict.
rewrite -(rev_rev (filter p xs)); congr.
rewrite -(appl_nil (rev (filter p xs))); generalize [].
by elim xs=> //= x xs IH acc; case (p x)=> _; rewrite IH - ?appA.
qed.

lemma filter_cons_in (p:'a -> bool) x xs:
  p x => filter p (x::xs) = x::(filter p xs)
by [].

lemma filter_cons_nin (p:'a -> bool) x xs:
  !(p x) => filter p (x::xs) = filter p xs
by [].

lemma mem_filter (p:'a -> bool) e xs:
  mem e (filter p xs) <=> (mem e xs /\ p e)
by (elim xs=> //=; smt).

lemma filter_app (p:'a -> bool) xs ys:
  filter p (xs ++ ys) = filter p xs ++ filter p ys
by (elim xs=> //= x xs ->; case (p x)).

lemma length_filter (p:'a -> bool) xs:
  length (filter p xs) <= length xs
by (elim xs=> //=; smt).

lemma all_filter (p:'a -> bool) xs:
  all p (filter p xs)
by [].

lemma filter_leq (p q:'a -> bool) xs:
  p <= q =>
  forall x, mem x (filter p xs) => mem x (filter q xs)
by [].

(** map *)
op map (f:'a -> 'b) (xs:'a list) =
  with xs = "[]"      => []
  with xs = (::) x xs => (f x)::(map f xs).

(* Lemmas *)
lemma map_in: forall (f:'a -> 'b) x xs,
  mem x xs => mem (f x) (map f xs).
by intros=> f x xs; elim/list_ind xs; smt.
qed.

lemma mapO: forall (f:'a -> 'b) (g:'b -> 'c) (h:'a -> 'c) xs,
  (forall x, g (f x) = h x) =>
  map g (map f xs) = map h xs.
proof strict.
by intros=> f g h xs fOg; elim/list_ind xs; smt.
qed.

lemma map_app: forall (f:'a -> 'b) xs ys,
  map f (xs ++ ys) = map f xs ++ map f ys.
proof strict.
by intros f xs ys; elim/list_ind xs; smt.
qed.

lemma length_map: forall (f:'a -> 'b) xs,
  length (map f xs) = length xs.
proof strict.
by intros f xs; elim/list_ind xs; smt.
qed.

(** revmap *)
op revmap (acc:'b list) (f:'a -> 'b) (xs:'a list) =
  with xs = "[]"      => acc
  with xs = (::) x xs => revmap ((f x)::acc) f xs.

(* Lemmas *)
lemma revmap_map (f:'a -> 'b) (xs:'a list):
  rev (revmap [] f xs) = map f xs.
proof strict.
rewrite -(rev_rev (map f xs)); congr.
rewrite -(appl_nil (rev (map f xs))); generalize [].
by elim xs=> //= x xs IH acc; rewrite IH - ?appA.
qed.

(** nth *)
require import Option.
require import Pair.

op nth (xs:'a list) n =
  with xs = "[]" => None
  with xs = (::) x xs => if n = 0
                         then Some x
                         else nth xs (n - 1).

(* Lemmas *)
lemma nth_cons0 (x:'a) xs:
  nth (x::xs) 0 = Some x
by done.

lemma nth_consN (x:'a) xs n:
  n <> 0 =>
  nth (x::xs) n = nth xs (n - 1)
by rewrite //= -neqF=> ->.

(* Lemmas *)
lemma nth_neg (xs:'a list) n: n < 0 => nth xs n = None.
proof strict.
generalize n; elim xs=> //= x xs IH n n_neg.
cut ->: (n = 0) = false by smt.
by rewrite //= IH; smt.
qed.

lemma nth_geq_len (xs:'a list) n: length xs <= n => nth xs n = None.
proof strict.
generalize n; elim xs=> //= x xs IH n n_geq_len.
cut ->: (n = 0) = false by smt.
by rewrite //= IH; smt.
qed.

lemma nth_range (xs:'a list) n:
  0 <= n < length xs =>
  nth xs n <> None.
proof strict.
generalize n; elim xs=> //=; first smt.
intros=> x xs IH n n_range; case (n = 0)=> // neq0_n.
by rewrite IH; smt.
qed.

lemma mem_nth (xs:'a list) (n:int):
  0 <= n < length xs =>
  mem (proj (nth xs n)) xs.
proof strict.
generalize n; elim xs=> //=; first smt.
intros=> x xs IH n n_range; case (n = 0).
  by rewrite proj_some=> _; left.
  by intros=> neq0_n; right; rewrite IH; first smt.
qed.

lemma mem_ex_nth (e:'a) (xs:'a list):
  mem e xs =>
  exists (n:int), 0 <= n < length xs /\ nth xs n = Some e.
proof strict.
elim xs=> //= x xs IH [x_e | e_in_xs].
  by exists 0; split=> //=; [smt|rewrite x_e].
  by apply IH in e_in_xs; elim e_in_xs=> n [n_bnd nth_e];
     exists (n + 1); smt.
qed.

lemma nth_append_left (ys xs:'a list) (n:int):
  0 <= n < length xs =>
  proj (nth (xs ++ ys) n) = proj (nth xs n).
proof strict.
generalize n; elim xs=> //=; first smt.
intros=> x xs IH n n_bnd; case (n = 0)=> //=.
by intros=> neq0_n; rewrite IH; first smt.
qed.

lemma nth_append_right (xs ys:'a list) (n:int):
  length xs <= n < length xs + length ys =>
  proj (nth (xs ++ ys) n) = proj (nth ys (n - length xs)).
proof strict.
generalize n; elim xs=> //= x xs IH n n_bnd.
cut ->: (n = 0) = false by smt.
by rewrite //= IH; smt.
qed.

(** nth_default *)
op nth_default (xs:'a list) (dv:'a) n =
  let r = nth xs n in
  if (r <> None) then proj r
                 else dv.

(** count *)
op count (e:'a) (xs:'a list) =
  with xs = "[]"      => 0
  with xs = (::) x xs => count e xs + ((x = e)?1:0).

op countacc (acc:int) (e:'a) (xs:'a list) =
  with xs = "[]"      => acc
  with xs = (::) x xs => countacc (acc + ((x = e)?1:0)) e xs.

(* Lemmas *)
lemma countacc_count (e:'a) xs:
  countacc 0 e xs = count e xs.
proof strict.
cut ->: count e xs = count e xs + 0 by smt; generalize 0.
elim xs=> //= x xs IH n; case (x = e).
  by rewrite IH; smt.
  by rewrite /= IH.
qed.

lemma nosmt count_cons_eq (x:'a) xs: count x (x::xs) = 1 + count x xs by [].
lemma nosmt count_cons_neq (x y:'a) xs: x <> y => count y (x::xs) = count y xs by [].

lemma leq0_count (e:'a) (xs:'a list):
  0 <= count e xs.
proof strict.
by elim xs=> //= x xs IH; smt.
qed.

lemma count_mem (e:'a) (xs:'a list):
  0 <> count e xs <=> mem e xs.
proof strict.
elim xs=> //= x xs IH; case (x = e)=> /=.
  smt.
  by rewrite IH.
qed.

(** DONE *)
(** unique *)
op unique:'a list -> bool.
axiom unique_nil: unique<:'a> [].
axiom unique_cons: forall (x:'a) xs, unique (x::xs) = (unique xs /\ !mem x xs).

(* Lemmas *)
lemma unique_count: forall (xs:'a list),
  unique xs <=> (forall x, count x xs <= 1).
proof strict.
intros=> xs; split.
  elim/list_ind xs.
    by intros=> h x {h} //=; smt.
    intros=> x xs IH; rewrite unique_cons -count_mem;
    simplify; intros=> [u_xs x_nin_xs] x'; case (x = x')=> x_x'.
      by subst x'; rewrite -x_nin_xs; smt.
      by rewrite /= IH.
  elim/list_ind xs.
    by intros=> h {h}; apply unique_nil.
    intros=> x xs IH count_xs; rewrite unique_cons; split.
     apply IH => x'. 
     by cut _ : count x' xs <= count x' (x :: xs); smt.
     by cut _ : count x (x :: xs) <= 1; smt.
qed.

(** rm *)
op rm:'a -> 'a list -> 'a list.
axiom rm_nil: forall (x:'a), rm x [] = [].
axiom rm_cons: forall (y x:'a) xs, rm y (x::xs) = ((x = y) ? xs : (x::rm y xs)).

(* Lemmas *)
lemma nosmt rm_consE: forall (x:'a) xs, rm x (x::xs) = xs by [].
lemma nosmt rm_consNE: forall (x y:'a) xs, x <> y => rm y (x::xs) = x::(rm y xs) by [].

lemma length_rm: forall (x:'a) xs,
  mem x xs =>
  length (rm x xs) = length xs - 1.
proof strict.
intros=> x xs; elim/list_ind xs.
  by apply absurd=> h {h} //=.
  intros=> x' xs IH x_in_xs //=; case (x' = x)=> x_x'.
    by subst x'; rewrite rm_consE; smt.
    generalize x_in_xs; rewrite // rm_consNE //= => x_in_xs; rewrite IH //; smt.
qed.

lemma count_rm_in: forall (x:'a) (xs:'a list),
  mem x xs =>
  count x (rm x xs) = count x xs - 1.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x.
  apply absurd=> _ //=.
  intros=> xs IH y x'; rewrite rm_cons (rewrite_if (count y)); smt.
qed.

lemma count_rm_nin: forall (x:'a) (xs:'a list),
  !mem x xs =>
  count x (rm x xs) = count x xs.
proof strict.
intros=> x xs; generalize x; elim/list_ind xs=> x.
  intros=> h {h}; rewrite rm_nil //.
  intros=> xs IH x' //=; smt.
qed.

lemma count_rm_neq: forall (x y:'a) (xs:'a list),
  y <> x =>
  count x (rm y xs) = count x xs.
proof strict.
intros=> x y xs; elim/list_ind xs.
  rewrite rm_nil //.
  intros=> x' xs IH x_y; smt.
qed.

theory PermutationLists.
  (** Equality up to permutation *)
  pred (<->) (xs xs':'a list) =
    forall (x:'a), count x xs = count x xs'.

  lemma perm_refl: forall (xs:'a list), xs <-> xs by [].
  lemma perm_symm: forall (xs ys:'a list), xs <-> ys => ys <-> xs by [].
  lemma perm_trans: forall (ys xs zs:'a list), xs <-> ys => ys <-> zs => xs <-> zs by [].

  lemma perm_nil: forall (xs:'a list),
    xs <-> [] =>
    xs = [].
  proof strict.
  intros=> xs; delta (<->) beta=> xs_nil;
  cut h: forall (x:'a), count x xs = 0.
    by intros=> x; rewrite xs_nil.
  by apply nmem_nil=> x; rewrite -count_mem eq_sym //= h.
  qed.

  lemma perm_cons: forall x (xs ys:'a list),
    xs <-> ys =>
    (x::xs) <-> (x::ys)
  by [].

  lemma perm_rm: forall x (xs ys:'a list),
    xs <-> ys =>
    (rm x xs) <-> (rm x ys).
  proof strict.
  intros=> x xs ys; case (mem x xs).
    intros=> x_in_xs xs_ys; cut x_in_ys: mem x ys; first by rewrite -count_mem -(xs_ys x) count_mem //.
    delta (<->) beta=> x'; case (x = x')=> x_x'.
        subst x'; rewrite count_rm_in // count_rm_in // xs_ys //.
        rewrite count_rm_neq // count_rm_neq // xs_ys //.
    intros=> x_nin_xs xs_ys; cut x_nin_ys: !mem x ys; first by rewrite -count_mem -(xs_ys x) count_mem //.
      delta (<->) beta=> x'; case (x = x')=> x_x'.
        subst x'; rewrite count_rm_nin // count_rm_nin // xs_ys //.
        rewrite count_rm_neq // count_rm_neq // xs_ys //.
  qed.

  lemma foldC: forall (x:'a) (f:'a -> 'b -> 'b) (z:'b) (xs:'a list),
      (forall a b X, f a (f b X) = f b (f a X)) =>
      mem x xs =>
      foldr f z xs = f x (foldr f z (rm x xs)).
  proof strict.
  intros=> x f z xs C; elim/list_ind xs; first smt.
    intros=> x' xs IH //=.
    case (x' = x)=> x_x';first subst x';rewrite rm_consE //.
    intros=> // x_in_xs.
    by rewrite rm_consNE //= IH // C //.
  qed.

  lemma foldCA: forall (f:'a -> 'a -> 'a) (z x:'a) (xs:'a list),
    (forall x y, f x y = f y x) =>
    (forall x y z, f x (f y z) = f (f x y) z) =>
    mem x xs =>
    foldr f z xs = f x (foldr f z (rm x xs)).
  proof strict.
  intros f z x xs C A.
  apply foldC=> a b c.
  rewrite A (C a) -A //.
  qed.

  lemma fold_permC: forall (f:'a -> 'b -> 'b) (z:'b) (xs ys:'a list),
    (forall a b X, f a (f b X) = f b (f a X)) =>
    xs <-> ys =>
    foldr f z xs = foldr f z ys.
  proof strict.
  intros=> f z xs ys C;generalize ys; elim/list_ind xs.
    by intros=> ys nil_ys; rewrite (perm_nil ys); [apply perm_symm=> // | trivial ].
    intros=> x xs IH ys xs_ys; rewrite (foldC x _ _ ys); first assumption.
    rewrite -count_mem -xs_ys; smt.
       cut rm_xs_ys: xs <-> rm x ys;
         first by rewrite -(rm_consE x xs); apply perm_rm=> //.
        rewrite //= (IH (rm x ys))=> //.
  qed.

  lemma fold_perm: forall (f:'a -> 'a -> 'a) (z:'a) (xs ys:'a list),
    (forall x y, f x y = f y x) =>
    (forall x y z, f x (f y z) = f (f x y) z) =>
    xs <-> ys =>
    foldr f z xs = foldr f z ys.
  proof strict.
  intros f z x xs C A.
  apply fold_permC=> a b c.
  rewrite A (C a) -A //.
  qed.

  (** Properties of unique lists up to permutation *)
  lemma perm_unique: forall (xs ys:'a list),
    xs <-> ys =>
    unique xs =>
    unique ys
  by [].

  lemma cons_nin: forall (x:'a) (xs ys:'a list),
    unique ys =>
    x::xs <-> ys =>
    !mem x xs
  by [].

  lemma perm_length: forall (xs ys:'a list),
    xs <-> ys =>
    length xs = length ys.
  proof strict.
  intros=> xs; elim/list_ind xs.
    smt.
    intros=> x xs IH ys xs_ys //=.
      rewrite (IH (rm x ys)).
        by rewrite -(rm_consE x xs); apply perm_rm=> //. (* This should become a lemma *)
        by rewrite length_rm; smt.
  qed.
end PermutationLists.
