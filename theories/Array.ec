(* A theory of polymorphic arrays. *)

(*
 * All operators are only partially specified, as we may choose to match
 * them with various programming language constructs.
 * 
 * The user wanting to instantiate it with particular implementation
 * choices should clone it and add axioms to further refine the
 * operators.
 *
 * The operator names for imperative operators correspond to the OCaml Array library.
 *
 *)

require import Logic.
require import Int.
require Fun. (* For reasoning about higher-order operators *)

(*********************************)
(*             Core              *)
(*********************************)
(* A type *)
type 'x array.

(* Arrays have a non-negative length *)
op length: 'x array -> int.
axiom length_pos: forall (xs:'x array), 0 <= length xs.

op "`|_|" (xs:'x array) = length xs.

(* And a bunch of elements *)
op "_.[_]": 'x array -> int -> 'x.

(* Equality is extensional *)
pred (==) (xs0 xs1:'x array) =
  length xs0 = length xs1 /\
  forall (i:int), 0 <= i < length xs0 => xs0.[i] = xs1.[i].

axiom array_ext (xs0 xs1:'x array):
  xs0 == xs1 => xs0 = xs1.

lemma rw_array_ext (xs0 xs1:'x array):
  xs0 == xs1 <=> xs0 = xs1.
proof strict.
by split; first apply array_ext.
qed.

(*********************************)
(*    "Functional" Operators     *)
(*********************************)
(* Using these should be avoided when extracting,
   for performance reasons. *)
(* empty *)
op empty: 'x array.

axiom length_empty: length (empty<:'x>) = 0.

lemma empty_unique (xs:'x array):
  length(xs) = 0 => xs = empty.
proof strict.
by intros=> xs_0; apply array_ext; split;
     [rewrite length_empty | smt].
qed.

(* cons *)
op "_::_" : 'x -> 'x array -> 'x array.

axiom length_cons (x:'x) (xs:'x array):
  length (x::xs) = 1 + length xs.

axiom get_cons (x:'x) (xs:'x array) (i:int):
  0 <= i <= length xs =>
  (x::xs).[i] = (0 = i) ? x : xs.[i - 1].

lemma cons_nonempty (x:'x) (xs:'x array):
  x::xs <> empty.
proof strict.
by rewrite -not_def=> cons_empty;
   cut:= fcongr length (x::xs) empty _=> //;
   rewrite length_empty length_cons; smt.
qed.

lemma consI (x y:'x) (xs ys:'x array):
  x::xs = y::ys <=> x = y /\ xs = ys.
proof strict.
split; last by intros=> [-> ->].
rewrite - !rw_array_ext /(==)=> [len val].
do !split.
  cut:= val 0 _; first smt.
  by rewrite 2?get_cons /=; first 2 smt.
  by generalize len; rewrite 2!length_cons; smt.
  intros=> i i_bnd; cut := val (i + 1) _; first smt.
  rewrite 2?get_cons; first 2 smt.
  by cut ->: (0 = i + 1) = false by smt; cut ->: i + 1 - 1 = i by smt.
qed.

(* snoc *)
op (:::): 'x array -> 'x -> 'x array.

axiom length_snoc (x:'x) (xs:'x array):
  length (xs:::x) = length xs + 1.

axiom get_snoc (xs:'x array) (x:'x) (i:int):
  0 <= i <= length xs =>
  (xs:::x).[i] = (i < length xs) ? xs.[i] : x.

lemma snoc_nonempty (xs:'x array, x:'x):
  xs:::x <> empty.
proof strict.
by rewrite -not_def=> snoc_empty;
   cut:= fcongr length (xs:::x) empty _=> //;
   rewrite length_empty length_snoc; smt.
qed.

(* Induction Principle *)
axiom array_ind (p:'x array -> bool):
  p empty =>
  (forall x xs, p xs => p (x::xs)) =>
  (forall xs, p xs).

(***************************)
(*      OCaml Arrays       *)
(***************************)
(* set *)
op "_.[_<-_]": 'x array -> int -> 'x -> 'x array.

axiom length_set (i:int) (x:'x) (xs:'x array):
  length (xs.[i <- x]) = length xs.

axiom get_set (xs:'x array) (i j:int) (x:'x):
  0 <= j < length xs =>
  xs.[i <- x].[j] = (i = j) ? x : xs.[j].

lemma set_set i j (x y:'x) xs:
  xs.[i <- x].[j <- y] =
    (i = j) ? xs.[j <- y] :
              xs.[j <- y].[i <- x].
proof strict.
by apply array_ext; split; smt.
qed.

lemma nosmt set_setE x i (y:'a) xs:
  xs.[i <- x].[i <- y] = xs.[i <- y].
proof strict.
by rewrite set_set.
qed.

lemma nosmt set_setN x i j (y:'a) xs:
  i <> j =>
  xs.[i <- x].[j <- y] = xs.[j <- y].[i <- x].
proof strict.
by rewrite set_set -neqF=> ->.
qed.

(* make *)
op make: int -> 'x -> 'x array.

axiom length_make (x:'x) l:
  0 <= l =>
  length (make l x) = l.

axiom get_make l (x:'x) i:
  0 <= i < l =>
  (make l x).[i] = x.

(* init *)
op init: int -> (int -> 'x) -> 'x array.

axiom length_init (f:int -> 'x) l:
  0 <= l =>
  length (init l f) = l.

axiom get_init l (f:int -> 'x) i:
  0 <= i < l =>
  (init l f).[i] = f i.

(* append *)
op (||): 'x array -> 'x array -> 'x array.

axiom length_append (xs0 xs1:'x array):
  length (xs0 || xs1) = length xs0 + length xs1.

axiom get_append (xs0 xs1:'x array) (i:int):
  0 <= i < length (xs0 || xs1) =>
  (xs0 || xs1).[i] = (0 <= i < length xs0) ? xs0.[i] : xs1.[i - length xs0].

lemma nosmt get_append_left (xs0 xs1:'x array) (i:int):
 0 <= i < length xs0 =>
 (xs0 || xs1).[i] = xs0.[i]
by smt.

lemma nosmt get_append_right (xs0 xs1:'x array) (i:int):
 length xs0 <= i < length xs0 + length xs1 =>
 (xs0 || xs1).[i] = xs1.[i - length xs0]
by smt.

(* sub *)
op sub: 'x array -> int -> int -> 'x array.

axiom length_sub (xs:'x array) (s l:int):
  0 <= s => 0 <= l => s + l <= length xs =>
  length (sub xs s l) = l.

axiom get_sub (xs:'x array) (s l i:int):
  0 <= s => 0 <= l => s + l <= length xs =>
  0 <= i < l =>
  (sub xs s l).[i] = xs.[i + s].

(* fill *)
op fill: 'x array -> int -> int -> 'x -> 'x array.

axiom length_fill (s l:int) x (xs:'x array):
  0 <= s => 0 <= l => s + l <= length xs =>
  length (fill xs s l x) = length xs.

axiom get_fill (xs:'x array) (s l:int) x i:
  0 <= s => 0 <= l => s + l <= length xs =>
  0 <= i < length xs =>
  (fill xs s l x).[i] = (s <= i < s + l) ? x : xs.[i].

(* blit (previously write) *)
op blit: 'x array -> int -> 'x array -> int -> int -> 'x array.

axiom length_blit (dst src:'x array) (dOff sOff l:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  length (blit dst dOff src sOff l) = length dst.

axiom get_blit (dst src:'x array) (dOff sOff l i:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  0 <= i < length dst =>
  (blit dst dOff src sOff l).[i] =
    (dOff <= i < dOff + l) ? src.[i - dOff + sOff]
                           : dst.[i].

(* map *)
op map: ('x -> 'y) -> 'x array -> 'y array.

axiom length_map (xs:'x array) (f:'x -> 'y):
  length (map f xs) = length xs.

axiom get_map (xs:'x array) (f:'x -> 'y, i:int):
  0 <= i < length(xs) =>
  (map f xs).[i] = f (xs.[i]).

(* map2 *) (* Useful for bitwise operations *)
op map2: ('x -> 'y -> 'z) -> 'x array -> 'y array -> 'z array.

axiom length_map2 (xs:'x array) (ys:'y array) (f:'x -> 'y -> 'z):
  length xs = length ys =>
  length (map2 f xs ys) = length xs.

axiom get_map2 (xs:'x array) (ys:'y array) (f:'x -> 'y -> 'z, i:int):
  length xs = length ys =>
  0 <= i < length xs =>
  (map2 f xs ys).[i] = f (xs.[i]) (ys.[i]).

(* mapi *)
op mapi: (int -> 'x -> 'y) -> 'x array -> 'y array.

axiom length_mapi (f:int -> 'x -> 'y) (xs:'x array):
  length (mapi f xs) = length xs.

axiom get_mapi (f:int -> 'x -> 'y) (xs:'x array) (i:int):
  0 <= i < length xs =>
  (mapi f xs).[i] = f i (xs.[i]).

(* fold_left *)
op fold_left: ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state.

axiom fold_left_empty (f:'state -> 'x -> 'state) s:
  (fold_left f s empty) = s.

axiom fold_left_cons (f:'state -> 'x -> 'state) s xs:
  0 < length xs =>
  (fold_left f s xs) = f (fold_left f s (sub xs 1 (length xs - 1))) xs.[0].

(* fold_right *)
op fold_right: ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state.

axiom fold_right_empty xs (f:'state -> 'x -> 'state) s:
  length xs = 0 =>
  (fold_right f s xs) = s.

axiom fold_right_cons (f:'state -> 'x -> 'state) s xs:
  0 < length xs =>
  (fold_right f s xs) = fold_right f (f s xs.[0]) (sub xs 1 (length xs - 1)).

(* lemmas *)
lemma empty_append_l (xs:'x array):
  (xs || empty) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_append length_empty.
  by intros=> i; rewrite length_append length_empty /= => i_bnd;
     rewrite get_append ?length_append ?length_empty /= // i_bnd.
qed.

lemma empty_append_r (xs:'x array):
  (empty || xs) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_append length_empty.
  by intros=> i; rewrite length_append length_empty /= => i_bnd;
     rewrite get_append ?length_append ?length_empty /= //;
     cut ->: (0 <= i < 0) = false by smt.
qed.

lemma sub_cons x (xs:'x array):
  sub (x::xs) 1 (length (x::xs) - 1) = xs.
proof strict.
apply array_ext; smt.
qed.

lemma sub_full (xs:'x array):
  sub xs 0 (length xs) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_sub; first 2 smt.
  by intros=> i; rewrite length_sub //=; first 2 smt.
qed.

lemma sub_append_l (xs0 xs1:'x array):
  sub (xs0 || xs1) 0 (length xs0) = xs0.
proof strict.
by apply array_ext; split; smt.
qed.

lemma sub_append_r (xs0 xs1:'x array):
  sub (xs0 || xs1) (length xs0) (length xs1) = xs1.
proof strict.
by apply array_ext; split; smt.
qed.

lemma sub_append_sub (xs:'x array) (i l1 l2:int):
  0 <= i => 0 <= l1 => 0 <= l2 => i + l1 + l2 <= length xs =>
  (sub xs i l1 || sub xs (i + l1) l2) = sub xs i (l1 + l2).
proof strict.
by intros=> i_pos l1_pos l2_pos i_l1_l2_bnd;
   apply array_ext; split; smt.
qed.

lemma map_map (f:'x -> 'y) (g:'y -> 'z) xs:
 map g (map f xs) = map (fun x, g (f x)) xs.
proof strict.
apply array_ext; split.
  by rewrite !length_map.
  by intros=> i; rewrite !length_map=> i_bnd;
     rewrite !get_map ?length_map.
qed.

lemma map_cons (f:'x -> 'y) x xs:
  map f (x::xs) = (f x)::(map f xs).
proof strict.
apply array_ext; split; smt.
qed.

lemma mapi_mapi (f:int -> 'x -> 'y) (g:int -> 'y -> 'z) xs:
 mapi g (mapi f xs) = mapi (fun k x, g k (f k x)) xs.
proof strict.
apply array_ext; split.
  by rewrite !length_mapi.
  by intros=> i; rewrite !length_mapi=> i_bnd; rewrite ?get_mapi ?length_mapi.
qed.

lemma mapi_id (f:int -> 'x -> 'x) (xs:'x array):
 (forall k x, 0 <= k < length xs => f k x = x) =>
 mapi f xs = xs.
proof strict.
intros=> f_id; apply array_ext; split.
  by rewrite length_mapi.
  by intros=> i; rewrite !length_mapi=> i_bnd; rewrite ?get_mapi ?length_mapi ?f_id.
qed.

(* Useless? *)
lemma fold_left_deterministic: forall (f1 f2:'state -> 'x -> 'state) s1 s2 xs1 xs2,
  f1 = f2 => s1 = s2 => xs1 = xs2 =>
  fold_left f1 s1 xs1 = fold_left f2 s2 xs2
by [].

lemma fold_right_map (f:'x -> 'y -> 'x) (x:'x) (g:'z -> 'y) (zs:'z array):
 fold_right f x (map g zs) = fold_right (fun x y, f x (g y)) x zs.
proof strict.
 elim/array_ind zs x.
  by intros=> x; rewrite !fold_right_empty ?length_map ?length_empty.
  intros=> z zs IH x; rewrite !(fold_right_cons _ x); first 2 smt.
  by rewrite map_cons !sub_cons IH 2?get_cons; first 2 smt.
qed.

(* Alternative induction principle: building arrays from the back *)
lemma array_ind_snoc (p:'x array -> bool):
  p empty =>
  (forall x xs, p xs => p (xs:::x)) =>
  (forall xs, p xs).
proof strict.
intros=> p0 prec xs.
cut h : (forall n, 0 <= n => forall xs, length xs = n => p xs).
  elim/Induction.induction => //; first smt.
  intros=> i ipos hrec xs' hlen.
  cut ->: xs' = (sub xs' 0 i):::xs'.[i] by (apply array_ext; smt).
  apply prec.
  apply hrec.  
  by rewrite length_sub; smt.
by apply (h (length xs) _);smt.
qed.

(* This proof needs cleaned up, and the lemma library completed. *)
lemma fold_length (xs:'x array):
  fold_left (fun n x, n + 1) 0 xs = length xs.
proof strict.
elim/array_ind xs.
  by rewrite fold_left_empty length_empty.
  by intros=> x xs IH; rewrite fold_left_cons;
       [ | cut ->: sub (x::xs) 1 (length (x::xs) - 1) = xs by (apply array_ext; smt)];
     smt.
qed.

lemma blit_append (dst src:'x array):
  length src <= length dst =>
  blit dst 0 src 0 (length src) = (src || (sub dst (length src) (length dst - length src))).
proof strict.
intros=> src_dst; apply array_ext; split; smt.
qed.

(** Things that are not in the OCaml array library:
      - take and drop (prefix and suffix),
      - complex initialization,
      - logical predicates *)
(* take *)
op take (len:int) (xs:'a array) = sub xs 0 len.

lemma length_take (xs:'a array) (l:int):
  0 <= l <= length xs =>
  length (take l xs) = l
by smt.

lemma get_take (xs:'a array) (l k:int):
  0 <= k < l <= length xs =>
  (take l xs).[k] = xs.[k]
by smt.

(* drop *)
op drop (len:int) (xs:'a array) = sub xs len (length xs-len).

lemma length_drop (xs:'a array) (l:int):
  0 <= l <= length xs =>
  length (drop l xs) = length xs - l
by smt.

lemma get_drop  (xs:'a array) (l k:int):
  0 <= l => 0 <= k < length xs-l =>
  (drop l xs).[k] = xs.[l + k]
by smt.

lemma take_drop (xs:'a array) (l:int):
  0 <= l <= length xs =>
  (take l xs || drop l xs) = xs
by smt.

(* init_dep: init, but using a function that may depend
   on the rest of the array! *)
op init_dep: 'x array -> int -> (int -> 'x array -> 'x) -> 'x array.

axiom init_dep_def (xs:'x array) (size:int) (f:int -> 'x array -> 'x):
  init_dep xs size f =
    let r = make (length xs + size) xs.[0] in (* creates the space *)
    let r = blit r 0 xs 0 (length xs) in      (* copies the initial value in *)
    ForLoop.range 0 size r (fun i r, r.[i + length xs <- f i r]). (* extends using f *)

(* all: this is computable because all arrays are finite *)
op all: ('x -> bool) -> 'x array -> bool.

axiom all_def p (xs:'x array):
  all p xs <=>
  (forall i, 0 <= i < length xs => p xs.[i]).

(* alli *)
op alli: (int -> 'x -> bool) -> 'x array -> bool.

axiom alli_def p (xs:'x array):
  alli p xs <=>
  (forall i, 0 <= i < length xs => p i xs.[i]).

lemma alli_base p: alli p empty<:'x>.
proof strict.
by rewrite alli_def length_empty; smt.
qed.

lemma alli_ind p (x:'x) xs:
  alli p (x::xs) =
    (p 0 x /\ alli (fun i x, p (i + 1) x) xs).
proof strict.
rewrite (alli_def _ xs).
cut ->: (p 0 x /\ forall (i:int), 0 <= i < length xs => (fun i x, p (i + 1) x) i xs.[i]) <=>
         forall (i:int), 0 <= i < length (x::xs) => p i (x::xs).[i].
  split; first smt.
  intros=> alli; split.
    by cut ->: x = (x::xs).[0]
         by (rewrite get_cons //=; smt);
       apply alli; first smt.
    by intros=> i i_bnd //=;
       cut ->: xs.[i] = (x::xs).[i + 1]
         by (rewrite get_cons //=; smt);
       apply alli; first smt.
by rewrite -alli_def.
qed.

lemma alli_true p (xs:'x array):
  (forall i x, p i x) =>
  alli p xs.
proof strict.
by rewrite alli_def=> p_true i i_bnd;
   apply p_true.
qed.

(* note: I'm not sure this is the most useful formulation of this lemma. Check use cases. *)
(* overall, I feel that the general rangeb_forall is more useful *)
lemma range_alli i j p (xs:'x array):
  0 <= i < j < length xs =>
  ForLoop.range i j true (fun k b, b /\ p k xs.[k]) <=>
   alli (fun k, p (k + i)) (sub xs i (j - i)).
proof strict.
intros=> i_j_bnd.
cut ->: (fun k b, b /\ p k xs.[k]) =
         (fun k b, b /\ (fun k, p k xs.[k]) k) by smt.
rewrite ForLoop.rangeb_forall //=.
rewrite alli_def length_sub; first 3 smt.
split.
  intros=> all_ij k k_bnd; rewrite get_sub=> //=; first 3 smt.
  by apply all_ij; smt.
  intros=> //= all_ij k k_bnd; rewrite {2}(_: k = k - i + i); first smt.
  rewrite -(get_sub xs i (j - i) (k - i)); first 4 smt.
  pose k':= k - i; cut ->: k = k' + i by smt.
  by apply all_ij; smt.
qed.

(* TODO *)

(** Distribution on 'a array of length k from distribution on 'a *)
(* We return the empty array when the length is negative *)
theory Darray.
  require import Distr.
  require import Real.

  op darray: int -> 'a distr -> 'a array distr.

  (* Negative length case... This appears to be a necessary evil for now *)
  (* At least it's only one axiom *)
  axiom mu_neg (len:int) (d:'a distr) (p:'a array -> bool):
    len < 0 =>
    mu (darray len d) p = charfun p empty.

  lemma mu_x (len:int) (d:'a distr) (x:'a array):
    len < 0 =>
    mu_x (darray len d) x = if x = empty then 1%r else 0%r.
  proof strict.
  rewrite /mu_x=> len_neg; case (x = empty).
    by intros=> ->; rewrite mu_neg.
    by rewrite mu_neg // /charfun -neqF=> ->.
  qed.

  lemma supp_neg (len:int) (d:'a distr) (x:'a array):
    len < 0 =>
    in_supp x (darray len d) <=> x = empty
  by [].

  lemma weight_neg (len:int) (d:'a distr):
    len < 0 =>
    weight (darray len d) = 1%r
  by [].

  (* Non-negative length case *)
  axiom mu_x_def (len: int) (d:'a distr) (x:'a array):
    len = length x =>
    mu_x (darray len d) x = fold_right (fun p x, p * mu_x d x) 1%r x.

  axiom supp_def (len:int) (x:'a array) (d:'a distr):
    0 <= len =>
    in_supp x (darray len d) <=>
    (length x = len /\ all (support d) x).

  lemma supp_full (len:int) (d:'a distr) (x:'a array):
    0 <= len =>
    (forall y, in_supp y d) =>
    length x = len <=> in_supp x (darray len d).
  proof strict.
  intros leq0_len dF; split.
    by intros=> Hlen; rewrite Darray.supp_def=> //; split=> //;
       rewrite all_def=> i Hi; rewrite /support dF.
    by rewrite Darray.supp_def.
  qed.

  lemma supp_len (len:int) (x: 'a array) (d:'a distr):
    0 <= len =>
    in_supp x (darray len d) => length x = len.
  proof strict. by intros=> leq0_len; rewrite supp_def. qed.

  lemma supp_k (len:int) (x: 'a array) (d:'a distr) (k:int):
    0 <= k < len =>
    in_supp x (darray len d) =>
    in_supp x.[k] d.
  proof strict.
  intros=> k_bnd; rewrite supp_def -/(support d x.[k]); first smt.
  by intros=> [len_def all_in_supp]; subst;
     generalize all_in_supp; rewrite all_def=> H; apply H.
  qed.

  (* This would be a lemma by definition of ^
     if we had it in the correct form (if we know that Real is a field) *)
  axiom weight_d (d:'a distr) len:
    0 <= len => weight (darray len d) = (weight d) ^ len.

  lemma darrayL (d:'a distr) len:
    0 <= len =>
    weight d = 1%r =>
    weight (darray len d) = 1%r.
  proof strict.
  intros leq0_len H; rewrite (weight_d d len) // H.
  smt "Alt-Ergo".
  qed.

  (* if len is negative, then uniformity is easy to prove.
     otherwise, the folded function can be replaced with the same constant for x and y
     (but we need to know that it is only applied to elements of d's support,
      which justifies leaving it as an axiom for now) *)
  axiom uniform (d:'a distr) len:
    isuniform d =>
    isuniform (darray len d).
end Darray.
