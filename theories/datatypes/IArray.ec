(* -------------------------------------------------------------------- *)
(* Length-indexed arrays.  [ 'a array<:n> ] is the type of arrays of [ 'a ]
   of length [n]; the length lives in the index rather than in a runtime
   [size] field.  Indexed counterpart of [Array.ec] (subsuming [Word.eca]).

   The derived operators and lemmas live in a [declare index {n}] section, so they
   are written without a [{n}] binder and get one back on section close.
   Proofs that need [0 <= n] obtain it explicitly from [Int.ge0_index]. *)

require import AllCore List.

(* -------------------------------------------------------------------- *)
(* Signature: the indexed type and its reflection to lists.  Model for
   the three axioms: ['a array<:n>] IS the length-[n] ['a list]s, with
   [ofarr]/[mkarr] the identity (and [mkarr] arbitrary off-length). *)
type {n} 'a array.

op ofarr {n} ['a] (a : 'a array<:n>) : 'a list.
op mkarr {n} ['a] (s : 'a list) : 'a array<:n>.

axiom size_ofarr {n} ['a] (a : 'a array<:n>) :
  size (ofarr a) = n.

axiom ofarrK {n} ['a] (a : 'a array<:n>) :
  mkarr (ofarr a) = a.

axiom mkarrK {n} ['a] (s : 'a list) :
  size s = n => ofarr (mkarr[:n] s) = s.

(* ==================================================================== *)
section IArray.
declare index {n}.

(* -------------------------------------------------------------------- *)
(* Single-head accessors, [opaque] as in Array.ec: the lemmas below are
   the interface; simplify/delta do not see the list model. *)
op [opaque] "_.[_]" ['a] (a : 'a array<:n>) (i : int) : 'a =
  nth witness (ofarr a) i.

op [opaque] "_.[_<-_]" ['a] (a : 'a array<:n>) (i : int) (x : 'a) : 'a array<:n> =
  mkarr (mkseq (fun k => if i = k then x else a.[k]) n).

(* -------------------------------------------------------------------- *)
lemma getE ['a] (a : 'a array<:n>) i :
  a.[i] = nth witness (ofarr a) i.
proof. by rewrite /"_.[_]". qed.

lemma get_neg ['a] (a : 'a array<:n>) (i : int) :
  i < 0 => a.[i] = witness.
proof. by rewrite getE; apply/nth_neg. qed.

lemma get_default ['a] (a : 'a array<:n>) (i : int) :
  n <= i => a.[i] = witness.
proof. by rewrite getE -(size_ofarr a); apply/nth_default. qed.

lemma eq_from_get ['a] (a1 a2 : 'a array<:n>) :
  (forall i, 0 <= i < n => a1.[i] = a2.[i]) => a1 = a2.
proof.
move=> eq_get; rewrite -(ofarrK a1) -(ofarrK a2); congr.
apply/(eq_from_nth witness); first by rewrite !size_ofarr.
by move=> i; rewrite (size_ofarr a1) -!getE => /eq_get.
qed.

lemma arrayP ['a] (a1 a2 : 'a array<:n>) :
  (a1 = a2) <=> (forall i, 0 <= i < n => a1.[i] = a2.[i]).
proof. by split=> [-> //|]; apply/eq_from_get. qed.

lemma ofarr_inj ['a] (a1 a2 : 'a array<:n>) :
  ofarr a1 = ofarr a2 => a1 = a2.
proof. by move=> h; rewrite -(ofarrK a1) -(ofarrK a2) h. qed.

(* [mkarr] is injective on length-[n] lists only (off-length lists are
   mapped arbitrarily). *)
lemma mkarr_pinj ['a] (s1 s2 : 'a list) :
  size s1 = n => size s2 = n =>
  mkarr[:n] s1 = mkarr[:n] s2 => s1 = s2.
proof. by move=> h1 h2 h; rewrite -(mkarrK[:n] s1) // -(mkarrK[:n] s2) // h. qed.

lemma arrayW ['a] (P : 'a array<:n> -> bool) :
  (forall s, size s = n => P (mkarr s)) => forall a, P a.
proof. by move=> ih a; rewrite -(ofarrK a); apply/ih; rewrite size_ofarr. qed.

(* -------------------------------------------------------------------- *)
lemma setE ['a] (a : 'a array<:n>) (i : int) (x : 'a) :
  a.[i <- x] = mkarr (mkseq (fun k => if i = k then x else a.[k]) n).
proof. by rewrite /"_.[_<-_]". qed.

lemma get_set_if ['a] (a : 'a array<:n>) (x : 'a) (i j : int) :
  a.[i <- x].[j] = if 0 <= i < n /\ j = i then x else a.[j].
proof.
have ge0n := ge0_index[:n]; rewrite getE setE mkarrK.
- by rewrite size_mkseq; clear a; smt().
rewrite nth_mkseq_if /= !getE.
move: (size_ofarr a); move: (ofarr a) => s hs; clear a.
smt(nth_neg nth_default).
qed.

lemma get_set ['a] (a : 'a array<:n>) (x : 'a) (i j : int) :
  0 <= i < n => a.[i <- x].[j] = if j = i then x else a.[j].
proof. by move=> lt_in; rewrite get_set_if lt_in. qed.

lemma set_out ['a] (i : int) (x : 'a) (a : 'a array<:n>) :
  ! (0 <= i < n) => a.[i <- x] = a.
proof.
move=> Nlt_in; apply/eq_from_get=> j lt_jn.
by rewrite get_set_if Nlt_in.
qed.

lemma set_neg ['a] (i : int) (y : 'a) (a : 'a array<:n>) :
  i < 0 => a.[i <- y] = a.
proof. by move=> lt0_i; rewrite set_out // lezNgt lt0_i. qed.

lemma set_above ['a] (i : int) (y : 'a) (a : 'a array<:n>) :
  n <= i => a.[i <- y] = a.
proof. by move=> le_ni; rewrite set_out // ltzNge le_ni. qed.

lemma set_set_if ['a] (a : 'a array<:n>) (k k' : int) (x x' : 'a) :
      a.[k <- x].[k' <- x']
   =  if   k = k'
      then a.[k' <- x']
      else a.[k' <- x'].[k <- x].
proof.
apply/eq_from_get=> i lt_in; case: (0 <= k < n)=> [lt_kn|Nk]; last first.
- by rewrite !(set_out k) //; case: (k = k').
case: (0 <= k' < n)=> [lt_k'n|Nk']; last first.
- by rewrite !(set_out k') //; case: (k = k').
rewrite fun_if2 !get_set //.
case: (k = k')=> [->>|]; first by case: (i = k').
by case: (i = k')=> //; case: (i = k).
qed.

lemma set_set_eq ['a] (a : 'a array<:n>) (k : int) (x x' : 'a) :
  a.[k <- x].[k <- x'] = a.[k <- x'].
proof. by rewrite set_set_if. qed.

lemma set_set_swap ['a] (a : 'a array<:n>) (k k' : int) (x x' : 'a) :
  k <> k' => a.[k <- x].[k' <- x'] = a.[k' <- x'].[k <- x].
proof. by rewrite set_set_if=> ->. qed.

(* -------------------------------------------------------------------- *)
op offun ['a] (f : int -> 'a) : 'a array<:n> =
  mkarr (mkseq f n).

lemma offunifE ['a] (f : int -> 'a) i :
  (offun f).[i] = if 0 <= i < n then f i else witness.
proof.
have ge0n := ge0_index[:n]; rewrite getE /offun mkarrK; first by rewrite size_mkseq; smt().
by rewrite nth_mkseq_if.
qed.

lemma offunE ['a] (f : int -> 'a) i :
  0 <= i < n => (offun f).[i] = f i.
proof. by move=> lt_in; rewrite offunifE lt_in. qed.

(* -------------------------------------------------------------------- *)
op map ['a 'b] (f : 'a -> 'b) (a : 'a array<:n>) : 'b array<:n> =
  mkarr (List.map f (ofarr a)).

lemma mapE ['a 'b] (f : 'a -> 'b) (a : 'a array<:n>) i :
  0 <= i < n => (map f a).[i] = f a.[i].
proof.
move=> lt_in; rewrite getE /map mkarrK.
- by rewrite size_map size_ofarr.
by rewrite (nth_map witness) ?size_ofarr // -getE.
qed.

lemma map_comp ['a 'b 'c] (g : 'b -> 'c) (f : 'a -> 'b) (a : 'a array<:n>) :
  map (g \o f) a = map g (map f a).
proof. by rewrite /map map_comp mkarrK // size_map size_ofarr. qed.

end section IArray.
