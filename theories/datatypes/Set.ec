(* -------------------------------------------------------------------- *)
(* set.ec -- sets-as-predicates, with mathcomp-flavoured infix notation *)
(*                                                                      *)
(* A "set" here is just 'a -> bool. No new type, no membership lemmas   *)
(* to unfold through -- everything below is `abbrev`, so it's pure      *)
(* notation and disappears under `apply`/`smt`/pattern matching just    *)
(* like the raw predicate would.                                        *)
(* -------------------------------------------------------------------- *)

require import AllCore.

(* -------------------------------------------------------------------- *)
(* Core combinators                                                  *)
(* -------------------------------------------------------------------- *)


type 'a set = 'a -> bool.

abbrev setT : 'a set = fun _ => true.
abbrev set0 : 'a set = fun _ => false.
abbrev set1 (a : 'a) : 'a set = fun x => x = a.

op ( `||` ) (A B : 'a set) : 'a set = fun x => A x \/ B x.
op ( `&&` ) (A B : 'a set) : 'a set = fun x => A x /\ B x.
op ( `\\` ) (A B : 'a set) : 'a set = fun x => A x /\ !B x.
op ( `<=` ) (A B : 'a set) : bool      = forall x, A x => B x.
op ( `==` ) (A B : 'a set) : bool      = A `<=` B /\ B `<=` A.

op ( `$` ) (f : 'a -> 'b) (A : 'a set) : 'b set = fun y => exists x, A x /\ y = f x.

op ( `*` ) (A : 'a set) (B : 'b set) : ('a * 'b) set = fun (p : 'a * 'b) => A p.`1 /\ B p.`2.
op (`->`) (dom : 'a set) (post : 'a -> 'b set) : ('a -> 'b) -> bool =
  fun g => forall a, dom a => post a (g a).
  

op bigcup (A : 'a set) (S : 'a -> 'b set) : 'b set =
  fun y => exists a, A a /\ S a y.

op disjoint (A B : 'a set) : bool =
  forall x, !(A x /\ B x).

abbrev empty (A : 'a set) = forall a, ! (A a).
abbrev nonempty (A : 'a set) = exists a, (A a).

lemma empty_set0 (A : 'a set) : empty A <=> A = set0.
proof.
  split.    
  - by move => eA; apply fun_ext => a; rewrite eA.
  - by move => ->. 
qed.

lemma setUP (A B : 'a set) (x : 'a) : (A `||` B) x <=> (A x \/ B x).
proof. by []. qed.

lemma setIP (A B : 'a set) (x : 'a) : (A `&&` B) x <=> (A x /\ B x).
proof. by smt(). qed.
  
lemma setDP (A B : 'a set) (x : 'a) : (A `\\` B) x <=> (A x /\ !B x).
proof. by rewrite /(`\\`). qed.

lemma subsetP (A B : 'a set) : (A `<=` B) <=> (forall x, A x => B x).
proof. by rewrite /(`<=`). qed.

lemma eqsetP (A B : 'a set) : (A `==` B) <=> (A `<=` B /\ B `<=` A).
proof. by rewrite /(`==`). qed.


lemma imageP (f : 'a -> 'b) (A : 'a set) (y : 'b) :
  (f `$` A) y <=> exists x, A x /\ y = f x.
proof. by rewrite /(`$`). qed.

lemma bigcupP (A : 'a set) (S : 'a -> 'b set) (y : 'b) :
  bigcup A S y <=> exists a, A a /\ S a y.
proof. by rewrite /bigcup. qed.

lemma prodP (A : 'a set) (B : 'b set) (p : 'a * 'b) :
  (A `*` B) p <=> (A p.`1 /\ B p.`2).
proof. by rewrite /(`*`). qed.

lemma funsetP (dom : 'a set) (post : 'a -> 'b set) (g : 'a -> 'b) :
  (dom `->` post) g <=> forall a, dom a => post a (g a).
proof. by rewrite /(`->`). qed.


(* -------------------------------------------------------------------- *)
(* Subset: preorder                                                  *)
(* -------------------------------------------------------------------- *)

lemma subset_refl (A : 'a set) : A `<=` A.
proof. by []. qed.

lemma subset_trans (B A C : 'a set) :
  A `<=` B => B `<=` C => A `<=` C.
proof. by move=> hAB hBC x /hAB /hBC. qed.

lemma subset_asym (A B : 'a set) :
  A `<=` B => B `<=` A => (forall x, A x <=> B x).
proof. by move=> hAB hBA x; split=> [/hAB|/hBA]. qed.

(* -------------------------------------------------------------------- *)
(* Union / intersection: lattice laws                                *)
(* -------------------------------------------------------------------- *)

lemma setUC (A B : 'a set) : A `||` B = B `||` A.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma setUA (A B C : 'a set) : A `||` (B `||` C) = (A `||` B) `||` C.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma setU0 (A : 'a set) : A `||` set0 = A.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma setUid (A : 'a set) : A `||` A = A.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma subsetUl (A B : 'a set) : A `<=` A `||` B.
proof. by move=> x hAx; left. qed.

lemma subsetUr (A B : 'a set) : B `<=` A `||` B.
proof. by move=> x hBx; right. qed.

lemma setUsub (A B C : 'a set) :
  A `<=` C => B `<=` C => A `||` B `<=` C.
proof. by move=> hA hB x [/hA|/hB]. qed.

lemma setIC (A B : 'a set) : A `&&` B = B `&&` A.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma setIA (A B C : 'a set) : A `&&` (B `&&` C) = (A `&&` B) `&&` C.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma subsetIl (A B : 'a set) : A `&&` B `<=` A.
proof. by move=> x []. qed.

lemma subsetIr (A B : 'a set) : A `&&` B `<=` B.
proof. by move=> x [] _. qed.

(* -------------------------------------------------------------------- *)
(* Image                                                             *)
(* -------------------------------------------------------------------- *)

lemma image_id (A : 'a set) : (fun x => x) `$` A = A.
proof. by rewrite fun_ext => x /=; smt(). qed.

lemma image_comp (f : 'b -> 'c) (g : 'a -> 'b) (A : 'a set) :
  f `$` (g `$` A) = (fun x => f (g x)) `$` A.
proof. by rewrite fun_ext => y /=; smt(). qed.

lemma image_mono (f : 'a -> 'b) (A B : 'a set) :
  A `<=` B => f `$` A `<=` f `$` B.
proof. by move=> hAB y [x [/hAB hBx ->]]; exists x. qed.

lemma image_set0 (f : 'a -> 'b) : f `$` set0 = set0.
proof. by rewrite fun_ext => y /=; smt(). qed.

lemma image_eq_in (f g : 'a -> 'b) (A : 'a set) :
  (forall x, A x => f x = g x) => f `$` A = g `$` A.
proof. by move=> h; rewrite fun_ext => y /=; smt(). qed.

lemma image_const (c : 'b) (A : 'a set) :
  nonempty A => (fun _ => c) `$` A = set1 c.
proof.
  move=> [a0 hA0]; rewrite /(`$`) fun_ext => y /=; smt().
qed.

(* -------------------------------------------------------------------- *)
(* Bigcup                                                            *)
(* -------------------------------------------------------------------- *)

lemma bigcup_mono (A : 'a set) (S T : 'a -> 'b set) :
  (forall a, A a => S a `<=` T a) => bigcup A S `<=` bigcup A T.
proof. by move=> h y [a [hAa /(h a hAa) hTay]]; exists a. qed.

lemma bigcup_eq (A : 'a set) (S T : 'a -> 'b set) :
  (forall a, A a => S a = T a) => bigcup A S = bigcup A T.
proof.
  move=> h; apply fun_ext => b.
  apply eq_iff; split.
  - move => [a [* *]]; exists a. rewrite -h //=.
  - move => [a [* *]]; exists a. rewrite h //=.
qed.

lemma bigcup_set1 (a : 'a) (S : 'a -> 'b set) :
  bigcup (set1 a) S = S a.
proof. by rewrite fun_ext => y /=; smt(). qed.

lemma bigcup_const (A : 'a set) (B : 'b set) :
  (exists a, A a) => bigcup A (fun _ => B) = B.
proof. by move=> [a0 hA0]; rewrite fun_ext => y /=; smt(). qed.

lemma bigcup_image (A : 'a set) (S : 'a -> 'b set) (f : 'b -> 'c) :
  f `$` (bigcup A S) = bigcup A (fun a => f `$` S a).
proof. by rewrite fun_ext => z /=; smt(). qed.

lemma prod_eq_bigcup (A : 'a set) (B : 'b set) :
  A `*` B = bigcup B (fun b => (fun a => (a,b)) `$` A).
proof.
  rewrite fun_ext => -[a b] /=.
  apply eq_iff; split.
  - by move=> [hAa hBb]; exists b; split; [exact hBb | exists a].
  - by move=> [b' [hBb' [a' [hAa' [-> ->]]]]] //=.
qed.

