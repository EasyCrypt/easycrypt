require import AllCore List Distr.
import MRat.

(******************************************************************************)
(* Variant of FMap where get samples a random (valid) image                   *)
(******************************************************************************)

(* This theory develops a variant of [fmap] where update ("_.[_<-_]")
is cumulative and get ("_.[_]") is a distribution that uniformly
samles a result from among the stored key-value pairs. 

The type [('a, 'b) rmap] of random maps is implemented as [('a * 'b)
list. We define a [dom] operation using "\in" and "\notin" the same as
for [fmap]. Consequently, we have the following syntax (where 
[m : ('a, 'b) rmap], [x : 'a] and [y : 'b] [oy : option y]):

x \in m      : x has some binding in y          (domain operation)
oy \in m.[x] : oy is in the support of m.[x]    (support of distribution)
(x,y) \in m  : the pair (x,y) is a binding in m (list membership)
*)

type ('a,'b) rmap = ('a*'b) list.

op empty : ('a,'b) rmap = [].

op dom (m : ('a,'b) rmap) = (fun x => has (fun e => fst e = x) m).

(* range of possible results for lookup *)
op ran (m : ('a,'b) rmap) x = 
  unzip2 (filter (fun e => fst e = x) m).

lemma ranP (m : ('a,'b) rmap) x y : 
  y \in ran m x <=> (x,y) \in m.
proof. 
split => [|xy_m @/ran]; first by case/mapP => -[x' y']; rewrite mem_filter /#.
by rewrite (@map_f (fun p => snd p) _ (x,y)) mem_filter.
qed.

op "_.[_]" (m : ('a,'b) rmap) (x : 'a) : ('b option) distr = 
  let r = ran m x in
  if r = [] then dunit None else dmap (drat r) Some.

op "_.[_<-_]" (m : ('a,'b) rmap) (x : 'a) (y : 'b) : ('a,'b) rmap = 
  (x,y) :: m.

abbrev (\in)    ['a 'b] x (m : ('a, 'b) rmap) = (dom m x).
abbrev (\notin) ['a 'b] x (m : ('a, 'b) rmap) = ! (dom m x).

lemma domP (m : ('a,'b) rmap) x : 
  x \in m <=> exists y, (x,y) \in m.
proof. by rewrite /dom hasP /= /#. qed.

lemma domE (m : ('a, 'b) rmap, x : 'a) : 
  x \in m <=> ran m x <> [].
proof. 
split; last by case/nilP => y; rewrite ranP; smt(domP).
by case/domP => y xy_m; apply/nilP; exists y; apply/ranP.
qed.

lemma get_none (m : ('a, 'b) rmap, x : 'a) y :
  x \notin m => y \in m.[x] => is_none y.
proof. 
by rewrite domE negbK /("_.[_]") => -> /=; smt(supp_dunit).
qed.

lemma get_some (m : ('a, 'b) rmap, x : 'a) y :
  x \in m => y \in m.[x] => is_some y.
proof.
by rewrite domE /("_.[_]") /= => ?; rewrite ifF // supp_dmap.
qed.

lemma get_ll (m : ('a,'b) rmap) x : is_lossless (m.[x]).
proof. smt(dunit_ll dmap_ll drat_ll). qed.

lemma get1E_some (m : ('a,'b) rmap) x y : 
  mu1 m.[x] (Some y) = 
  if y \in ran m x then mu1 (drat (ran m x)) y else 0%r.
proof.
rewrite /("_.[_]") /=; case (y \in ran m x) => [y_m|yNm].
- by rewrite ifF 1:/# dmapE (mu_eq _ _ (pred1 y)).
case (ran m x = []) => rN0 ; first by rewrite dunitE.
rewrite dmapE (mu_eq _ _ (pred1 y)) //; smt(supp_drat mu_bounded).
qed.

lemma get1E_none (m : ('a,'b) rmap) x : 
  mu1 m.[x] None = b2r (x \notin m).
proof.
rewrite /("_.[_]") /= -if_neg -domE.
by case (x \in m) => [|]; rewrite ?dunitE // dmapE mu0_false.
qed.

lemma supp_get (m : ('a, 'b) rmap) (x : 'a) oy : 
  oy \in m.[x] <=> if is_some oy then oget oy \in ran m x else x \notin m.
proof.
case: oy => [|y] /= @/support; rewrite ?get1E_none ?get1E_some; 1:smt().
case (y \in ran m x) => //; smt(supp_drat mu_bounded).
qed.

lemma ran_set_same (m : ('a, 'b) rmap) x y : 
  ran m.[x<-y] x = y :: ran m x.
proof. done. qed.

lemma ran_set (m : ('a, 'b) rmap) x y x' :
  ran m.[x<-y] x' = if x = x' then y :: ran m x else ran m x'. 
proof. smt(). qed.

lemma ran_empty x : ran empty<:'a,'b> x = [] by done.

lemma supp_get_some (m : ('a, 'b) rmap) (x : 'a) y : 
  Some y \in m.[x] <=>  y \in ran m x.
proof. smt(supp_get). qed.

lemma supp_get_non (m : ('a, 'b) rmap) x : 
  None \in m.[x] <=> x \notin m.
proof. smt(supp_get). qed.

lemma mem_set (m : ('a, 'b) rmap) x y (z : 'a) :
  z \in m.[x <- y] <=> z \in m \/ (z = x).
proof. smt(). qed.


lemma mem_empty (x : 'a) : x \notin empty<:'a,'b> by done.

op filter ['a, 'b] (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) : ('a, 'b) rmap =
  List.filter (fun xy : 'a * 'b => p xy.`1 xy.`2) m.

lemma filter_set (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) (x : 'a) (b : 'b) : 
  filter p m.[x <- b] = 
  (if p x b then [(x,b)] else []) ++ filter p m.
proof. smt(). qed.

lemma mem_filter_pair (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) (x : 'a*'b) : 
  x \in filter p m <=> p x.`1 x.`2 /\ (x \in m).
proof. smt(List.mem_filter). qed.

lemma mem_filter (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) (x : 'a) : 
  x \in filter p m <=> exists y, p x y /\ (x,y) \in m.
proof. smt(List.mem_filter domP). qed.

(* smt seems unable to use this at all *)
lemma nosmt dom_mem_filter (p : 'a -> bool) (m : ('a, 'b) rmap) (x : 'a) : 
  x \in filter (fun x _ => p x) m <=> p x /\ x \in m.
proof. by rewrite mem_filter; smt(domP). qed.

lemma dom_filter (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) (x : 'a) : 
 x \in filter p m => x \in m.
proof. smt(mem_filter domP). qed.

(* if the filter acts only on the domain, it does not affect the
probabilities of the parts of the domain it preserves *)
(* TOTHINK: is there a reasonably simple statement for general predicates? *)
lemma dom_filterE (p : 'a -> bool) (m : ('a, 'b) rmap) (x : 'a) E : 
  p x => mu (filter (fun z _ => p z) m).[x] E = mu m.[x] E.
proof.
move => p_x; congr; rewrite /("_.[_]") /=; pose m' := filter _ _.
suff -> : ran m x = ran m' x by done.
by rewrite /ran /m' -filter_predI; congr; apply List.eq_in_filter => />.
qed.

lemma mem_supp_filter (p : 'a -> 'b -> bool) (m : ('a, 'b) rmap) (x : 'a) oy : 
  x \in filter p m =>
  oy \in (filter p m).[x] => oy \in m.[x].
proof. 
move => x_p_m; move/hasP : (x_p_m) => /= |> [? y] /=/>. 
rewrite mem_filter => /= -[p_x_y x_y_m]; case: oy => [|y']; 1: smt(get_some).
rewrite !supp_get_some /ran; apply/subseq_mem/map_subseq.
rewrite -filter_predI predIC filter_predI filter_subseq.
qed.
