(*
** We prove that the Merkle-Damgaard hash function
**
**  MD : {0,1}* -> {0,1}^n
**  MD(m) = f*(pad(m), IV) 
**
** based on a FIL random oracle (ideal compression function)
**
**  f : {0,1}^k x {0,1}^n -> {0,1}^n
**
** is indifferentiable from a VIL random oracle, provided
** pad is prefix-free
**
*)


cnst k : int. (* block length *)
cnst n : int. (* state length *)
cnst q : int. (* number of queries allowed *)

type block   = bitstring{k}.
type state   = bitstring{n}.
type msg     = bool list. (* {0,1}^* *)
type padding = block list.
type fmap    = (block * state, state) map.
type chain   = (block * state) list.

cnst IV : state.

pred injective(T:('a, 'b) map) = 
  forall (x,y:'a), in_dom(x,T) => in_dom(y,T) => T[x] = T [y] => x = y.

pred injective_fst(I:('a, 'b * 'c) map) = 
  forall (x,y:'a), in_dom(x,I) => in_dom(y,I) => fst(I[x]) = fst(I[y]) => x = y.

pred inclusion(T', T:('a, 'b) map) = 
  (forall (x:'a), in_dom(x,T') => in_dom(x,T)) &&
  (forall (x:'a), in_dom(x,T') => T'[x] = T[x]).

pred inverse(T:('a,'b) map, T': ('b, 'a) map) =
  (forall (x:'a), in_dom(x,T) => in_dom(T[x],T') && T'[T[x]] = x) &&
  (forall (y:'b), in_dom(y,T') => in_dom(T'[y],T) && T[T'[y]] = y).

pred ext_eq (T1, T2:('a,'b) map) =
  (forall (a:'a), in_dom(a,T1) <=> in_dom(a,T2)) &&
  (forall (a:'a), in_dom(a,T1) => T1[a] = T2[a]).


(** Operators *)

(** p, q *)

axiom q_pos : 0 < q.

axiom n_pos : 0 < n.


(** pad and unpad *)

op pad   : msg -> padding.
op unpad : padding -> msg option.

axiom unpad_pad : forall (m:msg), unpad(pad(m)) = Some(m).

axiom unpad_nil : unpad([]) = None.

axiom unpad_ex_pad : 
  forall (p:padding), unpad(p) <> None => exists (m:msg), p = pad(m).

axiom unpad_inj : forall (x,y:padding), 
  unpad(x) = unpad(y) => unpad(x) <> None => x = y.

axiom prefixfree:
  forall (m1,m2:msg, bl:block list), m1 <> m2 => pad(m1) <> pad(m2) ++ bl.


(** mapfst *)

op mapfst : chain -> padding.

axiom mapfst_nil : mapfst([]) = [].

axiom mapfst_cons : 
  forall (x:block, y:state, c:chain), mapfst((x,y) :: c) = x :: mapfst(c).


(** ischained *)

op ischained : (fmap, state, chain, state) -> bool.

axiom ischained_nil : 
  forall (T:fmap, y,z:state), ischained(T, y, [], z) <=> y = z.

axiom ischained_cons : 
  forall (T:fmap, y:state, xy:block*state, z:state),
    ischained(T, y, xy::[], z) <=> in_dom(xy, T) && y = snd(xy) && T[xy] = z.

axiom ischained_conscons : 
  forall (T:fmap, xy:block*state, y:state, xy':block*state, c:chain, z:state),
    ischained(T, y, xy :: (xy'::c), z) <=>
    (in_dom(xy, T) && y = snd(xy) && T[xy] = snd(xy') && 
     ischained(T, snd(xy'), xy'::c, z)).


(** findseq *)

op findseq : (block, state, fmap) -> chain option.

(* soundness *)
axiom findseq_ischained : 
  forall (T:fmap, x:block, y:state),
    findseq(x,y,T) <> None => ischained(T,IV, proj(findseq(x,y,T)),y).

axiom findseq_unpad : 
  forall (T:fmap, x:block, y:state),
   findseq(x,y,T) <> None =>
   unpad(mapfst(proj(findseq(x,y,T)) ++ ((x,y)::[]))) <> None.

(* completeness *)
axiom findseq_complete : 
  forall (T:fmap, x:block, y:state, c:chain),
   injective(T) =>
   !in_rng(IV,T) =>
   ischained(T,IV,c,y) =>
   unpad(mapfst(c ++ ((x,y)::[]))) <> None =>
   findseq(x,y,T) <> None.


(** valid_chain *)

pred valid_chain (c:chain, T:fmap) = 
  exists (z:state), ischained(T, IV, c, z) && unpad(mapfst(c)) <> None.


(** Misc *)
op set_bad3 : (state, fmap, fmap, (state, block*state) map) -> bool.

axiom set_bad3_def : 
  forall (z:state, T',T:fmap, invT:(state, block * state) map),
    set_bad3(z, T', T, invT) <=>
    (in_dom(z, invT) && !in_dom(invT[z], T') &&
    forall (c:chain), !valid_chain(c ++ [invT[z]], T)).

pred claim5(T',T:fmap) =
  forall (x':block, y':state, x:block, y:state), 
    in_dom((x',y'), T) &&
    in_dom((x, y ), T') && 
    T[(x',y')] = y && 
    findseq(x',y',T) = None => in_dom((x',y'), T').

pred ROmapinT(ROmap:(msg,state * int) map, T:fmap) =
  (forall (m:msg), 
    in_dom(m,ROmap) =>
      exists (x:block,y:state), 
        findseq(x,y,T) <> None &&
        m = proj(unpad(mapfst(proj(findseq(x,y,T)) ++ [(x,y)]))) &&
        in_dom((x,y), T))  &&
  (forall (x:block,y:state), 
    findseq(x,y,T) <> None =>
    in_dom(proj(unpad(mapfst(proj(findseq(x,y,T)) ++ [(x,y)]))),ROmap) => 
    in_dom((x,y),T)) &&
  (forall (x:block,y:state), 
    findseq(x,y,T) <> None =>
    in_dom((x,y),T) => 
    in_dom(proj(unpad(mapfst(proj(findseq(x,y,T)) ++ [(x,y)]))), ROmap) &&
    fst(ROmap[proj(unpad(mapfst(proj(findseq(x,y,T)) ++ [(x,y)])))]) = T[(x,y)]).

axiom eq_ext_eq : forall (T1,T2:('a,'b) map), ext_eq(T1, T2) <=> T1 = T2.


(*
** Lemmas
**
** The following lemmas follow from the definitions above and
** are either derived automatically or are proven in Coq.
*)

(* Can be proven with eprover *)
axiom hd_tl:
  forall (l:'a list), l <> [] => hd(l) :: tl(l) = l.

lemma tl_length :  
  forall (l:'a list), l <> [] => length(tl(l)) = length(l) - 1.

lemma length0 : 
  forall (l:'a list), length(l) = 0 => l = [].

lemma length_tl_notnil:
 forall (l:'a list), l <> [] && tl(l) <> [] <=> length(l) > 1.

lemma hd_length_one:
 forall (l:'a list), l <> [] && length(l) <= 1 => l = [hd(l)].

lemma append_same_nil:
 forall (l1,l2:'a list), l1 ++ l2 = l1 => l2 = [].

lemma app_nil_end: forall (l:'a list), l ++ [] = l.

lemma app_cons_nil : forall (a:'a,l:'a list), [a] ++ l = a :: l.

(* Proven in coqproofs.v *)
axiom exists_last:
  forall (l:'a list),
    l = [] || exists (x:'a, l':'a list), l = l' ++ [x].

(* Proven in coqproofs.v *)
axiom app_inj_tl: 
  forall (l1,l2:'a list, x1,x2:'a),
    l1 ++ [x1] = l2 ++ [x2] => l1 = l2 && x1 = x2.

(* requires Eprover, also proven in coq: coqproofs.v *)
lemma cons_app_swap: forall (x:'a, l:'a list),
  exists (x':'a, l':'a list), x :: l = l' ++ [x'].

lemma append_cons: 
  forall (x:'a, xs:'a list, l:'a list ),
    ((x::xs) ++ l) = (x::(xs++l)).
unset append_cons.

lemma append_nil: 
  forall (l:'a list ),
    ([] ++ l) = l.
unset append_nil.

lemma last_in:
 forall (l:'a list, x:'a), mem(x, l ++ [x]).

lemma in_split:
  forall (l:'a list, x:'a),
    mem(x, l) => exists (l1,l2:'a list), l = l1 ++ [x] ++ l2.


(** Finite maps *)

lemma in_dom_upd_map : 
  forall (m:('a,'b) map, a, a':'a, b:'b),
    in_dom(a',m[a <- b]) <=> (a = a' || in_dom(a',m)).

lemma in_dom_upd_map_excl : 
  forall (m:('a,'b) map, a, a':'a, b:'b),
    in_dom(a',m[a <- b]) <=> (a = a' || (a<>a' && in_dom(a',m))).

lemma get_upd_overwrite:
  forall (a,a':'a, I:('a, 'b * bool) map, b:'b),
  in_dom(a, I[a' <- (b,false)]) && snd(I[a' <- (b,false)][a]) => 
  in_dom(a, I) && I[a' <- (b,false)][a] = I[a].

lemma inclusion_injective:
  forall (T,T':('a,'b) map), inclusion(T',T) && injective (T) => injective(T').

lemma inclusion_upd:
  forall (T,T':('a,'b) map, a:'a),
    inclusion(T', T) => in_dom(a, T) => inclusion(T', T'[a <- T[a]]).

lemma inclusion_upd':
  forall (T,T':('a,'b) map, a:'a),
    inclusion(T', T) => in_dom(a, T) => inclusion(T'[a <- T[a]], T).

lemma inclusion_upd'':
  forall (T,T': ('a,'b) map, a:'a, b:'b),
    inclusion(T', T) => inclusion(T'[a <- b], T[a <- b]).

lemma inclusion_not_rng:
  forall (T,T':('a,'b) map, b:'b),
    inclusion(T', T) => !in_rng(b, T) => !in_rng(b, T').

lemma not_rng_upd:
  forall (T:('a,'b) map, a:'a, b,b':'b),
   !in_rng(b', T) => b <> b' => !in_rng(b', T[a <- b]).

lemma injective_upd: 
  forall (T:('a, 'b) map, a:'a, b:'b),
    !in_rng(b, T) => injective(T) => injective(T[a <- b]).

lemma inverse_dom_rng:
  forall (T:('a,'b) map, invT:('b,'a) map, b:'b),
    inverse(T, invT) => in_dom(b, invT) => in_rng(b, T).

lemma inverse_rng_dom:
  forall (T:('a,'b) map, invT:('b,'a) map, b:'b),
    inverse(T, invT) => in_rng(b, T) => in_dom(b, invT).


(** Padding *)

lemma padnil: forall (m:msg), pad(m) <> [].

lemma prefixfree':
  forall (p1,p2:padding), 
    unpad(p1 ++ p2) <> None => p2 <> [] => unpad(p1) = None.

(* requires z3, also proven in old version: proofs.v *)

lemma unpad_hd:
  forall (ms:padding),
    ms <> [] && tl(ms) <> [] && unpad(ms) <> None => 
    unpad(mapfst([]) ++ [hd(ms)]) = None.

(* Proven in Coq: coqproofs.v *)
axiom unpad_tl_prefix:
  forall (ms,c:padding),
    2 < length(ms) => 
    unpad(c ++ ms) <> None => 
    unpad(c ++ [hd(ms)] ++ [hd(tl(ms))]) = None.


(** mapfst *)

(* Proven in Coq: coqproofs.v *)
axiom mapfst_app: 
  forall (c1,c2:chain), mapfst(c1 ++ c2) = mapfst(c1) ++ mapfst(c2).


(** ischained *)

unset all.
set ischained_nil, ischained_cons, ischained_conscons.

lemma ischained_lasteq : 
  forall (T:fmap, xy:block * state, y:state, c:chain, z:state),
    ischained(T, y, xy :: c, z) => y = snd(xy).

(* Proven in Coq: coqproofs.v *)
axiom ischained_app : 
  forall (T:fmap, Y:state, xy:block * state, S:state, c1,c2:chain),
   ischained(T, Y, c1, snd(xy)) && in_dom(xy,T) && ischained(T, T[xy], c2, S) <=>
   ischained(T, Y, c1 ++ (xy::c2), S).

(* Proven in Coq: coqproofs.v *)
axiom ischained_same_length :
  forall (T:fmap, Y1,Y2:state, c1,c2:chain, z:state),
    length(c1) = length(c2) =>
    injective(T) =>
    ischained(T, Y1, c1, z) =>
    ischained(T, Y2, c2, z) =>
    c1 = c2.

(* Proven in Coq: coqproofs.v *)
axiom ischained_diff_length:
 forall (T:fmap, Y1,Y2:state, c1,c2:chain, z:state),
  length(c2) < length(c1) =>
  injective(T) =>
  ischained(T, Y1, c1, z) =>
  ischained(T, Y2, c2, z) =>
  exists (xy:block * state, pre:(block * state) list), c1 = pre ++ xy::c2.

(* Proven in Coq: coqproofs.v *)
axiom ischained_diff_length_absurd: 
  forall (T:fmap, Y1,Y2:state, c1,c2:chain, z:state),
    length(c2) < length(c1) =>
    !in_rng(Y2,T) =>
    injective(T) =>
    ischained(T, Y1, c1, z) =>
    ischained(T, Y2, c2, z) =>
    false.

lemma ischained_inj : 
  forall (T:fmap, Y:state, c1,c2:chain, z:state),
    !in_rng(Y,T) =>
    injective(T) =>
    ischained(T, Y, c1, z) =>
    ischained(T, Y, c2, z) =>
    c1 = c2.

(* also proven in old version: proofs.v *)
lemma ischained_in_dom: 
  forall (T:fmap, c:chain, xy:block*state, z:state),
    mem(xy,c) => ischained(T,IV,c,z) => in_dom(xy,T).
 
(* Proven in Coq: coqproofs.v *)
axiom ischained_upd: 
  forall (T:fmap, c:chain, xy:block*state, z,z':state),
    !mem(xy,c) => ischained(T,IV,c,z) => ischained(T[xy <- z'],IV,c,z).

(* also proven in old version: proofs.v *)
lemma ischained_upd' : forall (T:fmap,c:chain, xy:block*state, z,z':state),
  !in_dom(xy,T) =>
  ischained(T,IV,c,z) =>
  ischained(T[xy <- z'],IV,c,z).

(* Proven in Coq: coqproofs.v *)
axiom ischained_mapfst_eq : 
  forall (T:fmap, c1,c2:chain, z1,z2:state),
   ischained(T,IV,c1,z1) =>
   ischained(T,IV,c2,z2) =>
   mapfst(c1) = mapfst(c2) =>
   c1 = c2 && z1 = z2.

(* Proven in Coq: coqproofs.v *)
axiom ischained_inclusion:
  forall (T',T:fmap, Y:state, c:chain, z:state),
   inclusion(T',T) => ischained(T',Y,c,z) => ischained(T,Y,c,z).

(* Proven in Coq: coqproofs.v *)
axiom ischained_helpful_upd:
  forall (T:fmap, c:chain, x:block, y,y',z:state),
    !ischained(T, IV, c, y') =>
    ischained(upd(T,(x,y),z), IV, c, y') => mem((x,y), c).

(* Proven in Coq: coqproofs.v *)
axiom ischained_last_cases:
  forall (T:fmap,c:chain,z:state),
    ischained(T,IV,c,z) => 
    z = IV || (exists (x:block,y:state), in_dom((x,y), T) && T[(x,y)] = z).

(* 
** This claim follows from prefix-freeness and the uniqueness of 
** chains in well-formed tables
*)

(* Proven in Coq: coqproofs.v *)
axiom claim4 : 
  forall (T:fmap),
    !in_rng(IV,T) =>
    injective(T) =>
    forall (c1,c2:chain, xy,xy':block * state),
      ischained(T, IV, c1, snd(xy)) =>
      unpad(mapfst(c1 ++ [xy])) <> None =>
      ischained(T, IV, c2, snd(xy')) =>
      unpad(mapfst(c2 ++ [xy'])) <> None => !mem(xy, c2).


(** findseq *)

(* Consequence of completeness and uniqueness of chains *)
timeout 20.
set all.

lemma findseq_complete_unique: 
  forall (T:fmap, x:block, y:state, c:chain),
    injective(T) =>
    !in_rng(IV,T) =>
    ischained(T,IV,c,y) =>
    unpad(mapfst(c ++ [(x,y)])) <> None =>
    findseq(x,y,T) <> None && findseq(x,y,T) = Some(c).

lemma findseq_complete_valid_chain:
  forall (T:fmap, x:block, y:state, c:chain),
    injective(T) => 
    !in_rng(IV,T) =>
    valid_chain(c ++ [(x,y)],T) => findseq(x,y,T) <> None.

unset all.
set findseq_complete_unique, findseq_complete_valid_chain, ischained_app.

lemma findseq_complete_unique_valid_chain:
  forall (T:fmap, x:block, y:state, c:chain),
    injective(T) => 
    !in_rng(IV,T) =>
    valid_chain(c ++ [(x,y)], T) => 
    findseq(x,y,T) <> None && proj(findseq(x,y,T)) = c.
(* better to have it this way to ease the proof of valid_chain_upd_nohelp! *)

set all.
timeout 5.

lemma findseq_ischained_unpad:
  forall (T:fmap, x:block, y:state, c:chain),
    injective(T) => 
    !in_rng(IV,T) =>
    ischained(T,IV,c,y) =>
    unpad(mapfst(c) ++ [x]) = None => 
    findseq(x,y,T) = None.

lemma findseq_mapfst_eq:
  forall (T:fmap, x1:block, y1:state, x2:block, y2:state),
    findseq(x1,y1,T) <> None =>
    findseq(x2,y2,T) <> None =>
    proj(unpad(mapfst(proj(findseq(x2,y2,T)) ++ [(x2,y2)]))) =
    proj(unpad(mapfst(proj(findseq(x1,y1,T)) ++ [(x1,y1)]))) =>
    (x1,y1) = (x2,y2).

(* Proven in Coq: coqproofs.v *)
axiom findseq_inclusion_eq:
  forall (T',T:fmap, x:block, y:state),
    inclusion(T',T) &&
    injective(T) &&
    !in_rng(IV,T) &&
    !findseq(x,y,T') = None =>
    findseq(x,y,T) = findseq(x,y,T').

lemma findseq_inclusion_upd_eq : 
   forall (T,T':fmap, x:block, y:state, x':block, y',z':state),
     inclusion(T',T) =>
     injective(T) =>
     !in_rng(IV,T) =>
     z' <> IV =>
     !in_rng(z',T) =>
     !in_dom((x',y'),T) =>
     findseq(x,y,T') <> None =>
     findseq(x,y,T[(x',y') <- z']) = findseq(x,y,T').

lemma findseq_last_in_dom_ischained :
  forall (T,T':fmap, x:block, y:state),
    inclusion(T',T) =>
    findseq (x,y,T') <> None =>
    in_dom((x, y),T) =>
    ischained(T,IV, proj(findseq (x,y,T')) ++ [(x, y)], T[(x,y)]).

(* Proven in Coq: coqproofs.v *)
axiom findseq_last_in_dom_valid :
  forall (T:fmap,T':fmap,x:block,y:state),
    inclusion(T',T) =>
    findseq (x,y,T') <> None =>
    in_dom((x, y),T) =>
    valid_chain(proj(findseq(x,y,T')) ++ [(x, y)], T).

(* Follows from findseq_inclusion *)
lemma findseq_upd:
  forall (T',T:fmap, xy:block * state, x':block, y':state),
    inclusion(T',T) &&
    injective(T) &&
    !in_rng(IV,T) &&
    in_dom(xy,T) &&
    findseq(x',y',T') <> None => 
    findseq(x',y',upd(T',xy,T[xy])) <> None.

(* 
** NOTE: the following lemma is an immediate consequence of
** findseq_inclusion_upd_eq and the reflexivity of inclusion; i.e., it
** is just a special case, written a little differently.
** unfortunately, it cannot be proved automatically, because the
** solvers seem to have trouble matching a variable xy:block*state to
** a pair of two variables x:block and y:state see lemma
** findseq_upd'_tmp below 
*)

(* also proven in old version: proofs.v *)
lemma findseq_upd':
  forall (T:fmap, xy:block*state, x':block, y',z:state),
    injective(T) =>
    !in_rng(IV,T) =>
    !in_dom(xy,T) =>
    !in_rng(z,T) =>
    z <> IV &&
    findseq(x',y',T[xy <- z]) = None => 
    findseq(x',y',T) = None.

(* Proven in Coq: coqproofs.v
** the proof involves a case analysis on the list returned by findseq,
** which can have either the form [] or al@a::[] (exists_last)
** given lemma exists_last, z3 manages to do it
*)
axiom findseq_pred_in_T':
  forall (T',T:fmap, x':block, y':state, x:block, y:state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    in_dom((x',y'),T) =>
    T[(x',y')] = y =>
    findseq(x,y,T') <> None =>
    in_dom((x',y'),T').
 
(* also proven in old version: proofs.v *)
lemma findseq_helpful_upd:
  forall (T:fmap, x,x':block, y,y',z:state),
    injective(T) =>
    !in_rng(IV,T) =>
    findseq(x',y',T) = None =>
    findseq(x',y',upd(T,(x,y),z)) <> None => 
    mem((x,y), proj(findseq(x',y',T[(x,y) <- z]))).

(* Proven in Coq: coqproofs.v *)
axiom findseq_useless_upd:
  forall (T,T':fmap, x,x':block, y,y':state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    findseq(x, y, T') <> None =>
    (* NOTE:added this premise; otherwise the conclusion makes no sense *)
    in_dom((x,y),T) =>
    findseq(x',y',T'[(x,y) <- T[(x,y)]]) = findseq(x',y',T').

(*
** * in case (x,y) != (x',y'), this follows from findseq_useless_upd
** * in case (x,y) = (x',y'), this is quite trivial and follows
**   from either findseq_inclusion_upd_eq or also findseq_useless_upd.
** TODO understand the following:
** Although it is clear that this lemma is quite close to
** the lemma findseq_useless_upd, and the proof would be very similar,
** the latter speaks about an update with the value T[xy] where xy is
** already in dom(T), thereby guaranteeing
** that upd(T',(x,y),T[(x,y)]) is still well-formed.
** Here however, xy is _NOT_ in dom(T) and we instead guarantee that
** upd(T',(x,y),z) is still well-formed by imposing sensible conditions on z;
** so it is surprising the SMT solvers manage to derive this!
*)
lemma findseq_useless_upd':
  forall (T,T':fmap, x,x':block, y,y',z:state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    z <> IV =>
    !in_rng(z,T) =>
    !in_dom((x,y),T) =>
    (* small but significant difference to findseq_inclusion_upd_eq: 
    ** here the latter says find_seq(x', y', T') <> None
    *)
    findseq(x, y, T') <> None =>
    findseq(x',y', T'[(x,y) <- z]) = findseq(x',y',T').

(* Proven in Coq: coqproofs.v *)
axiom findseq_upd_nohelp:
  forall (T:fmap, x,x':block, y,y',z:state),
    injective(T) =>
    !in_rng(IV,T) =>
    !in_dom((x,y),T) =>
    z <> IV =>
    !in_rng(z,T) =>
    z <> y =>
    (!exists(x0:block), in_dom((x0,z),T)) =>
    in_dom((x',y'), T[(x,y) <- z]) =>
    findseq(x',y', T[(x,y) <- z]) = findseq(x',y',T).


(** valid_chain *)

(* Proven in Coq: coqproofs.v *)
axiom valid_chain_upd:
  forall (T:fmap, xy:block*state, z:state, c:chain),
    !in_dom(xy,T) => valid_chain(c,T) => valid_chain(c,T[xy <- z]).

(* also proven in old version: proofs.v *)
lemma valid_chain_empty:
  forall(c:chain, xy:block*state), !valid_chain(c ++ [xy], empty_map).

(* Proven in Coq: coqproofs.v *)
axiom valid_chain_upd_nohelp:
  forall (T:fmap, x:block, y,z:state, xy':block * state, c:chain),
    injective(T) =>
    !in_rng(IV,T) =>
    !in_dom((x,y),T) =>
    z <> IV =>
    !in_rng(z,T) =>
    z <> y =>
    (!exists(x0:block), in_dom((x0,z),T)) =>
    in_dom(xy', T[(x,y) <- z]) =>
    findseq(x,y,T) = None => 
    valid_chain(c ++ [xy'], T[(x,y) <- z]) <=> valid_chain(c ++ [xy'], T).

(* Proven in Coq: coqproofs.v *)
axiom valid_chain_upd_nohelp':
  forall (T:fmap, x:block, y,z:state, xy':block * state, c:chain),
    injective(T) =>
    !in_rng(IV,T) =>
    !in_dom((x,y),T) =>
    z <> IV =>
    !in_rng(z,T) =>
    z <> y =>
    (!exists(x0:block), in_dom((x0,z),T)) =>
    in_dom(xy',T) => 
    valid_chain(c ++ [xy'], T[(x,y) <- z]) <=> valid_chain(c ++ [xy'], T).


(** set_bad3 *)

(* To ease proofs in Coq *)
lemma set_bad3_eq :
  forall (z:state, T1,T1',T2,T2':fmap, invT1,invT2:(state, block * state) map),
   (set_bad3(z,T1',T1,invT1) = true <=> set_bad3(z,T2',T2,invT2) = true) => 
   set_bad3(z,T1',T1,invT1) = set_bad3(z,T2',T2,invT2).

(* Proven in Coq: coqproofs.v *)
axiom set_bad3_upd:
  forall (T,T':fmap, invT:(state,block * state) map, x:block,y,y0,z:state),
    inclusion(T',T) =>
    injective(T) =>
    inverse(T,invT) =>
    !in_rng(IV,T) =>
    !in_dom((x,y),T) =>
    !in_rng(z,T) =>
    z <> IV =>
    findseq(x,y,T') <> None =>
    set_bad3(y0, T'[(x,y) <- z], T[(x,y) <- z], invT[z <- (x,y)]) =
    set_bad3(y0, T', T, invT).

(* Proven in Coq: coqproofs.v *)
axiom set_bad3_upd':
  forall (T,T':fmap, invT:(state,block * state) map, x:block, y,y0,z:state),
    inclusion(T',T) =>
    injective(T) =>
    inverse(T,invT) => 
    !in_rng(IV,T) => 
    !in_dom((x,y), T) =>
    !in_rng(z,T) => 
    z <> IV =>
    z <> y =>
    (!exists(x0:block), in_dom((x0,z),T)) =>
    set_bad3(y0,T'[(x,y) <- z], T[(x,y) <- z], invT[z <- (x,y)]) = 
    set_bad3(y0,T',T,invT).

(* Proven in Coq: coqproofs.v *)
axiom set_bad3_upd_I:
  forall (T,T':fmap, invT:(state,block * state) map,
          x:block, y,z:state, I:(int, state * bool) map, i,icount:int),
    injective(T) =>
    !in_rng(IV,T) =>
    z <> IV =>
    !in_rng(z,T) =>
    (forall(i:int), in_dom(i,I) => !z = fst(I[i])) &&
    (forall(i:int), in_dom(i,I) => (set_bad3(fst(I[i]),T',T,invT) <=> snd(I[i]))) &&
    !in_dom((x,y), T) =>
    in_dom(i, I[icount <- (z,false)]) =>
    findseq(x,y,T) <> None =>
 set_bad3(fst(I[icount <- (z,false)][i]), T', T[(x,y) <- z], invT[z <- (x,y)]) => 
 snd(I[icount <- (z,false)][i]).


(** claim5 *)

(* Proven in Coq: coqproofs.v *)
axiom ischained_last_in_dom_claim5:
  forall (T:fmap, T':fmap, c:chain, xy:block*state, xy':block*state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    ischained(T,IV,c ++ [xy'], snd(xy)) =>
    unpad(mapfst(c ++ xy'::[xy])) <> None =>
    in_dom(xy',T') =>
    claim5(T', T) => 
    ischained(T',IV,c ++ [xy'], snd(xy)).

(* Proven in Coq: coqproofs.v *)
axiom findseq_set_bad3_claim5:
  forall (T,T':fmap, invT:(state,block * state) map, x:block, y:state),
    inclusion(T',T) =>
    inverse(T,invT) =>
    injective(T) =>
    !in_rng(IV,T) =>
    !set_bad3(y,T',T,invT) =>
    claim5(T', T) =>
    findseq(x,y,T) <> None => 
    findseq(x,y,T') <> None.

(* also proven in Coq: coqproofs.v *)
axiom claim5_upd:
  forall (T,T':fmap, invT:(state,block * state) map, x:block,y:state),
    injective(T) =>
    !in_rng(IV,T) =>
    inverse(T,invT) =>
    in_dom((x,y),T) =>
    !set_bad3(y,T',T,invT) =>
    claim5(T',T) => 
    claim5(upd(T',(x,y),T[(x,y)]), T).

(* Proven in Coq: coqproofs.v *)
axiom claim5_upd':
  forall (T':fmap, T:fmap, invT:(state,(block*state)) map, x:block, y,z:state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    inverse(T,invT) =>
    !in_dom((x,y), T) =>
    z <> IV =>
    !in_rng(z,T) => 
    !set_bad3(y,T',T,invT) =>
    claim5(T',T) => 
    claim5(T'[(x,y) <- z], T[(x,y) <- z]).

(* Proven in Coq: coqproofs.v *)
axiom findseq_claim5_aux:
  forall (T':fmap, T:fmap, x:block,y:state,z:state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    !in_rng(z,T) =>
    z <> IV =>
    claim5(T'[(x,y) <- z], T[(x,y) <- z]) =>
    findseq(x,y,T') = None => 
    findseq(x,y,T[(x,y) <- z]) = None.

(* Proven in Coq: coqproofs.v *)
axiom findseq_claim5:
  forall (T,T':fmap, invT:(state, block * state) map, x:block, y,z:state),
    inclusion(T',T) =>
    injective(T) =>
    !in_rng(IV,T) =>
    inverse(T,invT) =>
    !in_dom((x,y), T) =>
    !in_rng(z,T) =>
    z <> IV =>
    !set_bad3(y,T',T,invT) =>
    claim5(T',T) => (* implies claim5(T'[(x,y) <- z], T[(x,y) <- z]) *)
    findseq(x,y,T') = None => 
    findseq(x,y,T[(x,y) <- z]) = None.


(** ROmapinT *)

(* Proven in Coq: coqproofs.v *)
axiom ROmapinT_upd:
  forall (T:fmap, ROmap:(msg,state * int) map, x:block, y,z:state, i:int),
    injective(T) =>
    !in_rng(IV,T) => 
    !in_dom((x,y), T) =>
    z <> IV =>
    !in_rng(z,T) =>
    ROmapinT(ROmap,T) =>
    findseq(x,y,T) <> None =>
    !in_dom(proj(unpad(mapfst((proj(findseq(x,y,T))) ++ [(x,y)]))), ROmap) => 
    ROmapinT(upd(ROmap,proj(unpad(mapfst((proj(findseq(x,y,T))) ++ [(x,y)]))), 
      (z,i)), T[(x,y) <- z]).

(** Proven in coqproofs.v *)
axiom ROmapinT_upd2 : 
  forall (T,T':fmap, invT:(state, block * state) map, x:block, y,z:state, 
    ROmap:(msg,state * int) map), 
  inclusion(T',T) &&
  injective(T) &&
  !in_rng(IV,T) &&
  inverse(T,invT) &&
  !in_dom((x,y), T) &&
  !in_rng(z,T) && 
  z <> y &&
  z <> IV &&
  (forall (x0:block), !in_dom((x0,z),T)) &&
  !set_bad3(y,T',T,invT) &&
  claim5(T',T) &&
  findseq(x,y,T') = None &&
  ROmapinT(ROmap,T) => 
  ROmapinT(ROmap,T[(x,y) <- z]).
  
(** Proven in coqproofs.v *)
axiom ROmapinT_upd3: 
forall (ROmap:(msg,state * int) map, m:block, h:state, T:fmap),
injective(T) =>
!in_rng (IV,T) =>
!in_dom ((m,h),T) =>
findseq (m,h,T) = None =>
forall (z:state), z<>IV => !in_rng(z,T) => z<>h => (!exists(x0:block), in_dom((x0,z),T)) =>
ROmapinT(ROmap,T) =>
ROmapinT(ROmap,T[(m, h) <- z]).

(** Misc *)

(** Proven in coqproofs.v *)
axiom help : forall (i:int, I:(int, state * bool) map, S:state list, z1,z2:state),
 !in_dom (i,I) && 
 (forall (z:state), mem(z,S) => exists (i:int), in_dom(i,I) && fst(I[i]) = z) =>
 mem(z1, z2::S) =>
 exists (i':int), 
   in_dom(i',I[i <- (z2,false)]) && fst(I[i <- (z2, false)][i']) = z1.

(** Proven in coqproofs.v *)
axiom help1 : forall (I:(int, state * bool) map, S:state list, j:int),
 (forall (z:state), mem(z,S) => exists (i:int), in_dom(i,I) && fst(I[i]) = z) =>
 forall (z:state),
   let I' = I[j <- (fst(I[j]), false)] in
   mem(z,S) => exists (i:int), in_dom(i,I') && fst(I'[i]) = z.

(** Proven in coqproofs.v *)
axiom help1' : forall (I:(int, state * bool) map, S:state list, z_0:state, i':int),
 (forall (z:state), mem(z,S) => exists (i:int), in_dom(i,I) && fst(I[i]) = z) =>
(* !mem (z_0,S) => *)
 !in_dom (i',I) =>
 forall (z:state), 
   let I' = I[i' <- (z_0, true)] in
   mem(z,z_0::S) => exists (i:int), in_dom(i,I') && fst(I'[i]) = z.

(** Proven in coqproofs.v *)
axiom help4 : forall (ch:(bitstring{k} * bitstring{n}) list, 
 ms:bitstring{k} list, m:bool list, hash:bitstring{n},T:fmap),
 mapfst(ch) ++ ms = pad(m) =>
 ms <> [] =>
 1 < length(tl(ms)) =>
 unpad(mapfst(ch ++ [(hd(ms),hash)]) ++ [hd(tl(ms))]) = None.

(** Proven in coqproofs.v *)
axiom help5 : forall (ch:(bitstring{k} * bitstring{n}) list, 
 ms:bitstring{k} list, m:bool list, hash:bitstring{n},T:fmap),
 mapfst(ch) ++ ms = pad(m) =>
 unpad(mapfst(ch ++ [(hd(ms),hash)])) = None =>
 ischained(T,IV,ch,hash) =>
 injective(T) =>
 !in_rng(IV, T) =>
 ms <> [] =>
 in_dom((hd(ms), hash), T) =>
 1 < length(tl(ms)) =>
 findseq(hd(tl(ms)),T[(hd(ms),hash)],T) = None.

(* almost the same as above -> remove one of them *)
lemma help5' : forall (ch:(bitstring{k} * bitstring{n}) list, 
 ms:bitstring{k} list, m:bool list, hash:bitstring{n},T:fmap),
 mapfst(ch) ++ ms = pad(m) =>
 unpad(mapfst(ch) ++ [hd(ms)]) = None =>
 ischained(T,IV,ch,hash) =>
 injective(T) =>
 !in_rng(IV, T) =>
 ms <> [] =>
 in_dom((hd(ms), hash), T) =>
 1 < length(tl(ms)) =>
 findseq(hd(tl(ms)),T[(hd(ms),hash)],T) = None.

(** Proven in coqproofs.v *)
axiom help6 : 
forall (m:block, hash:state, T:fmap, T':fmap, invT:(state, block * state) map, I:(int, state * bool) map, icount:int),
findseq (m,hash,T) = None =>
inclusion(T',T) =>
injective(T) =>
!in_rng (IV,T) =>
inverse(T,invT) =>
!in_dom (icount,I) =>
(forall (i_5 : int), in_dom (i_5,I) => set_bad3 (fst (I[i_5]),T', T,invT) <=> snd (I[i_5])) =>
!in_dom ((m,hash),T) => 
forall (z:state), z<>IV => !in_rng(z,T) => z<>hash => (!exists(x0:block), in_dom((x0,z),T)) =>
(forall (i_5 : int), in_dom (i_5,I) => z<>fst(I[i_5])) =>
forall (i:int), in_dom (i,I[icount <- (z,true)]) => snd (I[icount <- (z,true)][i]) =>
set_bad3 (fst (I[icount <- (z,true)][i]),T', T[(m,hash) <- z], invT[z <- (m,hash)]).

unset all.
set valid_chain_upd, set_bad3_def.
(** Also proven in coqproofs.v *)
lemma help6' : 
forall (m:block, hash:state, T:fmap, T':fmap, invT:(state, block * state) map, I:(int, state * bool) map, icount:int),
!in_dom (icount,I) =>
(forall (i_5 : int), in_dom (i_5,I) => set_bad3 (fst (I[i_5]),T', T,invT) <=> snd (I[i_5])) =>
!in_dom ((m,hash),T) => 
forall (z:state), 
(forall (i_5 : int), in_dom (i_5,I) => z<>fst(I[i_5])) =>
forall (i:int), in_dom (i,I[icount <- (z,true)]) =>
set_bad3 (fst (I[icount <- (z,true)][i]),T', T[(m,hash) <- z], invT[z <- (m,hash)]) => 
snd (I[icount <- (z,true)][i]).


(** Games *)

adversary D () : bool { msg -> state; (block, state) -> state }.

game Greal = {
  var T : fmap
  var count_call : int

  fun f(x:block, y:state) : state = {
    var z : state;
    if (!in_dom((x,y),T)) {
       z = {0,1}^n;
       T[(x,y)] = z;
    }
    return T[(x,y)];
  }

  fun F(m:msg) : state = {
    var ms:padding = pad(m);
    var hash : state = IV;
    if ( count_call + length(ms) <= q) {
      count_call = count_call + length(ms);
      while(!(ms = [])) {
        hash = f(hd(ms), hash);
        ms = tl(ms);
      }
    }
    return hash;
  }

  fun f_adv(x:block, y:state) : state = {
    var z_adv : state;
    if (count_call + 1 <= q) {
      z_adv = f(x,y);
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }

  abs D = D {F, f_adv}

  fun Main() : bool = {
    var b : bool;
    count_call = 0;
    T = empty_map;
    b = D();
    return b;
  }
}.


game Greal' = {
  var count_call : int
  var T' : fmap
  var T : fmap
  var invT : (state,(block*state)) map
  var bad1, bad2, bad3 : bool
  var S : state list
  var Y : state list 
 
  fun f(x:block, y:state) : state = {
    var z : state;
    if (!in_dom((x,y),T)) {
       z = {0,1}^n;
       S = z::S;
       Y = y::Y;
       T[(x,y)] = z;
       invT[z] = (x,y);
    }
    return T[(x,y)];
  }

  fun f_bad(x:block, y:state) : state = {
    var z : state;
    if (!in_dom((x,y),T)) {
       z = {0,1}^n;
       bad1 = bad1 || (mem(z,S));
       S = z::S;
       Y = y::Y;
       bad2 = bad2 || mem(z,Y); 
       T[(x,y)] = z;
       invT[z] = (x,y);
    }
    return T[(x,y)];
  }

  fun f_adv(x:block, y:state) : state =  {
    var m:msg;
    var z_adv : state;
    if (count_call + 1 <= q) {
      if (!in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          m = proj(unpad(mapfst(proj(findseq(x,y,T')) ++ ((x,y)::[]))));
          T'[(x,y)] = f_bad(x,y); (* TODO: use f2 instead? *)
        } else {
          if (set_bad3(y,T',T,invT)) {
            bad3 = true;
            T'[(x,y)] = f(x,y); 
            (* TODO: we can also use f_bad here (and discard f completely) *)
          } else {
            T'[(x,y)] = f_bad(x,y);
          }
        }
      }
      z_adv = T'[(x,y)];
      count_call = count_call+1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }
 
  fun F(m:msg) : state = {
    var ms:padding = pad(m);
    var ch:chain = [];
    var hash : state = IV;
    if ( count_call + length(ms) <= q) {
      count_call = count_call + length(ms);
      while(1 < length(ms)) {
        ch = ch ++ (hd(ms),hash) :: [];
        hash = f_bad(hd(ms), hash);
        ms = tl(ms);
      }
      hash = f_bad(hd(ms),hash); (* TODO: use f2 instead? *)
    }   
    return hash;
  }

  abs D = D {F, f_adv}

  fun Main() : bool = {
    var b : bool;
    count_call = 0;
    T = empty_map;
    invT = empty_map;
    T' = empty_map;
    S = IV::[];
    Y = [];
    bad1 = false;
    bad2 = false;
    bad3 = false;
    b = D();
    return b;
  }
}.


(* We will prove that: Greal.Main[res] = Greal'.Main[res] *)

unset all.
set set_bad3_def.
prover "alt-ergo".
   
equiv Greal_Greal'_f_adv : Greal.f_adv ~ Greal'.f_adv : 
  ={x,y,T,count_call} && inclusion(T'{2},T{2}) ==>
  ={res,T,count_call} && inclusion(T'{2},T{2}).
  if;[ | trivial].
  inline{1} f.
  if{2}.
    (* !in_dom((x, y),T') *)
    if{2}.
      (* !(findseq (x,y,T') = None) *)
     inline{2} f_bad;derandomize;wp;rnd;trivial.
    (* findseq (x,y,T') = None *)
    if{2}.
      (* set_bad3 (y,T',T,invT) *)
      inline{2} f;derandomize;wp;rnd;trivial.
    (* !set_bad3 (y,T',T,invT) *)
    inline{2} f_bad;derandomize;wp;rnd;trivial.
  (* in_dom((x, y),T') *)
  derandomize;wp;rnd{1};trivial.
save.

set tl_length, length0, hd_tl, unpad_nil, unpad_pad.

equiv Greal_Greal'_F : Greal.F ~ Greal'.F :
  ={m,T, count_call} && inclusion(T'{2},T{2})  ==>
  ={res,T, count_call} && inclusion(T'{2},T{2}).
 app 2 3 
  ={m,T,count_call,ms,hash} && inclusion(T'{2},T{2}) &&
  (ms = pad(m)){1} && hash{1} = IV; [trivial | ]. 
 if; [ | trivial].
 app 1 1 
  ={m,T,count_call,ms,hash} && inclusion(T'{2},T{2}) &&
   (ms = pad(m)){1} && hash{1} = IV && count_call{1} <= q; [trivial | ].
 splitw{1}: 1 < length (ms).
 while >> : ={T,count_call,ms,hash} && inclusion(T'{2},T{2}) && ms{1} <> [].
 inline f, f_bad; derandomize; wp; trivial.
 condt{1}; condf{1} at 3.
 inline f, f_bad; derandomize; wp; trivial.
save.

unset tl_length, length0, hd_tl, unpad_nil, unpad_pad.

equiv Greal_Greal' : Greal.Main ~ Greal'.Main : true ==> ={res} 
  by auto (={T, count_call} && inclusion(T'{2},T{2})).

claim Greal_Greal' : Greal.Main[res] = Greal'.Main[res]
using Greal_Greal'.


game GrealRO = {
  var ROmap : (msg, state * int) map
  var T' :  fmap
  var T'i : (block * state, int) map
  var T : (block * int, int) map
  var l, icount, count_call : int
  var I : (int, state * bool) map
  var bad1, bad2, bad3 : bool
  var Y, S : state list

  fun RO(m:msg, y:state) : state * int = {
    var z : state;
    if (!in_dom(m,ROmap)) {
      z = {0,1}^n;
      bad1 = bad1 || (mem(z,S));
      S = z::S;
      Y = y::Y;
      bad2 = bad2 || mem(z,Y); (* TODO: remove this line? *)
      ROmap[m] = (z,icount);
      I[icount] = (z,false);
      icount = icount + 1;
    }
    return ROmap[m];
  }
   
  fun f_adv(x:block, y:state) : state =  {
    var m : msg;
    var z, zxy, z_adv : state;
    var j, k': int;
    var found, found_bad3 : bool;
    var c : chain;

    if (count_call + 1 <= q) {
      if (!in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          c = proj(findseq(x,y,T'));
          m = proj(unpad(mapfst(c ++ ((x,y)::[]))));
          (z,j) = RO(m,y);
          T'[(x,y)] = z;
          T'i[(x,y)] = j;
        } else {
          found = false;
          found_bad3 = false;
          j = 0;
          k' = 0;
            while (k' < icount) {
            if (snd(I[k'])) { 
              if ( (* !(found && k' = j ) && *) fst(I[k']) = y ) { 
               found_bad3 = true; 
              }
             } else {
              if (!found && fst(I[k']) = y && in_dom((x,k'),T) && snd(I[T[(x,k')]])) {
                found = true;
                j = T[(x,k')] ;
              }
            }
            k' = k' + 1;
          }

          if (found) { 
            zxy = fst(I[j]);
            I[j] = (zxy,false);
            T'[(x,y)] = zxy;
            T'i[(x,y)] = j;
          } else {
            if (found_bad3) {
              bad3 = true;
              z = {0,1}^n;
              I[icount] = (z,false);
              T'[(x,y)] = z;
              T'i[(x,y)] = icount;
              icount = icount+1;
            } else {
              z = {0,1}^n;
              bad1 = bad1 || (mem(z,S));
              S = z::S;
              Y = y::Y;
              bad2 = bad2 || mem(z,Y); 
              I[icount] = (z,false);
              T'[(x,y)] = z;
              T'i[(x,y)] = icount;
              icount = icount + 1;
            }
          }
        }
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }
 
  fun F(m:msg) : state = {
    var ms:padding = pad(m);
    var z:state;
    var i' : int;
    var i : int = 0;
    var hash : state = IV;

    if (count_call + length(ms) <= q) {
      count_call = count_call + length(ms);
      while(1 < length(ms) && in_dom((hd(ms),hash),T')) {
        i = T'i[(hd(ms),hash)];
        hash = T'[(hd(ms),hash)];
        ms=tl(ms);
      }
      while(1 < length(ms) && in_dom((hd(ms), i),T)) {
        i = T[(hd(ms),i)];
        hash = fst(I[i]);
        ms = tl(ms);
      }
      while(1 < length(ms)) {
        z = {0,1}^n;
        bad1 = bad1 || (mem(z,S));
        S = z::S;
        Y = hash::Y;
        bad2 = bad2 || mem(z,Y);
        T[(hd(ms),i)] = icount;
        I[icount] = (z,true);
        i = icount;
        hash = z;
        icount = icount + 1;
        ms = tl(ms);
      }
      (hash,i') = RO(m,hash);
    }
    return hash;
  }

  abs D = D {F, f_adv}

  fun Main() : bool = {
    var b : bool;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    S = IV::[];
    Y = [];
    bad1 = false;
    bad2 = false;
    bad3 = false;
    b = D();
    return b;
  }
}.


(* We will prove that the two game are equivalent upto 
           bad1 || bad2 || bad3 
 | Greal'.Main[res] - GrealRO.Main[res] |     <= 
 GrealRO.Main[ bad1 || bad2 || bad3]  <=
 GrealRO.Main[bad1] +  GrealRO.Main[bad2] + GrealRO.Main[bad3]
*)

pred Biginvariant(T':fmap, S:state list, Y:state list,
                  T1:fmap, T2:(block * int, int) map,
                  invT1:(state,(block*state)) map,
                  T'i2 : (block * state, int) map,
		  ROmap:(msg,state * int) map,
		  I:(int, state * bool) map,
		  icount:int) =
(inclusion(T', T1) &&
(forall (z:state), in_rng(z,T1) => mem(z,S)) &&
(forall (z:state,i:int), in_rng((z,i),ROmap) => mem(z,S)) &&
(forall (m:msg), in_dom(m,ROmap) 
  => (in_dom(snd(ROmap[m]),I) && fst(I[snd(ROmap[m])]) = fst(ROmap[m]))) &&
(forall (x:block,y:state), in_dom((x,y),T1) => mem(y,Y)) &&
injective(T1) &&
!in_rng(IV,T1) &&
(forall (i:int), !in_rng((IV,i),ROmap)) &&
inverse(T1,invT1) &&
ROmapinT(ROmap,T1) &&
(forall (x:block,y:state), in_dom((x,y),T1)
  => (in_dom((x,y),T') || y = IV || in_dom(y,invT1))) &&
(forall (i:int), in_dom(i,I) => mem(fst(I[i]), S)) &&
(forall (z:state), mem(z, S) 
  => exists (i:int), in_dom(i,I) && fst(I[i]) = z) &&
injective_fst(I) &&
claim5(T',T1) &&
1 <= icount &&
!in_dom(icount,I) &&
(forall (i:int), in_dom(i,I) => 0<=i && i<icount) &&
(forall (i:int), (0<=i && i<icount) => in_dom(i,I)) &&
(forall (z:state), in_dom(z,invT1) 
  => mem(z,S)) &&
fst(I[0]) = IV &&
(forall (i:int), in_dom(i,I)
  => (set_bad3(fst(I[i]),T',T1,invT1) <=> snd(I[i]))) &&

(forall (x:block,i:int), in_dom((x,i),T2)
  => in_dom(i,I) && in_dom((x,fst(I[i])),T1) &&
     in_dom(T2[(x,i)],I) && 
     fst(I[T2[(x,i)]]) = T1[(x,fst(I[i]))]) &&
(forall (x:block,y:state,i:int),
  !in_dom((x,y),T') && in_dom((x,y),T1) && 
  in_dom(i,I) && fst(I[i]) = y && !in_dom((x,i),T2)
  => !findseq(x,y,T1) = None) &&
 (forall (x:block,y:state), in_dom((x,y),T'i2) 
  => in_dom((x,y),T') && in_dom(T'i2[(x,y)],I) &&
     fst(I[T'i2[(x,y)]]) = T'[(x,y)]) && 
 (forall (x:block,y:state), in_dom((x,y),T') 
  => in_dom((x,y),T'i2))
).

equiv Greal'_GrealRO_f_adv : Greal'.f_adv ~ GrealRO.f_adv : 
 !bad1{1} && !bad2{1} && !bad3{1} &&
 !bad1{2} && !bad2{2} && !bad3{2} &&
 ={x,y,T',S,Y, count_call} && 
 Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}) ==>
 ={bad1,bad2,bad3} &&
 (!bad1{1} && !bad2{1} && !bad3{1} =>
  ={res,T',S,Y, count_call} && 
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).

if; [ | trivial].
app 0 0 !bad1{1} && !bad2{1} && !bad3{1} &&
 (!bad1{2} && !bad2{2} && !bad3{2} &&
 ={bad1,bad2,bad3,x,y,T',S,Y,count_call} && 
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).
trivial.

if. (* !in_dom((x, y),T') *)
  if. (* findseq (x,y,T') <> None *)
    inline.
    unfold Biginvariant.
    case{1}: in_dom((x,y),T).
      derandomize; wp; rnd.
      timeout 1.
      set findseq_last_in_dom_valid, findseq_useless_upd, set_bad3_upd, 
        findseq_pred_in_T', findseq_upd, findseq_inclusion_eq.
      print set.
      trivial. (* 33 remain *)
      prover cvc3.
      timeout 3.
      trivial. (* 1 remains *)

      unset findseq_useless_upd.
      app 0 0 ={x,y,T'} && 
        inclusion(T'{1}, T{1}) &&
        injective(T{1}) &&
        !in_rng(IV,T{1}) &&
        inverse(T{1}, invT{1}) &&
        (forall (i:int), 
         in_dom(i,I{2}) => 
         (set_bad3 (fst(I{2}[i]),T'{1},T{1},invT{1}) <=> snd(I{2}[i]))) &&
        !in_dom((x{1}, y{1}),T'{1}) &&
        in_dom((x{1}, y{1}),T{1}) &&
        findseq(x{1},y{1},T'{1}) <> None.
        trivial.
      prover "alt-ergo". 
      trivial.
      unset findseq_last_in_dom_valid, findseq_useless_upd, set_bad3_upd, 
        findseq_pred_in_T', findseq_upd, findseq_inclusion_eq.

      (* !in_dom ((x,y),T) *)
      derandomize; wp; rnd.
      set findseq_mapfst_eq, findseq_useless_upd', findseq_inclusion_eq, 
       findseq_inclusion_upd_eq.
      timeout 3.
      trivial. (* 29 remain *)
      prover cvc3.
      timeout 5.
      trivial. (* 6 remain *)
   
      unset findseq_mapfst_eq, findseq_useless_upd', findseq_inclusion_eq, 
       findseq_inclusion_upd_eq.
      set set_bad3_upd, findseq_pred_in_T', findseq_upd, findseq_upd', help.
      prover "alt-ergo".
      trivial. (* 1 remains *)
 
      app 0 0 (
       ={bad1,bad2,bad3,x,y,T',S,Y,count_call} &&
       !bad1{1} &&
       !bad2{1} &&
       !bad3{1} &&
       injective(T{1}) &&
       !in_rng(IV, T{1}) &&
       ROmapinT(ROmap{2},T{1}) &&
       !in_dom ((x{2},y{2}),T'{2}) && 
       !in_dom ((x{1},y{1}),T{1}) &&
       findseq (x{1},y{1},T'{1}) <> None && 
       findseq(x{1},y{1},T{1}) = findseq(x{1},y{1},T'{2}) &&
       !in_dom(
        proj(unpad(mapfst(proj(findseq(x{1},y{1},T{1})) ++ 
           [(x{1}, y{1})]))), ROmap{2}) && 
       !in_dom(icount{2},I{2}) && 
       (forall (z:state), 
         mem(z,S{1}) => exists (i:int), in_dom(i,I{2}) && fst(I{2}[i]) = z) &&
      forall (z_0:state),
        let m_R = proj (unpad (mapfst (proj (findseq (x{2},y{2},T'{2})) ++ 
                            [(x{2},y{2})]))) in
        let ROmap_R = ROmap{2}[m_R <- (z_0,icount{2})] in
        let I_R = I{2}[icount{2} <- (z_0,false)] in
        let z_R,j_R = ROmap_R[m_R] in
        !in_dom (m_R,ROmap{2}) =>
        mem (z_0,S{1}) <> true =>
        mem (z_0,y{1} :: Y{1}) <> true =>
        z_0 <> IV && !in_rng(z_0, T{1})).
      unset all.
      set findseq_mapfst_eq, findseq_useless_upd', findseq_inclusion_eq, 
        findseq_inclusion_upd_eq, help.
      trivial.
      set ROmapinT_upd.
      trivial.
      unset all. 
      set set_bad3_def.

  (* findseq (x,y,T') = None *)
  app 0 4 !bad1{1} && !bad2{1} && !bad3{1} &&
          ={bad1,bad2,bad3,x,y,T',S,Y,count_call} && 
	  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},
           T'i{2},ROmap{2},I{2},icount{2}) &&
	  !in_dom((x{1}, y{1}),T'{1}) &&
	  findseq (x{1},y{1},T'{1}) = None &&
	  !found{2} && !found_bad3{2} && j{2} = 0 && k'{2} = 0; auto.
  if{1}. (* set_bad3(y,T',T) *)
    while{2}>> :
      !bad1{1} && !bad2{1} && !bad3{1} &&
      ={bad1,bad2,bad3,x,y,T',S,Y,count_call} &&
      Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},
       T'i{2},ROmap{2},I{2},icount{2}) &&
     !in_dom((x{1}, y{1}),T'{1}) &&
     findseq(x{1},y{1},T'{1}) = None &&
     set_bad3 (y{1},T'{1},T{1},invT{1}) &&
     0 <= k'{2} &&
     !found{2} &&
     (!found_bad3{2} => 
      exists (i:int), k'{2} <= i && i < icount{2} && fst(I{2}[i]) = y{2}) &&
     (forall(i:int), 
       0 <= i && i < icount{2} => fst(I{2}[i]) = y{2} => snd(I{2}[i])).
     wp; trivial.
    if{2}. (* found *)
     simpl.
      (* !found *) 
      if{2}. (* found_bad3 *)
        inline; derandomize; wp; trivial.
        (* !found_bad3 *)
        trivial.
      simpl.

    (* !set_bad3 (y,T',T) *)
    while{2}>> : 
      !bad1{1} && !bad2{1} && !bad3{1} &&
      ={bad1,bad2,bad3,x,y,T',S,Y,count_call} &&
      Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},
       T'i{2},ROmap{2},I{2},icount{2}) &&
      !in_dom((x{1}, y{1}),T'{1}) &&
      findseq (x{1},y{1},T'{1}) = None &&
      !set_bad3 (y{1},T'{1},T{1},invT{1}) &&
      0 <= k'{2} && k'{2} <= icount{2} &&
      !found_bad3{2} &&
      (!found{2} => 
       forall (i:int), 
         0 <= i && i < k'{2} => 
        (!fst(I{2}[i]) = y{2} ||
	 !in_dom((x{2},i), T{2}) ||
	 !snd(I{2}[T{2}[(x{2},i)]]))) &&
      (found{2} => 
       in_dom((x{1},y{1}),T{1}) && 
       in_dom(j{2},I{2}) &&
       I{2}[j{2}] = (T{1}[(x{1},y{1})], true)).
    wp; trivial.
    inline{1}.
    app 2 0 
      !bad1{1} && !bad2{1} && !bad3{1} &&
      ={bad1,bad2,bad3,x,y,T',S,Y,count_call} && x_0{1} = x{1} && y_0{1} = y{1} &&
      Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},
       T'i{2},ROmap{2},I{2},icount{2}) &&
      !in_dom((x{1}, y{1}),T'{1}) &&
      findseq (x{1},y{1},T'{1}) = None &&
      !set_bad3 (y{1},T'{1},T{1},invT{1}) &&
      !found_bad3{2} &&
      (!found{2} => 
       forall (i:int), 
         in_dom(i,I{2}) => 
          !fst(I{2}[i]) = y{2} ||
	  !in_dom((x{2},i), T{2}) ||
	  !snd(I{2}[T{2}[(x{2},i)]])) &&
     (found{2} =>
        in_dom((x{1},y{1}),T{1}) && 
        in_dom(j{2},I{2}) &&
	I{2}[j{2}] = (T{1}[(x{1},y{1})], true)).
    trivial.
    if{2}. (* found *)
      if{1}. (* !in_dom((x, y),T) *)
        trivial.
 
        (* in_dom((x, y),T) *)
        unfold Biginvariant.
        set claim5_upd.
        prover "alt-ergo".
        timeout 5.
        trivial. (* 6 remain *) 
        unset claim5_upd.
        prover cvc3.
        timeout 14.
        trivial. (* 1 remains *)
        set help1.
        trivial.
        unset help1.
      (* !found *)
      if{2}. (* found_bad3 *)
        simpl.
        (* !found_bad3 *)
        if{1}. (* !in_dom((x_0, y_0),T)) *)
          wp; rnd.
          unfold Biginvariant.
          prover "alt-ergo", cvc3.
          timeout 1.
          trivial. (* 6 remain *)         
          set set_bad3_upd', claim5_upd'.
          timeout 3.
          trivial. (* 3 remain *)
          unset set_bad3_upd', claim5_upd'.
          set findseq_upd_nohelp, findseq_mapfst_eq, findseq_claim5, help.
          trivial. (* 1 remains *)

          app 0 0
            ={bad1,bad2,bad3,x,y,T',S,Y,count_call} && 
            x_0{1} = x{1} && y_0{1} = y{1} && 
            !bad1{1} && !bad2{1} && !bad3{1} && 
            inclusion(T'{1},T{1}) &&
            injective(T{1}) &&
            !in_rng(IV,T{1}) &&
            inverse(T{1},invT{1}) &&
            !in_dom((x{1},y{1}), T{1}) &&
            (forall (z:state), in_rng(z,T{1}) => mem(z,S{1})) && 
            (forall (x:block,y:state), in_dom((x,y),T{1}) => mem(y,Y{1})) &&
            mem(IV,S{1}) &&
            !set_bad3(y{1},T'{1},T{1},invT{1}) &&
            claim5(T'{1},T{1}) &&
            findseq(x{1},y{1},T'{1}) = None &&
            ROmapinT(ROmap{2},T{1}).
            trivial.
          set ROmapinT_upd2.
          trivial.
          unset ROmapinT_upd2.
          unset findseq_upd_nohelp, findseq_mapfst_eq, findseq_claim5, help.

          (* in_dom ((x_0, y_0),T) *)
          app 0 0 false.
          set findseq_complete_valid_chain, findseq_set_bad3_claim5.
          app 0 0
           inverse(T{1}, invT{1}) &&
           fst(I{2}[0]) = IV &&
           !in_rng(IV,T{1}) &&
           findseq(x{1},y{1},T{1}) = None &&
           in_dom((x{1}, y{1}),T{1}) &&
           !in_dom((x{1}, y{1}),T'{1}) &&
           (y{1} = IV || in_dom(y{1},invT{1})) &&
           (exists (i:int),
             in_dom(i,I{2}) && 
             fst(I{2}[i]) = y{1} &&
             (!in_dom((x{1}, i), T{2}) || !snd(I{2}[T{2}[(x{1},i)]]))) &&
           (forall (i:int),  
             in_dom(i,I{2}) => 
             (in_dom(fst(I{2}[i]),invT{1}) && 
              !in_dom(invT{1}[fst(I{2}[i])],T'{1}) &&
              forall (c:chain), !valid_chain(c++invT{1}[fst(I{2}[i])]::[], T{1})) 
             <=> snd(I{2}[i])) &&
           (forall (i:int), 
             in_dom((x{1},i),T{2}) => 
             in_dom(i,I{2}) && 
             in_dom((x{1},fst(I{2}[i])),T{1}) &&
             in_dom(T{2}[(x{1},i)],I{2}) && 
             fst(I{2}[T{2}[(x{1},i)]]) = T{1}[(x{1},fst(I{2}[i]))]) &&
           (forall (i:int),
             in_dom(i,I{2}) && 
             fst(I{2}[i]) = y{1} && 
             !in_dom((x{1},i),T{2}) => 
             !findseq(x{1},y{1},T{1}) = None).
           trivial.
           timeout 10.
           trivial. (* proved by CVC3 *)
           unset findseq_complete_valid_chain, findseq_set_bad3_claim5.
         trivial.
      trivial.
save.

equiv Greal'_GrealRO_F : Greal'.F ~ GrealRO.F : 
 !(bad1{1} || bad2{1} || bad3{1}) && !(bad1{2} || bad2{2} || bad3{2}) &&
 ={m,bad1,bad2,bad3,T',S,Y, count_call} && 
 Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}) 
 ==>
 (bad1{1} || bad2{1} || bad3{1} <=> bad1{2} || bad2{2} || bad3{2}) &&
 (!(bad1{1} || bad2{1} || bad3{1}) => 
   ={res,bad1,bad2,bad3,T',S,Y,count_call} && 
   Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).
(* Proof *)
app 3 3 
  !bad1{1} && !bad2{1} && !bad3{1} &&
  ={bad1,bad2,bad3,m,ms,hash,T',S,Y, count_call} && 
  mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
  hash{1} = IV && 
  i{2} = 0 && 
  ms{1} <> [] &&
  (tl(ms{1}) <> [] => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}).

  set mapfst_nil, ischained_nil, unpad_nil, padnil, app_nil_end,
    hd_tl, unpad_pad, prefixfree', unpad_hd.
  trivial.
  unset mapfst_nil, ischained_nil, unpad_nil, padnil, app_nil_end,
    hd_tl, unpad_pad, prefixfree', unpad_hd.
if; [ | trivial].
app 1 1 
  !bad1{1} && !bad2{1} && !bad3{1} &&
  ={bad1,bad2,bad3,m,ms,hash,T',S,Y, count_call} && 
  (mapfst(ch{1}) ++ ms{1} = pad(m{1})) && 
  hash{1} = IV && 
  i{2} = 0 && 
  ms{1} <> [] &&
  (tl(ms{1}) <> [] => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}).
 trivial. 

splitw{1}: in_dom((hd(ms),hash),T').
set findseq_ischained_unpad, length_tl_notnil.
while>> : 
  !bad1{1} && !bad2{1} && !bad3{1} &&
  ={bad1,bad2,bad3,m,ms,hash,T',S,Y,count_call} && 
  in_dom(i{2},I{2}) && 
  fst(I{2}[i{2}]) = hash{2} &&
  mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
  ms{1} <> [] &&
  (1 < length(ms{1}) => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  (1 < length(ms{1}) => findseq(hd(ms{1}), hash{1}, T{1}) = None) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}).
inline{1}; derandomize; wp; rnd{1}.
set mapfst_nil, mapfst_app, mapfst_cons, hd_tl, prefixfree',
  ischained_app, ischained_nil, unpad_pad, unpad_tl_prefix,
  app_cons_nil, help4, help5.
trivial.
unset mapfst_nil, mapfst_app, mapfst_cons, hd_tl, prefixfree',
  ischained_app, ischained_nil, unpad_pad, unpad_tl_prefix, 
  app_cons_nil, help4, help5.

splitw{1}: in_dom((hd(ms),hash),T).
while>> : 
  !bad1{1} && !bad2{1} && !bad3{1} &&
  ={bad1,bad2,bad3,m,ms,hash,T',S,Y,count_call} && 
  in_dom(i{2},I{2}) && 
  fst(I{2}[i{2}]) = hash{2} &&
  mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
  ms{1} <> [] &&
  (1 < length(ms{1}) => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  (1 < length(ms{1}) => findseq(hd(ms{1}), hash{1}, T{1}) = None) &&
  (1 < length(ms{1}) => !in_dom((hd(ms{1}), hash{1}),T'{1})) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}).
app 0 0 
  !bad1{1} && !bad2{1} && !bad3{1} &&
  ={bad1,bad2,bad3,m,ms,hash,T',S,Y, count_call} && 
  in_dom(i{2},I{2}) && 
  fst(I{2}[i{2}]) = hash{2} &&
  mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
  ms{1} <> [] &&
  (1 < length(ms{1}) => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  (1 < length(ms{1}) => findseq(hd(ms{1}), hash{1}, T{1}) = None) &&
  (1 < length(ms{1}) => !in_dom((hd(ms{1}), hash{1}),T'{1})) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}) &&
  (1 < length(ms{1}) && in_dom((hd(ms{1}), hash{1}), T{1})) =
  (1 < length(ms{2}) && in_dom((hd(ms{2}), i{2}), T{2})) &&
  1 < length (ms{1}) && in_dom((hd (ms{1}), hash{1}),T{1}) &&
  (1 < length(tl(ms{1})) =>
   unpad((mapfst(ch{1}) ++ [hd(ms{1})] ++ [hd(tl(ms{1}))])) = None) &&
  ischained(T{1},IV,ch{1} ++ [(hd (ms{1}), hash{1})],T{1}[(hd(ms{1}), hash{1})]) &&
  (1 < length(tl(ms{1})) =>
    findseq(hd(tl(ms{1})), T{1}[(hd(ms{1}), hash{1})],T{1}) = None) && 
  (1 < length(tl(ms{1})) => 
    !in_dom((hd(tl(ms{1})),T{1}[(hd(ms{1}), hash{1})]),T'{1})) && 
  fst(I{2}[T{2}[(hd (ms{2}), i{2})]]) = T{1}[(hd (ms{1}), hash{1})].
set findseq_ischained_unpad, mapfst_nil, mapfst_app, mapfst_cons, hd_tl, 
    ischained_app, ischained_nil, unpad_pad, unpad_tl_prefix, 
    app_cons_nil, help4, help5.
trivial. 
inline{1}; derandomize; wp; rnd{1}.
timeout 1.
trivial. 
unset findseq_ischained_unpad, mapfst_nil, mapfst_app, mapfst_cons, hd_tl, 
  ischained_app, ischained_nil, unpad_pad, unpad_tl_prefix, 
  app_cons_nil, help4, help5.
while>> : 
  (bad1 || bad2 || bad3){1} = (bad1 || bad2 || bad3){2} && ={m,ms} && 
  (!bad1{1} && !bad2{1} && !bad3{1} =>
   ={hash,T',S,Y, count_call} && 
   in_dom(i{2},I{2}) && 
   fst(I{2}[i{2}]) = hash{2} &&
   mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
   ms{1} <> [] &&
   (1 < length(ms{1}) => unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None) &&
   ischained(T{1},IV,ch{1},hash{1}) &&
   (1 < length(ms{1}) => findseq(hd(ms{1}), hash{1}, T{1}) = None) &&
   (1 < length(ms{1}) => !in_dom((hd(ms{1}), hash{1}),T{1})) &&
   Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).
inline{1}; derandomize; wp; rnd.
app 0 0 
  (bad1 || bad2 || bad3){1} = (bad1 || bad2 || bad3){2} &&
  ={m,ms} && 
  1 < length(ms{1}) && 
  (!bad1{1} && !bad2{1} && !bad3{1} =>
   ={hash,T',S,Y, count_call} && 
   in_dom(i{2},I{2}) && 
   fst(I{2}[i{2}]) = hash{2} &&
   mapfst(ch{1}) ++ ms{1} = pad(m{1}) && 
   ms{1} <> [] &&
   unpad(mapfst(ch{1}) ++ [hd(ms{1})]) = None &&
   ischained(T{1},IV,ch{1},hash{1}) &&
   findseq(hd(ms{1}), hash{1}, T{1}) = None &&
   !in_dom((hd(ms{1}), hash{1}),T{1}) &&
   Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2}) &&
   (1 < length(tl(ms{1})) =>
    unpad((mapfst(ch{1}) ++ [hd(ms{1})] ++ [hd(tl(ms{1}))])) = None) &&
   (forall (z:state), 
    z <> IV && !mem(z,S{2}) && !mem(z,hash{2}::Y{2}) => 
  ischained(upd(T{1},(hd(ms{1}),hash{1}),z),IV, ch{1} ++ [(hd(ms{1}),hash{1})],z))).
  set findseq_ischained_unpad, mapfst_nil, mapfst_app, mapfst_cons,
    hd_tl, ischained_app, ischained_nil, ischained_cons, ischained_upd',
    unpad_pad, unpad_tl_prefix, app_cons_nil, help4, help5.
  trivial. 
  app 0 0
   !bad1{1} && !bad2{1} && !bad3{1} =>
   1 < length (tl (ms{1})) =>
   unpad (mapfst(ch{1} ++ [(hd (ms{1}), hash{1})]) ++ [hd (tl (ms{1}))]) = None.
    trivial.
  trivial.

set help5', injective_upd.
timeout 10.
trivial. (* only Biginvariant remains *)
unfold Biginvariant.
  trivial.
  set findseq_upd_nohelp, ischained_last_cases.
  trivial. (* 4 remain *)
  set help1', help6, help6', ROmapinT_upd3.
  trivial. (* 0 remain *)
unset findseq_ischained_unpad, mapfst_nil, mapfst_app, mapfst_cons,
  hd_tl, ischained_app, ischained_nil, ischained_cons, ischained_upd',
  unpad_pad, unpad_tl_prefix, app_cons_nil, help4, help5, help5',
  injective_upd, findseq_upd_nohelp, ischained_last_cases, help1',
  help6, help6', ROmapinT_upd3.

timeout 5.
inline.
app 2 2 
  (bad1 || bad2 || bad3){1} = (bad1 || bad2 || bad3){2} &&
  ={m,ms} && m_0{2} = m{2} && y{1} = hash{1} &&
  (!bad1{1} && !bad2{1} && !bad3{1} =>
    ={y,hash,T',S,Y, count_call} && 
    ms{1} = [x{1}] && 
  in_dom(i{2},I{2}) && 
  fst(I{2}[i{2}]) = hash{2} &&
  mapfst(ch{1}) ++ ms{1} = pad(m{1}) &&
  ischained(T{1},IV,ch{1},hash{1}) &&
  !findseq(x{1},y{1},T{1}) = None &&
  findseq(x{1},y{1},T{1}) = Some(ch{1}) &&
  m{1} = proj(unpad(mapfst(proj(findseq(x{1},y{1},T{1})) ++ [(x{1},y{1})]))) &&
  Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).
  set hd_length_one, findseq_complete_unique, mapfst_app, mapfst_cons,
     mapfst_nil, unpad_pad.
  trivial.
  timeout 15.
  trivial.
  unset hd_length_one, findseq_complete_unique, mapfst_app, mapfst_cons, 
    mapfst_nil, unpad_pad.
set findseq_mapfst_eq.
if{1}; [ | if{2}; [ trivial | trivial ] ].
if{2}; [ | trivial ].
  wp; rnd.
  trivial. (* only Biginvariant remains *)
  unfold Biginvariant.
  set findseq_useless_upd', ischained_last_cases, findseq_upd', ROmapinT_upd.
  trivial. (* 3 remain *)
  timeout 10.
  unset findseq_useless_upd', ischained_last_cases, findseq_upd', ROmapinT_upd.
  app 0 0 
   !in_dom((x{1},y{1}),T{1}) &&
   (!bad1{1} && !bad2{1} && !bad3{1} =>
   ={hash,S,Y, count_call} && 
   injective(T{1}) && 
   !in_rng(IV,T{1}) &&
   inverse(T{1},invT{1}) && 
   mem(IV,S{1}) &&
   (forall (z:state), in_rng(z,T{1}) => mem(z,S{1})) &&
   (forall (x:block,y:state), in_dom((x,y),T{1}) => mem(y,Y{1})) &&
   !in_dom(icount{2},I{2}) &&
   (forall (i:int), in_dom(i,I{2}) => mem(fst(I{2}[i]), S{1})) &&
   (forall (z:state), 
    mem(z, S{2}) => exists (i:int), in_dom(i,I{2}) && fst(I{2}[i]) = z) &&
   (forall (z:state), in_dom(z,invT{1}) => mem(z,S{1})) &&
   (forall (i:int), 
     in_dom(i,I{2}) => 
     (set_bad3(fst(I{2}[i]),T'{1},T{1},invT{1}) <=> snd(I{2}[i]))) &&
   !findseq(x{1},y{1},T{1}) = None).
    trivial.
  set valid_chain_upd_nohelp', get_upd_overwrite, set_bad3_upd_I, help.
  trivial. (* 1 remains *)
   app 0 0
    forall (z:state), 
      !bad1{1} => !bad2{1} => !bad3{1} =>
      !mem(z,S{1}) =>
      !mem(z,y{1}::Y{1}) =>
      forall (i:int),
        in_dom(i,upd(I{2},icount{2},(z, false))) =>
        snd(upd(I{2},icount{2},(z, false))[i]) =>
      in_dom(fst(I{2}[icount{2} <- (z,false)][i]), invT{1}[z <- (x{1}, y{1})]) &&
      in_dom(fst(I{2}[i]), invT{1}) &&
      !in_dom(invT{1}[z <- (x{1}, y{1})]
                     [fst(I{2}[icount{2} <- (z, false)][i])],T'{1}) &&
      forall (c:chain),
        !valid_chain(
          c++[invT{1}[z <- (x{1}, y{1})][fst(I{2}[icount{2} <- (z,false)][i])]],
          T{1}[(x{1},y{1}) <- z]).
   trivial.
  trivial.
save.

unset valid_chain_upd_nohelp', get_upd_overwrite, set_bad3_upd_I, help,
  findseq_mapfst_eq, length_tl_notnil.

set valid_chain_empty.

lemma help2 : 
 let I = empty_map[0 <- (IV,false)] in in_dom(0,I) && fst(I[0]) = IV.


equiv Greal'_GrealRO : Greal'.Main ~ GrealRO.Main : 
  true ==> 
  (bad1 || bad2 || bad3){1} = (bad1 || bad2 || bad3){2} &&
  (!(bad1 || bad2 || bad3){1} => ={res})
by auto upto (bad1 || bad2 || bad3) with 
 (={bad1,bad2,bad3,T',S,Y,count_call} && 
 Biginvariant(T'{1},S{1},Y{1},T{1},T{2},invT{1},T'i{2},ROmap{2},I{2},icount{2})).
unset help2, valid_chain_empty.

claim Greal'_GrealRO : 
  | Greal'.Main[res] - GrealRO.Main[res] | <= GrealRO.Main[bad1 || bad2 || bad3]
using Greal'_GrealRO.

claim GrealRO_split2 : 
  GrealRO.Main[bad1 || bad2 || bad3] <= 
  GrealRO.Main[bad1] +  GrealRO.Main[bad2 || bad3]
split.

claim GrealRO_split3 : 
  GrealRO.Main[bad2 || bad3] <= GrealRO.Main[bad2] +  GrealRO.Main[bad3]
split.

claim fact1 : 
  | Greal.Main[res] - GrealRO.Main[res] | <= 
  GrealRO.Main[bad1] + GrealRO.Main[bad2] + GrealRO.Main[bad3].

unset Greal_Greal', Greal'_GrealRO, GrealRO_split2, GrealRO_split3.


(*
 We bound the probability of GrealRO.Main[bad1] 
 and GrealRO.Main[bad2]. 
*)

game GrealRO_bad = {
  var ROmap : (msg,state * int) map
  var T' :  fmap
  var T'i : (block * state, int) map
  var T : (block * int, int) map
  var count_call : int
  var icount : int
  var I : (int, state * bool) map
  var bad1, bad2, bad3 : bool
  var S : state list
  var Y : state list
  var l : int

  fun sample_z (y:state) : state = {
    var z : state;
    if (length(S) <= q && length(Y) < q) {
      z = {0,1}^n;
      if (mem(z,S)) { bad1 = true; }
      S = z::S;
      Y = y::Y;
      if (mem(z,Y)) { bad2 = true; }
    } else { 
      z = IV; 
    }
    return z;
  }

  fun RO(m:msg, y:state) : state * int = {
    var z : state;
    if (!in_dom(m,ROmap)) {
       z = sample_z (y);
       ROmap[m] = (z,icount);
       I[icount] = (z,false);
       icount=icount+1;
    }
    return ROmap[m];
  }
   
  fun f_adv(x:block, y:state) : state =  {
    var m:msg;
    var z, zxy : state;
    var j, k': int;
    var found, found_bad3 : bool;
    var c : chain;
    var z_adv : state;

    if (count_call + 1 <= q) {

      if (!in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          c = proj(findseq(x,y,T'));
          m = proj(unpad(mapfst(c ++ ((x,y)::[]))));
          (z,j) = RO(m,y);
          T'[(x,y)] = z;
          T'i[(x,y)] = j;
          
        } else {
          
          found = false;
          found_bad3 = false;
          j = 0;
          k' = 0;
            while (k' < icount) {
            if (snd(I[k'])) { 
              if ( fst(I[k']) = y ) { found_bad3 = true; }
            } else {
              if (!found && fst(I[k']) = y && in_dom((x,k'),T) && snd(I[T[(x,k')]])) {
                found = true;
                j = T[(x,k')];
              }
            }
            k' = k' + 1;
          }

          if (found) { 
            zxy =fst(I[j]);
            I[j] = (zxy,false);
            T'[(x,y)] = zxy;
            T'i[(x,y)] = j;
          } else {
            if (found_bad3) {
              bad3 = true;
              z = {0,1}^n;
              I[icount] = (z,false);
              T'[(x,y)] = z;
              T'i[(x,y)] = icount;
              icount = icount+1;
            } else {
              z = sample_z (y);
              I[icount] = (z,false);
              T'[(x,y)] = z;
              T'i[(x,y)] = icount;
              icount = icount + 1;
            }
          }
        }
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }
 
  fun F(m:msg) : state = {
    var ms:padding = pad(m);
    var z:state;
    var i' : int;
    var i : int = 0;
    var hash : state = IV;
    if (count_call + length(ms) <= q) {
      count_call = count_call + length(ms);
      while(1<length(ms) && in_dom((hd(ms),hash),T')) {
        i = T'i[(hd(ms),hash)];
        hash = T'[(hd(ms),hash)];
        ms=tl(ms);
      }
      while(1 < length(ms) && in_dom((hd(ms), i),T)) {
        i = T[(hd(ms),i)];
        hash = fst(I[i]);
        ms = tl(ms);
      }
      while(1 < length(ms)) {
        z = sample_z (hash);
        T[(hd(ms),i)] = icount;
        I[icount] = (z,true);
        i = icount;
        hash = z;
        icount = icount + 1;
        ms = tl(ms);
      }
      (hash,i') = RO(m,hash);
    }
    return hash;
  }

  abs D = D {F, f_adv}

  fun Main() : bool = {
    var b : bool;
    S = IV::[];
    Y = [];
    bad1 = false;
    bad2 = false;
    bad3 = false;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    b = D();
    return b;
  }
}.


equiv GrealRO_GrealRO_bad_fadv : GrealRO.f_adv ~ GrealRO_bad.f_adv :
  ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, x, y} && 
  (length(S) - 1 <= count_call){1} &&
  (length(Y) <= count_call){1} && 
  (count_call <= q){1} ==>
  ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, res} && 
  (length(S) - 1 <= count_call){1} && (length(Y) <= count_call){1} &&
  (count_call <= q){1}.
if;[ | trivial].
if;[ | trivial].
if.
timeout 3.
inline RO, sample_z; derandomize; wp; rnd.
trivial.
wp.
app 5 5  
 ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, x, y,
   found, found_bad3, j, k'} && 
 (length(S) - 1 <= count_call){1} && 
 (length(Y) <= count_call){1} && 
 count_call{1} <= q && count_call{1} + 1 <= q.

while :
  ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, x, y,
    found, found_bad3, j, k'} && 
  (length(S) - 1 <= count_call){1} && 
  (length(Y) <= count_call){1} && 
  count_call{1} <= q && count_call{1} + 1 <= q.
wp; trivial.
wp; trivial.
if; [wp; trivial | ].
if; [wp; rnd; wp; trivial | ].
inline sample_z; derandomize; wp; rnd; trivial.
save.

set tl_length, length0, hd_tl, unpad_nil, unpad_pad.

equiv GrealRO_GrealRO_bad_fadv : GrealRO.F ~ GrealRO_bad.F :
  ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, m} && 
  (length(S) - 1 <= count_call){1} && 
  (length(Y) <= count_call){1} && 
  count_call{1} <= q 
  ==>
  ={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y, res} &&
  (length(S) - 1 <= count_call){1} && 
  (length(Y) <= count_call){1} && 
  count_call{1} <= q.
app 3 3  
  ={ROmap,T',T'i,T,count_call,icount,I,bad1,bad2,bad3,S,Y,m,ms,i,hash} && 
  (length(S) - 1 <= count_call){1} &&
  (length(Y) <= count_call){1} && 
  (count_call <= q){1} &&
  (1 <= length(ms)){1}.
wp; trivial.
if;[ | trivial].
app 1 1 
  ={ROmap,T',T'i,T,count_call,icount,I,bad1,bad2,bad3,S,Y,m,ms,i,hash} && 
  (length(S) - 1 <= count_call - length(ms) ){1} && 
  (length(Y) <= count_call - length(ms)){1} && 
  (count_call <= q){1} && (1 <= length(ms)){1}.
trivial.
while>> : 
 ={ROmap,T',T'i,T,count_call,icount,I,bad1,bad2,bad3,S,Y,m,ms,i,hash} && 
  (length(S) - 1 <= count_call - length(ms) ){1} && 
  (length(Y) <= count_call - length(ms)){1} && 
  (count_call <= q){1} && (1 <= length(ms)){1}.
trivial.
while>> :
 ={ROmap,T',T'i,T,count_call,icount,I,bad1,bad2,bad3,S,Y,m,ms,i,hash} && 
  (length(S) - 1 <= count_call - length(ms) ){1} && 
  (length(Y) <= count_call - length(ms)){1} && 
  (count_call <= q){1} && (1 <= length(ms)){1}.
trivial.
while>> : 
 ={ROmap,T',T'i,T,count_call,icount,I,bad1,bad2,bad3,S,Y,m,ms,i,hash} && 
  (length(S) - 1 <= count_call - length(ms) ){1} && 
  (length(Y) <= count_call - length(ms)){1} && 
  (count_call <= q){1} && (1 <= length(ms)){1}.
inline sample_z; derandomize; trivial.
inline RO; inline sample_z; derandomize; wp; rnd; trivial.
save.

set tl_length, length0, hd_tl, unpad_nil, unpad_pad.
set q_pos.

equiv  GrealRO_GrealRO_bad : GrealRO.Main ~ GrealRO_bad.Main :
  true ==>
  ={bad1, bad2} && 
  (length(S) - 1 <= count_call){2} && 
  (length(Y) <= count_call){2} &&
  (count_call <= q){2}
by auto 
  (={ROmap,T',T'i, T, count_call, icount, I, bad1, bad2, bad3, S, Y} && 
   (length(S) - 1 <= count_call){1} && (length(Y) <= count_call){1} && 
   (count_call <= q){1}).

claim Pr_bad1_eq : 
  GrealRO.Main[bad1] = GrealRO_bad.Main[bad1 && length(S) - 1 <= q]
using GrealRO_GrealRO_bad.

claim Pr_bad2_eq : GrealRO.Main[bad2] = GrealRO_bad.Main[bad2 && length(Y) <= q]
using GrealRO_GrealRO_bad.

timeout 10.
set n_pos.

claim Pr_bad1 : 
  GrealRO_bad.Main[bad1 && length(S)-1 <= q] <= q%r * (q%r / (2^n)%r)
compute 5 (bad1), (length(S)-1).

claim Pr_bad2 : 
  GrealRO_bad.Main[bad2 && length(Y) <= q] <= q%r * (q%r / (2^n)%r)
compute 5 (bad2), (length(Y)).

unset n_pos.

claim fact1_bad : 
  | Greal.Main[res] - GrealRO.Main[res] | <= 
  q%r * (q%r / (2^n)%r) + q%r * (q%r / (2^n)%r) + GrealRO.Main[bad3].

unset fact1, Pr_bad1, Pr_bad1_eq, Pr_bad2, Pr_bad2_eq, pow2_pos, q_pos.

(* 
 We still have to bound the probability of bad3 and to show that
 GrealRO.Main[res] is equal to Gideal.Main[res]. For both we use eager sampling.
 
 We focus on GrealRO.Main[res]
*)

game GidealEager = {
  var ROmap : (msg,state * int) map
  var T' :  fmap
  var T'i : (block * state, int) map
  var T : (block * int, int) map
  var icount : int
  var I : (int, state * bool) map
  var bad4 : bool
  var Yadv : state list
  var l : int
  var count_call : int

  fun RO(m:msg) : state * int = {
    var z : state;
    if (!in_dom(m,ROmap)) {
       z = {0,1}^n;
       ROmap[m] = (z,icount);
       I[icount] = (z,false);
       icount=icount+1;
    }
    return ROmap[m];
  }
   
  fun f_adv(x:block, y:state) : state =  {
    var m:msg;
    var z, zxy : state;
    var j, k' : int;
    var found : bool;
    var z_adv : state;

    if (count_call + 1 <= q) {
      if (0 < icount && !in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          m = proj(unpad(mapfst(proj(findseq(x,y,T')) ++ ((x,y)::[]))));
          (z,j) = RO(m);
          T'[(x,y)] = z;
          T'i[(x,y)] = j;
        } else {
          found = false;
          j = 0;
          k' = 0;
            while (k' < icount && !found) {
            if (!snd(I[k']) && fst(I[k']) = y && 
              in_dom((x,k'),T) && snd(I[T[(x,k')]]) && k' < T[(x,k')] && 
              T[(x,k')] < icount) {
              found = true;
              j =T[(x,k')] ;
            } else {
              k' = k' + 1;
            }
          }
          if (found) { 
            zxy =fst(I[j]);
            if (mem(zxy,Yadv)) { bad4 = true; }
            I[j] = (zxy,false);
            T'[(x,y)] = zxy;
            T'i[(x,y)] = j;
          } else {
            z = {0,1}^n;
            I[icount] = (z,false);
            T'[(x,y)] = z;
            T'i[(x,y)] = icount;
            icount = icount+1;
          }
        }
        Yadv = y :: Yadv;
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }
 
  fun F(m:msg) : state = {
    var ms:padding;
    var z:state;
    var i' : int;
    var i : int;
    var hash : state;
    var icount' : int;
    if (0 < icount) {   
      ms = pad(m);
      i = 0;
      hash = IV;
      icount' = icount;
      if (count_call + length(ms) <= q) {
        count_call = count_call + length(ms);
        while(1<length(ms) && in_dom((hd(ms),hash),T')) {
          i = T'i[(hd(ms),hash)];
          hash = T'[(hd(ms),hash)];
          ms=tl(ms);
        }
            while(1 < length(ms) && in_dom((hd(ms), i),T)) {
          i = T[(hd(ms),i)];
          ms = tl(ms);
        }
            while(1 < length(ms)) {
          z = {0,1}^n;
          T[(hd(ms),i)] = icount;
          I[icount] = (z,true);
          i = icount;
          icount = icount + 1;
          ms = tl(ms);
        }
        (hash,i') = RO(m);
      }
    } else {
      hash = IV;
    }
    return hash;
  }

  abs D = D {F, f_adv}

  fun Main() : bool = {
    var b : bool;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    bad4 = false;
    Yadv = [];
    l = 0; (* Needed to satisfy syntactic condition on eager sampling? *)
    l = 0;
    while (l < icount) {
      if (snd(I[l])) { I[l] = ({0,1}^n, true);}
      l = l + 1;
    }
    l = 0;
    b = D();
    return b;
  }
}.

(* We prove that:
   GrealRO.Main ~ GidealEager.Main : true ==> 
       ={res} && 
       ({ bad3{1} } => 
         (bad4{2} || 
         exists (i:int), 
           { 0 <= i } && { i < icount{2} } &&
           { snd(I{2}[i]) } && { mem(fst(I{2}[i]), Yadv{2}) }))
   This allow to conclude:
   GrealRO.Main[res] = GidealEager.Main[res]
*)

pred Inv_I (icount:int, ROmap:(msg,state*int)map, 
            T':(block*state,state)map, T'i:(block*state, int)map, 
            T:(block *int, int)map) =
  0 < icount &&
  (forall (xy:block*state), in_dom(xy,T') => in_dom(xy,T'i)) &&
  (forall (m:msg), in_dom(m,ROmap) => snd(ROmap[m]) < icount) &&
  (forall (xy:block*state), in_dom(xy,T'i) => T'i[xy] < icount) &&
  (forall (xi:block*int), in_dom(xi,T) => T[xi] < icount) &&
  (forall (xi:block*int), in_dom(xi,T) => snd(xi) < T[xi]).

pred Inv_exists (icount:int, I:(int,state*bool)map, Yadv: state list) =
  exists (i:int), 
   0 <= i && i < icount && snd(I[i]) && mem(fst(I[i]), Yadv).


(* Proven in coqproofs.v *)
axiom Inv_exists_add_i : 
  forall (icount:int, I:(int,state*bool)map, Yadv: state list, zb:state*bool),
     Inv_exists(icount, I, Yadv) =>
     Inv_exists(icount+1, upd(I,icount,zb), Yadv).

lemma Inv_exists_cons : 
  forall (icount:int, I:(int,state*bool)map, Yadv: state list, y:state),
    Inv_exists (icount, I, Yadv) =>
    Inv_exists (icount, I, y::Yadv).

(* Proven in coqproofs.v *)
axiom Inv_exists_upd_not_in :  
  forall (icount:int, I:(int,state*bool)map, Yadv: state list, j:int),
    !mem(fst(I[j]),Yadv) => 
    Inv_exists(icount, I, Yadv) =>
    Inv_exists(icount, upd(I,j, (fst(I[j]), false)), Yadv).

equiv GrealRO_GidealEager_f_adv : GrealRO.f_adv ~ GidealEager.f_adv :
   ={x,y,T,T',T'i,I,icount,ROmap,count_call} &&  
   Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
   (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2})))
   ==>
   ={res,T,T',T'i,I,icount,ROmap,count_call} && 
   Inv_I(icount{1},ROmap{1},T'{1}, T'i{1},T{1}) &&
   (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))).
  if; [ | trivial].
  if; [ | trivial].
  (* !in_dom((x, y),T') *)
  unfold Inv_I.
  if; [inline RO; derandomize; trivial | ].

  (* findseq(x,y,T') = None *)
  app 5 4 
    ={x,y,T,T',T'i,I,icount,ROmap,found,j,count_call} && 
    0 < icount{1} && j{1} < icount{1} &&
    Inv_I(icount{1},ROmap{1},T'{1}, T'i{1},T{1}) &&
    (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) &&
    (found_bad3{1} => 
     exists (i:int), 
       0 <= i && i < icount{2} && snd(I{2}[i]) && fst(I{2}[i]) = y{2}).
    splitw{1} last: !found.
    while{1} << : 
      ={found,j,I,icount,y,count_call} && 
       0 <= k'{1} && j{1} < icount{1} &&
       (k'{1} < icount{1} => found{1}) &&
       (found_bad3{1} => 
          exists (i:int), 
            0 <= i && i < icount{2} &&  snd(I{2}[i]) && fst(I{2}[i]) = y{2}).
      trivial.
    while: 
      ={x,y,T,T',T'i,I,icount,ROmap,found,j,count_call} && 
      0 <= k'{1} &&
      k'{1} <= icount{2} && 
      j{1} < icount{1} &&
      (!found{1} => ={k'}) &&
      0 < icount{1} && 
      (forall (xi:block*int), in_dom(xi,T{1}) => T{1}[xi] < icount{1}) &&
      (forall (xi:block*int), in_dom(xi,T{1}) => snd(xi) < T{1}[xi]) &&
      (found_bad3{1} => 
         exists (i:int),
           0 <= i && i < icount{2} && snd(I{2}[i]) && fst(I{2}[i]) = y{2}); 
      trivial.
    trivial.
  unfold Inv_I.
  if; [trivial | ].

  (* !found *)
  if{1}; trivial.
save.


set tl_length, length0, hd_tl, unpad_nil, unpad_pad.
unset Inv_exists_cons, Inv_exists_upd_not_in.

equiv GrealRO_GidealEager_F : GrealRO.F ~ GidealEager.F :
  ={m,T,T',T'i,I,icount,ROmap, count_call} && 
  Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
  (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) ==>
  ={res,T,T',T'i,I,icount,ROmap, count_call} && 
  Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) && 
  (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))).
  condt{2} at 1.
  app 3 4 
    ={m,T,T',T'i,I,icount,ROmap, hash,i,ms,count_call} && 
    Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
    (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) &&
    i{1} = 0 && 1 <= length(ms{1}); [trivial | ].
  if; [ | trivial].
  app 1 1 
    ={m,T,T',T'i,I,icount,ROmap, hash,i,ms,count_call} && 
    Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
    (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) &&
    i{1} = 0 && 1 <= length(ms{1}); [trivial | ].
  while >> : 
    ={m,T,T',T'i,I,icount,ROmap, hash,i,ms,count_call} && 
    Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
    (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) &&
    i{1} < icount{1} && 1 <= length(ms{1}); [trivial | ].
  while >> : 
    ={m,T,T',T'i,I,icount,ROmap,i,ms,count_call} && 
    Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
    (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))) &&
    i{1} < icount{1} && 1 <= length(ms{1}); [trivial | ].
  while >> : 
    ={m,T,T',T'i,I,icount,ROmap,i,ms,count_call} && 
    Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
    (bad3{1} => (bad4{2}|| Inv_exists(icount{2},I{2},Yadv{2}))) &&
    (1 < length(ms{1}) => (!in_dom((hd(ms), i),T)){1}) &&
    i{1} < icount{1} && 1 <= length(ms{1}); [trivial | ].
  inline RO; derandomize; trivial.
save.
    
equiv GrealRO_GidealEager : GrealRO.Main ~ GidealEager.Main : 
  true ==> 
  ={res} && (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2}))).
(* Proof: *)
auto 
  (={T,T',T'i,I,icount,ROmap,count_call} && 
  Inv_I(icount{1},ROmap{1},T'{1},T'i{1},T{1}) &&
  (bad3{1} => (bad4{2} || Inv_exists(icount{2},I{2},Yadv{2})))).
  unroll{2} last; condf{2} last.
  derandomize; wp; rnd{2}; trivial.
save.

unset tl_length, length0, hd_tl, unpad_nil, unpad_pad, Inv_exists_add_i.

claim GrealRO_GidealEager_res : GrealRO.Main[res] = GidealEager.Main[res]
using GrealRO_GidealEager.

(* We add this operator to be able to express the probability of Inv_exists. *)
op check_exists : (int, (int,state * bool) map, state list) -> bool.

axiom check_exists_Inv_exists : 
  forall (icount:int, I:(int,state * bool)map, Yadv: state list),
    check_exists(icount, I, Yadv) <=> Inv_exists(icount, I, Yadv).

claim GrealRO_GidealEager_bad3 : 
  GrealRO.Main[bad3] <= GidealEager.Main[bad4 || check_exists(icount,I,Yadv)]
using GrealRO_GidealEager.

(* Now we show that the probability of res in GidealEagerRes is the same that
   the probability of res in Gideal.
   We do a step of eager sampling using the game GidealLazy.
   This step will also allows to bound GidealEager.Main[bad4 || check_exists(icount,I,Yadv)].
*)

game GidealLazy = GidealEager
   where f_adv =  {
    var m:msg;
    var z, z', zxy : state;
    var j, k' : int;
    var found : bool;
    var z_adv : state;

    if (count_call + 1 <= q) {
      if (0 < icount && !in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          m = proj(unpad(mapfst(proj(findseq(x,y,T')) ++ ((x,y)::[]))));
          (z,j) = RO(m);
          T'[(x,y)] = z;
          T'i[(x,y)] = j;
        } else {
          found = false;
          j = 0;
          k' = 0;
            while (k' < icount && !found) {
            if (!snd(I[k']) && fst(I[k']) = y && 
              in_dom((x,k'),T) && snd(I[T[(x,k')]]) && k' < T[(x,k')] && 
              T[(x,k')] < icount) {
              found = true;
              j =T[(x,k')];
            } else {
              k' = k' + 1;
            }
          }
          if (found) { 
            zxy ={0,1}^n;
            if (mem(zxy,Yadv)) { bad4 = true; }
            I[j] = (zxy,false);
            T'[(x,y)] = zxy;
            T'i[(x,y)] = j;
          } else {
            z = {0,1}^n;
            I[icount] = (z,false);
            T'[(x,y)] = z;
            T'i[(x,y)] = icount;
            icount = icount+1;
          }
        }
        Yadv = y :: Yadv;
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }

  and Main = {
    var b : bool;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    bad4 = false;
    Yadv = [];
    l = 0;
    b = D();
    l = 0;
    while (l < icount) {
      if (snd(I[l])) { I[l] = ({0,1}^n, true);}
      l = l + 1;
    }
    l = 0;
    return b;
  }.

op upd_T : (block list, int, int, (block*int, int) map) ->
           int * (block list * (block*int, int) map).

axiom upd_T_le : 
  forall (ms:block list, icount:int, i:int, T:(block * int, int) map),
    length(ms) <= 1 =>
    upd_T(ms,icount,i,T) = (i,(ms,T)).

axiom upd_T_gt :
  forall (ms:block list, icount:int, i:int, T:(block*int, int) map),
    1 < length(ms) =>
    upd_T(ms,icount,i,T) = 
    upd_T(tl(ms), icount+1, icount,upd(T,(hd(ms),i),icount)).

set tl_length, length0, hd_tl, unpad_nil, unpad_pad, eq_ext_eq.

timeout 2.

equiv GidealLazy_GidealEager :
  GidealLazy.Main ~ GidealEager.Main : true ==> ={res,bad4,I,icount,Yadv}
  by eager { l = 0;
          while (l < icount) {
            if (snd(I[l])) { I[l] = ({0,1}^n, true);}
            l = l + 1;
          }
          l = 0;
        }.
(* eager for f_adv *)
  if{1}.  
    (* count_call{1} + 1 <= q *)
    condt{2} at 4; [trivial | ].
    while{2} << : true; try derandomize; trivial.
    if{1}.
    (* (0 < icount) && !in_dom((x,y),T'){1} *)
    condt{2} at 4; [trivial | ].
    while{2} << : true; try derandomize; trivial.    
    if{1}.
      (* (find_seq (x,y,T') <> none){1} *)
      condt{2} at 4; [trivial | ].
      while{2} << : true; try derandomize; trivial.  
      inline RO; derandomize.
      swap{2} [5-6] -3.
      app 3 3 
        ={x,y,ROmap,T',T'i,T,icount,I,bad4,Yadv,l,z_0_0,m,m_0, count_call} &&
        0 < icount{1}; [wp; rnd; trivial | ].
      if{1}.
        (* !in_dom(m_0,ROmap) *)
        condt{2} at 4; [trivial | ].
        while{2} << : true; try derandomize; trivial. 
        swap{2} [4-5] -3.
        swap{2} [8-13] -5.
        app 11 9 
          ={x,y,ROmap,T',T'i,T,bad4,Yadv,l,z_0_0,m,m_0,z_0,z,j,l,
            count_call,z_adv} &&
          l{2} < icount{2} &&
          icount{1} = icount{2} + 1 &&
           ext_eq(I{1},(upd(I,icount,(z_0,false))){2}); [trivial | ].
        splitw{1}: l < icount - 1.
        while >> : 
          ={x,y,ROmap,T',T'i,T,bad4,Yadv,l,z_0_0,m,m_0,z_0,z,j,l,z_adv,count_call}
          && (l <= icount){2} && icount{1} = icount{2} + 1 && 
           ext_eq(I{1},(upd(I,icount,(z_0,false))){2}).
          derandomize; trivial.
        wp; unroll{1}; condf{1} last.
        condf{1} at 1; trivial.
      (* in_dom(m_0,ROmap) *)
      condf{2} at 4; [trivial | ].
      while{2} << : true; try derandomize; trivial.  
      wp; while << : ={l,icount,I}.
        derandomize;wp;rnd;trivial.
      trivial.

    (* (find_seq(x,y,T') = none){1} *)
    condf{2} at 4; [trivial | ].
    while{2} << : true; try derandomize; trivial.   
    app 4 0 
      ={x,y,ROmap,T',T'i,T,bad4,Yadv,icount, I, count_call} && 
      0 < icount{1} &&
      (!found{1} => 
       forall (i:int),
         0 <= i => i < icount{1} => 
         !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
           snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
      (found{1} =>
       (forall (i:int), 
         0 <= i => i < k'{1} => 
         !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
           snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
         (!snd(I[k']) && fst(I[k']) = y && in_dom((x,k'),T) && snd(I[T[(x,k')]]) && 
         k' < T[(x,k')] && T[(x,k')] < icount){1} &&
         (j = T[(x,k')]){1} &&
         0 <= k'{1} && k'{1} < icount{1}).
    while{1} : 
      ={x,y,ROmap,T',T'i,T,bad4,Yadv,icount,I,count_call} && 
      0 < icount{1} && 0 <= k'{1} && (k' <= icount){1} &&
      (!found{1} => 
       forall (i:int),
         0 <= i => i < k'{1} => 
         !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
         snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
      (found{1} =>
       (forall (i:int), 
         0 <= i => i < k'{1} => 
         !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
           snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
         (!snd(I[k']) && fst(I[k']) = y && in_dom((x,k'),T) && snd(I[T[(x,k')]]) && 
         k' < T[(x,k')] && T[(x,k')] < icount){1} &&
         (j = T[(x,k')]){1} &&
         0 <= k'{1} && k'{1} <= icount{1}) :
       -(found{1} ? icount{1} : k'{1}), -icount{1}; trivial.
    if{1}.
      (* found{1} : this is the hard case *)
      swap{1} 3 -1.
      swap{1} [3-8] 3.
      app 5 3 
        ={x,y,ROmap,T',T'i,T,bad4,Yadv,l,icount,count_call} && 
        0 < icount{1} &&
        !(snd(I[k'])){1} &&
        (fst(I[k']) = y){1} &&
        (in_dom((x, k'),T)){1} &&
        (k' < T[(x, k')]){1} &&
        (T[(x, k')] < icount){1} &&
        (j = T[(x, k')]){1} &&
        0 <= k'{1} && 
        (forall (i:int), 
          0 <= i => i < k'{1} => 
          !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
           snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
        ext_eq(I{1},upd(I{2},j{1},(zxy{1}, false))) &&
        I{2}[j{1}] = (zxy{1},true) && 
        I{1}[j{1}] = (zxy{1},false).
        wp.
        splitw{2} last: 
         !(!snd(I[l]) && fst(I[l]) = y && in_dom((x,l),T) && 
         snd(I[T[(x,l)]]) && l < T[(x,l)] && T[(x,l)] < icount).
        splitw{1} last: l < k'.
        let{2} at 3 k'2 : int = l; let {2} at 4 j2 : int = T[(x,k'2)].
        splitw{1} last: l < j.
        splitw{2} last: l < j2.
        unroll last.
        derandomize.
        while<< : 
          ={l,icount} && 
          !(snd(I[k'])){1} &&
          (fst(I[k']) = y){1} &&
          k'{1} < j{1} && j{1} < l{1} &&
          (forall (i:int), 
            0 <= i => i < k'{1} => 
            !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
             snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
          ext_eq(I{1},upd(I{2},j{1},(zxy{1}, false))) &&
          I{2}[j{1}] = (zxy{1},true) && 
          I{1}[j{1}] = (zxy{1},false).
          derandomize; trivial.
        wp.
        while<< : 
          ={l,icount} &&  
          !(snd(I[k'])){1} &&
          (fst(I[k']) = y){1} &&
          l{1} <= j{1} && j{1} = j2{2} &&
          k'{1} = k'2{2} && k'{1} < j{1} && 
          (forall (i:int), 
             0 <= i => i < k'{1} => 
             !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
              snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
           ext_eq(I{1},upd(I{2},j{1},(zxy{1}, false))) &&
           snd(I{2}[j{1}]) && 
           I{1}[j{1}] = (zxy{1},false).
          derandomize; trivial.
        wp.
        timeout 5. (* need higher timeout for "alt-ergo" 0.94 than for 0.93 *)
        while<< : 
          ={l,icount,T,x,y} &&
          !(snd(I[k'])){1} &&
          (fst(I[k']) = y){1} &&
          (in_dom((x, k'),T)){1} &&
          (k' < T[(x, k')]){1} &&
          (T[(x, k')] < icount){1} &&
          (j = T[(x, k')]){1} &&
          0 <= k'{1} && 
          (forall (i:int),
             0 <= i => i < k'{1} => 
             !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
              snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
           (forall (i:int), 
            0 <= i => i < k'{1} => 
            !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
             snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){2}) &&
           ext_eq(I{1},upd(I{2},j{1},(zxy{1}, false))) &&
           snd(I{2}[j{1}]) && 
           I{1}[j{1}] = (zxy{1},false) &&
           0 <= l{1} && l{1} <= k'{1}.
          derandomize; wp; rnd; trivial.
        wp; rnd{1}; rnd; trivial. 

      derandomize; wp.
      while{2}<< : 
         ={x,y,T,icount} && 
         0 <= k'{2} && k'{2} <= k'{1} &&
         (found{2} => ={j}) && 
         !(snd(I[k'])){1} &&
         (fst(I[k']) = y){1} &&
         (in_dom((x, k'),T)){1} &&
         (k' < T[(x, k')]){1} &&
         (T[(x, k')] < icount){1} &&
         (j = T[(x, k')]){1} &&
         k'{1} < icount{1} &&
         (forall (i:int), 
           0 <= i => i < k'{1} => 
           !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
           snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount){1}) &&
         ext_eq(I{1},upd(I{2},j{1},(zxy{1}, false))) &&
         I{2}[j{1}] = (zxy{1},true) &&
         I{1}[j{1}] = (zxy{1},false) : -(found{2} ? icount{2} : k'{2}), -icount{2}.
        timeout 10.
        wp; trivial.
        timeout 2.
        wp; rnd{2}; trivial.
        wp; trivial.

    (* !found *)
    derandomize; wp.
    while{2}<< : 
      ={T,x,y} && 
      !found{2} && 0 <= k'{2} && k'{2} <= icount{2} && 0 < icount{2} &&
      icount{1} = icount{2} + 1 &&
      (forall (i:int),
        0 <= i => i < icount{1} - 1 => 
        !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
        snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount - 1){1}) &&
      I{1} = upd(I{2},icount{2},(z_0{1},false)) : 
      -(found{2} ? icount{2} : k'{2}), -icount{2}.
      timeout 10.
      wp; trivial.
    wp; splitw{1} last: l < icount-1.
    unroll{1} last; condf{1} last.
    derandomize; wp.
    while<< : 
      ={l} && icount{1} = icount{2} + 1 && 
      I{1} = upd(I{2},icount{2},(z{1},false)) &&
      (forall (i:int),
        0 <= i => i < icount{1} - 1 => 
        !(!snd(I[i]) && fst(I[i]) = y && in_dom((x,i),T) && 
        snd(I[T[(x,i)]]) && i < T[(x,i)] && T[(x,i)] < icount - 1){1}).
      derandomize; trivial.
    wp; rnd{1}; trivial.
    wp; trivial.
  (* !((0 < icount) && !in_dom((x,y),T')){1} *)
  condf{2} at 4.   
  wp; while<< : ={l,icount,I}.
    derandomize; trivial.
  trivial.
  (* count_call{1} + 1 > q *)
  timeout 2.
  condf{2} at 4; [trivial | ].
  while{2}<< : true; derandomize; trivial.
  swap{1} 3.
  wp; while<< : ={icount,I,l}.
   derandomize; trivial.
  trivial.
save.

(* eager for F *)
  if{1}.
    (* 0 < icount{1} *)
    condt{2} at 4; [trivial | ].
    while{2}<< : true; derandomize; trivial.
    case{1}: count_call + length(pad(m)) <= q.
    condt{1} at 5; [trivial | ].
    condt{2} at 8; [wp;trivial | ].
    while{2}<< : true; derandomize; trivial.
    swap {2} [1-3] 7.
    app 7 7 
      ={ms,i,ROmap,T',T'i,T,icount,bad4,Yadv,l,m, icount',count_call} && 
      ext_eq(I{1},I{2}) &&
      1 <= length(ms{1}) &&
      icount'{1} = icount{1} && 0 < icount{1}.
      while<< : ={T,ms,i} && 1 <= length(ms{1}).
        trivial.
      while<< : ={T',T'i,ms,i,hash} && 1 <= length(ms{1}); trivial.
    while{1}>> : 
      ={ROmap,T',T'i,bad4,Yadv,m, icount', count_call} &&
      icount'{1} = icount{2} && icount'{1} <= icount{1} &&
      0 < icount{2} &&
      1 <= length(ms{1}) &&
      length(ms{1}) <= length(ms{2}) &&
      (forall (i:int), 
       (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
      (forall (i:int), 
       (i < icount{2} || icount{1} <= i) => 
       (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
      (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
      icount{1} = icount{2} + length(ms{2}) - length(ms{1}) &&
      (upd_T(ms,icount,i,T)){1} = (upd_T(ms,icount,i,T)){2}.
      wp; trivial.
    inline RO; derandomize.
    app 2 1 
      ={ROmap,T',T'i,bad4,Yadv,m, z_0_0, icount', count_call} &&
      icount'{1} = icount{2} && 
      icount'{1} <= icount{1} && 
      0 < icount{2} &&
      m_0{1} = m{1} &&
      length(ms{1}) <= length(ms{2}) &&
      length(ms{1}) = 1 &&
      (forall (i:int), 
       (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
      (forall (i:int), 
       (i < icount{2} || icount{1} <= i) => 
       (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
      (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
      icount{1} = icount{2} + length(ms{2}) - length(ms{1}) &&
      ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}.
      trivial.
    if{1}.
      (* !in_dom(m_0,ROmap){1} *)
      app 6 1 
        ={T',T'i,bad4,Yadv,m, z_0_0, l, icount', count_call} && 
        icount'{1} = icount{2} && 
        icount'{1} <= icount{1} && 
        0 < icount{2} &&
        l{1} <= icount'{1} &&
        (!in_dom(m,ROmap)){2} &&
        ROmap{1} = upd(ROmap{2},m{1},((z_0_0,icount-1)){1}) &&
        I{1}[icount{1}-1] = (z_0_0{1}, false) &&
        hash{1} = z_0_0{1} &&
        1 <= length(ms{2}) &&
        (forall (i:int),
         (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
        (forall (i:int), 
         (i < icount{2} || icount{1} <= i) => 
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
        (forall (i:int), 
         icount{2} <= i => i < icount{1}-1 => snd(I{1}[i])) &&
        icount{1} = icount{2} + length(ms{2}) && 
        ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}; [ trivial | ].
      splitw{1}: l < icount'.
      while>> : 
        ={T',T'i,bad4,Yadv,m, z_0_0, l, icount',count_call} && 
        icount'{1} = icount{2} && 
        0 < icount{2} && 
        l{1} <= icount'{1} &&
        (!in_dom(m,ROmap)){2} &&
        ROmap{1} = upd(ROmap{2},m{1},((z_0_0,icount-1)){1}) &&
        I{1}[icount{1}-1] = (z_0_0{1}, false) &&
        hash{1} = z_0_0{1} &&
        1 <= length(ms{2}) &&
        (forall (i:int), 
         (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
        (forall (i:int), 
         (i < icount{2} || icount{1} <= i) => 
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
        (forall (i:int), 
         icount{2} <= i => i < icount{1}-1 => snd(I{1}[i])) &&
        icount{1} = icount{2} + length(ms{2}) &&  
        ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}.
        derandomize; trivial.
      app 0 1 
        ={T',T'i,bad4,Yadv,m, z_0_0, count_call} &&
        l{1} = icount'{1} && 
        0 < icount{2} &&
        icount'{1} = icount{2} &&
        (!in_dom(m,ROmap)){2} && 
        l{2} = 0 &&
        ROmap{1} = upd(ROmap{2},m{1},((z_0_0,icount-1)){1}) &&
        I{1}[icount{1}-1] = (z_0_0{1}, false) &&
        hash{1} = z_0_0{1} &&
        1 <= length(ms{2}) &&
        (forall (i:int), 
         (icount{2} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
        (forall (i:int), 
         (i < icount{2} || icount{1} <= i) => 
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
        (forall (i:int), 
         icount{2} <= i => i < icount{1}-1 => snd(I{1}[i])) &&
        icount{1} = icount{2} + length(ms{2}) &&  
        ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2};[ trivial | ].
      splitw{1}: l < icount - 1.
      while>> :
        ={T',T'i,bad4,Yadv,m, z_0_0, count_call} &&
        l{1} = icount{2} && 
        l{2} = 0 &&
        (!in_dom(m,ROmap)){2} &&
        ROmap{1} = upd(ROmap{2},m{1},((z_0_0,icount-1)){1}) &&
        I{1}[icount{1}-1] = (z_0_0{1}, false) &&
        hash{1} = z_0_0{1} &&
        1 <= length(ms{2}) &&
        (forall (i:int), 
           (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
        in_dom(icount{1}-1, I{1}) && 
        (forall (i:int), 
           (i < icount{2} || icount{1} <= i) => 
           (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
        (forall (i:int), 
          icount{2} <= i => i < icount{1}-1 => snd(I{1}[i])) &&
        icount{1} - length(ms{2}) = icount{2} &&  
        ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}.
      derandomize; trivial.
      unroll{1}.
      condt{1} at 1.
      condf{1} at 4; wp; trivial.
      app 0 0 ext_eq(I{1},upd(I{2},icount{2},(z_0_0{2}, false))); trivial.
    (* in_dom(m_0,ROmap){1} *)
    swap{1} 3.
    app 1 1 
      ={T',T'i,bad4,Yadv,m, z_0_0, l, icount', ROmap,count_call} && 
      icount'{1} = icount{2} && 
      icount'{1} <= icount{1} && 
      0 < icount{2} &&
      l{1} <= icount'{1} &&
      (in_dom(m,ROmap)){2} &&
      (m_0 = m){1} &&
      1 <= length(ms{2}) &&
      (forall (i:int), 
        (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
        (forall (i:int), 
         (i < icount{2} || icount{1} <= i) =>
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&
      (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
        icount{1} = icount{2} + length(ms{2})-1 && 
        ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2};[ trivial | ].
    splitw{1}: l < icount'.
    while>> : 
      ={T',T'i,bad4,Yadv,m, l, icount', ROmap, count_call} && 
      icount'{1} = icount{2} && 
      0 < icount{2} && 
      l{1} <= icount'{1} &&
      (in_dom(m,ROmap)){2} && 
      (m_0 = m){1} &&
      1 <= length(ms{2}) &&
      (forall (i:int), 
        (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
      (forall (i:int), 
        (i < icount{2} || icount{1} <= i) => 
        (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&    
      (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
      icount{1} = icount{2} + length(ms{2}) - 1 &&  
      ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}.
      derandomize; trivial.
    app 0 1 
      ={T',T'i,bad4,Yadv,m, ROmap, count_call} &&
      l{1} = icount'{1} && 
      0 < icount{2} && 
      icount'{1} = icount{2} &&
      (in_dom(m,ROmap)){2} && 
      (m_0 = m){1} && 
      l{2} = 0 &&
      1 <= length(ms{2}) &&
      (forall (i:int), 
         (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
       (forall (i:int),
         (i < icount{2} || icount{1} <= i) => 
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&    
       (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
       icount{1} = icount{2} + length(ms{2}) - 1 &&  
       ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}; [trivial | ].
    while>> : 
      ={T',T'i,bad4,Yadv,m, ROmap, count_call} &&
      l{1} = icount{2} && 
      (in_dom(m,ROmap)){2} && 
      (m_0 = m){1} && 
      l{2} = 0 &&
      1 <= length(ms{2})  &&
      (forall (i:int), 
         (icount'{1} <= i && i < icount{1}) => in_dom(i,I{1})) &&  
      (forall (i:int), 
         (i < icount{2} || icount{1} <= i) => 
         (in_dom(i,I{1}) = in_dom(i,I{2})) && I{1}[i] = I{2}[i]) &&    
       (forall (i:int), icount{2} <= i => i < icount{1} => snd(I{1}[i])) &&
       icount{1} = icount{2} + length(ms{2}) - 1 &&  
       ((i,(ms,T))){1} = (upd_T(ms,icount,i,T)){2}.
       derandomize; trivial.
    condf{2} at 2; trivial.
    app 0 0 ext_eq(I{1},I{2}); trivial. 
    derandomize; trivial.
  (* !((count_call{1} + length(pad(m{1}))) <= q) *)
  condf{1} at 5; [trivial | ].
  condf{2} at 8.
  swap{1} [1-4] 3.
  wp; while<< : ={l,icount,I}; derandomize; trivial.
  (* !(0 < icount{1}) *)
  condf{2} at 4.
  wp; while{2}<< : true; derandomize; trivial.
  swap{1} 3; wp.
  while<< : ={l, I, icount}.
    derandomize; trivial.
  trivial.
save.

(* Head *)
trivial.

(* Tail *)
trivial.
save.

unset tl_length, length0, hd_tl, unpad_nil, unpad_pad, upd_T_le,
  upd_T_gt, eq_ext_eq.

claim GidealLazy_GidealEager_res : GidealLazy.Main[res] = GidealEager.Main[res]
using GidealLazy_GidealEager.

claim GidealLazy_GidealEager_bad :
  GidealLazy.Main[bad4 || check_exists(icount,I,Yadv)] = 
  GidealEager.Main[bad4 || check_exists(icount,I,Yadv)]
using GidealLazy_GidealEager.

(*
   We have to prove that the GidealLazy.Main[res] = Gideal.Main[res].
*)

game Gideal = {
  var ROmap : (msg,state) map
  var T' :  fmap
  var count_call : int

  fun F(m:msg) : state = {
    var z : state;
    if (!in_dom(m,ROmap)) {
      z = {0,1}^n;
      ROmap[m] = z;
    }
    return ROmap[m];
  } 

  fun f_adv(x:block, y:state) : state =  {
    var m:msg;
    var z_adv:state;

    if (count_call + 1 <= q) {
      if (!in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          m = proj(unpad(mapfst(proj(findseq(x,y,T')) ++ ((x,y)::[]))));
          T'[(x,y)] = F(m);
        } else {
          T'[(x,y)] = {0,1}^n;
        }
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv= IV;
    }
    return z_adv;
  }

  fun F_adv (m:msg) : state = { 
    var z_adv : state;
    if ( count_call + length(pad(m)) <= q) { 
      count_call = count_call + length(pad(m));
      z_adv = F(m);
    } else {
      z_adv = IV;
    }
    return z_adv;
  }

  abs D = D {F_adv, f_adv}

  fun Main() : bool = {
    var b : bool;
    count_call = 0;
    T' = empty_map;
    ROmap = empty_map;
    b = D();
    return b;
  }
}.

pred eq_fst (ROmap1:(msg, state * int) map, ROmap2:(msg, state) map) =
  (forall (m:msg), in_dom(m,ROmap1) = in_dom(m,ROmap2)) &&
  (forall (m:msg),
     in_dom(m,ROmap1) => fst(ROmap1[m]) = ROmap2[m]).

equiv GidealLazy_Gideal_F : GidealLazy.F ~ Gideal.F_adv :
  ={m,T',count_call} && 
  eq_fst(ROmap{1}, ROmap{2}) &&
  Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1})
  ==>
  ={res,T',count_call} && 
  eq_fst(ROmap{1}, ROmap{2}) &&
  Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}).
proof.
condt{1} at 1.
if{2}.
  condt{1} at 5; [ trivial | ].
  app 8 1 
    ={m,T', count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
    Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
    i{1} < icount{1}.
  while{1}<< : 
    ={m,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
    Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
    i{1} < icount{1}.
  set tl_length.
    wp; trivial.
  while{1}<< : 
    ={m,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
    Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
    i{1} < icount{1} : length(ms{1}), -1.
    wp; trivial.
  while{1}<< : 
    ={m,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
    Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
    i{1} < icount{1} : length(ms{1}), -1.
   trivial.
   trivial.
  unset tl_length.
  inline RO, F; derandomize; trivial.
  condf{1} at 5.
  trivial.
save.

equiv GidealLazy_Gideal_f : GidealLazy.f_adv ~ Gideal.f_adv :
  ={x,y,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
  Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) 
  ==>
  ={res,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
  Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}).
proof.
if;[ | trivial].
if;[ | trivial].
  (* !in_dom ((x, y),T') *)
  if.
  (* !(findseq (x,y,T') = None) *)
    unfold Inv_I; inline{1} RO; inline{2} F.
    derandomize; trivial.
  (* !(findseq (x,y,T') = None) *)
    app 4 0 
      ={x,y,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
      Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
      j{1} < icount{1}.
     while{1}<< : 
       ={x,y,T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
       Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1}) &&
       j{1} < icount{1} : -(found{1} ? icount{1} : k'{1}), -icount{1}; trivial.
if{1}; derandomize; trivial.
save.
  
equiv GidealLazy_Gideal : GidealLazy.Main ~ Gideal.Main : true ==> ={res}.
proof.
wp; while{1}<< : ={b}.
derandomize; wp; rnd{1}; trivial.
auto 
  (={T',count_call} && eq_fst(ROmap{1}, ROmap{2}) &&
  Inv_I(icount{1}, ROmap{1}, T'{1}, T'i{1}, T{1})).
save.

claim GidealLazy_Gideal : GidealLazy.Main[res] = Gideal.Main[res]
using GidealLazy_Gideal.

claim fact2 :  
  | Greal.Main[res] - Gideal.Main[res] | <= 
  q%r * (q%r / (2^n)%r) + q%r * (q%r / (2^n)%r) +
  GidealLazy.Main[bad4 || check_exists(icount,I,Yadv)].

unset fact1_bad, GrealRO_GidealEager_res, GrealRO_GidealEager_bad3,
  GidealLazy_GidealEager_res, GidealLazy_GidealEager_bad, GidealLazy_Gideal.


(* We still have to bound the GrealRO.Main[bad4 || check_exists(icount,I,Yadv)] *)

game GidealLazy' = GidealLazy
   where Main = {
    var b : bool;
    var z : state;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    bad4 = false;
    Yadv = [];
    l = 0;
    b = D();
    l = 0;
    while (l < icount) {
      if (snd(I[l])) { 
        z = {0,1}^n;
        if (mem(z,Yadv)) { bad4 = true; }
        I[l] = (z, false);
      }
      l = l + 1;
    }
    l = 0;
    return b;
  }.

equiv GidealLazy_GidealLazy'_RO : GidealLazy.RO ~ GidealLazy'.RO :
  ={m,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1} ==>
  ={res,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}
by auto.

equiv GidealLazy_GidealLazy'_f_adv : GidealLazy.f_adv ~ GidealLazy'.f_adv :
  ={x,y,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1} 
  ==>
  ={res,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}.
proof.
if;[ | trivial].
if;[ | trivial].
(* (0 < icount) && !in_dom((x, y),T') *)
if; [auto using GidealLazy_GidealLazy'_RO | ].
derandomize; wp.
while<< : ={x,y,I,T,found, icount, k',j,count_call};trivial.
save.

equiv GidealLazy_GidealLazy'_F : GidealLazy.F ~ GidealLazy'.F :
  ={m,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}
  ==>
  ={res,ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}.
proof.
if;[ | trivial].
case: count_call + length(pad(m)) <= q.
condt at 5.
trivial.
trivial.
auto using GidealLazy_GidealLazy'_RO.
while<< : ={ms,icount,i,I,T} && 0 < icount{1}; [trivial | ].
while<< : ={ms,i,T}; [auto | ].
while<< : ={hash,T'i,T',i,ms}; auto.
condf at 5; trivial.
save.

pred EqExcept (l:int,I1:(int,state*bool)map, I2:(int,state*bool)map) =
  forall (i:int), (i < 0 || l <= i) => I1[i] = I2[i].

lemma EqExcept_add :
  forall (l:int,I1:(int,state*bool)map, I2:(int,state*bool)map),
    EqExcept(l,I1,I2) => EqExcept(l+1,I1,I2).

lemma EqExcept_upd : 
  forall (i:int, l:int,I1:(int,state*bool)map, I2:(int,state*bool)map,
          zb1:state*bool, zb2:state*bool),
    EqExcept(l,I1,I2) => 
    0 <= i => i < l => 
    EqExcept(l,upd(I1,i,zb1),upd(I2,i,zb2)).

equiv GidealLazy_GidealLazy' : GidealLazy.Main ~ GidealLazy'.Main :
  true ==> bad4{1} || Inv_exists(icount{1},I{1},Yadv{1}) => bad4{2}.
proof.
app 12 12 
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}.
auto (={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} && 0 < icount{1}). 
wp.
while<< :
  ={icount,Yadv, l} && 0 <= l{1} && l{1} <= icount{1} &&
  (bad4{1} => bad4{2}) &&
  EqExcept(l{1},I{1},I{2}) &&
  (forall (i:int), 
    0 <= i => i < l{1} => snd(I{1}[i]) => mem(fst(I{1}[i]), Yadv{1}) => bad4{2}).
derandomize; trivial.
trivial.
save.

claim GidealLazy_GidealLazy' : 
  GidealLazy.Main[bad4 || check_exists(icount,I,Yadv)] <= GidealLazy'.Main[bad4]
using GidealLazy_GidealLazy'.


(* We next bound the probability of bad4 *)
  
game GidealLazy_bad = {
  var ROmap : (msg,state * int) map
  var T' :  fmap
  var T'i : (block * state, int) map
  var T : (block * int, int) map
  var icount : int
  var I : (int, state * bool) map
  var bad4 : bool
  var Yadv : state list
  var l : int
  var count_call : int

  fun sample_z (b:bool) : state = {
    var z : state;
    if (0 <= icount) {
      z = {0,1}^n;
      I[icount] = (z,b);
      icount=icount+1;
    } else {
      z = IV;
    }
    return z;
  }

  fun resample_z (i:int) : state = {
     var z : state;
     if (length(Yadv) <= q && 0 <= i && i < icount && snd(I[i]) ) {
       z = {0,1}^n;
       if (mem(z,Yadv)) { bad4 = true; }
       I[i] = (z, false);
     } else {
       z = IV;
     }
     return z;
   }

  fun RO(m:msg) : state * int = {
    var z : state;
    if (!in_dom(m,ROmap)) {
      z = sample_z(false);
      ROmap[m] = (z,icount - 1);
    }
    return ROmap[m];
  }

  fun f_adv(x:block, y:state) : state =  {
    var m:msg;
    var z, z', zxy : state;
    var j, k' : int;
    var found : bool;
    var z_adv : state;

    if (count_call + 1 <= q) {
      if (0 < icount && !in_dom((x,y),T')) {
        if (!(findseq(x,y,T') = None)) {
          m = proj(unpad(mapfst(proj(findseq(x,y,T')) ++ ((x,y)::[]))));
          (z,j) = RO(m);
          T'[(x,y)] = z;
          T'i[(x,y)] = j;
        } else {
          found = false;
          j = 0;
          k' = 0;
          while (k' < icount && !found) {
            if (!snd(I[k']) && fst(I[k']) = y && 
              in_dom((x,k'),T) && snd(I[T[(x,k')]]) && k' < T[(x,k')] && 
              T[(x,k')] < icount) {
              found = true;
              j =T[(x,k')];
            } else {
              k' = k' + 1;
            }
          }
          if (found) { 
            zxy = resample_z(j);
            T'[(x,y)] = zxy;
            T'i[(x,y)] = j;
          } else {
            T'i[(x,y)] = icount;
            z = sample_z(false);
            T'[(x,y)] = z;
          }
        }
        Yadv = y :: Yadv;
      }
      z_adv = T'[(x,y)];
      count_call = count_call + 1;
    } else {
      z_adv = IV;
    }
    return z_adv;
  }
 
  fun F(m:msg) : state = {
    var ms:padding;
    var z:state;
    var i' : int;
    var i : int;
    var hash : state;
    var icount' : int;
    if (0 < icount) {   
      ms = pad(m);
      i = 0;
      hash = IV;
      icount' = icount;
      if (count_call + length(ms) <= q) {
        count_call = count_call + length(ms);
        while(1<length(ms) && in_dom((hd(ms),hash),T')) {
          i = T'i[(hd(ms),hash)];
          hash = T'[(hd(ms),hash)];
          ms=tl(ms);
        }
        while(1 < length(ms) && in_dom((hd(ms), i),T)) {
          i = T[(hd(ms),i)];
          ms = tl(ms);
        }
        while(1 < length(ms)) {
          T[(hd(ms),i)] = icount;
          i = icount;
          z = sample_z(true);
          ms = tl(ms);
        }
        (hash,i') = RO(m);
      }
    } else {
      hash = IV;
    }
    return hash;
  }

  abs D = D {F, f_adv}

  fun Main () : bool = {
    var b : bool;
    var z : state;
    count_call = 0;
    I = empty_map;
    I[0] = (IV,false);
    icount = 1;
    T = empty_map;
    T' = empty_map;
    T'i = empty_map;
    ROmap = empty_map;
    bad4 = false;
    Yadv = [];
    l = 0;
    b = D();
    l = 0;
    while (l < icount) {
      if (snd(I[l])) {
        z = resample_z(l);
      }
      l = l + 1;
    }
    l = 0;
    return b;
  }
}.

equiv GidealLazy'_GidealLazy_bad_fadv :  GidealLazy'.f_adv ~ GidealLazy_bad.f_adv :
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call, x,y} &&
  (icount - 1 <= count_call && count_call <= q &&
   length(Yadv{1}) <= count_call{1} && 0 < icount{1}){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi])
  ==> 
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call, res} &&
  (icount - 1 <= count_call && count_call <= q &&
   length(Yadv{1}) <= count_call{1} && 0 < icount{1}){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]).
proof.
if; [ | trivial ].
if; [ | trivial ].
if.
inline RO, sample_z; derandomize; trivial.
app 4 4 
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call, x,y,j,found} &&
  (icount - 1 <= count_call && count_call <= q &&
   length(Yadv{1}) <= count_call{1} && 0 < icount{1}){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]) &&
  count_call{1} < q &&
  (found{1} => (0 <= j && j < icount && snd(I[j])){1}).
while<< : 
 ={k',icount,found,j,x,y,T,I} && 
 (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]) &&
 (found{1} => (0 <= j && j < icount && snd(I[j])){1}).
trivial.
trivial.
if.
inline resample_z; derandomize; trivial.
inline sample_z; derandomize; trivial.
save.


equiv GidealLazy'_GidealLazy_bad_F :  GidealLazy'.F ~ GidealLazy_bad.F :
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call, m} &&
  (icount{1} - 1 <= count_call{1} && count_call{1} <= q &&
  length(Yadv{1}) <= count_call{1} && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi])
  ==> 
  ={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call, res} &&
  (icount{1} - 1 <= count_call{1} && count_call{1} <= q &&
  length(Yadv{1}) <= count_call{1} && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]).
proof.
if;[ | trivial].
set tl_length, length0, hd_tl, unpad_nil, unpad_pad.
app 4 4 
  ={ROmap,T',T'i,T,icount,I,bad4,Yadv,count_call,m,ms,i,hash,icount'} &&
  (icount{1} - 1 <= count_call{1} && count_call{1} <= q &&
  length(Yadv{1}) <= count_call{1} && 1 <= length(ms) && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]); [trivial | ].
if; [ | trivial].
app 1 1
   ={ROmap,T',T'i,T,icount,I,bad4,Yadv,count_call,m,ms,i,hash,icount'} &&
   (icount - 1 <= count_call - length(ms) && count_call <= q &&
    length(Yadv) <= count_call - length(ms) && 1 <= length(ms) && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]); [trivial | ].
while>> :
  ={ROmap,T',T'i,T,icount,I,bad4,Yadv,count_call,m,ms,i,hash,icount'} &&
  (icount - 1 <= count_call - length(ms) && count_call <= q &&
    length(Yadv) <= count_call - length(ms) && 1 <= length(ms) && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]); [trivial | ].
while>> :
  ={ROmap,T',T'i,T,icount,I,bad4,Yadv,count_call,m,ms,i,hash,icount'} &&
  (icount - 1 <= count_call - length(ms) && count_call <= q &&
    length(Yadv) <= count_call - length(ms) && 1 <= length(ms) && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]); [trivial | ].
while>> :
  ={ROmap,T',T'i,T,icount,I,bad4,Yadv,count_call,m,ms,i,hash,icount'} &&
  (icount - 1 <= count_call - length(ms) && count_call <= q &&
    length(Yadv) <= count_call - length(ms) && 1 <= length(ms) && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi]).
inline sample_z; derandomize; trivial.
inline RO, sample_z; derandomize; trivial.
save.

unset tl_length, length0, hd_tl, unpad_nil, unpad_pad.
set q_pos.

equiv GidealLazy'_GidealLazy_bad : GidealLazy'.Main ~ GidealLazy_bad.Main :
  true ==> ={bad4} && (0 < icount && icount - 1 <= q){2}.
proof.
wp; while<< : ={l,icount,I,Yadv,bad4} && length(Yadv{1}) <= q && 0 <= l{1}.
inline resample_z; derandomize; trivial.
auto 
  (={ROmap, T', T'i, T, icount, I, bad4, Yadv, count_call} &&
  (icount - 1 <= count_call && count_call <= q &&
   length(Yadv) <= count_call  && 0 < icount){1} &&
  (forall (xi:block * int), in_dom(xi,T{1}) => 0 <= T{1}[xi])).
save.

(* 
** count_false(I,count) returns the number of 0 <= i < count such that
** snd(I[i]) = false
*)
op count_false : ((int, state * bool) map, int) -> int.

axiom count_false_bound :
  forall (I:(int, state * bool) map, icount:int),
    0 <= icount => count_false(I,icount) <= icount.

claim GidealLazy'_GidealLazy_bad : 
  GidealLazy'.Main[bad4] = 
  GidealLazy_bad.Main[bad4 && count_false(I,icount) - 1 <= q]
using GidealLazy'_GidealLazy_bad.

set pow2_pos, n_pos, q_pos. 

axiom count_false_empty: count_false(empty_map, 0) = 0.

axiom count_false_extend: 
  forall (I:(int, state * bool) map, icount:int, b:bool, z:state),
    0 <= icount =>
    count_false(I[icount <- (z,b)], icount + 1) = 
    count_false(I, icount) + (b ? 0 : 1).

(* TODO this is a trivial implication of the previous axiom *)
axiom count_false_extend_le: 
  forall (I:(int, state * bool) map, icount:int, b:bool, z:state),
    0 <= icount =>
    count_false(I, icount) <= count_false(I[icount <- (z,b)], icount + 1).

lemma count_false_init: count_false(empty_map[0 <- (IV,false)], 1) = 1.

axiom count_false_upd: 
  forall (I:(int, state * bool) map, i,icount:int, b:bool, z:state), 
    0 <= i => i < icount => snd(I[i]) =>
    count_false(I[i <- (z,false)], icount) = count_false(I,icount) + 1. 

claim Pr_bad4 : 
  GidealLazy_bad.Main[bad4 && count_false(I,icount) - 1 <= q] <=
  q%r * (q%r / (2^n)%r)
compute 10 (bad4), (count_false(I,icount) - 1).

lemma help3 : 1%r + 1%r + 1%r = 3%r.

claim Conclusion : 
  | Greal.Main[res] - Gideal.Main[res] | <= 3%r * q%r * (q%r / (2^n)%r).
