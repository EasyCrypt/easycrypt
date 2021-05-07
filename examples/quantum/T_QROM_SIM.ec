require import AllCore List Distr DBool DProd DList DMap DInterval CHoareTactic IntDiv.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal BRA.
require import VD.
require (****) T_QROM.

abstract theory T_QROM_SIM.

import Big.BAdd F.

clone include T_QROM with
   type from = FT.t,
   type hash = FT.t,
   op MUFF.FinT.enum <- FT.Support.enum,
   op dhash <- FT.dunifin
proof *.
realize MUFF.FinT.enum_spec. by apply FT.Support.enum_spec. qed.
realize dhash_ll. by apply FT.dunifin_ll. qed.
realize dhash_uni. by apply FT.dunifin_uni. qed.
realize dhash_fu. by apply FT.dunifin_fu. qed.

op q : { int | 0 <= q} as q_ge0.

op genseed = dlist FT.dunifin (2 * q).

op compute1(seed : hash list, x : from) : hash =
   bigi predT 
     (fun (j : int) => exp x j * nth F.zeror seed j) 0 (2 * q).
            
module LQRO : QRO_i = {
  
  proc init() = { 
    var seed : hash list;
    seed <$ genseed;
    QRO.h <- compute1 seed;
 }

 include QRO [h]

}.

op dcompute : (from -> hash) distr = 
  dmap genseed (fun seed => compute1 seed).

clone import QROM_Fundamental_Lemma as FL with
    op q <- q
    proof q_ge0 by smt(q_ge0).

section.

local clone import DMapSampling with 
  type t1 <- hash list,
  type t2 <- (from -> hash).

lemma eager_sampling  (A<:AdvRO{-QRO, -LQRO}[main : `{Inf, #H.h : q}]) &m (r : result):
  Pr[ QRO_main(A,LQRO).main() @ &m: res = r] = Pr[ QRO_main_D(A).main(dcompute) @ &m: res = r]. 
proof.
byequiv (_: _ ==> ={res}) => //.
proc; sim; conseq />.
transitivity*{1} { QRO.h <@ S.map(genseed, compute1); } => //; 1: smt ().
+ inline *; wp; rnd; wp; skip => />.
transitivity*{1} { QRO.h <@ S.sample(genseed, compute1); } => //; 1: smt().
+ by symmetry; call sample; skip => />.
by inline *; wp; rnd; wp; skip => />.
qed.

end section.

import TupleXY. 

op cundup ['a] (s : 'a list) =
  foldr rem s (undup s).
search perm_eq.

lemma size_cundup ['a] (s : 'a list) :
  size (cundup s) = size s - size (undup s).
proof. admitted.

lemma undup_cundup ['a] (s : 'a list) :
  perm_eq (undup s ++ cundup s) s.
admitted.

lemma mem_cundup ['a] (s:'a list) (x:'a) : x \in cundup s => x \in undup s.
admitted.

lemma map_cst ['a 'b] (c:'b) (s:'a list) : map (fun _ => c) s = nseq (size s) c.
proof.
  elim: s => [ | x s hrec] /=; 1: by rewrite nseq0.
  by rewrite addzC nseqS 1:size_ge0 hrec.
qed.

import MUFF.

lemma dfun_djoin d : 
  dfun d = dmap (djoin (map d FT.Support.enum)) (fun l => (fun x => nth zeror l (index x FT.Support.enum))).
proof.
  apply eq_distr => f.
  rewrite dfun1E_djoin dmap1E; apply mu_eq_support => z /supp_djoin [].
  rewrite size_map => hs h_.
  rewrite /(\o) /pred1 eq_iff; split => [-> | <-].
  + apply fun_ext => x; rewrite (nth_map witness).
    + by rewrite index_ge0 index_mem FT.Support.enumP.
    by rewrite nth_index // FT.Support.enumP.
  apply (eq_from_nth zeror); 1: by rewrite size_map hs.
  move=> i hi; rewrite (nth_map witness) 1:hs //= index_uniq 1:hs// FT.Support.enum_uniq.
qed.

lemma perfect_sim xy:
  xy \in wordn (2 * q) =>
 mu dfhash (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy) =
 mu dcompute (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy).
proof.
move => xys.
pose P := (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy).
case: (forall p p', p \in xy => p' \in xy => p.`1 = p'.`1 => p = p'); last first.
+ move=> /negb_forall [p] /= /negb_forall [p'] /= h.
  by do 2! rewrite mu0_false 1:[smt (allP)].
move=> hxy.
pose fxy := fun x => oget (assoc xy x).
pose xs := undup (unzip1 xy) ++ cundup (unzip1 xy).
pose ys := map fxy xs.
have hperm := undup_cundup (unzip1 xy). 
have heq : forall d, mu d P = mu1 (dmap d (fun fr => map fr xs)) ys.
+ move=> d; rewrite dmap1E; apply mu_eq => fr.
  rewrite /(\o) /pred1 eq_iff /P allP /=; split.
  + move=> h; rewrite /ys /xs; apply eq_in_map.
    move=> x; rewrite (perm_eq_mem _ _ hperm).
    move=> ^ => /mapP [p] /= [] /h heq -> hin.
    by have /#:= assocP xy p.`1.
  rewrite /ys => /eq_in_map heq p hp. 
  have : p.`1 \in xs. 
  + by rewrite /xs (perm_eq_mem _ _ hperm) mapP; exists p.
  move=> ^ hin /heq ->; rewrite /fxy; have := assocP xy; smt(mapP).
rewrite (heq dfhash) (heq (dcompute)) /=.
have /= := dsim_dout (undup (unzip1 xy)) (cundup (unzip1 xy)) _ _.
+ by apply undup_uniq.
+ by apply mem_cundup.
rewrite /dout /dfhash dfun_djoin dmap_comp /dv dlist_djoin map_cst /p /FT.Support.card /(\o) /= => <-; congr.
rewrite /dsim /dcompute dmap_comp /genseed.
have heqs : size (undup (unzip1 xy)) + size (cundup (unzip1 xy)) = 2*q.
+ by rewrite size_cundup size_map; smt(wordnP q_ge0).
rewrite heqs; apply eq_dmap_in=> l hl /=.
rewrite /(\o) /compute1 /= -(map_nth_range zeror xs) -map_comp.
by have -> : size xs = 2 * q by rewrite /xs size_cat.
qed.

lemma efficient_sim (A<:AdvRO{-QRO, -LQRO}[main : `{Inf, #H.h : q}]) &m (r : result):
  Pr[ QRO_main(A,QRO).main() @ &m: res = r ] = Pr[ QRO_main(A,LQRO).main() @ &m: res = r ].
proof.
have -> : 
 Pr[ QRO_main(A,QRO).main() @ &m: res = r ] = Pr[QRO_main_D(A).main(dfhash) @ &m : res = r].
   by byequiv=>//; conseq (_: _ ==> ={res})=> //; proc;inline*; sim; auto => />.
move : (dA_split A &m) => dA_split.
elim dA_split => C dA_split.
rewrite (eager_sampling A) (dA_split dfhash r) (dA_split dcompute r).
by apply BRA.eq_big_seq => */=; congr; apply perfect_sim.
qed.

end T_QROM_SIM.

