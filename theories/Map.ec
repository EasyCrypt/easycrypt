require Map_why.

require import Fun.
require export Option.
require        Set.

type ('a, 'b) map = ('a, 'b option) Map_why.map.

 (* empty map, get and set *)
cnst empty : ('a,'b) map = Map_why.const None.
op __get(m : ('a,'b) map, x : 'a) : 'b option = Map_why.__get m x.
op __set(m : ('a,'b) map, x : 'a, y : 'b) : ('a,'b) map = Map_why.__set m x (Some y).

 (* basic facts *)
lemma get_upd_eq : forall (m : ('a,'b) map,x : 'a, y: 'a, v : 'b),
x = y => proj (m.[x <- v].[y]) = v.

lemma get_upd_neq : forall (m : ('a,'b) map,x : 'a, y: 'a, v : 'b),
 x <> y => m.[x <- v].[y] = m.[y].

lemma get_upd_case : forall (m : ('a,'b) map,x : 'a, y: 'a, v1 : 'b, v2 : 'b),
(y = x => v1 = v2) =>
(y <> x => v2 = proj (m.[y])) =>
 proj (m.[x <- v1].[y]) = v2.

lemma upd_comm : forall (m : ('a,'b) map, x1 : 'a, x2: 'a, y1 : 'b, y2 : 'b),
 x1 <> x2 =>  m.[x1 <- y1].[x2 <- y2] = m.[x2 <- y2].[x1 <- y1]
proof.
intros m x1 x2 y1 y2 x1_neq_x2;
  cut ext_eq: (forall (a:'a), m.[x1 <- y1].[x2 <- y2].[a] = m.[x2 <- y2].[x1 <- y1].[a]);
  trivial.
save.

 (* domain operator *)
op dom ['a 'b] : ('a,'b) map -> 'a Set.t.

op in_dom (x:'a, m:('a,'b) map) : bool = 
 Set.mem x (dom m).

 (* axiomatization *)
axiom dom_def : 
 forall (x:'a, m : ('a,'b) map), 
 Set.mem x (dom m) <=> m.[x] <> None.

 (* facts about dom *)
lemma upd_in_dom_eq : forall (m:('a,'b) map, x1 : 'a, x2:'a, y:'b),
x1 = x2 => in_dom x2  m.[x1<-y].

lemma upd_in_dom_neq : forall (m:('a,'b) map, x1 : 'a, x2:'a, y:'b),
 x1 <> x2 => in_dom x2  m.[x1<-y] = in_dom x2 m.

lemma dom_empty : dom (empty<:'a,'b>) = Set.empty.

lemma in_dom_empty : forall(x : 'a), !in_dom x empty<:'a, 'b>.

lemma dom_update : forall(m : ('a,'b) map, x : 'a, y : 'b),
 dom (m.[x <- y]) = Set.add x (dom m)
proof.
 intros m x y.
 cut H: (Set.ext_eq (dom (m.[x <- y]))  (Set.add x (dom m))).
 trivial.
 trivial.
save.

  (* rng operator *)
op rng ['a 'b] : ('a,'b) map -> 'b Set.t.

op in_rng (x:'b, m:('a,'b) map) : bool = 
 Set.mem x (rng m).

 (* axiomatization *)
axiom rng_def : 
 forall (y:'b, m : ('a,'b) map), 
 Set.mem y (rng m) <=> (exists (x : 'a), in_dom x m && m.[x] = Some y).

 (*facts about range *)
lemma upd_in_rng_eq : forall (m:('a,'b) map, x: 'a, y1:'b, y2:'b),
y1 = y2 => in_rng y2  m.[x<-y1]
proof.
 intros m x y1 y2 H.
 cut Hsuff: (Set.mem y2 (rng m.[x<-y2])).
 cut Hsuff: (in_dom x m.[x<-y2] && m.[x<-y2].[x] = Some y2);trivial.
 trivial.
save.

lemma in_dom_in_rng : 
 forall (m:('a,'b) map, x:'a),
in_dom x m => in_rng (proj m.[x]) m
proof.
 intros m x Hdom.
 cut Hsuff: (Set.mem (proj m.[x]) (rng m)).
 cut Hsuff: (exists (x' : 'a), in_dom x' m && (m.[x]) = Some (proj(m.[x']))).
 trivial.
 cut A: ((exists (x' : 'a), in_dom x' m && proj(m.[x]) = proj(m.[x'])) =>
 (Set.mem (proj m.[x]) (rng m))).
  trivial.
  trivial.
  trivial.
save.

lemma upd_in_rng_neq : forall (m:('a,'b) map, x: 'a, y1:'b, y2:'b),
in_rng y1 m => (!in_dom x m || m.[x] <> Some y1) => in_rng y1 m.[x<-y2]
proof.
 intros m x y1 y2 Hinrng Hor.
 cut Hleft: (!in_dom x m  => in_rng y1 m.[x<-y2]).
 intros H.
 cut Hex: (exists (x : 'a), in_dom x m && m.[x] = Some y1).
 trivial.
 elim Hex.
 intros x' Heq.
 cut Hneq:  (x' <> x).
 trivial.
 cut Hsuff: (Set.mem y1 (rng m.[x <- y2])).
 cut Hsuff: (exists (x' : 'a),(in_dom x' m.[x<-y2] && proj(m.[x<-y2].[x']) = y1)).
 trivial.
 cut Hrngdef: 
((exists (x' : 'a), in_dom x' m.[x<- y2] && m.[x<-y2].[x'] = Some y1) => 
 Set.mem y1 (rng m.[x<-y2])).
 trivial.
 apply Hrngdef<:'a>(_).
 trivial.
 trivial.
 cut Hright: (m.[x] <> Some y1  => in_rng y1 m.[x<-y2]).
 cut Hex: (exists (x : 'a), in_dom x m && m.[x] = Some y1).
 trivial.
 elim Hex.
 intros x' Heq.
 cut Hneq:  (x' <> x).
 trivial.
 cut Hsuff: (Set.mem y1 (rng m.[x <- y2])).
 cut Hsuff: (exists (x' : 'a),(in_dom x' m.[x<-y2] && proj(m.[x<-y2].[x']) = y1)).
 trivial.
 cut Hrngdef: 
((exists (x' : 'a), in_dom x' m.[x<- y2] && m.[x<-y2].[x'] = Some y1) => 
 Set.mem y1 (rng m.[x<-y2])).
 trivial.
 apply Hrngdef<:'a>(_).
 trivial.
 trivial.
 trivial.
save.

lemma rng_empty : rng (empty<:'a,'b>) = Set.empty
proof.
 cut H: (Set.ext_eq (rng (empty<:'a,'b>)) Set.empty).
 trivial.
 trivial.
save.

lemma in_rng_empty : forall(x : 'b), !in_rng x empty<:'a, 'b>.

lemma rng_update_not_indom : forall(m : ('a,'b) map, x : 'a, y : 'b),
 !in_dom x m =>
 rng (m.[x <- y]) = Set.add y (rng m)
proof.
 intros m x y H.
 cut H0: (Set.ext_eq (rng (m.[x <- y])) (Set.add y (rng m))).
 cut Hsuff : ((forall (y' : 'b), Set.mem y' (rng (m.[x <- y])) =>
 Set.mem y' (Set.add y (rng m))) &&
 (forall (y' : 'b), Set.mem y' (Set.add y (rng m)) =>
  Set.mem y' (rng (m.[x <- y])))).
  split.
  intros y' Hy'.
  cut Hrngdef :
((exists (x' : 'a), in_dom x' m.[x<- y] && m.[x<-y].[x'] = Some y')).
 trivial.
 elim Hrngdef.
 intros x' Hin_dom_get_eq.
 trivial.
 intros y' Hy'.
 cut Hinvmem: (y' = y || Set.mem y' (rng m)).
 trivial.
 cut Hleft: ( Set.mem y' (rng m) => Set.mem y' (rng m.[x<-y])).
 intros Hmem. 
 cut Hsuff: (in_rng y' m.[x<-y]).
 trivial.
 trivial.
 cut Hright: (y' =  y => Set.mem y' (rng m.[x<-y])).
 intros Heq.
 cut Hsuff: (in_rng y' (m.[x<-y]));trivial.
 trivial.
 trivial.
 trivial.
save.

  (* find operator *)
op find : ('a * 'b) Pred -> ('a,'b) map -> 'a option.

 (* axiomatization *)
axiom find_none1 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map),
find P m = None => (forall(x : 'a), in_dom x m => !P((x,proj(m.[x])))).

lemma find_none1_aux : forall(P : ('a * 'b) Pred, m : ('a, 'b) map, x :'a),
find P m = None => in_dom x m => !P((x,proj(m.[x]))).

axiom find_none2 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map),
(forall(x : 'a), in_dom x m => !P((x,proj(m.[x])))) => find P m = None.

axiom find_some1 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map, x : 'a, y : 'b),
find P m = Some x => (in_dom x m && P(x,proj(m.[x]))).

axiom find_some2 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map, x1 : 'a),
(in_dom x1 m && P(x1,proj(m.[x1]))) => (exists(x2:'a), find P m = Some x2).

 (* some derived facts *)
lemma find_empty : forall(P : ('a * 'b) Pred), 
 find<:'a,'b> P empty = None.

lemma find_some_upd1 : 
 forall(P : ('a * 'b) Pred,m : ('a, 'b) map, x : 'a, y : 'b), 
 find P m <> None => !in_dom x m => find P m.[x<-y] <> None
proof.
 intros P m x y H H0.
 cut H1: (find P m.[x<-y] = None => false).
 intros Hfnone.
 cut H1: (find P m = None).
 apply find_none2<:'a,'b>(P,m,_).
 intros z Hz.
 cut Heq : (z = x => !P((z, proj m.[z]))).
 trivial.
 cut Hneq : (z <> x => !P((z, proj m.[z]))).
 trivial.
 trivial.
 trivial.
 trivial.
save.

lemma find_some_upd2 : 
 forall(P : ('a * 'b) Pred,m : ('a, 'b) map, x : 'a, y : 'b), 
P(x,y) => find P m.[x<-y] <> None.

lemma find_some_upd3 : 
 forall(P : ('a * 'b) Pred,m : ('a, 'b) map, x : 'a, y : 'b), 
 find P m <> None => proj(find P m) <> x  => find P m.[x<-y] <> None
proof.
 intros P m x y H H0.
 cut H1 : (exists (v: 'a), find P m = Some v).
 trivial.
 elim H1.
 intros v Hfind_v.
 cut H3 : (exists (v: 'a), find P m.[x<-y] = Some v).
 apply find_some2<:'a,'b>(P,m.[x<-y],v,_).
 trivial.
 trivial.
save.

lemma find_none_upd1 : 
 forall(P : ('a * 'b) Pred,m : ('a, 'b) map, x : 'a, y : 'b),
find P m = None => !P(x,y) =>  find P m.[x<-y] = None.

lemma find_none_upd2 :
 forall(P : ('a * 'b) Pred,m : ('a, 'b) map, x : 'a, y : 'b),
find P m = None => P(x,y) = true  =>  find P m.[x<-y] = Some x
proof.
intros P m x y H H1.
cut Hnone : (forall (x' : 'a), in_dom x' m => !P(x',proj m.[x'])).
intros x' Hxindom.
trivial.
cut Hsuff:
 (exists (x' : 'a), find P m.[x<-y] = Some x').
trivial.
elim Hsuff.
intros x' Hfind.
cut Hindom : (in_dom x' m.[x<-y]). 
trivial. 
cut HP : (P(x',proj m.[x<-y].[x']) = true).
trivial.
cut Hor: (x = x' || (x<>x' && in_dom x' m)).
trivial.
elim Hor;intros Heq.
trivial.
cut Habs: (P(x',proj (m.[x])) = true).
trivial.
trivial.
save.

(* remove operator *)
op rm (x: 'a,m :('a,'b) map) : ('a,'b) map =
 Map_why.__set m x None.

(* facts about remove *)
lemma rm_not_in_dom : forall(m :('a,'b) map, x: 'a), !in_dom x (rm x m).

lemma rm_upd : forall(m :('a,'b) map,x : 'a), ! in_dom x m => rm x m = m.

lemma rm_rest_dom : forall(x y : 'a)(m : ('a,'b) map),
  x <> y =>
  in_dom y (rm x m) = in_dom y m.

lemma rm_val : forall(x y : 'a)(m : ('a,'b) map),
  x <> y =>
  in_dom y m =>
  m.[y] = (rm x m).[y].

lemma rm_find : forall(P : ('a * 'b) Pred, m : ('a,'b) map)(x y : 'a),
find P m = Some y =>
 x <> y =>
 find P (rm x m) <> None
proof.
 intros P m x y Hfind Hneq.
 cut H: (in_dom y m && P(y,proj(m.[y])) = true).
 trivial.
 cut H' : (in_dom y (rm x m) && P(y,proj((rm x m).[y])) = true).
 trivial.
 trivial.
save.

(* extensional equality *)
pred [==] (m1 m2 : ('a,'b) map) = 
  (forall (x : 'a), in_dom x m1 <=> in_dom x m2) &&
  (forall (x : 'a), in_dom x m1 => m1.[x] = m2.[x]).

axiom extensionality : forall (m1 m2 : ('a,'b) map),
 m1 == m2 => m1 = m2.

(* equal except *)
pred eq_except(m1 m2 : ('a,'b) map, x : 'a) =
rm x m1 = rm x m2.

lemma eqe_symm :
  forall(m1 m2 : ('a, 'b) map)(x : 'a),
  eq_except m1 m2 x =  eq_except m2 m1 x.


lemma eqe_trans :
  forall(m1 m2 m3: ('a, 'b) map)(x : 'a),
  eq_except m1 m2 x =>  
  eq_except m2 m3 x =>
  eq_except m1 m3 x.

lemma eqe_sym :
  forall(m : ('a, 'b) map)(x : 'a),
  eq_except m m x.

lemma eqe_update_diff :
  forall(m1 m2 : ('a, 'b) map)(x1 x2: 'a)( y : 'b),
    eq_except m1 m2 x1 => 
    eq_except m1.[x2 <- y] m2.[x2 <- y]  x1.

lemma eqe_update_same :
 forall(m1 m2 : ('a, 'b) map)(x : 'a, y : 'b),
    eq_except m1 m2 x => eq_except m1.[x<-y] m2 x.

lemma eq_except_eq : 
   forall (m1 m2:('a,'b)map)(x:'a, z:'b),
   eq_except m1 m2 x =>
   in_dom x m1 =>
   m1.[x] = Some z =>
   m1 = m2.[x <- z].

(* alternative definition *)
lemma eq_except_def : forall (m1 m2 : ('a,'b) map)(x : 'a),
in_dom x m2 =>
eq_except m1 m2 x =>
exists(z : 'b), m1.[x<-z] = m2.


(* Disjointness of maps *)

pred disj(m1 m2 : ('a,'b) map) = 
  (forall (x : 'a), !in_dom x m1 || !in_dom x m2).

lemma disj_comm : forall (m1 m2 : ('a,'b) map), disj m1 m2 <=> disj m2 m1.

lemma disj_empty: forall(m : ('a,'b) map), disj m empty.

lemma disj_upd : forall(m1 m2 : ('a,'b) map)( x : 'a, y : 'b),
disj m1 m2 => !in_dom x m1 => disj m1 m2.[x<-y].

lemma disj_rm :forall(m1 m2 : ('a,'b) map)( x : 'a),
disj m1 m2 => disj (rm x m1) m2.

(* Split a map in two maps *)

pred split_map(m m1 m2 : ('a,'b) map) =
 disj m1 m2 &&
 (forall (x : 'a), in_dom x m <=> (in_dom x m1 || in_dom x m2)) &&
 (forall (x : 'a), in_dom x m1 => m.[x] = m1.[x]) &&
 (forall (x : 'a), in_dom x m2 => m.[x] = m2.[x]).

lemma split_map_empty : forall (m : ('a,'b) map)(x : 'a),
 split_map m m empty.

lemma split_map_comm : forall (m m1 m2 : ('a,'b) map)(x : 'a, y :'b),
 split_map m m1 m2 = split_map m m2 m1. 

lemma split_map_upd : forall (m m1 m2 : ('a,'b) map)(x : 'a, y :'b),
 split_map m m1 m2 => 
 !in_dom x m2=> 
 split_map m.[x<-y] m1.[x<-y] m2.

lemma split_map_rm : forall (m m1 m2 : ('a,'b) map)(x : 'a),
 split_map m m1 m2 => 
 !in_dom x m2 => 
 split_map (rm x m) (rm x m1) m2.



