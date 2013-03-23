require        Map_why.

require import Fun.
require export Option.
require        Set.

(** Type and Core definitions *)
type ('a,'b) map = ('a,'b option) Map_why.map.

(* empty, get and set: note that get returns an option *)
cnst empty:('a,'b) map = Map_why.const None.
op __get(m:('a,'b) map, x:'a): 'b option = Map_why.__get m x.
op __set(m:('a,'b) map, x:'a, y:'b): ('a,'b) map = Map_why.__set m x (Some y).

(* Some basic lemmas *)
lemma get_upd_eq: forall (m:('a,'b) map) x v,
  m.[x <- v].[x] = Some v.

lemma get_upd_neq: forall (m:('a,'b) map) x y v,
  x <> y => m.[x <- v].[y] = m.[y].

lemma get_upd_case: forall (m:('a,'b) map) x y v1 v2,
  (y = x => v1 = v2) =>
  (y <> x => m.[y] = Some v2) =>
  m.[x <- v1].[y] = Some v2.

lemma upd_comm: forall (m : ('a,'b) map) x1 x2 y1 y2,
  x1 <> x2 => m.[x1 <- y1].[x2 <- y2] = m.[x2 <- y2].[x1 <- y1]
proof.
intros m x1 x2 y1 y2 x1_neq_x2;
  cut ext_eq: (forall (a:'a), m.[x1 <- y1].[x2 <- y2].[a] = m.[x2 <- y2].[x1 <- y1].[a]);
  trivial.
save.

(** Formalization of map domain *)
op dom : ('a,'b) map -> 'a Set.set.

axiom dom_def: forall (m:('a,'b) map) x,
  Set.mem x (dom m) <=> m.[x] <> None.

op in_dom(x:'a, m:('a,'b) map): bool = Set.mem x (dom m).

(* Lemma about dom and in_dom *)
lemma upd_in_dom_eq: forall (m:('a,'b) map) x y,
  in_dom x (m.[x<-y]).

lemma upd_in_dom_neq: forall (m:('a,'b) map) x1 x2 y,
  x1 <> x2 => in_dom x2 m.[x1<-y] = in_dom x2 m.

lemma dom_empty: dom (empty<:'a,'b>) = Set.empty.

lemma in_dom_empty: forall x, !in_dom x empty<:'a, 'b>.

lemma dom_update: forall (m:('a,'b) map) x y,
  dom (m.[x <- y]) = Set.add x (dom m)
proof.
intros m x y;
  apply Set.extentionality<:'a> ((dom (m.[x <- y])),(Set.add x (dom m)),_);
  trivial.
save.

(** Formalization of map range *)
op rng: ('a,'b) map -> 'b Set.set.

axiom rng_def: forall (m:('a,'b) map) y,
  Set.mem y (rng m) <=> (exists x, in_dom x m && m.[x] = Some y).

op in_rng(x:'b, m:('a,'b) map): bool = 
 Set.mem x (rng m).

(* Lemmas about range *)
lemma upd_in_rng_eq: forall (m:('a,'b) map) x y1 y2,
  y1 = y2 => in_rng y2 (m.[x<-y1])
proof.
intros m x y1 y2 H;
  cut Hsuff: (Set.mem y2 (rng m.[x<-y2]));[ idtac | trivial ].
  cut Hsuff: (in_dom x m.[x<-y2] && m.[x<-y2].[x] = Some y2);trivial.
save.

lemma in_dom_in_rng: forall (m:('a,'b) map) x,
  in_dom x m => in_rng (proj m.[x]) m
proof.
intros m x Hdom;
cut Hsuff: (Set.mem (proj m.[x]) (rng m));[ idtac | trivial ].
  cut Hsuff: (exists x', in_dom x' m /\ m.[x] = Some (proj(m.[x'])));[ trivial | idtac ].
  cut A: ((exists x', in_dom x' m /\ proj (m.[x]) = proj (m.[x'])) =>
          Set.mem (proj m.[x]) (rng m));trivial.
save.

lemma upd_in_rng_neq: forall (m:('a,'b) map) x y1 y2,
  in_rng y1 m =>
  (!in_dom x m \/ m.[x] <> Some y1) =>
  in_rng y1 m.[x<-y2]
proof.
intros m x y1 y2 Hinrng Hor;
cut Hleft: (!in_dom x m  => in_rng y1 m.[x<-y2]).
  intros H;cut Hex: (exists x, in_dom x m /\ m.[x] = Some y1).
    trivial.
    elim Hex;intros x' Heq;cut Hneq: (x' <> x).
      trivial.
      cut Hsuff: (Set.mem y1 (rng m.[x <- y2])).
        cut Hsuff: (exists x', in_dom x' m.[x<-y2] /\ m.[x<-y2].[x'] = Some y1).
          trivial.
          cut Hrngdef: ((exists x', in_dom x' m.[x<- y2] /\ m.[x<-y2].[x'] = Some y1) => 
                        Set.mem y1 (rng m.[x<-y2])).
            trivial.
            apply Hrngdef<:'a>(_);trivial.
        trivial.
cut Hright: (m.[x] <> Some y1 => in_rng y1 m.[x<-y2]).
  cut Hex: (exists x, in_dom x m /\ m.[x] = Some y1).
    trivial.
    elim Hex;intros x' Heq;cut Hneq: (x' <> x).
      trivial.
      cut Hsuff: (Set.mem y1 (rng m.[x <- y2])).
        cut Hsuff: (exists x', in_dom x' m.[x<-y2] /\ m.[x<-y2].[x'] = Some y1).
          trivial.
          cut Hrngdef: ((exists x', in_dom x' m.[x<- y2] /\ m.[x<-y2].[x'] = Some y1) => 
                        Set.mem y1 (rng m.[x<-y2])).
            trivial.
            apply Hrngdef<:'a>(_);trivial.
  trivial.
trivial.
save.

lemma rng_empty: rng (empty<:'a,'b>) = Set.empty
proof.
apply Set.extentionality<:'b> ((rng empty<:'a,'b>),Set.empty,_);
  trivial.
save.

lemma in_rng_empty: forall x, !in_rng x empty<:'a, 'b>.

lemma rng_update_not_indom: forall (m:('a,'b) map) x y,
  !in_dom x m => rng (m.[x <- y]) = Set.add y (rng m)
proof.
intros m x y H;
apply Set.extentionality<:'b> ((rng (m.[x <- y])),(Set.add y (rng m)),_);
cut Hsuff: ((forall y', Set.mem y' (rng (m.[x <- y])) =>
               Set.mem y' (Set.add y (rng m))) /\
            (forall y', Set.mem y' (Set.add y (rng m)) =>
               Set.mem y' (rng (m.[x <- y]))));[ split;[ idtac | trivial ] | trivial ].
intros y';cut case_y_y': (y = y' \/ y <> y');[ trivial | elim case_y_y';[ trivial | idtac ]].
intros y_neq_y' y'_in_rng;
  cut y'_in_rng_m: (Set.mem y' (rng m));
  cut Hdom: (exists x', in_dom x' m /\ m.[x'] = Some y');
  trivial.
save.

(** find *) (* TODO: the axiomatization appears to be upside-down *)
op find: ('a * 'b) cPred -> ('a,'b) map -> 'a option.

axiom find_none1: forall (P:('a * 'b) cPred) m,
  find P m = None =>
  (forall x, in_dom x m => !P (x,proj (m.[x]))).

lemma find_none1_aux: forall (P:('a * 'b) cPred) m x,
  find P m = None =>
  in_dom x m => !P (x,proj (m.[x])).

axiom find_none2: forall (P:('a * 'b) cPred) m,
  (forall x, in_dom x m => !P (x,proj (m.[x]))) =>
  find P m = None.

axiom find_some1: forall (P:('a * 'b) cPred) m x,
  find P m = Some x =>
  in_dom x m /\ P (x,proj (m.[x])).

axiom find_some2: forall (P:('a * 'b) cPred) m x1,
  (in_dom x1 m /\ P (x1,proj (m.[x1]))) =>
  (exists x2, find P m = Some x2).

(* Lemmas *)
lemma find_empty: forall P,
  find<:'a,'b> P empty = None.

lemma find_some_upd1: forall (P:('a * 'b) cPred) m x y, 
  find P m <> None => !in_dom x m =>
  find P m.[x<-y] <> None
proof.
intros P m x y H H0;
cut H1: (find P m.[x<-y] = None => false).
  intros Hfnone;cut H1: (find P m = None).
    apply find_none2<:'a,'b>(P,m,_).
      intros z Hz;cut Heq: (z = x => !P (z, proj m.[z])).
        trivial.
        cut Hneq: (z <> x => !P (z, proj m.[z]));trivial.
      trivial.
  trivial.
save.

lemma find_some_upd2: forall (P:('a * 'b) cPred) m x y, 
  P (x,y) => find P m.[x <- y] <> None.

lemma find_some_upd3: forall (P:('a * 'b) cPred) m x y, 
  find P m <> None =>
  find P m <> Some x =>
  find P m.[x <- y] <> None
proof.
intros P m x y H H0;cut H1: (exists v, find P m = Some v).
  trivial.
  elim H1;intros v Hfind_v;cut H3: (exists v, find P m.[x<-y] = Some v).
    apply find_some2<:'a,'b>(P,m.[x<-y],v,_);trivial.
  trivial.
save.

lemma find_none_upd1: forall (P:('a * 'b) cPred) m x y,
  find P m = None =>
  !P (x,y) =>
  find P m.[x<-y] = None.

lemma find_none_upd2: forall (P:('a * 'b) cPred) m x y,
  find P m = None =>
  P (x,y) = true =>
  find P m.[x<-y] = Some x
proof.
intros P m x y H H1;cut Hnone: (forall x', in_dom x' m => !P (x',proj m.[x'])).
  intros x' Hxindom;trivial.
  cut Hsuff: (exists x', find P m.[x<-y] = Some x').
    trivial.
    elim Hsuff;intros x' Hfind;cut Hindom: (in_dom x' m.[x<-y]). 
      trivial. 
      cut HP: (P (x',proj m.[x<-y].[x']) = true).
        trivial.
        cut Hor: (x = x' \/ in_dom x' m).
          trivial.
          elim Hor;intros Heq;trivial.
save.

(** remove *)
op rm (x:'a,m:('a,'b) map): ('a,'b) map =
 Map_why.__set m x None.

(* Lemma *)
lemma rm_not_in_dom: forall (m:('a,'b) map) x, !in_dom x (rm x m).

lemma rm_upd: forall (m:('a,'b) map) x, !in_dom x m => rm x m = m.

lemma rm_rest_dom: forall x y (m:('a,'b) map),
  x <> y => in_dom y (rm x m) = in_dom y m.

lemma rm_val: forall x y (m:('a,'b) map),
  x <> y => in_dom y m =>
  m.[y] = (rm x m).[y].

lemma rm_find: forall (P:('a * 'b) cPred) m x y,
  find P m = Some y => x <> y =>
  find P (rm x m) <> None
proof.
intros P m x y Hfind Hneq;
cut H: (in_dom y m /\ P (y,proj (m.[y])) = true).
  trivial.
  cut H': (in_dom y (rm x m) /\ P (y,proj ((rm x m).[y])) = true);trivial.
save.

(** extentional equality *)
pred [==] (m1 m2:('a,'b) map) = 
  (forall x, in_dom x m1 <=> in_dom x m2) &&
  (forall x, in_dom x m1 => m1.[x] = m2.[x]).

axiom extentionality: forall (m1 m2:('a,'b) map),
  m1 == m2 => m1 = m2.

(** equal except *)
pred eq_except(m1 m2:('a,'b) map, x) =
  rm x m1 = rm x m2.

lemma eqe_symm: forall (m1 m2:('a,'b) map) x,
  eq_except m1 m2 x = eq_except m2 m1 x.

lemma eqe_trans: forall (m1 m2 m3:('a,'b) map) x,
  eq_except m1 m2 x =>
  eq_except m2 m3 x =>
  eq_except m1 m3 x.

lemma eqe_sym: forall (m:('a,'b) map) x,
  eq_except m m x.

lemma eqe_update_diff: forall (m1 m2:('a,'b) map) x1 x2 y,
  eq_except m1 m2 x1 => 
  eq_except m1.[x2 <- y] m2.[x2 <- y]  x1.

lemma eqe_update_same: forall (m1 m2:('a,'b) map) x y,
  eq_except m1 m2 x => eq_except m1.[x<-y] m2 x.

lemma eq_except_eq: forall (m1 m2:('a,'b) map) x z,
  eq_except m1 m2 x => in_dom x m1 =>
  m1.[x] = Some z =>
  m1 = m2.[x <- z].

(* Alternative Definition *)
lemma eq_except_def: forall (m1 m2:('a,'b) map) x,
  in_dom x m2 =>
  eq_except m1 m2 x =>
  exists z, m1.[x<-z] = m2
proof.
intros m1 m2 x x_in_dom_m2 m1_eq_except_m2_x;
cut H: (exists z, m2.[x] = Some z);[ trivial | idtac ].
elim H;intros z m2_z.
cut eq_except: (m2 = m1.[x <- z]);[ idtac | trivial ].
apply eq_except_eq<:'a,'b> (m2,m1,x,z,_,_,_);trivial.
save.

(** Disjointness of maps *)
pred disj(m1 m2:('a,'b) map) = forall x,
  !in_dom x m1 \/ !in_dom x m2.

lemma disj_comm: forall (m1 m2:('a,'b) map),
  disj m1 m2 <=> disj m2 m1.

lemma disj_empty: forall (m:('a,'b) map),
  disj m empty.

lemma disj_upd: forall (m1 m2:('a,'b) map) x y,
  disj m1 m2 => !in_dom x m1 =>
  disj m1 m2.[x<-y].

lemma disj_rm: forall (m1 m2:('a,'b) map) x,
  disj m1 m2 => disj (rm x m1) m2.

(** Split a map in two maps *)
pred split_map(m m1 m2:('a,'b) map) =
 disj m1 m2 &&
 (forall x, in_dom x m <=> (in_dom x m1 \/ in_dom x m2)) &&
 (forall x, in_dom x m1 => m.[x] = m1.[x]) &&
 (forall x, in_dom x m2 => m.[x] = m2.[x]).

lemma split_map_empty: forall (m:('a,'b) map),
  split_map m m empty.

lemma split_map_comm: forall (m m1 m2:('a,'b) map),
  split_map m m1 m2 = split_map m m2 m1. 

lemma split_map_upd: forall (m m1 m2:('a,'b) map) x y,
 split_map m m1 m2 =>
 !in_dom x m2 =>
 split_map m.[x<-y] m1.[x<-y] m2.

lemma split_map_rm: forall (m m1 m2:('a,'b) map) x,
 split_map m m1 m2 => 
 !in_dom x m2 => 
 split_map (rm x m) (rm x m1) m2.



