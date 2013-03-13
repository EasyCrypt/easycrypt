require map_why.

require import Fun.
require import option.
require Set.

type ('a, 'b) map = ('a, 'b option) map_why.map.

cnst empty : ('a,'b) map = map_why.const None.
op __get(m : ('a,'b) map, x : 'a) : 'b option = map_why.__get m x.
op __set(m : ('a,'b) map, x : 'a, y : 'b) : ('a,'b) map = map_why.__set m x (Some y).

lemma get_upd_eq : forall (m : ('a,'b) map,x : 'a, y: 'a, v : 'b),
x = y => proj (m.[x <- v].[y]) = v.

lemma get_upd_neq : forall (m : ('a,'b) map,x : 'a, y: 'a, v : 'b),
x <> y => m.[x <- v].[y] = m.[y].

lemma get_upd_case : forall (m : ('a,'b) map,x : 'a, y: 'a, v1 : 'b, v2 : 'b),
(y = x => v1 = v2) =>
(y <> x => v2 = proj (m.[y])) =>
proj (m.[x <- v1].[y]) = v2.

lemma upd_comm : forall (m : ('a,'b) map, x1 : 'a, x2: 'a, y1 : 'b, y2 : 'b),
x1 <> x2 =>  m.[x1<-y1].[x2<-y2] = m.[x2<-y2].[x1<-y1].

op dom ['a 'b] : ('a,'b) map -> 'a Set.t.

axiom dom_def : 
 forall (x:'a, m : ('a,'b) map), 
 Set.mem x (dom m) <=> m.[x] <> None.

op in_dom (x:'a, m:('a,'b) map) : bool = 
  Set.mem x (dom m).
 
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

op find : ('a * 'b) Pred -> ('a,'b) map -> 'a option.

axiom find1 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map),
 find P m = None <=> (forall(x : 'a), in_dom x m => !P((x,proj(m.[x])))).

axiom find2 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map, x : 'a, y : 'b),
 find P m = Some x => (in_dom x m && P(x,proj(m.[x]))).

axiom find3 : forall(P : ('a * 'b) Pred, m : ('a, 'b) map, x1 : 'a),
 (in_dom x1 m && P(x1,proj(m.[x1]))) => (exists(x2:'a), find P m = Some x2). 

 lemma find_empty : forall(P : ('a * 'b) Pred), 
  find<:'a,'b> P empty = None.
