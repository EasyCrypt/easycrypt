(* Extra operators on int *)
op [>] (x,y:int) = y < x as gt_int.
op [>=] (x,y:int) = y <= x as ge_int.

(* Extra operators on real *)
op [>] (x,y:real) = y < x as gt_real.
op [>=] (x,y:real) = y <= x as ge_real.

(* fst and snd *)

op fst (p : 'a * 'b) = 
  let a,b = p in a. 

op snd (p : 'a * 'b) = 
  let a,b = p in b.


(* option *)

axiom Some_inj : 
 forall (x, y : 'a),
  Some(x) = Some(y) => x = y.

op proj : 'a option -> 'a.

axiom Proj_Some : 
 forall (x: 'a),
  proj(Some(x)) = x.

axiom Proj_eq :
  forall (o1, o2: 'a option),
    !(o1 = None) => !(o2 = None) =>
    proj(o1) = proj(o2) =>
    o1 = o2.

axiom Some_or_None :
 forall (o: 'a option),
  o = None || exists (x: 'a), o = Some(x).

(* List *)

op hd : 'a list -> 'a.
op tl : 'a list -> 'a list. 

axiom head_def : 
  forall (a: 'a, l: 'a list),
    hd(a::l) = a.

axiom tail_def : 
  forall (a: 'a, l: 'a list),
    tl(a::l) = l.

(* map *)

cnst empty_map : ('a, 'b) map.

(* We use a trigger *)
axiom get_upd_map_same :
  forall (m: ('a,'b) map, a1, a2 : 'a, b: 'b)[ m[a1<-b][a2] ],
    a1 = a2 => m[a1<-b][a2] = b. 

axiom get_upd_map_diff :
  forall (m:('a,'b) map, a1, a2 : 'a, b: 'b)[ m[a1<-b][a2] ],
    a1 <> a2 => m[a1<-b][a2] = m[a2].

axiom upd_map_comm :
  forall (m:('a,'b) map, a, a':'a, b, b':'b)[ m[a<-b][a'<-b'] ],
    a <> a' => m[a<-b][a'<-b'] = m[a'<-b'][a<-b].

axiom upd_in_dom_same :
  forall (m:('a,'b) map, a, a':'a,b:'b)[in_dom(a', m[a<-b])],
    a = a' => in_dom(a', m[a<-b]).

axiom upd_in_dom_diff :
  forall (m:('a,'b)map, a, a':'a, b:'b)[ in_dom(a',m[a<-b]) ],
    a <> a' => (in_dom(a',m[a<-b]) <=> in_dom(a',m)).

(*lemma in_dom_upd_map : 
   forall (m:('a,'b) map, a, a':'a, b:'b),
     in_dom(a',m[a<-b]) <=> (a = a' || in_dom(a',m)). *)

axiom upd_in_rng_same :
  forall (m:('a,'b) map, a:'a, b, b':'b) [in_rng(b',m[a<-b])],
    b = b' => in_rng(b',m[a<-b]).

axiom upd_in_rng_diff :
  forall (m:('a,'b) map, a:'a, b, b':'b) [in_rng(b',m[a<-b])],
    b <> b' => (in_rng(b',m[a<-b]) <=> in_rng(b',m)).

(*lemma in_rng_upd_or : 
  forall (m: ('a,'b) map, a:'a, b, b':'b)[in_rng(b',m[a<-b])],
    in_rng(b',m[a<-b]) <=> (b=b' || in_rng(b',m)).

unset in_rng_upd_or.*)

axiom in_dom_in_rng : 
 forall (m:('a,'b) map, a:'a) [in_dom(a,m), in_rng(m[a],m) ],
  in_dom(a, m) => in_rng(m[a], m).

axiom in_rng_in_dom :
  forall (m:('a, 'b)map, b:'b),
    in_rng(b, m) => exists (a:'a), in_dom(a, m) && m[a] = b.

axiom empty_in_dom : 
  forall (a:'a) [in_dom(a,empty_map)],
    !in_dom(a, empty_map).

axiom empty_in_rng :
  forall (b:'b)[in_rng(b, empty_map)],
    !in_rng(b, empty_map).


(** real_of_bool *)

axiom real_of_bool_true : real_of_bool(true) = 1%r.
axiom real_of_bool_false : real_of_bool(false) = 0%r.

axiom real_of_int_le_compat : forall (x, y:int),
    x <= y => x%r <= y%r.

axiom real_of_int_lt_compat : forall (x, y:int),
    x < y => x%r < y%r.

axiom (*lemma*) rmult_le_compat_l :
 forall (x, y, z:real), 0%r <= x => y <= z => x * y <= x * z.

axiom (*lemma*) rmult_le_compat_r :
 forall (x, y, z:real), 0%r <= z => x <= y => x * z <= y * z.

axiom (*lemma*) rmul_plus_distr_r : 
 forall (x, y, z:real), (x + y) * z = x * z + y * z.

axiom rdiv_le_compat : forall (x1, x2, y1, y2 :real),
   0%r < y2 => y2 <= y1 => 0%r <= x1 => x1 <= x2 => x1 / y1 <= x2 / y2.

axiom (*lemma*) rdiv_0_le : forall (x, y:real),
   0%r < y => 0%r <= x => 0%r <= x / y. 

axiom pow2_pos : forall (n:int), 0 <= n => 0 < 2^n.
