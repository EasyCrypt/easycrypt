(** We add array, this will be removed in the futur *)
type 'a array.
op length : 'a array -> int.
op make : (int,'a) -> 'a array. 
op [~>] : ('a array, int) -> 'a  as aget.
op [<~] : ('a array, int * 'a) -> 'a array as aset.

axiom length_pos : forall (t:'a array),  0 <= length(t).

axiom aget_aset_same : forall (t : 'a array, i:int, a:'a),
   0<= i => i < length(t) => (t <~(i,a)) ~> i = a.

axiom aget_aset_diff : forall (t : 'a array, i,j:int, a:'a),
   i <> j => ((t <~(i,a)) ~> j) = (t ~> j).

axiom length_make : forall (a:'a, len:int),
  0 <= len => length(make(len,a)) = len.

axiom length_upd :  forall (t : 'a array, i:int, a:'a),
  length(t <~(i,a)) = length(t).


(* Misc *)

pred bounded(x,y,z:int) = x <= y && y <= z.

lemma mult_le_compat_l : forall (x1,x2,y1:int),
    bounded(0,x1,x2) => 0 <= y1 =>
    x1 * y1 <= x2 * y1.

lemma mult_le_compat_r: forall (x2,y1,y2:int),
    0 <= x2 => bounded(0,y1,y2) =>
    x2 * y1 <= x2 * y2.

lemma mult_le_compat : forall (x1,x2,y1,y2:int),
    bounded(0,x1,x2) =>
    bounded(0,y1,y2) => 
    x1 * y1 <= x2 * y2.
 
lemma square_le_compat : forall (x,y:int),
    bounded(0, x, y) =>
    x^2 <= y^2. 
