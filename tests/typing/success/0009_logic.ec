lemma L1 : true.
lemma L2 : !false.
lemma L3 : forall (b:_), b || !b.
lemma L4 : forall (x:'a), x = x.
lemma L5 : forall (b:bool), (if b then true else false) = b.
lemma L6 : forall (b:bool), if b then b else !b.
lemma L7 : forall (b:_, x:int), (if b then x else x) = x. 

type t.
lemma L8 : forall (x:t * t, y : t * t), 
  let (x1,x2) = x in
  let (y1,y2) = y in
  x1 = y1 => x2 = y2 => x = y.

pred A.
lemma L9 : A || !A.
lemma L10 : if A then A else !A.
lemma L11 : (if A then A else !A) = true.

