lemma L1 : true by [].
lemma L2 : !false by [].
lemma L3 : forall (b:_), b || !b by [].
lemma L4 : forall (x:'a), x = x by [].
lemma L5 : forall (b:bool), (if b then true else false) = b by [].
lemma L6 : forall (b:bool), if b then b else !b by [].
lemma L7 : forall (b:_, x:int), (if b then x else x) = x by []. 

type t.
lemma L8 : forall (x:t * t, y : t * t), 
  let (x1,x2) = x in
  let (y1,y2) = y in
  x1 = y1 => x2 = y2 => x = y
by [].

pred A.
lemma L9 : A || !A by [].
lemma L10 : if A then A else !A by [].
lemma L11 : (if A then A else !A) = true by [].
