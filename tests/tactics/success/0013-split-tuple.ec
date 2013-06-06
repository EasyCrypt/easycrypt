require Logic.

lemma foo2 : forall (x1 y1:'a1) (x2 y2:'a2),
   x1 = y1 =>
   x2 = y2 =>
   (x1,x2) = (y1, y2)
proof.
 intros x1 y1 x2 y2 H1 H2.
 split;assumption.
save.

lemma foo4 : forall (x1 y1:'a1) (x2 y2:'a2) (x3 y3:'a3) (x4 y4:'a4),
   x1 = y1 =>
   x2 = y2 =>
   x3 = y3 =>
   x4 = y4 =>
   (x1,x2,x3,x4) = (y1,y2,y3,y4)
proof.
 intros x1 y1 x2 y2 x3 y3 x4 y4 H1 H2 H3 H4.
 split;assumption.
save.
