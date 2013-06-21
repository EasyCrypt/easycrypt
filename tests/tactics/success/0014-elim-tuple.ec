lemma foo2 : forall (x1 y1:'a1) (x2 y2:'a2),
   (x1,x2) = (y1, y2) => x2 = y2.
 intros a b c d h.
 elim h;split.
save.

lemma foo20 :
  forall
    (x1 y1:'a1) (x2 y2:'a2) (x3 y3:'a3) (x4 y4:'a4) (x5 y5:'a5)
    (x6 y6:'a6) (x7 y7:'a7) (x8 y8:'a8) (x9 y9:'a9) (x10 y10:'a10)
    (x11 y11:'a11) (x12 y12:'a12) (x13 y13:'a13) (x14 y14:'a14) (x15 y15:'a15)
    (x16 y16:'a16) (x17 y17:'a17) (x18 y18:'a18) (x19 y19:'a19) (x20 y20:'a20),
      (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) =
      (y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19,y20) =>
         x20 = y20.
 intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.
 elim h;split.
save.
