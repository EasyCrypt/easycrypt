theory T1.
  type 'a t.
  op o : 'a T1.t -> 'a t.
end T1.

theory T2.
  export T1.
end T2.

theory T3.
  import T2.

  op o1 (x:'a T1.t) : _ = o(o(x)).
  op o (x:'a T1.t) : 'a T1.t = T1.o(o(x)).
end T3.
