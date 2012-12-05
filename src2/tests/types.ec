theory T1.
  type 'a t.
  type 'a t1 = 'a * int.
 (* type 'a t2 = 'a * _ .*)
end T1.

theory T2.
  type 'a t = 'a T1:>t.
end T2.

