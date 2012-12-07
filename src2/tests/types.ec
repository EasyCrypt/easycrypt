theory T1.
  type 'a t.
  print type t.
  type 'a t1 = 'a * int.
  print type t1.
 (* type 'a t2 = 'a * _ .*)
end T1.

theory T2.
  type 'a t = 'a T1:>t.
  print type t.
end T2.

