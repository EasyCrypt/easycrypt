type t.
type u.

theory T1.

op __abs : t -> t.
op o (x:t) : t = |x|.
op o1 (x:t) : t = __abs(x).

end T1.

theory T2.
op __abs : t -> u.
op o (x:t) : u = |x|.
op o1(x:t) : u = __abs(x).
end T2.
