type t.
type u.

theory T1.

op "`|_|" : t -> t.
op o (x:t) : t = `| x | .
op o1 (x:t) : t = "`|_|" x.

end T1.

theory T2.
op "`|_|" : t -> u.
op o (x:t) : u = `|x|.
op o1(x:t) : u = "`|_|" x.
end T2.
