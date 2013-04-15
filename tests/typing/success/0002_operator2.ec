type 'a list.
op __nil ['a] : 'a list.
op (::) ['a] : 'a -> 'a list -> 'a list.

op foo  x l = x :: <:'a=int> l.
op foo1 x l = x :: <:int> l.
op foo2 x y = [<:int> x; y ].
op foo3 x y = [<:'a=int> x; y ].
