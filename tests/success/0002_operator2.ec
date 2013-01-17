op foo (x:_, l:_) : _ = x :: <:'a=int> l.
op foo1 (x:_, l:_) : _ = x :: <:int> l.
op foo2 (x:_, y:_) : _ = [<:int> x; y ].
op foo3 (x:_, y:_) : _ = [<:'a=int> x; y ].