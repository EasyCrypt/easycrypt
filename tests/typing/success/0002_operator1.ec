type 'a list.

op nil : 'a list.
op (::)  : 'a -> 'a list -> 'a list.

op length ['a] : 'a list -> int.
op mem    ['a] : 'a -> 'a list -> bool.
