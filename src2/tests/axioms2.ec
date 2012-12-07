type 'a list.
op length ['a] : 'a list -> int.
op cons ['a] : ('a, 'a list) -> 'a list.

op eq ['a] : ('a,'a) -> bool.
axiom T : forall (la:'a list, lb: 'b list), eq(length(la), length(lb)).
cnst nil ['a] : 'a list.
