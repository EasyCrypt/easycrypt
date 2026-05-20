require import AllCore.
require Subtype.

subtype zmod3 =
  { x : int | 0 <= x < 3 }.

realize inhabited. by exists 0. qed.

op a: 'a.
subtype uses_thole as ST1 =
  { x : int | a<:bool> = a<:_> }.
realize inhabited by done.

fail subtype tvar_carrier as ST2 =
  { x : 'a | true }.

fail subtype tvar_prop as ST3 =
  { x : int | a<:'a> = a<:_> }.
