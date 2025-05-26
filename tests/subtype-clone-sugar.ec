require import AllCore.
require Subtype.

subtype zmod3 =
  { x : int | 0 <= x < 3 }.

realize inhabited. by exists 0. qed.
