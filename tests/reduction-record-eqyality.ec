require import AllCore.

type t = { x: int; y: int }.

lemma L x y :
  x = 0 => y = 1 => {| x = x; y = y |} = {| x = 0; y = 1 |}.
proof. move=> xE yE /=; split; assumption. qed.
