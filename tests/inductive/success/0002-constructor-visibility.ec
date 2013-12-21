theory Option.
  type 'a option = [
    | None
    | Some of 'a
  ].
end Option.

import Option.

op some (x:'a) = Some x.
