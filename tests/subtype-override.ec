require Subtype.

theory T1.
  subtype s = {b: bool | b}.
  realize inhabited by exists true.
end T1.

subtype s = {b: bool | !b}.
realize inhabited by exists false.

fail clone T1 as T2 with
type s   <- s,
op insub <- insub,
op val   <- val
proof *.
