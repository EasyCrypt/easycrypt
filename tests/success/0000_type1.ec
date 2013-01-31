type ('a,'b) t2 = 'a -> 'b.

type ('a,'b,'c) t3 = 'a -> 'b -> 'c.

type ('a,'b,'c) t4 = 'a -> ('b -> 'c).

type ('a,'b,'c) t5 = ('a -> 'b) -> 'c.

type ('a,'b,'c) t6 = ('a * 'b -> 'b * 'b) -> 'c.