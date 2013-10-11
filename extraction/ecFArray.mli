type 'x array 
val empty : 'a array 
val create : int -> 'a -> 'a array 
val init : int -> (int -> 'a) -> 'a array
val get : 'a t -> int -> 'a
val _dtlb_rb : 'a t -> int -> 'a 
val set : 'a t -> int -> 'a -> 'a t
val _dtlb_lsmn_rb : 'a t -> int -> 'a -> 'a t
val write : 'a t -> int -> 'a t -> int -> int -> 'a array
val impure : ('a array -> 'b) -> 'a t -> 'b
val length : 'a t -> int
val fold_left : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val fold_right : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val sub : 'a t -> int -> int -> 'a array
val brbr : 'a t -> 'a t -> 'a array
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c array 
val map : ('a -> 'b) -> 'a t -> 'b array 
val clclcl : 'a t -> 'a -> 'a array
val _clcl_ : 'a -> 'a t -> 'a array

