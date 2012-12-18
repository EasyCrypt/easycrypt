module type Monad =
  sig
    type +'a m
    val return : 'a -> 'a m
    val fail : string -> 'a m
    val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
    val ( >> ) : 'a m -> 'b m -> 'b m
  end

module type MonadPlus =
  sig
    include Monad
    val mzero : 'a m
    val mplus : 'a m -> 'a m -> 'a m
  end

module MonadDefault
  (M : sig
         type +'a m
         val return : 'a -> 'a m
         val fail : string -> 'a m
         val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
       end) : Monad with type +'a m = 'a M.m

module Monad_option : MonadPlus with type 'a m = 'a option
module Monad_list : MonadPlus with type 'a m = 'a list
module IO :
  sig
    include Monad
    val putStr : string -> unit m
    val runIO : 'a m -> 'a
    val mkIO : (unit -> 'b) -> 'b m
  end
module type MonadUtilsSig =
sig
  include Monad
  val liftM : ('a -> 'b) -> 'a m -> 'b m
  val liftM2 : ('a -> 'b -> 'c) -> 'a m -> 'b m -> 'c m
  val liftM3 : ('a -> 'b -> 'c -> 'd) -> 'a m -> 'b m -> 'c m -> 'd m
  val liftM4 :
    ('a -> 'b -> 'c -> 'd -> 'e) -> 'a m -> 'b m -> 'c m -> 'd m -> 'e m
  val liftM5 :
    ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
    'a m -> 'b m -> 'c m -> 'd m -> 'e m -> 'f m
  val ap : ('a -> 'b) m -> 'a m -> 'b m
  val sequence : 'a m list -> 'a list m
  val sequence_ : 'a m list -> unit m
  val mapM : ('a -> 'b m) -> 'a list -> 'b list m
  val mapM_ : ('a -> 'b m) -> 'a list -> unit m
  val ( =<< ) : ('a -> 'b m) -> 'a m -> 'b m
  val join : 'a m m -> 'a m
  val filterM : ('a -> bool m) -> 'a list -> 'a list m
  val mapAndUnzipM :
    ('a -> ('b * 'c) m) -> 'a list -> ('b list * 'c list) m
  val zipWithM : ('a -> 'b -> 'c m) -> 'a list -> 'b list -> 'c list m
  val zipWithM_ : ('a -> 'b -> 'c m) -> 'a list -> 'b list -> unit m
  val foldM : ('a -> 'b -> 'a m) -> 'a -> 'b list -> 'a m
  val foldM_ : ('a -> 'b -> 'a m) -> 'a -> 'b list -> unit m
  val replicateM : int -> 'a m -> 'a list m
  val replicateM_ : int -> 'a m -> unit m
  val quand : bool -> unit m -> unit m
  val unless : bool -> unit m -> unit m
end

module MonadUtils (M : Monad) : MonadUtilsSig with type 'a m = 'a M.m
module type MonadPlusUtilsSig =
sig
  include MonadUtilsSig
  val mzero : 'a m
  val mplus : 'a m -> 'a m -> 'a m
  val guard : bool -> unit m
  val msum : 'a m list -> 'a m
end

module MonadPlusUtils (M : MonadPlus) : MonadPlusUtilsSig with type 'a m = 'a M.m

module MonadPlusUtils_option : MonadPlusUtilsSig with type 'a m = 'a Monad_option.m
module MonadPlusUtils_list : MonadPlusUtilsSig with type 'a m = 'a Monad_list.m
module Monad_IO : MonadUtilsSig with type 'a m = 'a IO.m

module type Monad_state_type =
sig
  include MonadUtilsSig
  type state
  val get : state m
  val put : state -> unit m
  val runState : 'a m -> state -> 'a * state
end

module Monad_state (S : sig type state end) :
  Monad_state_type with type state = S.state
