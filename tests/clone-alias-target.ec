(* A clone replays a theory alias with its target substituted: an alias
   to a theory of the cloned theory points to its copy in the clone. It
   used to keep pointing to the original theory, printed `T.X`. *)

theory T.
  theory X.
    type u.
  end X.

  theory Y = X.
end T.

clone T as T1.

expect "
theory T1.
  (* import *) theory X.
                 (* import *) type u.
               end X.
  
  (* import *) theory Y = X.
end T1.
" by print theory T1.
