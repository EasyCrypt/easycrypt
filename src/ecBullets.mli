(* -------------------------------------------------------------------- *)
(* Bullet-stack management for [+strict_bullets]. A frame is pushed
   on the stack each time the user opens a new bullet level, and
   popped after a phrase whose subproof has fully closed (cascading
   through nested last-sibling frames). *)

open EcLocation

(* A single bullet frame: the token that opened it (e.g. "-", "++"),
   the location of that opening, and the open-goal count that should
   remain once this frame's subproof is fully discharged. *)
type frame = private {
  bf_token : string;
  bf_loc   : EcLocation.t;
  bf_floor : int;
}

type stack = frame list

(* Structured description of every way a strict-bullet check can
   fail. Each constructor carries enough context for diagnostics
   without forcing the caller to pattern-match on rendered strings. *)
type error =
  | UnbulletedSplit    of { opened : int; level : [`Top | `Frame of frame] }
  | NoSubgoalToOpen    of { token : string }
  | OuterSkipsInner    of { token : string; outer : frame; inner : frame }
  | ReuseBeforeClosing of { token : string; frame : frame }

exception BulletError of EcLocation.t option * error

val pp_error : Format.formatter -> error -> unit

(* Validate the optional bullet on the next phrase against [stack],
   returning the stack to install for that phrase. May raise
   [BulletError]. *)
val open_phrase :
     bullet:(string located) option
  -> EcCoreGoal.proof
  -> stack
  -> stack

(* Pop frames whose subproof has fully closed after the last phrase.
   Cascades through nested last-sibling frames. *)
val close_phrase : EcCoreGoal.proof -> stack -> stack
