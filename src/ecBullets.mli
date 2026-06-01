(* -------------------------------------------------------------------- *)
(* Bullet-stack management for [+strict_bullets]. A frame is pushed
   on the stack each time the user opens a new bullet level, and
   popped after a phrase whose subproof has fully closed (cascading
   through nested last-sibling frames). *)

open EcLocation
open EcParsetree

(* A single bullet frame: the bullet that opened it, the location of
   that opening, and the open-goal count that should remain once
   this frame's subproof is fully discharged. *)
type frame = private {
  bf_bullet : bullet;
  bf_loc    : EcLocation.t;
  bf_floor  : int;
}

type stack = frame list

(* Structured description of every way a strict-bullet check can
   fail. Each constructor carries enough context for diagnostics
   without forcing the caller to pattern-match on rendered strings. *)
type error =
  | UnbulletedSplit    of { opened : int; level : [`Top | `Frame of frame] }
  | NoSubgoalToOpen    of { bullet : bullet }
  | OuterSkipsInner    of { bullet : bullet; outer : frame; inner : frame }
  | ReuseBeforeClosing of { bullet : bullet; frame : frame }

exception BulletError of EcLocation.t option * error

(* Render a bullet as its surface syntax, e.g. ["-"], ["+++"]. *)
val pp_bullet : Format.formatter -> bullet -> unit

val pp_error : Format.formatter -> error -> unit

(* Validate the optional bullet on the next phrase against [stack],
   returning the stack to install for that phrase. May raise
   [BulletError]. *)
val open_phrase :
     bullet:bullet located option
  -> EcCoreGoal.proof
  -> stack
  -> stack

(* Pop frames whose subproof has fully closed after the last phrase.
   Cascades through nested last-sibling frames. *)
val close_phrase : EcCoreGoal.proof -> stack -> stack
