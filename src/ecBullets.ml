(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
type frame = {
  bf_token : string;
  bf_loc   : EcLocation.t;
  bf_floor : int;
}

type stack = frame list

type error =
  | UnbulletedSplit    of { opened : int; level : [`Top | `Frame of frame] }
  | NoSubgoalToOpen    of { token : string }
  | OuterSkipsInner    of { token : string; outer : frame; inner : frame }
  | ReuseBeforeClosing of { token : string; frame : frame }

exception BulletError of EcLocation.t option * error

(* -------------------------------------------------------------------- *)
let pp_error fmt = function
  | UnbulletedSplit { opened; level = `Top } ->
      Format.fprintf fmt
        "previous tactic left %d open subgoals at top level; the next \
         phrase needs a bullet to focus one of them" opened
  | UnbulletedSplit { opened; level = `Frame f } ->
      Format.fprintf fmt
        "previous tactic left %d open subgoals at the bullet level \
         opened by `%s' at %s; the next phrase needs a bullet to \
         focus one of them"
        opened f.bf_token (EcLocation.tostring f.bf_loc)
  | NoSubgoalToOpen { token } ->
      Format.fprintf fmt
        "bullet `%s' opens a new subproof level but there are no \
         remaining subgoals" token
  | OuterSkipsInner { token; outer; inner } ->
      Format.fprintf fmt
        "bullet `%s' (matches an outer level opened at %s) skips past \
         inner bullet `%s' opened at %s whose subproof is not closed"
        token (EcLocation.tostring outer.bf_loc)
        inner.bf_token (EcLocation.tostring inner.bf_loc)
  | ReuseBeforeClosing { token; frame } ->
      Format.fprintf fmt
        "bullet `%s' reused but the previous subgoal (opened at %s) \
         is not closed"
        token (EcLocation.tostring frame.bf_loc)

(* -------------------------------------------------------------------- *)
let n_open (juc : EcCoreGoal.proof) =
  List.length (EcCoreGoal.all_hd_opened juc)

let raise_error ?loc err = raise (BulletError (loc, err))

(* -------------------------------------------------------------------- *)
(* Validate the bullet against the current stack and return the
   pre-phrase stack. Each frame's [bf_floor] records the open-count
   that should remain once the frame's subproof is fully closed; the
   frame becomes poppable when [n_open <= bf_floor]. *)
let open_phrase ~(bullet : string located option)
    (juc : EcCoreGoal.proof) (stack : stack) : stack =
  let opened = n_open juc in
  (* Top-of-stack floor, or 0 if the stack is empty (top-level: one
     focused goal allowed without a bullet). A phrase may run
     unbulleted iff [opened <= floor_top + 1]: the focused goal
     plus the goals "outside" the current level. *)
  let floor_top =
    match stack with [] -> 0 | f :: _ -> f.bf_floor in
  match bullet with
  | None ->
      if opened > floor_top + 1 then begin
        let level =
          match stack with [] -> `Top | f :: _ -> `Frame f in
        raise_error (UnbulletedSplit { opened; level })
      end;
      stack
  | Some b ->
      let tok = unloc b in
      let loc = loc b in
      (* Search the stack from innermost outward for a frame matching
         [tok]. Inner frames not yet drained block the match. *)
      let rec scan acc = function
        | [] -> `Open
        | f :: rest when f.bf_token = tok -> `Match (List.rev acc, f, rest)
        | f :: rest -> scan (f :: acc) rest
      in
      match scan [] stack with
      | `Open ->
          if opened = 0 then
            raise_error ~loc (NoSubgoalToOpen { token = tok });
          { bf_token = tok; bf_loc = loc; bf_floor = opened - 1 } :: stack
      | `Match (inner, frame, outer) ->
          (* Inner frames must already be drained. *)
          List.iter (fun (f : frame) ->
            if opened > f.bf_floor then
              raise_error ~loc
                (OuterSkipsInner { token = tok; outer = frame; inner = f }))
            inner;
          (* The matching frame's current slot must be closed. *)
          if opened > frame.bf_floor then
            raise_error ~loc (ReuseBeforeClosing { token = tok; frame });
          { frame with bf_loc = loc } :: outer

(* After a phrase has run, pop frames whose subproof has fully
   closed. Cascades through nested last-sibling frames; this is what
   lets the last sibling at any level be addressed by an unbulleted
   phrase. *)
let close_phrase (juc : EcCoreGoal.proof) (stack : stack) : stack =
  let opened = n_open juc in
  let rec pop = function
    | f :: rest when opened <= f.bf_floor -> pop rest
    | s -> s
  in
  pop stack

(* -------------------------------------------------------------------- *)
let pp_exn fmt = function
  | BulletError (_, err) -> pp_error fmt err
  | exn -> raise exn

let () = EcPException.register pp_exn
