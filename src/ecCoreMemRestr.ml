open EcIdent
open EcPath
open EcAst

let mr_empty = Empty
let mr_full = All

let mr_union s1 s2 =
  match s1, s2 with
  | Empty, s | s, Empty -> s
  | _, _ -> Union(s1, s2)

let mr_diff s1 s2 =
  match s1, s2 with
  | Empty, _ -> Empty
  | _, Empty -> s1
  | _, _ -> Diff(s1, s2)

let mr_inter s1 s2 =
  match s1, s2 with
  | Empty, _ | _, Empty -> Empty
  | _, _ -> Inter(s1, s2)

let mr_globals (xs : Sx.t) =
  Sx.fold (fun g mr -> mr_union (Var g) mr) xs mr_empty

let functor_fun ff_params ff_xp =
  let fv = x_fv Mid.empty ff_xp in
  let _, ff_params =
    List.fold_right (fun (x,mty) (fv, params) ->
        if Mid.mem x fv then
          let fv = fv_union (mty_fv mty) (Mid.remove x fv) in
          fv, (x,mty)::params
        else
          fv, params) ff_params (fv, [])
  in
  {ff_params; ff_xp }

let mr_globfun ff_params ff_xp =
  GlobFun (functor_fun ff_params ff_xp)

let mr_globfuns ff_params (xs : Sx.t) =
  Sx.fold (fun f mr -> mr_union (mr_globfun ff_params f) mr) xs mr_empty
