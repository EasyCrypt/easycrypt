(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcEnv
open EcPV

(* -------------------------------------------------------------------- *)
(* Weakening of a memory, shared by the [weakmem] rules of every logic: a
   judgement on a statement that holds in a memory [me] holds in [me]
   extended with fresh local program variables [xs], which the judgement
   does not mention. *)

exception InvalidWeakening of string

let invalid fmt = Format.kasprintf (fun msg -> raise (InvalidWeakening msg)) fmt

(* -------------------------------------------------------------------- *)
(* The memory [me] is rebuilt from the declarations of [me'] that precede
   [xs] (a memory being built by successive [EcMemory.bindall]), then
   checked: binding [xs] in it must give back [me'] (which re-checks the
   freshness of [xs]). *)
let restrict
    (env : env) (xs : ovariable list) ((m, mt') : memenv) (used : PV.t)
=
  let name, decls' =
    match EcMemory.for_printing mt' with
    | None   -> invalid "the memory has no local variables"
    | Some x -> x in

  let n = List.length decls' - List.length xs in
  let decls  = List.filteri (fun i _ -> i <  n) decls' in
  let suffix = List.filteri (fun i _ -> i >= n) decls' in

  if n < 0 || not (List.all2 ov_equal xs suffix) then
    invalid "the variables are not the last declared ones";

  let mt = EcMemory.empty_local_mt ~witharg:(is_some name) in
  let mt =
    try  EcMemory.bindall_mt decls mt
    with EcMemory.DuplicatedMemoryBinding x ->
      invalid "variable %s declared twice" x in

  let mt'' =
    try  EcMemory.bindall_mt xs mt
    with EcMemory.DuplicatedMemoryBinding x ->
      invalid "variable %s already declared" x in

  if not (EcMemory.mt_equal mt'' mt') then
    invalid "the memory is not an extension of a memory by the variables";

  List.iter (fun (x : ovariable) ->
      x.ov_name |> oiter (fun x ->
        if PV.mem_pv env (pv_loc x) used then
          invalid "variable %s is used by the judgement" x))
    xs;

  (m, mt)

(* -------------------------------------------------------------------- *)
let used (env : env) (m : memory) (s : stmt) (fs : form list) =
  List.fold_left
    (fun pv f -> PV.union pv (PV.fv env m f))
    (PV.union (s_read env s) (s_write env s))
    fs
