(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcFol
open EcTypes
open EcTyping

module Mid = EcIdent.Mid
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
type pattern = (ptnmap * EcUnify.unienv) * form

type search = [
  | `ByPath    of path
  | `ByPattern of pattern
]

(* -------------------------------------------------------------------- *)
let as_bypath (search : search) =
  match search with `ByPath p -> Some p | _ -> None

let as_bypattern (search : search) =
  match search with `ByPattern ptn -> Some ptn | _ -> None

(* -------------------------------------------------------------------- *)
let match_ (env : EcEnv.env) (paths : Sp.t) (patterns : pattern list) f =
  let module E = struct exception MatchFound end in

  let hyps = EcEnv.LDecl.init env [] in
  let mode = EcMatching.fmsearch in

     not (Sp.disjoint (EcFol.f_ops f) paths)
  || List.exists (fun ((v, ue), ptn) ->
      let ev = EcMatching.MEV.of_idents (Mid.keys !v) `Form in
      let na = List.length (snd (EcFol.destr_app ptn)) in

      let trymatch _bds tp =
        let tp =
          match tp.f_node with
          | Fapp (h, hargs) when List.length hargs > na ->
              let (a1, a2) = List.takedrop na hargs in
              f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty)
          | _ -> tp
        in
  
        try
          ignore (EcMatching.f_match_core mode hyps (ue, ev) ~ptn tp);
          raise E.MatchFound
        with EcMatching.MatchFailure ->
          `Continue
  
      in try
          ignore (EcMatching.FPosition.select trymatch f);
          false
        with E.MatchFound -> true)
     patterns

(* -------------------------------------------------------------------- *)
let search (env : EcEnv.env) (search : search list) =
  let paths    = Sp.of_list (List.pmap as_bypath search) in
  let patterns = List.pmap as_bypattern search in

  let check ax =
    match ax.EcDecl.ax_spec with
    | None   -> false
    | Some f -> match_ env paths patterns f

  in EcEnv.Ax.all ~check env;
