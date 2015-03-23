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
  | `ByPath    of Sp.t
  | `ByPattern of pattern
]

(* -------------------------------------------------------------------- *)
let as_bypath (search : search) =
  match search with `ByPath p -> Some p | _ -> None

let as_bypattern (search : search) =
  match search with `ByPattern ptn -> Some ptn | _ -> None

(* -------------------------------------------------------------------- *)
let match_ (env : EcEnv.env) (search : search list) f =
  let module E = struct exception MatchFound end in

  let hyps = EcEnv.LDecl.init env [] in
  let mode = EcMatching.fmsearch in
  let opts = lazy (EcFol.f_ops f) in

  let do1 (search : search) =
    match search with
    | `ByPath paths ->
        not (Sp.disjoint (Lazy.force opts) paths)

    | `ByPattern ((v, ue), ptn) ->
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
          with E.MatchFound -> true

  in List.for_all do1 search

(* -------------------------------------------------------------------- *)
let search (env : EcEnv.env) (search : search list) =
  let check _ ax =
    match ax.EcDecl.ax_spec with
    | None   -> false
    | Some f -> match_ env search f

  in EcEnv.Ax.all ~check env
