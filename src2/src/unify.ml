(* -------------------------------------------------------------------- *)
open Maps
open Utils
open Types

(* -------------------------------------------------------------------- *)
let unify (t1 : ty) (t2 : ty) =
  let uf = UnionFind.create () in
  let tf = ref PTree.empty in

  let rec unify t1 t2 =
    match t1, t2 with
      | Tbase   t1      , Tbase   t2       -> t1 = t2
      | Tvar    a1      , Tvar    a2       -> a1 = a2
      | Ttuple  t1      , Ttuple  t2       -> List.all2 unify t1 t2
      | Tconstr (c1, p1), Tconstr (c2, p2) -> (c1 = c2) && (List.all2 unify p1 p2)
      | Trel    r1      , Trel    r2       -> assert false

      | Tunivar r1, Tunivar r2 -> begin
        let r1 = UnionFind.find uf r1 in
        let r2 = UnionFind.find uf r2 in
          if   r1 = r2
          then true
          else
            match PTree.lookup r1 !tf, PTree.lookup r2 !tf with
              | None   , None   -> UnionFind.union uf r1 r2; true
              | Some t , None
              | None   , Some t ->
                  tf := PTree.insert r1 t !tf;
                  tf := PTree.insert r2 t !tf;
                  true
              | Some t1, Some t2 ->
                  unify t1 t2
      end

      | _, _ -> false

  in
    unify t1 t2
