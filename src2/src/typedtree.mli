(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree

type tybase = Tunit | Tbool | Tint | Treal

type ty =
  | Tbase   of tybase
  | Tvar    of UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of int
  | Ttuple  of ty list
  | Tconstr of Path.path * ty list

type local = symbol * int

type tyexp =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of local * ty                   (* local variable    *)
  | Eident  of Path.path * ty               (* symbol            *)
  | Eapp    of Path.path * tyexp list       (* op. application   *)
  | Elet    of lpattern * tyexp * tyexp     (* let binding       *)
  | Etuple  of tyexp list                   (* tuple constructor *)
  | Eif     of tyexp * tyexp * tyexp        (* _ ? _ : _         *)
  | Ernd    of tyrexp                       (* random expression *)

and tyrexp =
  | Rbool                                   (* flip               *)
  | Rinter    of tyexp * tyexp              (* interval sampling  *)
  | Rbitstr   of tyexp                      (* bitstring sampling *)
  | Rexcepted of tyrexp * tyexp             (* restriction        *)
  | Rapp      of Path.path * tyexp list     (* p-op. application  *)
