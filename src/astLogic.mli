

type ('f,'p,'e) g_equiv = 
   'f * 'f * 'p * 'p * ('e * 'e) option
  (* AppEquiv: approximate, only one function, plus alpha and delta *)

type equiv = (Ast.fct, Fol.pred, Fol.term) g_equiv

type axiom = string * bool ref * Fol.pred

type ('inv,'s) helper =
  | Helper_inv of 'inv
  | Helper_eager of 's

type ('p,'bad) g_inv =
  | Inv_global of 'p
  | Inv_upto of 'bad

type bad = Fol.pred * Fol.pred * Fol.pred

type inv = (Fol.pred, bad) g_inv * string list

type ('p,'bad,'inv) g_equiv_kind =
  | Aequiv_spec of 'p * 'p * 'inv
  | Aequiv_inv of ('p,'bad) g_inv * string list


type 'e g_pr_hint =
  | Pr_equiv of string
  | Pr_bad of 'e * 'e * string
  | Pr_admit
  | Pr_compute
  | Pr_none
  | Pr_same
  | Pr_split
  | Pr_failure of int * 'e * 'e * (Ast.fct * 'e) list

type pr_hint = Ast.exp g_pr_hint

type ('f, 'pr, 'p, 'bad, 'inv, 'pr_hint) g_annot_body =
  | Aequiv of 'f * 'f * (('p,'bad,'inv) g_equiv_kind)
  | Aproba of 'pr * 'pr_hint

type claim = Ast.real_exp * pr_hint
    
(*type annot_body =
    (Ast.fct, Ast.real_exp, Fol.pred, bad, (inv, Ast.stmt * Ast.stmt) helper , 
     pr_hint ) g_annot_body *)

(** {2 Tactic } *)

type at_pos = 
  | At_last
  | At_pos of int list
  | At_empty

type 'f inline_kind =
  | IKat of at_pos 
  | IKfct of 'f

type 'f inline_info = ApiTypes.side * 'f inline_kind

type swap_kind =
  | SKpop of int
  | SKpush of int
  | SKswap of int * int * int (* start, length, delta *)

type swap_info = ApiTypes.side * swap_kind

type 'e rnd_bij_info =
  | RIid
  | RIidempotant of 'e
  | RIbij of 'e * 'e

type 'e rnd_info =
  | RIdisj of ApiTypes.side
  | RIpara of 'e rnd_bij_info

(* direction of tactic application *)
type tac_direction = 
  | Backwards
  | Forwards

type ('p, 'auto_info, 't, 'e, 'r, 'f,'v) tactic =
  (* basic tactic *)
  | Tidtac 
  | Tasgn
  | Trnd of (tac_direction * 'r rnd_info)
  | Tcall of 'auto_info 
  | Tinline of 'f inline_info
  | Tswap of swap_info
  | Tsimplify_post
  | Ttrivial
  (* | Tifrev *)
  | Teqobsin of 'p * 'p * 'p * string list
  | Tauto of 'auto_info 
  | Twp of (int*int) option
  | Tsp of (int*int) option
  | Tderandomize of ApiTypes.side
  | Tcase of (ApiTypes.side * 'e)
  | Tif of ApiTypes.side 
  | Tautosync
  | Tifsync of ((int * int) option)
  | Tifneg of (ApiTypes.side * at_pos)
  | Treduce of (ApiTypes.side * at_pos * bool)
  | Twhile of (ApiTypes.side * tac_direction * 'p * ('e * 'e) option)
  | TwhileApp of ('e * 'e * 'e * 'e * 'e * 'p)
  | TwhileAppGen of ('v * 'e * 'e * 'e * int * int * 'e * 'e * 'p)
  | Tpopspec of (ApiTypes.side * (EcUtil.pos * string) * 'e list)
  | Tprhl 
  | Taprhl 
  | Tunroll of (ApiTypes.side * at_pos)
  | Tsplitwhile of (ApiTypes.side * at_pos * 'e)
  | Tapp of (int * int * 'p * ('e*'e*'e*'e) option )
  | Tset of (ApiTypes.side * at_pos * (EcUtil.pos*string) * 't * 'e)
  | Tadmit
  | Tunfold of string list
  (* composition tactic *)
  | Ttry of ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic
  | Tseq of
      ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic *
        ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic
  | Trepeat of ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic
  | Tdo of int * ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic
  | Tsubgoal of ('p, 'auto_info, 't, 'e, 'r, 'f, 'v) tactic list
 
