open EcCoreGoal.FApi
open EcMatching.Position
open EcParsetree
open EcModules

type outline_variant =
  (* method of unification and path of procedure to outline *)
  | OV_Proc of [`Exact | `Alias] * EcPath.xpath
  (* replacement code *)
  | OV_Stmt of stmt

(*
  `outline` - replace a program slice with a procedure call or statement.

  Arguments,
    side: selects the program (left or right) that will outlined.
    cpr: selects the particular slice of the program to outline.
    variant: choose the type of outlining: procedure or statement.
*)
val t_outline : side -> codepos_range -> outline_variant -> backward

val process_outline : outline_info -> backward
