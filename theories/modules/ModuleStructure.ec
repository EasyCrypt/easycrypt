(* Theory abstracting over the structure of procedures *)
abstract theory Proc.
type a. (* type of argument to the procedure *)
type r. (* type of result of the procedure *)

(* Module type for procedure. Use wrapper to conform to the interface if needed *)
module type Proc = {
    proc p(a: a): r
}.
end Proc.