
open EcUtils

open EcFol
open EcBaseLogic
open EcLogic
open EcParsetree

type destr_error =
  | Destr_hl 

exception DestrError of destr_error

let destr_error e = raise (DestrError e)

let destr_hl f = 
  match f.f_node with
    | Fhoare (pre,s,post) -> pre, s, post
    | _ -> destr_error Destr_hl

let split_stmt n s = List.take_n n s
      

let process_phl _ _ _ _ (juc,n) = (juc,[n])





