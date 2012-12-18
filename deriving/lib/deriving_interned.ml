(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* Interned strings *)
module StringMap = Map.Make(String)

(* global state *)
let map = ref StringMap.empty
let counter = ref 0

type t = int * string
    deriving (Show)

let intern s = 
  try StringMap.find s !map
  with Not_found ->
    let fresh = (!counter, String.copy s) in begin
        map := StringMap.add s fresh !map;
        incr counter;
        fresh
      end
        
let to_string (_,s) = String.copy s
let name = snd
let compare (l,_) (r,_) = compare l r
let eq (l,_) (r,_) = l = r
