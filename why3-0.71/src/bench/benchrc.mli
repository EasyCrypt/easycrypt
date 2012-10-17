(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


(**

[probs "myprobs"]
   file = "examples/monbut.why" #relatives to the rc file
   file = "examples/monprogram.mlw"
   theory = "monprogram.T"
   goal = "monbut.T.G"

   transform = "split_goal" #applied in the order
   transform = "..."
   transform = "..."

[tools "mytools"]
prover = cvc3
prover = altergo
#or only one
driver = "..."
command = "..."

loadpath = "..." #added to the one in why3.conf
loadpath = "..."

timelimit = 30
memlimit = 300

use = "toto.T" #use the theory toto (allow to add metas)

transform = "simplify_array" #only 1 to 1

[bench "mybench"]
tools = "mytools"
tools = ...
probs = "myprobs"
probs = ...
timeline = "prgbench.time"
average = "prgbench.avg"
csv = "prgbench.csv"
*)

open Bench
open Why3
open Util


type benchrc = { tools : tool list Mstr.t;
                 probs : prob list Mstr.t;
                 benchs : bench Mstr.t
               }

val read_file : Whyconf.config -> string -> benchrc


val gen_from_file :
  format:string option ->
  prob_name:string ->
  file_path:string ->
  file_name:string ->
  Bench.gen_task
