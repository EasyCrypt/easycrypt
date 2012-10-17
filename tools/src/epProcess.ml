open EpLayout

let cntr = ref (-1)
let fresh_cntr () = incr cntr;!cntr

let rec merge env  = function
  | Cnewline             -> Cnewline
  | Cbreak               -> Cbreak
  | Cblock    xs         -> Cblock   (List.map (merge env) xs) 
  | Cseq      xs         -> Cseq     (List.map (merge env) xs) 
  | Ciseq     xs         -> Ciseq     (List.map (merge env) xs) 
  | Ccascade  (x,y)      -> Ccascade (merge env x, merge env y) 
  | Cpack     xs         -> Cpack    (List.map (merge env) xs)
  | Cipack    xs         -> Cipack   (List.map (merge env) xs)
  | Cinstr    xs         -> Cinstr   (List.map (merge env) xs)
  | Citem     (s,_,_)    -> 
    let p = fresh_cntr() in Citem (s,p, snd (List.nth env p))    (*List.assoc p env)*)


let rec hsum = function
  | Citem (_,_,(h,_))  -> h
  | Cseq xs            -> EpOutput.get_max_hpos () + 1
  | Ciseq xs           -> EpOutput.get_max_hpos () + 1
  | Cblock xs          -> List.fold_right (fun x b -> (hsum x) + EpOutput.sim + b) xs 10
  | Cpack xs           -> List.fold_right (fun x b -> (hsum x) + EpOutput.sim + b) xs 0
  | Cipack xs          -> EpOutput.get_max_hpos() + 1
  | Cinstr xs          -> EpOutput.get_max_hpos() + 1
  | Ccascade (a,b)     -> (hsum a) + EpOutput.sim + (hsum b) 
  | Cbreak             -> 0
  | Cnewline           -> EpOutput.get_max_hpos () + 1 


let le_max e = 
  ((hsum e) + EpOutput.sim + EpOutput.get_indent_size () <  (EpOutput.get_max_hpos ()))

let le_rel_max e = 
  let size = hsum e in EpOutput.check_hspace_for size


let rec  print_tree = function
  | Cpack  []   -> ()
  | Cipack []   -> ()
  | Cseq   []   -> ()
  | Ciseq  []   -> ()
  | Cinstr []   -> ()
  | Citem ("",_,_) -> ()
  | Cbreak      -> ()
  | Cnewline    ->  EpOutput.add_emptyline ()
  | Citem (s,_,(h,_)) when (EpOutput.check_hspace_for h) -> EpOutput.add_item s h
  | Citem (s,_,(h,_)) -> EpOutput.add_newline (); EpOutput.add_item s h

  | Cseq xs  ->
    EpOutput.add_newline ();
    List.iter (fun x -> EpOutput.add_newline ();print_tree x) xs;
    EpOutput.add_newline ()

  | Ciseq xs    ->
    EpOutput.add_indent ();
    List.iter (fun x -> EpOutput.add_newline ();print_tree x) xs;
    EpOutput.del_indent ()

  | Cpack xs ->
    List.iter print_tree  xs

  | Cipack xs   -> 
    EpOutput.add_indent ();
    List.iter print_tree  xs;
    EpOutput.del_indent ()

(*
  | Ccascade (a,b) when (le_max (Ccascade (a,b))) ->
    EpOutput.add_newline ();
    print_tree a; print_tree b*)

  | Cblock xs (*when (le_rel_max (Cblock xs))*) -> 
     EpOutput.add_item "\\{" 5;
     if ( EpOutput.check_pending_indent ()) then 
       List.iter print_tree xs
     else
       (EpOutput.set_pending_indent ();
       List.iter print_tree xs;
       EpOutput.del_indent ());
     EpOutput.add_item "\\}" 5
(*  | Cblock xs when (le_max (Cblock xs)) ->
     EpOutput.add_newline ();
     EpOutput.add_item "\\{" 5;
     List.iter print_tree xs;
     EpOutput.add_item "\\}" 5
*)
(*
  | Cblock xs -> 
    EpOutput.add_newline ();
    EpOutput.add_item "\\{" 5;
    EpOutput.add_indent ();
    List.iter print_tree xs;
    EpOutput.del_indent ();
    EpOutput.add_item "\\}" 5;
    EpOutput.add_newline ()
*)
  | Cinstr xs -> 
    EpOutput.add_newline ();
    EpOutput.set_pending_indent ();
    List.iter print_tree xs;
    EpOutput.del_indent ()

  | Ccascade (a,b) -> 
    EpOutput.add_newline (); 
    print_tree a;
    EpOutput.add_indent ();
    print_tree b;
    EpOutput.del_indent ()


let rec count_citems = function
  | Citem    (s,_,_) -> 1
  | Cblock   xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0
  | Cseq     xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0
  | Ciseq    xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0
  | Ccascade (x,y)   -> count_citems x +  count_citems y
  | Cpack    xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0
  | Cipack   xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0
  | Cinstr   xs      -> List.fold_right (fun x b -> (count_citems x) + b) xs 0 
  | Cbreak           -> 0
  | Cnewline         -> 0

(** *)
let rec process = function
  | Citem    (s,_,_)  -> EpLatex.Preview.make_preview s
  | Cblock   xs       -> String.concat "\n" (List.map process xs)
  | Cseq     xs       -> String.concat "\n" (List.map process xs)
  | Ciseq    xs       -> String.concat "\n" (List.map process xs)
  | Ccascade (x,y)    -> String.concat "\n" [process x; process y]
  | Cpack    xs       -> String.concat "\n" (List.map process xs)
  | Cipack   xs       -> String.concat "\n" (List.map process xs)
  | Cinstr   xs       -> String.concat "\n" (List.map process xs)
  | Cbreak            -> ""
  | Cnewline          -> ""



let start xs  =
  let s = String.concat "\n" (List.map process xs) in
  let res = EpLatex.Preview.process_preview s "ep2tex" in
  Printf.printf "Input list %d \n" (List.length res);
  Printf.printf "Items leidos %d \n" (count_citems (List.hd xs));
  let info2 = merge res (List.hd xs) in
  Printf.printf "Input list %d \n" (fresh_cntr());
  print_tree info2
