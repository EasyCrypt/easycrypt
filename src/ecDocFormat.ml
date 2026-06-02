type t =
  | Markdown
  | HTML


let all =
  [
    ("markdown", Markdown);
    ("html", HTML);
  ]

let choices =
  List.map fst all

let default : t =
  Markdown


let to_string (format : t) : string =
  match format with
  | Markdown -> "markdown"
  | HTML -> "html"

let of_string (s : string) : t option =
  List.assoc_opt (String.lowercase_ascii s) all
