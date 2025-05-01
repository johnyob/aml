open Core

type t =
  [ `Sexp of Sexp.t
  | `String of string
  ]
[@@deriving sexp]

let to_string t =
  match t with
  | `Sexp sexp -> Sexp.to_string sexp
  | `String str -> str
;;
