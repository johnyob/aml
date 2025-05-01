open! Core

module T = struct
  type t =
    [ `Debug
    | `Info
    | `Error
    ]
  [@@deriving equal, compare, sexp, enumerate]

  let to_string t =
    match t with
    | `Debug -> "Debug"
    | `Info -> "Info"
    | `Error -> "Error"
  ;;

  let of_string s =
    match s with
    | "Debug" -> `Debug
    | "Info" -> `Info
    | "Error" -> `Error
    | s -> failwithf "not a valid level %s" s ()
  ;;
end

include T

let arg =
  Command.Arg_type.enumerated ~list_values_in_help:true ~case_sensitive:false (module T)
;;

let as_or_more_verbose_than ~log_level ~msg_level =
  match log_level, msg_level with
  | `Error, Some `Error -> true
  | `Error, (None | Some (`Debug | `Info)) -> false
  | `Info, (None | Some (`Info | `Error)) -> true
  | `Info, Some `Debug -> false
  | `Debug, _ -> true
;;
