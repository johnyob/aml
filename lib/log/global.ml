open! Import

module Message = struct
  type t =
    { time : Time_float_unix.t
    ; level : Level.t option
    ; message : Sexp_or_string.t
    ; tags : (string * string) list
    }
  [@@deriving sexp]

  let create ?level ?time ?(tags = []) message =
    let time = Option.value_or_thunk time ~default:(fun () -> Time_float_unix.now ()) in
    { level; time; tags; message }
  ;;

  let to_write_only_text t ~zone =
    let prefix =
      match t.level with
      | None -> ""
      | Some l -> Level.to_string l ^ " "
    in
    let formatted_tags =
      match t.tags with
      | [] -> []
      | _ :: _ ->
        " --" :: List.concat_map t.tags ~f:(fun (t, v) -> [ " ["; t; ": "; v; "]" ])
    in
    let message = Sexp_or_string.to_string t.message in
    String.concat
      (Time_float.to_string_abs ~zone t.time :: " " :: prefix :: message :: formatted_tags)
  ;;
end

type t = { mutable level : Level.t }

let t = { level = `Info }
let level () = t.level
let set_level level = t.level <- level
let would_log msg_level = Level.as_or_more_verbose_than ~log_level:(level ()) ~msg_level

let zone =
  lazy (if am_running_test then Timezone.find_exn "lon" else force Timezone.local)
;;

let write_message ?level ?time ?tags message_data _message_source =
  let message =
    match message_data with
    | #Sexp_or_string.t as s -> s
    | `Structured data -> `Sexp (Message_sexp.render data)
  in
  Message.create ?level ?time ?tags message
  |> Message.to_write_only_text ~zone:(force zone)
  |> prerr_endline
;;

let structured_message ?level ?time ?tags message_data message_source =
  if would_log level then write_message ?level ?time ?tags message_data message_source
;;

let set_level_via_param =
  let open Command.Param in
  map
    (flag "log-level" (optional Level.arg) ~doc:"LEVEL The log level")
    ~f:(Option.iter ~f:set_level)
;;
