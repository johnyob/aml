open Core
open Aml_main

let open_with_lexbuf ~f filename () =
  let in_ = In_channel.create filename in
  protect
    ~f:(fun () ->
      let lexbuf = Lexing.from_channel in_ in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      f lexbuf)
    ~finally:(fun () -> In_channel.close in_)
;;

module Params = struct
  open Command.Spec

  let dump_ast =
    flag "-dump-ast" no_arg ~doc:"Dumps the parsed program (formatted as a sexp)."
  ;;

  let dump_constraint =
    flag
      "-dump-constraint"
      no_arg
      ~doc:"Dumps the generated constraint (formatted as a sexp)."
  ;;
end

module Command = struct
  let lex =
    Command.basic_spec
      ~summary:"Lexes [filename] and prints the tokens."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:lex_and_print)
  ;;

  let parse =
    Command.basic_spec
      ~summary:"Parses [filename] and prints the program (formatted as a sexp)."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:parse_and_print)
  ;;

  let constraint_gen =
    Command.basic_spec
      ~summary:
        "Parses [filename] and prints the generated constraint (formatted as a sexp)."
      Command.Spec.(empty +> anon ("filename" %: string) +> Params.dump_ast)
      (fun filename dump_ast ->
         open_with_lexbuf ~f:(constraint_gen_and_print ~dump_ast) filename)
  ;;

  let type_check =
    Command.basic_spec
      ~summary:"Type checks [filename]."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> Params.dump_ast
        +> Params.dump_constraint
        +> Aml_log.Global.set_level_via_param)
      (fun filename dump_ast dump_constraint () ->
         open_with_lexbuf filename ~f:(type_check_and_print ~dump_ast ~dump_constraint))
  ;;

  let v =
    Command.group
      ~summary:"aml"
      [ "lex", lex
      ; "parse", parse
      ; "constraint-gen", constraint_gen
      ; "type-check", type_check
      ]
  ;;
end

let () = Command_unix.run Command.v
