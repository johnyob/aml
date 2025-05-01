
{
open Core
open Grace
open Token

let keywords = 
  [ "let", LET 
  ; "in", IN 
  ; "true", CONST_TRUE
  ; "false", CONST_FALSE
  ; "fun", FUN 
  ; "match", MATCH 
  ; "with", WITH 
  ; "forall", FORALL 
  ; "type", TYPE 
  ; "external", EXTERNAL
  ; "bot", BOT
  ; "absurd", ABSURD
  ]
;;

let find_keyword =
  let keyword_tbl = Hashtbl.create (module String) in
  List.iter keywords ~f:(fun (keyword, token) ->
      Hashtbl.set keyword_tbl ~key:keyword ~data:token);
  Hashtbl.find keyword_tbl
;;

let range_of_lexbuf lexbuf = 
  Range.of_lexbuf ?source:(Aml_source.get ()) lexbuf
;;
}

let alpha = ['a' - 'z']
let digit = ['0' - '9']
let space = [' ' '\t']
let newline = '\r'? '\n'

let id_char = alpha | digit | ['_' '\'']
let id = alpha id_char*

let sign = '-'?
let int = sign digit+

rule read  = 
  parse
  (* reserved operators *)
  | "->"                          
      { RIGHT_ARROW }
  | ":"
      { COLON }
  | "="
      { EQUAL }
  | "."
      { DOT }
  | ","
      { COMMA }
  | ";;"
      { SEMI_SEMI_COLON }

  (* comments *)
  | "(*"
      { read_comment lexbuf }

  (* identifiers (or keywords) *)
  | id as id
      { match find_keyword id with 
        | Some token -> token 
        | None -> IDENT id }
  | "Refl"
      { REFL }

  (* constants *)
  | "()"
      { CONST_UNIT }
  | int as n
      { CONST_INT (Int.of_string n) }
  
  | space+
      { read  lexbuf }
  | newline
      { Lexing.new_line lexbuf; read lexbuf }

  | "\'"
      { QUOTE }

  (* braces *)
  | "("
      { LEFT_PAREN }
  | ")"
      { RIGHT_PAREN }

  | eof
      { EOF }
  | _ as c                            
      { Aml_error.(raise @@ unknown_start_of_token ~range:(range_of_lexbuf lexbuf) c) }

(** Read a comment delimited by (* ... *)
    Nesting is not permitted. *)
and read_comment  = 
  parse
  | "*)"
      { read lexbuf }
  | newline 
      { Lexing.new_line lexbuf; read_comment lexbuf }
  | eof
      { Aml_error.(raise @@ unterminated_comment ~range:(range_of_lexbuf lexbuf)) }
  | _
      { read_comment lexbuf }
