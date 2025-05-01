open Core
open Grace

module Token = struct
  include Token

  type t = token

  let pp ppf t =
    match t with
    | WITH -> Fmt.pf ppf "With"
    | TYPE -> Fmt.pf ppf "Type"
    | SEMI_SEMI_COLON -> Fmt.pf ppf "Semi_semi_colon"
    | RIGHT_PAREN -> Fmt.pf ppf "Right_paren"
    | RIGHT_ARROW -> Fmt.pf ppf "Right_arrow"
    | QUOTE -> Fmt.pf ppf "Quote"
    | MATCH -> Fmt.pf ppf "Match"
    | LET -> Fmt.pf ppf "Let"
    | LEFT_PAREN -> Fmt.pf ppf "Left_paren"
    | IN -> Fmt.pf ppf "In"
    | IDENT ident -> Fmt.pf ppf "Ident(%s)" ident
    | FUN -> Fmt.pf ppf "Fun"
    | EXTERNAL -> Fmt.pf ppf "External"
    | FORALL -> Fmt.pf ppf "Forall"
    | EQUAL -> Fmt.pf ppf "Equal"
    | EOF -> Fmt.pf ppf "Eof"
    | DOT -> Fmt.pf ppf "Dot"
    | COMMA -> Fmt.pf ppf "Comma"
    | CONST_UNIT -> Fmt.pf ppf "Const_unit"
    | CONST_TRUE -> Fmt.pf ppf "Const_true"
    | CONST_INT i -> Fmt.pf ppf "Const_int(%d)" i
    | CONST_FALSE -> Fmt.pf ppf "Const_false"
    | COLON -> Fmt.pf ppf "Colon"
    | REFL -> Fmt.pf ppf "Refl"
    | BOT -> Fmt.pf ppf "Bot"
    | ABSURD -> Fmt.pf ppf "Absurd"
  ;;

  let is_eof t =
    match t with
    | EOF -> true
    | _ -> false
  ;;

  let to_string = Fmt.to_to_string pp
end

module Lexer = struct
  let raw_read_token = Lexer.read

  let read_token ?source lexbuf =
    Aml_source.with_optional_source ?source @@ fun () -> raw_read_token lexbuf
  ;;

  let read_tokens ?source ?(keep_eof = false) lexbuf =
    Aml_source.with_optional_source ?source
    @@ fun () ->
    let rec loop acc =
      let tok = raw_read_token lexbuf in
      if Token.is_eof tok then if keep_eof then tok :: acc else acc else loop (tok :: acc)
    in
    loop [] |> List.rev
  ;;
end

module Parser = struct
  type 'a t = ?source:Source.t -> Lexing.lexbuf -> 'a

  let parse ~f ?source lexbuf =
    Aml_source.with_optional_source ?source
    @@ fun () ->
    try f Lexer.raw_read_token lexbuf with
    | Parser.Error ->
      Aml_error.(raise @@ syntax_error ~range:(Range.of_lexbuf ?source lexbuf))
  ;;

  let parse_structure = parse ~f:Parser.parse_structure
end
