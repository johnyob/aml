open! Import

let lex_and_print input =
  Aml_error.handle_uncaught ~exit:false
  @@ fun () ->
  let source = Aml_source.For_testing.expect_test_source input in
  let lexbuf = Lexing.from_string input in
  let tokens = Lexer.read_tokens ~source lexbuf in
  Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
;;

let%expect_test "unterminated comment" =
  let str = {| (* This is a very interesting comment |} in
  lex_and_print str;
  [%expect
    {|
    error[E001]: unterminated comment
        ┌─ expect_test.ml:1:40
      1 │   (* This is a very interesting comment
        │                                         ^
    |}]
;;

let%expect_test "unexpected char" =
  let str = {| 1 + 2 |} in
  lex_and_print str;
  [%expect
    {|
    error[E002]: unknown start of token: '+'
        ┌─ expect_test.ml:1:4
      1 │   1 + 2
        │     ^
    |}]
;;

let%expect_test "single-line comment" =
  let str = {| (* Some comment here *) |} in
  lex_and_print str;
  [%expect {| |}]
;;

let%expect_test "multi-line comment" =
  let str =
    {| 
      (* This is a very long 
         and interesting comment 
      *) 
    |}
  in
  lex_and_print str;
  [%expect {| |}]
;;

let%expect_test "keywords" =
  [ "let"
  ; "in"
  ; "fun"
  ; "match"
  ; "with"
  ; "forall"
  ; "type"
  ; "external"
  ; "Refl"
  ; "bot"
  ; "absurd"
  ; ";;"
  ; "->"
  ; ":"
  ; "="
  ; "."
  ; ","
  ; "'"
  ; "true"
  ; "false"
  ; "()"
  ; "("
  ; ")"
  ]
  |> List.iter ~f:(fun keyword ->
    Fmt.pr "Keyword: %s @.Output: " keyword;
    lex_and_print keyword);
  [%expect
    {|
    Keyword: let
    Output: Let
    Keyword: in
    Output: In
    Keyword: fun
    Output: Fun
    Keyword: match
    Output: Match
    Keyword: with
    Output: With
    Keyword: forall
    Output: Forall
    Keyword: type
    Output: Type
    Keyword: external
    Output: External
    Keyword: Refl
    Output: Refl
    Keyword: bot
    Output: Bot
    Keyword: absurd
    Output: Absurd
    Keyword: ;;
    Output: Semi_semi_colon
    Keyword: ->
    Output: Right_arrow
    Keyword: :
    Output: Colon
    Keyword: =
    Output: Equal
    Keyword: .
    Output: Dot
    Keyword: ,
    Output: Comma
    Keyword: '
    Output: Quote
    Keyword: true
    Output: Const_true
    Keyword: false
    Output: Const_false
    Keyword: ()
    Output: Const_unit
    Keyword: (
    Output: Left_paren
    Keyword: )
    Output: Right_paren
    |}]
;;

let%expect_test "ints" =
  [ "1"; "0"; "0123456789"; "-42" ]
  |> List.iter ~f:(fun int_ ->
    Fmt.pr "Int: %s @.Output: " int_;
    lex_and_print int_);
  [%expect
    {|
    Int: 1
    Output: Const_int(1)
    Int: 0
    Output: Const_int(0)
    Int: 0123456789
    Output: Const_int(123456789)
    Int: -42
    Output: Const_int(-42)
    |}]
;;

let%expect_test "ident" =
  [ "x"
  ; "type_"
  ; "lident"
  ; "x1"
  ; "snake_case"
  ; "prime'"
  ; "prime_numbers10998927898723178923''''"
  ]
  |> List.iter ~f:(fun ident ->
    Fmt.pr "Ident: %s @.Output: " ident;
    lex_and_print ident);
  [%expect
    {|
    Ident: x
    Output: Ident(x)
    Ident: type_
    Output: Ident(type_)
    Ident: lident
    Output: Ident(lident)
    Ident: x1
    Output: Ident(x1)
    Ident: snake_case
    Output: Ident(snake_case)
    Ident: prime'
    Output: Ident(prime')
    Ident: prime_numbers10998927898723178923''''
    Output: Ident(prime_numbers10998927898723178923'''')
    |}]
;;
