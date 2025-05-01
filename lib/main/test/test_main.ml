open! Core
open! Grace
open Aml_main

let type_check_and_print
      ?(dump_ast = false)
      ?(dump_constraint = false)
      ?(log_level = `Info)
      str
  =
  Aml_log.Global.set_level log_level;
  let source = Aml_source.For_testing.expect_test_source str in
  type_check_and_print
    ~source
    ~dump_ast
    ~dump_constraint
    (Lexing.from_string ~with_positions:true str)
;;

let include_prelude =
  {|
    external equal : int -> int -> bool;;
    external add : int -> int -> int;;
    external sub : int -> int -> int;;
    external mul : int -> int -> int;; 
    external div : int -> int -> int;;
    external mod : int -> int -> int;;
    external compare : int -> int -> int;;
    external if : 'a. bool -> 'a -> 'a -> 'a;;
    external fix : 'a 'b. (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b;;
  |}
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let power = fix (fun power n x -> 
        if (equal n 0) 
          1
          (mul x (power x (sub n 1)))
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let even = fun n -> equal (mod n 2) 0;;

      let power = fix (fun power x n ->
          if (equal n 1)
            x
            (if (even n)
              (power (mul x x) (div n 2))
              (mul x (power (mul x x) (div n 2))))
        )
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let sum = 
        fix (fun sum n -> 
          if (equal n 0) 
            0 
            (add n (sum (sub n 1)))
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let sum = fun n ->
        let loop = fix (fun loop n acc ->
          if (equal n 0) 
            acc
            (loop (sub n 1) (add n acc)))
        in loop n
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let app_error = 
        1 (fun y -> y)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E008]: mismatched type
        ┌─ expect_test.ml:3:9
      3 │          1 (fun y -> y)
        │          ^
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let x =
        (fun y z -> y z) ()
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E008]: mismatched type
        ┌─ expect_test.ml:3:26
      3 │          (fun y z -> y z) ()
        │                           ^^
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let f = forall (type 'a) -> 
        fun x -> 
          match x : 'a = int with Refl -> 1
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let f1 = forall (type 'a) -> 
        fun x ->
          match x : 'a = int with Refl -> 1
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let f2 = forall (type 'a) -> 
        fun x y -> 
          let y = (y : 'a) in
          match x : 'a = int with Refl -> 
            equal y 0
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let g = forall (type 'a) -> 
        fun x y -> 
          let y = (y : 'a) in 
          match x : 'a = int with Refl -> 
            if (equal y 0) y 0 
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E010]: type-level equality introduced by `match` escapes its scope
        ┌─ expect_test.ml:15:11
     14 │              let y = (y : 'a) in
     15 │ ╭            match x : 'a = int with Refl ->
     16 │ │              if (equal y 0) y 0
        │ ╰──
     17 │          ;;
        = hint: add a type annotation
    |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let g1 = forall (type 'a) -> 
        fun x y -> 
          match x : 'a = int with Refl -> 
            (if (equal (y : 'a) 0) (y : 'a) 0 : 'a)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let g2 = forall (type 'a) -> 
        fun x y -> 
          let y = (y : 'a) in 
          match x : 'a = int with Refl -> 
            (if (equal y 0) y 0 : 'a)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let p = forall (type 'a) -> 
        fun x -> 
          let y = match x : 'a = int with Refl -> 1 in 
          mul y 2
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let p1 = forall (type 'a) -> 
        fun x y -> 
          let y = (y : 'a) in 
          let z =
            match x : 'a = int with Refl -> if (equal y 0) y 0 
          in 
          add z 1
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E010]: type-level equality introduced by `match` escapes its scope
        ┌─ expect_test.ml:16:13
     16 │              match x : 'a = int with Refl -> if (equal y 0) y 0
        │              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        = hint: add a type annotation
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let magic = 
        forall (type 'a 'b) -> 
          (fun x -> x : 'a -> 'b)
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E008]: mismatched type
        ┌─ expect_test.ml:4:21
      4 │            (fun x -> x : 'a -> 'b)
        │                      ^
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let escape = fun f -> 
        forall (type 'a) -> 
          (f : 'a -> 'a)
      ;; 
    |}
    |> Dedent.string
  in
  type_check_and_print str;
  [%expect
    {|
    error[E009]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun f ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (f : 'a -> 'a)
        │ ╰──
      4 │    ;;
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let escape = fun x ->
        forall (type 'a) -> 
          (x : 'a)
      ;;
    |}
    |> Dedent.string
  in
  type_check_and_print str;
  [%expect
    {|
    error[E009]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun x ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (x : 'a)
        │ ╰──
      4 │    ;;
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let x = 
        (forall (type 'a) -> fun x -> let x = (x : 'a) in (x : 'a)) ()
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let x = 
        (forall (type 'a) -> ((fun x -> fun y -> y) (fun x -> x) : 'a -> 'a))
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_prelude
    ^ {|
      let coerce = forall (type 'a 'b) -> 
        fun w x -> 
          let x = (x : 'a) in 
          match w : 'a = 'b with Refl -> (x : 'b)
      ;;

      let f = forall (type 'a) -> 
        fun w x -> 
          let x = (x : 'a) in 
          match w : 'a = int with Refl ->
            coerce Refl (if true x 0)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E010]: type-level equality introduced by `match` escapes its scope
        ┌─ expect_test.ml:21:11
     20 │              let x = (x : 'a) in
     21 │ ╭            match w : 'a = int with Refl ->
     22 │ │              coerce Refl (if true x 0)
        │ ╰──
     23 │          ;;
        = hint: add a type annotation
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let f = forall (type 'a 'b) -> 
        fun w1 w2 g -> 
          let g = (g : 'a) in 
          match w1 : 'a = ('b -> 'b) with Refl -> 
          match w2 : 'a = (int -> int) with Refl -> 
          g 3 
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E010]: type-level equality introduced by `match` escapes its scope
        ┌─ expect_test.ml:6:11
      5 │              match w1 : 'a = ('b -> 'b) with Refl ->
      6 │ ╭            match w2 : 'a = (int -> int) with Refl ->
      7 │ │            g 3
        │ ╰──
      8 │          ;;
        = hint: add a type annotation
    |}]
;;

let%expect_test "" =
  let str =
    {| 
      let f = fun x -> 
        match x : int = bool with Refl -> absurd 
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type 'a prod1;;

      let f = fun x -> 
        match x : unit = unit prod1 with Refl -> absurd 
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let f = absurd;;   
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: unexpected consistent context
        ┌─ expect_test.ml:2:15
      2 │        let f = absurd;;
        │                ^^^^^^ type-level equational context is consistent at this point
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let f = match Refl : int = int with Refl -> absurd;;   
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: unexpected consistent context
        ┌─ expect_test.ml:2:51
      2 │        let f = match Refl : int = int with Refl -> absurd;;
        │                                                    ^^^^^^ type-level equational context is consistent at this point
    |}]
;;
