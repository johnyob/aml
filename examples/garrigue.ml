external equal : int -> int -> bool;;
external add : int -> int -> int;; 
external if : 'a. bool -> 'a -> 'a -> 'a;;

let f = forall (type 'a) -> 
  fun x -> 
    match x : 'a = int with Refl -> 1
;;

let f1 = forall (type 'a) -> 
  fun x ->
    match x : 'a = int with Refl -> 1
;;

let f2 = forall (type 'a) -> 
  fun x y -> 
    let y = (y : 'a) in
    match x : 'a = int with Refl -> 
      equal y 0
;;

(* Ill typed due to scope escape *)

(* let g = forall (type 'a) -> 
  fun x y -> 
    let y = (y : 'a) in 
    match x : 'a = int with Refl -> 
      if (equal y 0) y 0 
;; *)

let g1 = forall (type 'a) -> 
  fun x y -> 
    match x : 'a = int with Refl -> 
      (if (equal (y : 'a) 0) (y : 'a) 0 : 'a)
;;

let g2 = forall (type 'a) -> 
  fun x y -> 
    let y = (y : 'a) in 
    match x : 'a = int with Refl -> 
      (if (equal y 0) y 0 : 'a)
;;

let p = forall (type 'a) -> 
  fun x -> 
    let y = match x : 'a = int with Refl -> 1 in 
    add y 2
;;

(* Ill typed due to scope escape (well-typed using outside-in) *)

(* let p1 = forall (type 'a) -> 
  fun x y -> 
    let y = (y : 'a) in 
    let z =
      match x : 'a = int with Refl -> if (equal y 0) y 0 
    in 
    add z 1
;; *)


(* Ill typed due to scope escape (relies on propagation of scopes to children) *)

(* let f = forall (type 'a 'b) -> 
  fun w1 w2 g -> 
    let g = (g : 'a) in 
    match w1 : 'a = ('b -> 'b) with Refl -> 
    match w2 : 'a = (int -> int) with Refl -> 
    g 3 
;; *)