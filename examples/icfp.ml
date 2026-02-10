external choose3 : 'a. 'a -> 'a -> 'a -> 'a;;

let f = forall (type 'a 'b 'c 'd) ->
  fun w1 w2 x1 x2 x3 -> 
    let x1 = (x1 : 'c) in 
    let x2 = (x2 : 'd -> 'a) in 
    let x3 = (x3 : 'd -> 'b) in 
    match w2 : 'c = ('d -> 'a) with Refl -> 
    (* Under this constraint, 
       'c is equal to 'd -> 'a *)
    let g = fun z -> 
      match w1 : 'a = 'b with Refl ->
      (* And w1 gives us 'a = 'b, so 
         x2 and x3 can have the same type. *)
      (choose3 x1 x2 x3 z : 'a)
    in 
    ()
;;
