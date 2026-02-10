external choose3 : 'a. 'a -> 'a -> 'a -> 'a;;

let f = forall (type 'a 'b 'c 'd) ->
  fun w1 w2 x1 x2 x3 -> 
    let x1 = (x1 : 'c) in 
    let x2 = (x2 : 'd -> 'a) in 
    let x3 = (x3 : 'd -> 'b) in 
    match w2 : 'c = ('d -> 'a) with Refl -> 
    let g = fun z -> 
      match w1 : 'a = 'b with Refl ->
      (* The application of [z] here causes the 
         scope escape. This is because we propagate 
         the scope variable associated with 'a = 'b 
         to the LHS of the arrow as well. *)
      let x4 = choose3 x1 x2 x3 z in
      ()
    in 
    ()
;;
