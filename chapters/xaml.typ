#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

// HACK to get thm to left align
#show: thmrules

#let ebox = textsf("box")
#let escope = textsf("scope")
#let ecoerce = $triangle.r.small$
#let euse = textsf("use")

$
  #proof-tree(
    rule(
      $Gamma tack x : A space [Psi]$, 
      $x : A in Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack lambda x : A. M : A -> B space [Psi]$, 
      $Gamma, x : A tack M : B space [Psi]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack M space N : B space [Psi]$, 
      $Gamma tack M : A -> B space [Psi]$, 
      $Gamma tack N : A space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack elet ebox u = M ein N : B space [Psi_2]$, 
      $Gamma tack M : [Psi_1]A space [Psi_2]$, 
      $Gamma, u :: A[Psi_1]tack N : B space [Psi_2]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack ebox M : [Psi_1]A space [Psi_2]$, 
      $Gamma tack M : A space [Psi_1]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack u : A space [Psi_2]$, 
      $u :: A[Psi_1] in Gamma$, 
      $Psi_1 subset.eq Psi_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack escope eqname: A = B. M : angle.l A = B angle.r C space [Psi]$, 
      $Gamma, eqname: A = B tack M : C space [Psi]$, 
      $eqname disjoint C, Psi$
    )
  ) 

  #h1 

  #proof-tree(
    rule(
      $Gamma tack angle.l M angle.r : C space [Psi]$, 
      $Gamma tack M : angle.l A = B angle.r C space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack Lambda alpha. M : tforall(alpha) A space [Psi]$, 
      $Gamma, alpha tack M : A space [Psi]$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack M space [B] : A[alpha := B] space [Psi]$, 
      $Gamma tack M : tforall(alpha) A space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack Lambda scopev. M : tforall(scopev) A space [Psi]$, 
      $Gamma, scopev tack M : A space [Psi]$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack M space [Psi_2] : A[scopev := Psi_2] space [Psi_1]$, 
      $Gamma tack M : tforall(scopev) A space [Psi_1]$
    )
  )


  #v2 

  #proof-tree(
    rule(
      $Gamma tack erefl : tforall(alpha) alpha = alpha$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack M ecoerce gamma : B space [Psi]$, 
      $Gamma tack M : A space [Psi]$, 
      $Gamma tack gamma : A ~ B space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack euse u ewith M : A space [Psi_2]$, 
      $Gamma tack M : {Psi_1} space [Psi_2]$, 
      $u :: A[Psi_1] in Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack emptyset : {} space [Psi]$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack eqname <- M : {eqname} space [Psi]$, 
      $eqname : A in Gamma$, 
      $Gamma tack M : A space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack M,,N : {Psi_1, Psi_2} space [Psi_3]$, 
      $Gamma tack M : {Psi_1} space [Psi_3]$, 
      $Gamma tack N : {Psi_2} space [Psi_3]$
    )
  )
$


$
  
  #proof-tree(
    rule(
      $Gamma tack alpha ~ alpha space [Psi]$, 
      $alpha in Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack A ~ B space [Psi]$, 
      $eqname : A = B in Gamma$, 
      $eqname in Psi$
    )
  )

  #v2




  #h1 

  #proof-tree(
    rule(
      $Gamma tack overline(A) tformer ~ overline(B) tformer space [Psi]$, 
      $forall i. space Gamma tack A_i ~ B_i space [Psi]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack A_i ~ B_i space [Psi]$, 
      $Gamma tack overline(A) tformer ~ overline(B) tformer space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha) A ~ tforall(alpha) B space [Psi]$, 
      $Gamma, alpha tack A ~ B space [Psi]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack A[alpha := C] ~ B[alpha := C] space [Psi]$, 
      $Gamma tack tforall(alpha) A ~ tforall(alpha) B space [Psi]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack [Psi_2]A ~ [Psi_2]B space [Psi_1]$, 
      $Gamma tack A ~ B space [Psi_1, Psi_2]$
    )
  )

  #h1 

  // 1 minute madness password: llama

  // 

  #proof-tree(
    rule(
      $Gamma tack A ~ B space [Psi_1, Psi_2]$, 
      $Gamma tack [Psi_1]A ~ [Psi_1]B space [Psi_2]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack tforall(scopev) A ~ tforall(scopev) B space [Psi]$, 
      $Gamma, scopev tack A ~ B space [Psi]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack A[scopev := Psi_2] ~ B[scopev := Psi_2] space [Psi_1]$, 
      $Gamma tack tforall(scopev) A ~ tforall(scopev) B space [Psi_1]$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack A ~ B space [Psi]$, 
      $Gamma tack B ~ A space [Psi]$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack A ~ C space [Psi]$, 
      $Gamma tack A ~ B space [Psi]$, 
      $Gamma tack B ~ C space [Psi]$
    )
  )
$

Useful programs:
#let eunbox = textsf("unbox")

$
  eunbox M &= elet ebox u = M ein u \  

  lambda x : A. ebox x &: A -> [Psi]A \  

  lambda x : [emptyset]A. elet ebox u = x ein euse u ewith emptyset &: [emptyset]A -> A \ 

  lambda x: [Psi_1][Psi_2]A. ebox (eunbox (eunbox x)) &: [Psi_1][Psi_2]A -> [Psi_1, Psi_2]A \

  lambda x : [Psi_1, Psi_2]A. ebox (ebox (eunbox x)) &: [Psi_1, Psi_2]A -> [Psi_1][Psi_2]A \ 


  lambda f : ([Psi]A -> [Psi]B). ebox (lambda x : A. eunbox (f space  (ebox x))) &: ([Psi]A -> [Psi]B) -> [Psi](A -> B) \ 

  lambda f : [Psi](A -> B). lambda x : [Psi]A. ebox ((eunbox f) space (eunbox x)) &: [Psi](A -> B) -> [Psi]A -> [Psi]B \ 

  lambda x : [Psi](A = B). elet ebox u = x ein erefl [[Psi]A = [Psi]A] ecoerce (erefl = ebox u) &: [Psi](A = B) -> ([Psi]A = [Psi]B) \ 

  lambda x : [Psi]A = [Psi]B. ebox_= x &: ([Psi]A = [Psi]B) -> [Psi](A = B)
$

$
  (e : tau) --> elet x = [| e |] ein (x : tau_1 :> tau <: tau_2)
$

$
  tau :> tau &= "id" \ 
  [Psi]tau_1 :> tau_2 &= lambda x : [Psi]tau_1. (euse x ewith Psi_"elim" : tau_1 :> tau_2) \ 
  tau_1 -> tau_2 :> tau_3 -> tau_4 &= lambda f : tau_1 -> tau_2. lambda x : tau_3. (f space (x : tau_3 <: tau_1) :> tau_4) \

  tau_1 = tau_2 :> tau_3 = tau_4 &= lambda w : tau_1 = tau_2. ??
$

$
  #proof-tree(
    rule(
      $Gamma tack [Psi_1]A ~ B space [Psi_2]$, 
      $Gamma tack A ~ B space [Psi_1, Psi_2]$
    )
  )
$