
#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: thmrules

#let rng = textsf("rng")

#let consistent = textsf("consistent")
#let gt = math.upright(math.bold("t"))
#let gs = math.upright(math.bold("s"))



= Definitions

Syntax of Constraints:
$
  C &::= ctrue | cfalse | C_1 and C_2 | tau_1 = tau_2 | exists alpha. tau | cdef x : sigma cin C | x <= tau | sigma <= tau \ 
  &space | clet x : sigma cin C | forall alpha. C \ \ 
  sigma &::= forall overline(alpha : f). C => tau \ \ 
  tau &::= alpha | tau -> tau \ 
  f &::= frigid | fflex
$


Syntax directed ML type system:
$
  #proof-tree(
    rule(
      $Gamma tack x : tau[overline(alpha := tau')]$, 
      $x : forall overline(alpha). tau in Gamma$, 
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : tau_2$, 
      $Gamma tack e_1 : tau_1 -> tau_2$, 
      $Gamma tack e_2 : tau_1$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack lambda x. e : tau_1 -> tau_2$, 
      $Gamma, x : tau_1 tack e : tau_2$, 
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : tau_2$, 
      $Gamma tack e_1 : tau_1$, 
      $overline(alpha) \# Gamma$, 
      $Gamma, x : forall overline(alpha). tau_1 tack e_2 : tau_2$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau$, 
      $Gamma tack e : tau$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack Lambda alpha. e : tau[alpha := tau']$, 
      $Gamma tack e : tau$, 
      $alpha \# Gamma$
    )
  )
$

A _type substitution_ $theta$ is a total function from type variables to types. The domain of $theta$ is some finite subset of variables $cal(V)$ s.t 
$
  forall alpha in.not cal(V). space theta(alpha) = alpha 
$
We write $dom(theta)$ for $cal(V)$ and $rng(theta)$ for $union.big_(alpha in dom(theta)) fv(theta(alpha))$. 


A solved form is a constraint $hat(U)$ of the form $exists overline(alpha). and.big_i beta_i = tau_i$ and $overline(beta) \# fv(overline(tau))$. 

A solved form is _canonical_ when $fv(overline(tau)) subset.eq overline(alpha)$ and $overline(alpha) \# overline(beta)$. (i.e. the free variables are exactly $overline(alpha)$). 

Let $theta$ be an _idempotent_ type substitution of domain $overline(beta)$. We write $exists theta$ for the canonical solved form $exists rng(theta). and.big_i beta_i = theta(beta_i)$.

An idempotent substitution $theta$ is a unifier of $C$ if and only if $exists theta tack.double C$

An idempotent substitution $theta$ is the _most general unifier_ of $C$ if and only if $C equiv exists theta$. 



= Theorems 


#theorem[_ML type judgements are stable under substitution_][
Let $theta$ be a type substitution whose domain is disjoint with $fv(e)$. Then,
$
  Gamma tack e : tau ==> theta(Gamma) tack e : theta(tau)
$
]
#proof[We proceed by structural induction on $e$. 
- *Case* $x$. 
1. Let us assume $Gamma tack x : tau$
2. By inversion, we have $Gamma(x) = forall overline(alpha). tau'$ and $tau = tau' [overline(alpha := tau'')]$. 
3. We have $theta(Gamma)(x) = forall overline(alpha). theta(tau')$ for $overline(alpha) \# theta$. Similarly, note that $theta(tau) = theta(tau')[overline(alpha := theta(tau''))]$. 
4. From (3) + (Var), we have 
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack x : theta(tau') [overline(alpha) := theta(tau'')]$, 
        $theta(Gamma)(x) = forall overline(alpha). theta(tau')$,
      )
    )
  $

- *Case* $lambda x.e$. 
1. Let us assume $Gamma tack lambda x. e : tau$
2. By inversion, we have $Gamma, x : tau_1 tack e : tau_2$ and $tau = tau_1 -> tau_2$. 
3. Note that $theta(tau) = theta(tau_1) -> theta(tau_2)$. 
4. By (3) + Induction, we have $theta(Gamma, x : tau_1) tack e : theta(tau_2)$. Note that $theta(Gamma, x : tau_1) = theta(Gamma), x : theta(tau_1)$. 
5. From (4) + (Lam), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack lambda x. e : theta(tau_2)$, 
      rule(
        $theta(Gamma), x: theta(tau_1) tack e : theta(tau_2)$, 
        $(4)$
      )
    )
  )
$

- *Case* $e_1 space e_2$. 
1. Let us assume $Gamma tack e_1 space e_2 : tau$
2. By inversion, we have $Gamma tack e_1 : tau' -> tau$ and $Gamma tack e_2 : tau'$. 
3. By (2) + Induction, we have $theta(Gamma) tack e_1 : theta(tau' -> tau)$ and $theta(Gamma) tack e_2 : theta(tau')$. \ Note that $theta(tau' -> tau) = theta(tau') -> theta(tau)$. 
4. From (4) + (App), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack e_1 space e_2 : theta(tau)$, 
      rule(
        $theta(Gamma) tack e_1 : theta(tau') -> theta(tau)$, 
        $(4)$
      ), 
      rule(
        $theta(Gamma) tack e_2 : theta(tau')$, 
        $(4)$
      )
    )
  )
$

- *Case* $elet x = e_1 ein e_2$. 
1. Let us assume $Gamma tack elet x = e_1 ein e_2 : tau$. 
2. By inversion, we have $Gamma tack e_1 : tau'$, $overline(alpha) \# Gamma$, and $Gamma, x : forall overline(alpha). tau' tack e_2 : tau$. 
3. By (2) + Induction, we have $theta(Gamma) tack e_1 : theta(tau')$ and $theta(Gamma, x : forall overline(alpha). tau') tack e_2 : theta(tau)$. Without loss of generality $overline(alpha) \# theta$. Note that $theta(Gamma, x : forall overline(alpha). tau') = theta(Gamma), x: forall overline(alpha). theta(tau')$. 
4. By (3) + (Let), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$, 
      rule(
        $theta(Gamma) tack e_1 : theta(tau')$, 
        $(3)$
      ), 
      $overline(alpha) \# theta(Gamma)$, 
      rule(
        $theta(Gamma), x : forall overline(alpha). theta(tau') tack e_2 : theta(tau)$, 
        $(3)$
      )
    )
  )
$


- *Case* $(e : tau')$. 

1. Let us assume $Gamma tack (e : tau') : tau$
2. By inversion, we have $tau' = tau$ and $Gamma tack e : tau$
3. By (2) + Induction, we have $theta(Gamma) tack e : theta(tau)$. 
4. Since $dom(theta) \# fv(tau')$, we have $theta(tau') = tau'$. Hence $theta(tau') = tau' = theta(tau)$. 
5. From (4) + (Annot), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack (e : tau') : theta(tau)$, 
      rule(
        $theta(Gamma) tack e : theta(tau)$, 
        $(4)$
      ), 
      rule(
        $theta(tau) = tau'$, 
        $(4)$
      )
    )
  )
$

- *Case* $Lambda alpha. e$. 

1. Let us assume $Gamma tack Lambda alpha. e : tau$
2. By inversion, we have $Gamma tack e : tau'$, $alpha \# Gamma$, and $tau = tau' [alpha := tau'']$. 
3. Wlog, assume $alpha \# theta, tau''$. By (2) + Induction, we have $theta(Gamma) tack e : theta(tau')$. 
4. We have $alpha \# theta(Gamma)$
5. $theta(tau) = theta(tau'[alpha := tau'']) = theta(tau')[alpha := theta(tau'')]$ since $theta$ doesn't capture $alpha$. 
6. By (3) + (4) + (5) + (TLam), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack Lambda alpha. e : theta(tau)$, 
      rule(
        $theta(Gamma) tack e : theta(tau')$, 
        $(3)$
      ), 
      rule(
        $alpha \# theta(Gamma)$,
        $(4)$
      ), 
      rule(
        $theta(tau) = theta(tau')[alpha := theta(tau'')]$, 
        $(5)$
      )
    )
  )
$
]



// #theorem([_Constraint generation is sound with respect to the typing judgement_])[
//   Assume $fv(e) = dom(Gamma)$. 
//   If $phi(Gamma) tack e : phi(tau)$, then $phi, phi(Gamma) tack [| e : tau |]$.  
// ]
// #proof[
// We proceed by structural induction on $e$. 

//   - *Case* $x$. The derivation $phi(Gamma) tack e : phi(tau)$ has the following form:
//   $
//     #proof-tree(
//       rule(
//         $Gamma' tack x : tau'[overline(alpha := tau'')]$, 
//         $x : forall overline(alpha). tau' in Gamma'$
//       )
//     )
//   $

//   1. We conclude that $phi(Gamma) = Gamma'$ and $phi(tau) = tau'[overline(alpha := tau'')]$. 
  
  
//   2. We have $[| e : tau |] = x <= tau$. 
  
//   3. From 1, we have $x : forall overline(alpha). tau' in phi(Gamma)$, thus $phi(Gamma)(x) = (phi; emptyset)(forall overline(alpha). tau')$.


//   5. $phi, phi(Gamma) tack x <= tau$ iff $phi(tau) in (phi; emptyset) (forall overline(alpha). tau')$. 

//   6. By definition of $(phi; rho) sigma$, we need to show that
//     $
//       phi(tau) = phi'(tau') and phi scripts(=)_(\\ overline(alpha)) phi'
//     $
//     for some $phi'$. 
//     Define $phi' = phi[overline(alpha := tau'')]$. We have $phi(tau) = phi'(tau')$. 
    
//   - *Case* $lambda x. e$. The derivation $phi(Gamma) tack e : phi(tau)$ has the following form:
//   $
//     #proof-tree(
//       rule(
//         $Gamma' tack lambda x. e : tau_1 -> tau_2$, 
//         $Gamma', x : tau_1 tack e : tau_2$
//       )
//     )
//   $

//   1. We conclude that $phi(Gamma) = Gamma'$ and $phi(tau) = tau_1 -> tau_2$ and that $phi(Gamma), x : tau_1 tack e : tau_2$ holds.  
//   2. We have $[| lambda x. e : tau |] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |]$. 
//   3. Let $alpha_1, alpha_2 \# Gamma, phi$ and $phi' = phi[alpha_1 |-> tau_1, alpha_2 |-> tau_2]$. 
//     So we now have $phi'(Gamma, x : alpha_1) tack e : phi'(alpha_2)$ and $phi'(tau) = phi'(alpha_1 -> alpha_2)$. 
//   4. By induction, we have $phi', phi'(Gamma, x : alpha_1) tack [| e : alpha_2 |]$ 
//   5. We have $phi', phi'(Gamma) tack tau = alpha_1 -> alpha_2$. 
//   6. Therefore:
//     $
//       phi', phi'(Gamma) tack tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |]
//     $
//     Using $exists$, we have 
//     $
//       phi, phi(Gamma) tack exists alpha_1, alpha_2. tau= alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |]
//     $


//   - *Case* $e_1 space e_2$. The derivation $phi(Gamma) tack e_1 space e_2 : phi(tau)$ is of the form:
//   $
//     #proof-tree(
//       rule(
//         $Gamma' tack e_1 space e_2 : tau_2$, 
//         $Gamma' tack e_1 : tau_1 -> tau_2$, 
//         $Gamma' tack e_2 : tau_1$
//       )
//     )
//   $

//   1. We conclude that $phi(Gamma) = Gamma'$, $phi(tau) = tau_2$ and that $phi(Gamma) tack e_1 : tau_1 -> phi(tau)$ and $phi(Gamma) tack e_2 : tau_2$ holds. 
//   2. Let $alpha \# Gamma, phi$ and $phi' = phi[alpha |-> tau_2]$. So we have $phi'(Gamma) tack e_2 : phi'(alpha)$. So by induction, we have $phi', phi'(Gamma) tack [| e_2 : alpha |]$. 
//   3. Similarly, we  have $phi'(Gamma) tack e_1 : phi'(alpha -> tau)$. So by induction, we have $phi', phi'(Gamma) tack [| e_1 : alpha -> tau |]$. 
//   4. So we have 
//     $
//       #proof-tree(
//         rule(
//           $phi, phi(Gamma) tack exists alpha. [| e_1 : alpha -> tau |] and [|e_2 : alpha|]$, 
//           rule(
//             $phi', phi(Gamma) tack [| e_1 : alpha -> tau |] and [| e_2 : alpha |]$, 
//             rule(
//               $phi', phi(Gamma) tack [| e_1 : alpha -> tau |]$, 
//               rule(
//                 $phi', phi'(Gamma) tack [| e_1 : alpha -> tau |]$, 
//                 $(3)$
//               )
//             ), 
//             rule(
//               $phi', phi(Gamma) tack [| e_2 : alpha |]$, 
//               rule(
//                 $phi', phi'(Gamma) tack [| e_2 : alpha |]$, 
//                 $(2)$
//               )
//             )
//           )
//         )
//       )
//     $
//     using $phi'(Gamma) = phi(Gamma)$. We are done. 


//   - *Case* $elet x = e_1 ein e_2$. The derivation $phi(Gamma) tack e : phi(tau)$ is of the form:

//     $
//       #proof-tree(
//         rule(
//           $Gamma' tack elet x = e_1 ein e_2 : tau_2$, 
//           $Gamma' tack e_1 : tau_1$, 
//           $overline(alpha) = fv(tau_1) \\ fv(Gamma')$, 
//           $Gamma', x : forall overline(alpha). tau_1 tack e_2 : tau_2$
//         )
//       )      
//     $

//     1. We conclude that $phi(Gamma) = Gamma'$, $phi(tau) = tau_2$ and that $phi(Gamma) tack e_1 : tau_1$ and $phi(Gamma), x : forall overline(alpha). tau_1 tack e_2 : phi(tau)$ holds. 
//     2. Without loss of generality, let $overline(gt)$ be some arbitrary ground types and $phi' = phi[overline(alpha |-> gt)]$. We have $phi'(Gamma) tack e_1 : phi'(tau_1)$ by stability of typing. 

//         Let $beta \# phi(Gamma), psi, overline(alpha)$ and $phi'' = phi'[beta |-> phi'(tau_1)]$. 
//        From (2), we have $phi''(Gamma) tack e_1 : phi''(beta)$. 
//        By the inductive hypothesis, we have $phi'', phi''(Gamma) tack [| e_1 : beta |]$.


//        So we have $phi, phi(Gamma) tack exists (forall beta. [| e_1 : beta|] => beta)$. 

//     4. We now wish to show that $(phi; phi(Gamma)) (forall overline(alpha). tau_1) = (phi; phi(Gamma)) (forall beta. [| e_1 : beta|] => beta)$. 


//       This is equivalent to showing:
//       $
//         &{ tau_1 [overline(alpha := gt)] } = {gt_beta : phi[beta |-> gt_beta], phi(Gamma) tack [| e_1 : beta |]} \

//         &<==> tau_1 [overline(alpha := gt)] = gt_beta and phi[beta |-> gt_beta], phi(Gamma) tack [| e_1 : beta |] \ 


//         &<==> phi[beta |-> tau_1 [overline(alpha := gt)]], phi(Gamma) tack [| e_1 : beta |]

//       $  

//       The argument that $ phi[beta |-> tau_1 [overline(alpha := gt)]], phi(Gamma) tack [| e_1 : beta |]$ is true is given in (3).  

//     5. We have $[| elet x = e_1 cin e_2 : tau |] = clet x : forall beta. [| e_1 : beta|] => beta cin [| e_2 : tau |]$. 

//       From (2), we have $phi, phi(Gamma, x : forall overline(alpha). tau_1) tack e_2 : phi(tau)$, so by induction, we have \ $phi, phi(Gamma, x : forall overline(alpha). tau_1) tack [| e_2 : tau |]$. 

//       From (4), we have $phi, phi(Gamma)[x |-> (phi; phi(Gamma))(forall beta. [| e_1 : beta |] => beta )] tack [| e_2 : tau |]$. 

//       From (2) and the above, we now have 
//       $
//         phi, phi(Gamma) tack clet x : forall beta. [| e_1 : beta |] => beta cin [| e_2 : tau |]
//       $ 
  
// ]

#lemma[If $theta$ is a mgu of $exists overline(alpha). C$, then exists $theta'$ s.t $theta' >= theta : overline(alpha)$ and $theta'$ is the mgu of $C$ ]

// #theorem[
//   If $theta$ is a unifier of $cdef Gamma ein [| e : tau |]$, then $theta(Gamma) tack e : theta(tau)$. 
// ]
// #proof[
//   We proceed by structural induction on $e$.

//   - *Case* $x$. 

//   1. Let us assume $theta$ is a unifier of $cdef Gamma ein [| x : tau|]$
//   2. $[| x : tau |] = x <= tau$
//   3. From (1) + (2), $theta$ is a unifier of $forall overline(alpha). tau' <= tau equiv exists overline(alpha). tau' = tau$. 
//   4. By Lemma 0.1 + (3), there exists $theta'$ s.t $theta >= theta : overline(alpha)$ and $theta'$ is a unifier of $tau' = tau$. Hence $theta'(tau') = theta(tau)$
//   5. Let $overline(tau'')$ be such that $theta'(overline(alpha)) = overline(tau'')$. From (4), we have $ theta (tau') [overline(alpha := tau'')] = theta(tau)$. By (Var), we have 
//   $
//     #proof-tree(
//       rule(
//         $theta(Gamma) tack x : theta(tau') [overline(alpha := tau'')]$,
//         $theta(Gamma)(x) = forall overline(alpha). theta(tau')$  
//       )
//     )
//   $ 

//   - *Case* $lambda x.e$. 
//   1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| lambda x.e : tau|]$
//   2. $[| lambda x.e : tau |] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2|]$
//   3. Wlog $alpha_1, alpha_2 \# Gamma, theta, tau $. So we have
//   $
//     cdef Gamma cin exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |] \ 
//     equiv exists alpha_1, alpha_2. underbrace(tau = alpha_1 -> alpha_2 and cdef Gamma\, x : alpha_1 cin [| e : alpha_2 |], C)
//   $
//   3. By Lemma 0.1, there exists $theta'$ s.t $theta' >= theta : alpha_1, alpha_2$ and $theta'$ is the unifier of $C$. Applying Lemma 0.1 again, $theta'$ is a unifier of $tau = alpha_1 -> alpha_2$ and $cdef Gamma, x : alpha_1 cin [| e : alpha_2 |]$. 

//   4. $theta'(Gamma) = theta(Gamma)$ and $theta'(tau) = theta(tau)$ 

//   5. From (3) + Induction, we have $theta'(Gamma, x : alpha_1) tack e : theta'(alpha_2)$. Note that $theta'(Gamma, x : alpha_1) = theta(Gamma), x : theta'(alpha_1)$. 

//   6. Let $tau_1 = theta'(alpha_1)$ and $tau_2 = theta'(alpha_2)$. Since $theta'$ is idempotent, we have $theta'(tau_i) = tau_i$ and $overline(alpha) \# tau_i$. Since $theta'$ is an extension of $theta$, we have  $theta(tau_i) = tau_i$. Thus $theta(tau) = theta(tau_1) -> theta(tau_2) = tau_1 -> tau_2$.

//   7. By (5) + (6) + (Lam), we have 
//   $
//     #proof-tree(
//       rule(
//         $theta(Gamma) tack lambda x. e : theta(tau_1 -> tau_2)$, 
//         rule(
//           $theta(Gamma), x : tau_1 tack e : tau_2$, 
//           $(5)$,
//         )
//       )
//     )
//   $


//   - *Case* $e_1 space e_2$. 

//   1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| e_1 space e_2 : tau |]$ 
//   2. $[| e_1 space e_2 : tau |] = exists alpha. [| e_1 : alpha -> tau |] and [| e_2 : alpha|]$
//   3. Wlog $alpha \# Gamma, theta, tau$. We have 
//   $
//     cdef Gamma cin exists alpha. [| e_1 : alpha -> tau |] and [| e_2 :  alpha |] &equiv exists alpha. cdef Gamma cin [| e_1 : alpha -> tau|] and [| e_2 : alpha |] \ 
//     &equiv exists alpha. underbrace((cdef Gamma cin [| e_1 : alpha -> tau |]) and (cdef Gamma cin [| e_2 : alpha|]), C)
//   $
//   4. By Lemma 0.1, there exists $theta'$ s.t $theta >= theta : alpha$ and $theta'$ is a unifier of $C$. Similarly, $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha -> tau|]$ and $cdef Gamma cin [| e_2 : alpha |]$. 
//   5. Note that $theta'(Gamma) = theta(Gamma)$, $theta'(tau) = theta(tau)$. 
//   6. From (4) + Induction, we have $theta'(Gamma) tack e_1 : theta'(alpha -> tau)$ and $theta'(Gamma) tack e_2 : theta'(alpha)$. 
//   7. By (5) + (6) + (App), we have 
//   $
//     #proof-tree(
//       rule(
//         $theta(Gamma) tack e_1 space e_2 : theta(tau)$, 
//         rule(
//           $theta(Gamma) tack e_1 : theta'(alpha) -> theta(tau)$, 
//           $(6)$
//         ),
//         rule(
//           $theta(Gamma) tack e_2 : theta'(alpha)$,
//           $(6)$
//         )
//       )
//     )
//   $
  

//   - *Case* $elet x = e_1 ein e_2$. 

//   1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| elet x = e_1 ein e_2 : tau |]$

//   2. $[| elet x = e_1 ein e_2 : tau |] = elet x : forall alpha. [| e_1 : alpha |] => alpha cin [| e_2 : tau |]$

//   3. Wlog $alpha \# Gamma, tau, theta$. We have 
//   $
//     cdef Gamma cin clet x : sigma cin [| e_2 : tau |] &equiv cdef Gamma cin elet x : forall alpha. [| e_1 : alpha |] => alpha cin [| e_2 : tau |] \ 
//     &equiv cdef Gamma cin clet x : underbrace(forall alpha. cdef Gamma cin [| e_1 : alpha |] => alpha, sigma) cin [| e_2 : tau |] \ 
//     &equiv cdef Gamma cin exists sigma and cdef x : sigma cin [| e_2 : tau |] \ 
//     &equiv exists sigma and cdef Gamma, x : sigma cin [| e_2 : tau |]
//   $

//   4. From (3), we conclude that $theta$ is a unifier of $exists sigma$ and $cdef Gamma, x : sigma cin [| e_2 : tau |]$. 

//   5. By Lemma 0.2, exists $theta'$ s.t $theta' >= theta : alpha$ and $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha|]$. Let $overline(beta) = fv(theta'(alpha)) \\ rng(theta)$, by Lemma 0.2, $sigma$ is equivalent to $forall overline(beta). theta'(alpha)$. 

//   6. Note that $theta'(Gamma) = theta(Gamma)$. 

//   7. By (5) + Induction, we have $theta'(Gamma) tack e_1 : theta'(alpha)$. 

//   8. By (4) + Induction, we have $theta(Gamma, x : sigma) tack e_2 : theta(tau)$

//   9. We note that $theta(Gamma, x : sigma) = theta(Gamma), x :  theta(sigma)$. Note that $theta(sigma) = theta(forall overline(beta). theta'(alpha)) = forall overline(beta). theta (theta'(alpha))$ as $overline(beta) \# rng(theta)$. Since $theta'$ extends $theta$ and $theta$ is idempotent, we have  $theta(theta'(alpha)) = theta'(alpha)$. 

//   10. Since $overline(beta) \# rng(theta)$, it follows that $overline(beta) \# theta(Gamma)$.

//   11. By (6) + (7), we have $theta(Gamma) tack e_1 : theta'(alpha)$

//   12. By (8) + (9), we have $theta(Gamma), x : forall overline(beta). theta'(alpha) tack e_2 : theta(tau)$

//   13. By (10) + (11) + (12) + (Let), we have 
//   $
//     #proof-tree(
//       rule(
//         $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$, 
//         rule(
//           $theta(Gamma) tack e_1 : theta'(alpha)$, 
//           $(11)$
//         ), 
//         rule(
//           $overline(beta) \# theta(Gamma)$, 
//           $(10)$
//         ), 
//         rule(
//           $theta(Gamma), x : forall overline(beta). theta'(alpha) tack e_2 : theta(tau)$,
//           $(12)$ 
//         )
//       )
//     )
//   $
// ]


#theorem[_Constraint generation is sound and complete with respect to the ML typing judgements_][
  Let $theta$ be a type substitution whose domain is disjoint from $fv(e)$. Then, $theta$ is a unifier of $cdef Gamma cin [| e : tau |]$ if and only if $theta(Gamma) tack e : theta(tau)$ holds.  
]
#proof[
  We proceed by structural induction on $e$. 

  - *Case* $x$. 

  Forwards: $theta$ is unifier of $cdef Gamma cin [| x : tau |] ==> theta(Gamma) tack x : theta(tau)$ 
  
  1. Let us assume $theta$ is a unifier of $cdef Gamma ein [| x : tau|]$
  2. $[| x : tau |] = x <= tau$
  3. Note that 
    $
      cdef Gamma cin x <= tau &equiv cdef Gamma cin Gamma(x) <= tau \ 
      &equiv Gamma(x) <= tau
    $
    Wlog $Gamma(x) = forall overline(alpha). tau'$ where $overline(alpha) \# Gamma, theta, tau$. So we have 
    $
      Gamma(x) <= tau &= (forall overline(alpha). tau') <= tau \
      &equiv exists overline(alpha). tau' = tau
    $  
  4. From (1) + (3), $theta$ is a unifier of $exists overline(alpha). tau' = tau$. 
  5. By Lemma 0.1 + (4), there exists $theta'$ s.t $theta >= theta : overline(alpha)$ and $theta'$ is a unifier of $tau' = tau$. Hence $theta'(tau') = theta(tau)$
  6. Let $overline(tau'')$ be such that $theta'(overline(alpha)) = overline(tau'')$. From (5), we have $ theta (tau') [overline(alpha := tau'')] = theta(tau)$. By (Var), we have 
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack x : theta(tau') [overline(alpha := tau'')]$,
        $theta(Gamma)(x) = forall overline(alpha). theta(tau')$  
      )
    )
  $ 

  Backwards: $theta(Gamma) tack x : theta(tau) ==>$ $theta$ is a unifier of $cdef Gamma cin [| x : tau |]$

  1. Let us assume $theta(Gamma) tack x : theta(tau)$. 
  2. By inversion, we have $theta(Gamma)(x) = forall overline(alpha). tau'$ and $theta(tau) = tau'[overline(alpha := tau'')]$
  3. We wish to show that $theta$ is a unifier of $cdef Gamma cin [| x : tau|]$. By Forwards (3), it is sufficient to show that $theta$ is a unifier of $exists overline(alpha'). tau' = tau$. 
  4. Wlog $overline(alpha) \# Gamma, theta, tau$. 
  
    By Lemma 0.1 + (3), it is sufficient to show that there exists some unifier $theta'$ s.t $theta' >= theta : overline(alpha)$ and $theta'$ is a unifier of $tau' = tau$. 

    Let us define $theta'$ s.t 
    $
      theta'(beta) &= cases(
        theta(beta) #h1 &"if" beta in dom(theta), 
        tau''_beta &"if" beta in overline(alpha)
      )
    $

    Since $theta$ is idempotent, $theta(tau') = tau'$. Since $theta'$ extends $theta$, we have $theta'(tau) = theta(tau)$. So we have 
    $
      theta'(tau) = theta'(tau') \ 
      <==> theta(tau) = tau' [overline(alpha := tau')]
    $
    By (2), this holds 

  5. By (4) + (3), $theta$ is a unifier of $cdef Gamma cin [| x : tau |]$



  - *Case* $lambda x. e$. 
  

  Forwards: $theta$ is a unifier of $cdef Gamma cin [| lambda x. e : tau |] ==> theta(Gamma) tack lambda x. e : theta(tau)$
  1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| lambda x.e : tau|]$
  2. $[| lambda x.e : tau |] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2|]$
  3. Wlog $alpha_1, alpha_2 \# Gamma, theta, tau $. So we have
  $
    cdef Gamma cin exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |] \ 
    equiv exists alpha_1, alpha_2. underbrace(tau = alpha_1 -> alpha_2 and cdef Gamma\, x : alpha_1 cin [| e : alpha_2 |], C)
  $
  3. By Lemma 0.1, there exists $theta'$ s.t $theta' >= theta : alpha_1, alpha_2$ and $theta'$ is the unifier of $C$. Applying Lemma 0.1 again, $theta'$ is a unifier of $tau = alpha_1 -> alpha_2$ and $cdef Gamma, x : alpha_1 cin [| e : alpha_2 |]$. 

  4. $theta'(Gamma) = theta(Gamma)$ and $theta'(tau) = theta(tau)$ 

  5. From (3) + Induction, we have $theta'(Gamma, x : alpha_1) tack e : theta'(alpha_2)$. Note that $theta'(Gamma, x : alpha_1) = theta(Gamma), x : theta'(alpha_1)$. 

  6. Let $tau_1 = theta'(alpha_1)$ and $tau_2 = theta'(alpha_2)$. Since $theta'$ is idempotent, we have $theta'(tau_i) = tau_i$ and $overline(alpha) \# tau_i$. Since $theta'$ is an extension of $theta$, we have  $theta(tau_i) = tau_i$. Thus $theta(tau) = theta(tau_1) -> theta(tau_2) = tau_1 -> tau_2$.

  7. By (5) + (6) + (Lam), we have 
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack lambda x. e : theta(tau_1 -> tau_2)$, 
        rule(
          $theta(Gamma), x : tau_1 tack e : tau_2$, 
          $(5)$,
        )
      )
    )
  $

  Backwards: $theta(Gamma) tack lambda x.e : theta(tau) ==>$ $theta$ is a unifier of $cdef Gamma cin [| lambda x. e : tau |]$

  1. Let us assume $theta(Gamma) tack lambda x. e : theta(tau)$

  2. By inversion, we have $theta(Gamma), x : tau_1 tack e : tau_2$ and $theta(tau) = tau_1 -> tau_2$

  3. By Forwards (3), it is sufficient to show that $theta$ is a unifier of $exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef Gamma, x : alpha_1 cin [|e : alpha_2 |]$ for $alpha_1, alpha_2 \# Gamma, theta, tau$
  4. By Lemma 0.1, it is sufficient to show that there exists $theta'$ s.t $theta' >= theta : alpha_1, alpha_2$ and $theta'$ is a unifier of $C$. 

  5. Let $theta'$ be defined as an extension of $theta$ s.t $theta'(alpha_i) = tau_i$. 

    $theta'$ is a unifier of $C$ if $theta'$ is a unifier of $tau = alpha_1 -> alpha_2$ and $cdef Gamma, x : alpha_1 cin [| e : alpha_2 |]$. 

  6. Note that $theta'(Gamma, x : alpha_1) = theta'(Gamma), x : theta'(alpha_1) = theta(Gamma), x : tau_1$. Similarly, $theta'(alpha_2) = tau_2$. Therefore by (2), we have $theta'(Gamma, x : alpha_1) tack e : theta'(alpha_2)$.

  7. By (6) + Induction, we have $theta'$ is a unifier of $cdef Gamma, x : alpha_1 cin [| e : alpha_2 |]$. 

  8. $theta'$ is a unifier of $tau = alpha_1 -> alpha_2$ if and only if 
    $
      theta'(tau) = theta'(alpha_1 -> alpha_2) \ 
      <==> theta(tau) = tau_1 -> tau_2 
    $
    By (2), this holds. 

  9. By (7) + (8) + (5) + (4), $theta$ is a unifier of $cdef Gamma cin [| lambda x. e : tau |]$



  - *Case* $e_1 space e_2$. 

  Forwards: $theta$ is a unifier of $cdef Gamma cin [| e_1 space e_2 : tau |] ==> theta(Gamma) tack e_1 space e_2 : theta(tau)$
  1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| e_1 space e_2 : tau |]$ 
  2. $[| e_1 space e_2 : tau |] = exists alpha. [| e_1 : alpha -> tau |] and [| e_2 : alpha|]$
  3. Wlog $alpha \# Gamma, theta, tau$. We have 
  $
    cdef Gamma cin exists alpha. [| e_1 : alpha -> tau |] and [| e_2 :  alpha |] &equiv exists alpha. cdef Gamma cin [| e_1 : alpha -> tau|] and [| e_2 : alpha |] \ 
    &equiv exists alpha. underbrace((cdef Gamma cin [| e_1 : alpha -> tau |]) and (cdef Gamma cin [| e_2 : alpha|]), C)
  $
  4. By Lemma 0.1, there exists $theta'$ s.t $theta >= theta : alpha$ and $theta'$ is a unifier of $C$. Similarly, $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha -> tau|]$ and $cdef Gamma cin [| e_2 : alpha |]$. 
  5. Note that $theta'(Gamma) = theta(Gamma)$, $theta'(tau) = theta(tau)$. 
  6. From (4) + Induction, we have $theta'(Gamma) tack e_1 : theta'(alpha -> tau)$ and $theta'(Gamma) tack e_2 : theta'(alpha)$. 
  7. By (5) + (6) + (App), we have 
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack e_1 space e_2 : theta(tau)$, 
        rule(
          $theta(Gamma) tack e_1 : theta'(alpha) -> theta(tau)$, 
          $(6)$
        ),
        rule(
          $theta(Gamma) tack e_2 : theta'(alpha)$,
          $(6)$
        )
      )
    )
  $

  Backwards: $theta(Gamma) tack e_1 space e_2 : theta(tau) ==> theta$ is a unifier of $cdef Gamma cin [| e_1 space e_2 : tau |]$

  1. Let us assume $theta(Gamma) tack e_1 space e_2 : theta(tau)$

  2. By inversion, we have $theta(Gamma) tack e_1 : tau' -> theta(tau)$ and $theta(Gamma) tack e_2 : tau'$

  3. By Forwards (3), it is sufficient to show that $theta$ is a unifier of $exists alpha. (cdef Gamma cin [| e_1 : alpha -> tau|]) and (cdef Gamma cin [| e_2 : alpha |])$ for $alpha \# Gamma, theta, tau$

  4. By (3) + Lemma 0.1, it is sufficient to show there exists $theta'$ s.t $theta' >= theta : alpha$ and $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha -> tau |]$ and $cdef Gamma cin [| e_2 : alpha |]$. 

  5. Let us define $theta'$ to extend $theta$ with $theta'(alpha) = tau'$. 

    We note that $theta'(Gamma) = theta(Gamma)$ and $theta'(alpha -> tau) = tau' -> theta(tau)$. So by (2), we have $theta'(Gamma) tack e_1 : theta'(alpha -> tau)$. 

  6. By (5) + Induction, we have $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha -> tau |]$.

  7. Similarly, we have $theta'(Gamma) tack e_2 : theta'(alpha)$. So by Induction, we have $theta'$ is a unifier of $cdef Gamma cin [| e_2 : alpha |]$

  8. By (6) + (7) + (4) + (3), we have that $theta$ is a unifier of $cdef Gamma cin [| e_1 space e_2 : tau|]$



  - *Case* $elet x = e_1 ein e_2$. 

  Forwards: $theta$ is a unifier of $cdef Gamma cin [| elet x = e_1 ein e_2 : tau|] ==> theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$

  1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| elet x = e_1 ein e_2 : tau |]$

  2. $[| elet x = e_1 ein e_2 : tau |] = elet x : forall alpha. [| e_1 : alpha |] => alpha cin [| e_2 : tau |]$

  3. Wlog $alpha \# Gamma, tau, theta$. We have 
  $
    cdef Gamma cin clet x : sigma cin [| e_2 : tau |] &equiv cdef Gamma cin elet x : forall alpha. [| e_1 : alpha |] => alpha cin [| e_2 : tau |] \ 
    &equiv cdef Gamma cin clet x : underbrace(forall alpha. cdef Gamma cin [| e_1 : alpha |] => alpha, sigma) cin [| e_2 : tau |] \ 
    &equiv cdef Gamma cin exists sigma and cdef x : sigma cin [| e_2 : tau |] \ 
    &equiv exists sigma and cdef Gamma, x : sigma cin [| e_2 : tau |]
  $

  4. From (3), we conclude that $theta$ is a unifier of $exists sigma$ and $cdef Gamma, x : sigma cin [| e_2 : tau |]$. 

  5. By Lemma 0.2, exists $theta'$ s.t $theta' >= theta : alpha$ and $theta'$ is a unifier of $cdef Gamma cin [| e_1 : alpha|]$. Let $overline(beta) = fv(theta'(alpha)) \\ rng(theta)$, by Lemma 0.2, $sigma$ is equivalent to $forall overline(beta). theta'(alpha)$. 

  6. Note that $theta'(Gamma) = theta(Gamma)$. 

  7. By (5) + Induction, we have $theta'(Gamma) tack e_1 : theta'(alpha)$. 

  8. By (4) + Induction, we have $theta(Gamma, x : sigma) tack e_2 : theta(tau)$

  9. We note that $theta(Gamma, x : sigma) = theta(Gamma), x :  theta(sigma)$. Note that $theta(sigma) = theta(forall overline(beta). theta'(alpha)) = forall overline(beta). theta (theta'(alpha))$ as $overline(beta) \# rng(theta)$. Since $theta'$ extends $theta$ and $theta$ is idempotent, we have  $theta(theta'(alpha)) = theta'(alpha)$. 

  10. Since $overline(beta) \# rng(theta)$, it follows that $overline(beta) \# theta(Gamma)$.

      #comment[I don't see how this follows]

  11. By (6) + (7), we have $theta(Gamma) tack e_1 : theta'(alpha)$

  12. By (8) + (9), we have $theta(Gamma), x : forall overline(beta). theta'(alpha) tack e_2 : theta(tau)$

  13. By (10) + (11) + (12) + (Let), we have 
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$, 
        rule(
          $theta(Gamma) tack e_1 : theta'(alpha)$, 
          $(11)$
        ), 
        rule(
          $overline(beta) \# theta(Gamma)$, 
          $(10)$
        ), 
        rule(
          $theta(Gamma), x : forall overline(beta). theta'(alpha) tack e_2 : theta(tau)$,
          $(12)$ 
        )
      )
    )
  $

  Backwards: $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau) ==>$ $theta$ is a unifier of $cdef Gamma cin [| elet x = e_1 ein e_2 : tau |]$

  1. Let us assume $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$

  2. By inversion, we have $theta(Gamma) tack e_1 : tau'$, $overline(alpha) = fv(tau') \\ fv(theta(Gamma))$, and $theta(Gamma), x : forall overline(alpha). tau' tack e_2 : theta(tau)$

  3. Since $theta$ is idempotent, it follows that $theta(tau') = tau'$ and $overline(alpha) \# dom(theta)$. Hence $theta(forall overline(alpha). tau') = forall overline(alpha). tau'$

  4. By (2) + (3), we have $theta(Gamma, x : forall overline(alpha). tau') tack e_2 : theta(tau)$. By Induction, we have $theta$ is a unifier of $cdef Gamma, x : forall overline(alpha). tau' cin [| e_2 : tau |]$. 

  5. Let us define $theta'$ which extends $theta$ where $theta'(beta) = tau'$ , wlog. $beta \# Gamma, theta, tau, tau'$. 

    From (2), we have $theta'(Gamma) tack e _1 : theta'(beta)$ since $theta'(Gamma) = theta(Gamma)$. 
    By Induction, we have $theta'$ is a unifier of $cdef Gamma cin [| e_1 : beta |]$.

  6. By Lemma 0.1, $theta$ is a unifier for $exists beta. cdef Gamma cin [| e_1 : beta |]$. 

  7. We show that $forall overline(alpha). tau'$ and $forall beta. cdef Gamma cin [| e_1 : beta |] => beta$ are equivalent under $theta$. 

    Let $phi, rho$ be arbitrary. Assume $phi tack exists theta$. 
    That is 
    $
      &{ tau' [overline(alpha := gt)]} = { gt_beta : phi[beta |-> gt_beta], rho tack cdef Gamma cin [| e_1 : beta |]} \
      &<==> tau' [overline(alpha := gt)] = gt_beta and phi[beta |-> gt_beta], rho tack cdef Gamma cin [| e_1 : beta |] \ 
      &<==> phi[beta |-> tau' [overline(alpha := gt)]], rho tack cdef Gamma cin [| e_1 : beta |]
    $



    Let $overline(gt)$ be arbitrary ground types (without loss of generality).
    
    Define $theta''$ to extend $theta$ with $[overline(alpha := gt)]$. By stability of typing + (2), we have $theta''(Gamma) tack e_1 : theta''(tau')$. Note that $theta''(Gamma) = theta(Gamma)$. 

    Define $theta'''$ to extend $theta''$ with $beta |-> theta''(tau')$. So we have $theta'''(Gamma) tack e_1 : theta'''(beta)$. By Induction, we have that $theta'''$ is a unifier of $cdef Gamma cin [| e_1 : beta |]$. 

    Since $phi tack exists theta$, then $phi[beta |-> theta'''(beta)] tack exists theta'''$. Hence $phi[beta |-> theta'''(beta)] tack cdef Gamma cin [| e_1 : beta |]$. 
     
     #comment[This part of the proof isn't v nice -- can we improve it?]

  8. By (7) + (4), $theta$ is a unifier of $cdef Gamma, x : sigma cin [| e_2 : tau  |]$

  9. By (6) and (8), $theta$ is a unifier of $exists sigma and cdef Gamma, x : sigma cin [| e_2 : tau |]$. 


  10. By Forward (3) + (9), $theta$ is a unifier of $cdef Gamma cin [| elet x = e_1 ein e_2 : tau |]$. 


- *Case* $(e : tau')$

Forwards: $theta$ is a unifier of $cdef Gamma cin [| (e : tau') : tau |] ==> theta(Gamma) tack (e : tau') : theta(tau)$

1. Let us assume $theta$ is a unifier of $cdef Gamma cin [| (e : tau') : tau |]$
2. $[| (e : tau') : tau |] = [| e : tau' |] and tau' = tau$
3. Note that 
  $
    cdef Gamma cin ([| e : tau' |] and tau' = tau) equiv (cdef Gamma cin [| e : tau'|]) and tau' = tau 
  $
  Hence $theta$ is a unifier of $cdef Gamma cin [| e : tau' |]$ and $tau' = tau$

4. By (3), we have $theta(tau') = theta(tau)$
5. By (3) + Induction, we have $theta(Gamma) tack e : theta(tau')$
6. Since $dom(theta) \# fv((e : tau'))$, we have $theta(tau') = tau'$
6. By (Annot), we have 
$
  #proof-tree(rule(
    $theta(Gamma) tack (e : tau') : theta(tau)$, 
    rule(
      $theta(Gamma) tack e : theta(tau')$, 
      $(5)$
    ), 
    rule(
      $theta(tau') = theta(tau) = tau'$, 
      $(4), (6)$  
    )
  ))
$

Backwards: $theta(Gamma) tack (e : tau') : theta(tau) ==> theta$ is a unifier of $cdef Gamma cin [| (e : tau') : tau |]$
1. Let us assume that $theta(Gamma) tack (e : tau') : theta(tau)$ holds 
2. By inversion, we have $theta(Gamma) tack e : theta(tau')$ and $theta(tau) = tau'$
3. By Forwards (3), it is sufficient to show that $theta$ is a unifier for $cdef Gamma cin [| e : tau' |]$ and $tau' = tau$
4. By (2) + Induction, we have $theta$ is a unifier for $cdef Gamma cin [| e : tau' |]$
5. Since $dom(theta) \# fv((e : tau'))$, we have $theta(tau') = tau'$. By (2), we have $theta(tau') = theta(tau)$
6. By (5), $theta$ is a unifier for $tau' = tau$
7. By (3) + (4) + (6), $theta$ is a unifier for $cdef Gamma cin [| (e : tau') : tau |]$

- *Case* $Lambda alpha. e$
Forwards: $theta$ is a unifier of $cdef Gamma cin [| Lambda alpha. e : tau |] ==> theta(Gamma) tack Lambda alpha. e : theta(tau)$
1. Let us assume that $theta$ is a unifier of $cdef Gamma cin [| Lambda alpha. e : tau |]$
2. $[| Lambda alpha. e : tau |] = clet x : forall alpha : frigid, beta : fflex. [| e : beta |] => beta cin x <= tau $
3. Wlog $beta \# Gamma, tau, theta, e$. We have 
  $
    cdef Gamma cin clet x : forall alpha : frigid, beta : fflex. [| e : beta |] => beta cin x <= tau &equiv cdef Gamma cin (forall alpha. exists beta. [| e : beta |]) and cdef x : forall alpha, beta. [| e: beta |] => beta cin x <= tau \ 
    &equiv underbrace((forall alpha. exists beta. cdef Gamma cin [| e : beta |]), exists sigma) and sigma <= tau 
  $
  Hence $theta$ is a unifier for $exists sigma$ and $sigma <= tau$.

4. By Lemma 0.2, there exists a unifier $theta' >= theta : alpha, beta$ s.t $theta'(alpha) = alpha$, and $theta'$ is a unifier of $cdef Gamma cin [| e_1 : beta |]$. 
   Let $overline(gamma) = fv(theta'(beta)) \\ rng(theta)$. By Lemma 0.2, $sigma$ is equivalent to $forall alpha, overline(gamma). theta'(beta)$. 

5. By Lemma 0.3, $theta(tau)$ is an instance of $forall alpha, overline(gamma). theta'(beta)$

6. By (4) + Induction, we have $theta'(Gamma) tack e_1 : theta'(beta)$. Since $theta'(Gamma) = theta(Gamma)$, we have $theta(Gamma) tack e_1 : theta'(beta)$. 

7. Wlog $alpha \# theta(Gamma)$ (since we can alpha-rename)

8. By (5), $theta(tau) = phi(theta'(beta))[alpha := tau']$ where $dom(phi) subset.eq overline(gamma)$. 

9. Since $dom(theta) \# overline(gamma)$, $phi(theta(Gamma)) = theta(Gamma)$. By (6) + stability of typing, we have $theta(Gamma) tack e : phi(theta'(beta))$ 

10. By (9) + (8) + (TFun), we have 
$
  #proof-tree(
    rule(
      $theta(Gamma) tack Lambda alpha. e : theta(tau)$, 
      rule(
        $theta(Gamma) tack e : phi(theta'(beta))$, 
        $(9)$
      ), 

      rule(
        $theta(tau) = phi(theta'(beta))[alpha := tau']$, 
        $(8)$
      )
    )
  )
$
Backwards: $theta(Gamma) tack Lambda alpha. e : theta(tau) ==> theta$ is a unifier of $cdef Gamma cin [| Lambda alpha. e : tau |]$
1. Let us assume $theta(Gamma) tack Lambda alpha. e : theta(tau)$ holds 
2. By inversion, we have $alpha \# theta(Gamma)$, $theta(Gamma) tack e : tau'$, $theta(tau) = tau'[alpha := tau'']$
3. Since $theta$ is idempotent, $theta(theta(tau)) = theta(tau')[alpha := theta(tau'')] = theta(tau)$, as $alpha \# dom(theta)$. 
4. By (2) + stability of typing, we have $theta(Gamma) tack e : theta(tau')$
5. By (4) + Induction, we have $theta$ is a unifier of $cdef Gamma cin [| e : tau' |]$. 
6. Define $theta'$ to extend $theta$ on $beta$ s.t $theta'(beta) = tau'$. Hence $theta'$ is a unifier of $cdef Gamma cin [| e : beta |]$. By Lemma ??, $theta$ is a unifier of $exists beta. cdef Gamma cin [| e : beta |]$. 
7. Since $alpha in.not dom(theta)$, by Lemma ??, $theta$ is a unifier for $forall alpha. exists beta. cdef Gamma cin [| e : beta |]$
8. We now show that $theta$ is a unifier of $sigma <= tau$. 
  This is equivalent to $exists alpha, beta. cdef Gamma cin [| e : beta |] and beta = tau$

  Let us define $theta''$ to extend $theta$ on $alpha, beta$ s.t $theta''(alpha) = theta(tau'')$ and $theta''(beta) = theta(tau') [alpha := theta(tau'')]$. By (4) + stability of typing, we have $theta''(Gamma) tack e : theta''(beta)$. By Induction, $theta''$ is a unifier of $cdef Gamma cin [| e : beta |]$. 

  Additionally $theta''$ is the unifier of $beta = tau$ since $theta''(beta) = theta(tau')[alpha := theta(tau'')] = theta''(tau) = theta(tau)$. 

9. By (7) + (8), $theta$ is a unifier of $cdef Gamma cin [| Lambda alpha. e : tau |]$
]



#theorem[_Constraint generation is sound and complete with respect to the ML typing judgements_][
  $phi, phi(Gamma) tack [| e : tau |]$ if and only if $phi(Gamma) tack e : phi(tau)$
]
#proof[Follows from Theorem 0.2]





== Ideas


Scopes idea:
Polymorphic variables cannot have implicit eliminators (and therefore cannot appear under scopes). 
This is akin to flexization, where we require all (top-level) instances of a rigid variable to have no additional scopes. 

This means something like
```ocaml
let foo x = 
  let y = (x : int) in 
  ...
```
could have the type:
```
elim-s:(['s] => []) -> ['s]int -> ...
```

But something like:
```ocaml
let foo (type a) (x : a) = ...
```
must have the type 
```
'a -> ...
```

I like this approach more than flexization, since it should hold for all polymorphic variables (not just rigid ones). 


We can formalize this via 'dangerous variables'


#let dangerous = $textsf("dangerous")_square$
#let tunit = $textsf("unit")$
$
  #proof-tree(
    rule(
      $Gamma tack e : sigma$, 
      $Gamma(x) = sigma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack lambda x. e : tau_1 -> tau_2$,
      $Gamma tack tau_1 ok$, 
      $Gamma, x : tau_1 tack e : tau_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : tau_2$, 
      $Gamma tack e_1 : tau_1 -> tau_2$, 
      $Gamma tack e_2 : tau_2$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : sigma_2$, 
      $Gamma tack e_1 : sigma_1$, 
      $Gamma, x : sigma_1 tack e_2 : sigma_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack e : forall alpha. sigma$, 
      $Gamma, alpha tack e : sigma$,
      $alpha in.not dangerous(sigma)$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack e : forall sigma.alt. sigma$, 
      $Gamma, sigma.alt tack e : sigma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack e : sigma[alpha := tau]$, 
      $Gamma tack e : forall alpha. sigma$, 
      $Gamma tack tau ok $
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack e : sigma[sigma.alt := Psi]$, 
      $Gamma tack e : forall sigma.alt. sigma$, 
      $Gamma tack Psi ok$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : forall alpha. alpha = alpha$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : sigma$, 
      $Gamma tack e_1 : ceil(tau_1 = tau_2)$, 
      $Gamma, tau_1 = tau_2 tack e_2 : sigma$, 
      $Gamma tack sigma ok $
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack () : forall sigma.alt. [sigma.alt]tunit$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$, 
      $Gamma tack e : tau_1$, 
      $floor(tau_1) = tau = floor(tau_2)$, 
      $Gamma tack tau_2 ok$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack e : sigma_2$, 
      $Gamma tack e : sigma_1$, 
      $sigma_1 equiv sigma_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack Lambda alpha. e : forall alpha. sigma$, 
      $Gamma, alpha tack e : sigma$, 
      $alpha in.not dangerous(sigma)$
    )
  )
$

What is a dangerous variable? Any variable under a scope
$
  dangerous(alpha) &= emptyset \ 
  dangerous(tunit) &= emptyset \
  dangerous(tau_1 -> tau_2) &= dangerous(tau_1) union dangerous(tau_2) \ 
  dangerous(tau_1 = tau_2) &= dangerous(tau_1) union dangerous(tau_2) \ 
  dangerous([Psi] tau) &= fv(tau) \
  dangerous(forall alpha. sigma) &= dangerous(sigma) \\ {alpha} \ 
  dangerous(forall sigma.alt. sigma) &= dangerous(sigma)
$

What is $equiv$?

We have the axioms:
$
  [Psi](tau_1 -> tau_2) &equiv [Psi]tau_1 -> [Psi]tau_2 \ 
  [Psi](tau_1 = tau_2) &equiv [Psi] tau_1 = [Psi] tau_2 \ 
  tau &equiv [dot] tau \ 
  [Psi]tau &equiv [Psi]tau' &#h(2cm) "if" Psi tack tau = tau' \ 
  [Psi_1][Psi_2]tau &equiv [Psi_1, Psi_2] tau \ 
$
The axioms + standard congruence rules gives $equiv$. 

$floor(dot)$ and $ceil(dot)$ are erasure / insertion of scopes. 


Intuition behind dangerous variables: a generalizable variable under a scope $==>$ unsharing.

Question: How to implement $dangerous$ restriction in constraints. 

Idea: extend the idea to _dangerous_ types -- set of 'sub-types' (subtrees in the tree of a type) that fall under a scope. 

$
  C ::= ... | exists sigma.alt. C | tau in.not dangerous(tau)
$

$
  #proof-tree(
    rule(
      $phi; rho tack tau_1 in.not dangerous(tau_2)$, 
      $phi(tau_1) in.not dangerous(phi(tau_2))$
    )
  )
$

A problem with this formalization, is we could have $alpha = tint and beta = [sigma.alt]tint and alpha in.not dangerous(beta)$ which is a false by this definition. 

The other issue is that we only know for rigid variables that $alpha$ cannot be in a dangerous position. In general, we often do not know which variable is generalizable. 




