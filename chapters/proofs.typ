#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: thmrules



Constraints:
$
  Con in.rev C &::= ctrue | cfalse | C_1 and C_2 | tau_1 = tau_2 | exists alpha. C | forall alpha. C \ 
  &space | cdef x : sigma cin C | x <= tau | sigma <= tau \ 
  &space | clet x : sigma cin C  \ \ 
  Scm in.rev sigma &::= forall overline(alpha : f). C => tau \ \ 
  Ty in.rev tau &::= alpha | 1 | tau -> tau \ \
  f &::= frigid | fflex \ \ 
  GTy in.rev gt &::= 1 | gt -> gt \ \ 
  GScm in.rev gs &in cal(P)(GTy) \ \
  phi &::= dot | phi[alpha |-> gt] \ \ 
  rho &::= dot | rho[x |-> gs] 

  #v1
$

$
  #proof-tree(
    rule(
      $phi, rho tack ctrue$, 
      $$
    )
  )

  #h1 


$




ML:
$
  Exp in.rev e &::= x | lambda x. e | e space e | () | elet x = e ein e | Lambda alpha. e | (e : tau) \ \ 
  Ctx in.rev Gamma &::= dot | Gamma, x : sigma | Gamma, alpha :: f \ \
  Scm in.rev sigma &::= tau | tforall(alpha) sigma \
  #v1
$

$
  #proof-tree(
    rule(
      $Gamma tack x : tau[overline(alpha := tau')]$, 
      $x : tforall(overline(alpha)) tau in Gamma$, 
      $Gamma tack overline(tau') ok$
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
      $Gamma tack tau_1 ok$ 
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : tau_2$, 
      $Gamma, overline(alpha :: fflex) tack e_1 : tau_1$, 
      $overline(alpha) disjoint Gamma$, 
      $Gamma, x : tforall(overline(alpha)) tau_1 tack e_2 : tau_2$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau$,
      $Gamma tack e : tau$,
      $Gamma tack tau rigid$, 
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack Lambda alpha. e : tau[alpha := tau']$, 
      $Gamma, alpha :: frigid tack e : tau$, 
      $alpha disjoint Gamma$, 
      $Gamma tack tau' ok$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack () : 1$, 
      $$
    )
  )
$

Substitutions:

$
  
  Theta ::= dot | Theta, alpha :: kappa \ 
$
A variable is a proof of $kappa in Theta$

Types are wf $Theta tack kappa$

A renaming is between contexts $Theta => Psi$ which states that a variable $alpha :: kappa in Theta$ may be mapped into a variable $rho(alpha) :: kappa in Psi$

A type substitution is between contexts $Theta => Psi$ which maps a variable $alpha :: kappa in Theta$ to a type $Psi tack theta(alpha) :: kappa$. 
Lemma $theta : Theta => Psi$ and $Theta tack tau :: kappa$, then $Psi tack theta(tau) :: kappa$ 

Term contexts $Gamma$ are _indexed_ by $Theta$
$
  #proof-tree(
    rule(
      $dot tack dot ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta, alpha tack Gamma, alpha ok$, 
      $Theta tack Gamma ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta tack Gamma, x : sigma ok$, 
      $Theta tack Gamma ok$, 
      $Theta tack sigma ok$
    )
  )
$


A context substitution is between term contexts $Gamma => Delta$
$
  #proof-tree(
    rule(
      $(Xi, alpha = tau) : (Gamma, alpha) => Delta$, 
      $Xi : Gamma => Delta$, 
      $Delta tack tau ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $(Xi, alpha) : (Gamma, alpha) => (Delta, alpha)$, 
      $Xi : Gamma => Delta$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $(Xi, x) : (Gamma, x : sigma) => (Delta, x : sigma')$, 
      $Xi : Gamma => Delta$, 
      $[Xi]sigma = [Xi]sigma'$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $dot : dot => dot$,
    )
  )
$

If $Theta$ indexes $Gamma$, then $Psi <= Theta$ (thinning) indexes $Delta$. 

#comment[Problem with above definition is it doesn't permit us to introduce existentials -- which is necessary for reasoning about unifiers e.g. $theta$ is a unifier of $exists alpha. C$]


Could we just assume $theta(Gamma) ok$? 

How to show $theta'(Gamma) tack theta'(alpha_1) ok$. 













$
  Theta &::= dot | Theta, alpha :: f | Theta, alpha :: fflex := tau \ \ 
  [Theta]alpha &= cases(
    [Theta]tau #h1&"if" alpha :: fflex := tau in Theta, 
    alpha &"otherwise"
  ) \ 
  [Theta]1 &= 1 \ 
  [Theta](tau_1 -> tau_2) &= [Theta]tau_1 -> [Theta]tau_2 \
  [Theta](tforall(alpha) sigma) &= tforall(alpha) [Theta]sigma
$


#let Assn = textsf("Assn")

Unifiers:
- We write $phi tack C$ for $phi, dot tack C$

- A context substitution $Theta$ is a unifier of $C$ if 
$
  forall phi in Assn. wide phi in [| Theta |] ==> phi tack C
$

- $[| Theta |]$ is given by 
$
  [| dot |] &= Assn \ 
  [| Theta, alpha :: fflex := tau |] &= { phi : phi in [| Theta |] and phi(alpha) = phi(tau) }\ 
  [| Theta, alpha :: f |] &= { phi : phi in [| Theta |] and alpha in dom(phi) } \ 
$

- $Theta$ is most general for $C$ if
$
  forall phi. wide phi in [| Theta |] <==> phi tack C
$

#theorem[_Constraint generation is sound with respect to the ML typing judgements_][
  If $Theta$ is a unifier of $[| e : tau |]$ and $Theta tack tau ok$ then $[Theta]Theta tack e : [Theta]tau$ holds.  
]
#proof[
  We proceed by structural induction on $e$. 

  - *Case* $x$
  1. Let us assume $Theta$ is a unifier of $[| x : tau |]$
  2. $[| x : tau |] = x <= tau$
  3. Wlog, $x : sigma in Theta$ and $sigma = tforall(overline(alpha)) tau$
  4. 



  - *Case* $lambda x. e$
  + Let us assume $Theta$ is a unifier of $[| lambda x. e : tau |]$ 
  + $[| lambda x.e |] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |]$
  + $Theta' >= Theta : alpha_1, alpha_2$ s.t $Theta'$ is unifier of $tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |]$
  + $Theta', x : alpha_1$ is a unifier of $[| e : alpha_2 |]$. 
  + Induction (5): $[Theta', x : alpha_1](Theta', x : alpha_1) tack e : [Theta', x : alpha_1]alpha_2$. This is equivalent to $[Theta']Theta', x : [Theta']x: alpha_1 tack e : [Theta']alpha_2$
  + $[Theta']tau = [Theta']alpha_1 -> [Theta']alpha_2$
  + $[Theta']tau = [Theta]tau$. $Theta tack tau ok$, hence $[Theta]Theta tack [Theta]tau ok $
  + So we have $[Theta]Theta tack [Theta']alpha_1 ok$. 
  + Morally, we can have something like $[Theta]Theta, x : [Theta']alpha_1 tack e : [Theta']alpha_2$.
  + So we are done? 
]

