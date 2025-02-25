#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: thmrules



Constraints:
$
  Con in.rev C &::= ctrue | cfalse | C_1 and C_2 | tau_1 = tau_2 | exists alpha. C  \ 
  &space | cdef x : sigma cin C | x <= tau | sigma <= tau \ 
  &space | clet x : sigma cin C  \ \ 
  Scm in.rev sigma &::= forall overline(alpha). C => tau \ \ 
  Ty in.rev tau &::= alpha | 1 | tau -> tau \ \
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

  #proof-tree(
    rule(
      $phi, rho tack C_1 and C_2$, 
      $phi, rho tack C_1$, 
      $phi, rho tack C_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $phi, rho tack tau_1 = tau_2$, 
      $phi(tau_1) = phi(tau_2)$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $phi, rho tack exists alpha. C$, 
      $phi[alpha |-> gt], rho tack C$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $phi, rho tack cdef x : sigma cin C$, 
      $phi, rho[x |-> (phi, rho)sigma] tack C$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $phi, rho tack x <= tau$, 
      $phi(tau) in rho(x)$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $phi, rho tack sigma <= tau$, 
      $phi(tau) in (phi, rho)sigma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $phi, rho tack clet x : sigma cin C$, 
      $(phi, rho)sigma eq.not emptyset$, 
      $phi, rho[x |-> (phi, rho)sigma] tack C$ 
    )
  )
$

Interpretation of types under assignment $phi(tau)$ is standard. 
Interpretation of schemes is 
$
  (phi, rho)(cforall(overline(alpha), C, tau)) = { phi'(tau) in GTy : phi' >= phi : overline(alpha) and phi', rho tack C}
$
$
  #proof-tree(
    rule(
      $phi >= phi : dot$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $phi'[alpha |-> gt] >= phi : overline(alpha), alpha$, 
      $phi' >= phi : overline(alpha)$
    )
  )
$



ML:
$
  Exp in.rev e &::= x | lambda x. e | e space e | () | elet x = e_1 ein e_2\ \ 
  Ctx in.rev Gamma &::= dot | Gamma, x : sigma | Gamma, alpha \ \
  Theta &::= dot | Theta, alpha \ \
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
      $Gamma, overline(alpha) tack e_1 : tau_1$, 
      $overline(alpha) disjoint Gamma$, 
      $Gamma, x : tforall(overline(alpha)) tau_1 tack e_2 : tau_2$
    )
  )

  #v1 

  #proof-tree(
    rule(
      $Gamma tack () : 1$, 
      $$
    )
  )
$

Well-formedness: 
#judgement-box($Theta ok$, $Theta tack tau ok$, $Theta tack sigma ok$, $Theta tack Gamma ok$)
$
  #proof-tree(
    rule(
      $dot ok$, 
      $$
    )
  ) 

  #h1 

  #proof-tree(
    rule(
      $Theta, alpha ok$, 
      $Theta ok$, 
      $alpha disjoint Theta$
    )
  )
  
  #v2 

  #proof-tree(
    rule(
      $Theta tack 1 ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta tack alpha ok$, 
      $alpha in Theta$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta tack tau_1 -> tau_2 ok$, 
      $Theta tack tau_1 ok$, 
      $Theta tack tau_2 ok$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $dot tack dot ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta tack Gamma, x : sigma ok $, 
      $Theta tack Gamma ok$, 
      $Theta tack sigma ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Theta, alpha tack Gamma, alpha ok$, 
      $Theta tack Gamma ok$, 
      $alpha disjoint Theta$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Theta tack tforall(alpha) sigma ok $, 
      $Theta, alpha tack sigma ok$, 
      $alpha disjoint Theta$
    )
  )
$

We write $Gamma ok$ to say there exists some $Theta$ s.t $Theta tack Gamma ok$. 
Similarly we write $Gamma tack tau ok$ for exists $Theta$ s.t $Theta tack Gamma ok$ and $Theta tack tau ok$. Ditto for $Gamma tack sigma ok$. 



Constraint Generation:
$
  [| x : tau |] &= x <= tau \ 
  [| e_1 space e_2 : tau |] &= exists alpha. [| e_1 : alpha -> tau|] and [| e : alpha |] \
  [| efun x -> e : tau |] &= exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e : alpha_2 |] \ 
  [| clet x = e_1 ein e_2 : tau |] &= clet x : cforall(alpha, [| e_1 : alpha |], alpha) cin [| e_2 : tau |]  
$



Ordered Substitutions:

$
  Omega &::= dot | Omega, alpha | Omega, alpha := tau
$
$
  [Omega]alpha &= cases(
    [Omega]tau #h1&"if" alpha := tau in Omega, 
    alpha &"otherwise"
  ) \ 
  [Omega]1 &= 1 \ 
  [Omega](tau_1 -> tau_2) &= [Omega]tau_1 -> [Omega]tau_2 \
  [Omega](tforall(alpha) sigma) &= tforall(alpha) [Omega]sigma
$



#let Assn = textsf("Assn")
#let Env = textsf("Env")

Ordered Unifiers:

- A substitution $Omega$ is a unifier of $C$ if 
$
  forall phi in Assn. wide phi in [| Omega |] ==> phi tack C
$

- $[| Omega |]$ is given by 
$
  [| dot |] &= Assn \ 
  [| Omega, alpha := tau |] &= { phi : phi in [| Omega |] and phi(alpha) = phi(tau) }\ 
  [| Omega, alpha |] &= { phi : phi in [| Omega |] and alpha in dom(phi) } \ 
$

- $Omega$ is most general if 
$
  forall phi in Assn. wide phi in [| Omega |] <==> phi tack C
$


Application:
#judgement-box($[Omega]Gamma : Gamma$)
$
  [dot]dot &= dot \ 
  [Omega](Gamma, x : sigma) &= [Omega]Gamma, x : [Omega]sigma \ 
  [Omega, alpha](Gamma, alpha) &= [Omega]Gamma, alpha \ 
  [Omega, alpha := tau](Gamma, alpha) &= [Omega]Gamma \ 
  [Omega, alpha]Gamma &= [Omega]Gamma, alpha &"if" alpha in.not dom(Gamma) \ 
  [Omega, alpha := tau]Gamma &= [Omega]Gamma &"if" alpha in.not dom(Gamma) 
$
#judgement-box($[Omega]Theta : Theta$)
$
  [dot]dot &= dot \ 
  [Omega, alpha](Theta, alpha) &= [Omega]Theta, alpha \ 
  [Omega, alpha := tau](Theta, alpha) &= [Omega]Theta \ 
  [Omega, alpha]Theta &= [Omega]Theta, alpha &"if" alpha in.not dom(Theta) \ 
  [Omega, alpha := tau]Theta &= [Omega]Theta &"if" alpha in.not dom(Theta)
$



Extension:
#judgement-box($Omega --> Omega'$)
$
  #proof-tree(
    rule(
      $dot --> dot$,
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Omega, alpha --> Omega', alpha$, 
      $Omega --> Omega'$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Omega, alpha := tau --> Omega', alpha := tau'$, 
      $Omega --> Omega'$, 
      $[Omega']tau = [Omega']tau'$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Omega, alpha --> Omega', alpha := tau$,
      $Omega --> Omega'$, 
      $Omega' tack tau ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Omega --> Omega', alpha$,
      $Omega --> Omega'$, 
      $alpha disjoint Omega'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Omega --> Omega', alpha := tau$,
      $Omega --> Omega'$, 
      $Omega' tack tau ok$
    )
  )
$

- We write $Omega tack tau ok$ for $[Omega]dot tack [Omega]tau ok$

- $Omega$ is _soft_ iff it consists only of $alpha$ and $alpha = tau$ declarations 

#let soft = textsf("soft")
#let softex = $scripts(-->)_soft$
$
  #proof-tree(
    rule(
      $Omega softex Omega, Omega'$, 
      $Omega ok$, 
      $Omega' soft$
    )
  )
$

#lemma[Reflexivity and Transitivity][
  + $Omega ok$, then $Omega --> Omega$
  + $Omega --> Omega'$ and $Omega' -> Omega''$, then $Omega --> Omega''$
]

#let generic = textsf("generic")

#lemma[Stability for Well-Formedness][
  For any $Theta ok$ and $Theta --> Omega$, 
  + If $Theta tack tau ok$, then $[Omega]Theta tack [Omega]tau ok$
  + If $Theta tack Gamma ok$, then $[Omega]Theta tack [Omega]Gamma ok$
]

#proof[
  + We proceed by induction on $Theta tack tau ok$
    - *Case* $alpha$
    + Assume $Theta tack alpha ok$
    + By inversion of (Var), we have $alpha in Theta$
    + By extension, $Omega = Omega_L, Omega_alpha, Omega_R$ where $Omega_alpha$ is either $alpha$ or $alpha := tau$
    + Cases on (3)
      - *Case* $Omega_alpha = alpha$
      + Assume $Omega_alpha = alpha$
      + $[Omega]alpha = alpha$
      + $alpha in [Omega]Theta$
      + By (2, 3) we have $[Omega]Theta tack [Omega]alpha ok $
      - *Case* $Omega_alpha = alpha := tau$
      + Assume $Omega_alpha = alpha := tau$ and $Omega_L tack tau ok$
      + $[Omega]alpha = [Omega]tau = [Omega_L]tau$
      + $[Omega_L]dot tack [Omega_L]tau ok$ by (1)
      + $[Omega_L]dot = generic(Omega_L)$
      + $dot --> Omega_L --> Omega$ and $dot --> Theta_L --> Theta$, hence $generic(Omega_L) --> [Omega]Theta$
      + By weakening, $[Omega]Theta tack [Omega]tau ok$

    - *Case* $1$
    + Assume $Theta tack 1 ok$
    + $[Omega]1 = 1$
    + We have $[Omega]Theta tack [Omega]1 ok$

    - *Case* $tau_1 -> tau_2$
    + Assume $Theta tack tau_1 -> tau_2 ok$
    + By inversion, $Theta tack tau_1 ok$ and $Theta tack tau_2 ok$
    + By IH, $[Omega]Theta tack [Omega]tau_1 ok$ and $[Omega]Theta tack [Omega]tau_2 ok$
    + $[Omega](tau_1 -> tau_2) = [Omega]tau_1 -> [Omega]tau_2$
    + We have $[Omega]Theta tack [Omega](tau_1 -> tau_2) ok$ 

  + We proceed by induction on $Theta tack Gamma ok$
    - *Case* $dot$
    + Assume $Theta tack dot ok$
    + By inversion, $Theta = dot$
    + $[Omega]dot = generic(Omega)$
    + $generic(Omega) tack generic(Omega) ok$
    + So we have $[Omega]Theta tack [Omega]Gamma ok$

    - *Case* $Gamma, x : sigma$
    + Assume $Theta tack Gamma, x : sigma ok$
    + By inversion $Theta tack Gamma$, $x disjoint Gamma$, $Theta tack sigma ok$
    + IH: $[Omega]Theta tack [Omega]Gamma ok$
    + ??, $[Omega]Theta tack [Omega]sigma ok$
    + $[Omega](Gamma, x : sigma) = [Omega]Gamma, x : [Omega]sigma$
    + We have $[Omega]Theta tack [Omega]Gamma ok $

    - *Case* $Gamma, alpha$
    + Assume $Theta tack Gamma, alpha ok$
    + By inversion, $Theta = Theta_L, alpha$, $Theta_L tack Gamma ok$, $alpha disjoint Gamma$
    + $Omega = Omega_L, Omega_alpha, Omega_R$ where $Omega_R$ is soft 
    + $Theta_L --> Omega_L$
    + $[Omega_L]Theta_L tack [Omega_L]Gamma ok$
    + Cases on $Omega_alpha$:
      - *Case* $Omega_alpha = alpha$
      + Assume $Omega_alpha = alpha$
      + $[Omega_L, alpha](Gamma, alpha) = [Omega_L]Gamma, alpha$
      + $alpha disjoint [Omega_L]Gamma$ since $alpha disjoint Omega_L, Gamma$
      + $[Omega](Gamma, alpha) = [Omega_L]Gamma, alpha, generic(Omega_R)$ with $generic(Omega_R) disjoint alpha, [Omega_L]Gamma$
      + $[Omega](Theta_L, alpha) = [Omega]Theta_L, alpha, generic(Omega_R)$
      + By (4, 5) $[Omega]Theta tack [Omega](Gamma, alpha) ok $

      - *Case* $Omega_alpha = alpha := tau$

      + Assume $Omega_alpha = alpha := tau$
      + $[Omega_L, alpha := tau](Gamma, alpha) = [Omega_L]Gamma$
      + $[Omega](Gamma, alpha) = [Omega_L]Gamma, generic(Omega_R)$
      + $[Omega](Theta_L, alpha) = [Omega]Theta_L, generic(Omega_R)$
      + By (3, 4) $[Omega]Theta tack [Omega](Gamma, alpha) ok$

]

- $[| Gamma tack e : tau |] = cdef floor(Gamma) cin [| e : tau|]$
- $floor(Gamma)$ erases all bound type variables in $Gamma$:
$
  floor(dot) &= dot \ 
  floor(Gamma\, x : sigma) &= floor(Gamma), x : sigma \ 
  floor(Gamma\, alpha) &= floor(Gamma)
$
#theorem[_Constraint generation is sound with respect to the ML typing judgements_][
  Given $Theta tack Gamma ok$. 


  If $Omega$ is a unifier of $[| Gamma tack e : tau |]$ that extends $Theta$, 
  then there exists $Omega'$ such that \ $[Omega']Gamma tack e : [Omega']tau$ holds and $Omega'$ is a _soft extension_ of $Omega$. 
]
#proof[
  We proceed by structural induction on $e$. 

  - *Case* $x$
  + Let us assume $Omega$ is a unifier of $[| Gamma tack x : tau |]$ and extends $Theta$
  + $[| Gamma tack x : tau |] = cdef floor(Gamma) cin x <= tau$
  + Wlog, $x : sigma in floor(Gamma)$ and $sigma = tforall(overline(alpha)) tau'$ where $overline(alpha) disjoint Gamma, Omega, e, tau$
  + We have the equivalence $sigma <= tau equiv exists overline(alpha). tau' = tau$
  + By (1, 4) $Omega$ is a unifier of $exists overline(alpha). tau' = tau$
  + $Omega softex Omega'$ in $overline(alpha)$ s.t $Omega'$ is a unifier of $tau' = tau$
  + $[Omega']tau' = [Omega']tau$. 
  + We have $[Omega']Gamma tack [Omega']alpha_i ok$ for all $alpha_i$. 
  + So we have $[Omega']Gamma tack x : [Omega']tau$ with 
  $
    #proof-tree(
      rule(
        $[Omega']Gamma tack x : underbrace([Omega']tau', [Omega']tau "by (7)")$, 
        $x : tforall(overline(alpha)) [Omega]tau' in [Omega']Gamma$, 
        $[Omega']Gamma tack overline([Omega']alpha_i) ok$
      )
    )
  $

  - *Case* $lambda x. e$

  + Let us assume $Omega$ is a unifier of $[| Gamma tack lambda x. e : tau |]$ and extends $Theta$
  + $[| Gamma tack lambda x. e : tau |] = cdef floor(Gamma) cin exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef x : alpha_1 cin [| e: alpha_2 |]$

  + (2) is equivalent to $exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and cdef floor(Gamma), x : alpha_1 cin [| e_2 : alpha_2 |]$ wlog $alpha_1, alpha_2 disjoint Gamma, tau, Theta, Omega$

  + $Omega softex Omega'$ in $alpha_1, alpha_2$ s.t $Omega'$ is a unifier of $tau = alpha_1 -> alpha_2$ and $cdef floor(Gamma), x : alpha_1 cin [| e : alpha_2 |]$

  + Let $Gamma' = Gamma, alpha_1, x: alpha_1$.  $Theta' = Theta, alpha_1$ satisfies $Theta' tack Gamma' ok$. We have $Theta' --> Omega'$ and $Omega'$ is a unifier for $cdef floor(Gamma') cin [| e : alpha_2 |]$. By induction, exists $Omega''$ s.t $Omega' softex Omega''$ and \ $[Omega'']Gamma' tack e : [Omega'']alpha_2$
  
  + Wlog: $Omega'' = Omega''_L, Omega''_(alpha_1), Omega''_(alpha_2), Omega''_R$ where $Omega = Omega_L$ (defn of soft extension). 

  + $[Omega'']Gamma' = [Omega''_L]Gamma, generic(Omega''_alpha_1), x : [Omega'']alpha_1, generic(Omega''_(alpha_2), Omega''_R)$. 

  + By exchange (7, 5), we have $[Omega''_L]Gamma, generic(Omega'' _alpha_1, Omega''_alpha_2, Omega''_R), x : [Omega'']alpha_1 tack e : [Omega'']alpha_2$. 

  + Note that $[Omega''_L]Gamma, generic(Omega'' _alpha_1, Omega''_alpha_2, Omega''_R) = [Omega'']Gamma$

  + By (8, 9), we have $[Omega'']Gamma, x : [Omega'']alpha_1 tack e : [Omega''] alpha_2$

  + We have $[Omega'']Gamma tack [Omega'']alpha_1 ok$ (since $Theta --> Omega''$)

  + So we have $[Omega'']Gamma tack lambda x.e : [Omega'']tau$ by
  $
    #proof-tree(
      rule(
        $[Omega'']Gamma tack lambda x. e : underbrace([Omega'']alpha_1 -> [Omega'']alpha_2, [Omega'']tau "by (4)")$, 
        $[Omega'']Gamma, x : [Omega'']alpha_1 tack e : [Omega'']alpha_2$, 
        $[Omega'']Gamma tack [Omega'']alpha_1 ok$
      )
    )
  $
  
  - *Case* $e_1 space e_2$
  _I expect similar reasoning to $lambda x. e$_

  - *Case* $elet x = e_1 ein e_2$

  + Let us assume $Omega$ is a unifier of $[| Gamma tack elet x = e_1 ein e_2 : tau |]$ and extends $Theta$

  + $[| Gamma tack elet x = e_1 ein e_2 : tau |] = cdef floor(Gamma) cin clet x : cforall(alpha_1, [| e_1 : alpha_1 |], alpha_1) cin [| e_2 : tau |]$

  + By equivalences, we have 
    $
    [| Gamma tack elet x = e_1 ein e_2 : tau |] equiv exists sigma and cdef floor(Gamma), x : sigma cin [| e_2 : tau |]
    $
    where $sigma = cforall(alpha_1, cdef floor(Gamma) cin [| e_1 : alpha_1 |], alpha_1)$

  + Hence $Omega$ is a unifier for $exists sigma$ and $cdef floor(Gamma), x : sigma cin [| e_2 : tau |]$

  + By Lemma (EMTLI 1.4.8), exists a most general $Omega_1$ s.t $Omega softex Omega_1$ and $Omega_1$ is a unifier of $cdef floor(Gamma) cin [| e_1 : alpha_1|]$. Let $overline(beta) = fv([Omega_1]alpha_1) \\ Omega$, by Lemma (EMLTI 1.4.8), $sigma$ is equivalent to $tforall(overline(beta)) [Omega_1]alpha$ _under_ $Omega$.  

  + Let $Theta_1 = Theta, overline(beta)$ and $Gamma_1 = Gamma, overline(beta)$. (_informal reasoning_) For any generic in soft extension of  $Omega_1$ that is not in $overline(beta)$, we _fill_ the generic with $1$. We call this extension $Omega'_1$. 
  
  + We have $Omega softex Omega'_1$. Additionally $Omega'_1$ is still a unifier of $cdef floor(Gamma_1) cin [| e_1 : alpha_1 |]$ and \ $Theta_1 --> Omega'_1$

  + By induction, we have $[Omega''_1]Gamma_1 tack e_1 : [Omega''_1]alpha_1$ for some $Omega''_1$ which is soft extension of $Omega'_1$. 


  + We have $[Omega''_1](Gamma, overline(beta)) = [Omega]Gamma, overline(beta), overline(gamma)$ where $overline(gamma) = generic(Omega''_1 \\ Omega'_1)$. 
  
  + Additionally $[Omega''_1]alpha_1 = [Omega_1]alpha_1$. So we have $[Omega]Gamma, overline(beta), overline(gamma) tack e_1 : [Omega_1]alpha_1$. 

  + By exchange, we have $[Omega]Gamma, overline(gamma), overline(beta) tack e_1 : [Omega_1]alpha_1$

  + Define $Omega_2 = Omega, (Omega''_1 \\ Omega'_1)$. We have $Theta --> Omega softex Omega_2$. Hence $Omega_2$ is a unifier for \ $cdef floor(Gamma), x : tforall(overline(beta)) [Omega_1]alpha_1 cin [| e_2 : tau |]$. 

  + By induction, we have $[Omega''_2](Gamma, x : tforall(overline(beta)) [Omega_1]alpha_1) tack e_2 : [Omega''_2]tau$ where $Omega_2 softex Omega''_2 $

  + $[Omega''_2]Gamma = [Omega]Gamma, overline(gamma), overline(delta)$ where $overline(delta) = generic(Omega''_2 \\ Omega_2)$

  + $[Omega''_2](tforall(overline(beta)) [Omega_1]alpha_1) = tforall(overline(beta)) [Omega''_2][Omega_1]alpha_1$. Since $Omega''_2$ and $Omega_1$ only agree on $Omega$ and $alpha_1 in.not Omega''_2$, we have $[Omega''_2][Omega_1]alpha_1 = [Omega_1]alpha_1$. 

  + So we have $[Omega]Gamma, x : tforall(overline(beta)) [Omega_1]alpha_1, overline(gamma), overline(delta) tack e_2 : [Omega''_2]tau$. 

  + By exchange, we have $[Omega]Gamma, overline(gamma), overline(delta), x : tforall(overline(beta)) [Omega_1]alpha_1 tack e_2 : [Omega''_2]tau$

  + By weakening and exchange on (11), we have $[Omega]Gamma, overline(gamma), overline(delta), overline(beta) tack e_1 : [Omega_1]alpha_1$
  
  + We have $[Omega''_2]Gamma tack elet x = e_1 ein e_2 : [Omega''_2]tau$ by:

  $
  
    #proof-tree(
      rule(
        $underbrace([Omega]Gamma\, overline(gamma)\, overline(delta), [Omega''_2]Gamma "by (14)") tack elet x = e_1 ein e_2 : [Omega''_2]tau$, 
        $[Omega]Gamma, overline(gamma), overline(delta), overline(beta) tack e_1 : [Omega_1]alpha_1$, 
        $overline(beta) disjoint [Omega]Gamma, overline(gamma), overline(delta)$, 
        $[Omega]Gamma, overline(gamma), overline(delta), x : tforall(overline(beta)) [Omega_1]alpha_1 tack e_2 : [Omega''_2]tau$
      )
    )
  $



]





// Worklist based semantics?

// #let gen = textsf("gen")
// $
//   Gamma &::= dot | Gamma, alpha | Gamma, hat(alpha) | Gamma, x : sigma | Gamma tack.double C \
//   tau &::= alpha | hat(alpha) | 1 | tau -> tau \ 
//   sigma &::= tforall(overline(alpha)) C => tau \ 
//   C &::= ... | gen(sigma) >>_x C
// $

// Solver:
// $
//   // Garbage collection 
//   Gamma, alpha &--> Gamma \ 
//   Gamma, hat(alpha) &--> Gamma \ 
//   Gamma, x : sigma &--> Gamma 
  
//   \ \

//   // Decomposition for constraints 
//   Gamma tack.double C_1 and C_2 &--> Gamma tack.double C_2 tack.double C_1 \ 
//   Gamma tack.double exists alpha. C &--> Gamma, hat(alpha) tack.double C[alpha := hat(alpha)] \ 
//   Gamma tack.double x <= tau &--> Gamma tack.double sigma <= tau \ 
//   Gamma tack.double sigma <= tau &--> Gamma tack.double exists overline(alpha). C and tau' = tau \
//   Gamma tack.double cdef x : sigma cin C &--> Gamma, x : sigma tack.double C \ 
//   Gamma tack.double forall alpha. C &--> Gamma, alpha tack.double C \ \

//   // Ranks / Generalization 
//   Gamma tack.double clet x : sigma cin C &--> Gamma, triangle.r.small tack.double  >>_x C 
  
//   \ \

//   // Unification
//   // Refl (simple)
//   Gamma tack.double 1 = 1 &--> Gamma \ 
//   Gamma tack.double alpha = alpha &--> Gamma \ 
//   Gamma tack.double hat(alpha) = hat(alpha) &--> Gamma \ 
//   Gamma tack.double tau_1 -> tau_2 = tau_1 ' -> tau_2 ' &--> Gamma tack.double tau_1 = tau_1 ' tack.double tau_2 = tau_2 ' \ 
//   Gamma[hat(alpha)] tack.double hat(alpha) = tau_1 -> tau_2 &--> (Gamma[hat(alpha_1), hat(alpha_2)] tack.double hat(alpha_1) -> hat(alpha_2) = tau_1 -> tau_2)[hat(alpha) := hat(alpha_1) -> hat(alpha_2)]\
//   Gamma[hat(alpha)] tack.double tau_1 -> tau_2 = hat(alpha) &--> (Gamma[hat(alpha_1), hat(alpha_2)] tack.double tau_1 -> tau_2 = hat(alpha_1) -> hat(alpha_2))[hat(alpha) := hat(alpha_1) -> hat(alpha_2)]\



//   // Flex-Flex
//   Gamma[hat(alpha)][hat(beta)] tack.double hat(alpha) = hat(beta) &--> (Gamma[hat(alpha)][])[hat(beta) := hat(alpha)] \ 
//   Gamma[hat(alpha)][hat(beta)] tack.double hat(beta) = hat(alpha) &--> (Gamma[hat(alpha)][])[hat(beta) := hat(alpha)] \ 
//   // Var-Rigid
//   Gamma[alpha][hat(beta)] tack.double hat(beta) = alpha &--> (Gamma[alpha][])[hat(beta) := alpha] \ 
//   Gamma[alpha][hat(beta)] tack.double alpha = hat(beta) &--> (Gamma[alpha][])[hat(beta) := alpha] \ 
// $
// 

// == Solver

// #let umultieq = $epsilon.alt$

// $
// F ::= &square and C |  exists alpha. square \ 
//   | &cdef x : sigma cin square \
//   | &clet x : cforall(overline(alpha), square, tau)  cin C \
//   | &clet x : hat(sigma) cin square \  \

// S ::= &dot | S :: F
// $

// Normal forms are of the form:
// $
//   N &::= ctrue | cfalse | N and N | umultieq | cdef x : sigma cin N | clet x : hat(sigma) cin N  \ 
//   M &::= N | exists alpha. M \ 
//   hat(sigma) &::= cforall(alpha, hat(M), alpha)
// $

// A normal form is _solved_, denoted $hat(N)$ respectively if every multi-equation in $N$ contains at most one non-variable type, no two multi-equations share a variable, and $N$ is not cyclic. 
// An existential normal form is _solved_, denoted $hat(M)$, if the normal form $N$ in $M$ is solved. 


// The unifier re-writing rules are given by:
// #let tformerg = textsf("G")
// #let sunify = $-->$
// $
//   // Common rules
//   N &--> cfalse 
//   &&"if" N "is cyclic" \ 
//   cal(N)[cfalse] &--> cfalse \
//   cal(N)[N] &--> cal(N)[N']  
//   &&"if" N --> N' \ 
//   N and ctrue &--> N \ 
//   // Merge rule 
//   alpha = umultieq_1 and alpha = umultieq_2 &--> alpha = umultieq_1 = umultieq_2  \ 
//   // Normalize rules  
//   alpha = alpha = umultieq &--> alpha = umultieq \ 
//   // Shallowify
//   overline(tau)[tau_i] tformer = umultieq  &--> exists alpha. overline(tau)[alpha] tformer = umultieq and alpha = tau_i &&"if" tau_i in.not varset(Ty) and alpha disjoint overline(tau), umultieq \ 
//   // Decomposition types 
//   overline(alpha) tformer = overline(beta) tformer = umultieq &--> overline(alpha) tformer = umultieq and overline(alpha) = overline(beta) \ 
//   // Clash 
//   overline(alpha) tformer = overline(beta) tformerg = umultieq &--> cfalse &&"if" tformer != tformerg \ 
// $

// The solver re-writing rules are given by:
// $
// (S, U, C) &--> (S, U', C) &#h(2cm)&"if" U --> U' \ 
//  (S, U, tau_1 = tau_2) &--> (S, U and tau_1 = tau_2, ctrue) \ 
//  (S, U, Psi_1 = Psi_2) &--> (S, U and Psi_1 = Psi_2, ctrue) \
//  (S, U, C_1 and C_2) &--> (S :: square and C_2, U, C_1) \ 
//  (S, U, exists alpha. C) &--> (S :: exists alpha. square, U, C) &#h(2cm)&"if" alpha \# U \ 
//  (S, U, exists scopev. C) &--> (S :: exists scopev. square, U, C) \
//  (S, U, forall alpha. C) &--> (S :: forall alpha. square, U, C) \
//  (S, U, cdef x : sigma cin C) &--> (S :: cdef x : sigma cin square, U, C) \ 
//  (S, U, x <= tau) &--> (S, U, sigma <= tau) &&"if" x : sigma in ) \ 
//  (S, U, (cforall(Theta, C, tau')) <= tau) &--> (S, U, exists Theta. C and tau = tau')\
//  (S, U, clet x : cforall(Theta, C_1, tau) cin C_2) &--> (S :: clet x : cforall(Theta,  square, tau) cin C_2, U, C_1) \
//  (S, U, eqname : tau_1 = tau_2 ==> C) &--> (S :: eqname : tau_1 = tau_2 ==> square, U, C)
// $


