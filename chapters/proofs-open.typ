#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: thmrules

#let Assn = textsf("Assn")


Constraints:
$
  Con in.rev C &::= ctrue | cfalse | C_1 and C_2 | tau_1 = tau_2 | exists alpha. C  \ 
  &space | clet x = forall overline(alpha). lambda beta. C cin C | x space tau  \ 
  Ty in.rev tau &::= alpha | 1 | tau -> tau \ \
  Scm in.rev sigma &::= tau | tforall(alpha) sigma \ \ 
  Assn in.rev Psi &::= dot | Psi, alpha | Psi, alpha := tau | Psi, x : sigma

  #v1
$
$
  #proof-tree(
    rule(
      $Psi tack ctrue$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack C_1 and C_2$, 
      $Psi tack C_1$, 
      $Psi tack C_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack tau_1 = tau_2$, 
      $Psi tack tau_1, tau_2 ok$, 
      $[Psi]tau_1 = [Psi]tau_2$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Psi tack exists alpha. C$, 
      $Psi tack tau ok$,
      $alpha disjoint Psi$,
      $Psi, alpha := tau tack C$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack clet x = forall overline(alpha). lambda beta. C_1 cin C_2$,  
      $Psi tack forall overline(alpha). lambda beta. C_1 => sigma$,
      $Psi, x : sigma tack C_2$,
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack x space tau$, 
      $x : sigma in Psi$, 
      $Psi tack sigma <= tau$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Psi tack forall overline(alpha). lambda beta. C => tforall(overline(beta)\, overline(gamma)) tau$,
      $alpha, overline(beta), overline(gamma) disjoint Psi$, 
      $Psi, overline(beta), overline(gamma) tack tau ok$, 
      $Psi, overline(beta), overline(gamma), alpha := tau tack C$, 
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Psi tack tau_1 <= tau_2$, 
      $Psi tack tau_1 = tau_2$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack tforall(alpha) sigma <= tau$,
      $Psi tack tau' ok$,
      $Psi tack sigma[alpha := tau'] <= tau$
    )
  )
$


Assignments:
- Application:
$
  [Psi]alpha &= cases(
    [Psi]tau #h1&"if" alpha := tau in Psi, 
    alpha &"otherwise"
  ) \ 
  [Psi]1 &= 1 \ 
  [Psi](tau_1 -> tau_2) &= [Psi]tau_1 -> [Psi]tau_2 \ 
$
- Well-formedness:
#judgement-box($Psi ok$, $Psi tack tau ok$, $Psi tack sigma ok$)
$
  #proof-tree(
    rule(
      $Psi tack alpha ok$, 
      $alpha in dom(Psi)$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack 1 ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi tack tau_1 -> tau_2 ok$, 
      $Psi tack tau_1 ok$, 
      $Psi tack tau_2 ok$
    )
  )
$
$
  #v2 

  #proof-tree(
    rule(
      $Psi tack tforall(alpha) sigma ok$, 
      $Psi, alpha tack sigma ok$
    )
  )

$
$

  #v2 

  #proof-tree(
    rule(
      $dot ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi, alpha ok$, 
      $Psi ok$, 
      $alpha disjoint Psi$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi, alpha := tau ok$,
      $Psi ok$, 
      $Psi tack tau ok$, 
      $alpha disjoint Psi$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi, x : sigma ok$, 
      $Psi ok$, 
      $Psi tack sigma ok$,
      $x disjoint Psi$
    )
  )
$


ML:
$
  Exp in.rev e &::= x | lambda x. e | e space e | () | elet x = e_1 ein e_2\ \ 
  Ctx in.rev Gamma &::= dot | Gamma, x : sigma | Gamma, alpha \ \
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
      $Gamma tack Lambda alpha. e : tau[alpha := tau']$, 
      $Gamma, alpha tack e : tau$, 
      $alpha disjoint Gamma$, 
      $Gamma tack tau' ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau$, 
      $Gamma tack e : tau$, 
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

Well-formedness: 
#judgement-box($Gamma ok$, $Gamma tack tau ok$, $Gamma tack sigma ok$)
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
      $Gamma, alpha ok$, 
      $Gamma ok$, 
      $alpha disjoint Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma, x : sigma ok$, 
      $Gamma ok$, 
      $Gamma tack sigma ok$, 
      $x disjoint Gamma$
    )
  )
  
  #v2 

  #proof-tree(
    rule(
      $Gamma tack 1 ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack alpha ok$, 
      $alpha in Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack tau_1 -> tau_2 ok$, 
      $Gamma tack tau_1 ok$, 
      $Gamma tack tau_2 ok$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha) sigma ok $, 
      $Gamma, alpha tack sigma ok$, 
      $alpha disjoint Gamma$
    )
  )
$

Constraint Generation:
$
  [| x : tau |] &= x <= tau \ 
  [| e_1 space e_2 : tau |] &= exists alpha. [| e_1 : alpha -> tau|] and [| e : alpha |] \
  [| efun x -> e : tau |] &= exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and clet x = lambda alpha. alpha = alpha_1 cin [| e : alpha_2 |] \ 
  [| clet x = e_1 ein e_2 : tau |] &= clet x = lambda alpha. [| e_1 : alpha |] cin [| e_2 : tau |]  \ 
  [| Lambda alpha. e : tau |] &= clet x = forall alpha. lambda beta. [| e : beta |] cin x space tau\
  [| (e : tau') : tau |] &= [| e : tau' |] and tau' = tau \ 
  [| () : tau |] &= tau = 1
$

Extension:

#judgement-box($Psi --> Psi'$)
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
      $Psi, alpha --> Psi', alpha$, 
      $Psi --> Psi'$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Psi, alpha := tau --> Psi', alpha := tau'$, 
      $Psi --> Psi'$, 
      $[Psi']tau = [Psi']tau'$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Psi, x : sigma --> Psi', x : sigma'$, 
      $Psi --> Psi'$, 
      $[Psi]sigma = [Psi']sigma'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Psi, alpha --> Psi', alpha := tau$,
      $Psi --> Psi'$, 
      $Psi' tack tau ok$
    )
  )


  #h1 

  #proof-tree(
    rule(
      $Psi --> Psi', alpha := tau$,
      $Psi --> Psi'$, 
      $alpha disjoint Psi'$,
      $Psi' tack tau ok$
    )
  )
$

#theorem[_Constraint generation is sound with respect to the ML typing judgements_][
  Given $Gamma ok$ and $Gamma --> Psi$ and $Psi$ is identity on the fvs of $e$.  

  If $Psi tack [| e : tau |]$, then $Gamma tack e : [Psi]tau$. 
]

#proof[
  We proceed by induction on $e$. 

  - *Case* $x$
  + Let us assume $Psi tack [| x : tau |]$ holds 
  + $[| x : tau |] = x <= tau$
  + By inversion, we have $x : tforall(overline(alpha)) tau' in Psi$ (a) and $Psi tack tforall(overline(alpha)) tau' <= tau$
  + By definition of extension (3.a), $x : tforall(alpha) tau' in Gamma$
  + (_informal reasoning_) $Psi tack tforall(overline(alpha)) tau' <= tau$ iff $[Psi]tau = [Psi](tau'[overline(alpha := tau'')])$ and $Psi tack overline(tau'') ok$
  + $[Psi](tau'[overline(alpha := tau'')]) = ([Psi]tau')[overline(alpha := [Psi]tau'')]$
  + $[Psi]tau' = [Gamma]tau' = tau'$
  + $Gamma tack overline([Psi]tau'') ok$ since $Gamma --> Psi$ and $Psi tack overline(tau'') ok$
  + We have $Gamma tack x : [Psi]tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack x : tau'[overline(alpha := [Psi]tau'')]$, 
        $x : tforall(overline(alpha)) tau' in Gamma$, 
        $Gamma tack overline([Psi]tau'') ok$
      )
    )
  $

  - *Case* $lambda x.e$:
  + Let us assume $Psi tack [| lambda x. e : tau |]$
  + $[| lambda x. e : tau|] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 cin [| e : alpha_2 |]$, wlog $alpha_1, alpha_2, beta disjoint tau, Gamma, Psi$
  + By inversion, we have 
    $
      
      #proof-tree(
        rule(
          $Psi tack exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 cin [| e : alpha_2 |]$, 
          rule(
            $Psi' { Psi, alpha_1 := tau_1, alpha_2 := tau_2 tack tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 cin [| e_2 : alpha_2 |]$, 
            rule(
              $Psi' tack tau = alpha_1 -> alpha_2$, 
              $[Psi']tau = [Psi']alpha_1 -> [Psi']alpha_2$
            ), 
            rule(
              $Psi' tack clet x = lambda beta. beta = alpha_1 cin [| e_2 : alpha_2 |]$, 
              rule(
                $Psi' tack lambda beta. beta = alpha_1 => [Psi']alpha_1$, 
                $"Lemma ??"$
              ), 
              $Psi', x : [Psi']alpha_1 tack [| e_2 : alpha_2 |]$
            )
          )
        )
      )
    $
  + By (3), we have $[Psi']tau = [Psi']alpha_1 -> [Psi']alpha_2$ and $Psi', x : [Psi']alpha_1 tack [| e_2 : alpha_2 |]$

  + Since $alpha_1, alpha_2 disjoint tau$, we have $[Psi']tau = [Psi]tau$


  + We note that $Gamma tack [Psi']alpha_1 ok$, hence $Gamma, x : [Psi']alpha_1 ok$

  + By (6), we have $Gamma, x : [Psi']alpha_1 --> Psi', x : [Psi']alpha_1$. 

  + By induction (7, 4), we have $Gamma, x : [Psi']alpha_1 tack e_2 : [Psi', x : [Psi']alpha_1]alpha_2$. 

  + Note that $[Psi', x : [Psi']alpha_1]alpha_2 = [Psi']alpha_2$. 

  + We have $Gamma tack lambda x. e : [Psi]tau$ by:
    $
      #proof-tree(
        rule(
          $Gamma tack lambda x. e : underbrace([Psi']alpha_1 --> [Psi']alpha_2, [Psi]tau "by (4, 5)")$, 
          rule(
            $Gamma tack [Psi']alpha_1 ok$, 
            $(6)$
          ), 
          rule(
            $Gamma, x : [Psi']alpha_1 tack e : [Psi']alpha_2$, 
            $(8, 9)$
          )
        )
      )
    $


  - *Case* $e_1 space e_2$
  _Trivial_ 

  - *Case* $()$
  _Trivial_

  - *Case* $elet x = e_1 ein e_2$

  + Let us assume $Psi tack [| elet x = e_1 ein e_2 : tau |]$
  + $[| elet x = e_1 ein e_2 : tau |] = clet x = lambda alpha. [| e_1 : alpha|] cin [| e_2 : tau |]$, wlog $alpha disjoint tau, Gamma, Psi$

  + By inversion, we have 

    $
      #proof-tree(
        rule(
          $Psi tack elet x = lambda alpha. [| e_1 : alpha |] ein [| e_2 : tau |]$, 
          rule(
            $Psi tack lambda alpha. [| e_1 : alpha|] => tforall(overline(beta)) tau_1$, 
            $alpha, overline(beta) disjoint Psi$,
            $Psi, overline(beta) tack tau_1 ok$, 
            $Psi, overline(beta), alpha := tau_1 tack [| e_1 : alpha |]$
          ), 
          $Psi, x : tforall(overline(beta)) tau_1 tack [| e_2 : tau |]$
        )
      )
    $

  + Note that $Gamma, overline(beta) ok$ and $Gamma, overline(beta) --> Psi, overline(beta), alpha := tau_1$. 
  + By induction (3, 4), we have $Gamma, overline(beta) tack e_1 : [Psi, overline(beta), alpha := tau_1]alpha$. 

  + We note that $[Psi, overline(beta), alpha := tau_1]alpha = [Psi]tau_1$

  + We have $Gamma, overline(beta) tack [Psi]tau_1 ok$, so we have $Gamma, x : tforall(overline(beta)) [Psi]tau_1 ok$. 

  + We note that $Psi, x : tforall(overline(beta)) tau_1 --> Psi, x : tforall(overline(beta)) [Psi]tau_1$, hence $Psi, x : tforall(overline(beta)) [Psi]tau_1 tack [| e_2 : tau |]$

  + We have $Gamma, x : tforall(overline(beta)) [Psi]tau_1 --> Psi, x : tforall(overline(beta)) [Psi]tau_1$

  + By induction (7, 8, 9), we have $Gamma, x : tforall(overline(beta)) [Psi]tau_1 tack e : [Psi, x : tforall(overline(beta)) [Psi]tau_1]tau$

  + Note that $[Psi, x : tforall(overline(beta)) [Psi]tau_1]tau = [Psi]tau$

  + We have $Gamma tack elet x = e_1 ein e_2 : [Psi]tau$ by 
  $
    #proof-tree(
      rule(
        $Gamma tack elet x = e_1 ein e_2 : [Psi]tau$, 
        rule(
          $Gamma, overline(beta) tack e_1 : [Psi]tau_1$, 
          $(5, 6)$
        ), 
        rule(
          $overline(beta) disjoint Gamma$, 
          $(4)$
        ), 
        rule(
          $Gamma, x : tforall(overline(beta)) [Psi]tau_1 tack e_2 : [Psi]tau$, 
          $(10, 11)$
        )
      )
    )
  $ 

  - *Case* $(e : tau')$

  + Let us assume $Psi tack [| (e : tau') : tau |]$

  + $[| (e : tau') : tau |] = [| e : tau' |] and tau' = tau$

  + By inversion, we have 
    $
      #proof-tree(
        rule(
          $Psi tack [| e : tau' |] and tau' = tau$, 
          $Psi tack [| e : tau' |]$, 
          rule(
            $Psi tack tau' = tau$, 
            $Psi tack tau', tau ok$, 
            $[Psi]tau' = [Psi]tau$
          )
        )
      )
    $
  + By induction (3), we have $Gamma tack e : [Psi]tau'$
  + By (3), we have $[Psi]tau' = [Psi]tau$
  + By assumptions, we have $[Psi]tau' = tau'$. By (5), we have $[Psi]tau' = [Psi]tau = tau'$
  + We have $Gamma tack (e : tau') : [Psi]tau$ by 
  $
    #proof-tree(
      rule(
        $Gamma tack (e : tau') : underbrace(tau', [Psi]tau "by (6)")$, 
        $Gamma tack e : tau'$
      )
    )
  $

  - *Case* $Lambda alpha. e$

  + Let us assume $Psi tack [| Lambda alpha. e : tau |]$

  + $[| Lambda alpha. e : tau |] = clet x = forall alpha. lambda beta. [| e : beta |] cin x space tau$

  + By inversion, we have 
    $
      #proof-tree(
        rule(
          $Psi tack clet x = forall alpha. lambda beta. [| e : beta |] cin x space tau$, 
          rule(
            $Psi tack forall alpha. lambda beta. [| e : beta |] => tforall(alpha\, overline(gamma)) tau'$, 
            $alpha, overline(gamma), beta disjoint Psi$, 
            $Psi, alpha, overline(gamma) tack tau' ok$, 
            $Psi, alpha, overline(gamma), beta := tau' tack [| e : beta |]$
          ), 
          rule(
            $Psi, x : tforall(alpha\, overline(gamma)) tau' tack x space tau$, 
            $Psi tack tforall(alpha\, overline(gamma)) tau' <= tau$
          )
        )
      )
    $


  + By (3), we have $[Psi]tau'[alpha := [Psi]tau'', overline(gamma := [Psi]tau''')] = [Psi]tau$ where $Psi tack tau'', overline(tau''') ok$. 

  + Note that $Psi, alpha, overline(gamma), beta := tau' --> Psi, alpha, overline(gamma := tau'''), beta := tau'$

  + By Lemma ??, we have $Psi, alpha, overline(gamma := tau'''), beta := tau' tack [| e : beta |]$

  + Note that $Gamma, alpha ok$ and $Gamma, alpha --> Psi, alpha, overline(gamma := tau'''), beta := tau'$

  + By induction (3,7), we have $Gamma, alpha tack e : [Psi, alpha, overline(gamma := tau'''), beta := tau']beta$. 

  + We note that $[Psi, alpha, overline(gamma := tau'''), beta := tau']beta = [Psi]tau'[overline(gamma := [Psi]tau''')]$

  + By Lemma ?? (4), $Gamma tack [Psi]tau'' ok$

  + We have $Gamma tack Lambda alpha. e : [Psi]tau$ by 
  $
    #proof-tree(
      rule(
        $Gamma tack Lambda alpha. e : ([Psi]tau'[overline(gamma := [Psi]tau''')])[alpha := [Psi]tau'']$, 
        rule(
          $Gamma, alpha tack e : [Psi]tau'[overline(gamma := [Psi]tau''')]$, 
          $(8)$
        ), 
        $alpha disjoint Gamma$, 
        rule(
          $Gamma tack [Psi]tau'' ok$, 
          $(10)$
        )
      )
    )
  $
]

#theorem[_Constraint generation is complete with respect to the ML typing judgements_][
  Given $Gamma ok$ and $Gamma --> Psi$


  If $Gamma tack e : [Psi]tau$, then $Psi tack [| e : tau |]$
]

#proof[
  We proceed by induction on $e$. 

  - *Case* $x$
  + Let us assume $Gamma tack x : [Psi]tau$ holds 
  + By inversion, we have $x : tforall(overline(alpha)) tau' in Gamma$ (a), $Gamma tack overline(tau'') ok$ (b), and $[Psi]tau = tau'[overline(alpha := tau'')]$ (c)
  + $[| x : tau |] = x <= tau$
  + We have $x : tforall(overline(alpha)) tau in Psi$ and $Psi tack overline(tau'') ok$ 
  + By (2.c) and (4), we have $Psi tack tforall(overline(alpha)) tau' <= tau$
  + We have $Psi tack x <= tau$
  $
    #proof-tree(
      rule(
        $Psi tack x <= tau$, 
        $x : tforall(overline(alpha)) tau' in Psi$, 
        $Psi tack tforall(overline(alpha)) tau' <= tau$
      )
    )
  $

  - *Case* $lambda x. e$ 
  + Let us assume $Gamma tack lambda x. e : [Psi]tau$
  + By inversion, we have $Gamma tack tau_1 ok$ (a) and $Gamma, x : tau_1 tack e : tau_2$ (b), and $[Psi]tau = tau_1 -> tau_2$ (c). 
  + By (2.b), we have  $Gamma tack tau_2 ok$
  + $[| lambda x. e : tau|] = exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 ein [| e : alpha_2 |]$
  + Define $Psi' = Psi, alpha_1 := tau_1, alpha_2 := tau_2$. 
  + $Gamma --> Psi'$ by transitivity of $Psi --> Psi'$
  + We have $[Psi]tau_i = tau_i$. So it follows that 
    $
      [Psi']tau = [Psi']alpha_1 -> [Psi']alpha_2
    $
    by (2.c)
  + Define $Psi'' = Psi', x : alpha_1$. 
  + We have $Gamma tack [Psi'']alpha_1 ok$ (since $[Psi'']alpha_1 = tau_1$)
  + Note that $Gamma, x : tau_1 --> Psi''$. 
  + We have $Gamma, x : tau_1 tack e : [Psi'']alpha_2$ since $[Psi'']alpha_2 = tau_2$
  + By induction (11), we have $Psi'' tack [| e : alpha_2 |]$
  + We have $Psi tack [| lambda x. e : tau|]$ by 
  $
    #proof-tree(
      rule(
        $Psi tack exists alpha_1, alpha_2. tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 ein [| e : alpha_2 |]$, 
        rule(
          $Psi' tack tau = alpha_1 -> alpha_2 and clet x = lambda beta. beta = alpha_1 cin [| e : alpha_2|]$, 
          rule(
            $Psi' tack tau = alpha_1 -> alpha_2$, 
            rule(
              $[Psi']tau = [Psi']alpha_1 -> [Psi']alpha_2$, 
              $(7)$
            )
          ), 
          rule(
            $Psi' tack clet x = lambda beta. beta = alpha_1 cin [| e : alpha_2 |]$, 
            rule(
              $Psi' tack lambda beta. beta = alpha_1 => alpha_1$, 
              $"Lemma ??"$
            ), 
            rule(
              $Psi', x : alpha_1 tack [| e : alpha_2|]$, 
              $(12)$
            )
          )
        )
      )
    )
  $

  - *Case* $e_1 space e_2$
  _Trivial_ 

  - *Case* $()$

  _Trivial_ 

  - *Case* $elet x = e_1 ein e_2$
  + Let us assume $Gamma tack elet x = e_1 ein e_2 : [Psi]tau$
  + By inversion, we have $Gamma, overline(alpha) tack e_1 : tau_1$ (a), $overline(alpha) disjoint Gamma$ (b), and $Gamma, x : tforall(overline(alpha)) tau_1 tack e_2 : [Psi]tau$
  + $[| elet x = e_1 ein e_2 : tau |] = elet x = lambda beta. [| e_1 : beta |] cin [| e_2 : tau |]$, wlog $beta disjoint tau, Gamma, Psi$
  + We have $Gamma, overline(alpha) tack tau_1 ok$ 
  + Define $Psi' = Psi, overline(alpha), beta := tau_1$. 
  + We have $Gamma, overline(alpha) --> Psi'$
  + Since $[Psi']beta = tau_1$, we have $Gamma, overline(alpha) tack e_1 : [Psi']beta$
  + By induction (6, 7), we have $Psi' tack [| e_1 : beta |]$
  + We have $Psi, overline(alpha) tack tau_1 ok$
  + We have $Psi tack lambda beta. [| e_1 : beta |] => tforall(overline(alpha)) tau_1$
    $
      #proof-tree(
        rule(
          $Psi tack lambda beta. [| e_1 : beta |] => tforall(overline(alpha)) tau_1$, 
          rule(
            $Psi, overline(alpha) tack tau_1 ok$, 
            $(9)$
          ),
          rule(
            $Psi, overline(alpha), beta := tau_1 tack [| e_1 : beta |]$, 
            $(8)$
          )
        )
      )
    $
  + Define $Psi'' = Psi, x : tforall(overline(alpha)) tau_1$. 
  + We have $Gamma, x : tforall(overline(alpha)) tau_1 --> Psi''$
  + By induction (2.c, 12), we have $Psi'' tack [| e_2 : tau |]$
  + We have $Psi tack [| elet x = e_1 ein e_2 : tau |]$ by 
  $
    #proof-tree(
      rule(
        $Psi tack elet x = lambda beta. [| e_1 : beta |] cin [| e_2 : tau |]$, 
        rule(
          $Psi tack lambda beta. [| e_1 : beta |] => tforall(overline(alpha)) tau_1$, 
          $(10)$
        ), 
        rule(
          $Psi, x : tforall(overline(alpha)) tau_1 tack [| e_2 : tau |]$, 
          $(13)$
        )
      )
    )
  $ 

  - *Case* $(e : tau')$

  + Let us assume $Gamma tack (e : tau') : [Psi]tau$

  + By inversion, we have $Gamma tack e : tau'$ (a) and $[Psi]tau = tau'$ (b)

  + $[| (e : tau') : tau |] = [| e : tau' |] and tau = tau'$

  + By (2.b), we have 
    $
      [Psi][Psi]tau &= [Psi]tau' \ 
      <==> [Psi]tau &= [Psi]tau' = tau' 
    $

  + By (2.a, 4), we have $Gamma tack e : [Psi]tau'$

  + By induction (5), we have $Psi tack [| e : tau'|]$

  + We have $Psi tack tau, tau' ok$

  + By (2.b, 7, 4), we have $[Psi]tau = [Psi]tau'$

  + We have $Psi tack [| (e : tau') : tau |]$ by 
  $
    #proof-tree(
      rule(
        $Psi tack [| e : tau' |] and tau = tau'$, 
        rule(
          $Psi tack [| e : tau' |]$, 
          $(6)$
        ), 
        rule(
          $Psi tack tau = tau'$, 
          rule(
            $Psi tack tau, tau' ok$, 
            $(7)$
          ), 
          rule(
            $[Psi]tau = [Psi]tau'$, 
            $(8)$
          )
        )
      )
    )
  $

  - *Case* $Lambda alpha. e$

  + Let us assume $Gamma tack Lambda alpha. e : [Psi]tau$

  + By inversion, we have $Gamma, alpha tack e : tau'$ (a), $alpha disjoint Gamma$ (b), $Gamma tack tau'' ok$ (c), and $[Psi]tau = tau'[alpha := tau'']$ (d)

  + $[| Lambda alpha. e : tau |] = clet x = forall alpha. lambda beta. [| e : beta |] cin x space tau$

  + $Gamma, alpha --> Psi, alpha, beta := tau'$ 

  + $[Psi, alpha, beta := tau']beta = tau'$, so we have $Gamma, alpha tack e : [Psi, alpha, beta := tau']beta$

  + By induction (2.a, 4, 5), $Psi, alpha, beta := tau' tack [| e : beta |]$

  + By (2.d), we have 
    $
      #proof-tree(
        rule(
          $Psi tack tforall(alpha) tau' <= tau$, 
          rule(
            $Psi tack tau'' ok$,
            "Lemma ??"
          ),  
          rule(
            $Psi tack tau'[alpha := tau''] <= tau$, 
            rule(
              $Psi tack tau'[alpha := tau''] = tau$, 
              $Psi tack tau'[alpha := tau''] ok$, 
              $[Psi]tau'[alpha := tau''] = [Psi]tau$
            )
          )
        )
      )
    $

  + By Lemma ?? (2.a), we have $Gamma, alpha tack tau' ok$. By Lemma ??, we have $Psi, alpha tack tau' ok$. 

  + We have $Psi tack [| Lambda alpha. e : tau |]$ by 
  $
    #proof-tree(
      rule(
        $Psi tack clet x = forall alpha. lambda beta. [| e : beta |] cin x space tau $, 
        rule(
          $Psi tack forall alpha. lambda beta. [| e : beta |] => tforall(alpha) tau'$, 
          $alpha, beta disjoint Psi$, 
          rule(
            $Psi, alpha tack tau' ok$,
            $(8)$
          ), 
          rule(
            $Psi, alpha, beta := tau' tack [| e : beta |]$, 
            $(6)$
          )
        ), 
        rule(
          $Psi tack tforall(alpha) tau' <= tau$, 
          $(7)$
        )
      )
    )
  $
]

Lemmas to prove:
- $Psi tack tau ok$ and $Psi tack lambda alpha. alpha = tau => sigma$ iff $sigma = tau'$ where $[Psi]tau = [Psi]tau'$
- $Gamma --> Psi$ and $Psi tack tau ok$, then $Gamma tack [Psi]tau ok$
- $Gamma --> Psi$ and $Gamma tack tau ok$, then $Psi tack tau ok$ (This has a similar shape to the above lemma, can we unify them?)
- Some lemmas about elements being preserved up to equality in extension 

- Constraint subsumption matches ML subsumtpion 
- $Psi tack C$ and $Psi --> Psi'$ then $Psi' tack C$

= Solver 

Equivalences we need to show for solver correctness:
$
  (exists alpha. C_1) and C_2 &equiv exists alpha. C_1 and C_2  &#h1&"if" alpha disjoint C_2 \ 
  exists alpha. (alpha = tau) &equiv ctrue &&"if" alpha disjoint tau \ 
  exists overline(alpha). C &equiv C &&"if" overline(alpha) disjoint C \ 
  clet x = lambda alpha. C cin cal(C)[x space tau] &equiv clet x = lambda alpha. C cin cal(C)[C[alpha := tau]] &&"if" x, C disjoint cal(C) \ 
  clet x  = lambda alpha. exists beta. C_1 cin C_2 &equiv exists beta. clet x = lambda alpha. C_1 cin C_2 &&"if" beta disjoint C_2, exists alpha. C_1 "determines" beta \ 
  clet x = lambda alpha. C_1 cin exists beta. C_2 &equiv exists beta. clet x = lambda alpha. C_1 cin C_2 &&"if" beta disjoint alpha, C_1 \ 
  U &equiv cfalse &&"if" U "is cyclic" \ 
  cal(C)[cfalse] &equiv cfalse \ 
  C and ctrue &equiv C \ 
  alpha = beta and C &equiv C[alpha := beta] &&"if" alpha eq.not beta \ 
  
$

All of these look true by inspection :) 

Solver termination remains unchanged. 

Principality of $Psi tack C$ can be shown with the following sketch:
- Solver solved form is $exists overline(beta). (overline(alpha) = overline(tau))$ where $fv(overline(tau)) subset.eq overline(beta)$ and $overline(beta) disjoint overline(alpha)$
- The _principal assignment_ of this solved form is $Psi = overline(beta), overline(alpha := tau)$
- Sufficient to show: $Psi' tack exists overline(beta). (overline(alpha) = overline(tau)) ==> Psi --> Psi'$ (this is very trivial, just inversion)