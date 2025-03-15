#import "../../lib/std.typ": *
#import "../..//lib/syntax.typ": *
#import "../../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "../cmon.typ": *

// HACK to get thm to left align
#show: thmrules

We proceed by collecting auxiliary lemmas in Appendix B1. The two subsequent subsections contain the two proof directions of Theorem ??, respectively

== Auxiliary Lemmas

#lemma[_Substitution weakening_][
  Given $Phi disjoint Phi'$.
  + If $fv(tau^kappa) disjoint Phi'$, then ${Phi}tau^kappa = {Phi, Phi'}tau^kappa$
  + If $fv(sigma) disjoint Phi'$, then ${Phi}sigma = {Phi, Phi'}sigma$
] <weaken-sub-inv>
#proof[
  + By induction on the structure of $tau^kappa$

  + By induction on the structure of $sigma$
]


#lemma[_Erasure preservation_][
  + If $alpha fbind(phi) kappa in Phi$, then $alpha fbind(phi) kappa in floor(Phi)$
  + If $eqname : tau_1 = tau_2 in Phi$, then $eqname : tau_1 = tau_2 in floor(Phi)$
  + If $Phi assn$ and $x : sigma in Phi$, then $x : {Phi}sigma in floor(Phi)$
] <erasure-preservation>
#proof[
  + By induction on $alpha fbind(phi) kappa in Phi$
  + By induction on $eqname : tau_1 = tau_2 in Phi$
  + By induction on $Phi assn$

  - *Case* (EmpAssn)
  + Let us assume $emptyset assn$ (a) and $x : sigma in emptyset$ (b)
  + Contradiction (2.b)!

  - *Case* (TyVarAssn)
  + Let us assume $Phi, alpha fbind(phi) kappa assn$ (a) and $x : sigma in Phi, alpha fbind(phi) kappa$ (b)
  + By inversion (1.a), we have $Phi assn$ (a) and $alpha disjoint Phi$ (b)
  + By inversion (1.b), we have $x : sigma in Phi$
  + By induction (2.a, 3), we have $x : {Phi}sigma in floor(Phi)$
  + By @weaken-sub-inv ${Phi}sigma = {Phi, alpha fbind(phi) kappa}sigma$
  + By definition of erasure, $floor(Phi\, alpha fbind(phi) kappa) = floor(Phi), alpha fbind(phi) kappa$
  + By definition of membership (4), $x : {Phi}sigma in floor(Phi\, alpha fbind(phi) kappa)$.
  + By (7, 5), we have $x : {Phi, alpha fbind(phi) kappa}sigma in floor(Phi\, alpha fbind(phi) kappa)$

  - *Case* (SolvedTyVarAssn)
  + Let us assume $Phi, alpha fbind(fflex) kappa := tau^kappa assn$ (a) and $x : sigma in Phi, alpha fbind(fflex) kappa := tau^kappa$ (b)
  + By inversion (1.a), we have $Phi assn$ (a), $alpha disjoint Phi$ (b), and \ $Phi tack tau^kappa :: kappa$ (c)
  + By inversion (1.b), $x : sigma in Phi$
  + By induction (2.a, 3), $x : {Phi}sigma in floor(Phi)$
  + By @weaken-sub-inv, ${Phi, alpha fbind(fflex) kappa := tau^kappa}sigma = {Phi}sigma$
  + By definition of erasure, $floor(Phi\, alpha fbind(fflex) kappa := tau^kappa) = floor(Phi)$
  + By (4, 5, 6), we have $x : {Phi, alpha fbind(fflex) kappa := tau^kappa}sigma in floor(Phi\, alpha fbind(fflex) kappa := tau^kappa)$

  - *Case* (VarAssn)
  + Let us assume $Phi, x' : sigma' assn$ (a) and $x : sigma in Phi, x' : sigma'$ (b)
  + By inversion (1.a), we have $Phi assn$ (a), $x disjoint Phi'$ (b), and $Phi tack sigma' scm$ (c)
  + Two cases:
    - *Case* $x = x'$
    4. By inversion (1.b), $sigma = sigma'$
    + By definition of erasure, $floor(Phi\, x' : sigma') = floor(Phi), x' : {Phi}sigma'$
    + By @weaken-sub-inv, ${Phi}sigma' = {Phi, x' : sigma'}sigma'$
    + By (4, 6, 5), we have $floor(Phi\, x' : sigma') = floor(Phi), x : {Phi, x : sigma}sigma$
    + By definition of membership, we have $x : {Phi, x' : sigma'}sigma in floor(Phi\, x' : sigma')$

    - *Case* $x != x'$
    4. By inversion (1.b), $x : sigma in Phi$
    + By induction (2.a, 4), we have $x : {Phi}sigma in floor(Phi)$
    + By @weaken-sub-inv, ${Phi, x' : sigma'}sigma = {Phi}sigma$
    + By definition of erasure, $floor(Phi\, x' : sigma') = floor(Phi), x' : {Phi}sigma'$
    + By definition of membership, $x : {Phi}sigma in floor(Phi\, x' : sigma')$
    + By (6, 8), we have $x : {Phi, x' : sigma'}sigma in floor(Phi\, x' : sigma')$


  - *Case* (EqAssn)
  + Let us assume $Phi, eqname : tau_1 = tau_2 assn$ (a) and $x : sigma in Phi, eqname : tau_1 = tau_2$ (b)
  + By inversion (1.a), we have $Phi' assn$ (a), $eqname disjoint Phi$ (b), and $Phi tack tau_1, tau_2 :: ty frigid$ (c)
  + By inversion (1.b), $x : sigma in Phi$
  + By induction (2.a, 3), we have $x : {Phi}sigma in floor(Phi)$
  + By @weaken-sub-inv ${Phi, eqname : tau_1 = tau_2}sigma = {Phi}sigma$
  + By definition of erasure, $floor(Phi\, eqname : tau_1 = tau_2) = floor(Phi), eqname : tau_1 = tau_2$
  + By definition of membership (4), $x : {Phi}sigma in floor(Phi\, eqname : tau_1 = tau_2)$.
  + By (7, 5), we have $x : {Phi, eqname : tau_1 = tau_2}sigma in floor(Phi\, eqname : tau_1 = tau_2)$


]

#lemma[_Erasure preserves absence_][
  If the declaration $u$ is not in $Phi$, then $u$ is not in $floor(Phi)$
] <erasure-not-in>
#proof[
  By induction on the structure of $Phi$.
]


#definition[_Assignment size_][
  The size of $tau^kappa$ under the assignment $Phi$, written $Phi tack tau^kappa$, is defined as follows:
  $
    |Phi tack alpha| &= cases(
      1 + |Phi tack tau^kappa| #h1 &"if" alpha fbind(fflex) kappa := tau^kappa in Phi \
      1 &"otherwise"
    ) \
    |Phi tack overline(tau) tformer | &= 1 + sum_(i = 1)^n |Phi tack tau_i | \
    |Phi tack [Psi]tau| &= 1 + |Phi tack Psi| + |Phi tack tau| \
    |Phi tack emptyset| &= 1 \
    |Phi tack Psi, eqname| &= 1 + |Phi tack Psi|
  $
]


#lemma[_Erasure preserves well-formedness_][
  If $Phi assn$ and $Phi tack tau^kappa :: kappa space phi$, then $floor(Phi) tack {Phi}tau^kappa :: kappa space phi$
] <erasure-wf>
#proof[
  We proceed by induction on $|Phi tack tau^kappa|$.
  We consider cases on $Phi tack tau^kappa :: kappa space phi$.

  - *Case* (VarAssnWF)
  + Let us assume $Phi tack alpha :: kappa space phi$
  + By inversion, we have $alpha fbind(phi)' kappa in Phi$ (a) and $phi' <= phi'$ (b)
  + By @erasure-preservation (2.a), $alpha fbind(phi)' kappa in floor(Phi)$
  + By definition of substitution (2.a), ${Phi}alpha = alpha$
  + We have $floor(Phi) tack {Phi}alpha :: kappa space phi$ by:
  $
    #proof-tree(
      rule(
        $floor(Phi) tack underbrace(alpha, {Phi}alpha "by" (4)) :: kappa space phi$,
        rule(
          $alpha fbind(phi)' kappa in floor(Phi)$,
          $(3)$
        ),
        rule(
          $phi' <= phi$,
          $(2.b)$
        ),
        name: [VarWF]
      )
    )
  $

  - *Case* (SolvedVarAssnWF)
  + Let us assume $Phi tack alpha :: kappa$
  + By inversion, we have $alpha fbind(fflex) kappa := tau^kappa in Phi$ (a)
  + By (2.a) and $Phi assn$, we have $Phi = Phi_L, alpha fbind(fflex) kappa := tau^kappa, Phi_R$ where $Phi_L tack tau^kappa :: kappa$.
  + By definition of substitution (3), we have ${Phi}alpha = {Phi}tau^kappa$. \ By @weaken-sub-inv, we have ${Phi}tau^kappa = {Phi_L}tau^kappa$
  + By definition of assignment size, $|Phi tack alpha| = 1 + |Phi tack tau^kappa|$. Given $Phi_L tack tau^kappa :: kappa$, $|Phi tack tau^kappa| = |Phi_L tack tau^kappa|$
  + By (5), $|Phi_L tack tau^kappa| < |Phi tack alpha|$.
  + By induction (6), we have $floor(Phi_L) tack {Phi_L}tau^kappa :: kappa$
  + By weakening (7), $floor(Phi) tack {Phi}tau^kappa :: kappa$
  + By (4), we have $floor(Phi) tack {Phi}alpha :: kappa$

  - *Case* (TyConAssnWF)
  + Let us assume $Phi tack overline(tau) tformer :: ty space phi$
  + By inversion, we have $Phi tack overline(tau) :: ty space phi$
  + By defintion of substitution, ${Phi}(overline(tau) tformer) = overline({Phi}tau) tformer$
  + By definition of assignment size, $|Phi tack overline(tau) tformer| = 1 + sum_(i = 1)^n |Phi tack tau_i|$
  + By (4), we have $|Phi tack tau_i| < |Phi tack overline(tau) tformer|$ for all $1 <= i <= n$
  + By induction (5), we have $floor(Phi) tack {Phi}tau_i :: ty space phi$
  + We have $floor(Phi) tack {Phi}(overline(tau) tformer) :: ty space phi$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack underbrace(overline({Phi}tau) tformer, {Phi}(overline(tau) tformer) "by (3)") :: ty space phi$,
        $forall i,$,
        rule(
          $floor(Phi) tack {Phi}tau_i :: ty space phi$,
          $(6)$
        ),
        name: [TyConWF]
      )
    )
  $

  - *Case* (AmbAssnWF)
  + Let us assume $Phi tack [Psi]tau :: ty$
  + By inversion, we have $Phi tack Psi :: scope$ (a) and $Phi tack tau :: ty frigid$ (b)
  + By definition of substitution, ${Phi}[Psi]tau = [{Phi}Psi]{Psi}tau$
  + By definition of assignment size, $|Phi tack [Psi]tau| = 1 + |Phi tack Psi| + |Phi tack tau|$
  + By (4), we have $|Phi tack Psi|, |Phi tack tau| < |Phi tack [Psi]tau|$
  + By induction (5), we have $floor(Phi) tack {Phi}Psi :: scope$ (a) and $floor(Phi) tack {Phi}tau :: ty frigid$ (b)
  + We have $floor(Phi) tack {Phi}[Psi]tau :: ty$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack underbrace([{Phi}Psi]{Phi}tau, {Phi}[Psi]tau "by (3)") :: ty$,
        rule(
          $floor(Phi) tack {Phi}Psi :: scope$,
          $(6.a)$
        ),
        rule(
          $floor(Phi) tack {Phi}tau :: ty frigid$,
          $(6.b)$
        ),
        name: [AmbWF]
      )
    )
  $
  - *Case* (EmpScAssnWF)
  + Let us assume $Phi tack emptyset :: scope$
  + By definition of substitution, ${Phi}emptyset = emptyset$
  + We have $floor(Phi) tack {Phi}emptyset :: scope$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack emptyset :: scope$,
        name: [EmpScWF]
      )
    )
  $

  - *Case* (ConsScAssnWF)
  + Let us assume $Phi tack Psi, eqname :: scope$
  + By inversion, we have $Phi tack Psi :: scope$ (a) and $eqname : tau_1 = tau_2 in Phi$ (b)
  + By definition of substitution, ${Phi}(Psi, eqname) = {Phi}Psi, eqname$
  + By @erasure-preservation, $eqname : tau_1 = tau_2 in floor(Phi)$
  + By definition of assignment size, $|Phi tack Psi, eqname| = 1 + |Phi tack Psi|$
  + By (5), $|Phi tack Psi| < |Phi tack Psi, eqname|$
  + By induction (6), we have $floor(Phi) tack {Phi}Psi :: scope$
  + We have $floor(Phi) tack {Phi}(Psi, eqname) :: scope$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack underbrace({Phi}Psi\, eqname, {Phi}(Psi, eqname) "by (3)") :: scope$,
        rule(
          $floor(Phi) tack {Phi}Psi :: scope$,
          $(7)$
        ),
        rule(
          $eqname in dom(Phi)$,
          $(4)$
        ),
        name: [ConsScWF]
      )
    )
  $
]

#lemma[_Monomorphic abstractions produce monomorphic schemes_][
  Given $Phi tack tau :: ty$. If $Phi tack lambda alpha. alpha = tau => sigma$ then $floor(Phi) tack {Phi}tau <= {Phi}sigma$.
] <sat-mono-abs>
#proof[
  Let us assume $Phi tack tau :: ty$ \
  + Let us assume $Phi tack lambda alpha. alpha = tau => tforall(overline(beta :: kappa)) tau'$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $Phi tack lambda alpha. alpha = tau => tforall(overline(beta :: kappa))tau'$,
          rule(
            $alpha, overline(beta) disjoint Phi$,
            $(a)$
          ),
          rule(
            $Phi, overline(beta fbind(fflex) kappa) tack tau' :: ty$,
            $(b)$
          ),
          rule(
            $Phi' { Phi, overline(beta fbind(fflex) kappa), alpha fbind(fflex) ty := tau' tack alpha = tau$,
            rule(
              $floor(Phi') tack {Phi'}alpha equiv {Phi'}tau$,
              $(c)$
            )
          )
        )
      )
    $
  + Given $Phi tack tau :: ty$, by @weaken-sub-inv, ${Phi}tau = {Phi'}tau$
  + By definition of substitution ${Phi'}alpha = {Phi'}tau'$. Since $Phi'$ is identity for $overline(beta)$ and $alpha disjoint fv(tau')$, we have ${Phi'}tau' = {Phi}tau'$
  + By definition of substitution (4), ${Phi}(tforall(overline(beta ::kappa)) tau') = tforall(overline(beta :: kappa)) {Phi}tau'$
  + $floor(Phi') = floor(Phi), overline(beta fbind(fflex) kappa)$

  + We have $floor(Phi) tack {Phi}tau <= {Phi}(tforall(overline(beta :: kappa)) tau')$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack {Phi}tau <= underbrace(tforall(overline(beta :: kappa)) {Phi}tau', {Phi}(tforall(overline(beta :: kappa)) tau') "by (5)")$,
        rule(
          $floor(Phi), overline(beta fbind(fflex) kappa) tack {Phi}tau <= {Phi}tau'$,
          rule(
            $floor(Phi), overline(beta fbind(fflex) kappa) tack {Phi}tau equiv {Phi}tau'$,
            rule(
              $floor(Phi), overline(beta fbind(fflex) kappa) tack {Phi'}tau equiv {Phi'}alpha$,
              rule(
                $floor(Phi), overline(beta fbind(fflex) kappa) tack {Phi'}alpha equiv {Phi'}tau$,
                $(2.c, 6)$
              ),
              name: [$equiv$Sym]
            ),
            name: [by (3, 4)]
          ),
          name: [$<=equiv$]
        ),
        rule(
          $overline(beta) disjoint floor(Phi)$,
          [wlog]
        ),
        name: [$<=forall"R"^*$]
      )
    )
  $

]


#lemma[_Consistent instance is sound with respect to #aml _][
  Given $Phi tack tau :: ty frigid$.

  If $Phi tack alpha = ceil(tau)$ and $Phi$ identity for $fv(tau)$, then $floor(Phi) tack forall ceil(tau) <= {Phi}alpha$
] <sound-scope-erasure>
#proof[
  By induction on $Phi tack tau :: ty frigid$.
]

#lemma[_Consistent instance is complete with respect to #aml _][
  Given $Phi tack tau :: ty frigid$.

  $floor(Phi) tack forall ceil(tau) <= {Phi}alpha$ and $Phi$ is identity for $fv(tau)$, then $Phi tack alpha = ceil(tau)$
] <complete-scope-erasure>
#proof[
  By induction on $Phi tack tau :: ty frigid$.
]

#lemma[_Constraint abstractions produce well-formed schemes_][
  If $Phi tack Lambda => sigma$, then $Phi tack sigma scm$
] <sat-wf-abs>
#proof[
  Trivial inversion on $Phi tack Lambda => sigma$
]

== Proof of Soundness


#theorem[_Constraint generation is sound with respect to #aml _][
  $Phi assn$ and $Phi$ is the identity on $fv(e)$.

  If $Phi tack [| e : alpha |]$, then $floor(Phi) tack e : {Phi}alpha$.
]

#proof[
  We proceed by induction on $e$.

  - *Case* $x$
  + Let us assume $Phi tack [| x : alpha |]$ holds
  + $[| x : alpha |] = x space alpha$
  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack x space alpha$,
          rule(
            $Phi tack alpha :: ty$,
            $(a)$
          ),
          rule(
            $x : sigma in Phi$,
            $(b)$
          ),
          rule(
            $floor(Phi) tack {Phi}sigma <= {Phi}alpha$,
            $(c)$
          ),
          name: [App]
        )
      )
    $
    wlog $overline(alpha) disjoint alpha, e, Phi$

  + By @erasure-preservation (3.b), $x : {Phi}sigma in floor(Phi)$

  + So we have $floor(Phi) tack e : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack x : {Phi}alpha$,
        rule(
          $x : {Phi}sigma in floor(Phi)$,
          $(4)$
        ),
        rule(
          $floor(Phi) tack {Phi}sigma <= {Phi}alpha$,
          $(3.c)$
        ),
        name: [Var]
      )
    )
  $


  - *Case* $efun x -> e$:
  + Let us assume $Phi tack [| efun x -> e : alpha |]$
  + $[| efun x -> e : alpha |] = exists alpha_1 :: ty, alpha_2 :: ty. alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$, wlog $alpha_1, alpha_2, alpha_3 disjoint alpha, e, Phi$
  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack exists alpha_1 :: ty, alpha_2 :: ty. alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$,
          rule(
            $Phi' { Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2 tack alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e_2 : alpha_2 |]$,
            rule(
              $Phi' tack alpha = alpha_1 -> alpha_2$,
              rule(
                $floor(Phi') tack {Phi'}alpha equiv {Phi'}alpha_1 -> {Phi'}alpha_2$,
                $(c)$
              ),
              name: [Equal]
            ),
            rule(
              $Phi' tack clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e_2 : alpha_2 |]$,
              rule(
                $Phi' tack lambda alpha_3. alpha_3 = alpha_1 => sigma$,
                [@sat-mono-abs]
              ),
              rule(
                $Phi', x : sigma tack [| e_2 : alpha_2 |]$,
                $(d)$
              ),
              name: [Let]
            )
          ),
          name: [$"Exists"^*$]
        )
      )
    $
    where $Phi tack tau_1 :: ty$ (a), $Phi, alpha_1 fbind(fflex) ty := tau_1 tack tau_2 :: ty$ (b), and $floor(Phi') tack {Phi'}alpha_1 <= {Phi'}sigma$ (e)


  + By definition of erasure, $floor(Phi') = floor(Phi)$

  + By @weaken-sub-inv, we have ${Phi}alpha = {Phi'}alpha$ and ${Phi', x : sigma}alpha_2 = {Phi'}alpha_2$

  + By weakening (3.a), we have $Phi' tack tau_1 :: ty$.

  + By @erasure-wf (6), we have $floor(Phi') tack {Phi'}tau_1 :: ty$. By (4), we have $floor(Phi) tack {Phi'}tau_1 :: ty$.

  + By definition of substitution, ${Phi'}tau_1 = {Phi'}alpha_1$. By (7), we have $floor(Phi) tack {Phi'}alpha_1 :: ty$

  + $Phi', x : sigma assn$ by
    $
      #proof-tree(
        rule(
          $Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2, x : sigma assn$,
          rule(
            $Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2 assn$,
            rule(
              $Phi, alpha_1 fbind(fflex) ty := tau assn$,
              $Phi assn$,
              rule(
                $alpha_1 disjoint Phi$,
                $(2)$
              ),
              rule(
                $Phi tack tau_1 :: ty$,
                $(3.a)$
              )
            ),
            rule(
              $alpha_2 disjoint Phi, alpha_1$,
              $(2)$
            ),
            rule(
              $Phi, alpha_1 fbind(fflex) ty := tau_1 tack tau_2 :: ty$,
              $(3.b)$
            )
          ),
          rule(
            $x disjoint Phi'$,
            $(3)$
          ),
          rule(
            $Phi' tack sigma scm$,
            rule(
              [@sat-wf-abs],
              $(3)$
            )
          )
        )
      )
    $

  + Since $alpha_1, alpha_2 disjoint e$, $Phi', x : sigma$ is identity on $fv(e)$ given $Phi$ is identity on $fv(e)$

  + By induction (9, 10, 3.d), we have $floor(Phi'\, x : sigma) tack e : {Phi', x : sigma}alpha_2$.

  + By definition of erasure, $floor(Phi'\, x : sigma) = floor(Phi'), x : {Phi'}sigma$.

  + By definition of $<=$ on contexts, we have $floor(Phi)\, x : {Phi'}sigma <= floor(Phi), x : {Phi'}alpha_1$
    $
      #proof-tree(
        rule(
          $floor(Phi), x : {Phi'}sigma <= floor(Phi), x : {Phi'}alpha_1$,
          rule(
            $floor(Phi) <= floor(Phi)$,
            $$
          ),
          rule(
            $floor(Phi) tack {Phi'}alpha_1 <= {Phi'}sigma$,
            $(3.e, 4)$
          )
        )
      )
    $

  + By Theorem ?? (13, 12, 11), we have $floor(Phi), x : {Phi'}alpha_1 tack e : {Phi'}alpha_2$ \
    #comment[This theorem is monotonicity]


  + By (3.c, 5), we have $floor(Phi) tack {Phi}alpha equiv {Phi'}alpha_1 -> {Phi'}alpha_2$

  + We have $floor(Phi) tack efun x -> e : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack efun x -> e : {Phi}alpha$,
        rule(
          $floor(Phi) tack efun x -> e : {Phi'}alpha_1 -> {Phi'}alpha_2$,
          rule(
            $floor(Phi) tack {Phi'}alpha_1 :: ty$,
            $(8)$
          ),
          rule(
            $floor(Phi), x : {Phi'}alpha_1 tack e : {Phi'}alpha_2$,
            $(14)$
          ),
          name: [Fun]
        ),
        rule(
          $floor(Phi) tack {Phi}alpha equiv {Phi'}alpha_1 -> {Phi'}alpha_2$,
          $(15)$
        ),
        name: [Equiv]
      )
    )
  $

  - *Case* $e_1 space e_2$
  + Let us assume $Phi tack [| e_1 space e_2 : alpha |]$

  + $[| e_1 space e_2 : alpha |] = exists alpha_1 :: ty, alpha_2 :: ty. [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] and alpha_1 = alpha_2 -> alpha$ \ wlog $alpha_1, alpha_2 disjoint alpha, e_1, e_2, Phi$

  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack exists alpha_1 :: ty, alpha_2 :: ty. [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] and alpha_1 = alpha_2 -> alpha$,
          rule(
            $Phi' { Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2 tack [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] and alpha_1 = alpha_2 -> alpha$,
            rule(
              $Phi' tack [| e_1 : alpha_1 |]$,
              $(c)$
            ),
            rule(
              $Phi' tack [| e_2 : alpha_2 |]$,
              $(d)$
            ),
            rule(
              $Phi' tack alpha_1 = alpha_2 -> alpha$,
              rule(
                $floor(Phi') tack {Phi'}alpha_1 equiv {Phi'}alpha_2 -> {Phi'}alpha$,
                $(e)$
              ),
              name: [Equal]
            ),
            name: [$"Conj"^*$]
          ),
          name: [$"Exists"^*$]
        )
      )
    $
    where $Phi tack tau_1 :: ty$ (a) and $Phi, alpha_1 fbind(fflex) ty := tau_1 tack tau_2 :: ty$ (b).



  + By definition of erasure, we have $floor(Phi) = floor(Phi')$

  + By @weaken-sub-inv, ${Phi}alpha = {Phi'}alpha$

  + By (3.e, 5, 6), we have $floor(Phi) tack {Phi'}alpha_1 equiv {Phi'}alpha_2 -> {Phi}alpha$

  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2 assn$,
          rule(
            $Phi, alpha_1 fbind(fflex) ty := tau_1 assn$,
            $Phi assn$,
            rule(
              $alpha_1 disjoint Phi$,
              $(2)$
            ),
            rule(
              $Phi tack tau_1 :: ty$,
              $(3.a)$
            )
          ),
          rule(
            $alpha_2 disjoint Phi, alpha_1$,
            $(2)$
          ),
          rule(
            $Phi, alpha_1 fbind(fflex) ty := tau_1 tack tau_2 :: ty$,
            $(3.b)$
          )
        )
      )
    $

  + Since $alpha_1, alpha_2 disjoint Phi'$, $Phi'$ is identity on $fv(e)$ given $Phi$ is identity on $fv(e)$

  + By induction (3.c, 3.d, 7, 8), we have $floor(Phi') tack e_1 : {Phi'}alpha_1$ and $floor(Phi') tack e_2 : {Phi'}alpha_2$. By (4), we have $floor(Phi) tack e_1 : {Phi'}alpha_1$ and $floor(Phi) tack e_2 : {Phi'}alpha_2$.

  + We have $floor(Phi) tack e_1 space e_2 : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack e_1 space e_2 : {Phi}alpha$,
        rule(
          $floor(Phi) tack e_1 : {Phi'}alpha_2 -> {Phi}alpha$,
          rule(
            $floor(Phi) tack e_1 : {Phi'}alpha_1$,
            $(9)$
          ),
          rule(
            $floor(Phi) tack {Phi'}alpha_1 equiv {Phi'}alpha_2 -> {Phi}alpha$,
            $(6)$
          ),
          name: [Equiv]
        ),
        rule(
          $floor(Phi) tack e_2 : {Phi'}alpha_2$,
          $(9)$
        ),
        name: [App]
      )
    )
  $


  - *Case* $()$

  + Let us assume $Phi tack [| () : alpha |]$

  + $[| () : alpha |] = exists scopev :: scope. alpha = [scopev]tunit$, wlog $scopev disjoint alpha, Gamma, Phi$

  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack exists scopev :: scope. alpha = [scopev]tunit$,
          rule(
            $Phi' { Phi, scopev fbind(fflex) scopev := Psi tack alpha = [scopev]tunit$,
            rule(
              $floor(Phi') tack {Phi'}alpha equiv {Phi'}[scopev]tunit$,
              $(b)$
            ),
            name: [Equal]
          ),
          name: [Exists]
        )
      )
    $
    where $Phi tack Psi :: scope$ (a)

  + By definition of erasure, we have $floor(Phi) = floor(Phi')$

  + By @weaken-sub-inv, ${Phi'}alpha = {Phi}alpha$ and ${Phi'}Psi = {Phi}Psi$

  + By @erasure-wf (3.a), $floor(Phi) tack {Phi}Psi :: scope$

  + By definition of substitution and (5), ${Phi'}[scopev]tunit = [{Phi'}Psi]tunit= [{Phi}Psi]tunit$

  + We have $floor(Phi) tack () : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack () : {Phi}alpha$,
        rule(
          $floor(Phi) tack tforall(rho.alt :: scope) [rho.alt]tunit <= {Phi}alpha$,
          rule(
            $floor(Phi) tack {Phi}Psi :: scope$,
            $(6)$
          ),
          rule(
            $floor(Phi) tack [rho.alt]tunit [rho.alt := {Phi}Psi] <= {Phi}alpha$,
            rule(
              $floor(Phi) tack [{Phi}Psi]tunit equiv {Phi}alpha$,
              $(3.b, 5, 7)$
            ),
            name: [$<= equiv$]
          ),
          name: [$<=forall$L]
        ),
        name: [Unit]
      )
    )
  $

  - *Case* $erefl$

  _Similar argument to $()$._


  - *Case* $elet x = e_1 ein e_2$

  + Let us assume $Phi tack [| elet x = e_1 ein e_2 : alpha |]$
  + $[| elet x = e_1 ein e_2 : alpha |] = clet x = lambda beta. [| e_1 : beta |] cin [| e_2 : alpha |]$, wlog $beta disjoint alpha, e_1, e_2, Phi$



  + By inversion, we have

    $
      #proof-tree(
        rule(
          $Phi tack elet x = lambda beta. [| e_1 : beta |] ein [| e_2 : alpha |]$,
          rule(
            $Phi tack lambda beta. [| e_1 : beta |] => tforall(overline(gamma :: kappa)) tau_1$,
            rule(
              $beta, overline(gamma) disjoint Phi$,
              $(a)$
            ),
            rule(
              $Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$,
              $(b)$
            ),
            rule(
              $Phi, overline(gamma fbind(fflex) kappa), beta fbind(fflex) ty := tau_1 tack [| e_1 : beta |]$,
              $(c)$
            ),
            name: [Abs]
          ),
          rule(
            $Phi, x : tforall(overline(gamma :: kappa)) tau_1 tack [| e_2 : alpha |]$,
            $(d)$
          ),
          name: [Let]
        )
      )
    $

  + Let $Phi' = Phi, overline(gamma fbind(fflex) kappa), beta fbind(fflex) ty := tau_1$.

  + By definition of erasure, $floor(Phi') = floor(Phi), overline(gamma fbind(fflex) kappa)$

  + $Phi' assn$ by
    $
      #proof-tree(rule(
        $Phi, overline(gamma fbind(fflex) kappa), beta fbind(fflex) ty := tau_1 assn$,
        rule(
          $Phi, overline(gamma fbind(fflex) kappa) assn$,
          $Phi assn$,
          rule(
            $overline(gamma) disjoint Phi$,
            $(3.a)$
          )
        ),
        rule(
          $beta disjoint Phi, overline(gamma)$,
          $(3.a)$
        ),
        rule(
          $Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$,
          $(3.b)$
        )
      ))
    $

  + Since $beta disjoint e_1$, $Phi'$ is identity on $fv(e_1)$ given $Phi$ is identity on $fv(e_1)$.

  + By induction (3.c, 6, 7), we have $floor(Phi') tack e_1 : {Phi'}beta$. By (5), we have $floor(Phi), overline(gamma fbind(fflex) kappa) tack e_1 : {Phi'} beta$.

  + By definition of substitution, ${Phi'}beta = {Phi'}tau_1$. Given $Phi'$ is identity for $overline(gamma)$, we have ${Phi'}tau_1 = {Phi}tau_1$.

  + By (3.b), we have $Phi tack tforall(overline(gamma :: kappa)) tau_1 scm$.
    We have $Phi, x : tforall(overline(gamma :: kappa)) tau_1 assn$

  + $Phi, x : tforall(overline(gamma :: kappa)) tau_1$ is identity on $fv(e_2)$ since $Phi$ is identity on $fv(e_2)$

  + By induction (3.d, 10, 11), we have $floor(Phi\, x : tforall(overline(gamma :: kappa)) tau_1) tack e_2 : {Phi, x : tforall(overline(gamma :: kappa)) tau_1}alpha$

  + By definition of erasure, $floor(Phi\, x : tforall(overline(gamma :: kappa)) tau_1) = floor(Phi), x : tforall(overline(gamma :: kappa)) {Phi}tau_1$.

  + By @weaken-sub-inv, ${Phi, x : tforall(overline(gamma :: kappa)) tau_1}alpha = {Phi}alpha$

  + By @erasure-not-in (3.a), $overline(gamma) disjoint floor(Phi)$

  + We have $floor(Phi) tack elet x = e_1 ein e_2 : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack elet x = e_1 ein e_2 : {Phi}alpha$,
        rule(
          $floor(Phi) tack e_1 : tforall(overline(gamma :: kappa)) {Phi}tau_1$,
          rule(
            $floor(Phi), overline(gamma fbind(fflex) kappa) tack e_1 : {Phi}tau_1$,
            $(8, 9)$
          ),
          rule(
            $overline(gamma) disjoint floor(Phi)$,
            $(15)$
          ),
          name: [$"Gen"^*$]
        ),
        rule(
          $floor(Phi), x : tforall(overline(gamma :: kappa)) {Phi}tau_1 tack e_2 : {Phi}alpha$,
          $(12, 13, 14)$
        ),
        name: [Let]
      )
    )
  $



  - *Case* $(e : tau)$

  + Let us assume $Phi tack [| (e : tau) : alpha |]$

  + $[| (e : tau) : alpha |] = alpha = ceil(tau) and (exists beta :: ty. beta = ceil(tau) and [| e : beta |])$, wlog $beta disjoint alpha, e, tau, Phi$

  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack alpha = ceil(tau) and (exists beta :: ty. beta = ceil(tau) and [| e : beta |])$,
          rule(
            $Phi tack alpha = ceil(tau)$,
            $(a)$
          ),
          rule(
            $Phi tack exists beta :: ty. beta = ceil(tau) and [| e : beta |]$,
            rule(
              $Phi' { Phi, beta fbind(fflex) ty := tau' tack beta = ceil(tau) and [| e : beta |]$,
              rule(
                $Phi' tack beta = ceil(tau)$,
                $(c)$
              ),
              rule(
                $Phi' tack [| e : beta |]$,
                $(d)$
              ),
              name: [Conj]
            ),
            name: [Exists]
          ),
          name: [Conj]
        )
      )
    $
    where $Phi tack tau' :: ty$ (b)


  + By definition of erasure, $floor(Phi') = floor(Phi)$

  + By @sound-scope-erasure (4.a, 4.c, $Phi$/$Phi'$ is identity on $fv(tau)$), we have $floor(Phi) tack forall ceil(tau) <= {Phi}alpha$ and $floor(Phi') tack forall ceil(tau) <= {Phi'}beta$. By (4), we have $floor(Phi) tack forall ceil(tau) <= {Phi'}beta$

  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, beta fbind(fflex) ty := tau' assn$,
          $Phi assn$,
          rule(
            $beta disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau' :: ty$,
            $(3.b)$
          )
        )
      )
    $

  + $Phi'$ is identity on $fv(e)$ since $Phi$ is identity on $fv(e)$ and $beta disjoint e$

  + By induction (6, 7, 3.d), we have $floor(Phi') tack e : {Phi'}beta$. By (4), we have $floor(Phi) tack e : {Phi'}beta$

  + By Lemma ?? (5), we have $floor(Phi) tack tau :: ty frigid$ \
    #comment[Requires $floor(Phi) tack forall ceil(tau) <= \_ => floor(Phi) tack forall ceil(tau) scm => floor(Phi) tack tau :: ty frigid$]

  + We have $floor(Phi) tack (e : tau) : {Phi}alpha$ by
  $
    #proof-tree(
      rule(
        $floor(Phi) tack (e : tau) : {Phi}alpha$,
        rule(
          $floor(Phi) tack e : {Phi'}beta$,
          $(8)$
        ),
        rule(
          $floor(Phi) tack tau :: ty frigid$,
          $(9)$
        ),
        rule(
          $floor(Phi) tack forall ceil(tau) <= {Phi'}beta, {Phi}alpha$,
          $(5)$
        ),
        name: [Annot]
      )
    )
  $

  - *Case* $efun (etype beta) -> e$

  + Let us assume $Phi tack [| Lambda alpha. e : alpha |]$

  + $[| efun (etype beta) -> e : alpha |] = clet x = forall beta :: ty. lambda gamma. [| e : gamma |] cin x space alpha$ wlog $gamma disjoint e, Phi$


  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack clet x = forall beta :: ty. lambda gamma. [| e : gamma |] cin x space alpha$,
          rule(
            $Phi tack forall beta :: ty. lambda gamma. [| e : gamma |] => tforall(beta :: ty\, overline(delta :: kappa)) tau$,
            rule(
              $beta, gamma, overline(delta) disjoint Phi$,
              $(a)$
            ),
            rule(
              $Phi' tack tau ::ty$,
              $(b)$
            ),
            rule(
              $Phi', gamma fbind(fflex) ty := tau tack [| e : gamma |]$,
              $(c)$
            ),
            rule(
              $beta in.not dangerous(tau)$,
              $(d)$
            ),
            // name: [Abs]
          ),
          rule(
            $Phi, x : tforall(beta ::ty\, overline(delta :: kappa)) tau tack x space alpha$,
            rule(
              $floor(Phi) tack {Phi}(tforall(beta :: ty\, overline(delta :: kappa)) tau) <= {Phi}alpha$,
              $(e)$
            )
          ),
          name: [Let]
        )
      )
    $

    where $Phi' = Phi, beta fbind(frigid) ty, overline(delta fbind(fflex) kappa)$

  + Let $Phi'' = Phi', gamma fbind(fflex) ty := tau$. By definition of erasure, $floor(Phi'') = floor(Phi), beta fbind(frigid) kappa, overline(delta fbind(fflex) kappa)$.

  + $Phi'' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, beta fbind(frigid) ty, overline(delta fbind(fflex) kappa), gamma fbind(fflex) ty := tau assn$,
          rule(
            $Phi' assn$,
            $Phi assn$,
            rule(
              $beta, overline(delta) disjoint Phi$,
              $(3.a)$
            )
          ),
          rule(
            $gamma disjoint Phi'$,
            $(2)$
          ),
          rule(
            $Phi' tack tau :: ty$,
            $(3.c)$
          )
        )
      )
    $

  + We have $Phi''$ is identity on $fv(e)$ since $Phi$ is identity on $fv(e)$, $Phi''$ is identity for $beta, overline(delta)$ and $gamma disjoint e$.

  + By induction (3.c, 5, 6), we have $floor(Phi'') tack e : {Phi''}gamma$. By (4), we have \ $floor(Phi), beta fbind(frigid) kappa, overline(delta fbind(fflex) kappa) tack e : {Phi''}gamma$

  + By definition of substitution, ${Phi''}gamma = {Phi''}tau$. Note that ${Phi''}tau = {Phi}tau$ since $Phi''$ is identity for $beta, overline(delta)$.

  + We note that ${Phi}(tforall(beta :: ty\, overline(delta :: kappa)) tau) = tforall(beta :: ty\, overline(delta :: kappa)) {Phi}tau$

  + Note that $beta disjoint rng(Phi)$ (as $beta disjoint Phi$). By (3.d), we have $beta in.not dangerous({Phi}tau)$. By definition of $dangerous$, we have $beta in.not dangerous(tforall(overline(delta :: kappa)) {Phi}tau)$.

  + By @erasure-not-in, we have $overline(delta), beta disjoint floor(Phi)$

  + We have $floor(Phi) tack efun (etype beta) -> e : {Phi}alpha$ by
  $
    #proof-tree(
      prem-min-spacing: 2pt,
      rule(
        $floor(Phi) tack efun (etype beta) -> e : {Phi}alpha$,
        rule(
          $floor(Phi) tack efun (etype beta) -> e : tforall(beta :: ty\, overline(delta :: kappa)) {Phi}tau$,
          rule(
            $floor(Phi), beta fbind(frigid) ty tack e : tforall(overline(delta :: kappa)) {Phi}tau$,
            rule(
              $floor(Phi), beta fbind(frigid) ty, overline(delta fbind(fflex) kappa) tack e : {Phi}tau$,
              $(7, 8)$
            ),
            rule(
              $overline(delta) disjoint floor(Phi)$,
              $(11)$
            ),
            name: [$"Gen"^*$]
          ),
          rule(
            $beta disjoint floor(Phi)$,
            $(11)$
          ),
          rule(
            $beta in.not dangerous(tforall(overline(delta :: kappa)) {Phi}tau)$,
            $(10)$
          ),
          // name: [TyFun]
        ),
        rule(
          $floor(Phi) tack tforall(beta :: ty\, overline(delta :: kappa)) {Phi}tau <= {Phi}alpha$,
          $(3.e, 9)$
        ),
        name: [Sub]
      ),
    )
  $

  - *Case* $ematch e : tau_1 = tau_2 ewith erefl -> e_2$

  + Let us assume $Phi tack [| ematch e : tau_1 = tau_2 ewith erefl -> e_2 : alpha |]$

  + $[| ematch e : tau_1 = tau_2 ewith erefl -> e_2 : alpha |] = (exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |])$ \ $and eqname : tau_1 = tau_2 => [| e_2 : alpha |]$ wlog $beta, eqname disjoint alpha, tau_1, tau_2, e_1, e_2, Phi$

  + By inversion, we have
    $
      #proof-tree(
        rule(
          $Phi tack (exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |]) and eqname : tau_1 = tau_2 => [| e_2 : alpha |]$,
          rule(
            $Phi tack exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |]$,
            rule(
              $Phi, beta fbind(fflex) ty := tau tack [| (e_1 : tau_1 = tau_2) : beta |]$,
              $(a)$
            ),
            name: [Exists]
          ),
          rule(
            $Phi tack eqname : tau_1 = tau_2 => [| e_2 : alpha |]$,
            rule(
              $Phi tack tau_1, tau_2 :: ty frigid$,
              $(b)$
            ),
            rule(
              $Phi, eqname : tau_1 = tau_2 => [| e_2 : alpha |]$,
              $(c)$
            ),
            name: [Impl]
          ),
          name: [Conj]
        )
      )
    $

  + Let $Phi' = Phi, beta fbind(fflex) ty := tau$.

  + By definition of erasure, $floor(Phi') = floor(Phi)$

  + $Phi' assn$ by

    $
      #proof-tree(
        rule(
          $Phi, beta fbind(fflex) ty := tau assn$,
          $Phi assn$,
          rule(
            $beta disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau :: ty$,
            $(3)$
          )
        )
      )
    $

  + $Phi'$ is identity on $fv((e_1 : tau_1 = tau_2))$ since $Phi$ is identity on $fv((e_1 : tau_1 = tau_2))$ and $beta disjoint tau_1, tau_2, e_1$

  + By induction (3.a, 6, 7), we have $floor(Phi') tack (e_1 : tau_1 = tau_2) : {Phi'}beta$

  + By definition of substitution, ${Phi'}beta = {Phi'}tau$. By @weaken-sub-inv, ${Phi'}tau = {Phi}tau$

  + Since $Phi$ is identity on $fv((e_1 : tau_1 = tau_2))$, it follows that ${Phi}tau_1 = tau_1$ and ${Phi}tau_2 = tau_2$

  + By @erasure-wf (3.b), we have $floor(Phi) tack {Phi}tau_1, {Phi}tau_2 :: ty frigid$. By (9), we have \ $floor(Phi) tack tau_1, tau_2 :: ty frigid$

  + $Phi, eqname : tau_1 = tau_2 assn$ by
    $
      #proof-tree(
        rule(
          $Phi, eqname : tau_1 = tau_2 assn$,
          $Phi assn$,
          rule(
            $eqname disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau_1, tau_2 :: ty frigid$,
            $(3.b)$
          )
        )
      )
    $

  + $Phi, eqname : tau_1 = tau_2$ is identity on $fv(e_2)$ since $Phi$ is identity on $fv(e_2)$

  + By induction (12, 13, 3.c), we have $floor(Phi\, eqname : tau_1 = tau_2) tack e_2 : {Phi, eqname : tau_1 = tau_2}alpha$

  + By @weaken-sub-inv, ${Phi, eqname : tau_1 = tau_2}alpha = {Phi}alpha$

  + By definition of erasure, $floor(Phi\, eqname : tau_1 = tau_2) = floor(Phi), eqname : tau_1 = tau_2$. By (14, 15), we have \ $floor(Phi), eqname : tau_1 = tau_2 tack e_2 : {Phi}alpha$

  + By Lemma ?? (16), we have $Gamma, eqname : tau_1 = tau_2 tack {Phi}alpha :: ty$ \
    #comment[Requires $Gamma tack e : tau => Gamma tack tau :: ty$ ]

  + We have two cases on ${Phi}alpha$:
    - *Case* ${Phi}alpha = alpha$

    19. By inversion of VarWF (17), we have $alpha fbind(phi) ty in Gamma, eqname : tau_1 = tau_2$

    + By definition of membership, we have $alpha fbind(phi) ty in Gamma$

    + We have $Gamma tack alpha :: ty$ by VarWF

    - *Case* ${Phi}alpha = tau$ where $tau in.not varset(Ty)$

    19. By inversion of substitution, we have $alpha fbind(fflex) ty := tau' in Phi$ and $tau = {Phi}tau'$

    + Hence $Phi = Phi_L, alpha fbind(fflex) ty := tau', Phi_R$ where $Phi_L tack tau' :: ty$ since $Phi assn$

    + By weakening (20), we have $Phi tack tau' :: ty$

    + By @erasure-wf (21), we have $floor(Phi) tack {Phi}tau' :: ty$

    + By (22, 19), we have $floor(Phi) tack {Phi}alpha :: ty$

  + By (18), we have $floor(Phi) tack {Phi}alpha :: ty$

  + By @erasure-not-in (2), we have $eqname disjoint floor(Phi)$

  + We have $floor(Phi) tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : {Phi}alpha$ by:

  $
    #proof-tree(
      rule(
        $floor(Phi) tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : {Phi}alpha$,
        rule(
          $floor(Phi) tack (e_1 : tau_1 = tau_2) : {Phi}tau$,
          $(8, 9)$
        ),
        rule(
          $eqname disjoint floor(Phi)$,
          $(20)$
        ),
        rule(
          $floor(Phi), eqname : tau_1 = tau_2 tack e_2 : {Phi}alpha$,
          $(16)$
        ),
        rule(
          $floor(Phi) tack {Phi}alpha :: ty$,
          $(19)$
        )
      )
    )
  $
]

== Proof of Completeness

#theorem[_Constraint generation is complete with respect to #aml _][
  $Phi assn$ and $Phi$ is the identity on $fv(e)$.

  If $floor(Phi) tack e : {Phi}alpha$, then $Phi tack [| e : alpha |]$.
]
#proof[
  We proceed by structural induction on $e$.

  - *Case* $x$
  + Let us assume $floor(Phi) tack x : {Phi}alpha$ holds.
  + $[| x : alpha |] = x space alpha$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack x : {Phi}alpha$,
          rule(
            $x : sigma in floor(Phi)$,
            $(a)$
          ),
          rule(
            $floor(Phi) tack sigma <= {Phi}alpha$,
            $(b)$
          ),
        )
      )
    $
  + By Lemma ?? (3.a), $x : sigma' in Phi$ where $sigma = {Phi}sigma'$ \
    #comment[$x : {Phi}sigma in floor(Phi) ==> x : sigma in Phi$]
  + By (3.b, 4), we have $floor(Phi) tack {Phi}sigma' <= {Phi}alpha$
  + By Lemma ?? (1), we have $floor(Phi) tack {Phi}alpha :: ty$ \
    #comment[This is regularity $Gamma tack e : tau ==> Gamma tack tau :: ty$]
  + By Lemma ?? (6), we have $Phi tack alpha :: ty$ \
    #comment[$floor(Phi) tack {Phi}tau :: ty ==> Phi tack tau :: ty$]
  + We have $Phi tack x space alpha$ by
  $
    #proof-tree(
      rule(
        $Phi tack x space alpha$,
        rule(
          $Phi tack alpha :: ty$,
          $(7)$
        ),
        rule(
          $x : sigma' in Phi$,
          $(4)$
        ),
        rule(
          $floor(Phi) tack {Phi}sigma' <= {Phi}alpha$,
          $(5)$
        )
      )
    )
  $

  - *Case* $efun x -> e$
  + Let us assume $floor(Phi) tack efun x -> e : {Phi}alpha$
  + $[|efun x -> e : alpha|] = exists alpha_1, alpha_2 :: ty. alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$, wlog $alpha_1, alpha_2, alpha_3 disjoint e, Phi$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack efun x -> e : underbrace(tau_1 -> tau_2, {Phi}alpha)$,
          rule(
            $floor(Phi) tack tau_1 :: ty$,
            $(a)$
          ),
          rule(
            $floor(Phi), x : tau_1 tack e : tau_2$,
            $(b)$
          ),
          rule(
            $x disjoint floor(Phi)$,
            $(c)$
          )
        )
      )
    $
  + By Lemma ?? (1), we have $floor(Phi) tack {Phi}alpha :: ty$. By Lemma ??, we have $Phi tack alpha :: ty$. \
    #comment[The first part is regularity $floor(Phi) tack e : {Phi}alpha ==> floor(Phi) tack {Phi}alpha :: ty ==> Phi tack alpha :: ty$]
  + Let us define $Phi' = Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2$.
  + By definition of erasure, $floor(Phi) = floor(Phi')$
  + By Lemma ?? (3.b), we conclude that $floor(Phi) tack tau_2 :: ty$. \
    #comment[This is regularity $Gamma, x : \_ tack e : tau => Gamma tack tau :: ty$]
  + By Lemma ?? (3.a, 7), we have $Phi tack tau_1, tau_2 :: ty$ \
    #comment[$floor(Phi) tack tau :: ty ==> Phi tack tau :: ty$]
  + We have
    $
      {Phi}alpha &= tau_1 -> tau_2 &#h1&"(3)" \
      <==> {Phi}{Phi}alpha &= {Phi}tau_1 -> {Phi}tau_2 \
      <==> {Phi}alpha &= {Phi}tau_1 -> {Phi}tau_2 &&"idemp subst ??" \
    $
    We conclude that ${Phi}tau_1 = tau_1$ and ${Phi}tau_2 = tau_2$.
  + By (4, 8), $alpha_1, alpha_2 disjoint {Phi}alpha, tau_1, tau_2$. Thus ${Phi'}alpha = {Phi}alpha$, $tau_1 = {Phi'}tau_1$, and \ $tau_2 = {Phi'}tau_2$. By (9), we have ${Phi'}alpha = {Phi'}tau_1 -> {Phi'}tau_2$. By definition of substitution (5), we have ${Phi'}tau_1 -> {Phi'}tau_2 = {Phi'}alpha_1 -> {Phi'}alpha_2 = {Phi'}(alpha_1 -> alpha_2) $
  + We have $Phi' tack alpha = alpha_1 -> alpha_2$ by
    $
      #proof-tree(
        rule(
          $Phi' tack alpha = alpha_1 -> alpha_2$,
          rule(
            $Phi' tack alpha, alpha_1 -> alpha_2 :: ty$,
            $"weakening" (4), (5)$
          ),
          rule(
            $floor(Phi') tack {Phi'}alpha equiv {Phi'}(alpha_1 -> alpha_2)$,
            rule(
              $floor(Phi) tack {Phi}alpha equiv {Phi}alpha$,
              rule(
                $floor(Phi) tack {Phi}alpha :: ty$,
                $(4)$
              ),
              name: [$equiv$Refl]
            ),
            name: [By (10)]
          ),
          name: [Equal]
        )
      )
    $
  + $Phi', x : alpha_1 assn$ by
    $
      #proof-tree(
        rule(
          $Phi', x : alpha_1 assn$,
          rule(
            $Phi, alpha_1 fbind(fflex) ty := tau_1, alpha_2 fbind(fflex) ty := tau_2 assn$,
            rule(
              $Phi, alpha_1 fbind(fflex) ty := tau_1 assn$,
              $Phi assn$,
              rule(
                $alpha_1 disjoint Phi$,
                $(2)$
              ),
              rule(
                $Phi tack tau_1 :: ty$,
                $(8)$
              )
            ),
            rule(
              $alpha_2 disjoint Phi, alpha_1$,
              $(2)$
            ),
            rule(
              $Phi, alpha_1 fbind(fflex) ty := tau_1 tack tau_2 :: ty$,
              $"weakening" (8)$
            )
          ),
          rule(
            $x disjoint Phi'$,
            [@erasure-not-in (3.c)]
          ),
          rule(
            $Phi' tack alpha_1 :: ty$,
            $(5)$
          )
        )
      )
    $
  + $Phi', x : alpha_1$ is identity on $fv(e)$ since $alpha_1, alpha_2 disjoint e$ and $Phi$ is identity on $fv(e)$
  + By (3.b, 5, 6) and the definition of substitution, we have $floor(Phi'\, x : alpha_1) tack e : {Phi', x : alpha_1}alpha_2$
  + By induction (12, 13, 14), we have $Phi', x : alpha_1 tack [| e : alpha_2 |]$
  + We have $Phi' tack lambda alpha_3. alpha_3 = alpha_1 => alpha_1$ by
    $
      #proof-tree(
        rule(
          $Phi' tack lambda alpha_3. alpha_3 = alpha_1 => alpha_1$,
          rule(
            $alpha_3 disjoint Phi'$,
            $(2)$
          ),
          rule(
            $Phi' tack alpha_1 :: ty$,
            $(5)$
          ),
          rule(
            $Phi', alpha fbind(fflex) ty := alpha_1 tack alpha_3 = alpha_1$,
            $("Refl")$
          ),
          name: [Abs]
        )
      )
    $
  + We have $Phi tack [| efun x -> e : alpha |]$ by
  $
    #proof-tree(
      rule(
        $Phi tack exists alpha_1, alpha_2 :: ty. alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$,
        rule(
          $Phi tack tau_1, tau_2 :: ty$,
          $(8)$
        ),
        rule(
          $Phi' tack alpha = alpha_1 -> alpha_2 and clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$,
          rule(
            $Phi' tack alpha = alpha_1 -> alpha_2$,
            $(11)$
          ),
          rule(
            $Phi' tack clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]$,
            rule(
              $Phi' tack lambda alpha_3. alpha_3 = alpha_1 => alpha_1$,
              $(16)$
            ),
            rule(
              $Phi', x : alpha_1 tack [| e : alpha_2|]$,
              $(15)$
            )
          ),
          name: [Conj]
        ),
        name: [$"Exists"^*$]
      )
    )
  $

  - *Case* $e_1 space e_2$
  _Trivial_

  - *Case* $elet x = e_1 ein e_2$

  + Let us assume $floor(Phi) tack elet x = e_1 ein e_2 : {Phi}alpha$

  + $[| elet x = e_1 ein e_2 : alpha |] = clet x = lambda beta. [| e_1 : beta |] cin [| e_2 : alpha |]$, wlog $beta disjoint alpha, e_1, e_2, Phi$

  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack elet x = e_1 ein e_2 : {Phi}alpha$,
          rule(
            $floor(Phi), overline(gamma fbind(fflex) kappa) tack e_1 : tau_1$,
            $(a)$
          ),
          rule(
            $x, overline(gamma) disjoint floor(Phi)$,
            $(b)$
          ),
          rule(
            $floor(Phi), x : tforall(overline(gamma :: kappa)) tau_1 tack e_2 : {Phi}alpha_1$,
            $(c)$
          ),
          name: [Let]
        )
      )
    $
    wlog $overline(gamma) disjoint Phi, beta, alpha$

  + By Lemma ?? (3.a), we have $floor(Phi), overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$. By Lemma ??, $Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$
    #comment[Regularity + $floor(Phi), overline(gamma fbind(fflex) kappa) tack tau_1 :: ty => floor(Phi) tack tforall(overline(gamma :: kappa)) tau_1 scm => Phi tack tforall(overline(gamma :: kappa)) tau_1 scm => Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$]
  + Let us define $Phi' = Phi, overline(gamma fbind(fflex) kappa), beta fbind(fflex) ty := tau_1$
  + By definition of erasure, $floor(Phi') = floor(Phi), overline(gamma fbind(fflex) kappa)$
  + By (4), we note that ${Phi, overline(gamma fbind(fflex) kappa)}tau_1 = tau_1$. So by the definition of substitution, ${Phi'}beta = tau_1$
  + By (3.a, 6, 7), we have $floor(Phi') tack e_1 : {Phi'}beta$
  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, overline(gamma fbind(fflex) kappa), beta fbind(fflex) ty := tau_1 assn$,
          rule(
            $Phi, overline(gamma fbind(fflex) kappa) assn$,
            $Phi assn$,
            rule(
              $overline(gamma) disjoint Phi$,
              $(3)$
            ),
            name: [$"TyVarAssn"^*$]
          ),
          rule(
            $beta disjoint Phi, overline(gamma)$,
            $(2, 3)$
          ),
          rule(
            $Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$,
            $(4)$
          ),
          name: [$"SolvedTyVarAssn"$]
        )
      )
    $
  + $Phi'$ is identity for $fv(e_1)$ given $Phi$ is identity for $e_1$ and $beta disjoint e_1$
  + By induction (8, 9, 10), we have $Phi' tack [| e_1 : beta |]$
  + Let $sigma = tforall(overline(gamma :: kappa)) tau_1$.
  + Note that $floor(Phi\, x : sigma) = floor(Phi), x : sigma$ by definition of erasure (7)
  + By @weaken-sub-inv, ${Phi}alpha = {Phi, x : sigma}alpha$
  + By (3.c, 13, 14), we have $floor(Phi\, x : sigma) tack e_2 : {Phi, x : sigma}alpha$
  + By (4), we have $Phi tack tforall(overline(gamma fbind(fflex) kappa)) tau_1 scm$. By (3.b), we have $Phi, x : tforall(overline(gamma fbind(fflex) kappa)) tau_1 assn$
  + $Phi, x : sigma$ is identity on $fv(e_2)$ given $Phi$ is identity on $fv(e_2)$
  + By induction (15, 16, 17), we have $Phi, x : sigma tack [| e_2 : alpha |]$
  + We have $Phi tack [| elet x = e_1 ein e_2 : alpha |]$ by
  $
    #proof-tree(
      rule(
        $Phi tack clet x = lambda beta. [| e_1 : beta |] cin [| e_2 : alpha |]$,
        rule(
          $Phi tack lambda beta. [| e_1 : beta |] => tforall(overline(gamma :: kappa)) tau_1$,
          rule(
            $beta, overline(gamma) disjoint Phi$,
            $(2, 3)$
          ),
          rule(
            $Phi, overline(gamma fbind(fflex) kappa) tack tau_1 :: ty$,
            $(4)$
          ),
          rule(
            $Phi' tack [| e_1 : beta |]$,
            $(11)$
          ),
          name: [Abs]
        ),
        rule(
          $x disjoint Phi$,
          [@erasure-not-in (3.b)]
        ),
        rule(
          $Phi, x : tforall(overline(gamma :: kappa)) tau_1 tack [| e_2 : alpha|]$,
          $(18)$
        ),
        name: [Let]
      )
    )
  $

  - *Case* $(e : tau)$
  + Let us assume $floor(Phi) tack (e : tau) : {Phi}alpha$
  + $[| (e : tau) : alpha |] = alpha = ceil(tau) and (exists beta :: ty. beta = ceil(tau) and [| e : beta |])$, wlog $beta disjoint alpha, e, tau, Phi$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack (e : tau) : {Phi}alpha$,
          rule(
            $floor(Phi) tack e : tau_1$,
            $(a)$
          ),
          rule(
            $floor(Phi) tack forall ceil(tau) <= tau_1, {Phi}alpha$,
            $(b)$
          )
        )
      )
    $

  + Let us define $Phi' = Phi, beta fbind(fflex) ty := tau_1$
  + By definition of erasure (4), $floor(Phi') = floor(Phi)$
  + By Lemma ?? (3.a), we have $floor(Phi) tack tau_1 :: ty$. By Lemma ??, we have $Phi tack tau_1 :: ty$
  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, beta fbind(fflex) ty := tau_1 assn$,
          $Phi assn$,
          rule(
            $beta disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau_1 :: ty$,
            $(6)$
          )
        )
      )
    $
  + $Phi'$ is identity for $fv(e)$ since $Phi$ is identity for $fv(e)$ and $beta disjoint e$
  + By @weaken-sub-inv, ${Phi'}tau_1 = {Phi}tau_1 = tau_1$. So by definition of substitution, we have ${Phi'}beta = {Phi'}tau_1 = tau_1$
  + By (3.a, 5, 9), we have $floor(Phi') tack e : {Phi'}beta$
  + By induction (10, 7, 8), we have $Phi' tack [| e : beta |]$
  + By @complete-scope-erasure, we have $Phi tack alpha = ceil(tau)$ and $Phi' tack beta = ceil(tau)$
  + We have $Phi tack [| (e : tau) : alpha |]$ by
  $
    #proof-tree(
      rule(
        $Phi tack alpha = ceil(tau) and (exists beta :: ty. beta = ceil(tau) and [| e : beta |])$,
        rule(
          $Phi tack alpha = ceil(tau)$,
          $(12)$
        ),
        rule(
          $Phi tack exists beta :: ty. beta = ceil(tau) and [| e : beta |]$,
          rule(
            $beta disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau_1 :: ty$,
            $(6)$
          ),
          rule(
            $Phi' tack beta = ceil(tau) and [| e : beta |]$,
            rule(
              $Phi' tack beta = ceil(tau)$,
              $(12)$
            ),
            rule(
              $Phi' tack [| e : beta |]$,
              $(11)$
            ),
            name: [Conj]
          ),
          name: [Exists]
        ),
        name: [Conj]
      )
    )
  $


  - *Case* $efun (etype beta) -> e$
  + Let us assume $floor(Phi) tack efun (etype beta) -> e : {Phi}alpha$
  + $[| efun (etype beta) -> e : alpha |] = clet x = forall beta :: ty. lambda gamma. [| e : gamma |] cin x space alpha$, wlog $gamma, x disjoint alpha, beta, e, Phi$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack efun (etype beta) -> e : {Phi}alpha$,
          rule(
            $floor(Phi), beta fbind(frigid) ty tack e : tau$,
            $(a)$,
          ),
          rule(
            $beta disjoint floor(Phi)$,
            $(b)$,
          ),
          rule(
            $beta in.not dangerous(tau)$,
            $(c)$,
          ),
          rule(
            $floor(Phi) tack tforall(beta :: ty) tau <= {Phi}alpha$,
            $(d)$,
          ),
          name: [TyFun]
        )
      )
    $

  + Let us define $Phi' = Phi, beta fbind(frigid) ty, gamma fbind(fflex) ty := tau$
  + By Lemma ??, we have $floor(Phi), beta fbind(frigid) ty tack tau :: ty$. By Lemma ??, we have $Phi, beta fbind(frigid) ty tack tau :: ty$
  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, beta fbind(frigid) ty, gamma fbind(fflex) ty := tau assn$,
          rule(
            $Phi, beta fbind(frigid) ty assn$,
            $Phi assn$,
            rule(
              $beta disjoint Phi$,
              [Lemma ?? (3.b)]
            )
          ),
          rule(
            $gamma disjoint Phi, beta$,
            $(2)$
          ),
          rule(
            $Phi, beta fbind(frigid) ty tack tau :: ty$,
            $(5)$
          )
        )
      )
    $

  + $Phi'$ is identity for $fv(e)$ given $Phi$ is identity for $fv(e)$ and $gamma disjoint e$ (2)
  + By definition of erasure (4), $floor(Phi') = floor(Phi), beta fbind(frigid) ty$
  + By @weaken-sub-inv (5), ${Phi'}tau = tau$. So by the definition of substitution, ${Phi'}gamma = {Phi'}tau = tau$.
  + By (3.a, 8, 9), we have $floor(Phi') tack e : {Phi'}gamma$
  + By induction (6, 7, 10), we have $Phi' tack [| e : gamma |]$
  + By Lemma (1), we have $floor(Phi) tack {Phi}alpha :: ty$. By Lemma ??, we have $Phi tack alpha :: ty$
  + We have $Phi tack forall beta :: ty. lambda gamma. [| e : gamma |] => tforall(beta :: ty) tau$ by
    $
      #proof-tree(
        rule(
          $Phi tack forall beta. lambda gamma. [| e : gamma |] => tforall(beta :: ty) tau$,
          rule(
            $beta, gamma disjoint Phi$,
            $(2, 3.b)$
          ),
          rule(
            $Phi, beta fbind(frigid) ty tack tau :: ty$,
            $(5)$
          ),
          rule(
            $Phi' tack [| e : gamma |]$,
            $(11)$
          ),
          rule(
            $beta in.not dangerous(tau)$,
            $(3.c)$
          ),
          name: [Abs]
        )
      )
    $
  + By Lemma (1), we have $floor(Phi) tack {Phi}alpha :: ty$. By Lemma ??, we have $Phi tack alpha :: ty$.
  + By definition of substitution (9), we have ${Phi}(tforall(beta :: ty) tau) = tforall(beta :: ty) {Phi}tau = tforall(beta :: ty) tau$
  + By definition of erasure, $floor(Phi\, x : tforall(beta :: ty) tau) = floor(Phi), x : tforall(beta :: ty) tau$
  + By @weaken-sub-inv, we have ${Phi, x : tforall(beta :: ty) tau}(tforall(beta :: ty) tau) = {Phi}(tforall(beta :: ty) tau)$ and \ ${Phi, x : tforall(beta :: ty) tau}alpha = {Phi}alpha$
  + We have $Phi tack [| efun (etype beta) -> e |]$ by
  $
    #proof-tree(
      rule(
        $Phi tack clet x = forall beta :: ty. lambda gamma. [| e : gamma |] cin x space alpha$,
        rule(
          $Phi tack forall beta. lambda gamma. [| e : gamma |] => tforall(beta :: ty) tau$,
          $(13)$
        ),
        rule(
          $x disjoint Phi$,
          $(2)$
        ),
        rule(
          $Phi, x : tforall(beta :: ty) tau tack x space alpha$,
          rule(
            $Phi, x : tforall(beta :: ty) tau tack alpha :: ty$,
            [weakening (14)]
          ),
          rule(
            $floor(Phi'') tack {Phi''}(tforall(beta :: ty) tau) <= {Phi''}alpha$,
            rule(
              $floor(Phi) tack tforall(beta :: ty) tau <= {Phi}alpha$,
              $(3.c)$
            ),
            name: [(15, 16, 17)]
          ),
          name: [App]
        ),
        name: [Let]
      )
    )
  $

  - *Case* $ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2$
  + Let us assume $floor(Phi) tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2$
  + $[| ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : alpha |] = (exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |]) and eqname : tau_1 = tau_2 => [| e_2 : alpha |]$ wlog $eqname, beta disjoint e_1, tau_1, tau_2, e_2, alpha, Phi$
  + By inversion (1), we have
    $
      #proof-tree(
        rule(
          $floor(Phi) tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : {Phi}alpha$,
          rule(
            $floor(Phi) tack (e_1 : tau_1 = tau_2) : tau$,
            $(a)$
          ),
          rule(
            $eqname disjoint floor(Phi)$,
            $(b)$
          ),
          rule(
            $floor(Phi), eqname : tau_1 = tau_2 tack e_2 : {Phi}alpha$,
            $(c)$
          ),
          rule(
            $floor(Phi) tack {Phi}alpha :: ty$,
            $(d)$
          )
        )
      )
    $
  + By inversion of (3.a), we have $floor(Phi) tack tau_1 = tau_2 :: ty frigid$. Hence $floor(Phi) tack tau_1, tau_2 :: ty frigid$.

  + Let us define $Phi' = Phi, beta fbind(fflex) ty := tau$.

  + By definition of erasure (5), $floor(Phi') = floor(Phi)$
  + By Lemma ?? (3.a), $floor(Phi) tack tau :: ty$. By Lemma ??, we have $Phi tack tau :: ty$
  + By (7), we note that ${Phi}tau = tau$. By @weaken-sub-inv, ${Phi'}tau = {Phi}tau = tau$.
    By definition of substitution (5), ${Phi'}beta = {Phi'}tau = tau$
  + By (3.a, 6, 8), we have $floor(Phi') tack (e_1 : tau_1 = tau_2) : {Phi'}beta$
  + $Phi' assn$ by
    $
      #proof-tree(
        rule(
          $Phi, beta fbind(fflex) ty := tau assn$,
          $Phi assn$,
          rule(
            $beta disjoint Phi$,
            $(2)$
          ),
          rule(
            $Phi tack tau :: ty$,
            $(7)$
          )
        )
      )
    $
  + $Phi'$ is identity on $fv(e_1 : tau_1 = tau_2)$ since $Phi$ is identity on $fv(e_1 : tau_1 = tau_2)$ and $beta disjoint e_1, tau_1, tau_2$
  + By induction (9, 10, 11), we have $Phi' tack [| (e_1 : tau_1 = tau_2) : beta |]$
  + By Lemma ?? (4), we have $Phi tack tau_1, tau_2 :: ty frigid$
  + By @weaken-sub-inv, ${Phi, eqname : tau_1 = tau_2}alpha = {Phi}alpha$
  + By definition of erasure $floor(Phi\, eqname : tau_1 = tau_2) = floor(Phi), eqname : tau_1 = tau_2$
  + By (3.c, 14, 15), we have $floor(Phi\, eqname : tau_1 = tau_2) tack e_2 : {Phi, eqname : tau_1 = tau_2}alpha$
  + $Phi, eqname : tau_1 = tau_2 assn$ by
    $
      #proof-tree(
        rule(
          $Phi, eqname : tau_1 = tau_2 assn$,
          $Phi assn$,
          rule(
            $eqname disjoint Phi$,
            [Lemma ?? (3.b)]
          ),
          rule(
            $Phi tack tau_1, tau_2 :: ty frigid$,
            $(13)$
          )
        )
      )
    $

  + $Phi, eqname : tau_1 = tau_2$ is identity on $fv(e_2)$ given $Phi$ is identity on $fv(e_2)$
  + By induction $(16, 17, 18)$, we have $Phi, eqname : tau_1 = tau_2 tack [| e_2 : alpha |]$
  + We have $Phi tack [| ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : alpha |]$ by
  $
    #proof-tree(
      rule(
        $Phi tack (exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |]) and eqname : tau_1 = tau_2 => [| e_2 : alpha |]$,
        rule(
          $Phi tack exists beta :: ty. [| (e_1 : tau_1 = tau_2) : beta |]$,
          rule(
            $Phi' tack [| (e_1 : tau_1 = tau_2) : beta |]$,
            $(12)$
          )
        ),
        rule(
          $Phi tack eqname : tau_1 = tau_2 => [| e_2 : alpha |]$,
          rule(
            $Phi tack tau_1, tau_2 :: ty frigid$,
            $(13)$
          ),
          rule(
            $eqname disjoint Phi$,
            $(??)$
          ),
          rule(
            $Phi, eqname : tau_1 = tau_2 tack [| e_2 : alpha |]$,
            $(19)$
          )
        )
      )
    )
  $
]
