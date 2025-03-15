#import "../../lib/std.typ": *
#import "../..//lib/syntax.typ": *
#import "../../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "../cmon.typ": *

// HACK to get thm to left align
#show: thmrules

We proceed by collecting auxiliary lemmas in Appendix A1 before proving soundness and completeness of the syntax-directed system from Section ?? in individual subsections.
Following this, we state and prove useful properties concerning subsumption. And finally, we prove monotonicity.

== Auxiliary Lemmas

We begin by stating the standard weakening, exchange, and type substitution lemmas.

*Remark*. We state these for the non-syntax-directed variant of #aml. But by soundness and completeness of the syntax-directed of #aml with respect to #aml, it follows that these lemmas also hold for the syntax-directed system.

#lemma("Weakening")[
  Suppose $Gamma, Theta, Delta ctx$. Then
  + If $Gamma, Delta tack tau^kappa :: kappa space phi$, then $Gamma, Theta, Delta tack tau^kappa :: kappa space phi$
  + If $Gamma, Delta tack tau equiv tau' space [Psi]$, then $Gamma, Theta, Delta tack tau equiv tau' space [Psi]$
  + If $Gamma, Delta tack sigma <= sigma'$, then $Gamma, Theta, Delta tack sigma <= sigma'$
  + If $Gamma, Delta tack e : sigma$, then $Gamma, Theta, Delta tack e : sigma$
]
#proof[
  By induction on the derivation.
]


#lemma("Exchange")[
  Suppose $Gamma, Theta, Delta ctx$ and $Gamma, Delta, Theta ctx$. Then
  + If $Gamma, Theta, Delta tack tau^kappa :: kappa space phi$, then $Gamma, Delta, Theta tack tau^kappa :: kappa space phi$.
  + If $Gamma, Theta, Delta tack tau equiv tau' space [Psi]$, then $Gamma, Delta, Theta tack tau equiv tau' space [Psi]$
  + If $Gamma, Theta, Delta tack sigma <= sigma'$, then $Gamma, Delta, Theta tack sigma <= sigma'$
  + If $Gamma, Theta, Delta tack e : sigma$, then $Gamma, Delta, Theta tack e : sigma$
]
#proof[
  By induction on the derivation.
]


#lemma("Flexibility Weakening")[
  Suppose $Gamma, alpha ::^frigid kappa, Delta ctx$

  + If $Gamma tack tau^kappa :: kappa space phi$, then $Gamma tack tau^kappa :: kappa space phi'$ where $phi <= phi'$.
  + If $Gamma, alpha ::^frigid kappa, Delta tack tau^kappa :: kappa$ and $alpha in.not dangerous(tau^kappa)$, then $Gamma, alpha ::^fflex, Delta tack tau^kappa :: kappa$
  + If $Gamma, alpha ::^frigid kappa,  Delta tack tau equiv tau' space [Psi]$ and $alpha in.not dangerous(tau, tau')$, then $Gamma, alpha ::^fflex kappa , Delta tack tau equiv tau' space [Psi]$
  + If $Gamma, alpha ::^frigid kappa, Delta tack sigma <= sigma'$ and $alpha in.not dangerous(sigma, sigma')$, then $Gamma, alpha ::^fflex kappa, Delta tack sigma <= sigma'$
]
#proof[
  By induction on the derivation.
]


#lemma("Type Substitution")[
  Suppose $Gamma tack tau^kappa :: kappa space phi$. Then
  + If $Gamma, alpha ::^phi kappa, Delta tack tau^kappa' :: kappa' space phi'$, then $Gamma, Delta[alpha := tau^kappa] tack tau^kappa'[alpha := tau^kappa] :: kappa' space phi'$
  + If $Gamma, alpha ::^phi kappa, Delta tack tau_1 equiv tau_2$, then $Gamma, Delta[alpha := tau^kappa] tack tau_1[alpha := tau^kappa] equiv tau_2[alpha := tau^kappa]$
  + If $Gamma, alpha ::^phi kappa, Delta tack sigma <= sigma'$, then $Gamma, Delta[alpha := tau^kappa] tack sigma[alpha := tau^kappa] <= sigma'[alpha := tau^kappa]$
  + If $Gamma, alpha ::^phi kappa, Delta tack e : sigma$, then $Gamma, Delta[alpha := tau^kappa] tack e[alpha := tau^kappa] : sigma[alpha := tau^kappa]$
]
#proof[
  By induction on the derivation of the substitutee.
]

It is important to note that type substitution requires the preservation of flexibility. This restriction can _only_ be relaxed if the rigid variable that is being substituted does not occur in a dangerous position (as formalized in the flexibility weakening lemma).


#aml preserves well-formedness in all judgements. This is carefully ensured in each rule. Consequentially, the following regularity lemma is provable.

#lemma("Well-formedness Properties")[
  Suppose $Gamma ctx$.
  + If $Gamma tack tau_1 equiv tau_2 space [Psi]$, then $Gamma tack tau_1 :: ty$ and $Gamma tack tau_2 :: ty$.
  + If $Gamma tack sigma_1 <= sigma_2$, then $Gamma tack sigma_1 scm$ and $Gamma tack sigma_2 scm$.
  + If $Gamma tack e : sigma$, then $Gamma tack sigma scm$.
]
#proof[
  By induction on the derivation.
]

#lemma[_Soundness of generalization_][
  If $Gamma, cal(V) tack e : tau$ and $cal(V) disjoint Gamma$ then $Gamma tack e : tforall(cal(V)) tau$.
] <soundgen>
#proof[
  Trivial proof by induction on the cardinality of $cal(V)$.
]



#definition[
  The equations of a context $Gamma$, written $eqs(Gamma)$, is defined by:
  $
    eqs(emptyset) &= emptyset \
    eqs(Gamma, eqname : tau_1 = tau_2) &= eqs(Gamma), eqname : tau_1 = tau_2 \
    eqs(Gamma, \_) &= eqs(Gamma)
  $
  We write $fv(eqs(Gamma))$ for the set of free variables in the types of $eqs(Gamma)$.
]

#lemma[
  Given $alpha in.not textsf("eqs")(Gamma)$.

  + If $Gamma tack tau equiv tau' space [Psi]$ and $alpha in.not dangerous(tau')$, then $alpha in.not dangerous(tau)$
  + If $Gamma tack sigma <= sigma'$ and $alpha in.not dangerous(sigma')$, then $alpha in.not dangerous(sigma)$
] <dangerous-anti-monotonicity-lemma>
#proof[
  + Induction on the derivation $Gamma tack tau equiv tau' space [Psi]$.

    - *Case* ($equiv$Amb)
    + Let us assume $Gamma tack [Psi']tau equiv [Psi']tau' space [Psi]$
    + By inversion of ($equiv$Amb), we have $Gamma tack tau equiv tau' space [Psi']$.
    + By definition of $dangerous$, $alpha in.not dangerous([Psi']tau') <==> alpha in.not fv(tau')$
    + Since $dangerous(tau') subset.eq fv(tau')$, we conclude that $alpha in.not dangerous(tau')$

    + By induction (2, 4), we have $alpha in.not dangerous(tau)$

    + Hence $alpha in.not fv(tau)$. So by definition, $alpha in.not dangerous([Psi']tau)$

    - *Case* ($equiv$Use)

    + Let us assume $Gamma tack tau equiv tau' space [Psi]$

    + By inversion of ($equiv$Use), we have $eqname : tau = tau' in Gamma$ and $eqname in Psi$

    + By assumption, we have $alpha in.not fv(tau, tau')$

    + Given $dangerous(tau) subset.eq fv(tau)$, we have $alpha in.not dangerous(tau)$

    - *Otherwise*
    _Congruence cases_

  +
    We proceed by induction on the derivation of $Gamma tack sigma <= sigma'$.
    - *Case* ($<=equiv$)
    + Use (1)

    - *Case* ($<=forall$L)
    + Let us assume $Gamma tack sigma <= sigma'$.
    + By inversion of the ($forall$L) rule, we have $sigma = tforall(beta :: kappa) sigma''$ (a), $Gamma tack tau :: kappa$ (b), and\
      $Gamma tack sigma''[beta := tau] <= sigma'$ (c).
    + By induction (2.c), we have $alpha in.not dangerous(sigma''[beta := tau])$
    + By (3), we conclude $alpha in.not dangerous(sigma'')$ and $alpha in.not dangerous(tau)$.
    + By (4), $alpha in.not dangerous(tforall(beta) sigma'')$

    - *Case* ($<=forall$R)
    + Let us assume $Gamma tack sigma <= sigma'$.
    + By inversion of the ($forall$R) rule, we have $sigma' = tforall(beta :: kappa) sigma''$ (a), $beta disjoint Gamma$ (b), and $Gamma, beta^fflex :: kappa tack sigma <= sigma''$ (c)
    + By definition of $dangerous$, we have $alpha in.not dangerous(sigma'')$
    + By induction (2.c), we have $alpha in.not dangerous(sigma)$
]



== Proof of Soundness


#theorem[_Soundness of the syntax-directed #aml typing judgements_][
  When $Gamma sdtack e : tau$ then we also have $Gamma tack e : tau$.
]

#proof[
  We proceed by structural induction on $e$.

  - *Case* $x$.
  1. Let us assume $Gamma sdtack x : tau$.
  2. By inversion, we have $x : sigma in Gamma$ (a) and $Gamma tack sigma <= tau$ (b).
  3. We have $Gamma tack x : tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack x : tau$,
        rule(
          $Gamma tack x : sigma$,
          rule(
            $x : sigma in Gamma$,
            $(2. a)$
          ),
          name: [Var]
        ),
        rule(
          $Gamma tack sigma <= tau$,
          $(2.b)$
        ),
        name: [Sub]
      )
    )
  $

  - *Case* $elet x = e_1 ein e_2$.
  1. Let us assume $Gamma sdtack elet x = e_1 ein e_2 : tau$.
  2. By inversion, we have $Gamma, cal(V) sdtack e_1 : tau'$ (a), $cal(V) disjoint Gamma$ (b), and $Gamma, x : tforall(cal(V)) tau' sdtack e_2 : tau$ (c).
  3. By induction (2.a), we have $Gamma, cal(V) tack e_1 : tau'$ (a). By @soundgen (3.a, 2.b), we have \ $Gamma tack e_1 : tforall(cal(V)) tau'$ (b).
  4. By induction (2.c), we have $Gamma, x : tforall(cal(V)) tau' tack e_2 : tau$ (a).
  5. We have $Gamma tack elet x = e_1 ein e_2 : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : tau$,
      rule(
        $Gamma tack e_1 : tforall(cal(V)) tau'$,
        $(3.a)$
      ),
      rule(
        $Gamma, x : tforall(cal(V)) tau' tack e_2 : tau$,
        $(4.a)$
      ),
      name: [Let]
    )
  )
  $


  - *Cases* $efun x -> e$, $e_1 space e_2$, $(e: tau')$, and $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$.
  _Trivial, this is identical to their declarative counterpart._

  - *Cases* $efun (etype alpha) -> e$, $erefl$, and $()$.
  _Trivial, equivalent to the declarative counterpart with instantiation._
]


== Proof of Completness


#theorem[_Completeness of the syntax-directed #aml typing judgements_][
  When $Gamma tack e : sigma$, then for some $cal(V) disjoint Gamma$, we also have $Gamma, cal(V) sdtack e : tau$ where $Gamma tack tforall(cal(V)) tau <= sigma$.
]

#proof[
  We proceed by rule induction on $Gamma tack e : sigma$.

  - *Case* (Var)
  1. Let us assume $Gamma tack x : sigma$.
  2. By inversion of the (Var) rule, we have $x : sigma in Gamma$.
  3. Wlog, we write $sigma = tforall(cal(V)) tau$ s.t $cal(V) disjoint Gamma$. We have $Gamma, cal(V) tack sigma <= tau$ with a trivial substituion.
  4. By weakining, we have $x : sigma in Gamma, cal(V)$.
  5. We have $Gamma, cal(V) sdtack x : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma, cal(V) sdtack x : tau$,
      rule(
        $x : sigma in Gamma, cal(V)$,
        $(4)$
      ),

      rule(
        $Gamma, cal(V) tack sigma <= tau$,
        $(3)$
      ),
      name: [Var]
    )
  )
  $
  6. We have $Gamma tack tforall(cal(V)) tau <= sigma$ by reflexivity of $<=$.

  - *Case* (Sub)
  1. Let us assume $Gamma tack e : sigma$.
  2. By inversion of the (Sub) rule, we have $Gamma tack e : sigma'$ (a) and $Gamma tack sigma' <= sigma$ (b).
  3. By induction (2.a), we have $Gamma, cal(V) sdtack e : tau$ (a) and $Gamma tack tforall(cal(V)) tau <= sigma'$ (b).
  4. By transitivity of $<=$ (3.b, 2.b), we have $Gamma tack tforall(cal(V)) tau <= sigma$.

  - *Case* (Gen)
  1. Let us assume $Gamma tack e : sigma$.
  2. By inversion of the (Gen) rule, we have $Gamma, alpha ::^fflex kappa tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), and \ $sigma = tforall(alpha :: kappa) sigma'$ (c).
  3. By induction (2.a), we have $Gamma, alpha ::^fflex kappa, cal(V) sdtack e : tau$ (a), $cal(V) disjoint Gamma$ (b), and \ $Gamma, alpha ::^fflex kappa tack tforall(cal(V)) tau <= sigma'$ (c).
  4. Let $cal(V') = alpha ::^fflex kappa, cal(V)$. By (2.b, 3.b), $cal(V') disjoint Gamma$. By (3.a), $Gamma, cal(V') sdtack e : tau$.
  5. By definition of $<=$ and (3.c), we have $Gamma tack tforall(cal(V')) tau <= tforall(alpha) sigma'$.

  - *Case* (Let)
  1. Let us assume $Gamma tack elet x = e_1 ein e_2 : sigma$
  2. By inversion of the (Let) rule, we have $Gamma tack e_1 : sigma'$ (a), and $Gamma, x : sigma' tack e_2 : sigma$ (b).
  3. By induction (2.a), we have $Gamma, cal(V_1) sdtack e_1 : tau'$ (a), $cal(V_1) disjoint Gamma$ (b), and $Gamma tack tforall(cal(V_1)) tau' <= sigma'$ (c).
  4. By induction (2.b), we have $Gamma, x : sigma', cal(V_2) sdtack e_2 : tau$ (a), $cal(V_2) disjoint Gamma, x : sigma'$ (b), and \ $Gamma tack tforall(cal(V_2)) tau <= sigma$ (c).
  5. By @monotonicity (3.c, 4.a), we have $Gamma, x : tforall(cal(V_1)) tau', cal(V_2) sdtack e_2 : tau$.
  6. By term exchange (5, 4.b), we have $Gamma, cal(V_2), x : tforall(cal(V_1)) tau' sdtack e_2 : tau$.
  7. By weakening and type exchange (3.a, 3.b, 4.b), we have $Gamma, cal(V_2), cal(V_1) sdtack e_1 : tau'$ (a) and $cal(V_1) disjoint Gamma, cal(V_2)$ (b).
  8. We have $Gamma, cal(V_2) sdtack elet x = e_1 ein e_2 : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma, cal(V_2) sdtack elet x = e_1 ein e_2 : tau$,
      rule(
        $Gamma, cal(V_2), cal(V_1) sdtack e_1 : tau'$,
        $(7.a)$
      ),
      rule(
        $cal(V_1) disjoint Gamma, cal(V_2)$,
        $(7.b)$
      ),
      rule(
        $Gamma, cal(V_2), x : tforall(cal(V_1)) tau' sdtack e_2 : tau$,
        $(6)$
      ),
      name: [Let]
    )
  )
  $

  - *Cases* (Fun), (App), (Annot), and (Match).
  _Trivial, this is identical to their declarative counterpart._


  - *Cases* (TyFun).
  1. Let us assume $Gamma tack efun (etype alpha) -> e : sigma$.
  2. By inversion of the (TFun) rule, we have $Gamma, alpha ::^frigid ty tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), \ $alpha in.not dangerous(sigma')$ (c), and $sigma = tforall(alpha :: ty) sigma'$ (d).
  3. By induction (2.a), we have $Gamma, alpha ::^frigid ty, cal(V) sdtack e : tau'$ (a), $cal(V) disjoint Gamma, alpha ::^frigid ty$ (b), and \ $Gamma, alpha ::^frigid ty tack tforall(cal(V)) tau' <= sigma'$ (d).
  4. Wlog $beta disjoint Gamma, cal(V), alpha$. Define $cal(V') = cal(V), beta ::^fflex ty$.
  5. By weakening and type exchange (3.a), we have $Gamma, cal(V)', alpha ::^frigid ty sdtack e : tau'$.
  6. By (3.b, 4), we have $alpha disjoint Gamma, cal(V)'$.
  7. By @dangerous-anti-monotonicity-lemma (2.c, 3.d), $alpha in.not dangerous(tforall(cal(V)) tau')$. Since $alpha disjoint cal(V)$, it follows that $alpha in.not dangerous(tau')$.
  8. Define $tau = tau'[alpha := beta]$.
  9. We have $Gamma, cal(V)' tack tforall(alpha :: ty) tau' <= tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V') tack tforall(alpha :: ty) tau' <= underbrace(tau'[alpha := beta], tau "by (8)")$,
        rule(
          $Gamma, cal(V') tack beta :: ty$,
          rule(
            $beta ::^fflex ty  in Gamma, cal(V')$,
            $(4)$
          ),
          name: [VarWF]
        ),
        rule(
          $Gamma, cal(V') tack tau'[alpha := beta] <= tau'[alpha := beta]$,
          $"refleixivity of" <=$
        ),
        name: [$<=forall$L]
      )
    )
  $
  10. We have $Gamma, cal(V)' sdtack efun (etype alpha) -> e : tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V') sdtack efun (etype alpha) -> e : tau$,
        rule(
          $Gamma, cal(V'), alpha ::^frigid ty sdtack e : tau'$,
          $(5)$
        ),
        rule(
          $alpha disjoint Gamma, cal(V')$,
          $(6)$
        ),
        rule(
          $alpha in.not dangerous(tau')$,
          $(7)$
        ),
        rule(
          $Gamma, cal(V') tack tforall(alpha :: ty) tau' <= tau$,
          $(9)$
        ),
        name: [TyFun]
      )
    )
  $
  11. By definition of substitution (4), $(tforall(cal(V)) tau'[alpha := beta])[beta := alpha] = tforall(cal(V)) tau'$
  12. By flexibility weakening (3.d, 2.d, 7), we have $Gamma, alpha ::^fflex ty tack tforall(cal(V)) tau' <= sigma'$
  13. We have $Gamma tack tforall(cal(V')) tau <= sigma$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack tforall(beta :: ty\, cal(V)) tau'[alpha := beta] <= tforall(alpha :: ty) sigma'$,
        rule(
          $Gamma, alpha ::^fflex ty tack tforall(beta :: ty\, cal(V)) tau'[alpha := beta] <= sigma'$,
          rule(
            $Gamma, alpha ::^fflex ty tack alpha :: ty$,
            rule(
              $alpha ::^fflex ty in Gamma, alpha ::^fflex ty$
            ),
            name: [VarWF]
          ),
          rule(
            $Gamma, alpha ::^fflex ty tack (tforall(cal(V)) tau'[alpha := beta])[beta := alpha] <= sigma'$,
            rule(
              $Gamma, alpha ::^fflex ty tack tforall(cal(V)) tau' <= sigma'$,
              $(12)$
            ),
            name: [$"by" (11)$]
          ),
          name: [$<=forall$L]
        ),
        rule(
          $alpha disjoint Gamma$,
          $(2.b)$
        ),
        name: [$<=forall$R]
      ),
    )
  $

  - *Case* (Unit).
  1. Let us assume $Gamma tack () : sigma$.
  2. By inversion of the (Unit) rule, we have $sigma = tforall(scopev :: scope) [scopev]tunit$.
  3. Wlog $scopev' disjoint Gamma$. Define $cal(V) = scopev' ::^fflex scope$.
  4. By (3), we have $cal(V) disjoint Gamma$
  5. We have $Gamma, cal(V) tack scopev' ok$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack scopev' :: scope$,
        rule(
          $scopev' ::^fflex scope in Gamma, cal(V)$,
          $(3)$
        ),
        name: [VarWF]
      )
    )
  $

  6. We have $Gamma, cal(V) tack tforall(scopev) [scopev]tunit <= [scopev']tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack tforall(scopev :: scope) [scopev]tunit <= [scopev']tunit$,
        rule(
          $Gamma, cal(V) tack scopev' :: scope$,
          $(5)$
        ),
        rule(
          $Gamma, cal(V) tack [scopev']tunit <= [scopev']tunit$,
          $"refleixitivity of" <=$
        ),
        name: [$<=forall$L]
      )
    )
  $


  7. We have $Gamma, cal(V) sdtack erefl : [scopev']tunit$ by
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) sdtack erefl : [scopev']tunit$,
        rule(
          $Gamma, cal(V) tack tforall(scopev :: scope) [scopev]tunit <= [scopev']tunit$,
          $(6)$
        ),
        name: [Refl]
      )
    )
  $

  8. We now show that $Gamma tack tforall(scopev' :: scope) [scopev']tunit <= tforall(scopev :: scopev) [scopev]tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack tforall(scopev' :: scope) [scopev']tunit <= tforall(scopev :: scope) [scopev]tunit$,
        rule(
          $Gamma, scopev ::^fflex scope tack tforall(scopev') [scopev']tunit <= [scopev]tunit$,
          $"(6)" (alpha "equiv")$
        ),
        rule(
          $scopev disjoint Gamma$,
          $"wlog"$
        ),
        name: [$<=forall$R]
      )
    )
  $


  - *Case* (Refl).
  _Symmetrical to (Unit)._


]








== Proofs of Reflexivity and Transitivity of Subsumption


#theorem("Reflexivity and Transitivity of Subsumption")[
  + $Gamma tack sigma <= sigma$
  + If $Gamma tack sigma_1 <= sigma_2$ and $Gamma tack sigma_2 <= sigma_3$, then $Gamma tack sigma_1 <= sigma_3$
]
#proof[
  + By structural induction on $sigma$.
  + By induction on the sum of the _quantifiers_ of $sigma_1, sigma_2$ and $sigma_3$.
]





== Proof of Monotonicity



#lemma[If $Gamma' <= Gamma$ then:
  - If $Gamma tack tau :: kappa space phi$, then $Gamma' tack tau :: space phi$.
  - If $Gamma tack tau equiv tau' space [Psi]$, then $Gamma' tack tau equiv tau' space [Psi]$
  - If $Gamma tack sigma <= sigma'$, then $Gamma' tack sigma <= sigma'$.
] <monotonicity-lemma>
#proof[
  By induction on the derivation.
]

#theorem[_Monotonicity of #aml typing judgements_][
  If $Gamma tack e : tau$ holds and $Gamma' <= Gamma$, then $Gamma' tack e : tau$ holds.
] <monotonicity>
#proof[
  We proceed by structural induction on $e$.
  - *Case* $x$.
  1. Let us assume $Gamma tack x : tau$ (a) and $Gamma' <= Gamma$ (b).
  2. By inversion, we have $x : sigma in Gamma$ (a) and $Gamma tack sigma <= tau$ (b).
  3. By definition of $<=$ (1.b), $x : sigma' in Gamma'$ (a) and $Gamma tack sigma' <= sigma$ (b).
  4. By transitivity of $<=$ (3.b, 2.b), $Gamma tack sigma' <= sigma$.
  5. By @monotonicity-lemma (1.b, 2.a, 3.a), we have $Gamma' tack sigma' <= sigma$ (a) and $Gamma' tack sigma <= tau$ (b).
  6. By transitivity of $<=$ (5.a, 5.b), we have $Gamma' tack sigma' <= tau$.
  7. We have $Gamma' tack x : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma' tack x : tau$,
      rule(
        $x : sigma' in Gamma'$,
        $(3.a)$
      ),
      rule(
        $Gamma' tack sigma' <= tau$,
        $(6)$
      ),
      name: [Var]
    )
  )
  $

  - *Cases* $erefl$ and $()$.
  _Trivial base cases._

  - *Cases* $efun x -> e$, $e_1 space e_2$, $elet x = e_1 ein e_2$, $efun (etype alpha) -> e$, $(e : tau')$, and \ $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$.
  _Trivial inductive cases._
]
